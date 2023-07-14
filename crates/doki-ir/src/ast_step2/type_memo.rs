use super::{LambdaId, TypeIdTag};
use crate::ast_step1::{ConstructorNames, PaddedTypeMap, Terminal, TypeId, TypePointer};
use crate::id_generator::{self, IdGenerator};
use crate::intrinsics::IntrinsicTypeTag;
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::BTreeMap;
use std::fmt::{self, Display};
use std::iter::once;

#[derive(PartialEq, Eq, PartialOrd, Ord, Default, Clone, Hash)]
pub struct TypeOf<T: TypeFamily> {
    ts: Vec<TypeUnitOf<T>>,
    pub recursive: bool,
    pub reference: bool,
    pub derefed: bool,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum TypeInnerOf<T: TypeFamily> {
    RecursionPoint(T::RecursionPoint),
    Type(TypeOf<T>),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum TypeUnitOf<T: TypeFamily> {
    Normal {
        id: TypeId,
        args: Vec<TypeInnerOf<T>>,
    },
    Fn(
        BTreeMap<LambdaId<T::LambdaTag>, T::LambdaCtx>,
        TypeInnerOf<T>,
        TypeInnerOf<T>,
    ),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
struct IntermediateTypeF;
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct TypeForHashF;
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct NormalTypeF;

pub trait TypeFamily {
    type RecursionPoint: Eq + Ord + Clone + std::hash::Hash + std::fmt::Debug + BrokenLinkCheck;
    type LambdaTag: Eq
        + Ord
        + Clone
        + std::hash::Hash
        + std::fmt::Debug
        + BrokenLinkCheck
        + DisplayTypeWithEnv;
    type LambdaCtx: Eq + Ord + Clone + std::hash::Hash + DebugCtx + BrokenLinkCheck;
}

impl TypeFamily for IntermediateTypeF {
    type RecursionPoint = IndexOrPointer;
    type LambdaTag = TypeInnerOf<IntermediateTypeF>;
    type LambdaCtx = Vec<TypeInnerOf<Self>>;
}

impl TypeFamily for TypeForHashF {
    type RecursionPoint = u32;
    type LambdaTag = TypeInnerOf<Self>;
    type LambdaCtx = ();
}

impl TypeFamily for NormalTypeF {
    type RecursionPoint = u32;
    type LambdaTag = id_generator::Id<TypeIdTag>;
    type LambdaCtx = Vec<TypeInnerOf<Self>>;
}

type IntermediateTypeUnit = TypeUnitOf<IntermediateTypeF>;
type IntermediateTypeInner = TypeInnerOf<IntermediateTypeF>;
pub type TypeForHash = TypeOf<TypeForHashF>;
pub type TypeUnitForHash = TypeUnitOf<TypeForHashF>;
pub type TypeInnerForHash = TypeInnerOf<TypeForHashF>;
pub type Type = TypeOf<NormalTypeF>;
pub type TypeUnit = TypeUnitOf<NormalTypeF>;
pub type TypeInner = TypeInnerOf<NormalTypeF>;

impl<T: TypeFamily> From<TypeUnitOf<T>> for TypeOf<T> {
    fn from(value: TypeUnitOf<T>) -> Self {
        TypeOf {
            ts: once(value).collect(),
            recursive: false,
            reference: false,
            derefed: false,
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum IndexOrPointer {
    Index(u32),
    Pointer(TypePointer),
}

impl<T: TypeFamily> TypeOf<T> {
    pub fn iter(&self) -> impl Iterator<Item = &TypeUnitOf<T>> {
        self.ts.iter()
    }

    pub fn len(&self) -> usize {
        self.ts.len()
    }

    pub fn deref(self) -> Self {
        debug_assert!(self.recursive);
        debug_assert!(self.reference);
        Self {
            derefed: true,
            ..self
        }
    }

    pub fn contains_broken_link_rec(&self, depth: u32) -> bool {
        let depth = self.recursive as u32 + depth;
        self.ts.iter().any(|t| match t {
            TypeUnitOf::Normal { id: _, args } => {
                args.iter().any(|a| a.contains_broken_link(depth))
            }
            TypeUnitOf::Fn(l, a, r) => {
                l.iter().any(|(l, ctx)| {
                    l.root_t.contains_broken_link(depth) || ctx.contains_broken_link(depth)
                }) || a.contains_broken_link(depth)
                    || r.contains_broken_link(depth)
            }
        })
    }

    pub fn contains_broken_link(&self) -> bool {
        self.contains_broken_link_rec(0)
    }
}

pub trait BrokenLinkCheck {
    fn contains_broken_link(&self, depth: u32) -> bool;
}

impl<T: TypeFamily> BrokenLinkCheck for TypeInnerOf<T> {
    fn contains_broken_link(&self, depth: u32) -> bool {
        match self {
            TypeInnerOf::RecursionPoint(d) => d.contains_broken_link(depth),
            TypeInnerOf::Type(t) => t.contains_broken_link_rec(depth),
        }
    }
}

impl BrokenLinkCheck for u32 {
    fn contains_broken_link(&self, depth: u32) -> bool {
        *self >= depth
    }
}

impl BrokenLinkCheck for IndexOrPointer {
    fn contains_broken_link(&self, depth: u32) -> bool {
        match self {
            IndexOrPointer::Index(i) => *i >= depth,
            IndexOrPointer::Pointer(_) => unimplemented!(),
        }
    }
}

impl BrokenLinkCheck for id_generator::Id<TypeIdTag> {
    fn contains_broken_link(&self, _depth: u32) -> bool {
        false
    }
}

impl BrokenLinkCheck for () {
    fn contains_broken_link(&self, _depth: u32) -> bool {
        false
    }
}

impl<T: BrokenLinkCheck> BrokenLinkCheck for Vec<T> {
    fn contains_broken_link(&self, depth: u32) -> bool {
        self.iter().any(|a| a.contains_broken_link(depth))
    }
}

#[derive(Debug, Default)]
pub struct TypeMemo {
    type_memo: FxHashMap<TypePointer, IntermediateTypeInner>,
    type_memo_for_hash: FxHashMap<TypePointer, IntermediateTypeInner>,
    pub minimized_pointers: FxHashSet<TypePointer>,
    pub ref_pointers: FxHashSet<TypePointer>,
    ref_checked_pointers: FxHashSet<TypePointer>,
}

fn remove_pointer_from_type_inner_for_hash(t: IntermediateTypeInner) -> TypeInnerForHash {
    match t {
        TypeInnerOf::RecursionPoint(IndexOrPointer::Pointer(_)) => {
            panic!()
        }
        TypeInnerOf::RecursionPoint(IndexOrPointer::Index(d)) => TypeInnerOf::RecursionPoint(d),
        TypeInnerOf::Type(TypeOf {
            ts,
            recursive,
            reference,
            derefed,
        }) => TypeInnerOf::Type(TypeOf {
            ts: ts
                .into_iter()
                .map(remove_pointer_from_type_unit_for_hash)
                .collect(),
            recursive,
            reference,
            derefed,
        }),
    }
}

fn remove_pointer_from_type_unit_for_hash(t: TypeUnitOf<IntermediateTypeF>) -> TypeUnitForHash {
    match t {
        TypeUnitOf::Normal { id, args } => TypeUnitOf::Normal {
            id,
            args: args
                .into_iter()
                .map(remove_pointer_from_type_inner_for_hash)
                .collect(),
        },
        TypeUnitOf::Fn(id, a, b) => TypeUnitOf::Fn(
            id.into_keys()
                .map(|l| (l.map_type(remove_pointer_from_type_inner_for_hash), ()))
                .collect(),
            remove_pointer_from_type_inner_for_hash(a),
            remove_pointer_from_type_inner_for_hash(b),
        ),
    }
}

fn remove_pointer_from_type_inner(
    t: IntermediateTypeInner,
    type_id_generator: &mut IdGenerator<TypeForHash, TypeIdTag>,
) -> TypeInner {
    match t {
        TypeInnerOf::RecursionPoint(IndexOrPointer::Pointer(_)) => {
            panic!()
        }
        TypeInnerOf::RecursionPoint(IndexOrPointer::Index(d)) => TypeInnerOf::RecursionPoint(d),
        TypeInnerOf::Type(TypeOf {
            ts,
            recursive,
            reference,
            derefed,
        }) => TypeInnerOf::Type(TypeOf {
            ts: ts
                .into_iter()
                .map(|t| remove_pointer_from_type_unit(t, type_id_generator))
                .collect(),
            recursive,
            reference,
            derefed,
        }),
    }
}

fn remove_pointer_from_type_unit(
    t: TypeUnitOf<IntermediateTypeF>,
    type_id_generator: &mut IdGenerator<TypeForHash, TypeIdTag>,
) -> TypeUnit {
    match t {
        TypeUnitOf::Normal { id, args } => TypeUnitOf::Normal {
            id,
            args: args
                .into_iter()
                .map(|t| remove_pointer_from_type_inner(t, type_id_generator))
                .collect(),
        },
        TypeUnitOf::Fn(id, a, b) => TypeUnitOf::Fn(
            id.into_iter()
                .map(|(l, ctx)| {
                    let l = l.map_type(|t| {
                        let t = remove_pointer_from_type_inner_for_hash(t);
                        debug_assert!(!t.contains_broken_link(0));
                        if let TypeInnerOf::Type(t) = t {
                            type_id_generator.get_or_insert(t)
                        } else {
                            panic!()
                        }
                    });
                    (
                        l,
                        ctx.into_iter()
                            .map(|t| remove_pointer_from_type_inner(t, type_id_generator))
                            .collect(),
                    )
                })
                .collect(),
            remove_pointer_from_type_inner(a, type_id_generator),
            remove_pointer_from_type_inner(b, type_id_generator),
        ),
    }
}

impl TypeMemo {
    pub fn get_type(
        &mut self,
        p: TypePointer,
        map: &mut PaddedTypeMap,
        type_id_generator: &mut IdGenerator<TypeForHash, TypeIdTag>,
    ) -> Type {
        let t = self.get_type_inner(p, &Default::default(), map, false);
        match remove_pointer_from_type_inner(t, type_id_generator) {
            TypeInnerOf::RecursionPoint(_) => panic!(),
            TypeInnerOf::Type(t) => {
                debug_assert!(!t.contains_broken_link());
                t
            }
        }
    }

    pub fn get_type_for_hash(&mut self, p: TypePointer, map: &mut PaddedTypeMap) -> TypeForHash {
        let t = self.get_type_inner(p, &Default::default(), map, true);
        match remove_pointer_from_type_inner_for_hash(t) {
            TypeInnerOf::RecursionPoint(_) => panic!(),
            TypeInnerOf::Type(t) => {
                debug_assert!(!t.contains_broken_link());
                t
            }
        }
    }

    fn get_lambda_ids(
        &mut self,
        p: TypePointer,
        trace: &FxHashSet<TypePointer>,
        map: &mut PaddedTypeMap,
        for_hash: bool,
    ) -> BTreeMap<LambdaId<IntermediateTypeInner>, <IntermediateTypeF as TypeFamily>::LambdaCtx>
    {
        let p = map.find(p);
        let Terminal::LambdaId(ids) = map.dereference_without_find(p) else {
            panic!()
        };
        let mut new_ids = BTreeMap::new();
        let empty_trace;
        let trace_for_id = if for_hash {
            trace
        } else {
            empty_trace = Default::default();
            &empty_trace
        };
        for (id, ctx) in ids.clone() {
            let id = id.map_type(|p| self.get_type_inner(p, trace_for_id, map, true));
            new_ids.insert(
                id,
                ctx.into_iter()
                    .map(|c| self.get_type_inner(c, trace, map, for_hash))
                    .collect(),
            );
        }
        new_ids
    }

    fn get_type_inner(
        &mut self,
        p: TypePointer,
        trace: &FxHashSet<TypePointer>,
        map: &mut PaddedTypeMap,
        for_hash: bool,
    ) -> IntermediateTypeInner {
        let p = map.find(p);
        if for_hash {
            if let Some(t) = self.type_memo_for_hash.get(&p) {
                debug_assert!(!trace.contains(&p));
                return t.clone();
            }
        } else if let Some(t) = self.type_memo.get(&p) {
            return t.clone();
        }
        if trace.contains(&p) {
            return TypeInnerOf::RecursionPoint(IndexOrPointer::Pointer(p));
        }
        let mut trace = trace.clone();
        trace.insert(p);
        let t = match &map.dereference_without_find(p) {
            Terminal::TypeMap(type_map) => {
                let mut ts = Vec::new();
                for (type_id, normal_type) in type_map.normals.clone() {
                    let a = self.get_type_from_id_and_args_rec(
                        type_id,
                        &normal_type,
                        &trace,
                        map,
                        for_hash,
                    );
                    ts.push(a)
                }
                TypeInnerOf::Type(TypeOf {
                    ts,
                    recursive: false,
                    reference: false,
                    derefed: false,
                })
            }
            Terminal::LambdaId(_) => panic!(),
        };
        let r = replace_pointer(t, p, 0);
        let mut t = r.t;
        if r.replaced {
            if let TypeInnerOf::Type(t) = &mut t {
                t.recursive = true;
            } else {
                panic!()
            }
        };
        if self.ref_pointers.contains(&p) {
            if let TypeInnerOf::Type(t) = &mut t {
                t.reference = true;
            } else {
                panic!()
            }
        } else {
            debug_assert!(self.ref_checked_pointers.contains(&p));
            #[cfg(debug_assertions)]
            if let TypeInnerOf::Type(t) = &mut t {
                assert!(!t.reference);
            } else {
                panic!()
            }
        }
        if !r.contains_pointer {
            let o = if for_hash {
                self.type_memo_for_hash.insert(p, t.clone())
            } else {
                self.type_memo.insert(p, t.clone())
            };
            debug_assert!(o.is_none());
        }
        t
    }

    fn get_type_from_id_and_args_rec(
        &mut self,
        id: TypeId,
        args: &[TypePointer],
        trace: &FxHashSet<TypePointer>,
        map: &mut PaddedTypeMap,
        for_hash: bool,
    ) -> IntermediateTypeUnit {
        if let TypeId::Intrinsic(IntrinsicTypeTag::Fn) = id {
            debug_assert_eq!(args.len(), 3);
            let mut args = args.iter();
            let a = self.get_type_inner(*args.next().unwrap(), trace, map, for_hash);
            let b = self.get_type_inner(*args.next().unwrap(), trace, map, for_hash);
            let lambda_id = self.get_lambda_ids(*args.next().unwrap(), trace, map, for_hash);
            TypeUnitOf::Fn(lambda_id, a, b)
        } else {
            TypeUnitOf::Normal {
                id,
                args: args
                    .iter()
                    .map(|t| self.get_type_inner(*t, trace, map, for_hash))
                    .collect(),
            }
        }
    }

    pub fn collect_ref_pointers(&mut self, p: TypePointer, map: &mut PaddedTypeMap) {
        self.collect_ref_pointers_aux(p, &Default::default(), &Default::default(), map)
    }

    fn collect_ref_pointers_aux(
        &mut self,
        p: TypePointer,
        ref_candidates: &FxHashSet<TypePointer>,
        trace: &FxHashSet<TypePointer>,
        map: &mut PaddedTypeMap,
    ) {
        let p = map.find(p);
        if self.ref_checked_pointers.contains(&p) {
            return;
        }
        if trace.contains(&p) {
            if ref_candidates.contains(&p) {
                let new = self.ref_pointers.insert(p);
                debug_assert!(new);
                let new = self.ref_checked_pointers.insert(p);
                debug_assert!(new);
            }
            return;
        }
        let mut trace = trace.clone();
        trace.insert(p);
        match map.dereference_without_find(p) {
            Terminal::TypeMap(t) => {
                let t = t.normals.clone();
                let union = if t.len() == 1 {
                    let (id, ts) = t.iter().next().unwrap();
                    match id {
                        TypeId::Intrinsic(IntrinsicTypeTag::Fn) => match map.dereference(ts[2]) {
                            Terminal::TypeMap(_) => panic!(),
                            Terminal::LambdaId(l) => l.len() > 1,
                        },
                        _ => false,
                    }
                } else {
                    t.len() > 1
                };
                let mut new_ref_candidates;
                let ref_candidates = if union {
                    new_ref_candidates = ref_candidates.clone();
                    new_ref_candidates.insert(p);
                    &new_ref_candidates
                } else {
                    ref_candidates
                };
                for (id, ts) in t {
                    match id {
                        TypeId::Intrinsic(id) => match id {
                            IntrinsicTypeTag::Fn => {
                                self.collect_ref_pointers_aux(ts[2], ref_candidates, &trace, map);
                                for t in &ts[..2] {
                                    self.collect_ref_pointers_aux(
                                        *t,
                                        &Default::default(),
                                        &trace,
                                        map,
                                    );
                                }
                            }
                            _ => {
                                for t in ts {
                                    self.collect_ref_pointers_aux(
                                        t,
                                        &Default::default(),
                                        &trace,
                                        map,
                                    );
                                }
                            }
                        },
                        TypeId::UserDefined(_) => {
                            for t in ts {
                                self.collect_ref_pointers_aux(t, ref_candidates, &trace, map);
                            }
                        }
                    }
                }
            }
            Terminal::LambdaId(l) => {
                for (id, ctx) in l.clone() {
                    for t in ctx {
                        self.collect_ref_pointers_aux(t, ref_candidates, &trace, map);
                    }
                    self.collect_ref_pointers_aux(id.root_t, &Default::default(), &trace, map);
                }
            }
        }
        self.ref_checked_pointers.insert(p);
    }
}

struct ReplacePointerResult {
    t: IntermediateTypeInner,
    replaced: bool,
    contains_pointer: bool,
}

fn replace_pointer(
    t: IntermediateTypeInner,
    from: TypePointer,
    depth: u32,
) -> ReplacePointerResult {
    match t {
        TypeInnerOf::RecursionPoint(IndexOrPointer::Index(i)) => ReplacePointerResult {
            t: TypeInnerOf::RecursionPoint(IndexOrPointer::Index(i)),
            replaced: false,
            contains_pointer: i > depth,
        },
        TypeInnerOf::RecursionPoint(IndexOrPointer::Pointer(i)) => {
            if i == from {
                ReplacePointerResult {
                    t: TypeInnerOf::RecursionPoint(IndexOrPointer::Index(depth)),
                    replaced: true,
                    contains_pointer: false,
                }
            } else {
                ReplacePointerResult {
                    t: TypeInnerOf::RecursionPoint(IndexOrPointer::Pointer(i)),
                    replaced: false,
                    contains_pointer: true,
                }
            }
        }
        TypeInnerOf::Type(t) => {
            let depth = t.recursive as u32 + depth;
            let mut new_t = Vec::new();
            let mut replaced = false;
            let mut contains_pointer = false;
            use TypeUnitOf::*;
            for u in t.ts {
                match u {
                    Normal { id, args } => {
                        let args = args
                            .into_iter()
                            .map(|arg| {
                                let r = replace_pointer(arg, from, depth);
                                replaced |= r.replaced;
                                contains_pointer |= r.contains_pointer;
                                r.t
                            })
                            .collect();
                        new_t.push(Normal { id, args });
                    }
                    Fn(l, a, b) => {
                        let l = l
                            .into_iter()
                            .map(|(l, ctx)| {
                                (
                                    l.map_type(|t| {
                                        let r = replace_pointer(t, from, depth);
                                        replaced |= r.replaced;
                                        contains_pointer |= r.contains_pointer;
                                        r.t
                                    }),
                                    ctx.into_iter()
                                        .map(|c| {
                                            let r = replace_pointer(c, from, depth);
                                            replaced |= r.replaced;
                                            contains_pointer |= r.contains_pointer;
                                            r.t
                                        })
                                        .collect(),
                                )
                            })
                            .collect();
                        let r = replace_pointer(a, from, depth);
                        replaced |= r.replaced;
                        contains_pointer |= r.contains_pointer;
                        let a = r.t;
                        let r = replace_pointer(b, from, depth);
                        replaced |= r.replaced;
                        contains_pointer |= r.contains_pointer;
                        let b = r.t;
                        new_t.push(Fn(l, a, b));
                    }
                }
            }
            ReplacePointerResult {
                t: TypeInnerOf::Type(TypeOf {
                    ts: new_t,
                    recursive: t.recursive,
                    reference: t.reference,
                    derefed: t.derefed,
                }),
                replaced,
                contains_pointer,
            }
        }
    }
}

pub enum GetTagNormalResult {
    NotTagged,
    Impossible,
    Tagged(u32, TypeUnitOf<NormalTypeF>),
}

pub fn get_tag_normal(ot: &Type, type_id: TypeId) -> GetTagNormalResult {
    debug_assert_ne!(type_id, TypeId::Intrinsic(IntrinsicTypeTag::Fn));
    let mut tag = 0;
    let mut result = None;
    for t in ot.ts.clone() {
        let t = if ot.recursive {
            t.replace_index(ot, 0)
        } else {
            t
        };
        match &t {
            TypeUnitOf::Normal { id, .. } if *id == type_id => {
                debug_assert!(result.is_none());
                result = Some((tag, t));
                tag += 1;
            }
            TypeUnitOf::Fn(lambda_ids, _, _) => {
                tag += lambda_ids.len() as u32;
            }
            _ => {
                tag += 1;
            }
        }
    }
    match result {
        Some((tag_of_t, t)) => {
            if tag == 1 {
                GetTagNormalResult::NotTagged
            } else {
                GetTagNormalResult::Tagged(tag_of_t, t)
            }
        }
        None => GetTagNormalResult::Impossible,
    }
}

impl TypeInner {
    fn replace_index(self, to: &Type, depth: u32) -> Self {
        match self {
            TypeInnerOf::RecursionPoint(a) if a == depth => TypeInnerOf::Type(to.clone()),
            TypeInnerOf::RecursionPoint(a) => TypeInnerOf::RecursionPoint(a),
            TypeInnerOf::Type(TypeOf {
                ts,
                recursive,
                reference,
                derefed,
            }) => TypeInnerOf::Type(TypeOf {
                ts: ts
                    .into_iter()
                    .map(|t| t.replace_index(to, depth + recursive as u32))
                    .collect(),
                recursive,
                reference,
                derefed,
            }),
        }
    }
}

impl TypeUnit {
    pub fn replace_index(self, to: &Type, depth: u32) -> Self {
        match self {
            TypeUnitOf::Normal { id, args } => TypeUnitOf::Normal {
                id,
                args: args
                    .into_iter()
                    .map(|t| t.replace_index(to, depth))
                    .collect(),
            },
            TypeUnitOf::Fn(ids, a, b) => TypeUnitOf::Fn(
                ids.into_iter()
                    .map(|(id, ctx)| {
                        (
                            id,
                            ctx.into_iter()
                                .map(|t| t.replace_index(to, depth))
                                .collect(),
                        )
                    })
                    .collect(),
                a.replace_index(to, depth),
                b.replace_index(to, depth),
            ),
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum Precedence {
    Strong = 0,
    Fn = 1,
    Weak = 2,
}

use Precedence as P;

pub trait DisplayTypeWithEnv {
    fn fmt_with_env(
        &self,
        p: Precedence,
        f: &mut std::fmt::Formatter<'_>,
        env: &ConstructorNames,
    ) -> std::fmt::Result;
}

pub struct DisplayTypeWithEnvStruct<'a, T: DisplayTypeWithEnv>(pub &'a T, pub &'a ConstructorNames);

struct DisplayTypeHelper<'a, T: DisplayTypeWithEnv>(&'a T, Precedence, &'a ConstructorNames);

impl<T: DisplayTypeWithEnv> Display for DisplayTypeHelper<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt_with_env(self.1, f, self.2)
    }
}

impl<T: DisplayTypeWithEnv> Display for DisplayTypeWithEnvStruct<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt_with_env(P::Weak, f, self.1)
    }
}

impl<R: TypeFamily> DisplayTypeWithEnv for TypeOf<R> {
    fn fmt_with_env(
        &self,
        mut p: Precedence,
        f: &mut std::fmt::Formatter<'_>,
        env: &ConstructorNames,
    ) -> std::fmt::Result {
        if self.recursive {
            write!(f, "rec ")?;
            p = P::Strong;
        }
        if self.reference {
            write!(f, "&")?;
            p = P::Strong;
        }
        match self.ts.len() {
            0 => write!(f, "Never"),
            1 => self.ts.first().unwrap().fmt_with_env(p, f, env),
            _ => write!(
                f,
                "({})",
                self.ts
                    .iter()
                    .format_with(" | ", |t, f| f(&DisplayTypeHelper(t, P::Strong, env)))
            ),
        }?;
        Ok(())
    }
}

impl<R: TypeFamily> DisplayTypeWithEnv for TypeInnerOf<R> {
    fn fmt_with_env(
        &self,
        p: Precedence,
        f: &mut std::fmt::Formatter<'_>,
        env: &ConstructorNames,
    ) -> std::fmt::Result {
        match self {
            TypeInnerOf::RecursionPoint(d) => {
                write!(f, "d{d:?}")
            }
            TypeInnerOf::Type(t) => t.fmt_with_env(p, f, env),
        }
    }
}

impl<R: TypeFamily> DisplayTypeWithEnv for TypeUnitOf<R> {
    fn fmt_with_env(
        &self,
        p: Precedence,
        f: &mut std::fmt::Formatter<'_>,
        env: &ConstructorNames,
    ) -> std::fmt::Result {
        use TypeUnitOf::*;
        match self {
            Normal { args, id } => {
                debug_assert_ne!(*id, TypeId::Intrinsic(IntrinsicTypeTag::Fn));
                match id {
                    TypeId::UserDefined(u) => {
                        write!(f, "{}", env.get(*u))?;
                    }
                    TypeId::Intrinsic(d) => {
                        write!(f, "{d:?}")?;
                    }
                }
                if !args.is_empty() {
                    write!(
                        f,
                        "[{}]",
                        args.iter().format_with(", ", |a, f| f(&DisplayTypeHelper(
                            a,
                            P::Weak,
                            env
                        )))
                    )?;
                };
                Ok(())
            }
            Fn(_id, a, b) => {
                if p == P::Strong {
                    write!(f, "(")?;
                }
                #[cfg(feature = "display-fn-id")]
                {
                    let id_paren = _id.len() >= 2;
                    write!(
                        f,
                        "{} -{}{}{}-> ",
                        DisplayTypeHelper(a, P::Strong, env),
                        if id_paren { "(" } else { "" },
                        _id.iter()
                            .format_with(" | ", |(a, _), f| f(&DisplayTypeHelper(a, P::Fn, env))),
                        if id_paren { ")" } else { "" },
                    )?;
                    b.fmt_with_env(P::Fn, f, env)?;
                }
                #[cfg(not(feature = "display-fn-id"))]
                write!(
                    f,
                    "{} -> {}",
                    DisplayTypeHelper(a, P::Strong, env),
                    DisplayTypeHelper(b, P::Fn, env)
                )?;
                if p == P::Strong {
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }
}

impl<R: DisplayTypeWithEnv> DisplayTypeWithEnv for LambdaId<R> {
    fn fmt_with_env(
        &self,
        _p: Precedence,
        f: &mut std::fmt::Formatter<'_>,
        env: &ConstructorNames,
    ) -> std::fmt::Result {
        write!(f, "f{}(", self.id,)?;
        self.root_t.fmt_with_env(P::Strong, f, env)?;
        write!(f, ")")
    }
}

impl DisplayTypeWithEnv for id_generator::Id<TypeIdTag> {
    fn fmt_with_env(
        &self,
        _p: Precedence,
        f: &mut std::fmt::Formatter<'_>,
        _env: &ConstructorNames,
    ) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl<R: TypeFamily> fmt::Debug for TypeOf<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.recursive {
            write!(f, "rec ")?;
        }
        if self.reference {
            write!(f, "&(")?;
        }
        match self.ts.len() {
            0 => write!(f, "Never"),
            1 => write!(f, "{:?}", self.ts.first().unwrap()),
            _ => write!(f, "({:?})", self.ts.iter().format(" | ")),
        }?;
        if self.reference {
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl<R: TypeFamily> fmt::Debug for TypeInnerOf<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeInnerOf::RecursionPoint(d) => {
                write!(f, "d{d:?}")
            }
            TypeInnerOf::Type(t) => write!(f, "{t:?}"),
        }
    }
}

impl<R: TypeFamily> fmt::Debug for TypeUnitOf<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use TypeUnitOf::*;
        match self {
            Normal { args, id } => {
                debug_assert_ne!(*id, TypeId::Intrinsic(IntrinsicTypeTag::Fn));
                if args.is_empty() {
                    write!(f, "{id}")
                } else {
                    write!(f, "{}[{:?}]", id, args.iter().format(", "))
                }
            }
            Fn(id, a, b) => {
                let id_paren = id.len() >= 2;
                write!(
                    f,
                    "({a:?}) -{}{}{}-> {b:?}",
                    if id_paren { "(" } else { "" },
                    id.iter().format_with(" | ", |(a, ctx), f| f(&format_args!(
                        "{}{}",
                        a,
                        DebugCtxS(ctx)
                    ))),
                    if id_paren { ")" } else { "" },
                )
            }
        }
    }
}

pub trait DebugCtx {
    fn ctx_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
}

impl DebugCtx for () {
    fn ctx_fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Ok(())
    }
}

impl<T: fmt::Debug> DebugCtx for Vec<T> {
    fn ctx_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({:?})", self.iter().format(", "))
    }
}

struct DebugCtxS<T>(T);

impl<T: DebugCtx> Display for DebugCtxS<&T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.ctx_fmt(f)
    }
}
