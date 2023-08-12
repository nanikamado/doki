use super::{LambdaId, TypeIdTag};
use crate::ast_step1::{ConstructorNames, PaddedTypeMap, Terminal, TypeId, TypePointer};
use crate::intrinsics::IntrinsicTypeTag;
use crate::util::id_generator::{self, IdGenerator};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::BTreeMap;
use std::fmt::{self, Display};
use std::iter::once;
use std::rc::Rc;

#[derive(PartialEq, Eq, PartialOrd, Ord, Default, Clone, Hash)]
pub struct TypeOf<T: TypeFamily> {
    ts: Rc<Vec<TypeUnitOf<T>>>,
    pub reference: bool,
    pub diverging: bool,
    pub derefed: bool,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum TypeInnerOf<T: TypeFamily> {
    RecursionPoint(u32),
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
pub struct TypeForHashF;
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct NormalTypeF;

pub trait TypeFamily {
    type LambdaTag: Eq
        + Ord
        + Clone
        + std::hash::Hash
        + std::fmt::Debug
        + BrokenLinkCheck
        + DisplayTypeWithEnv;
    type LambdaCtx: Eq + Ord + Clone + std::hash::Hash + DebugCtx + BrokenLinkCheck;
}

impl TypeFamily for TypeForHashF {
    type LambdaTag = TypeInnerOf<Self>;
    type LambdaCtx = ();
}

impl TypeFamily for NormalTypeF {
    type LambdaTag = id_generator::Id<TypeIdTag>;
    type LambdaCtx = Vec<TypeInnerOf<Self>>;
}

pub type TypeForHash = TypeOf<TypeForHashF>;
pub type TypeUnitForHash = TypeUnitOf<TypeForHashF>;
pub type TypeInnerForHash = TypeInnerOf<TypeForHashF>;
pub type Type = TypeOf<NormalTypeF>;
pub type TypeUnit = TypeUnitOf<NormalTypeF>;
pub type TypeInner = TypeInnerOf<NormalTypeF>;

impl<T: TypeFamily> From<TypeUnitOf<T>> for TypeOf<T> {
    fn from(value: TypeUnitOf<T>) -> Self {
        TypeOf {
            ts: Rc::new(once(value).collect()),
            reference: false,
            derefed: false,
            diverging: false,
        }
    }
}

impl<T: TypeFamily> TypeOf<T> {
    pub fn iter(&self) -> impl Iterator<Item = &TypeUnitOf<T>> {
        self.ts.iter()
    }

    pub fn len(&self) -> usize {
        self.ts.len()
    }

    pub fn deref(self) -> Self {
        debug_assert!(self.reference);
        Self {
            derefed: true,
            ..self
        }
    }

    pub fn contains_broken_link_rec(&self, depth: u32) -> bool {
        let depth = depth + 1;
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
    type_memo: FxHashMap<TypePointer, TypeInner>,
    type_memo_for_hash: FxHashMap<TypePointer, TypeInnerForHash>,
    pub ref_pointers: FxHashSet<TypePointer>,
    pub diverging_pointers: FxHashSet<TypePointer>,
    pub ref_checked_pointers: FxHashSet<TypePointer>,
    pub type_id_generator: IdGenerator<TypeForHash, TypeIdTag>,
    trace: FxHashMap<TypePointer, usize>,
    used_trace: FxHashSet<TypePointer>,
    lambda_ids_pointer_memo:
        FxHashMap<TypePointer, BTreeMap<LambdaId<id_generator::Id<TypeIdTag>>, Vec<TypePointer>>>,
}

impl TypeMemo {
    pub fn get_type(&mut self, p: TypePointer, map: &mut PaddedTypeMap) -> Type {
        debug_assert!(self.trace.is_empty());
        debug_assert!(self.used_trace.is_empty());
        let t = self.get_type_inner(p, map);
        match t {
            TypeInnerOf::RecursionPoint(_) => panic!(),
            TypeInnerOf::Type(t) => {
                debug_assert!(!t.contains_broken_link());
                t
            }
        }
    }

    pub fn get_type_for_hash(&mut self, p: TypePointer, map: &mut PaddedTypeMap) -> TypeForHash {
        map.minimize(p);
        let t = self.get_type_inner_for_hash(
            p,
            &mut Default::default(),
            &mut Default::default(),
            map,
            0,
        );
        match t {
            TypeInnerOf::RecursionPoint(_) => panic!(),
            TypeInnerOf::Type(t) => {
                debug_assert!(!t.contains_broken_link());
                t
            }
        }
    }

    pub fn get_lambda_ids(
        &mut self,
        p: TypePointer,
        map: &mut PaddedTypeMap,
    ) -> BTreeMap<LambdaId<id_generator::Id<TypeIdTag>>, <NormalTypeF as TypeFamily>::LambdaCtx>
    {
        let p = map.find(p);
        let Terminal::LambdaId(ids) = map.dereference_without_find(p) else {
            panic!()
        };
        let mut new_ids = BTreeMap::new();
        for (id, ctx) in ids.clone() {
            let id = id.map_type(|p| {
                let t = self.get_type_for_hash(p, map);
                debug_assert!(!t.contains_broken_link());
                self.type_id_generator.get_or_insert(t)
            });
            new_ids.insert(
                id,
                ctx.into_iter()
                    .map(|c| self.get_type_inner(c, map))
                    .collect(),
            );
        }
        new_ids
    }

    pub fn get_lambda_ids_pointer<'a>(
        &'a mut self,
        p: TypePointer,
        map: &mut PaddedTypeMap,
    ) -> &'a BTreeMap<LambdaId<id_generator::Id<TypeIdTag>>, Vec<TypePointer>> {
        let p = map.find(p);
        // Reason: false positive
        #[allow(clippy::map_entry)]
        if self.lambda_ids_pointer_memo.contains_key(&p) {
            &self.lambda_ids_pointer_memo[&p]
        } else {
            let Terminal::LambdaId(ids) = map.dereference_without_find(p) else {
                panic!()
            };
            let mut new_ids = BTreeMap::new();
            for (id, ctx) in ids.clone() {
                let id = id.map_type(|p| {
                    let t = self.get_type_for_hash(p, map);
                    debug_assert!(!t.contains_broken_link());
                    self.type_id_generator.get_or_insert(t)
                });
                new_ids.insert(id, ctx);
            }
            self.lambda_ids_pointer_memo.insert(p, new_ids);
            &self.lambda_ids_pointer_memo[&p]
        }
    }

    fn get_lambda_ids_for_hash(
        &mut self,
        p: TypePointer,
        trace: &mut FxHashMap<TypePointer, u32>,
        used_trace: &mut FxHashSet<TypePointer>,
        map: &mut PaddedTypeMap,
        depth: u32,
    ) -> BTreeMap<LambdaId<TypeInnerForHash>, <TypeForHashF as TypeFamily>::LambdaCtx> {
        let p = map.find(p);
        let Terminal::LambdaId(ids) = map.dereference_without_find(p) else {
            panic!()
        };
        let mut new_ids = BTreeMap::new();
        for (id, _ctx) in ids.clone() {
            let id =
                id.map_type(|p| self.get_type_inner_for_hash(p, trace, used_trace, map, depth));
            new_ids.insert(id, ());
        }
        new_ids
    }

    fn get_type_inner(&mut self, p: TypePointer, map: &mut PaddedTypeMap) -> TypeInner {
        let p = map.find(p);
        if let Some(t) = self.type_memo.get(&p) {
            return t.clone();
        }
        let depth = self.trace.len();
        if let Some(d) = self.trace.get(&p) {
            self.used_trace.insert(p);
            return TypeInnerOf::RecursionPoint((depth - *d - 1) as u32);
        }
        self.trace.insert(p, depth);
        let mut t = match &map.dereference_without_find(p) {
            Terminal::TypeMap(type_map) => {
                let mut ts = Vec::new();
                for (type_id, normal_type) in type_map.normals.clone() {
                    let a = self.get_type_from_id_and_args_rec(type_id, &normal_type, map);
                    ts.push(a)
                }
                TypeInnerOf::Type(TypeOf {
                    ts: Rc::new(ts),
                    reference: false,
                    derefed: false,
                    diverging: false,
                })
            }
            Terminal::LambdaId(_) => panic!(),
        };
        self.trace.remove(&p);
        if self.diverging_pointers.contains(&p) {
            if let TypeInnerOf::Type(t) = &mut t {
                t.diverging = true;
            } else {
                panic!()
            }
        } else if self.ref_pointers.contains(&p) {
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
        self.used_trace.remove(&p);
        if self.used_trace.is_empty() {
            let o = self.type_memo.insert(p, t.clone());
            debug_assert!(o.is_none());
        }
        t
    }

    fn get_type_inner_for_hash(
        &mut self,
        p: TypePointer,
        trace: &mut FxHashMap<TypePointer, u32>,
        used_trace: &mut FxHashSet<TypePointer>,
        map: &mut PaddedTypeMap,
        depth: u32,
    ) -> TypeInnerForHash {
        let p = map.find(p);
        if let Some(t) = self.type_memo_for_hash.get(&p) {
            debug_assert!(!trace.contains_key(&p));
            return t.clone();
        }
        if let Some(d) = trace.get(&p) {
            used_trace.insert(p);
            return TypeInnerOf::RecursionPoint(depth - *d - 1);
        }
        trace.insert(p, depth);
        let depth = depth + 1;
        let mut t = match &map.dereference_without_find(p) {
            Terminal::TypeMap(type_map) => {
                let mut ts = Vec::new();
                for (type_id, normal_type) in type_map.normals.clone() {
                    let a = self.get_type_from_id_and_args_rec_for_hash(
                        type_id,
                        &normal_type,
                        trace,
                        used_trace,
                        map,
                        depth,
                    );
                    ts.push(a)
                }
                TypeInnerOf::Type(TypeOf {
                    ts: Rc::new(ts),
                    reference: false,
                    derefed: false,
                    diverging: false,
                })
            }
            Terminal::LambdaId(_) => panic!(),
        };
        trace.remove(&p);
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
        if used_trace.is_empty() {
            let o = self.type_memo_for_hash.insert(p, t.clone());
            debug_assert!(o.is_none());
        }
        used_trace.remove(&p);
        t
    }

    fn get_type_from_id_and_args_rec(
        &mut self,
        id: TypeId,
        args: &[TypePointer],
        map: &mut PaddedTypeMap,
    ) -> TypeUnit {
        if let TypeId::Intrinsic(IntrinsicTypeTag::Fn) = id {
            debug_assert_eq!(args.len(), 3);
            let mut args = args.iter();
            let a = self.get_type_inner(*args.next().unwrap(), map);
            let b = self.get_type_inner(*args.next().unwrap(), map);
            let lambda_id = self.get_lambda_ids(*args.next().unwrap(), map);
            TypeUnitOf::Fn(lambda_id, a, b)
        } else {
            TypeUnitOf::Normal {
                id,
                args: args.iter().map(|t| self.get_type_inner(*t, map)).collect(),
            }
        }
    }

    fn get_type_from_id_and_args_rec_for_hash(
        &mut self,
        id: TypeId,
        args: &[TypePointer],
        trace: &mut FxHashMap<TypePointer, u32>,
        used_trace: &mut FxHashSet<TypePointer>,
        map: &mut PaddedTypeMap,
        depth: u32,
    ) -> TypeUnitForHash {
        if let TypeId::Intrinsic(IntrinsicTypeTag::Fn) = id {
            debug_assert_eq!(args.len(), 3);
            let mut args = args.iter();
            let a =
                self.get_type_inner_for_hash(*args.next().unwrap(), trace, used_trace, map, depth);
            let b =
                self.get_type_inner_for_hash(*args.next().unwrap(), trace, used_trace, map, depth);
            let lambda_id =
                self.get_lambda_ids_for_hash(*args.next().unwrap(), trace, used_trace, map, depth);
            TypeUnitOf::Fn(lambda_id, a, b)
        } else {
            TypeUnitOf::Normal {
                id,
                args: args
                    .iter()
                    .map(|t| self.get_type_inner_for_hash(*t, trace, used_trace, map, depth))
                    .collect(),
            }
        }
    }

    pub fn collect_ref_pointers(&mut self, p: TypePointer, map: &mut PaddedTypeMap) {
        self.collect_ref_pointers_aux(
            p,
            &mut Default::default(),
            &mut Vec::with_capacity(5),
            None,
            map,
        )
    }

    fn collect_ref_pointers_aux(
        &mut self,
        p: TypePointer,
        trace_map: &mut FxHashSet<TypePointer>,
        trace: &mut Vec<TypePointer>,
        mut divergent_stopper: Option<DivergentStopper>,
        map: &mut PaddedTypeMap,
    ) {
        let p = map.find(p);
        if self.ref_checked_pointers.contains(&p) {
            return;
        }
        if trace_map.contains(&p) {
            if trace.contains(&p) {
                for u in trace {
                    self.diverging_pointers.insert(*u);
                    self.ref_checked_pointers.insert(*u);
                }
            } else if let DivergentStopper::Union(u) = divergent_stopper.unwrap() {
                self.ref_pointers.insert(u);
                self.ref_checked_pointers.insert(u);
            }
            return;
        }
        match map.dereference_without_find(p) {
            Terminal::TypeMap(t) => {
                let t = t.normals.clone();
                let is_union = t
                    .iter()
                    .map(|(id, ts)| match id {
                        TypeId::Intrinsic(IntrinsicTypeTag::Fn) => match map.dereference(ts[2]) {
                            Terminal::TypeMap(_) => panic!(),
                            Terminal::LambdaId(l) => l.len(),
                        },
                        _ => 1,
                    })
                    .sum::<usize>()
                    > 1;
                let mut new_trace;
                let trace = if is_union {
                    // trace.clear();
                    divergent_stopper = Some(DivergentStopper::Union(p));
                    new_trace = Vec::new();
                    &mut new_trace
                } else {
                    trace.push(p);
                    trace
                };
                trace_map.insert(p);
                for (id, ts) in t {
                    match id {
                        TypeId::Intrinsic(id) => match id {
                            IntrinsicTypeTag::Fn => {
                                self.collect_ref_pointers_aux(
                                    ts[2],
                                    trace_map,
                                    trace,
                                    divergent_stopper,
                                    map,
                                );
                                for t in &ts[..2] {
                                    self.collect_ref_pointers_aux(
                                        *t,
                                        trace_map,
                                        &mut Vec::new(),
                                        Some(DivergentStopper::Indirect),
                                        map,
                                    );
                                }
                            }
                            _ => {
                                for t in ts {
                                    self.collect_ref_pointers_aux(
                                        t,
                                        trace_map,
                                        &mut Vec::new(),
                                        Some(DivergentStopper::Indirect),
                                        map,
                                    );
                                }
                            }
                        },
                        TypeId::UserDefined(_) => {
                            for t in ts {
                                self.collect_ref_pointers_aux(
                                    t,
                                    trace_map,
                                    trace,
                                    divergent_stopper,
                                    map,
                                );
                            }
                        }
                    }
                }
                if !is_union {
                    trace.pop().unwrap();
                }
                trace_map.remove(&p);
            }
            Terminal::LambdaId(l) => {
                for (id, ctx) in l.clone() {
                    for t in ctx {
                        self.collect_ref_pointers_aux(t, trace_map, trace, divergent_stopper, map);
                    }
                    self.collect_ref_pointers_aux(
                        id.root_t,
                        trace_map,
                        &mut Vec::new(),
                        Some(DivergentStopper::Indirect),
                        map,
                    );
                }
            }
        }
        self.ref_checked_pointers.insert(p);
    }
}

#[derive(Debug, Clone, Copy)]
enum DivergentStopper {
    Indirect,
    Union(TypePointer),
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

pub struct DisplayTypeWithEnvStructOption<'a, T: DisplayTypeWithEnv>(
    pub &'a Option<T>,
    pub &'a ConstructorNames,
);

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

impl<T: DisplayTypeWithEnv> Display for DisplayTypeWithEnvStructOption<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(t) = self.0 {
            t.fmt_with_env(P::Weak, f, self.1)
        } else {
            Ok(())
        }
    }
}

impl<R: TypeFamily> DisplayTypeWithEnv for TypeOf<R> {
    fn fmt_with_env(
        &self,
        mut p: Precedence,
        f: &mut std::fmt::Formatter<'_>,
        env: &ConstructorNames,
    ) -> std::fmt::Result {
        if self.diverging {
            write!(f, "!")?;
            p = P::Strong;
        }
        if self.derefed {
            write!(f, "*")?;
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
