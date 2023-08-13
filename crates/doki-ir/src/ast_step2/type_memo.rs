use super::{LambdaId, TypeIdTag};
use crate::ast_step1::{ConstructorNames, PaddedTypeMap, Terminal, TypeId, TypePointer};
use crate::intrinsics::IntrinsicTypeTag;
use crate::util::id_generator::{self, IdGenerator};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::BTreeMap;
use std::fmt::{self, Display, Formatter};
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
pub enum TypeTag<T: TypeFamily> {
    TypeId(TypeId),
    LambdaId(LambdaId<T::LambdaTag>),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct TypeUnitOf<T: TypeFamily> {
    id: TypeTag<T>,
    args: Vec<TypeInnerOf<T>>,
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
pub type TypeInnerForHash = TypeInnerOf<TypeForHashF>;
pub type Type = TypeOf<NormalTypeF>;
pub type TypeInner = TypeInnerOf<NormalTypeF>;

impl<T: TypeFamily> From<TypeUnitOf<T>> for TypeOf<T> {
    fn from(value: TypeUnitOf<T>) -> Self {
        TypeOf {
            ts: Rc::new(vec![value]),
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
        self.ts
            .iter()
            .any(|TypeUnitOf { id: _, args }| args.iter().any(|a| a.contains_broken_link(depth)))
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
        map: &PaddedTypeMap,
        depth: u32,
    ) -> BTreeMap<LambdaId<TypeInnerForHash>, ()> {
        let p = map.find_imm(p);
        let Terminal::LambdaId(ids) = map.dereference_without_find(p) else {
            panic!()
        };
        let mut new_ids = BTreeMap::new();
        for id in ids.keys().copied().collect_vec() {
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
                for (id, args) in type_map.normals.clone() {
                    if let TypeId::Intrinsic(IntrinsicTypeTag::Fn) = id {
                        debug_assert_eq!(args.len(), 3);
                        let mut args = args.iter();
                        let a = self.get_type_inner(*args.next().unwrap(), map);
                        let b = self.get_type_inner(*args.next().unwrap(), map);
                        ts.push(TypeUnitOf {
                            id: TypeTag::TypeId(TypeId::Intrinsic(IntrinsicTypeTag::Fn)),
                            args: vec![a, b],
                        });
                        let l = map.find(*args.next().unwrap());
                        for (id, ctx) in self.get_lambda_ids_pointer(l, map).clone() {
                            ts.push(TypeUnitOf {
                                id: TypeTag::LambdaId(id),
                                args: ctx.iter().map(|c| self.get_type_inner(*c, map)).collect(),
                            });
                        }
                    } else {
                        ts.push(TypeUnitOf {
                            id: TypeTag::TypeId(id),
                            args: args.iter().map(|t| self.get_type_inner(*t, map)).collect(),
                        })
                    }
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
        map: &PaddedTypeMap,
        depth: u32,
    ) -> TypeInnerForHash {
        let p = map.find_imm(p);
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
                for (id, args) in type_map.normals.iter() {
                    if let TypeId::Intrinsic(IntrinsicTypeTag::Fn) = id {
                        debug_assert_eq!(args.len(), 3);
                        let mut args = args.iter();
                        let a = self.get_type_inner_for_hash(
                            *args.next().unwrap(),
                            trace,
                            used_trace,
                            map,
                            depth,
                        );
                        let b = self.get_type_inner_for_hash(
                            *args.next().unwrap(),
                            trace,
                            used_trace,
                            map,
                            depth,
                        );
                        ts.push(TypeUnitOf {
                            id: TypeTag::TypeId(TypeId::Intrinsic(IntrinsicTypeTag::Fn)),
                            args: vec![a, b],
                        });
                        let lambda_id = self.get_lambda_ids_for_hash(
                            *args.next().unwrap(),
                            trace,
                            used_trace,
                            map,
                            depth,
                        );
                        for (id, ()) in lambda_id {
                            ts.push(TypeUnitOf {
                                id: TypeTag::LambdaId(id),
                                args: Vec::new(),
                            });
                        }
                    } else {
                        ts.push(TypeUnitOf {
                            id: TypeTag::TypeId(*id),
                            args: args
                                .iter()
                                .map(|t| {
                                    self.get_type_inner_for_hash(*t, trace, used_trace, map, depth)
                                })
                                .collect(),
                        })
                    }
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

    pub fn collect_ref_pointers(&mut self, p: TypePointer, map: &PaddedTypeMap) {
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
        map: &PaddedTypeMap,
    ) {
        let p = map.find_imm(p);
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
                let is_union = t
                    .normals
                    .iter()
                    .map(|(id, ts)| match id {
                        TypeId::Intrinsic(IntrinsicTypeTag::Fn) => match map.dereference_imm(ts[2])
                        {
                            Terminal::TypeMap(_) => panic!(),
                            Terminal::LambdaId(l) => l.len(),
                        },
                        _ => 1,
                    })
                    .sum::<usize>()
                    > 1;
                let mut new_trace;
                let trace = if is_union {
                    divergent_stopper = Some(DivergentStopper::Union(p));
                    new_trace = Vec::new();
                    &mut new_trace
                } else {
                    trace.push(p);
                    trace
                };
                trace_map.insert(p);
                for (id, ts) in &t.normals {
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
                                        *t,
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
                                    *t,
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
                for (id, ctx) in l {
                    for t in ctx {
                        self.collect_ref_pointers_aux(*t, trace_map, trace, divergent_stopper, map);
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
            _ => {
                let mut function = None;
                let mut fn_contexts = Vec::new();
                let mut normals = Vec::new();
                for t in self.ts.iter() {
                    match &t.id {
                        TypeTag::TypeId(TypeId::Intrinsic(IntrinsicTypeTag::Fn)) => {
                            function = Some((&t.args[0], &t.args[1]));
                        }
                        TypeTag::TypeId(u) => {
                            normals.push((u, &t.args));
                        }
                        TypeTag::LambdaId(l) => fn_contexts.push(l),
                    }
                }
                let is_single = normals.len() + function.is_some() as usize == 1;
                let paren = p == P::Strong || !is_single || function.is_some() && p == P::Fn;
                if paren {
                    write!(f, "(")?;
                }
                if let Some(first) = normals.pop() {
                    let w = |f: &mut Formatter, id, args: &[TypeInnerOf<R>]| {
                        match id {
                            TypeId::UserDefined(i) => write!(f, "{}", env.get(i))?,
                            TypeId::Intrinsic(i) => write!(f, "{i:?}")?,
                        };
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
                    };
                    w(f, *first.0, first.1)?;
                    for (id, args) in normals {
                        write!(f, " | ")?;
                        w(f, *id, args)?;
                    }
                    write!(f, " | ")?;
                }
                if let Some((arg, ret)) = function {
                    #[cfg(feature = "display-fn-id")]
                    {
                        let id_paren = fn_contexts.len() >= 2;
                        write!(
                            f,
                            "{} -{}{}{}-> ",
                            DisplayTypeHelper(arg, P::Strong, env),
                            if id_paren { "(" } else { "" },
                            fn_contexts
                                .iter()
                                .format_with(" | ", |a, f| f(&DisplayTypeHelper(*a, P::Fn, env))),
                            if id_paren { ")" } else { "" },
                        )?;
                        ret.fmt_with_env(P::Fn, f, env)?;
                    }
                    #[cfg(not(feature = "display-fn-id"))]
                    write!(
                        f,
                        "{} -> {}",
                        DisplayTypeHelper(arg, P::Strong, env),
                        DisplayTypeHelper(ret, P::Fn, env)
                    )?;
                } else {
                    debug_assert!(fn_contexts.is_empty());
                }
                if paren {
                    write!(f, ")")?;
                }
                Ok(())
            }
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
        match &self.id {
            TypeTag::TypeId(TypeId::Intrinsic(IntrinsicTypeTag::Fn)) => {
                write!(f, "({:?}) -> {:?}", self.args[0], self.args[1])
            }
            TypeTag::TypeId(id) => {
                write!(f, "{id}")
            }
            TypeTag::LambdaId(l) => {
                write!(f, "{l}")
            }
        }?;
        if !self.args.is_empty() {
            write!(f, "[{:?}]", self.args.iter().format(", "))?;
        }
        Ok(())
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
