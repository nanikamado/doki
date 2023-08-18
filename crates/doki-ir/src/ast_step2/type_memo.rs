use super::{LambdaId, TypeIdTag, TypeUnique};
use crate::ast_step1::{
    self, ConstructorNames, PaddedTypeMap, TypeId, TypePointer, TypeTagForBoxPoint,
};
use crate::intrinsics::IntrinsicTypeTag;
use crate::util::id_generator::IdGenerator;
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use std::collections::BTreeMap;
use std::fmt::{self, Display, Formatter};
use std::rc::Rc;

#[derive(PartialEq, Eq, PartialOrd, Ord, Default, Clone, Hash)]
pub struct TypeOf<T: TypeFamily> {
    ts: Rc<SmallVec<[TypeUnitOf<T>; 2]>>,
    pub diverging: bool,
    pub refed: bool,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum TypeInnerOf<T: TypeFamily> {
    RecursionPoint { i: u32, refed: bool },
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
    args: SmallVec<[TypeInnerOf<T>; 2]>,
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
    type LambdaTag = TypeUnique;
    type LambdaCtx = Vec<TypeInnerOf<Self>>;
}

pub type TypeForHash = TypeOf<TypeForHashF>;
pub type TypeInnerForHash = TypeInnerOf<TypeForHashF>;
pub type Type = TypeOf<NormalTypeF>;
pub type TypeInner = TypeInnerOf<NormalTypeF>;

impl<T: TypeFamily> From<TypeUnitOf<T>> for TypeOf<T> {
    fn from(value: TypeUnitOf<T>) -> Self {
        TypeOf {
            ts: Rc::new(smallvec::smallvec![value]),
            refed: false,
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
            TypeInnerOf::RecursionPoint { i, refed: _ } => i.contains_broken_link(depth),
            TypeInnerOf::Type(t) => t.contains_broken_link_rec(depth),
        }
    }
}

impl BrokenLinkCheck for u32 {
    fn contains_broken_link(&self, depth: u32) -> bool {
        *self >= depth
    }
}

impl BrokenLinkCheck for TypeUnique {
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
    pub type_id_generator: IdGenerator<TypeForHash, TypeIdTag>,
    trace: FxHashMap<TypePointer, usize>,
    used_trace: FxHashSet<TypePointer>,
    #[allow(clippy::type_complexity)]
    lambda_ids_pointer_memo:
        FxHashMap<TypePointer, BTreeMap<LambdaId<TypeUnique>, (u32, Vec<TypePointer>)>>,
}

impl TypeMemo {
    pub fn get_type(&mut self, p: TypePointer, map: &mut PaddedTypeMap) -> Type {
        debug_assert!(self.trace.is_empty());
        debug_assert!(self.used_trace.is_empty());
        let t = self.get_type_inner(p, map);
        match t {
            TypeInnerOf::RecursionPoint { .. } => panic!(),
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
            TypeInnerOf::RecursionPoint { .. } => panic!(),
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
    ) -> &'a BTreeMap<LambdaId<TypeUnique>, (u32, Vec<TypePointer>)> {
        let p = map.find(p);
        // Reason: false positive
        #[allow(clippy::map_entry)]
        if self.lambda_ids_pointer_memo.contains_key(&p) {
            &self.lambda_ids_pointer_memo[&p]
        } else {
            let mut new_ids = BTreeMap::new();
            for (original_id, args) in map
                .dereference_without_find(p)
                .functions
                .clone()
                .into_iter()
            {
                let id = original_id.map_type(|p| {
                    let t = self.get_type_for_hash(p, map);
                    debug_assert!(!t.contains_broken_link());
                    self.type_id_generator.get_or_insert(t)
                });
                new_ids.entry(id).or_insert((original_id.id, args));
            }
            self.lambda_ids_pointer_memo.insert(p, new_ids);
            &self.lambda_ids_pointer_memo[&p]
        }
    }

    fn get_type_inner(&mut self, p: TypePointer, map: &mut PaddedTypeMap) -> TypeInner {
        let p = map.find(p);
        if let Some(t) = self.type_memo.get(&p) {
            return t.clone();
        }
        let depth = self.trace.len();
        if let Some(d) = self.trace.get(&p) {
            self.used_trace.insert(p);
            return TypeInnerOf::RecursionPoint {
                i: (depth - *d - 1) as u32,
                refed: false,
            };
        }
        self.trace.insert(p, depth);
        let mut ts = SmallVec::new();
        let terminal = map.dereference_without_find(p);
        let reference_point = terminal.box_point.clone();
        let box_point = match reference_point {
            ast_step1::BoxPoint::Diverging => None,
            ast_step1::BoxPoint::Boxed(pss) => Some(pss),
            ast_step1::BoxPoint::NotSure => panic!(),
        };
        let set_refed = |t: TypeInner, boxed: Option<bool>| {
            if boxed.unwrap() {
                match t {
                    TypeInnerOf::RecursionPoint { i, .. } => {
                        TypeInnerOf::RecursionPoint { i, refed: true }
                    }
                    TypeInnerOf::Type(t) => TypeInnerOf::Type(TypeOf { refed: true, ..t }),
                }
            } else {
                t
            }
        };
        for (id, args) in terminal.type_map.clone() {
            let args = args.iter().map(|t| self.get_type_inner(*t, map));
            let args = if let Some(box_point) = &box_point {
                args.zip_eq(&box_point[&TypeTagForBoxPoint::Normal(id)])
                    .map(|(t, boxed)| set_refed(t, *boxed))
                    .collect()
            } else {
                args.collect()
            };
            ts.push(TypeUnitOf {
                id: TypeTag::TypeId(id),
                args,
            })
        }
        for (id, (original_id, ctx)) in self.get_lambda_ids_pointer(p, map).clone() {
            let args = ctx.iter().map(|c| self.get_type_inner(*c, map));
            let args = if let Some(box_point) = &box_point {
                args.zip_eq(&box_point[&TypeTagForBoxPoint::Lambda(original_id)])
                    .map(|(t, boxed)| set_refed(t, *boxed))
                    .collect()
            } else {
                args.collect()
            };
            ts.push(TypeUnitOf {
                id: TypeTag::LambdaId(id),
                args,
            });
        }
        let t = TypeInnerOf::Type(TypeOf {
            ts: Rc::new(ts),
            refed: false,
            diverging: false,
        });
        self.trace.remove(&p);
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
            return TypeInnerOf::RecursionPoint {
                i: depth - *d - 1,
                refed: false,
            };
        }
        trace.insert(p, depth);
        let depth = depth + 1;
        let mut ts = SmallVec::new();
        let terminal = map.dereference_without_find(p);
        let set_refed = |t: TypeInnerForHash, boxed: Option<bool>| {
            if boxed.unwrap() {
                match t {
                    TypeInnerOf::RecursionPoint { i, .. } => {
                        TypeInnerOf::RecursionPoint { i, refed: true }
                    }
                    TypeInnerOf::Type(t) => TypeInnerOf::Type(TypeOf { refed: true, ..t }),
                }
            } else {
                t
            }
        };
        let box_point = match &terminal.box_point {
            ast_step1::BoxPoint::Diverging => None,
            ast_step1::BoxPoint::Boxed(pss) => Some(pss),
            ast_step1::BoxPoint::NotSure => panic!("p = {p}, terminal = {terminal:?}"),
        };
        for (id, args) in &terminal.type_map {
            let args = args
                .iter()
                .map(|t| self.get_type_inner_for_hash(*t, trace, used_trace, map, depth));
            let args = if let Some(box_point) = box_point {
                args.zip_eq(&box_point[&TypeTagForBoxPoint::Normal(*id)])
                    .map(|(t, boxed)| set_refed(t, *boxed))
                    .collect()
            } else {
                args.collect()
            };
            ts.push(TypeUnitOf {
                id: TypeTag::TypeId(*id),
                args,
            })
        }
        let mut ls = FxHashSet::default();
        for (l, _) in &terminal.functions {
            let l = LambdaId {
                id: l.id,
                root_t: self.get_type_inner_for_hash(l.root_t, trace, used_trace, map, depth),
            };
            ls.insert(l);
        }
        for l in ls {
            ts.push(TypeUnitOf {
                id: TypeTag::LambdaId(l),
                args: SmallVec::new(),
            });
        }
        trace.remove(&p);
        let t = TypeInnerOf::Type(TypeOf {
            ts: Rc::new(ts),
            refed: false,
            diverging: false,
        });
        if used_trace.is_empty() {
            let o = self.type_memo_for_hash.insert(p, t.clone());
            debug_assert!(o.is_none());
        }
        used_trace.remove(&p);
        t
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
        if self.refed {
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
                let paren = p != P::Weak && (!is_single || function.is_some() && p == P::Strong);
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
                    if function.is_some() {
                        write!(f, " | ")?;
                    }
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
            TypeInnerOf::RecursionPoint { i, refed } => {
                if *refed {
                    write!(f, "&")?
                }
                write!(f, "d{i:?}")
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

impl DisplayTypeWithEnv for TypeUnique {
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
        match self.ts.len() {
            0 => write!(f, "Never"),
            1 => write!(f, "{:?}", self.ts.first().unwrap()),
            _ => write!(f, "({:?})", self.ts.iter().format(" | ")),
        }?;
        Ok(())
    }
}

impl<R: TypeFamily> fmt::Debug for TypeInnerOf<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeInnerOf::RecursionPoint { i, refed } => {
                if *refed {
                    write!(f, "&")?
                }
                write!(f, "d{i:?}")
            }
            TypeInnerOf::Type(t) => write!(f, "{t:?}"),
        }
    }
}

impl<R: TypeFamily> fmt::Debug for TypeUnitOf<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.id {
            TypeTag::TypeId(TypeId::Intrinsic(IntrinsicTypeTag::Fn)) => {
                write!(f, "({:?}) -> {:?}", self.args[0], self.args[1])?;
            }
            TypeTag::TypeId(id) => {
                write!(f, "{id}")?;
                if !self.args.is_empty() {
                    write!(f, "[{:?}]", self.args.iter().format(", "))?;
                };
            }
            TypeTag::LambdaId(l) => {
                write!(f, "{l}")?;
                if !self.args.is_empty() {
                    write!(f, "[{:?}]", self.args.iter().format(", "))?;
                };
            }
        };
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
