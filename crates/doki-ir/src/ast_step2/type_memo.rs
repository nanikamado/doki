use super::{LambdaId, TypeIdTag, TypeUnique};
use crate::ast_step1::{self, ConstructorNames, PaddedTypeMap, TypeId, TypePointer};
use crate::intrinsics::IntrinsicTypeTag;
use crate::util::id_generator::IdGenerator;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
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
pub struct TypeUnitOf<T: TypeFamily> {
    id: TypeId,
    args: SmallVec<[TypeInnerOf<T>; 2]>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct TypeForHashF;
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct NormalTypeF;

pub trait TypeFamily {
    type LambdaTag: Eq + Ord + Clone + std::hash::Hash + std::fmt::Debug + DisplayTypeWithEnv;
    type LambdaCtx: Eq + Ord + Clone + std::hash::Hash + DebugCtx;
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
}

#[derive(Debug, Default)]
pub struct TypeMemo {
    type_memo: FxHashMap<TypePointer, Type>,
    type_memo_for_hash: FxHashMap<TypePointer, TypeForHash>,
    pub type_id_generator: IdGenerator<TypeForHash, TypeIdTag>,
    trace: FxHashMap<TypePointer, usize>,
}

impl TypeMemo {
    pub fn get_type(&mut self, p: TypePointer, map: &mut PaddedTypeMap) -> Type {
        let p = map.find(p);
        if let Some(t) = self.type_memo.get(&p) {
            t.clone()
        } else {
            let t = self.get_type_inner(p, map);
            self.trace.clear();
            let TypeInnerOf::Type(t) = t else { panic!() };
            self.type_memo.insert(p, t.clone());
            t
        }
    }

    pub fn get_type_for_hash(&mut self, p: TypePointer, map: &mut PaddedTypeMap) -> TypeForHash {
        let p = map.find(p);
        if let Some(t) = self.type_memo_for_hash.get(&p) {
            t.clone()
        } else {
            map.minimize(p);
            let t = TypeMemo::get_type_inner_for_hash(p, &mut Default::default(), map);
            let TypeInnerOf::Type(t) = t else { panic!() };
            self.type_memo_for_hash.insert(p, t.clone());
            t
        }
    }

    fn get_type_inner(&mut self, p: TypePointer, map: &mut PaddedTypeMap) -> TypeInner {
        let p = map.find(p);
        if let Some(d) = self.trace.get(&p) {
            return TypeInnerOf::RecursionPoint {
                i: (self.trace.len() - *d - 1) as u32,
                refed: false,
            };
        }
        self.trace.insert(p, self.trace.len());
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
                args.zip_eq(&box_point[&id])
                    .map(|(t, boxed)| set_refed(t, *boxed))
                    .collect()
            } else {
                args.collect()
            };
            ts.push(TypeUnitOf { id, args })
        }
        TypeInnerOf::Type(TypeOf {
            ts: Rc::new(ts),
            refed: false,
            diverging: false,
        })
    }

    fn get_type_inner_for_hash(
        p: TypePointer,
        trace: &mut FxHashMap<TypePointer, u32>,
        map: &PaddedTypeMap,
    ) -> TypeInnerForHash {
        let p = map.find_imm(p);
        if let Some(d) = trace.get(&p) {
            return TypeInnerOf::RecursionPoint {
                i: trace.len() as u32 - *d - 1,
                refed: false,
            };
        }
        trace.insert(p, trace.len() as u32);
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
                .map(|t| TypeMemo::get_type_inner_for_hash(*t, trace, map));
            let args = if let Some(box_point) = box_point {
                args.zip_eq(&box_point[id])
                    .map(|(t, boxed)| set_refed(t, *boxed))
                    .collect()
            } else {
                args.collect()
            };
            ts.push(TypeUnitOf { id: *id, args })
        }
        TypeInnerOf::Type(TypeOf {
            ts: Rc::new(ts),
            refed: false,
            diverging: false,
        })
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
                        TypeId::Intrinsic(IntrinsicTypeTag::Fn) => {
                            function = Some((&t.args[0], &t.args[1]));
                        }
                        TypeId::Function(_) => fn_contexts.push(t),
                        u => {
                            normals.push((u, &t.args));
                        }
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
                            TypeId::Function(i) => writeln!(f, "Fn({i})")?,
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
                            fn_contexts.iter().format_with(" | ", |a, f| {
                                f(&a.id)?;
                                f(&format_args!(
                                    "[{}]",
                                    a.args.iter().format_with(", ", |a, f| f(&DisplayTypeHelper(
                                        a,
                                        P::Weak,
                                        env
                                    )))
                                ))
                            }),
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
            TypeId::Intrinsic(IntrinsicTypeTag::Fn) => {
                write!(f, "({:?}) -> {:?}", self.args[0], self.args[1])?;
            }
            id => {
                write!(f, "{id}")?;
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
