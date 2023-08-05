use crate::ast_step1::TypePointer;
use crate::util::dfa_minimization::Dfa;
use rustc_hash::FxHashMap;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum CTypeScheme<T> {
    I64,
    U8,
    Ptr,
    Aggregate(Vec<T>),
    Union(Vec<T>),
    Mut(T),
    Diverge,
}

pub struct CTypeEnv<'a>(pub &'a FxHashMap<PointerForCType, CTypeScheme<PointerForCType>>);

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct PointerForCType {
    pub modifier: PointerModifier,
    pub p: TypePointer,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum PointerModifier {
    Normal,
    UnionMember(u32),
    Derefed,
}

impl PointerForCType {
    pub fn from(p: TypePointer) -> Self {
        Self {
            p,
            modifier: PointerModifier::Normal,
        }
    }
}

pub trait PointerReplacer {
    fn replace(&mut self, v: PointerForCType) -> usize;
}

impl Dfa for CTypeEnv<'_> {
    type Transition = CTypeScheme<usize>;
    type Node = PointerForCType;

    fn get(&self, node: Self::Node, points: &FxHashMap<Self::Node, usize>) -> Self::Transition {
        self.0[&node].replace_ref(|a| points[a])
    }
}

impl PointerReplacer for FxHashMap<PointerForCType, usize> {
    fn replace(&mut self, v: PointerForCType) -> usize {
        self[&v]
    }
}

impl<T> CTypeScheme<T> {
    pub fn replace_ref<U>(&self, mut f: impl FnMut(&T) -> U) -> CTypeScheme<U> {
        match self {
            CTypeScheme::I64 => CTypeScheme::I64,
            CTypeScheme::U8 => CTypeScheme::U8,
            CTypeScheme::Ptr => CTypeScheme::Ptr,
            CTypeScheme::Aggregate(rs) => CTypeScheme::Aggregate(rs.iter().map(&mut f).collect()),
            CTypeScheme::Union(ts) => CTypeScheme::Union(ts.iter().map(&mut f).collect()),
            CTypeScheme::Mut(r) => CTypeScheme::Mut(f(r)),
            CTypeScheme::Diverge => CTypeScheme::Diverge,
        }
    }
}