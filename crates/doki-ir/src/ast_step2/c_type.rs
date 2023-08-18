use super::CType;
use crate::ast_step1::TypePointer;
use crate::ast_step2::StructId;
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
    Boxed,
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
    fn replace(&mut self, v: PointerForCType) -> u32;
}

impl Dfa for CTypeEnv<'_> {
    type Transition<'a> = CTypeScheme<CType> where Self: 'a;
    type Node = PointerForCType;

    fn get<'a>(
        &'a self,
        node: Self::Node,
        points: &FxHashMap<Self::Node, u32>,
    ) -> Self::Transition<'a> {
        debug_assert_ne!(PointerModifier::Boxed, node.modifier);
        self.0[&node].replace_ref(|a| {
            if a.modifier == PointerModifier::Boxed {
                CType {
                    i: StructId(
                        points[&PointerForCType {
                            modifier: PointerModifier::Normal,
                            p: a.p,
                        }] as usize,
                    ),
                    boxed: true,
                }
            } else {
                CType {
                    i: StructId(points[a] as usize),
                    boxed: false,
                }
            }
        })
    }
}

impl PointerReplacer for FxHashMap<PointerForCType, u32> {
    fn replace(&mut self, v: PointerForCType) -> u32 {
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
