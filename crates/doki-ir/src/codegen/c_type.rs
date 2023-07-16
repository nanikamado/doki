use crate::ast_step1::TypeId;
use crate::ast_step2::{Type, TypeInner, TypeInnerOf, TypeUnitOf};
use crate::collector::Collector;
use crate::intrinsics::IntrinsicTypeTag;
use rustc_hash::{FxHashMap, FxHashSet};
use std::fmt::Display;

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum CType {
    I64,
    U8,
    Ptr,
    Aggregate(usize),
    Ref(Box<CType>),
    Diverge,
}

impl Display for CType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CType::I64 => write!(f, "int64_t"),
            CType::U8 => write!(f, "uint8_t"),
            CType::Ptr => write!(f, "void*"),
            CType::Aggregate(i) => write!(f, "struct t{i}"),
            CType::Ref(i) => write!(f, "{i}*"),
            CType::Diverge => write!(f, "struct diverge"),
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum CAggregateType {
    Union(Vec<CType>),
    Struct(Vec<CType>),
}

pub struct Env {
    pub aggregate_types: Collector<CAggregateType>,
    pub memo: FxHashMap<Type, CType>,
    pub reffed_aggregates: FxHashSet<usize>,
}

impl Env {
    fn c_type_inner(&mut self, t: &Type, mut type_stack: Option<(usize, Type)>) -> CType {
        let reserved_id = if t.recursive {
            let i = self.aggregate_types.get_empty_id();
            type_stack = Some((i, t.clone()));
            Some(i)
        } else {
            None
        };
        let mut ts = Vec::new();
        if type_stack.is_none() {
            debug_assert!(!t.contains_broken_link_rec(0));
        }
        for tu in t.iter() {
            use TypeUnitOf::*;
            match tu {
                Normal { id, args } => match id {
                    TypeId::Intrinsic(
                        IntrinsicTypeTag::I64 | IntrinsicTypeTag::U8 | IntrinsicTypeTag::Ptr,
                    ) => {
                        let c_t = match id {
                            TypeId::Intrinsic(IntrinsicTypeTag::I64) => CType::I64,
                            TypeId::Intrinsic(IntrinsicTypeTag::U8) => CType::U8,
                            TypeId::Intrinsic(IntrinsicTypeTag::Ptr) => CType::Ptr,
                            _ => panic!(),
                        };
                        ts.push(c_t);
                    }
                    TypeId::Intrinsic(IntrinsicTypeTag::Mut) => {
                        debug_assert_eq!(args.len(), 1);
                        let arg_t = self.c_type_from_inner_type(&args[0], &type_stack);
                        let c_t = CType::Ref(Box::new(arg_t));
                        ts.push(c_t);
                    }
                    _ => {
                        let t = CAggregateType::Struct(
                            args.iter()
                                .map(|t| self.c_type_from_inner_type(t, &type_stack))
                                .collect(),
                        );
                        ts.push(CType::Aggregate(self.aggregate_types.get_or_insert(t)));
                    }
                },
                Fn(lambda_id, _, _) => {
                    for ctx in lambda_id.values() {
                        let c_t = CAggregateType::Struct(
                            ctx.iter()
                                .map(|t| self.c_type_from_inner_type(t, &type_stack))
                                .collect(),
                        );
                        ts.push(CType::Aggregate(self.aggregate_types.get_or_insert(c_t)))
                    }
                }
            }
        }
        if ts.len() == 1 {
            let ct = ts.into_iter().next().unwrap();
            if let Some(i) = reserved_id {
                if ct.contains_aggregate(i, &self.aggregate_types) {
                    CType::Diverge
                } else {
                    ct
                }
            } else {
                ct
            }
        } else if let Some(i) = reserved_id {
            let i = self
                .aggregate_types
                .get_or_insert_with_id(CAggregateType::Union(ts), i);
            CType::Aggregate(i)
        } else {
            debug_assert!(!t.reference);
            CType::Aggregate(
                self.aggregate_types
                    .get_or_insert(CAggregateType::Union(ts)),
            )
        }
    }

    fn c_type_memoize(&mut self, t: &Type, type_stack: Option<(usize, Type)>) -> CType {
        if let Some(t) = self.memo.get(t) {
            t.clone()
        } else {
            let recurring = contains_index(t, 0);
            let c_t = self.c_type_inner(t, type_stack);
            if !recurring {
                let _o = self.memo.insert(t.clone(), c_t.clone());
                #[cfg(debug_assertions)]
                if let Some(t) = _o {
                    assert_eq!(t, c_t);
                }
            }
            c_t
        }
    }

    pub fn c_type(&mut self, t: &Type, type_stack: Option<(usize, Type)>) -> CType {
        if type_stack.is_none() {
            debug_assert!(!t.contains_broken_link_rec(0));
        }
        if t.reference && !t.derefed {
            let t = self.c_type_memoize(&t.clone().deref(), type_stack);
            let i = if let CType::Aggregate(i) = t {
                i
            } else {
                panic!()
            };
            self.reffed_aggregates.insert(i);
            CType::Ref(Box::new(t))
        } else {
            self.c_type_memoize(t, type_stack)
        }
    }

    pub fn c_type_from_inner_type(
        &mut self,
        t: &TypeInner,
        type_stack: &Option<(usize, Type)>,
    ) -> CType {
        match t {
            TypeInnerOf::RecursionPoint(d) => {
                assert_eq!(*d, 0);
                let s = type_stack.as_ref().unwrap();
                if s.1.reference {
                    CType::Ref(Box::new(CType::Aggregate(s.0)))
                } else {
                    CType::Aggregate(s.0)
                }
            }
            TypeInnerOf::Type(t) => self.c_type(t, type_stack.clone()),
        }
    }
}

fn contains_index(t: &Type, mut depth: i32) -> bool {
    if t.recursive {
        depth += 1;
    }
    let check = |a: &[TypeInner]| {
        a.iter().any(|a| match a {
            TypeInnerOf::RecursionPoint(a) => *a as i32 == depth,
            TypeInnerOf::Type(t) => contains_index(t, depth),
        })
    };
    t.iter().any(|a| match a {
        TypeUnitOf::Normal { id: _, args } => check(args),
        TypeUnitOf::Fn(ls, _, _) => ls.iter().any(|(_, ctx)| check(ctx)),
    })
}

impl CType {
    fn contains_aggregate(&self, i: usize, aggregate_types: &Collector<CAggregateType>) -> bool {
        match self {
            CType::I64 | CType::U8 | CType::Ptr => false,
            CType::Aggregate(j) => {
                i == *j
                    || aggregate_types
                        .get_rev(*j)
                        .map(|t| match t {
                            CAggregateType::Union(ts) | CAggregateType::Struct(ts) => {
                                ts.iter().any(|t| t.contains_aggregate(i, aggregate_types))
                            }
                        })
                        .unwrap_or(false)
            }
            CType::Ref(c) => c.contains_aggregate(i, aggregate_types),
            CType::Diverge => false,
        }
    }
}
