use crate::ast_step1::TypeId;
use crate::ast_step2::{Type, TypeInner, TypeInnerOf, TypeUnitOf};
use crate::intrinsics::IntrinsicTypeTag;
use crate::util::collector::Collector;
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
    fn c_type_inner(&mut self, t: &Type, type_stack: &mut Vec<(usize, Type)>) -> CType {
        let reserved_id = self.aggregate_types.get_empty_id();
        type_stack.push((reserved_id, t.clone()));
        let mut ts = Vec::new();
        if type_stack.is_empty() {
            debug_assert!(!t.contains_broken_link_rec(0));
        }
        let is_single = t
            .iter()
            .map(|t| match t {
                TypeUnitOf::Normal { .. } => 1,
                TypeUnitOf::Fn(l, _, _) => l.len(),
            })
            .sum::<usize>()
            == 1;
        let aggregate_to_c_type =
            |t: CAggregateType, aggregate_types: &mut Collector<CAggregateType>| {
                if is_single {
                    CType::Aggregate(aggregate_types.get_or_insert_with_id(t, reserved_id))
                } else {
                    CType::Aggregate(aggregate_types.get_or_insert(t))
                }
            };
        for tu in t.iter() {
            use TypeUnitOf::*;
            match tu {
                Normal { id, args } => {
                    let c_t = match id {
                        TypeId::Intrinsic(
                            IntrinsicTypeTag::I64 | IntrinsicTypeTag::U8 | IntrinsicTypeTag::Ptr,
                        ) => match id {
                            TypeId::Intrinsic(IntrinsicTypeTag::I64) => CType::I64,
                            TypeId::Intrinsic(IntrinsicTypeTag::U8) => CType::U8,
                            TypeId::Intrinsic(IntrinsicTypeTag::Ptr) => CType::Ptr,
                            _ => panic!(),
                        },
                        TypeId::Intrinsic(IntrinsicTypeTag::Mut) => {
                            debug_assert_eq!(args.len(), 1);
                            let arg_t = self.c_type_from_inner_type(&args[0], type_stack);
                            CType::Ref(Box::new(arg_t))
                        }
                        _ => {
                            let t = CAggregateType::Struct(
                                args.iter()
                                    .map(|t| self.c_type_from_inner_type(t, type_stack))
                                    .collect(),
                            );
                            aggregate_to_c_type(t, &mut self.aggregate_types)
                        }
                    };
                    ts.push(c_t);
                }
                Fn(lambda_id, _, _) => {
                    for ctx in lambda_id.values() {
                        let c_t = CAggregateType::Struct(
                            ctx.iter()
                                .map(|t| self.c_type_from_inner_type(t, type_stack))
                                .collect(),
                        );
                        let c_t = aggregate_to_c_type(c_t, &mut self.aggregate_types);
                        ts.push(c_t);
                    }
                }
            }
        }
        type_stack.pop().unwrap();
        if is_single {
            debug_assert_eq!(ts.len(), 1);
            ts.into_iter().next().unwrap()
        } else {
            let i = self
                .aggregate_types
                .get_or_insert_with_id(CAggregateType::Union(ts), reserved_id);
            CType::Aggregate(i)
        }
    }

    fn c_type_memoize(&mut self, t: &Type, type_stack: &mut Vec<(usize, Type)>) -> CType {
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

    pub fn c_type(&mut self, t: &Type, type_stack: &mut Vec<(usize, Type)>) -> CType {
        if type_stack.is_empty() {
            debug_assert!(!t.contains_broken_link_rec(0));
        }
        if t.diverging {
            CType::Diverge
        } else if t.reference && !t.derefed {
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
        type_stack: &mut Vec<(usize, Type)>,
    ) -> CType {
        match t {
            TypeInnerOf::RecursionPoint(d) => {
                let s = &type_stack[type_stack.len() - 1 - *d as usize];
                if s.1.reference {
                    CType::Ref(Box::new(CType::Aggregate(s.0)))
                } else {
                    CType::Aggregate(s.0)
                }
            }
            TypeInnerOf::Type(t) => self.c_type(t, type_stack),
        }
    }
}

fn contains_index(t: &Type, mut depth: i32) -> bool {
    depth += 1;
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
