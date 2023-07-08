use super::collector::Collector;
use crate::ast_step1::TypeId;
use crate::ast_step2::{Type, TypeInner, TypeInnerOf, TypeUnitOf};
use crate::intrinsics::IntrinsicTypeTag;
use rustc_hash::{FxHashMap, FxHashSet};
use std::fmt::Display;

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum CType {
    I64,
    U8,
    String,
    Aggregate(usize),
    Ref(Box<CType>),
}

impl Display for CType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CType::I64 => write!(f, "int64_t"),
            CType::U8 => write!(f, "uint8_t"),
            CType::String => write!(f, "struct intrinsic_str_t"),
            CType::Aggregate(i) => write!(f, "struct t{i}"),
            CType::Ref(i) => write!(f, "{i}*"),
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
        debug_assert!(!t.reference);
        let single = if t.len() == 1 {
            match t.iter().next().unwrap() {
                TypeUnitOf::Normal { .. } => true,
                TypeUnitOf::Fn(l, _, _) => l.len() == 1,
            }
        } else {
            false
        };
        let reserved_id;
        if t.recursive && recurring(t) {
            let i = self.aggregate_types.get_empty_id();
            type_stack = Some((i, t.clone().get_ref()));
            reserved_id = Some(i);
        } else {
            reserved_id = None;
        }
        let mut ts = Vec::new();
        debug_assert!(!t.contains_broken_link_rec(type_stack.is_some() as u32));
        for tu in t.iter() {
            use TypeUnitOf::*;
            match tu {
                Normal { id, args } => match id {
                    TypeId::Intrinsic(IntrinsicTypeTag::String)
                    | TypeId::Intrinsic(IntrinsicTypeTag::I64)
                    | TypeId::Intrinsic(IntrinsicTypeTag::U8) => {
                        let c_t = match id {
                            TypeId::Intrinsic(IntrinsicTypeTag::String) => CType::String,
                            TypeId::Intrinsic(IntrinsicTypeTag::I64) => CType::I64,
                            TypeId::Intrinsic(IntrinsicTypeTag::U8) => CType::U8,
                            _ => panic!(),
                        };
                        if single {
                            debug_assert!(reserved_id.is_none());
                            return c_t;
                        }
                        ts.push(c_t);
                    }
                    TypeId::Intrinsic(IntrinsicTypeTag::Mut) => {
                        debug_assert_eq!(args.len(), 1);
                        let arg_t = self.c_type_from_inner_type(&args[0], &type_stack);
                        let c_t = CType::Ref(Box::new(arg_t));
                        if single {
                            debug_assert!(reserved_id.is_none());
                            return c_t;
                        }
                        ts.push(c_t);
                    }
                    _ => {
                        let t = CAggregateType::Struct(
                            args.iter()
                                .map(|t| self.c_type_from_inner_type(t, &type_stack))
                                .collect(),
                        );
                        if single {
                            return match reserved_id {
                                Some(i) => {
                                    debug_assert!(ts.is_empty());
                                    self.aggregate_types.insert_with_id(t, i);
                                    CType::Aggregate(i)
                                }
                                None => CType::Aggregate(self.aggregate_types.get_or_insert(t)),
                            };
                        }
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
                        match reserved_id {
                            Some(i) if single => {
                                self.aggregate_types
                                    .insert_with_id(CAggregateType::Union(ts), i);
                                return CType::Aggregate(i);
                            }
                            _ => (),
                        }
                        ts.push(CType::Aggregate(self.aggregate_types.get_or_insert(c_t)))
                    }
                }
            }
        }
        if let Some(i) = reserved_id {
            debug_assert!(ts.len() >= 2);
            self.aggregate_types
                .insert_with_id(CAggregateType::Union(ts), i);
            CType::Aggregate(i)
        } else if ts.len() == 1 {
            ts.into_iter().next().unwrap()
        } else {
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
        debug_assert!(!t.contains_broken_link_rec(type_stack.is_some() as u32));
        if t.reference {
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
                CType::Ref(Box::new(CType::Aggregate(type_stack.as_ref().unwrap().0)))
            }
            TypeInnerOf::Type(t) => self.c_type(t, type_stack.clone()),
        }
    }
}

fn recurring(t: &Type) -> bool {
    contains_index(t, -1)
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
