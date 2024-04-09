use super::c_type::PointerForCType;
use super::type_memo::TypeMemo;
use super::{CType, Env};
use crate::ir1::{self, PaddedTypeMap, TypePointer};
use crate::ir2::c_type::PointerModifier;
use crate::TypeId;
use itertools::Itertools;
use rustc_hash::FxHashMap;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UnionOp {
    pub new_tag: u32,
    pub convert_op: Vec<u32>,
    pub ref_op: ConvertOpRef,
    pub unit_c_type: CType,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConvertOp {
    Unknown,
    Id,
    Unexpected,
    Struct(Vec<u32>, ConvertOpRef),
    ReTag(Vec<UnionOp>),
    AddTag(UnionOp),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConvertOpRef {
    pub from_boxed: bool,
    pub to_boxed: bool,
}

impl ConvertOpRef {
    pub fn is_add_ref(&self) -> bool {
        !self.from_boxed && self.to_boxed
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeConverter {
    pub id: u32,
    pub op: ConvertOp,
}

#[derive(Debug)]
pub struct ConverterCollector(FxHashMap<(TypePointer, TypePointer), TypeConverter>);

const FN_TAG: ir1::TypeId = ir1::TypeId::Intrinsic(crate::intrinsics::IntrinsicTypeTag::Fn);

enum SingleOrUnion {
    Never,
    Single(TypeId, Vec<TypePointer>),
    Union,
}

fn c_type_tag_count(
    p: TypePointer,
    _type_memo: &mut TypeMemo,
    map: &mut PaddedTypeMap,
) -> SingleOrUnion {
    let terminal = map.dereference_without_find(p).clone();
    match terminal.type_map.len()
        - terminal
            .type_map
            .get(&TypeId::Intrinsic(crate::intrinsics::IntrinsicTypeTag::Fn))
            .is_some() as usize
    {
        0 => SingleOrUnion::Never,
        1 => {
            let (id, (args, boxed)) = terminal.type_map.into_iter().next().unwrap();
            if terminal.diverged.unwrap() {
                SingleOrUnion::Never
            } else {
                debug_assert!(!boxed);
                SingleOrUnion::Single(id, args)
            }
        }
        _ => SingleOrUnion::Union,
    }
}

impl ConverterCollector {
    pub fn new() -> Self {
        ConverterCollector(Default::default())
    }

    pub fn into_inner(self) -> FxHashMap<(TypePointer, TypePointer), TypeConverter> {
        self.0
    }

    pub fn add(&mut self, a: TypePointer, b: TypePointer, env: &mut Env<'_, '_>) -> u32 {
        let a = env.map.find(a);
        let b = env.map.find(b);
        if a == b
            || env.type_memo.get_type_for_hash(a, &mut env.map)
                == env.type_memo.get_type_for_hash(b, &mut env.map)
        {
            0
        } else if let Some(c) = self.0.get(&(a, b)) {
            c.id
        } else {
            self.0.insert(
                (a, b),
                TypeConverter {
                    id: self.0.len() as u32,
                    op: ConvertOp::Unknown,
                },
            );
            let a_len = c_type_tag_count(a, &mut env.type_memo, &mut env.map);
            let b_len = c_type_tag_count(b, &mut env.type_memo, &mut env.map);
            let op = match (a_len, b_len) {
                (SingleOrUnion::Never, _) => ConvertOp::Unexpected,
                (SingleOrUnion::Single(_, a_args), SingleOrUnion::Single(_, b_args)) => {
                    if a_args.is_empty() {
                        debug_assert!(b_args.is_empty());
                        ConvertOp::Id
                    } else {
                        let converters = a_args
                            .iter()
                            .zip_eq(b_args)
                            .map(|(a, b)| self.add(*a, b, env))
                            .collect_vec();
                        if converters.iter().all(|a| *a == 0) {
                            ConvertOp::Id
                        } else {
                            let r = ConvertOpRef {
                                from_boxed: false,
                                to_boxed: false,
                            };
                            ConvertOp::Struct(converters, r)
                        }
                    }
                }
                (SingleOrUnion::Single(a_tag, a_args), SingleOrUnion::Union) => {
                    let b_t = env.map.dereference_imm(b);
                    let (tag, (_, (args, b_boxed))) = b_t
                        .type_map
                        .iter()
                        .enumerate()
                        .find(|(_, (k, _))| **k == a_tag)
                        .unwrap();
                    let b_boxed = *b_boxed;
                    if b_t.diverged.unwrap() {
                        ConvertOp::Unexpected
                    } else {
                        let converters = a_args
                            .iter()
                            .copied()
                            .zip_eq(args.iter().copied())
                            .collect_vec()
                            .into_iter()
                            .map(|(a, b)| self.add(a, b, env))
                            .collect();
                        let r = ConvertOpRef {
                            from_boxed: false,
                            to_boxed: b_boxed,
                        };
                        ConvertOp::AddTag(UnionOp {
                            new_tag: tag as u32,
                            convert_op: converters,
                            ref_op: r,
                            unit_c_type: env.c_type(PointerForCType {
                                modifier: PointerModifier::UnionMember(tag as u32),
                                p: b,
                            }),
                        })
                    }
                }
                (SingleOrUnion::Union, SingleOrUnion::Union) => {
                    let b_t = env.map.dereference_imm(b);
                    let a_t = env.map.dereference_imm(a);
                    debug_assert!(!b_t.diverged.unwrap());
                    debug_assert!(!a_t.diverged.unwrap());
                    let b_t: FxHashMap<_, _> = b_t
                        .type_map
                        .iter()
                        .filter(|(id, _)| **id != FN_TAG)
                        .enumerate()
                        .map(|(i, (type_id, args))| (*type_id, (i, args.clone())))
                        .collect();
                    let ops = a_t
                        .type_map
                        .clone()
                        .into_iter()
                        .filter(|(id, _)| {
                            *id != ir1::TypeId::Intrinsic(crate::intrinsics::IntrinsicTypeTag::Fn)
                        })
                        .map(|(type_id, (a_args, a_boxed))| {
                            let (b_tag, (b_args, b_boxed)) = &b_t[&type_id];
                            let convert_op = a_args
                                .iter()
                                .zip(b_args)
                                .map(|(a, b)| self.add(*a, *b, env))
                                .collect_vec();
                            let ref_op = ConvertOpRef {
                                from_boxed: a_boxed,
                                to_boxed: *b_boxed,
                            };
                            UnionOp {
                                new_tag: *b_tag as u32,
                                convert_op,
                                ref_op,
                                unit_c_type: env.c_type(PointerForCType {
                                    modifier: PointerModifier::UnionMember(*b_tag as u32),
                                    p: b,
                                }),
                            }
                        })
                        .collect_vec();
                    ConvertOp::ReTag(ops)
                }
                _ => panic!(),
            };
            let e = self.0.get_mut(&(a, b)).unwrap();
            e.op = op;
            e.id
        }
    }
}
