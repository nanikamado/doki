use super::c_type::PointerForCType;
use super::type_memo::TypeMemo;
use super::{CType, Env};
use crate::ast_step1::{self, BoxPoint, PaddedTypeMap, TypePointer};
use crate::TypeId;
use itertools::Itertools;
use rustc_hash::FxHashMap;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UnionOp {
    pub new_tag: u32,
    pub convert_op: Vec<(u32, ConvertOpRef)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConvertOp {
    Unknown,
    Id,
    Unexpected,
    Struct(Vec<(u32, ConvertOpRef)>),
    ReTag(Vec<UnionOp>),
    AddTag(u32, Vec<(u32, ConvertOpRef)>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConvertOpRef {
    None,
    RemainRef(CType),
    AddRef(CType),
    Deref,
}

impl ConvertOpRef {
    pub fn is_add_ref(&self) -> bool {
        matches!(self, ConvertOpRef::AddRef(_))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeConverter {
    pub id: u32,
    pub op: ConvertOp,
}

#[derive(Debug)]
pub struct ConverterCollector(FxHashMap<(TypePointer, TypePointer), TypeConverter>);

const FN_TAG: ast_step1::TypeId =
    ast_step1::TypeId::Intrinsic(crate::intrinsics::IntrinsicTypeTag::Fn);

enum SingleOrUnion {
    Never,
    Single(TypeId, Vec<(TypePointer, bool)>),
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
            let (id, args) = terminal.type_map.iter().next().unwrap();
            let terminal = map.dereference_without_find(p);
            match &terminal.box_point {
                BoxPoint::NotSure => panic!(),
                BoxPoint::Diverging => SingleOrUnion::Never,
                BoxPoint::Boxed(box_point) => SingleOrUnion::Single(
                    *id,
                    args.iter()
                        .copied()
                        .zip_eq(
                            box_point
                                .values()
                                .next()
                                .unwrap()
                                .iter()
                                .map(|a| a.unwrap()),
                        )
                        .collect(),
                ),
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
                (SingleOrUnion::Single(_, a_args), SingleOrUnion::Single(_, b)) => {
                    if a_args.is_empty() {
                        debug_assert!(b.is_empty());
                        ConvertOp::Id
                    } else {
                        let converters = a_args
                            .iter()
                            .zip_eq(b)
                            .map(|(a, b)| self.add_aux(*a, b, env))
                            .collect_vec();
                        if converters.iter().all(|(a, p)| *a == 0 && !p.is_add_ref()) {
                            ConvertOp::Id
                        } else {
                            ConvertOp::Struct(converters)
                        }
                    }
                }
                (SingleOrUnion::Single(a_tag, a_args), SingleOrUnion::Union) => {
                    let b_t = env.map.dereference_imm(b);
                    let (tag, (_, args)) = b_t
                        .type_map
                        .iter()
                        .enumerate()
                        .find(|(_, (k, _))| **k == a_tag)
                        .unwrap();
                    match &b_t.box_point {
                        BoxPoint::NotSure => panic!(),
                        BoxPoint::Diverging => ConvertOp::Unexpected,
                        BoxPoint::Boxed(box_point) => {
                            let converters = a_args
                                .iter()
                                .copied()
                                .zip_eq(
                                    args.iter()
                                        .copied()
                                        .zip_eq(box_point[&a_tag].iter().map(|a| a.unwrap())),
                                )
                                .collect_vec()
                                .into_iter()
                                .map(|(a, b)| self.add_aux(a, b, env))
                                .collect();
                            ConvertOp::AddTag(tag as u32, converters)
                        }
                    }
                }
                (SingleOrUnion::Union, SingleOrUnion::Union) => {
                    let b_t = env.map.dereference_imm(b);
                    let a_t = env.map.dereference_imm(a);
                    match (a_t.box_point.clone(), b_t.box_point.clone()) {
                        (BoxPoint::NotSure, _)
                        | (_, BoxPoint::NotSure)
                        | (BoxPoint::Diverging, _)
                        | (_, BoxPoint::Diverging) => panic!(),
                        (BoxPoint::Boxed(a_box_point), BoxPoint::Boxed(b_box_point)) => {
                            let b_t: FxHashMap<_, _> = b_t
                                .type_map
                                .iter()
                                .filter(|(id, _)| **id != FN_TAG)
                                .enumerate()
                                .map(|(i, (type_id, args))| {
                                    (
                                        *type_id,
                                        (
                                            i,
                                            args.iter()
                                                .copied()
                                                .zip_eq(
                                                    b_box_point[type_id].iter().map(|a| a.unwrap()),
                                                )
                                                .collect_vec(),
                                        ),
                                    )
                                })
                                .collect();
                            let ops = a_t
                                .type_map
                                .iter()
                                .filter(|(id, _)| {
                                    **id != ast_step1::TypeId::Intrinsic(
                                        crate::intrinsics::IntrinsicTypeTag::Fn,
                                    )
                                })
                                .map(|(k, v)| {
                                    (
                                        *k,
                                        v.iter()
                                            .copied()
                                            .zip_eq(a_box_point[k].iter().map(|a| a.unwrap()))
                                            .collect_vec(),
                                    )
                                })
                                .collect_vec()
                                .into_iter()
                                .map(|(type_id, a_args)| {
                                    let (b_tag, b_args) = &b_t[&type_id];
                                    let convert_op = a_args
                                        .iter()
                                        .zip(b_args)
                                        .map(|(a, b)| self.add_aux(*a, *b, env))
                                        .collect_vec();
                                    UnionOp {
                                        new_tag: *b_tag as u32,
                                        convert_op,
                                    }
                                })
                                .collect_vec();
                            ConvertOp::ReTag(ops)
                        }
                    }
                }
                _ => panic!(),
            };
            let e = self.0.get_mut(&(a, b)).unwrap();
            e.op = op;
            e.id
        }
    }

    fn add_aux(
        &mut self,
        (a, a_boxed): (TypePointer, bool),
        (b, b_boxed): (TypePointer, bool),
        env: &mut Env<'_, '_>,
    ) -> (u32, ConvertOpRef) {
        let c = self.add(a, b, env);
        let r = match (a_boxed, b_boxed) {
            (true, true) => ConvertOpRef::RemainRef(env.c_type(PointerForCType::from(b))),
            (true, false) => ConvertOpRef::Deref,
            (false, true) => ConvertOpRef::AddRef(env.c_type(PointerForCType::from(b))),
            (false, false) => ConvertOpRef::None,
        };
        (c, r)
    }
}
