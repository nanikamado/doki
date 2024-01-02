use crate::ast_step1::{self, BoxPoint, PaddedTypeMap, TypePointer};
use crate::TypeId;
use itertools::Itertools;
use rustc_hash::FxHashMap;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FieldOp {
    pub p: TypePointer,
    pub boxed: bool,
}

#[derive(Debug, Default)]
pub struct PrinterCollector {
    map: FxHashMap<TypePointer, Vec<(TypeId, Vec<FieldOp>)>>,
}

impl PrinterCollector {
    pub fn into_inner(self) -> FxHashMap<TypePointer, Vec<(TypeId, Vec<FieldOp>)>> {
        self.map
    }

    pub fn inner(&self) -> &FxHashMap<TypePointer, Vec<(TypeId, Vec<FieldOp>)>> {
        &self.map
    }

    pub fn add(&mut self, a: TypePointer, map: &mut PaddedTypeMap) {
        let t = map.dereference_without_find(a);
        if self.map.contains_key(&a) {
            return;
        }
        self.map.insert(a, Vec::new());
        match &t.box_point {
            BoxPoint::NotSure => panic!(),
            BoxPoint::Diverging => (),
            BoxPoint::Boxed(box_points) => {
                let mut union_members = Vec::new();
                for ((tag, args), (box_tag, box_points)) in
                    t.type_map.clone().into_iter().zip_eq(box_points.clone())
                {
                    debug_assert_eq!(tag, box_tag);
                    if tag == ast_step1::TypeId::Intrinsic(crate::intrinsics::IntrinsicTypeTag::Fn)
                    {
                        continue;
                    }
                    let args = args.iter().map(|a| map.find(*a)).collect_vec();
                    union_members.push((
                        tag,
                        args.iter()
                            .zip_eq(box_points)
                            .map(|(p, boxed)| FieldOp {
                                p: *p,
                                boxed: boxed.unwrap(),
                            })
                            .collect(),
                    ));
                    for a in args {
                        self.add(a, map);
                    }
                }
                self.map.insert(a, union_members);
            }
        }
    }
}
