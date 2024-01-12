use crate::ast_step1::{self, Diverged, FieldType, PaddedTypeMap, TypePointer};
use crate::TypeId;
use rustc_hash::FxHashMap;

#[derive(Debug, Default)]
pub struct PrinterCollector {
    map: FxHashMap<TypePointer, Vec<(TypeId, Vec<FieldType>)>>,
}

impl PrinterCollector {
    pub fn into_inner(self) -> FxHashMap<TypePointer, Vec<(TypeId, Vec<FieldType>)>> {
        self.map
    }

    pub fn inner(&self) -> &FxHashMap<TypePointer, Vec<(TypeId, Vec<FieldType>)>> {
        &self.map
    }

    pub fn add(&mut self, a: TypePointer, map: &mut PaddedTypeMap) {
        let t = map.dereference_without_find(a);
        if self.map.contains_key(&a) {
            return;
        }
        self.map.insert(a, Vec::new());
        match &t.diverged {
            Diverged::NotSure => panic!(),
            Diverged::Yes => (),
            Diverged::No => {
                let mut union_members = Vec::new();
                for (tag, args) in t.type_map.clone() {
                    if tag == ast_step1::TypeId::Intrinsic(crate::intrinsics::IntrinsicTypeTag::Fn)
                    {
                        continue;
                    }
                    for a in &args {
                        self.add(a.p, map);
                    }
                    union_members.push((tag, args));
                }
                self.map.insert(a, union_members);
            }
        }
    }
}
