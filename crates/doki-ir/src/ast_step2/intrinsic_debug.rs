use crate::ast_step1::{self, PaddedTypeMap, TypePointer};
use crate::TypeId;
use rustc_hash::FxHashMap;

#[derive(Debug, Default)]
pub struct PrinterCollector {
    map: FxHashMap<TypePointer, PrinterCollectorValue>,
}

#[derive(Debug, Default)]
pub struct PrinterCollectorValue {
    pub union_members: Vec<(TypeId, (Vec<TypePointer>, bool))>,
}

impl PrinterCollector {
    pub fn into_inner(self) -> FxHashMap<TypePointer, PrinterCollectorValue> {
        self.map
    }

    pub fn inner(&self) -> &FxHashMap<TypePointer, PrinterCollectorValue> {
        &self.map
    }

    pub fn add(&mut self, a: TypePointer, map: &mut PaddedTypeMap) {
        let t = map.dereference_without_find(a);
        if self.map.contains_key(&a) {
            return;
        }
        self.map.insert(a, Default::default());
        match t.diverged {
            None => panic!(),
            Some(true) => (),
            Some(false) => {
                let mut union_members = Vec::new();
                for (tag, args) in t.type_map.clone() {
                    if tag == ast_step1::TypeId::Intrinsic(crate::intrinsics::IntrinsicTypeTag::Fn)
                    {
                        continue;
                    }
                    for a in &args.0 {
                        self.add(*a, map);
                    }
                    union_members.push((tag, args));
                }
                self.map.insert(a, PrinterCollectorValue { union_members });
            }
        }
    }
}
