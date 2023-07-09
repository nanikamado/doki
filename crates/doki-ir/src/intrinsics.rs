use crate::ast_step1::{self, PaddedTypeMap, TypePointer};
use crate::{ast_step2, TypeId};
use once_cell::sync::Lazy;
use rustc_hash::FxHashMap;
use std::fmt::Display;
use strum::EnumIter;
pub use strum::IntoEnumIterator;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, EnumIter)]
pub enum IntrinsicVariable {
    Minus,
    Plus,
    Percent,
    Multi,
    Div,
    Lt,
    Eq,
    PrintStr,
    I64ToString,
    AppendStr,
    Mut,
    Set,
    Get,
}

impl Display for IntrinsicVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

const fn runtime_intrinsic_type(i: IntrinsicTypeTag) -> ast_step2::TypeUnitForHash {
    ast_step2::TypeUnitOf::Normal {
        id: ast_step1::TypeId::Intrinsic(i),
        args: Vec::new(),
    }
}

impl IntrinsicVariable {
    pub fn parameter_len(self) -> usize {
        use IntrinsicVariable::*;
        match self {
            Minus | Plus | Percent | Multi | Div | Lt | Eq | AppendStr | Set => 2,
            PrintStr | I64ToString | Mut | Get => 1,
        }
    }

    pub fn runtime_return_type(self) -> Option<IntrinsicTypeTag> {
        use IntrinsicVariable::*;
        match self {
            Minus | Plus | Percent | Multi | Div | Lt | Eq => Some(IntrinsicTypeTag::I64),
            PrintStr | Set => Some(IntrinsicTypeTag::Unit),
            I64ToString | AppendStr => Some(IntrinsicTypeTag::String),
            Mut => Some(IntrinsicTypeTag::Mut),
            Get => None,
        }
    }

    pub fn insert_return_type(
        self,
        t: TypePointer,
        type_map: &mut PaddedTypeMap,
        arg_types: &[TypePointer],
        pointer_of_mut: &mut Vec<TypePointer>,
    ) {
        use IntrinsicVariable::*;
        match self {
            Mut => {
                debug_assert_eq!(arg_types.len(), 1);
                pointer_of_mut.push(arg_types[0]);
                type_map.insert_normal(
                    t,
                    TypeId::Intrinsic(IntrinsicTypeTag::Mut),
                    vec![arg_types[0]],
                )
            }
            Set => {
                debug_assert_eq!(arg_types.len(), 2);
                type_map.insert_normal(t, TypeId::Intrinsic(IntrinsicTypeTag::Unit), Vec::new());
                type_map.insert_normal(
                    arg_types[0],
                    TypeId::Intrinsic(IntrinsicTypeTag::Mut),
                    vec![arg_types[1]],
                )
            }
            Get => {
                debug_assert_eq!(arg_types.len(), 1);
                type_map.insert_normal(
                    arg_types[0],
                    TypeId::Intrinsic(IntrinsicTypeTag::Mut),
                    vec![t],
                )
            }
            _ => {
                let ret_type = self.runtime_return_type().unwrap();
                type_map.insert_normal(t, TypeId::Intrinsic(ret_type), Vec::new());
            }
        }
    }

    pub fn runtime_arg_type_restriction(self) -> Vec<Option<ast_step1::TypeId>> {
        use IntrinsicVariable::*;
        const I64: Option<TypeId> = Some(TypeId::Intrinsic(IntrinsicTypeTag::I64));
        const STRING: Option<TypeId> = Some(TypeId::Intrinsic(IntrinsicTypeTag::String));
        match self {
            Minus | Plus | Percent | Multi | Div | Lt | Eq => vec![I64, I64],
            PrintStr => vec![STRING],
            I64ToString => vec![I64],
            AppendStr => vec![STRING, STRING],
            Mut => vec![None],
            Set => vec![Some(TypeId::Intrinsic(IntrinsicTypeTag::Mut)), None],
            Get => vec![Some(TypeId::Intrinsic(IntrinsicTypeTag::Mut))],
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntrinsicTypeTag {
    String,
    I64,
    U8,
    Unit,
    True,
    False,
    Fn,
    Mut,
}

impl IntrinsicTypeTag {
    pub fn parameter_len(self) -> usize {
        if let Self::Fn = self {
            2
        } else {
            0
        }
    }
}

pub static INTRINSIC_TYPES: Lazy<FxHashMap<&'static str, IntrinsicTypeTag>> = Lazy::new(|| {
    [
        ("String", IntrinsicTypeTag::String),
        ("I64", IntrinsicTypeTag::I64),
        ("()", IntrinsicTypeTag::Unit),
        ("True", IntrinsicTypeTag::True),
        ("False", IntrinsicTypeTag::False),
        ("->", IntrinsicTypeTag::Fn),
    ]
    .map(|(n, t)| (n, t))
    .iter()
    .cloned()
    .collect()
});

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, EnumIter)]
pub enum IntrinsicConstructor {
    Unit,
    True,
    False,
}

impl Display for IntrinsicConstructor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

pub static INTRINSIC_CONSTRUCTORS: Lazy<FxHashMap<String, IntrinsicConstructor>> =
    Lazy::new(|| {
        [
            ("()", IntrinsicConstructor::Unit),
            ("True", IntrinsicConstructor::True),
            ("False", IntrinsicConstructor::False),
        ]
        .map(|(n, t)| (n.to_string(), t))
        .iter()
        .cloned()
        .collect()
    });

impl IntrinsicConstructor {
    pub fn to_str(self) -> &'static str {
        match self {
            IntrinsicConstructor::Unit => "()",
            IntrinsicConstructor::True => "True",
            IntrinsicConstructor::False => "False",
        }
    }

    pub fn to_runtime_type(self) -> ast_step2::TypeForHash {
        runtime_intrinsic_type(self.into()).into()
    }
}

impl From<IntrinsicConstructor> for IntrinsicTypeTag {
    fn from(c: IntrinsicConstructor) -> Self {
        match c {
            IntrinsicConstructor::Unit => Self::Unit,
            IntrinsicConstructor::True => Self::True,
            IntrinsicConstructor::False => Self::False,
        }
    }
}
