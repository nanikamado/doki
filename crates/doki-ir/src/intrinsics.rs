use crate::ast_step1::{self, PaddedTypeMap, TypePointer};
use crate::TypeId;
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
    SetMut,
    GetMut,
    GetChar,
}

impl Display for IntrinsicVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

impl IntrinsicVariable {
    pub fn parameter_len(self) -> usize {
        use IntrinsicVariable::*;
        match self {
            Minus | Plus | Percent | Multi | Div | Lt | Eq | AppendStr | SetMut => 2,
            PrintStr | I64ToString | Mut | GetMut | GetChar => 1,
        }
    }

    pub fn runtime_return_type(self) -> Option<IntrinsicTypeTag> {
        use IntrinsicVariable::*;
        match self {
            Minus | Plus | Percent | Multi | Div | Lt | Eq | GetChar => Some(IntrinsicTypeTag::I64),
            PrintStr | SetMut => Some(IntrinsicTypeTag::Unit),
            I64ToString | AppendStr => Some(IntrinsicTypeTag::String),
            Mut => Some(IntrinsicTypeTag::Mut),
            GetMut => None,
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
            SetMut => {
                debug_assert_eq!(arg_types.len(), 2);
                type_map.insert_normal(t, TypeId::Intrinsic(IntrinsicTypeTag::Unit), Vec::new());
                type_map.insert_normal(
                    arg_types[0],
                    TypeId::Intrinsic(IntrinsicTypeTag::Mut),
                    vec![arg_types[1]],
                )
            }
            GetMut => {
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
            SetMut => vec![Some(TypeId::Intrinsic(IntrinsicTypeTag::Mut)), None],
            GetMut => vec![Some(TypeId::Intrinsic(IntrinsicTypeTag::Mut))],
            GetChar => vec![I64],
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntrinsicTypeTag {
    String,
    I64,
    U8,
    Unit,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, EnumIter)]
pub enum IntrinsicConstructor {
    Unit,
}

impl Display for IntrinsicConstructor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

impl From<IntrinsicConstructor> for IntrinsicTypeTag {
    fn from(c: IntrinsicConstructor) -> Self {
        match c {
            IntrinsicConstructor::Unit => Self::Unit,
        }
    }
}
