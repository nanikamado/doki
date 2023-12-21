use crate::ast_step1::{self, PaddedTypeMap, TypePointer};
use crate::TypeId;
use std::fmt::Display;
use strum::EnumIter;
pub use strum::IntoEnumIterator;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, EnumIter)]
pub enum IntrinsicVariable {
    Minus,
    MinusF64,
    Plus,
    PlusF64,
    Multi,
    MultiF64,
    Div,
    DivF64,
    Lt,
    LtF64,
    LeF64,
    Eq,
    EqU8,
    EqF64,
    BitAnd,
    BitAndU8,
    BitOr,
    BitOrU8,
    RightShift,
    RightShiftU8,
    Percent,
    Write,
    Mut,
    SetMut,
    GetMut,
    GetChar,
    Malloc,
    LoadU8,
    StoreU8,
    LoadF64,
    StoreF64,
    U8ToI64,
    I64ToU8,
    ReadFile,
    Stdout,
    Stdin,
    WriteF64,
    F64StrLen,
    SqrtF64,
}

impl Display for IntrinsicVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

impl IntrinsicVariable {
    pub fn runtime_return_type(self) -> Option<IntrinsicTypeTag> {
        use IntrinsicVariable::*;
        match self {
            Minus | Plus | Percent | Multi | Div | Lt | Eq | EqU8 | EqF64 | GetChar | U8ToI64
            | BitAnd | BitOr | RightShift | ReadFile | F64StrLen => Some(IntrinsicTypeTag::I64),
            Write | SetMut | StoreU8 | StoreF64 | WriteF64 => Some(IntrinsicTypeTag::Unit),
            Mut => Some(IntrinsicTypeTag::Mut),
            Malloc | Stdout | Stdin => Some(IntrinsicTypeTag::Ptr),
            LoadU8 | I64ToU8 | BitAndU8 | BitOrU8 | RightShiftU8 => Some(IntrinsicTypeTag::U8),
            GetMut => None,
            LoadF64 | PlusF64 | MinusF64 | DivF64 | LeF64 | LtF64 | MultiF64 | SqrtF64 => {
                Some(IntrinsicTypeTag::F64)
            }
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
        const U8: Option<TypeId> = Some(TypeId::Intrinsic(IntrinsicTypeTag::U8));
        const PTR: Option<TypeId> = Some(TypeId::Intrinsic(IntrinsicTypeTag::Ptr));
        const MUT: Option<TypeId> = Some(TypeId::Intrinsic(IntrinsicTypeTag::Mut));
        const F64: Option<TypeId> = Some(TypeId::Intrinsic(IntrinsicTypeTag::F64));
        match self {
            Minus | Plus | Percent | Multi | Div | Lt | Eq | BitAnd | BitOr | RightShift => {
                vec![I64, I64]
            }
            PlusF64 | MinusF64 | MultiF64 | DivF64 | LeF64 | LtF64 | EqF64 => {
                vec![F64, F64]
            }
            EqU8 | BitAndU8 | BitOrU8 => vec![U8, U8],
            RightShiftU8 => vec![U8, I64],
            Write => vec![PTR, I64, I64],
            Malloc | I64ToU8 | GetChar => vec![I64],
            U8ToI64 => vec![U8],
            Mut => vec![None],
            SetMut => vec![MUT, None],
            GetMut => vec![MUT],
            LoadU8 | LoadF64 => vec![PTR, I64],
            StoreU8 => vec![PTR, I64, U8],
            StoreF64 => vec![PTR, I64, F64],
            ReadFile => vec![PTR, I64, I64, PTR, MUT],
            Stdout | Stdin => Vec::new(),
            WriteF64 => vec![PTR, I64, F64, PTR],
            SqrtF64 => vec![F64],
            F64StrLen => vec![F64, PTR],
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntrinsicTypeTag {
    Ptr,
    I64,
    U8,
    F64,
    Unit,
    Mut,
    Fn,
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
