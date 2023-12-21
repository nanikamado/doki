use doki_ir::intrinsics::IntrinsicVariable;
use easy_ext::ext;

#[ext(IntrinsicVariableExt)]
impl IntrinsicVariable {
    pub fn to_str(self) -> &'static str {
        use IntrinsicVariable::*;
        match self {
            Minus => "intrinsic_minus",
            Plus => "intrinsic_plus",
            Percent => "intrinsic_rem",
            Multi => "intrinsic_mul",
            Div => "intrinsic_div",
            Lt => "intrinsic_lt",
            Eq => "intrinsic_eq",
            EqU8 => "intrinsic_eq_u8",
            BitAnd => "intrinsic_bitwise_and",
            BitOr => "intrinsic_bitwise_or",
            BitAndU8 => "intrinsic_bitwise_and_u8",
            BitOrU8 => "intrinsic_bitwise_or_u8",
            RightShift => "intrinsic_right_shift",
            RightShiftU8 => "intrinsic_right_shift_u8",
            Write => "intrinsic_write",
            Mut => "intrinsic_mut",
            SetMut => "intrinsic_set",
            GetMut => "intrinsic_get",
            GetChar => "intrinsic_getchar",
            Malloc => "intrinsic_malloc",
            LoadU8 => "intrinsic_load_u8",
            StoreU8 => "intrinsic_store_u8",
            LoadF64 => "intrinsic_load_f64",
            StoreF64 => "intrinsic_store_f64",
            I64ToU8 => "intrinsic_i64_to_u8",
            U8ToI64 => "intrinsic_u8_to_i64",
            ReadFile => "intrinsic_read_file",
            Stdout => "intrinsic_stdout",
            Stdin => "intrinsic_stdin",
            PlusF64 => "intrinsic_plus_f64",
            MinusF64 => "intrinsic_minus_f64",
            MultiF64 => "intrinsic_mul_f64",
            DivF64 => "intrinsic_div_f64",
            LeF64 => "intrinsic_le_f64",
            LtF64 => "intrinsic_lt_f64",
            EqF64 => "intrinsic_eq_f64",
            WriteF64 => "intrinsic_write_f64",
            F64StrLen => "intrinsic_f64_str_len",
            SqrtF64 => "intrinsic_sqrt_f64",
        }
    }
}
