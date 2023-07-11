use doki_ir::intrinsics::IntrinsicVariable;
use easy_ext::ext;

#[ext(IntrinsicVariableExt)]
impl IntrinsicVariable {
    pub fn to_str(self) -> &'static str {
        match self {
            IntrinsicVariable::Minus => "intrinsic_minus",
            IntrinsicVariable::Plus => "intrinsic_plus",
            IntrinsicVariable::Percent => "intrinsic_rem",
            IntrinsicVariable::Multi => "intrinsic_mul",
            IntrinsicVariable::Div => "intrinsic_div",
            IntrinsicVariable::Lt => "intrinsic_lt",
            IntrinsicVariable::Eq => "intrinsic_eq",
            IntrinsicVariable::PrintStr => "intrinsic_print_str",
            IntrinsicVariable::I64ToString => "intrinsic_i64_to_string",
            IntrinsicVariable::AppendStr => "intrinsic_append_str",
            IntrinsicVariable::Mut => "intrinsic_mut",
            IntrinsicVariable::SetMut => "intrinsic_set",
            IntrinsicVariable::GetMut => "intrinsic_get",
        }
    }
}
