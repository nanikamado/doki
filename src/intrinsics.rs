use doki::intrinsics::IntrinsicVariable;
use easy_ext::ext;

#[ext(IntrinsicVariableExt)]
impl IntrinsicVariable {
    pub fn to_str(self) -> &'static str {
        match self {
            IntrinsicVariable::Minus => "minus",
            IntrinsicVariable::Plus => "plus",
            IntrinsicVariable::Percent => "rem",
            IntrinsicVariable::Multi => "mul",
            IntrinsicVariable::Div => "div",
            IntrinsicVariable::Lt => "lt",
            IntrinsicVariable::Eq => "eq",
            IntrinsicVariable::PrintStr => "print_str",
            IntrinsicVariable::I64ToString => "i64_to_string",
            IntrinsicVariable::AppendStr => "append_str",
        }
    }
}
