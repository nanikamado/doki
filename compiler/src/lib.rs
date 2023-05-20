use doki_ir::LocalVariable;
pub use gen_c::gen_c;
pub use parser::{parse, ParseError, Span};
use std::collections::BTreeMap;

mod gen_c;
mod intrinsics;

pub fn token_map(src: &str) -> Result<BTreeMap<Span, LocalVariable>, ParseError> {
    let ast = parser::parse(src)?;
    Ok(gen_c::token_map(ast))
}
