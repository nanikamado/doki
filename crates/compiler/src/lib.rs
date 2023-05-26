use doki_ir::ConstructorNames;
pub use doki_ir::DisplayTypeWithEnv;
pub use gen_c::{gen_c, SpanMapEntry};
pub use parser::{parse, ParseError, Span};
use std::collections::BTreeMap;

mod gen_c;
mod intrinsics;

pub struct AnalyzedSrc {
    pub span_map: BTreeMap<Span, SpanMapEntry>,
    pub constructor_names: ConstructorNames,
}

pub fn token_map(src: &str, minimize_type: bool) -> Result<AnalyzedSrc, ParseError> {
    let ast = parser::parse(src)?;
    Ok(gen_c::token_map(ast, minimize_type))
}
