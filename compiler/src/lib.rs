use doki_ir::ConstructorNames;
pub use doki_ir::DisplayTypeWithEnv;
pub use gen_c::gen_c;
pub use parser::{parse, ParseError, Span};
use std::collections::BTreeMap;

mod gen_c;
mod intrinsics;

pub struct AnalyzedSrc {
    pub token_map: BTreeMap<Span, Vec<doki_ir::Type>>,
    pub constructor_names: ConstructorNames,
}

pub fn token_map(src: &str) -> Result<AnalyzedSrc, ParseError> {
    let ast = parser::parse(src)?;
    Ok(gen_c::token_map(ast))
}
