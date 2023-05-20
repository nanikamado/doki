use doki_ir::LocalVariable;
pub use parser::Span;
use std::collections::BTreeMap;
use std::io::Write;

mod gen_c;
mod intrinsics;

pub fn compile(src: &str, filename: &str, w: &mut impl Write) {
    let ast = parser::parse(src, filename);
    gen_c::gen_c(ast, w)
}

pub fn token_map(src: &str, filename: &str) -> Option<BTreeMap<Span, LocalVariable>> {
    let ast = parser::parse(src, filename);
    Some(gen_c::token_map(ast))
}
