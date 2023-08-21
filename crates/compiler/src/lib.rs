use doki_ir::ConstructorNames;
pub use doki_ir::DisplayTypeWithEnv;
pub use gen_c::{gen_c, SpanMapEntry};
pub use parser::{ParseError, Span};
use rustc_hash::FxHashMap;
use std::collections::BTreeMap;
use std::fs;
use std::path::Path;
use typed_arena::Arena;

mod gen_c;
mod intrinsics;

pub struct AnalyzedSrc<'a> {
    pub span_map: BTreeMap<Span<'a>, SpanMapEntry>,
    pub constructor_names: ConstructorNames,
}

pub fn token_map<'a>(
    path: &'a str,
    src_files: &mut FxHashMap<&'a str, &'a str>,
    minimize_type: bool,
    arena: &'a Arena<String>,
) -> Result<AnalyzedSrc<'a>, (&'a str, ParseError<'a>)> {
    let ast = parse(path, src_files, arena)?;
    Ok(gen_c::token_map(ast, path, src_files, minimize_type))
}

pub fn parse<'a>(
    path: &'a str,
    src_files: &mut FxHashMap<&'a str, &'a str>,
    arena: &'a Arena<String>,
) -> Result<parser::Ast<'a>, (&'a str, ParseError<'a>)> {
    let p = Path::new(path).parent().unwrap();
    let src = fs::read_to_string(path).unwrap();
    let src = src_files
        .entry(arena.alloc(path.to_string()))
        .or_insert(arena.alloc(src));
    let mut ast = parser::parse(src, path).map_err(|e| (path, e))?;
    let mut imports = ast.imports.clone();
    while let Some(i) = imports.pop() {
        let i = p.join(i).canonicalize().unwrap();
        let src = fs::read_to_string(&i).unwrap();
        let i = arena.alloc(i.to_str().unwrap().to_string());
        use std::collections::hash_map::Entry::*;
        if let Vacant(e) = src_files.entry(i) {
            let src = e.insert(arena.alloc(src));
            let mut a = parser::parse(src, i).map_err(|e| (i.as_str(), e))?;
            ast.variable_decls.append(&mut a.variable_decls);
            ast.data_decls.append(&mut a.data_decls);
            imports.append(&mut a.imports);
        }
    }
    Ok(ast)
}
