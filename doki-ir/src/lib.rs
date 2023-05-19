mod ast_step1;
mod ast_step2;
mod codegen;
pub mod intrinsics;

pub use crate::ast_step1::{
    Block, ConstructorId, Env, GlobalVariable, Lambda, LocalVariable, TypeId, VariableDecl,
};
use std::io::Write;

impl Env {
    pub fn gen_c(self, entry_point: GlobalVariable, w: &mut impl Write) {
        let ast = self.build_ast4(entry_point);
        let ast = ast_step2::Ast::from(ast);
        codegen::codegen(ast, w)
    }
}
