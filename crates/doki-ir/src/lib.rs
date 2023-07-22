mod ast_step1;
mod ast_step2;
mod codegen;
mod collector;
mod id_generator;
pub mod intrinsics;
mod scc;
mod tail_recursion_elimination;

pub use crate::ast_step1::{
    Block, ConstructorId, ConstructorNames, Env, GlobalVariable, Lambda, LocalVariable, TypeId,
    VariableDecl,
};
pub use crate::ast_step2::{
    DisplayTypeWithEnvStruct as DisplayTypeWithEnv, LocalVariable as LocalVariable2, Type,
    TypeForHash,
};
use codegen::Codegen;
use std::fmt::Display;

impl<'a> Env<'a> {
    pub fn gen_c(self, entry_point: GlobalVariable, minimize_type: bool) -> impl Display + 'a {
        let ast = self.build(entry_point);
        let mut ast = ast_step2::Ast::from(ast, minimize_type);
        tail_recursion_elimination::run(&mut ast);
        Codegen(ast)
    }

    pub fn build_ast_step2(
        self,
        entry_point: GlobalVariable,
        minimize_type: bool,
    ) -> ast_step2::Ast<'a> {
        let ast = self.build(entry_point);
        ast_step2::Ast::from(ast, minimize_type)
    }
}
