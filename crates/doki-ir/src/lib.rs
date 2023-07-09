mod ast_step1;
mod ast_step2;
mod codegen;
mod collector;
mod id_generator;
pub mod intrinsics;

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

impl Env {
    pub fn gen_c(self, entry_point: GlobalVariable, minimize_type: bool) -> impl Display {
        let ast = self.build(entry_point);
        let ast = ast_step2::Ast::from(ast, minimize_type);
        Codegen(ast)
    }

    pub fn build_ast_step2(
        self,
        entry_point: GlobalVariable,
        minimize_type: bool,
    ) -> ast_step2::Ast {
        let ast = self.build(entry_point);
        ast_step2::Ast::from(ast, minimize_type)
    }
}
