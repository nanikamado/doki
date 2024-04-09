mod codegen;
pub mod intrinsics;
mod ir1;
mod ir2;
mod tail_recursion_elimination;
mod util;

pub use crate::ir1::{
    Block, CodegenOptions, ConstructorId, ConstructorNames, Env, GlobalVariable, Lambda,
    LocalVariable, TypeId, VariableDecl,
};
pub use crate::ir2::{
    DisplayTypeWithEnvStruct as DisplayTypeWithEnv, LocalVariable as LocalVariable2, Type,
};
use codegen::Codegen;
use std::fmt::Display;

impl<'a> Env<'a> {
    pub fn gen_c<S: Display>(
        self,
        entry_point: GlobalVariable,
        span_of_main: S,
    ) -> impl Display + 'a {
        let mut ast = self.build_ast_step2(entry_point, span_of_main);
        tail_recursion_elimination::run(&mut ast);
        Codegen(ast)
    }

    pub fn build_ast_step2<S: Display>(
        self,
        entry_point: GlobalVariable,
        span_of_main: S,
    ) -> ir2::Ast<'a> {
        let ast = self.build(entry_point, span_of_main);
        ir2::Ast::from(ast)
    }
}
