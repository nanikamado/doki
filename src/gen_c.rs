use crate::intrinsics::IntrinsicVariableExt;
use crate::parse::{Ast, Expr};
use doki::intrinsics::IntoEnumIterator;
use doki::{Block, GlobalVariable, LocalVariable};
use rustc_hash::FxHashMap;

#[derive(Debug, Default)]
struct Env<'a> {
    local_variable_map: FxHashMap<&'a str, LocalVariable>,
    global_variable_map: FxHashMap<&'a str, GlobalVariable>,
    data_decl_map: FxHashMap<&'a str, doki::ConstructorId>,
    build_env: doki::Env,
}

pub fn gen_c(ast: Ast) -> String {
    let mut env = Env::default();
    for d in ast.data_decls {
        let constructor_id = env
            .build_env
            .new_constructor(d.field_len, d.name.to_string());
        env.data_decl_map.insert(d.name, constructor_id);
        let decl_id = env.build_env.new_global_variable();
        env.global_variable_map.insert(d.name, decl_id);
        let ret_global = env.build_env.new_local_variable();
        let mut ret = ret_global;
        let mut block = env.build_env.new_block();
        let mut b = &mut block;
        let mut args = Vec::new();
        for _ in 0..d.field_len {
            let l = env.build_env.lambda(b, ret);
            b = l.body;
            ret = l.ret;
            args.push(l.parameter);
        }
        env.build_env.construction(ret, args, constructor_id, b);
        let d = doki::VariableDecl {
            value: block,
            ret: ret_global,
            decl_id,
            name: d.name.to_string(),
        };
        env.build_env.set_global_variable(d);
    }
    for d in doki::intrinsics::IntrinsicVariable::iter() {
        let decl_id = env.build_env.new_global_variable();
        env.global_variable_map.insert(d.to_str(), decl_id);
        let ret_global = env.build_env.new_local_variable();
        let mut ret = ret_global;
        let mut block = env.build_env.new_block();
        let mut b = &mut block;
        let mut args = Vec::new();
        for _ in 0..d.parameter_len() {
            let l = env.build_env.lambda(b, ret);
            b = l.body;
            ret = l.ret;
            args.push(l.parameter);
        }
        env.build_env.intrinsic_call(ret, args, d, b);
        let d = doki::VariableDecl {
            value: block,
            ret: ret_global,
            decl_id,
            name: d.to_str().to_string(),
        };
        env.build_env.set_global_variable(d);
    }
    for d in &ast.variable_decls {
        let gid = env.build_env.new_global_variable();
        env.global_variable_map.insert(d.name, gid);
    }
    for d in ast.variable_decls {
        let ret = env.build_env.new_local_variable();
        let mut block = env.build_env.new_block();
        env.expr(d.expr, ret, &mut block);
        let d = doki::VariableDecl {
            value: block,
            ret,
            decl_id: env.global_variable_map[d.name],
            name: d.name.to_string(),
        };
        env.build_env.set_global_variable(d);
    }
    // env.build_env.intrinsic_call(
    //     ret,
    //     args,
    //     doki::intrinsics::IntrinsicVariable::AppendStr,
    //     block,
    // );
    let entry_point = env.global_variable_map["main"];
    env.build_env.gen_c(entry_point)
}

impl<'a> Env<'a> {
    fn expr(&mut self, e: Expr<'a>, ret: LocalVariable, block: &mut Block) {
        match e {
            Expr::Ident(s) => {
                if let Some(v) = self.global_variable_map.get(s) {
                    self.build_env.global_variable(ret, *v, block);
                } else if let Some(v) = self.local_variable_map.get(s) {
                    self.build_env.local_variable(ret, *v, block);
                } else {
                    panic!("variable `{s}` not found in this scope")
                }
            }
            Expr::Lambda { param, expr } => {
                let l = self.build_env.lambda(block, ret);
                let shadowed = self.local_variable_map.get(param).copied();
                self.local_variable_map.insert(param, l.parameter);
                self.expr(*expr, l.ret, l.body);
                if let Some(s) = shadowed {
                    self.local_variable_map.insert(param, s);
                }
            }
            Expr::Call(f, a) => {
                let fv = self.build_env.new_local_variable();
                let av = self.build_env.new_local_variable();
                self.expr(*f, fv, block);
                self.expr(*a, av, block);
                self.build_env.call(fv, av, ret, block);
            }
            Expr::Num(s) => {
                self.build_env.i64(ret, s.to_string(), block);
            }
            Expr::Str(s) => {
                self.build_env.string(ret, s, block);
            }
        }
    }
}
