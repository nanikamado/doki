use crate::intrinsics::IntrinsicVariableExt;
use crate::parse::{Ast, Expr, Pattern};
use doki_ir::intrinsics::IntoEnumIterator;
use doki_ir::{Block, GlobalVariable, LocalVariable};
use rustc_hash::FxHashMap;

#[derive(Debug, Default)]
struct Env<'a> {
    local_variable_map: FxHashMap<&'a str, LocalVariable>,
    global_variable_map: FxHashMap<&'a str, GlobalVariable>,
    data_decl_map: FxHashMap<&'a str, doki_ir::ConstructorId>,
    build_env: doki_ir::Env,
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
        let d = doki_ir::VariableDecl {
            value: block,
            ret: ret_global,
            decl_id,
            name: d.name.to_string(),
        };
        env.build_env.set_global_variable(d);
    }
    for d in doki_ir::intrinsics::IntrinsicVariable::iter() {
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
        let d = doki_ir::VariableDecl {
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
        let d = doki_ir::VariableDecl {
            value: block,
            ret,
            decl_id: env.global_variable_map[d.name],
            name: d.name.to_string(),
        };
        env.build_env.set_global_variable(d);
    }
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
                self.let_in(l.ret, param, l.parameter, *expr, l.body);
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
            Expr::Match { operand, branches } => {
                let operand_v = self.build_env.new_local_variable();
                self.expr(*operand, operand_v, block);
                let mut b = Block::default();
                b.panic("match is not exhaustive".to_string());
                for (p, e) in branches.into_iter().rev() {
                    let mut b2 = Block::default();
                    self.let_in(ret, p, operand_v, e, &mut b2);
                    b = b2.try_catch(b);
                }
                block.append(b);
            }
            Expr::Let(p, e1, e2) => {
                let l = self.build_env.new_local_variable();
                self.expr(*e1, l, block);
                self.let_in(ret, p, l, *e2, block);
            }
        }
    }

    fn let_in(
        &mut self,
        ret: LocalVariable,
        mut p: Pattern<'a>,
        v: LocalVariable,
        e: Expr<'a>,
        block: &mut Block,
    ) {
        self.find_field_less_constructor(&mut p);
        let mut shadowed_variables = FxHashMap::default();
        self.binds_in_pattern(&p, &mut shadowed_variables);
        self.pattern(&p, v, block);
        self.expr(e, ret, block);
        for (name, v) in shadowed_variables {
            if let Some(v) = v {
                self.local_variable_map.insert(name, v);
            }
        }
    }

    fn find_field_less_constructor(&self, p: &mut Pattern<'a>) {
        match p {
            Pattern::Wildcard | Pattern::Str(_) | Pattern::Num(_) => (),
            Pattern::Constructor { name, fields } => {
                if self.data_decl_map.contains_key(name) {
                    for f in fields {
                        self.find_field_less_constructor(f);
                    }
                } else {
                    if !fields.is_empty() {
                        panic!("`{name}` is not a constructor");
                    }
                    *p = Pattern::Bind(name)
                }
            }
            Pattern::Or(a, b) => {
                self.find_field_less_constructor(a);
                self.find_field_less_constructor(b);
            }
            Pattern::Bind(_) => panic!(),
        }
    }

    fn binds_in_pattern(
        &mut self,
        p: &Pattern<'a>,
        shadowed_variables: &mut FxHashMap<&'a str, Option<LocalVariable>>,
    ) {
        match p {
            Pattern::Bind(name) => {
                if !shadowed_variables.contains_key(name) {
                    shadowed_variables.insert(name, self.local_variable_map.get(name).copied());
                    let l = self.build_env.new_local_variable();
                    self.local_variable_map.insert(name, l);
                }
            }
            Pattern::Wildcard | Pattern::Num(_) | Pattern::Str(_) => (),
            Pattern::Constructor { name: _, fields } => {
                if !fields.is_empty() {
                    let f = &fields[0];
                    let mut binds_in_f = FxHashMap::default();
                    self.binds_in_pattern(f, &mut binds_in_f);
                    shadowed_variables.extend(&binds_in_f);
                    for g in &fields[1..] {
                        let mut binds_in_g = FxHashMap::default();
                        self.binds_in_pattern(g, &mut binds_in_g);
                        shadowed_variables.extend(&binds_in_g);
                        for f in binds_in_f.keys() {
                            if binds_in_g.contains_key(f) {
                                panic!("variable {f} is defined twice");
                            }
                        }
                    }
                }
            }
            Pattern::Or(a, b) => {
                let mut binds_in_a = FxHashMap::default();
                self.binds_in_pattern(a, &mut binds_in_a);
                let mut binds_in_b = FxHashMap::default();
                self.binds_in_pattern(b, &mut binds_in_b);
                for a in binds_in_a.keys() {
                    if !binds_in_b.contains_key(a) {
                        panic!("`{a}` is not in some branch");
                    }
                }
                for b in binds_in_b.keys() {
                    if !binds_in_a.contains_key(b) {
                        panic!("`{b}` is not in some branch");
                    }
                }
                shadowed_variables.extend(binds_in_a);
            }
        }
    }

    fn pattern(&mut self, e: &Pattern<'a>, operand: LocalVariable, block: &mut Block) {
        match e {
            Pattern::Bind(name) => {
                let v = self.local_variable_map[name];
                self.build_env.local_variable(v, operand, block);
            }
            Pattern::Wildcard => (),
            Pattern::Constructor { name, fields } => {
                let d = self.data_decl_map[name];
                block.test_constructor(operand, doki_ir::TypeId::UserDefined(d));
                for (i, f) in fields.iter().enumerate() {
                    let ret = self.build_env.new_local_variable();
                    self.build_env.field_access(ret, operand, d, i, block);
                    self.pattern(f, ret, block);
                }
            }
            Pattern::Or(a, b) => {
                let mut a_block = Block::default();
                self.pattern(a, operand, &mut a_block);
                let mut b_block = Block::default();
                self.pattern(b, operand, &mut b_block);
                block.append(a_block.try_catch(b_block));
            }
            Pattern::Num(a) => {
                block.test_number(operand, a.to_string());
            }
            Pattern::Str(a) => {
                block.test_string(operand, a.clone());
            }
        }
    }
}
