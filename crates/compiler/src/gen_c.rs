use crate::intrinsics::IntrinsicVariableExt;
use crate::AnalyzedSrc;
use doki_ir::intrinsics::IntoEnumIterator;
use doki_ir::{Block, ConstructorId, GlobalVariable, LocalVariable};
use itertools::Itertools;
use parser::{Ast, DataDecl, Expr, ExprWithSpan, Pattern, PatternWithSpan, Span};
use rustc_hash::{FxHashMap, FxHasher};
use std::collections::BTreeMap;
use std::fmt::Display;
use std::iter::once;

#[derive(Debug)]
struct Env<'a> {
    local_variable_map: FxHashMap<&'a str, LocalVariable>,
    global_variable_map: FxHashMap<&'a str, GlobalVariable>,
    data_decl_map: FxHashMap<&'a str, doki_ir::ConstructorId>,
    build_env: doki_ir::Env<'a>,
    local_variable_span_map: BTreeMap<Span<'a>, LocalVariable>,
    global_variable_span_map: BTreeMap<Span<'a>, GlobalVariable>,
    str_constructor_id: Option<ConstructorId>,
    utf8_to_utf16_ln_col_map: FxHashMap<&'a str, Vec<(u32, u32)>>,
    entry_point: Option<(GlobalVariable, Span<'a>)>,
}

fn build<'a>(
    ast: Ast<'a>,
    src_files: &FxHashMap<&'a str, &'a str>,
    minimize_types: bool,
) -> Env<'a> {
    let utf8_to_utf16_ln_col_map = src_files
        .iter()
        .map(|(n, s)| (*n, utf8_to_utf16_ln_col(s)))
        .collect();
    let mut env = Env {
        utf8_to_utf16_ln_col_map,
        local_variable_map: Default::default(),
        global_variable_map: Default::default(),
        data_decl_map: Default::default(),
        build_env: doki_ir::Env::new(minimize_types),
        local_variable_span_map: Default::default(),
        global_variable_span_map: Default::default(),
        str_constructor_id: Default::default(),
        entry_point: None,
    };
    for d in ast.data_decls.into_iter().chain(once(DataDecl {
        name: "Str",
        field_len: 2,
    })) {
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
            name: d.name,
        };
        env.build_env.set_global_variable(d);
    }
    env.str_constructor_id = Some(env.data_decl_map["Str"]);
    for d in doki_ir::intrinsics::IntrinsicVariable::iter() {
        let decl_id = env.build_env.new_global_variable();
        env.global_variable_map.insert(d.to_str(), decl_id);
        let ret_global = env.build_env.new_local_variable();
        let mut ret = ret_global;
        let mut block = env.build_env.new_block();
        let mut b = &mut block;
        let mut args = Vec::new();
        for _ in d.runtime_arg_type_restriction() {
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
            name: d.to_str(),
        };
        env.build_env.set_global_variable(d);
    }
    for d in &ast.variable_decls {
        let gid = env.build_env.new_global_variable();
        env.global_variable_map.insert(d.name, gid);
        env.global_variable_span_map.insert(d.ident_span, gid);
        if d.name == "main" {
            debug_assert!(env.entry_point.is_none());
            env.entry_point = Some((gid, d.expr.1));
        }
    }
    for d in ast.variable_decls {
        let ret = env.build_env.new_local_variable();
        let mut block = env.build_env.new_block();
        env.expr(d.expr, ret, &mut block);
        let d = doki_ir::VariableDecl {
            value: block,
            ret,
            decl_id: env.global_variable_map[d.name],
            name: d.name,
        };
        env.build_env.set_global_variable(d);
    }
    env
}

pub fn gen_c<'a>(
    ast: Ast<'a>,
    src_files: &mut FxHashMap<&'a str, &'a str>,
    minimize_types: bool,
) -> impl Display + 'a {
    let env = build(ast, src_files, minimize_types);
    let (entry_point, span) = env.entry_point.unwrap();
    let (ln, col) = env.utf8_to_utf16_ln_col_map[span.file_name][span.start];
    env.build_env
        .gen_c(entry_point, format!("{}:{ln}:{col}", span.file_name))
}

pub enum SpanMapEntry {
    Expr(Vec<doki_ir::Type>),
    GlobalVariable { ts: Vec<doki_ir::TypeForHash> },
}

pub fn token_map<'a>(
    ast: Ast<'a>,
    path: &str,
    src_files: &FxHashMap<&'a str, &'a str>,
    minimize_types: bool,
) -> AnalyzedSrc<'a> {
    let env = build(ast, src_files, minimize_types);
    let (entry_point, span) = env.entry_point.unwrap();
    let (ln, col) = env.utf8_to_utf16_ln_col_map[span.file_name][span.start];
    let ast = env
        .build_env
        .build_ast_step2(entry_point, format!("{}:{ln}:{col}", span.file_name));
    let global_variables: multimap::MultiMap<_, _, std::hash::BuildHasherDefault<FxHasher>> = ast
        .variable_decls
        .iter()
        .map(|v| {
            let t = &v.t_for_hash;
            (
                v.original_decl_id,
                (t.clone(), ast.type_id_generator.get(t).unwrap()),
            )
        })
        .collect();
    let mut span_map: BTreeMap<_, _> = env
        .global_variable_span_map
        .into_iter()
        .flat_map(|(s, g)| {
            if s.file_name == path {
                let ts = global_variables
                    .get_vec(&g)
                    .into_iter()
                    .flatten()
                    .map(|(t, _)| t.clone())
                    .collect_vec();
                Some((s, SpanMapEntry::GlobalVariable { ts }))
            } else {
                None
            }
        })
        .collect();
    let m: multimap::MultiMap<_, _, std::hash::BuildHasherDefault<FxHasher>> = ast
        .local_variable_replace_map
        .into_iter()
        .map(|((l, (id, g)), l2)| (l, (g, id, l2)))
        .collect();
    span_map.extend(env.local_variable_span_map.into_iter().flat_map(|(s, l)| {
        if s.file_name == path {
            let ts = m
                .get_vec(&l)
                .into_iter()
                .flatten()
                .sorted_by_key(|(g, id, _)| {
                    global_variables
                        .get_vec(g)
                        .unwrap()
                        .binary_search_by_key(id, |(_, id)| *id)
                })
                .map(|(_, _, l)| ast.variable_types.get_type(*l).clone().0.unwrap())
                .collect();
            Some((s, SpanMapEntry::Expr(ts)))
        } else {
            None
        }
    }));
    AnalyzedSrc {
        span_map,
        constructor_names: ast.constructor_names,
    }
}

impl<'a> Env<'a> {
    fn expr(&mut self, (e, span): ExprWithSpan<'a>, ret: LocalVariable, block: &mut Block) {
        self.local_variable_span_map.insert(span, ret);
        match e {
            Expr::Ident(s) => {
                if let Some(v) = self.local_variable_map.get(s) {
                    self.build_env.local_variable(ret, *v, block);
                } else if let Some(v) = self.global_variable_map.get(s) {
                    self.build_env.global_variable(ret, *v, block);
                } else {
                    panic!("variable `{s}` not found in this scope")
                }
            }
            Expr::Lambda { param, expr } => {
                let l = self.build_env.lambda(block, ret);
                let mut b = self.build_env.new_block();
                let (ln, col) = self.utf8_to_utf16_ln_col_map[param.1.file_name][param.1.start];
                b.panic(format!(
                    "pattern is not exhaustive\n{}:{ln}:{col}",
                    param.1.file_name,
                ));
                let mut b2 = self.build_env.new_block();
                self.let_in(l.ret, param, l.parameter, *expr, &mut b2);
                l.body.append(b2.try_catch(b));
            }
            Expr::Call(f, a) => {
                let fv = self.build_env.new_local_variable();
                let av = self.build_env.new_local_variable();
                self.expr(*f, fv, block);
                self.expr(*a, av, block);
                let (ln, col) = self.utf8_to_utf16_ln_col_map[span.file_name][span.start];
                self.build_env
                    .call(ret, fv, av, format!("{}:{ln}:{col}", span.file_name), block);
            }
            Expr::I64(s) => {
                self.build_env.i64(ret, s.parse().unwrap(), block);
            }
            Expr::U8(s) => {
                self.build_env.u8(ret, s.parse().unwrap(), block);
            }
            Expr::Str(s) => {
                let l = self.build_env.new_local_variable();
                self.build_env.i64(l, s.len() as i64, block);
                let p = self.build_env.new_local_variable();
                self.build_env.string(p, s, block);
                self.build_env.construction(
                    ret,
                    vec![l, p],
                    self.str_constructor_id.unwrap(),
                    block,
                )
            }
            Expr::Match { operand, branches } => {
                let file_name = operand.1.file_name;
                let (ln, col) = self.utf8_to_utf16_ln_col_map[operand.1.file_name][operand.1.start];
                let operand_v = self.build_env.new_local_variable();
                self.expr(*operand, operand_v, block);
                let mut b = Block::default();
                b.panic(format!("match is not exhaustive\n{}:{ln}:{col}", file_name,));
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
                let mut b = self.build_env.new_block();
                let (ln, col) = self.utf8_to_utf16_ln_col_map[p.1.file_name][p.1.start];
                b.panic(format!(
                    "pattern is not exhaustive\n{}:{ln}:{col}",
                    p.1.file_name,
                ));
                let mut b2 = self.build_env.new_block();
                self.let_in(ret, p, l, *e2, &mut b2);
                block.append(b2.try_catch(b));
            }
        }
    }

    fn let_in(
        &mut self,
        ret: LocalVariable,
        mut p: PatternWithSpan<'a>,
        v: LocalVariable,
        e: ExprWithSpan<'a>,
        block: &mut Block,
    ) {
        self.find_field_less_constructor(&mut p.0);
        let mut shadowed_variables = FxHashMap::default();
        self.binds_in_pattern(&p, &mut shadowed_variables);
        self.pattern(&p, v, block);
        self.expr(e, ret, block);
        for (name, v) in shadowed_variables {
            if let Some(v) = v {
                self.local_variable_map.insert(name, v);
            } else {
                self.local_variable_map.remove(name);
            }
        }
    }

    fn find_field_less_constructor(&self, p: &mut Pattern<'a>) {
        match p {
            Pattern::Wildcard | Pattern::Num(_) => (),
            Pattern::Constructor {
                name,
                fields,
                span: _,
            } => {
                if *name == "_" {
                    *p = Pattern::Wildcard
                } else if self.data_decl_map.contains_key(name) {
                    for (f, _) in fields {
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
                self.find_field_less_constructor(&mut a.0);
                self.find_field_less_constructor(&mut b.0);
            }
            Pattern::Bind(_) => panic!(),
        }
    }

    fn binds_in_pattern(
        &mut self,
        (p, span): &PatternWithSpan<'a>,
        shadowed_variables: &mut FxHashMap<&'a str, Option<LocalVariable>>,
    ) {
        match p {
            Pattern::Bind(name) => {
                let l = if shadowed_variables.contains_key(name) {
                    self.local_variable_map[name]
                } else {
                    shadowed_variables.insert(name, self.local_variable_map.get(name).copied());
                    let l = self.build_env.new_local_variable();
                    self.local_variable_map.insert(name, l);
                    l
                };
                self.local_variable_span_map.insert(*span, l);
            }
            Pattern::Wildcard | Pattern::Num(_) => (),
            Pattern::Constructor {
                name: _,
                fields,
                span: _,
            } => {
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

    fn pattern(
        &mut self,
        (p, _span): &PatternWithSpan<'a>,
        operand: LocalVariable,
        block: &mut Block,
    ) {
        match p {
            Pattern::Bind(name) => {
                let v = self.local_variable_map[name];
                self.build_env.local_variable(v, operand, block);
            }
            Pattern::Wildcard => (),
            Pattern::Constructor {
                name,
                fields,
                span: _,
            } => {
                let d = self.data_decl_map[name];
                block.test_constructor(operand, doki_ir::TypeId::UserDefined(d));
                for (i, f) in fields.iter().enumerate() {
                    let ret = self.build_env.new_local_variable();
                    self.build_env
                        .field_access(ret, operand, d, i as u32, block);
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
                block.test_number(operand, a.parse().unwrap());
            }
        }
    }
}

fn utf8_to_utf16_ln_col(src: &str) -> Vec<(u32, u32)> {
    let mut utf8_to_utf16_map = Vec::with_capacity(src.len());
    utf8_to_utf16_map.push((1, 1));
    let mut line = 1;
    let mut col_utf16 = 1;
    for c in src.chars() {
        if c == '\n' {
            line += 1;
            col_utf16 = 1;
        } else {
            col_utf16 += c.len_utf16() as u32;
        }
        for _ in 0..c.len_utf8() {
            utf8_to_utf16_map.push((line, col_utf16));
        }
    }
    utf8_to_utf16_map
}
