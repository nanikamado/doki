mod c_type;

use self::c_type::{CAggregateType, CType};
use crate::ast_step1::{ConstructorId, ConstructorNames, TypeId};
use crate::ast_step2::{
    self, Ast, Block, Expr, Function, GlobalVariableId, Instruction, LocalVariable,
    LocalVariableCollector, Tester, Type, TypeUnitOf, VariableId,
};
use crate::collector::Collector;
use crate::intrinsics::{IntrinsicTypeTag, IntrinsicVariable};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::RefCell;
use std::fmt::Display;
use stripmargin::StripMargin;
use unic_ucd_category::GeneralCategory;

pub struct Codegen(pub Ast);

impl Display for Codegen {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ast = &self.0;
        let mut c_type_env = c_type::Env {
            aggregate_types: Default::default(),
            memo: Default::default(),
            reffed_aggregates: Default::default(),
        };
        let local_variable_types: LocalVariableCollector<(&Type, CType)> =
            ast.variable_types.map(|t| {
                let ct = c_type_env.c_type(t, None);
                (t, ct)
            });
        let global_variable_types = ast
            .variable_decls
            .iter()
            .map(|d| (d.decl_id, c_type_env.c_type(&d.t, None)))
            .collect();
        let next_label = RefCell::new(1);
        let env = Env {
            context: &Default::default(),
            variable_names: &ast.variable_names,
            local_variable_types: &local_variable_types,
            global_variable_types: &global_variable_types,
            constructor_names: &ast.constructor_names,
            catch_label: 0,
            next_label: &next_label,
        };
        let mut mutted_types = Collector::default();
        let intrinsic_variables = ast
            .used_intrinsic_variables
            .as_raw()
            .iter()
            .map(|((v, arg_ts), id)| {
                let arg_ts_c = arg_ts
                    .iter()
                    .map(|t| c_type_env.c_type(t, None))
                    .collect_vec();
                use IntrinsicVariable::*;
                let ret_t = match *v {
                    Mut => {
                        let t = &arg_ts_c[0];
                        mutted_types.get_or_insert(t.clone());
                        CType::Ref(Box::new(t.clone()))
                    }
                    GetMut => {
                        let t = &arg_ts_c[0];
                        let t = if let CType::Ref(t) = t { t } else { panic!() };
                        (**t).clone()
                    }
                    _ => {
                        let env: &mut c_type::Env = &mut c_type_env;
                        let t = TypeUnitOf::Normal {
                            id: TypeId::Intrinsic(v.runtime_return_type().unwrap()),
                            args: Vec::new(),
                        }
                        .into();
                        env.c_type(&t, None)
                    }
                };
                (*v, id, ret_t, arg_ts_c)
            })
            .unique()
            .collect_vec();
        let mutted_types = mutted_types.as_raw();
        let unit_t: Type = TypeUnitOf::Normal {
            id: TypeId::Intrinsic(IntrinsicTypeTag::Unit),
            args: Vec::new(),
        }
        .into();
        let unit_t = c_type_env.c_type(&unit_t, None);
        let c_type_env = c_type_env;
        let aggregates: FxHashMap<_, _> = c_type_env.aggregate_types.rev_map_as_raw().clone();
        let sorted = sort_aggregates(&aggregates);
        write!(
            f,
            "
            #include <stdio.h>
            #include <stdlib.h>
            #include <string.h>
            #include <stdint.h>
            #include <inttypes.h>
            #include <unistd.h>
            struct diverge{{}};
            {}{}{}",
            sorted.iter().format_with("", |(i, t), f| {
                match t {
                    CAggregateType::Struct(fields) => f(&format_args!(
                        "{} {{{}}};\n",
                        CType::Aggregate(*i),
                        fields
                            .iter()
                            .enumerate()
                            .format_with("", |(i, field), f| f(&format_args!("{field} _{i};",)))
                    )),
                    CAggregateType::Union(ts) => f(&format_args!(
                        "union u{i}{{{}}};{}{{int tag;union u{i} value;}};",
                        ts.iter()
                            .enumerate()
                            .format_with("", |(i, t), f| { f(&format_args!("{t} _{i};")) }),
                        CType::Aggregate(*i),
                    )),
                }
            }),
            c_type_env.reffed_aggregates.iter().format_with("", |i, f| {
                let t = CType::Aggregate(*i);
                f(&format_args!(
                    "static {t}* ref_t{i}({t} a) {{
                        {t}* tmp = malloc(sizeof({t}));
                        *tmp = a;
                        return tmp;
                    }}"
                ))
            }),
            mutted_types
                .iter()
                .format_with("", |(t, n), f| f(&format_args!(
                    "static {t}* mut_{n}({t} a) {{
                    {t}* tmp = malloc(sizeof({t}));
                    *tmp = a;
                    return tmp;
                    }}"
                )))
        )?;
        write_fns(f, &ast.functions, &c_type_env, &env, false);
        write!(
            f,
            "{}",
            ast.variable_decls
                .iter()
                .format_with("", |d, f| f(&format_args!(
                    "static {} g_{}_{};",
                    env.global_variable_types[&d.decl_id],
                    d.decl_id,
                    convert_name(&env.variable_names[&VariableId::Global(d.decl_id)]),
                )))
        )?;
        write!(
            f,
            "static {0} intrinsic_unit(){{
                return ({0}){{}};
            }}
            {1}{2}{3}",
            unit_t,
            r#"
            |static int panic(char* msg){
            |    fprintf(stderr, "error: %s\n", msg);
            |    exit(1);
            |}
            |"#
            .strip_margin(),
            intrinsic_variables
                .into_iter()
                .map(|(v, id, ret_t, arg_ts)| format!(
                    "static {} intrinsic_{v}_{id}({}){{{}}}",
                    ret_t,
                    arg_ts
                        .iter()
                        .enumerate()
                        .format_with(",", |(i, t), f| f(&format_args!("{t} _{i}"))),
                    PrimitiveDefPrint {
                        i: v,
                        arg_ts: &arg_ts,
                        mutted_types
                    }
                ))
                .format(""),
            ast.variable_decls
                .iter()
                .format_with("", |d, f| f(&format_args!(
                    "static {} init_g_{}_{}(){}",
                    env.global_variable_types[&d.decl_id],
                    d.decl_id,
                    convert_name(&env.variable_names[&VariableId::Global(d.decl_id)]),
                    Dis(&TerminalBlock(&d.value, d.ret), env)
                ))),
        )?;
        write_fns(f, &ast.functions, &c_type_env, &env, true);
        write!(
            f,
            "int main(void) {{
                {}
                {}((struct t0){{}},(struct t0){{}});
            }}",
            ast.variable_decls
                .iter()
                .format_with("", |d, f| f(&format_args!(
                    "g_{0}_{1}=init_g_{0}_{1}();",
                    d.decl_id,
                    convert_name(&env.variable_names[&VariableId::Global(d.decl_id)]),
                ))),
            ast.entry_point
        )
    }
}

struct PrimitiveDefPrint<'a> {
    i: IntrinsicVariable,
    arg_ts: &'a [CType],
    mutted_types: &'a FxHashMap<CType, usize>,
}

impl Display for PrimitiveDefPrint<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use IntrinsicVariable::*;
        let v = self.i;
        match v {
            Minus => write!(f, "return _0 - _1;"),
            Plus => write!(f, "return _0 + _1;"),
            Percent => write!(f, "return _0 % _1;"),
            Multi => write!(f, "return _0 * _1;"),
            Div => write!(f, "return _0 / _1;"),
            Lt => write!(f, "return _0 < _1;"),
            Eq => write!(f, "return _0 == _1;"),
            EqU8 => write!(f, "return _0 == _1;"),
            Write => write!(
                f,
                r#"write(STDOUT_FILENO, _0, _1);return intrinsic_unit();"#
            ),
            Mut => {
                let n = self.mutted_types[&self.arg_ts[0]];
                write!(f, "return mut_{n}(_0);")
            }
            SetMut => write!(f, "*_0 = _1;return intrinsic_unit();"),
            GetMut => write!(f, "return *_0;"),
            GetChar => write!(f, "return getchar();"),
            Malloc => write!(f, "return malloc(_0);"),
            LoadU8 => write!(f, "return *(uint8_t*)_0;"),
            StoreU8 => write!(f, "*(uint8_t*)_0 = _1;return intrinsic_unit();"),
            AddPtr => write!(f, "return (uint8_t*)_0+_1;"),
            U8ToI64 => write!(f, "return _0;"),
            I64ToU8 => write!(f, r#"if(_0<0||0xFF<=_0)panic("overflow");return _0;"#),
        }
    }
}

fn sort_aggregates(aggregates: &FxHashMap<usize, CAggregateType>) -> Vec<(usize, &CAggregateType)> {
    let mut done = FxHashSet::default();
    let mut sorted = Vec::with_capacity(aggregates.len());
    for i in aggregates.keys() {
        sort_aggregates_rec(*i, aggregates, &mut done, &mut sorted);
    }
    sorted
}
fn sort_aggregates_rec<'a>(
    i: usize,
    h: &'a FxHashMap<usize, CAggregateType>,
    done: &mut FxHashSet<usize>,
    sorted: &mut Vec<(usize, &'a CAggregateType)>,
) -> bool {
    if !done.contains(&i) {
        done.insert(i);
        if let Some(a) = &h.get(&i) {
            let (CAggregateType::Union(cs) | CAggregateType::Struct(cs)) = a;
            for c in cs {
                if let CType::Aggregate(i) = c {
                    let created = sort_aggregates_rec(*i, h, done, sorted);
                    if !created {
                        return false;
                    }
                }
            }
            sorted.push((i, a));
            true
        } else {
            // `i` cannot be created at runtime because of diverging.
            false
        }
    } else {
        true
    }
}

fn write_fns(
    s: &mut std::fmt::Formatter<'_>,
    functions: &[Function],
    c_type_env: &c_type::Env,
    env: &Env,
    write_body: bool,
) {
    write!(
        s,
        "{}",
        functions.iter().format_with("", |function, f| {
            let next_label = RefCell::new(1);
            let env = Env {
                context: &function
                    .context
                    .iter()
                    .enumerate()
                    .map(|(i, d)| (*d, i))
                    .collect(),
                variable_names: env.variable_names,
                local_variable_types: env.local_variable_types,
                global_variable_types: env.global_variable_types,
                constructor_names: env.constructor_names,
                catch_label: 0,
                next_label: &next_label,
            };
            let (t, ct) = env.local_variable_types.get_type(function.parameter);
            f(&format_args!(
                "static {} {}({} {}/*{}*/,{} ctx)",
                env.get_type(function.ret),
                function.id,
                ct,
                Dis(&VariableId::Local(function.parameter), env),
                ast_step2::DisplayTypeWithEnvStruct(*t, env.constructor_names),
                CType::Aggregate(
                    c_type_env.aggregate_types.get(CAggregateType::Struct(
                        function
                            .context
                            .iter()
                            .map(|l| env.local_variable_types.get_type(*l).1.clone())
                            .collect()
                    ))
                )
            ))?;
            if write_body {
                f(&format_args!(
                    "{};",
                    Dis(&TerminalBlock(&function.body, function.ret), env)
                ))
            } else {
                f(&";")
            }
        })
    )
    .unwrap()
}

#[derive(Debug, Clone, Copy)]
struct Env<'a> {
    context: &'a FxHashMap<LocalVariable, usize>,
    variable_names: &'a FxHashMap<VariableId, String>,
    local_variable_types: &'a LocalVariableCollector<(&'a Type, CType)>,
    global_variable_types: &'a FxHashMap<GlobalVariableId, CType>,
    constructor_names: &'a ConstructorNames,
    catch_label: u32,
    next_label: &'a RefCell<u32>,
}

impl Env<'_> {
    fn get_type(&self, v: VariableId) -> &CType {
        match v {
            VariableId::Local(v) => &self.local_variable_types.get_type(v).1,
            VariableId::Global(v) => &self.global_variable_types[&v],
        }
    }
}

fn collect_local_variables_block(b: &Block, vs: &mut FxHashSet<LocalVariable>) {
    for i in &b.instructions {
        match i {
            Instruction::Assign(d, _) => {
                vs.insert(*d);
            }
            Instruction::TryCatch(a, b) => {
                collect_local_variables_block(a, vs);
                collect_local_variables_block(b, vs);
            }
            _ => (),
        }
    }
}

struct Dis<'a, T>(&'a T, Env<'a>);

impl<'a, T: DisplayWithEnv> Display for Dis<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt_with_env(self.1, f)
    }
}

trait DisplayWithEnv {
    fn fmt_with_env(&self, env: Env<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
}

struct TerminalBlock<'a>(&'a Block, VariableId);

impl DisplayWithEnv for TerminalBlock<'_> {
    fn fmt_with_env(&self, env: Env<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut vs = FxHashSet::default();
        if let VariableId::Local(l) = self.1 {
            vs.insert(l);
        }
        collect_local_variables_block(self.0, &mut vs);
        if vs.is_empty() {
            write!(
                f,
                "{{{}return {};label_0:panic(\"pattern is not exhaustive\");}}",
                Dis(self.0, env),
                Dis(&self.1, env)
            )
        } else {
            write!(
                f,
                "{{{}{}return {};label_0:panic(\"pattern is not exhaustive\");}}",
                vs.iter().format_with("", |v, f| {
                    let (t, ct) = env.local_variable_types.get_type(*v);
                    f(&format_args!(
                        "{} /*{}*/ {};",
                        ct,
                        ast_step2::DisplayTypeWithEnvStruct(*t, env.constructor_names),
                        Dis(&VariableId::Local(*v), env),
                    ))
                }),
                Dis(self.0, env),
                Dis(&self.1, env)
            )
        }
    }
}

impl DisplayWithEnv for Block {
    fn fmt_with_env(&self, env: Env<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for i in &self.instructions {
            i.fmt_with_env(env, f)?;
        }
        Ok(())
    }
}

impl DisplayWithEnv for Instruction {
    fn fmt_with_env(&self, env: Env<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Instruction::Assign(d, e) => {
                let t = &env.local_variable_types.get_type(*d).1;
                write!(
                    f,
                    "{}={};",
                    Dis(&VariableId::Local(*d), env),
                    Dis(&(*d, e, t), env)
                )
            }
            Instruction::Test(Tester::Tag { tag }, e) => {
                write!(
                    f,
                    "if({}.tag!={})goto label_{};",
                    Dis(e, env),
                    tag,
                    env.catch_label
                )
            }
            Instruction::Test(Tester::I64 { value }, e) => {
                write!(
                    f,
                    "if({}!={value})goto label_{};",
                    Dis(e, env),
                    env.catch_label
                )
            }
            Instruction::FailTest => {
                write!(f, "goto label_{};", env.catch_label)
            }
            Instruction::Panic { msg } => {
                write!(f, "panic({msg:?});")
            }
            Instruction::TryCatch(a, b) => {
                let catch_label = env.next_label.replace_with(|l| *l + 1);
                write!(
                    f,
                    "{}goto label_skip_{catch_label};label_{catch_label}:{}label_skip_{catch_label}:",
                    Dis(a, Env { catch_label, ..env }),
                    Dis(b, env)
                )
            }
        }
    }
}

impl DisplayWithEnv for (LocalVariable, &Expr, &CType) {
    fn fmt_with_env(&self, env: Env<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (v_for_panic_cast, e, t) = self;
        match e {
            Expr::Lambda {
                lambda_id: _,
                context,
            } => write!(
                f,
                r#"({}){{{}}}"#,
                t,
                context.iter().format_with(",", |c, f| f(&format_args!(
                    "{}",
                    Dis(&VariableId::Local(*c), env)
                )))
            ),
            Expr::I64(a) => write!(f, "{a}"),
            Expr::U8(a) => write!(f, "{a}"),
            Expr::Str(a) => write!(f, "{a:?}"),
            Expr::Ident(i) => i.fmt_with_env(env, f),
            Expr::Call {
                f: g,
                a,
                real_function,
            } => write!(f, "{real_function}({},{})", Dis(a, env), Dis(g, env)),
            Expr::BasicCall { args, id } => {
                use crate::ast_step2::BasicFunction::*;
                match id {
                    Intrinsic { v, id } => write!(
                        f,
                        "intrinsic_{v}_{id}({})",
                        args.iter().format_with(",", |a, f| f(&Dis(a, env)))
                    ),
                    Construction(id) => {
                        if let CType::Diverge = t {
                            write!(f, "({}){{}}", CType::Diverge)
                        } else {
                            write!(
                                f,
                                "/*{}*/({}){{{}}}",
                                Dis(id, env),
                                t,
                                args.iter().format_with(",", |a, f| f(&Dis(a, env)))
                            )
                        }
                    }
                    IntrinsicConstruction(id) => {
                        write!(
                            f,
                            "/*{id}*/({t}){{{}}}",
                            args.iter().format_with(",", |a, f| f(&Dis(a, env)))
                        )
                    }
                    FieldAccessor {
                        constructor: _,
                        field,
                    } => {
                        debug_assert_eq!(args.len(), 1);
                        let ct = env.get_type(args[0]);
                        if let CType::Diverge = ct {
                            write!(
                                f,
                                "(panic(\"unexpected\"),{})",
                                Dis(&VariableId::Local(*v_for_panic_cast), env)
                            )
                        } else {
                            write!(f, "{}._{field}", Dis(&args[0], env))
                        }
                    }
                }
            }
            Expr::Upcast { tag, value } => {
                let i = if let CType::Aggregate(i) = t {
                    i
                } else {
                    panic!()
                };
                write!(f, "({t}){{{tag},(union u{i}){}}}", Dis(value, env))
            }
            Expr::Downcast {
                tag,
                value,
                check: true,
            } => {
                write!(
                    f,
                    "({0}.tag=={tag}||panic(\"failed to downcast\"),{0}.value._{tag})",
                    Dis(value, env)
                )
            }
            Expr::Downcast {
                tag,
                value,
                check: false,
            } => {
                write!(f, "{0}.value._{tag}", Dis(value, env))
            }
            Expr::Ref(v) => {
                let t = if let CType::Ref(t) = t { t } else { panic!() };
                let i = if let CType::Aggregate(t) = **t {
                    t
                } else {
                    panic!()
                };
                write!(f, "ref_t{i}({})", Dis(v, env))
            }
            Expr::Deref(v) => write!(f, "*{}", Dis(v, env)),
        }
    }
}

impl DisplayWithEnv for VariableId {
    fn fmt_with_env(&self, env: Env<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VariableId::Global(d) => {
                write!(f, "g_{d}_{}", convert_name(&env.variable_names[self]))
            }
            VariableId::Local(d) => {
                if let Some(d) = env.context.get(d) {
                    write!(f, "ctx._{d}")
                } else {
                    write!(f, "l_{d}")
                }
            }
        }
    }
}

impl DisplayWithEnv for ConstructorId {
    fn fmt_with_env(&self, _env: Env<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

fn convert_name(name: &str) -> String {
    if is_valid_name(name) {
        name.to_string()
    } else {
        "unicode".to_string() + &name.chars().map(|c| format! {"_{:x}",c as u32}).join("")
    }
}

fn is_valid_name(name: &str) -> bool {
    name.chars().all(|c| {
        GeneralCategory::of(c).is_letter()
            || matches!(
                GeneralCategory::of(c),
                GeneralCategory::DecimalNumber
                    | GeneralCategory::NonspacingMark
                    | GeneralCategory::SpacingMark
                    | GeneralCategory::ConnectorPunctuation
                    | GeneralCategory::LetterNumber
            )
            || c == '_'
    }) && !(name.len() >= 8 && name[0..8] == *"unicode_")
}
