use crate::ast_step1::{self, ConstructorId, ConstructorNames};
use crate::ast_step2::c_type::CTypeScheme;
use crate::ast_step2::{
    self, Ast, CType, ConvertOpRef, EndInstruction, Expr, Function, FunctionBody, GlobalVariableId,
    Instruction, LocalVariable, LocalVariableCollector, StructId, Tester, Type, VariableId,
};
use crate::intrinsics::IntrinsicVariable;
use crate::util::collector::Collector;
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use std::fmt::Display;
use unic_ucd_category::GeneralCategory;

const BACKTRACE_STACK_LIMIT: i32 = 500;

pub struct Codegen<'a>(pub Ast<'a>);

impl Display for Codegen<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ast = &self.0;
        let global_variable_types: FxHashMap<_, CType> = ast
            .variable_decls
            .iter()
            .map(|d| (d.decl_id, d.c_t))
            .collect();
        let unit_t = CType {
            i: StructId(0),
            boxed: false,
        };
        let mut refed_types = Collector::default();
        let sorted = sort_aggregates(&ast.c_type_definitions, &mut refed_types);
        let refed_types = refed_types.as_raw();
        let env = Env {
            variable_names: &ast.variable_names,
            local_variable_types: &ast.variable_types,
            global_variable_types: &global_variable_types,
            constructor_names: &ast.constructor_names,
            c_type_definitions: &ast.c_type_definitions,
            refed_types,
            global_variable_initialization: false,
            backtrace: ast.backtrace,
            boehm: ast.boehm,
        };
        let structs = sorted.iter().format_with("", |(i, t), f| {
            let i = CType {
                i: *i,
                boxed: false,
            };
            match t {
                CTypeScheme::Aggregate(ts) => f(&format_args!(
                    "{}{{{}}};",
                    Dis(&i, env),
                    ts.iter()
                        .enumerate()
                        .format_with("", |(i, t), f| f(&format_args!("{} _{i};", Dis(t, env))))
                )),
                CTypeScheme::Union(ts) => f(&format_args!(
                    "union u{0}{{{1}}};{2}{{int tag;union u{0} value;}};",
                    i.i.0,
                    ts.iter().enumerate().format_with("", |(i, t), f| {
                        f(&format_args!("{} _{i};", Dis(t, env)))
                    }),
                    Dis(&i, env),
                )),
                _ => {
                    panic!()
                }
            }
        });
        write!(
            f,
            "#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <errno.h>
#include <math.h>
struct diverge{{}};"
        )?;
        if env.boehm {
            write!(
                f,
                "\n\
            #include <gc.h>\n\
            #define malloc GC_malloc\n\
            "
            )?;
        }
        if env.backtrace {
            write!(
                f,
                "static char* TRACE_STACK[{BACKTRACE_STACK_LIMIT}];\
                static int trace_stack_top;",
            )?;
        }
        write!(
            f,
            "{}{}",
            structs,
            refed_types.iter().format_with("", |(t, n), f| {
                f(&format_args!(
                    "static {0}* ref_{n}({0} a) {{
                            {0}* tmp = malloc(sizeof({0}));
                            *tmp = a;
                            return tmp;
                        }}",
                    Dis(
                        &CType {
                            i: *t,
                            boxed: false
                        },
                        env
                    ),
                ))
            })
        )?;
        write_fns(f, &ast.functions, env, false)?;
        for d in &ast.variable_decls {
            write!(f, "static {0} {1};", Dis(&d.c_t, env), Dis(&d.decl_id, env),)?;
            if d.is_original {
                write!(
                    f,
                    "static {0} init_{1}(void);",
                    Dis(&d.c_t, env),
                    Dis(&d.decl_id, env),
                )?;
            }
        }
        write!(
            f,
            "static {0} intrinsic_unit(void){{
                return ({0}){{}};
            }}",
            Dis(&unit_t, env),
        )?;
        write!(
            f,
            r#"
int read_file(uint8_t* buff, int offset, int buff_len, void* fp, void* status) {{
    size_t n = fread(buff+offset, 1, buff_len, fp);
    if(ferror(fp))
        *(int64_t*)status = errno;
    return n;
}}"#
        )?;
        if env.backtrace {
            write!(
                f,
                "__attribute__ ((__noreturn__)) static int panic(char* msg){{\
                fprintf(stderr, \"error: %s\\nstack backtrace:\\n\", msg);\
                while(--trace_stack_top>=0)\
                fprintf(stderr, \"%5d: %s\\n\", trace_stack_top, TRACE_STACK[trace_stack_top]);\
                exit(1);}}\
                static void trace_stack_push(char* span) {{\
                    if(trace_stack_top=={BACKTRACE_STACK_LIMIT})panic(\"stack overflow\");\
                    TRACE_STACK[trace_stack_top++]=span;\
                }}\
                "
            )
        } else {
            write!(
                f,
                "__attribute__ ((__noreturn__)) static int panic(char* msg){{\
                fprintf(stderr, \"error: %s\\n\", msg);\
                exit(1);}}\
                "
            )
        }?;
        for ((v, arg_ts, ret_t), id) in ast.used_intrinsic_variables.as_raw() {
            write!(f, "static {} intrinsic_{v}_{id}", Dis(ret_t, env))?;
            if arg_ts.is_empty() {
                write!(f, "(void)")
            } else {
                write!(
                    f,
                    "({})",
                    arg_ts
                        .iter()
                        .enumerate()
                        .format_with(",", |(i, t), f| f(&format_args!("{} _{i}", Dis(t, env))))
                )
            }?;
            write!(f, "{{{}}}", Dis(&PrimitiveDefPrint { i: *v, arg_ts }, env))?;
        }
        for d in &ast.variable_decls {
            if d.is_original {
                write!(f,
                    "static {0} init_{1}_inner(void){2}\
                    static char init_status_{1}=0;\
                    static {0} init_{1}(void){{\
                        if(init_status_{1}==2)return {1};\
                        else if(init_status_{1}==1)panic(\"cycle detected when initializing global variables\");\
                        init_status_{1}=1;\
                        {1}=init_{1}_inner();\
                        init_status_{1}=2;\
                        return {1};\
                    }}",
                    Dis(&d.c_t, env),
                    Dis(&d.decl_id, env),
                    Dis(
                        &FunctionBodyWithCtx {
                            f: &d.value,
                            parameters: &[],
                        },
                        Env { global_variable_initialization: true, ..env }
                    )
                )?;
            }
        }
        write_fns(f, &ast.functions, env, true)?;
        write!(
            f,
            "static {} inner_main(void){}",
            Dis(&ast.entry_block_ret_t, env),
            Dis(
                &FunctionBodyWithCtx {
                    f: &ast.entry_block,
                    parameters: &[],
                },
                env
            )
        )?;
        fn struct_converter(
            f: &mut std::fmt::Formatter<'_>,
            param: impl Display,
            ops: &[(u32, ConvertOpRef)],
            env: Env,
        ) -> std::fmt::Result {
            if ops.iter().all(|(c, r)| *c == 0 && !r.is_add_ref()) {
                write!(f, "{param}")
            } else {
                write!(
                    f,
                    "{{{}}}",
                    ops.iter().enumerate().format_with(",", |(i, (c, r)), f| {
                        if *c == 0 {
                            match r {
                                ConvertOpRef::None => f(&format_args!("{param}._{i}")),
                                ConvertOpRef::Ref(t) => f(&format_args!(
                                    "ref_{}(*{param}._{i})",
                                    env.refed_types[&t.i]
                                )),
                                ConvertOpRef::AddRef(t) => match env.refed_types.get(&t.i) {
                                    Some(t) => f(&format_args!("ref_{}({param}._{i})", t)),
                                    _ => f(&format_args!("/*u={t:?}*/ref_none",)),
                                },
                            }
                        } else {
                            match r {
                                ConvertOpRef::None => {
                                    f(&format_args!("converter_{}({param}._{i})", c))
                                }
                                ConvertOpRef::Ref(t) => f(&format_args!(
                                    "ref_{}(converter_{}(*{param}._{i}))",
                                    env.refed_types[&t.i], c
                                )),
                                ConvertOpRef::AddRef(t) => match env.refed_types.get(&t.i) {
                                    Some(t) => {
                                        f(&format_args!("ref_{}(converter_{}({param}._{i}))", t, c))
                                    }
                                    _ => f(&format_args!("/*t={t:?}*/ref_none",)),
                                },
                            }
                        }
                    })
                )
            }
        }
        for c in ast.type_converter.values() {
            write!(
                f,
                "{} converter_{}({});",
                Dis(&c.c_type_to, env),
                c.id,
                Dis(&c.c_type_from, env),
            )?;
        }
        for c in ast.type_converter.values() {
            write!(
                f,
                "{} converter_{}({} _0){{",
                Dis(&c.c_type_to, env),
                c.id,
                Dis(&c.c_type_from, env),
            )?;
            match &c.op {
                ast_step2::ConvertOp::Unknown => panic!(),
                ast_step2::ConvertOp::Id => write!(f, "return _0;"),
                ast_step2::ConvertOp::Unexpected => write!(f, r#"panic("unexpected");"#),
                ast_step2::ConvertOp::Struct(ops) => {
                    write!(f, "return ({})", Dis(&c.c_type_to, env),)?;
                    struct_converter(f, "_0", ops, env)?;
                    write!(f, ";")
                }
                ast_step2::ConvertOp::ReTag(ts) => {
                    write!(f, "switch(_0.tag){{")?;
                    for (i, t) in ts.iter().enumerate() {
                        write!(f, "case {i}:")?;
                        write!(
                            f,
                            "return ({0}){{{1},{{._{1}=",
                            Dis(&c.c_type_to, env),
                            t.new_tag
                        )?;
                        struct_converter(f, format_args!("_0.value._{i}"), &t.convert_op, env)?;
                        write!(f, "}}}};")?;
                        write!(f, "break;")?;
                    }
                    write!(f, r#"default:panic("unexpected");"#)?;
                    write!(f, "}}")
                }
                ast_step2::ConvertOp::AddTag(tag, ops) => {
                    write!(f, "return ({}){{{tag},{{._{tag}=", Dis(&c.c_type_to, env))?;
                    struct_converter(f, "_0", ops, env)?;
                    write!(f, "}}}};")
                }
            }?;
            write!(f, "}}")?;
        }
        writeln!(
            f,
            "int main(void) {{
                {}{}
                inner_main();
            }}",
            ast.original_variables_map
                .iter()
                .format_with("", |(_, (decl_id, _)), f| f(&format_args!(
                    "init_{0}();",
                    Dis(decl_id, env),
                ))),
            ast.variable_decls.iter().rev().format_with("", |d, f| {
                let (org_decl_id, original_p) = ast.original_variables_map[&d.original_decl_id];
                if let Some(c) = &ast.type_converter.get(&(original_p, d.p)) {
                    f(&format_args!(
                        "{}=converter_{}({});",
                        Dis(&d.decl_id, env),
                        c.id,
                        Dis(&org_decl_id, env)
                    ))
                } else {
                    f(&format_args!(
                        "{}={};",
                        Dis(&d.decl_id, env),
                        Dis(&org_decl_id, env)
                    ))
                }
            }),
        )
    }
}

struct PrimitiveDefPrint<'a> {
    i: IntrinsicVariable,
    arg_ts: &'a [CType],
}

impl DisplayWithEnv for PrimitiveDefPrint<'_> {
    fn fmt_with_env(&self, env: Env<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use IntrinsicVariable::*;
        let v = self.i;
        match v {
            Minus | MinusF64 => write!(f, "return _0 - _1;"),
            Plus | PlusF64 => write!(f, "return _0 + _1;"),
            Percent => write!(f, "return _0 % _1;"),
            Multi | MultiF64 => write!(f, "return _0 * _1;"),
            Div | DivF64 => write!(f, "return _0 / _1;"),
            Lt | LtF64 => write!(f, "return _0 < _1;"),
            LeF64 => write!(f, "return _0 <= _1;"),
            Eq | EqF64 | EqU8 => write!(f, "return _0 == _1;"),
            BitOr | BitOrU8 => write!(f, "return _0 | _1;"),
            BitAnd | BitAndU8 => write!(f, "return _0 & _1;"),
            RightShift | RightShiftU8 => write!(f, "return _0 >> _1;"),
            Write => write!(
                f,
                r#"fwrite((uint8_t*)_0+_1,1,_2,stdout);return intrinsic_unit();"#
            ),
            Mut => {
                let t = self.arg_ts[0];
                write!(
                    f,
                    "\
                    {0}* tmp = malloc(sizeof({0}));\
                    *tmp = _0;\
                    return tmp;",
                    Dis(&t, env),
                )
            }
            SetMut => write!(f, "*_0 = _1;return intrinsic_unit();"),
            GetMut => write!(f, "return *_0;"),
            GetChar => write!(f, "return getchar();"),
            Malloc => write!(f, "return malloc(_0);"),
            LoadU8 => write!(f, "return ((uint8_t*)_0)[_1];"),
            StoreU8 => write!(f, "((uint8_t*)_0)[_1] = _2;return intrinsic_unit();"),
            U8ToI64 => write!(f, "return _0;"),
            I64ToU8 => write!(f, r#"if(_0<0||0xFF<=_0)panic("overflow");return _0;"#),
            ReadFile => write!(f, "return read_file(_0,_1,_2,_3,_4);"),
            Stdout => write!(f, "return stdout;"),
            Stdin => write!(f, "return stdin;"),
            WriteF64 => write!(f, "snprintf(_0,_1,\"%f\",_2);return intrinsic_unit();"),
            F64StrLen => write!(f, "return snprintf(NULL,0,\"%f\",_0);"),
            SqrtF64 => write!(f, "return sqrt(_0);"),
        }
    }
}

fn sort_aggregates<'a>(
    c_type_definitions: &'a [CTypeScheme<CType>],
    refed_types: &mut Collector<StructId>,
) -> Vec<(StructId, &'a CTypeScheme<CType>)> {
    let mut done = FxHashSet::default();
    let mut sorted = Vec::with_capacity(c_type_definitions.len());
    for (i, _) in c_type_definitions.iter().enumerate() {
        sort_aggregates_rec(
            CType {
                i: StructId(i),
                boxed: false,
            },
            c_type_definitions,
            &mut done,
            &mut sorted,
            refed_types,
        );
    }
    sorted
}

fn sort_aggregates_rec<'a>(
    i: CType,
    h: &'a [CTypeScheme<CType>],
    done: &mut FxHashSet<StructId>,
    sorted: &mut Vec<(StructId, &'a CTypeScheme<CType>)>,
    refed_types: &mut Collector<StructId>,
) {
    if i.boxed {
        refed_types.get_or_insert(i.i);
        #[cfg(debug_assertions)]
        {
            let a = &h[i.i.0];
            assert!(matches!(a, Union(_)))
        }
        return;
    }
    if done.contains(&i.i) {
        return;
    }
    done.insert(i.i);
    let a = &h[i.i.0];
    use ast_step2::c_type::CTypeScheme::*;
    match a {
        Aggregate(is) | Union(is) => {
            for i in is {
                sort_aggregates_rec(*i, h, done, sorted, refed_types);
            }
            sorted.push((i.i, a));
        }
        _ => (),
    }
}

fn write_fns(
    f: &mut std::fmt::Formatter<'_>,
    functions: &[Function],
    env: Env,
    write_body: bool,
) -> std::fmt::Result {
    for function in functions {
        fn write_fn(
            f: &mut std::fmt::Formatter<'_>,
            function: &Function,
            env: Env,
            write_body: bool,
            global_variable_initialization: bool,
        ) -> std::fmt::Result {
            write!(
                f,
                "static {} {}{}",
                Dis(&env.local_variable_types.get_type(function.ret).1, env),
                if global_variable_initialization {
                    "init_"
                } else {
                    ""
                },
                function.id
            )?;
            if function.parameters.is_empty() {
                write!(f, "(void)")?;
            } else {
                let ps = function.parameters.iter().format_with(",", |l, f| {
                    let (t, ct) = env.local_variable_types.get_type(*l);
                    f(&format_args!(
                        "{} {}/*{}*/",
                        Dis(ct, env),
                        Dis(l, env),
                        ast_step2::DisplayTypeWithEnvStructOption(t, env.constructor_names),
                    ))
                });
                write!(f, "({ps})")?;
            }
            if write_body {
                write!(
                    f,
                    "{}",
                    Dis(
                        &FunctionBodyWithCtx {
                            f: &function.body,
                            parameters: &function.parameters,
                        },
                        Env {
                            global_variable_initialization,
                            ..env
                        }
                    )
                )
            } else {
                write!(f, ";")
            }
        }
        write_fn(f, function, env, write_body, false)?;
        write_fn(f, function, env, write_body, true)?;
    }
    Ok(())
}

#[derive(Debug, Clone, Copy)]
struct Env<'a> {
    variable_names: &'a FxHashMap<GlobalVariableId, String>,
    local_variable_types: &'a LocalVariableCollector<(Option<Type>, CType)>,
    global_variable_types: &'a FxHashMap<GlobalVariableId, CType>,
    constructor_names: &'a ConstructorNames,
    c_type_definitions: &'a [CTypeScheme<CType>],
    refed_types: &'a FxHashMap<StructId, usize>,
    global_variable_initialization: bool,
    backtrace: bool,
    boehm: bool,
}

fn collect_local_variables_in_block(b: &FunctionBody, vs: &mut FxHashSet<LocalVariable>) {
    for bb in &b.basic_blocks {
        for b in &bb.instructions {
            if let Instruction::Assign(d, e) = b {
                vs.insert(*d);
                collect_local_variables_in_expr(e, vs);
            }
        }
        if let EndInstruction::Ret(l) = bb.end_instruction {
            vs.insert(l);
        }
    }
}

fn collect_local_variables_in_expr(e: &Expr, vs: &mut FxHashSet<LocalVariable>) {
    match e {
        Expr::I64(_)
        | Expr::F64(_)
        | Expr::U8(_)
        | Expr::Str(_)
        | Expr::Ident(VariableId::Global(_)) => (),
        Expr::Call { args, .. } | Expr::BasicCall { args, .. } => {
            for a in args {
                collect_local_variables_in_variable(*a, vs);
            }
        }
        Expr::Ident(VariableId::Local(a))
        | Expr::Ref(a)
        | Expr::Deref(a)
        | Expr::Downcast { value: a, .. }
        | Expr::Upcast { value: a, .. } => collect_local_variables_in_variable(*a, vs),
    }
}

fn collect_local_variables_in_variable(v: LocalVariable, vs: &mut FxHashSet<LocalVariable>) {
    vs.insert(v);
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

struct FunctionBodyWithCtx<'a> {
    f: &'a FunctionBody,
    parameters: &'a [LocalVariable],
}

impl DisplayWithEnv for FunctionBodyWithCtx<'_> {
    fn fmt_with_env(&self, env: Env<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut vs = FxHashSet::default();
        collect_local_variables_in_block(self.f, &mut vs);
        for p in self.parameters {
            vs.remove(p);
        }
        write!(
            f,
            "{{{}",
            vs.iter().format_with("", |v, f| {
                let (t, ct) = env.local_variable_types.get_type(*v);
                f(&format_args!(
                    "{} /*{}*/ {};",
                    Dis(ct, env),
                    ast_step2::DisplayTypeWithEnvStructOption(t, env.constructor_names),
                    Dis(v, env),
                ))
            }),
        )?;
        for (i, bb) in self.f.basic_blocks.iter().enumerate() {
            write!(f, "label_{i}:")?;
            for b in &bb.instructions {
                b.fmt_with_env(env, f)?;
            }
            match &bb.end_instruction {
                EndInstruction::Ret(ret) => {
                    write!(f, "return {};", Dis(ret, env))?;
                }
                EndInstruction::Goto { label } => {
                    write!(f, "goto label_{label};")?;
                }
                EndInstruction::Panic { msg } => {
                    write!(f, r#"panic("{}");"#, StringEscape(msg))?;
                }
            }
        }
        write!(f, "}}")
    }
}

impl DisplayWithEnv for Instruction {
    fn fmt_with_env(&self, env: Env<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Instruction::Assign(d, e) => {
                if env.backtrace {
                    if let Expr::Call { span, .. } = e {
                        write!(f, r#"trace_stack_push("{}");"#, StringEscape(span))?;
                    }
                }
                let t = &env.local_variable_types.get_type(*d).1;
                write!(f, "{}={};", Dis(d, env), Dis(&(e, t), env))?;
                if env.backtrace && matches!(e, Expr::Call { .. }) {
                    write!(f, "trace_stack_top--;")?;
                }
                Ok(())
            }
            Instruction::Test {
                tester: Tester::Tag { tag },
                operand: e,
                catch_label,
            } => {
                write!(
                    f,
                    "if({}.tag!={})goto label_{};",
                    Dis(e, env),
                    tag,
                    catch_label
                )
            }
            Instruction::Test {
                tester: Tester::I64 { value },
                operand: e,
                catch_label,
            } => {
                write!(f, "if({}!={value})goto label_{};", Dis(e, env), catch_label)
            }
        }
    }
}

impl DisplayWithEnv for (&Expr, &CType) {
    fn fmt_with_env(&self, env: Env<'_>, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (e, t) = self;
        match e {
            Expr::I64(a) => write!(fmt, "{a}"),
            Expr::U8(a) => write!(fmt, "{a}"),
            Expr::F64(a) => write!(fmt, "{a}"),
            Expr::Str(a) => write!(fmt, "\"{}\"", StringEscape(a)),
            Expr::Ident(VariableId::Global(i)) => {
                debug_assert_eq!(**t, env.global_variable_types[i]);
                i.fmt_with_env(env, fmt)
            }
            Expr::Ident(VariableId::Local(i)) => i.fmt_with_env(env, fmt),
            Expr::Call {
                args,
                f,
                tail_call: _,
                span: _,
            } => write!(
                fmt,
                "{}{f}({})",
                if env.global_variable_initialization {
                    "init_"
                } else {
                    ""
                },
                args.iter().format_with(",", |a, f| f(&Dis(a, env)))
            ),
            Expr::BasicCall { args, id } => {
                use crate::ast_step2::BasicFunction::*;
                match id {
                    Intrinsic { v, id } => write!(
                        fmt,
                        "intrinsic_{v}_{id}({})",
                        args.iter().format_with(",", |a, f| f(&Dis(a, env)))
                    ),
                    Construction => {
                        write!(
                            fmt,
                            "({}){{{}}}",
                            Dis(*t, env),
                            args.iter().format_with(",", |a, f| f(&Dis(a, env)))
                        )
                    }
                    FieldAccessor { field, boxed } => {
                        debug_assert_eq!(args.len(), 1);
                        if *boxed {
                            write!(fmt, "*")?;
                        }
                        write!(fmt, "{}._{field}", Dis(&args[0], env))
                    }
                }
            }
            Expr::Upcast { tag, value } => {
                write!(
                    fmt,
                    "({}){{{tag},(union u{}){{._{tag}={}}}}}",
                    Dis(*t, env),
                    t.i.0,
                    Dis(value, env)
                )
            }
            Expr::Downcast {
                tag,
                value,
                check: true,
            } => {
                write!(
                    fmt,
                    "({0}.tag=={tag}||panic(\"failed to downcast\"),{0}.value._{tag})",
                    Dis(value, env)
                )
            }
            Expr::Downcast {
                tag,
                value,
                check: false,
            } => {
                write!(fmt, "{0}.value._{tag}", Dis(value, env))
            }
            Expr::Ref(v) => {
                debug_assert!(t.boxed);
                write!(fmt, "ref_{}({})", env.refed_types[&t.i], Dis(v, env))
            }
            Expr::Deref(v) => write!(fmt, "*{}", Dis(v, env)),
        }
    }
}

impl DisplayWithEnv for GlobalVariableId {
    fn fmt_with_env(&self, env: Env<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if env.global_variable_initialization {
            write!(
                f,
                "init_g_{self}_{}()",
                convert_name(&env.variable_names[self])
            )
        } else {
            write!(f, "g_{self}_{}", convert_name(&env.variable_names[self]))
        }
    }
}

impl DisplayWithEnv for ast_step1::GlobalVariable {
    fn fmt_with_env(&self, env: Env<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if env.global_variable_initialization {
            write!(f, "init_g_original_{self}()",)
        } else {
            write!(f, "g_original_{self}",)
        }
    }
}

impl DisplayWithEnv for LocalVariable {
    fn fmt_with_env(&self, _env: Env<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "l_{self}")
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

impl DisplayWithEnv for CType {
    fn fmt_with_env(&self, env: Env<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match env.c_type_definitions[self.i.0] {
            CTypeScheme::I64 => write!(f, "int64_t"),
            CTypeScheme::U8 => write!(f, "uint8_t"),
            CTypeScheme::F64 => write!(f, "double"),
            CTypeScheme::Ptr => write!(f, "void*"),
            CTypeScheme::Aggregate(_) => write!(f, "struct t{}", self.i.0),
            CTypeScheme::Union(_) => write!(f, "struct t{}", self.i.0),
            CTypeScheme::Mut(t) => write!(f, "{}*", Dis(&t, env)),
            CTypeScheme::Diverge => write!(f, "struct diverge"),
        }?;
        if self.boxed {
            write!(f, "*")?
        }
        Ok(())
    }
}

struct StringEscape<'a>(&'a str);

impl Display for StringEscape<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for c in self.0.bytes() {
            match c {
                b'\'' => write!(f, r"\'"),
                b'\"' => write!(f, r#"\""#),
                b'\\' => write!(f, r"\\"),
                b'?' => write!(f, r"\?"),
                b' '..=b'~' => write!(f, "{}", c as char),
                b'\n' => write!(f, r"\n"),
                b'\t' => write!(f, r"\t"),
                b'\r' => write!(f, r"\r"),
                _ => write!(f, r"\x{:02X}", c),
            }?;
        }
        Ok(())
    }
}
