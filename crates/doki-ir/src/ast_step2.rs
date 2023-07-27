mod local_variable;
mod type_memo;

pub use self::local_variable::{LocalVariable, LocalVariableCollector};
use self::type_memo::{get_tag_normal, GetTagNormalResult, TypeMemo};
pub use self::type_memo::{
    DisplayTypeWithEnv, DisplayTypeWithEnvStruct, Type, TypeForHash, TypeInner, TypeInnerForHash,
    TypeInnerOf, TypeUnit, TypeUnitForHash, TypeUnitOf,
};
use crate::ast_step1::{
    self, ConstructorNames, GlobalVariable, LambdaId, LocalVariableTypes, PaddedTypeMap,
    ReplaceMap, TypeId, TypePointer,
};
use crate::ast_step2::type_memo::BrokenLinkCheck;
use crate::collector::Collector;
use crate::id_generator::{self, IdGenerator};
use crate::intrinsics::{IntrinsicConstructor, IntrinsicTypeTag, IntrinsicVariable};
use crate::ConstructorId;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::fmt::{Debug, Display};

#[derive(Debug)]
pub struct Ast<'a> {
    pub variable_decls: Vec<VariableDecl<'a>>,
    pub entry_point: FxLambdaId,
    pub variable_names: FxHashMap<VariableId, String>,
    pub functions: Vec<Function>,
    pub type_map: PaddedTypeMap,
    pub variable_types: LocalVariableCollector<Type>,
    pub constructor_names: ConstructorNames,
    pub type_id_generator: IdGenerator<TypeForHash, TypeIdTag>,
    pub local_variable_replace_map: FxHashMap<(ast_step1::LocalVariable, Root), LocalVariable>,
    pub used_intrinsic_variables: Collector<(IntrinsicVariable, Vec<Type>)>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct GlobalVariableId(usize);

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl<'a> {
    pub name: &'a str,
    pub value: FunctionBody,
    pub decl_id: GlobalVariableId,
    pub original_decl_id: GlobalVariable,
    pub t: Type,
    pub t_for_hash: TypeForHash,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FunctionBody {
    pub basic_blocks: Vec<BasicBlock>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct BasicBlock {
    pub instructions: Vec<Instruction>,
    pub end_instruction: EndInstruction,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Tester {
    Tag { tag: u32 },
    I64 { value: i64 },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Instruction {
    Assign(LocalVariable, Expr),
    Test {
        tester: Tester,
        operand: VariableId,
        catch_label: usize,
    },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum EndInstruction {
    Ret(VariableId),
    Goto { label: usize },
    Panic { msg: String },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    Lambda {
        lambda_id: FxLambdaId,
        context: Vec<LocalVariable>,
    },
    I64(i64),
    U8(u8),
    Str(String),
    Ident(VariableId),
    Call {
        ctx: VariableId,
        a: VariableId,
        f: FxLambdaId,
        tail_call: RefCell<bool>,
    },
    BasicCall {
        args: Vec<VariableId>,
        id: BasicFunction,
    },
    Upcast {
        tag: u32,
        value: VariableId,
    },
    Downcast {
        tag: u32,
        value: VariableId,
        check: bool,
    },
    Ref(VariableId),
    Deref(VariableId),
}

#[derive(Debug, PartialEq, Clone, Copy, Eq)]
pub enum BasicFunction {
    Intrinsic { v: IntrinsicVariable, id: usize },
    Construction(ConstructorId),
    IntrinsicConstruction(IntrinsicConstructor),
    FieldAccessor { field: usize },
}

#[derive(Debug, PartialEq, Hash, Clone, Copy, Eq)]
pub enum VariableId {
    Local(LocalVariable),
    Global(GlobalVariableId),
}

#[derive(Debug, PartialEq, Clone)]
pub struct Function {
    pub id: FxLambdaId,
    pub context: Vec<LocalVariable>,
    pub parameter: LocalVariable,
    pub body: FunctionBody,
    pub ret: VariableId,
}

impl<'a> Ast<'a> {
    pub fn from(ast: ast_step1::Ast<'a>, minimize_type: bool) -> Self {
        let mut memo = Env::new(
            ast.variable_decls,
            ast.local_variable_types,
            ast.type_map,
            ast.constructor_names,
            minimize_type,
        );
        memo.monomorphize_decl_rec(
            ast.entry_point,
            ast.type_of_entry_point,
            &mut Default::default(),
        );
        let mut variable_names = FxHashMap::default();
        for v in &memo.monomorphized_variables {
            variable_names.insert(VariableId::Global(v.decl_id), v.name.to_string());
        }
        let b = &memo.monomorphized_variables.last().unwrap().value;
        match &b.basic_blocks[0].instructions[0] {
            Instruction::Assign(_, Expr::Lambda { lambda_id, context }) => {
                debug_assert!(context.is_empty());
                let entry_point = *lambda_id;
                let functions = memo
                    .functions
                    .into_values()
                    .map(|f| match f {
                        FunctionEntry::Placeholder(_) => panic!(),
                        FunctionEntry::Function(f) => f,
                    })
                    .collect();
                Self {
                    variable_decls: memo.monomorphized_variables,
                    entry_point,
                    functions,
                    variable_names,
                    type_map: memo.map,
                    variable_types: memo.local_variable_collector,
                    constructor_names: memo.constructor_names,
                    type_id_generator: memo.type_memo.type_id_generator,
                    local_variable_replace_map: memo.local_variable_replace_map,
                    used_intrinsic_variables: memo.used_intrinsic_variables,
                }
            }
            _ => panic!(),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
struct FnId {
    arg_t: TypeForHash,
    ret_t: TypeForHash,
    lambda_id: LambdaId<TypeForHash>,
}

pub struct Env<'a> {
    variable_decls: FxHashMap<GlobalVariable, ast_step1::VariableDecl<'a>>,
    monomorphized_variable_map: FxHashMap<Root, GlobalVariableId>,
    monomorphized_variables: Vec<VariableDecl<'a>>,
    map: PaddedTypeMap,
    functions: FxHashMap<LambdaId<TypeUnique>, FunctionEntry>,
    type_memo: TypeMemo,
    local_variable_types_old: LocalVariableTypes,
    local_variable_replace_map: FxHashMap<(ast_step1::LocalVariable, Root), LocalVariable>,
    local_variable_collector: LocalVariableCollector<Type>,
    global_variable_count: usize,
    constructor_names: ConstructorNames,
    minimize_type: bool,
    used_intrinsic_variables: Collector<(IntrinsicVariable, Vec<Type>)>,
}

#[derive(Debug)]
pub enum FunctionEntry {
    Placeholder(FxLambdaId),
    Function(Function),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct FxLambdaId(pub u32);

#[derive(Debug, Clone, Copy)]
pub struct TypeIdTag;

type TypeUnique = id_generator::Id<TypeIdTag>;
type Root = (TypeUnique, ast_step1::GlobalVariable);

struct BasicBlockEnv {
    basic_blocks: Vec<Option<BasicBlock>>,
    instructions: Vec<Instruction>,
    current_basic_block: Option<usize>,
}

impl BasicBlockEnv {
    fn new_label(&mut self) -> usize {
        let l = self.basic_blocks.len();
        self.basic_blocks.push(None);
        l
    }

    fn end_current_block(&mut self, end_instruction: EndInstruction) {
        let e = &mut self.basic_blocks[self.current_basic_block.unwrap()];
        debug_assert!(e.is_none());
        *e = Some(BasicBlock {
            instructions: std::mem::take(&mut self.instructions),
            end_instruction,
        });
        self.current_basic_block = None;
    }
}

impl<'a> Env<'a> {
    pub fn new(
        variable_decls: Vec<ast_step1::VariableDecl<'a>>,
        local_variable_types: LocalVariableTypes,
        map: PaddedTypeMap,
        constructor_names: ConstructorNames,
        minimize_type: bool,
    ) -> Self {
        Env {
            variable_decls: variable_decls.into_iter().map(|d| (d.decl_id, d)).collect(),
            monomorphized_variable_map: Default::default(),
            monomorphized_variables: Default::default(),
            map,
            functions: FxHashMap::default(),
            type_memo: TypeMemo::default(),
            local_variable_types_old: local_variable_types,
            local_variable_replace_map: FxHashMap::default(),
            local_variable_collector: LocalVariableCollector::new(),
            global_variable_count: 0,
            constructor_names,
            minimize_type,
            used_intrinsic_variables: Default::default(),
        }
    }

    fn monomorphize_decl_rec(
        &mut self,
        decl_id: GlobalVariable,
        p: TypePointer,
        replace_map: &mut ReplaceMap,
    ) -> GlobalVariableId {
        let p = self.map.clone_pointer(p, replace_map);
        let t_for_hash = self.get_type_for_hash(p);
        let t_id = self
            .type_memo
            .type_id_generator
            .get_or_insert(t_for_hash.clone());
        let t = self.get_type(p);
        let root = (t_id, decl_id);
        if let Some(d) = self.monomorphized_variable_map.get(&root) {
            *d
        } else {
            let new_decl_id = GlobalVariableId(self.global_variable_count);
            self.global_variable_count += 1;
            let d = self.variable_decls.get(&decl_id).unwrap().clone();
            self.monomorphized_variable_map.insert(root, new_decl_id);
            let (instructions, _) = self.function_body(d.value, root, replace_map, d.ret);
            let d = VariableDecl {
                value: FunctionBody {
                    basic_blocks: instructions,
                },
                decl_id: new_decl_id,
                original_decl_id: decl_id,
                name: d.name,
                t,
                t_for_hash,
            };
            self.monomorphized_variables.push(d);
            new_decl_id
        }
    }

    fn new_variable(&mut self, t: Type) -> LocalVariable {
        debug_assert!(!t.contains_broken_link());
        self.local_variable_collector.new_variable(t)
    }

    fn local_variable_def_replace(
        &mut self,
        v: ast_step1::LocalVariable,
        root_t: Root,
        replace_map: &mut ReplaceMap,
    ) -> LocalVariable {
        debug_assert!(!self.local_variable_replace_map.contains_key(&(v, root_t)));
        let t = self.local_variable_types_old.get(v);
        let t = self.map.clone_pointer(t, replace_map);
        let t = self.get_type(t);
        let new_v = self.new_variable(t);
        self.local_variable_replace_map.insert((v, root_t), new_v);
        new_v
    }

    fn get_defined_local_variable(
        &mut self,
        v: ast_step1::LocalVariable,
        root_t: Root,
        replace_map: &mut ReplaceMap,
    ) -> LocalVariable {
        if let Some(d) = self.local_variable_replace_map.get(&(v, root_t)) {
            *d
        } else {
            // Some variables are undefined because of
            // the elimination of unreachable code.
            let t = self.local_variable_types_old.get(v);
            let t = self.map.clone_pointer(t, replace_map);
            let t = self.get_type(t);
            self.new_variable(t)
        }
    }

    fn get_defined_variable_id(
        &mut self,
        v: ast_step1::VariableId,
        root_t: Root,
        replace_map: &mut ReplaceMap,
    ) -> VariableId {
        match v {
            ast_step1::VariableId::Local(d) => {
                VariableId::Local(self.get_defined_local_variable(d, root_t, replace_map))
            }
            ast_step1::VariableId::Global(d, r, p) => {
                let mut r = replace_map.clone().merge(r, &mut self.map);
                VariableId::Global(self.monomorphize_decl_rec(d, p, &mut r))
            }
        }
    }

    fn block(
        &mut self,
        block: ast_step1::Block,
        catch_label: usize,
        root_t: Root,
        replace_map: &mut ReplaceMap,
        basic_block_env: &mut BasicBlockEnv,
    ) -> Result<(), EndInstruction> {
        for i in block.instructions {
            self.instruction(i, catch_label, root_t, replace_map, basic_block_env)?;
        }
        Ok(())
    }

    fn function_body(
        &mut self,
        block: ast_step1::Block,
        root_t: Root,
        replace_map: &mut ReplaceMap,
        ret: ast_step1::LocalVariable,
    ) -> (Vec<BasicBlock>, VariableId) {
        let fallback = Some(BasicBlock {
            instructions: Vec::new(),
            end_instruction: EndInstruction::Panic {
                msg: "uncaught exception detected".to_string(),
            },
        });
        let mut block_env = BasicBlockEnv {
            basic_blocks: vec![None, fallback],
            instructions: Vec::new(),
            current_basic_block: Some(0),
        };
        let (end, ret) = if let Err(end) = self.block(block, 1, root_t, replace_map, &mut block_env)
        {
            let t = self.local_variable_types_old.get(ret);
            let t = self.map.clone_pointer(t, replace_map);
            let t = self.get_type(t);
            let ret = self.new_variable(t);
            (end, VariableId::Local(ret))
        } else {
            let ret = self.get_defined_variable_id(
                ast_step1::VariableId::Local(ret),
                root_t,
                replace_map,
            );
            (EndInstruction::Ret(ret), ret)
        };
        block_env.end_current_block(end);
        (
            block_env
                .basic_blocks
                .into_iter()
                .map(|a| a.unwrap())
                .collect(),
            ret,
        )
    }

    // Returns true if exited with a error
    fn instruction(
        &mut self,
        instruction: ast_step1::Instruction,
        catch_label: usize,
        root_t: Root,
        replace_map: &mut ReplaceMap,
        basic_block_env: &mut BasicBlockEnv,
    ) -> Result<(), EndInstruction> {
        match instruction {
            ast_step1::Instruction::Assign(v, e) => {
                let t = self
                    .map
                    .clone_pointer(self.local_variable_types_old.get(v), replace_map);
                let t = self.map.clone_pointer(t, replace_map);
                let t = self.get_type(t);
                let e = self.expr(e, &t, root_t, replace_map, basic_block_env, catch_label);
                match e {
                    Ok(e) => {
                        let new_v =
                            if let Some(v) = self.local_variable_replace_map.get(&(v, root_t)) {
                                *v
                            } else {
                                let new_v = self.new_variable(t);
                                self.local_variable_replace_map.insert((v, root_t), new_v);
                                new_v
                            };
                        basic_block_env
                            .instructions
                            .push(Instruction::Assign(new_v, e));
                        Ok(())
                    }
                    Err(msg) => Err(EndInstruction::Panic { msg }),
                }
            }
            ast_step1::Instruction::Test(ast_step1::Tester::I64 { value }, l) => {
                let type_id = TypeId::Intrinsic(IntrinsicTypeTag::I64);
                let a = self.downcast(
                    l,
                    root_t,
                    type_id,
                    replace_map,
                    &mut basic_block_env.instructions,
                    true,
                    catch_label,
                );
                match a {
                    Ok(a) => {
                        basic_block_env.instructions.push(Instruction::Test {
                            tester: Tester::I64 { value },
                            operand: a,
                            catch_label,
                        });
                        Ok(())
                    }
                    Err(_) => Err(EndInstruction::Goto { label: catch_label }),
                }
            }
            ast_step1::Instruction::Test(ast_step1::Tester::Constructor { id }, a) => {
                let t = self
                    .map
                    .clone_pointer(self.local_variable_types_old.get(a), replace_map);
                let t = self.get_type(t);
                let a = self.get_defined_local_variable(a, root_t, replace_map);
                match get_tag_normal(&t, id) {
                    GetTagNormalResult::Tagged(tag, _untagged_t) => {
                        let a =
                            self.deref(VariableId::Local(a), &t, &mut basic_block_env.instructions);
                        basic_block_env.instructions.push(Instruction::Test {
                            tester: Tester::Tag { tag },
                            operand: a,
                            catch_label,
                        });
                        Ok(())
                    }
                    GetTagNormalResult::NotTagged => Ok(()),
                    GetTagNormalResult::Impossible => {
                        Err(EndInstruction::Goto { label: catch_label })
                    }
                }
            }
            ast_step1::Instruction::TryCatch(a, b) => {
                let catch = basic_block_env.new_label();
                let mut next = None;
                let end_instruction =
                    if let Err(end) = self.block(a, catch, root_t, replace_map, basic_block_env) {
                        end
                    } else {
                        let l = basic_block_env.new_label();
                        next = Some(l);
                        EndInstruction::Goto { label: l }
                    };
                basic_block_env.end_current_block(end_instruction);
                basic_block_env.current_basic_block = Some(catch);
                let end_instruction = if let Err(end) =
                    self.block(b, catch_label, root_t, replace_map, basic_block_env)
                {
                    end
                } else {
                    let l = next.unwrap_or_else(|| basic_block_env.new_label());
                    next = Some(l);
                    EndInstruction::Goto { label: l }
                };
                if let Some(next) = next {
                    basic_block_env.end_current_block(end_instruction);
                    basic_block_env.current_basic_block = Some(next);
                    Ok(())
                } else {
                    Err(end_instruction)
                }
            }
            ast_step1::Instruction::FailTest => Err(EndInstruction::Goto { label: catch_label }),
            ast_step1::Instruction::Panic { msg } => Err(EndInstruction::Panic { msg }),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn downcast(
        &mut self,
        a: ast_step1::LocalVariable,
        root_t: Root,
        type_id: TypeId,
        replace_map: &mut ReplaceMap,
        instructions: &mut Vec<Instruction>,
        test_instead_of_panic: bool,
        catch_label: usize,
    ) -> Result<VariableId, String> {
        let t = self
            .map
            .clone_pointer(self.local_variable_types_old.get(a), replace_map);
        let t = self.get_type(t);
        let a = self.get_defined_local_variable(a, root_t, replace_map);
        let a = self.deref(VariableId::Local(a), &t, instructions);
        match get_tag_normal(&t, type_id) {
            GetTagNormalResult::Tagged(tag, casted_t) => {
                let casted_t: Type = casted_t.into();
                if test_instead_of_panic {
                    instructions.push(Instruction::Test {
                        tester: Tester::Tag { tag },
                        operand: a,
                        catch_label,
                    });
                };
                Ok(self.expr_to_variable(
                    Expr::Downcast {
                        tag,
                        value: a,
                        check: !test_instead_of_panic,
                    },
                    casted_t,
                    instructions,
                ))
            }
            GetTagNormalResult::NotTagged => Ok(a),
            GetTagNormalResult::Impossible => Err(format!(
                "expected {type_id} but got {}. cannot downcast.",
                DisplayTypeWithEnvStruct(&t, &self.constructor_names)
            )),
        }
    }

    // Returns `None` if impossible type error
    fn expr(
        &mut self,
        e: ast_step1::Expr,
        t: &Type,
        root_t: Root,
        replace_map: &mut ReplaceMap,
        basic_block_env: &mut BasicBlockEnv,
        catch_label: usize,
    ) -> Result<Expr, String> {
        use Expr::*;
        let e = match e {
            ast_step1::Expr::Lambda {
                lambda_id,
                parameter,
                body,
                ret,
                context,
            } => {
                let context = context
                    .into_iter()
                    .map(|v| self.get_defined_local_variable(v, root_t, replace_map))
                    .collect_vec();
                let possible_functions = self.get_possible_functions(t);
                let parameter = self.local_variable_def_replace(parameter, root_t, replace_map);
                let (basic_blocks, ret) = self.function_body(body, root_t, replace_map, ret);
                let lambda_id = LambdaId {
                    id: lambda_id.id,
                    root_t: root_t.0,
                };
                let e = self.functions.get_mut(&lambda_id).unwrap();
                let FunctionEntry::Placeholder(fx_lambda_id) = *e else {
                    panic!()
                };
                *e = FunctionEntry::Function(Function {
                    id: fx_lambda_id,
                    parameter,
                    body: FunctionBody { basic_blocks },
                    context: context.clone(),
                    ret,
                });
                let e = if possible_functions.len() == 1 && possible_functions[0].0 == 0 {
                    Lambda {
                        context,
                        lambda_id: possible_functions[0].1,
                    }
                } else {
                    let i = possible_functions
                        .binary_search_by_key(&fx_lambda_id, |(_, l, _)| *l)
                        .unwrap();
                    let f = &possible_functions[i];
                    let d = self.new_variable(f.2.clone());
                    basic_block_env.instructions.push(Instruction::Assign(
                        d,
                        Lambda {
                            context,
                            lambda_id: fx_lambda_id,
                        },
                    ));
                    Upcast {
                        tag: f.0 as u32,
                        value: VariableId::Local(d),
                    }
                };
                if t.reference {
                    let v = self.expr_to_variable(
                        e,
                        t.clone().deref(),
                        &mut basic_block_env.instructions,
                    );
                    Expr::Ref(v)
                } else {
                    e
                }
            }
            ast_step1::Expr::I64(s) => self.add_tags_to_expr(
                I64(s),
                t,
                TypeId::Intrinsic(IntrinsicTypeTag::I64),
                &mut basic_block_env.instructions,
            ),
            ast_step1::Expr::U8(s) => self.add_tags_to_expr(
                U8(s),
                t,
                TypeId::Intrinsic(IntrinsicTypeTag::U8),
                &mut basic_block_env.instructions,
            ),
            ast_step1::Expr::Str(s) => self.add_tags_to_expr(
                Str(s),
                t,
                TypeId::Intrinsic(IntrinsicTypeTag::Ptr),
                &mut basic_block_env.instructions,
            ),
            ast_step1::Expr::Ident(v) => {
                Ident(self.get_defined_variable_id(v, root_t, replace_map))
            }
            ast_step1::Expr::Call { f, a } => {
                let f_t = self.local_variable_types_old.get(f);
                let f_t = self.map.clone_pointer(f_t, replace_map);
                let f_t = self.get_type(f_t);
                let possible_functions = self.get_possible_functions(&f_t);
                let f = self.get_defined_local_variable(f, root_t, replace_map);
                let f = self.deref(
                    VariableId::Local(f),
                    &f_t,
                    &mut basic_block_env.instructions,
                );
                let a = VariableId::Local(self.get_defined_local_variable(a, root_t, replace_map));
                if possible_functions.is_empty() {
                    return Err("not a function".to_string());
                }
                if possible_functions.len() == 1 && possible_functions[0].0 == 0 {
                    Call {
                        ctx: f,
                        a,
                        f: possible_functions[0].1,
                        tail_call: RefCell::new(false),
                    }
                } else {
                    let ret_v = self.new_variable(t.clone());
                    let skip = basic_block_env.new_label();
                    for (tag, id, casted_t) in possible_functions {
                        let next = basic_block_env.new_label();
                        basic_block_env.instructions.push(Instruction::Test {
                            tester: Tester::Tag { tag: tag as u32 },
                            operand: f,
                            catch_label: next,
                        });
                        let new_f = self.new_variable(casted_t);
                        basic_block_env.instructions.push(Instruction::Assign(
                            new_f,
                            Expr::Downcast {
                                tag: tag as u32,
                                value: f,
                                check: false,
                            },
                        ));
                        basic_block_env.instructions.push(Instruction::Assign(
                            ret_v,
                            Expr::Call {
                                ctx: VariableId::Local(new_f),
                                a,
                                f: id,
                                tail_call: RefCell::new(false),
                            },
                        ));
                        basic_block_env.end_current_block(EndInstruction::Goto { label: skip });
                        basic_block_env.current_basic_block = Some(next);
                    }
                    basic_block_env.end_current_block(EndInstruction::Panic {
                        msg: "not a function".to_string(),
                    });
                    basic_block_env.current_basic_block = Some(skip);
                    Ident(VariableId::Local(ret_v))
                }
            }
            ast_step1::Expr::BasicCall {
                args,
                id: ast_step1::BasicFunction::Construction(id),
            } => {
                let args = args
                    .into_iter()
                    .map(|a| {
                        VariableId::Local(self.get_defined_local_variable(a, root_t, replace_map))
                    })
                    .collect();
                self.add_tags_to_expr(
                    BasicCall {
                        args,
                        id: BasicFunction::Construction(id),
                    },
                    t,
                    TypeId::UserDefined(id),
                    &mut basic_block_env.instructions,
                )
            }
            ast_step1::Expr::BasicCall {
                args,
                id: ast_step1::BasicFunction::IntrinsicConstruction(id),
            } => {
                debug_assert!(args.is_empty());
                self.add_tags_to_expr(
                    BasicCall {
                        args: Vec::new(),
                        id: BasicFunction::IntrinsicConstruction(id),
                    },
                    t,
                    TypeId::Intrinsic(id.into()),
                    &mut basic_block_env.instructions,
                )
            }
            ast_step1::Expr::BasicCall {
                args,
                id: ast_step1::BasicFunction::FieldAccessor { constructor, field },
            } => {
                debug_assert_eq!(args.len(), 1);
                let a = args.into_iter().next().unwrap();
                let a = self.downcast(
                    a,
                    root_t,
                    TypeId::UserDefined(constructor),
                    replace_map,
                    &mut basic_block_env.instructions,
                    false,
                    catch_label,
                )?;
                BasicCall {
                    args: vec![a],
                    id: BasicFunction::FieldAccessor { field },
                }
            }
            ast_step1::Expr::BasicCall {
                args,
                id: ast_step1::BasicFunction::Intrinsic(id),
            } => {
                let arg_restrictions = id.runtime_arg_type_restriction();
                let mut args_new = Vec::with_capacity(args.len());
                let mut arg_ts = Vec::with_capacity(args.len());
                for (a, param_t) in args.into_iter().zip_eq(arg_restrictions) {
                    let a = if let Some(param_t) = param_t {
                        self.downcast(
                            a,
                            root_t,
                            param_t,
                            replace_map,
                            &mut basic_block_env.instructions,
                            false,
                            catch_label,
                        )?
                    } else {
                        VariableId::Local(self.get_defined_local_variable(a, root_t, replace_map))
                    };
                    args_new.push(a);
                    arg_ts.push(match a {
                        VariableId::Local(a) => self.local_variable_collector.get_type(a).clone(),
                        VariableId::Global(_) => panic!(),
                    });
                }
                let count = self.used_intrinsic_variables.get_or_insert((id, arg_ts));
                let e = BasicCall {
                    args: args_new,
                    id: BasicFunction::Intrinsic { v: id, id: count },
                };
                match id.runtime_return_type() {
                    Some(rt) => self.add_tags_to_expr(
                        e,
                        t,
                        TypeId::Intrinsic(rt),
                        &mut basic_block_env.instructions,
                    ),
                    None => e,
                }
            }
        };
        Ok(e)
    }

    fn get_possible_functions(&mut self, ot: &Type) -> Vec<(i32, FxLambdaId, Type)> {
        let mut fs = Vec::new();
        let mut tag = 0;
        for t in ot.iter() {
            let t = t.clone().replace_index(ot, 0);
            match t {
                TypeUnitOf::Normal { .. } => {
                    tag += 1;
                }
                TypeUnitOf::Fn(fn_id, arg_t, ret_t) => {
                    debug_assert!(!arg_t.contains_broken_link(0));
                    debug_assert!(!ret_t.contains_broken_link(0));
                    for id_type_inner in fn_id {
                        let len = self.functions.len() as u32;
                        let e = self
                            .functions
                            .entry(id_type_inner.0)
                            .or_insert(FunctionEntry::Placeholder(FxLambdaId(len)));
                        let id = match e {
                            FunctionEntry::Placeholder(id) => *id,
                            FunctionEntry::Function(f) => f.id,
                        };
                        fs.push((
                            tag,
                            id,
                            TypeUnitOf::Fn([id_type_inner].into(), arg_t.clone(), ret_t.clone())
                                .into(),
                        ));
                        tag += 1;
                    }
                }
            }
        }
        fs
    }

    fn minimize(&mut self, p: TypePointer) {
        if self.minimize_type && !self.type_memo.minimized_pointers.contains(&p) {
            self.map.minimize(p, &mut self.type_memo.minimized_pointers);
        }
    }

    fn get_type(&mut self, p: TypePointer) -> Type {
        self.minimize(p);
        self.type_memo.collect_ref_pointers(p, &mut self.map);
        self.type_memo.get_type(p, &mut self.map)
    }

    fn get_type_for_hash(&mut self, p: TypePointer) -> TypeForHash {
        self.minimize(p);
        self.type_memo.collect_ref_pointers(p, &mut self.map);
        self.type_memo.get_type_for_hash(p, &mut self.map)
    }

    fn expr_to_variable(
        &mut self,
        e: Expr,
        t: Type,
        instructions: &mut Vec<Instruction>,
    ) -> VariableId {
        let d = self.new_variable(t);
        instructions.push(Instruction::Assign(d, e));
        VariableId::Local(d)
    }

    fn deref(
        &mut self,
        v: VariableId,
        t: &Type,
        instructions: &mut Vec<Instruction>,
    ) -> VariableId {
        if t.reference {
            let d = self.new_variable(t.clone().deref());
            instructions.push(Instruction::Assign(d, Expr::Deref(v)));
            VariableId::Local(d)
        } else {
            v
        }
    }

    fn add_tags_to_expr(
        &mut self,
        e: Expr,
        t: &Type,
        id: TypeId,
        instructions: &mut Vec<Instruction>,
    ) -> Expr {
        let e = match get_tag_normal(t, id) {
            GetTagNormalResult::Tagged(tag, tu) => {
                let d = self.new_variable(tu.into());
                instructions.push(Instruction::Assign(d, e));
                Expr::Upcast {
                    tag,
                    value: VariableId::Local(d),
                }
            }
            GetTagNormalResult::NotTagged => e,
            GetTagNormalResult::Impossible => {
                panic!()
            }
        };
        if t.reference {
            let d = self.new_variable(t.clone().deref());
            instructions.push(Instruction::Assign(d, e));
            Expr::Ref(VariableId::Local(d))
        } else {
            e
        }
    }
}

impl Display for FxLambdaId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "f_{}", self.0)
    }
}

impl Display for GlobalVariableId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
