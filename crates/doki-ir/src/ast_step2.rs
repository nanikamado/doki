pub mod c_type;
mod local_variable;
mod type_memo;
mod union_find;

use self::c_type::{CTypeEnv, CTypeScheme, PointerForCType};
pub use self::local_variable::{LocalVariable, LocalVariableCollector};
use self::type_memo::TypeMemo;
pub use self::type_memo::{
    DisplayTypeWithEnv, DisplayTypeWithEnvStruct, DisplayTypeWithEnvStructOption, Type,
    TypeForHash, TypeInner, TypeInnerForHash, TypeInnerOf, TypeUnit, TypeUnitForHash, TypeUnitOf,
};
use self::union_find::UnionFind;
use crate::ast_step1::{
    self, ConstructorNames, GlobalVariable, LambdaId, LocalVariableTypes, PaddedTypeMap,
    ReplaceMap, Terminal, TypeId, TypePointer,
};
use crate::ast_step2::c_type::PointerModifier;
use crate::intrinsics::{IntrinsicConstructor, IntrinsicTypeTag, IntrinsicVariable};
use crate::util::collector::Collector;
use crate::util::dfa_minimization::Dfa;
use crate::util::id_generator::{self, IdGenerator};
use crate::ConstructorId;
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::RefCell;
use std::fmt::{Debug, Display};

#[derive(Debug)]
pub struct Ast<'a> {
    pub variable_decls: Vec<VariableDecl<'a>>,
    pub entry_point: FxLambdaId,
    pub variable_names: FxHashMap<VariableId, String>,
    pub functions: Vec<Function>,
    pub variable_types: LocalVariableCollector<(Option<Type>, CType)>,
    pub constructor_names: ConstructorNames,
    pub type_id_generator: IdGenerator<TypeForHash, TypeIdTag>,
    pub local_variable_replace_map: FxHashMap<(ast_step1::LocalVariable, Root), LocalVariable>,
    pub used_intrinsic_variables: Collector<(IntrinsicVariable, Vec<CType>, CType)>,
    pub c_type_definitions: Vec<CTypeScheme<CType>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct CType(pub usize);

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct GlobalVariableId(usize);

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl<'a> {
    pub name: &'a str,
    pub value: FunctionBody,
    pub decl_id: GlobalVariableId,
    pub original_decl_id: GlobalVariable,
    pub t: Type,
    pub c_t: CType,
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
    pub context_c_type: CType,
    pub parameter: LocalVariable,
    pub body: FunctionBody,
    pub ret: VariableId,
}

impl<'a> Ast<'a> {
    pub fn from(ast: ast_step1::Ast<'a>) -> Self {
        let mut memo = Env::new(
            ast.variable_decls,
            ast.local_variable_types,
            ast.type_map,
            ast.constructor_names,
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
                    variable_types: memo.local_variable_collector,
                    constructor_names: memo.constructor_names,
                    type_id_generator: memo.type_memo.type_id_generator,
                    local_variable_replace_map: memo.local_variable_replace_map,
                    used_intrinsic_variables: memo.used_intrinsic_variables,
                    c_type_definitions: memo.c_type_definitions,
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
    local_variable_collector: LocalVariableCollector<(Option<Type>, CType)>,
    global_variable_count: usize,
    constructor_names: ConstructorNames,
    used_intrinsic_variables: Collector<(IntrinsicVariable, Vec<CType>, CType)>,
    c_type_memo: FxHashMap<PointerForCType, CType>,
    c_type_memo_from_hash: Collector<CTypeForHash>,
    c_type_for_hash_memo: FxHashMap<TypePointer, CTypeForHash>,
    c_type_definitions: Vec<CTypeScheme<CType>>,
    normalizer_for_c_type: UnionFind<PointerForCType>,
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
    ) -> Self {
        let mut c_type_memo_from_hash: Collector<_> = Default::default();
        c_type_memo_from_hash
            .get_or_insert(CTypeForHash(vec![CTypeForHashUnit::Aggregate(Vec::new())]));
        let c_type_definitions = vec![CTypeScheme::Aggregate(Vec::new())];
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
            used_intrinsic_variables: Default::default(),
            c_type_memo: Default::default(),
            c_type_memo_from_hash,
            c_type_for_hash_memo: Default::default(),
            c_type_definitions,
            normalizer_for_c_type: Default::default(),
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
        let t = self.get_type(PointerForCType::from(p)).unwrap();
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
                c_t: self.c_type(PointerForCType::from(p)),
                t_for_hash,
            };
            self.monomorphized_variables.push(d);
            new_decl_id
        }
    }

    fn new_variable(&mut self, p: PointerForCType) -> LocalVariable {
        let ct = self.c_type(p);
        let t = self.get_type(p);
        self.local_variable_collector.new_variable((t, ct))
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
        let new_v = self.new_variable(PointerForCType::from(t));
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
            // let t = self.get_type(t);
            self.new_variable(PointerForCType::from(t))
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
                let p1 = self.map.clone_pointer(p, replace_map);
                let mut r = replace_map.clone().merge(r, &mut self.map);
                let p2 = self.map.clone_pointer(p, &mut r);
                debug_assert_eq!(p1, p2);
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
            let ret = self.new_variable(PointerForCType::from(t));
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
                let p = self
                    .map
                    .clone_pointer(self.local_variable_types_old.get(v), replace_map);
                let e = self.expr(e, p, root_t, replace_map, basic_block_env, catch_label);
                match e {
                    Ok(e) => {
                        let new_v =
                            if let Some(v) = self.local_variable_replace_map.get(&(v, root_t)) {
                                *v
                            } else {
                                let new_v = self.new_variable(PointerForCType::from(p));
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
                let p = self
                    .map
                    .clone_pointer(self.local_variable_types_old.get(a), replace_map);
                let a = self.get_defined_local_variable(a, root_t, replace_map);
                match self.get_tag_normal(p, id) {
                    GetTagNormalResult::Tagged(tag) => {
                        // let t = self.get_type(p);
                        let a =
                            self.deref(VariableId::Local(a), p, &mut basic_block_env.instructions);
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
        let p = self
            .map
            .clone_pointer(self.local_variable_types_old.get(a), replace_map);
        let a = self.get_defined_local_variable(a, root_t, replace_map);
        let a = self.deref(VariableId::Local(a), p, instructions);
        match self.get_tag_normal(p, type_id) {
            GetTagNormalResult::Tagged(tag) => {
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
                    PointerForCType {
                        p,
                        modifier: PointerModifier::UnionMember(tag),
                    },
                    instructions,
                ))
            }
            GetTagNormalResult::NotTagged => Ok(a),
            GetTagNormalResult::Impossible => {
                let t = self.get_type(PointerForCType::from(p)).unwrap();
                Err(format!(
                    "expected {type_id} but got {}. cannot downcast.",
                    DisplayTypeWithEnvStruct(&t, &self.constructor_names)
                ))
            }
        }
    }

    // Returns `None` if impossible type error
    fn expr(
        &mut self,
        e: ast_step1::Expr,
        p: TypePointer,
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
                let is_ref = self.type_is_ref(p);
                let (possible_functions, tag_len) = self.get_possible_functions(p);
                let parameter = self.local_variable_def_replace(parameter, root_t, replace_map);
                let (basic_blocks, ret) = self.function_body(body, root_t, replace_map, ret);
                let lambda_id = LambdaId {
                    id: lambda_id.id,
                    root_t: root_t.0,
                };
                let FunctionEntry::Placeholder(fx_lambda_id) =
                    *self.functions.get(&lambda_id).unwrap()
                else {
                    panic!()
                };
                let (e, context_c_type) = if possible_functions.len() == 1 && tag_len == 1 {
                    (
                        Lambda {
                            context: context.clone(),
                            lambda_id: possible_functions[0].1,
                        },
                        possible_functions[0].2,
                    )
                } else {
                    let i = possible_functions
                        .binary_search_by_key(&fx_lambda_id, |(_, l, _)| *l)
                        .unwrap();
                    let f = &possible_functions[i];
                    let d = self.local_variable_collector.new_variable((None, f.2));
                    basic_block_env.instructions.push(Instruction::Assign(
                        d,
                        Lambda {
                            context: context.clone(),
                            lambda_id: fx_lambda_id,
                        },
                    ));
                    (
                        Upcast {
                            tag: f.0,
                            value: VariableId::Local(d),
                        },
                        f.2,
                    )
                };
                self.functions.insert(
                    lambda_id,
                    FunctionEntry::Function(Function {
                        id: fx_lambda_id,
                        parameter,
                        body: FunctionBody { basic_blocks },
                        context,
                        context_c_type,
                        ret,
                    }),
                );
                if is_ref {
                    let v = self.expr_to_variable_derefed(e, p, &mut basic_block_env.instructions);
                    Expr::Ref(v)
                } else {
                    e
                }
            }
            ast_step1::Expr::I64(s) => self.add_tags_to_expr(
                I64(s),
                p,
                TypeId::Intrinsic(IntrinsicTypeTag::I64),
                &mut basic_block_env.instructions,
            ),
            ast_step1::Expr::U8(s) => self.add_tags_to_expr(
                U8(s),
                p,
                TypeId::Intrinsic(IntrinsicTypeTag::U8),
                &mut basic_block_env.instructions,
            ),
            ast_step1::Expr::Str(s) => self.add_tags_to_expr(
                Str(s),
                p,
                TypeId::Intrinsic(IntrinsicTypeTag::Ptr),
                &mut basic_block_env.instructions,
            ),
            ast_step1::Expr::Ident(v) => {
                match v {
                    ast_step1::VariableId::Local(_) => (),
                    ast_step1::VariableId::Global(_, _, p2) => {
                        let p2 = self.map.clone_pointer(p2, replace_map);
                        debug_assert_eq!(p, p2);
                    }
                }
                let v = self.get_defined_variable_id(v, root_t, replace_map);
                Ident(v)
            }
            ast_step1::Expr::Call { f, a } => {
                let f_t = self.local_variable_types_old.get(f);
                let f_t_p = self.map.clone_pointer(f_t, replace_map);
                let (possible_functions, tag_len) = self.get_possible_functions(f_t_p);
                let f = self.get_defined_local_variable(f, root_t, replace_map);
                let f = self.deref(
                    VariableId::Local(f),
                    f_t_p,
                    &mut basic_block_env.instructions,
                );
                let a = VariableId::Local(self.get_defined_local_variable(a, root_t, replace_map));
                if possible_functions.is_empty() {
                    return Err("not a function".to_string());
                }
                if possible_functions.len() == 1 && tag_len == 1 {
                    Call {
                        ctx: f,
                        a,
                        f: possible_functions[0].1,
                        tail_call: RefCell::new(false),
                    }
                } else {
                    let ret_v = self.new_variable(PointerForCType::from(p));
                    let skip = basic_block_env.new_label();
                    for (tag, id, casted_ct) in possible_functions {
                        let next = basic_block_env.new_label();
                        basic_block_env.instructions.push(Instruction::Test {
                            tester: Tester::Tag { tag },
                            operand: f,
                            catch_label: next,
                        });
                        let new_f = self
                            .local_variable_collector
                            .new_variable((None, casted_ct));
                        basic_block_env.instructions.push(Instruction::Assign(
                            new_f,
                            Expr::Downcast {
                                tag,
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
                    p,
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
                    p,
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
                        VariableId::Local(a) => self.local_variable_collector.get_type(a).1,
                        VariableId::Global(_) => panic!(),
                    });
                }
                let ct_p = if let Some(rt) = id.runtime_return_type() {
                    match self.get_tag_normal(p, TypeId::Intrinsic(rt)) {
                        GetTagNormalResult::NotTagged => PointerForCType::from(p),
                        GetTagNormalResult::Tagged(tag) => PointerForCType {
                            p,
                            modifier: PointerModifier::UnionMember(tag),
                        },
                        GetTagNormalResult::Impossible => panic!(),
                    }
                } else {
                    PointerForCType::from(p)
                };
                let ret_t = self.c_type(ct_p);
                let count = self
                    .used_intrinsic_variables
                    .get_or_insert((id, arg_ts, ret_t));
                let e = BasicCall {
                    args: args_new,
                    id: BasicFunction::Intrinsic { v: id, id: count },
                };
                match id.runtime_return_type() {
                    Some(rt) => self.add_tags_to_expr(
                        e,
                        p,
                        TypeId::Intrinsic(rt),
                        &mut basic_block_env.instructions,
                    ),
                    None => e,
                }
            }
        };
        Ok(e)
    }

    fn get_possible_functions(&mut self, ot: TypePointer) -> (Vec<(u32, FxLambdaId, CType)>, u32) {
        let ot = self.map.find(ot);
        self.c_type(PointerForCType::from(ot));
        let mut fs = Vec::new();
        let mut tag = 0;
        if let ast_step1::Terminal::TypeMap(ts) = self.map.dereference(ot) {
            let normals_len = ts.normals.len();
            for (id, args) in ts.normals.clone() {
                if let TypeId::Intrinsic(IntrinsicTypeTag::Fn) = id {
                    let ls = self
                        .type_memo
                        .get_lambda_ids_pointer(args[2], &mut self.map);
                    let ls_len = ls.len();
                    for lambda_id in ls.keys().copied().collect_vec() {
                        let len = self.functions.len() as u32;
                        let e = self
                            .functions
                            .entry(lambda_id)
                            .or_insert(FunctionEntry::Placeholder(FxLambdaId(len)));
                        let id = match e {
                            FunctionEntry::Placeholder(id) => *id,
                            FunctionEntry::Function(f) => f.id,
                        };
                        let p = PointerForCType {
                            p: ot,
                            modifier: if normals_len + ls_len == 2 {
                                PointerModifier::Normal
                            } else {
                                PointerModifier::UnionMember(tag)
                            },
                        };
                        let ctx_hash = self.c_type_for_hash(p);
                        let ct = self.c_type_memo_from_hash.get(&ctx_hash).unwrap();
                        debug_assert_eq!(
                            self.c_type_definitions.len(),
                            self.c_type_memo_from_hash.len()
                        );
                        fs.push((tag, id, CType(ct)));
                        tag += 1;
                    }
                } else {
                    tag += 1;
                }
            }
        } else {
            panic!()
        }
        (fs, tag)
    }

    fn get_type(&mut self, p: PointerForCType) -> Option<Type> {
        match p.modifier {
            PointerModifier::Normal => {
                self.type_memo.collect_ref_pointers(p.p, &self.map);
                let t = self.type_memo.get_type(p.p, &mut self.map);
                Some(t)
            }
            PointerModifier::UnionMember(_) => None,
            PointerModifier::Derefed => {
                self.type_memo.collect_ref_pointers(p.p, &self.map);
                let mut t = self.type_memo.get_type(p.p, &mut self.map);
                debug_assert!(t.reference);
                debug_assert!(!t.derefed);
                t.derefed = true;
                Some(t)
            }
        }
    }

    fn get_type_for_hash(&mut self, p: TypePointer) -> TypeForHash {
        self.type_memo.collect_ref_pointers(p, &self.map);
        self.type_memo.get_type_for_hash(p, &mut self.map)
    }

    fn expr_to_variable(
        &mut self,
        e: Expr,
        t: PointerForCType,
        instructions: &mut Vec<Instruction>,
    ) -> VariableId {
        let d = self.new_variable(t);
        instructions.push(Instruction::Assign(d, e));
        VariableId::Local(d)
    }

    fn expr_to_variable_derefed(
        &mut self,
        e: Expr,
        p: TypePointer,
        instructions: &mut Vec<Instruction>,
    ) -> VariableId {
        let d = self.new_variable(PointerForCType {
            p,
            modifier: PointerModifier::Derefed,
        });
        instructions.push(Instruction::Assign(d, e));
        VariableId::Local(d)
    }

    fn deref(
        &mut self,
        v: VariableId,
        p: TypePointer,
        instructions: &mut Vec<Instruction>,
    ) -> VariableId {
        if self.type_is_ref(p) {
            let d = self.new_variable(PointerForCType {
                p,
                modifier: PointerModifier::Derefed,
            });
            instructions.push(Instruction::Assign(d, Expr::Deref(v)));
            VariableId::Local(d)
        } else {
            v
        }
    }

    fn add_tags_to_expr(
        &mut self,
        e: Expr,
        p: TypePointer,
        id: TypeId,
        instructions: &mut Vec<Instruction>,
    ) -> Expr {
        let e = match self.get_tag_normal(p, id) {
            GetTagNormalResult::Tagged(tag) => {
                let d = self.new_variable(PointerForCType {
                    p,
                    modifier: PointerModifier::UnionMember(tag),
                });
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
        let t = self.get_type(PointerForCType::from(p)).unwrap();
        if t.reference {
            let d = self.new_variable(PointerForCType {
                p,
                modifier: PointerModifier::Derefed,
            });
            instructions.push(Instruction::Assign(d, e));
            Expr::Ref(VariableId::Local(d))
        } else {
            e
        }
    }

    fn get_tag_normal(&mut self, ot: TypePointer, type_id: TypeId) -> GetTagNormalResult {
        debug_assert_ne!(type_id, TypeId::Intrinsic(IntrinsicTypeTag::Fn));
        let mut tag = 0;
        let mut result = None;
        if let ast_step1::Terminal::TypeMap(ts) = self.map.dereference(ot) {
            let ts_len = ts.normals.len();
            for (id, args) in ts.normals.clone() {
                if let TypeId::Intrinsic(IntrinsicTypeTag::Fn) = id {
                    debug_assert_eq!(tag + 1, ts_len);
                } else {
                    if id == type_id {
                        debug_assert!(result.is_none());
                        let p = self.map.new_pointer();
                        self.map.insert_normal(p, id, args);
                        result = Some(tag);
                    }
                    tag += 1;
                }
            }
        } else {
            panic!()
        }
        match result {
            Some(tag_of_t) => {
                if tag == 1 {
                    GetTagNormalResult::NotTagged
                } else {
                    GetTagNormalResult::Tagged(tag_of_t as u32)
                }
            }
            None => GetTagNormalResult::Impossible,
        }
    }

    pub fn c_type(&mut self, p: PointerForCType) -> CType {
        let p = self.normalizer_for_c_type.find(PointerForCType {
            p: self.map.find(p.p),
            ..p
        });
        if let Some(t) = self.c_type_memo.get(&p) {
            *t
        } else {
            debug_assert!(!self.normalizer_for_c_type.contains(p));
            self.type_memo.collect_ref_pointers(p.p, &self.map);
            self.map.minimize(p.p);
            let c_type_for_hash = self.c_type_for_hash(p);
            if let Some(t) = self.c_type_memo_from_hash.get(&c_type_for_hash) {
                return CType(t);
            }
            let mut partitions = Default::default();
            self.collect_pointers(p.p, &mut partitions);
            let c_type_schemes = partitions
                .keys()
                .map(|p| (*p, self.get_c_type_scheme_from_pointer(*p)))
                .collect();
            let (partitions, c_type_defs) = CTypeEnv(&c_type_schemes).split_partitions(partitions);
            debug_assert!(partitions.contains_key(&p));
            let partition_rev: FxHashMap<_, _> = partitions.iter().map(|(k, v)| (*v, *k)).collect();
            let c_type_defs_rev: FxHashMap<_, _> =
                c_type_defs.iter().map(|(k, v)| (*v, k)).collect();
            for (t, p) in &partitions {
                debug_assert!(self.map.is_terminal(t.p));
                let r = partition_rev[p];
                debug_assert!(self.map.is_terminal(r.p));
                debug_assert!(self.type_memo.ref_checked_pointers.contains(&t.p));
                debug_assert!(self.type_memo.ref_checked_pointers.contains(&r.p));
                if *t != r {
                    self.normalizer_for_c_type.union(*t, r)
                }
            }
            let mut new_c_type_defs = Vec::new();
            for (g, t) in &partition_rev {
                let t = self.normalizer_for_c_type.find(*t);
                let for_hash = self.c_type_for_hash(t);
                if let Some(c_type) = self.c_type_memo_from_hash.get(&for_hash) {
                    self.c_type_memo.insert(t, CType(c_type));
                } else {
                    let c_type = self.c_type_memo_from_hash.get_or_insert(for_hash);
                    self.c_type_memo.insert(t, CType(c_type));
                    let d = c_type_defs_rev[g];
                    debug_assert_eq!(
                        matches!(c_type_schemes[&t], CTypeScheme::Union(_)),
                        matches!(d, CTypeScheme::Union(_))
                    );
                    new_c_type_defs.push(d);
                }
            }
            for d in new_c_type_defs {
                let d = d.replace_ref(|a| {
                    let a = partition_rev[a];
                    let a = self.normalizer_for_c_type.find(a);
                    let for_hash = self.c_type_for_hash(a);
                    CType(self.c_type_memo_from_hash.get(&for_hash).unwrap())
                });
                self.c_type_definitions.push(d);
            }
            debug_assert_eq!(
                self.c_type_memo_from_hash.len(),
                self.c_type_definitions.len()
            );
            self.c_type_memo[&self.normalizer_for_c_type.find(p)]
        }
    }

    fn type_is_ref(&mut self, p: TypePointer) -> bool {
        self.type_memo.collect_ref_pointers(p, &self.map);
        debug_assert!(self.type_memo.ref_checked_pointers.contains(&p));
        self.type_memo.ref_pointers.contains(&p)
    }

    fn c_type_for_hash(&mut self, p: PointerForCType) -> CTypeForHash {
        #[cfg(debug_assertions)]
        if self.map.minimize_types {
            let p = self.map.find(p.p);
            assert!(self.map.minimized_pointers.contains(&p))
        }
        match p.modifier {
            PointerModifier::Normal => {
                if let CTypeForHashInner::Type(t) = self.c_type_for_hash_inner(
                    p.p,
                    &mut Default::default(),
                    &mut Default::default(),
                    0,
                ) {
                    t
                } else {
                    panic!()
                }
            }
            PointerModifier::UnionMember(tag) => self.c_type_for_hash_inner_with_tag(p.p, tag),
            PointerModifier::Derefed => self.c_type_for_hash_inner_derefed(p.p),
        }
    }

    fn collect_hash_unit(
        &mut self,
        p: TypePointer,
        ts: &mut Vec<CTypeForHashUnit>,
        trace: &mut FxHashMap<TypePointer, u32>,
        used_trace: &mut FxHashSet<TypePointer>,
        depth: u32,
    ) {
        if let Terminal::TypeMap(type_map) = &self.map.dereference_without_find(p) {
            for (type_id, args) in type_map.normals.clone() {
                match type_id {
                    TypeId::Intrinsic(tag) => match tag {
                        IntrinsicTypeTag::Ptr => ts.push(CTypeForHashUnit::Ptr),
                        IntrinsicTypeTag::I64 => ts.push(CTypeForHashUnit::I64),
                        IntrinsicTypeTag::U8 => ts.push(CTypeForHashUnit::U8),
                        IntrinsicTypeTag::Unit => ts.push(CTypeForHashUnit::Aggregate(Vec::new())),
                        IntrinsicTypeTag::Fn => {
                            let ids = self
                                .type_memo
                                .get_lambda_ids_pointer(args[2], &mut self.map);
                            for ctx in ids.values().cloned().collect_vec() {
                                let ctx = ctx
                                    .iter()
                                    .map(|p| {
                                        self.c_type_for_hash_inner(*p, trace, used_trace, depth)
                                    })
                                    .collect();
                                ts.push(CTypeForHashUnit::Aggregate(ctx));
                            }
                        }
                        IntrinsicTypeTag::Mut => {
                            let t = self.c_type_for_hash_inner(args[0], trace, used_trace, depth);
                            ts.push(CTypeForHashUnit::Ref(t));
                        }
                    },
                    TypeId::UserDefined(_) => {
                        let args = args
                            .iter()
                            .map(|p| self.c_type_for_hash_inner(*p, trace, used_trace, depth))
                            .collect();
                        ts.push(CTypeForHashUnit::Aggregate(args));
                    }
                }
            }
        } else {
            panic!()
        }
    }

    fn c_type_for_hash_inner(
        &mut self,
        p: TypePointer,
        trace: &mut FxHashMap<TypePointer, u32>,
        used_trace: &mut FxHashSet<TypePointer>,
        depth: u32,
    ) -> CTypeForHashInner {
        let p = self.map.find(p);
        let p = self.normalizer_for_c_type.find(PointerForCType::from(p));
        debug_assert_eq!(p.modifier, PointerModifier::Normal);
        let p = p.p;
        debug_assert!(self.type_memo.ref_checked_pointers.contains(&p));
        if self.type_memo.diverging_pointers.contains(&p) {
            return CTypeForHashInner::Type(CTypeForHash(vec![CTypeForHashUnit::Diverge]));
        }
        if let Some(t) = self.c_type_for_hash_memo.get(&p) {
            debug_assert!(!trace.contains_key(&p));
            return CTypeForHashInner::Type(t.clone());
        }
        if let Some(d) = trace.get(&p) {
            used_trace.insert(p);
            return CTypeForHashInner::Index(depth - *d - 1);
        }
        trace.insert(p, depth);
        let depth = depth + 1;
        let mut ts = Vec::new();
        self.collect_hash_unit(p, &mut ts, trace, used_trace, depth);
        let mut t = CTypeForHash(ts);
        trace.remove(&p);
        if self.type_memo.ref_pointers.contains(&p) {
            t = CTypeForHash(vec![CTypeForHashUnit::Ref(CTypeForHashInner::Type(t))]);
        }
        if used_trace.is_empty() {
            let o = self.c_type_for_hash_memo.insert(p, t.clone());
            debug_assert!(o.is_none());
        }
        used_trace.remove(&p);
        CTypeForHashInner::Type(t)
    }

    fn c_type_for_hash_inner_derefed(&mut self, p: TypePointer) -> CTypeForHash {
        let p = self.map.find(p);
        let p = self.normalizer_for_c_type.find(PointerForCType::from(p));
        debug_assert_eq!(p.modifier, PointerModifier::Normal);
        let p = p.p;
        debug_assert!(self.type_memo.ref_checked_pointers.contains(&p));
        if self.type_memo.diverging_pointers.contains(&p) {
            return CTypeForHash(vec![CTypeForHashUnit::Diverge]);
        }
        let mut ts = Vec::new();
        self.collect_hash_unit(
            p,
            &mut ts,
            &mut Default::default(),
            &mut Default::default(),
            0,
        );
        CTypeForHash(ts)
    }

    fn c_type_for_hash_inner_with_tag(&mut self, p: TypePointer, tag: u32) -> CTypeForHash {
        let p = self.map.find(p);
        let p = self.normalizer_for_c_type.find(PointerForCType::from(p));
        debug_assert_eq!(p.modifier, PointerModifier::Normal);
        let p = p.p;
        debug_assert!(self.type_memo.ref_checked_pointers.contains(&p));
        if self.type_memo.diverging_pointers.contains(&p) {
            return CTypeForHash(vec![CTypeForHashUnit::Diverge]);
        }
        let mut ts = Vec::new();
        self.collect_hash_unit(
            p,
            &mut ts,
            &mut Default::default(),
            &mut Default::default(),
            0,
        );
        CTypeForHash(vec![ts.into_iter().nth(tag as usize).unwrap()])
    }

    pub fn get_c_type_scheme_from_pointer(
        &mut self,
        node: PointerForCType,
    ) -> CTypeScheme<PointerForCType> {
        debug_assert!(self.map.is_terminal(node.p));
        if self.type_memo.diverging_pointers.contains(&node.p) {
            return CTypeScheme::Diverge;
        }
        if node.modifier == PointerModifier::Normal && self.type_memo.ref_pointers.contains(&node.p)
        {
            return CTypeScheme::Mut(PointerForCType {
                modifier: PointerModifier::Derefed,
                p: node.p,
            });
        }
        let mut ts = Vec::new();
        if let Terminal::TypeMap(t) = self.map.dereference(node.p) {
            for (id, args) in t.normals.clone() {
                match id {
                    TypeId::Intrinsic(tag) => match tag {
                        IntrinsicTypeTag::Ptr => ts.push(CTypeScheme::Ptr),
                        IntrinsicTypeTag::I64 => ts.push(CTypeScheme::I64),
                        IntrinsicTypeTag::U8 => ts.push(CTypeScheme::U8),
                        IntrinsicTypeTag::Unit => ts.push(CTypeScheme::Aggregate(Vec::new())),
                        IntrinsicTypeTag::Fn => {
                            let ids = self
                                .type_memo
                                .get_lambda_ids_pointer(args[2], &mut self.map);
                            for ctx in ids.values() {
                                ts.push(CTypeScheme::Aggregate(
                                    ctx.iter()
                                        .copied()
                                        .map(|p| PointerForCType::from(self.map.find_imm(p)))
                                        .collect(),
                                ));
                            }
                        }
                        IntrinsicTypeTag::Mut => {
                            ts.push(CTypeScheme::Mut(PointerForCType::from(
                                self.map.find_imm(args[0]),
                            )));
                        }
                    },
                    TypeId::UserDefined(_) => {
                        ts.push(CTypeScheme::Aggregate(
                            args.iter()
                                .copied()
                                .map(|p| PointerForCType::from(self.map.find_imm(p)))
                                .collect(),
                        ));
                    }
                }
            }
        } else {
            panic!()
        }
        if let PointerModifier::UnionMember(tag) = node.modifier {
            ts.into_iter().nth(tag as usize).unwrap()
        } else if ts.len() == 1 {
            ts.pop().unwrap()
        } else {
            CTypeScheme::Union(
                (0..ts.len() as u32)
                    .map(|i| PointerForCType {
                        modifier: PointerModifier::UnionMember(i),
                        p: node.p,
                    })
                    .collect(),
            )
        }
    }

    fn collect_pointers(
        &mut self,
        p: TypePointer,
        pointers: &mut FxHashMap<PointerForCType, usize>,
    ) {
        let p = self.map.find_imm(p);
        let contains = pointers.insert(PointerForCType::from(p), 0).is_some();
        if contains {
            return;
        }
        if self.type_memo.ref_pointers.contains(&p) {
            pointers.insert(
                PointerForCType {
                    p,
                    modifier: PointerModifier::Derefed,
                },
                0,
            );
        }
        let mut tag = 0;
        if let Terminal::TypeMap(t) = self.map.dereference_without_find(p) {
            for (id, args) in t.normals.clone() {
                match id {
                    TypeId::Intrinsic(IntrinsicTypeTag::Fn) => {
                        for ctx in self
                            .type_memo
                            .get_lambda_ids_pointer(args[2], &mut self.map)
                            .values()
                            .cloned()
                            .collect_vec()
                        {
                            for t in ctx {
                                self.collect_pointers(t, pointers);
                            }
                            tag += 1;
                        }
                    }
                    _ => {
                        for t in args {
                            self.collect_pointers(t, pointers);
                        }
                        tag += 1;
                    }
                }
            }
        } else {
            panic!()
        }
        if tag >= 2 {
            for i in 0..tag {
                pointers.insert(
                    PointerForCType {
                        p,
                        modifier: PointerModifier::UnionMember(i),
                    },
                    0,
                );
            }
        }
    }
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum CTypeForHashInner {
    Type(CTypeForHash),
    Index(u32),
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct CTypeForHash(Vec<CTypeForHashUnit>);

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum CTypeForHashUnit {
    I64,
    U8,
    Ptr,
    Aggregate(Vec<CTypeForHashInner>),
    Ref(CTypeForHashInner),
    Diverge,
}

pub enum GetTagNormalResult {
    NotTagged,
    Impossible,
    Tagged(u32),
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
