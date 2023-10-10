pub mod c_type;
mod local_variable;
mod type_memo;
mod union_find;

use self::c_type::{CTypeEnv, CTypeScheme, PointerForCType};
pub use self::local_variable::{LocalVariable, LocalVariableCollector};
use self::type_memo::TypeMemo;
pub use self::type_memo::{
    DisplayTypeWithEnv, DisplayTypeWithEnvStruct, DisplayTypeWithEnvStructOption, Type,
    TypeForHash, TypeInner, TypeInnerForHash, TypeInnerOf, TypeUnitOf,
};
use self::union_find::UnionFind;
use crate::ast_step1::{
    self, BoxPoint, ConstructorNames, GlobalVariable, LambdaId, LocalVariableTypes, PaddedTypeMap,
    ReplaceMap, TypeId, TypePointer, TypeTagForBoxPoint,
};
use crate::ast_step2::c_type::PointerModifier;
use crate::intrinsics::{IntrinsicTypeTag, IntrinsicVariable};
use crate::util::collector::Collector;
use crate::util::dfa_minimization::Dfa;
use crate::util::id_generator::{self, IdGenerator};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fmt::{Debug, Display};

#[derive(Debug)]
pub struct Ast<'a> {
    pub variable_decls: Vec<VariableDecl<'a>>,
    pub entry_block: FunctionBody,
    pub variable_names: FxHashMap<GlobalVariableId, String>,
    pub functions: Vec<Function>,
    pub variable_types: LocalVariableCollector<(Option<Type>, CType)>,
    pub constructor_names: ConstructorNames,
    pub type_id_generator: IdGenerator<TypeForHash, TypeIdTag>,
    pub local_variable_replace_map: FxHashMap<(ast_step1::LocalVariable, Root), LocalVariable>,
    pub used_intrinsic_variables: Collector<(IntrinsicVariable, Vec<CType>, CType)>,
    pub c_type_definitions: Vec<CTypeScheme<CType>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct StructId(pub usize);

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct CType {
    pub i: StructId,
    pub boxed: bool,
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
    I64(i64),
    U8(u8),
    Str(String),
    Ident(VariableId),
    Call {
        args: Vec<VariableId>,
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
    Intrinsic { v: IntrinsicVariable, id: u32 },
    Construction,
    FieldAccessor { field: u32, boxed: bool },
}

#[derive(Debug, PartialEq, Hash, Clone, Copy, Eq)]
pub enum VariableId {
    Local(LocalVariable),
    Global(GlobalVariableId),
}

#[derive(Debug, PartialEq, Clone)]
pub struct VariableInContext {
    pub l: LocalVariable,
    pub boxed: bool,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Function {
    pub id: FxLambdaId,
    pub parameters: Vec<LocalVariable>,
    pub body: FunctionBody,
    pub ret: VariableId,
}

impl<'a> Ast<'a> {
    pub fn from(ast: ast_step1::Ast<'a>) -> Self {
        let variable_decls = ast.variable_decls.iter().map(|d| (d.decl_id, d)).collect();
        let mut memo = Env::new(
            variable_decls,
            ast.local_variable_types,
            ast.type_map,
            ast.constructor_names,
        );
        let entry_block = {
            let mut replace_map = Default::default();
            let ast_step1::Instruction::Assign(ret, _) =
                ast.entry_block.instructions.last().unwrap()
            else {
                panic!()
            };
            let p = memo.map.new_pointer();
            let t = memo.get_type_for_hash(p);
            let type_id = memo.type_memo.type_id_generator.get_or_insert(t);
            let (mut entry_block, _) = memo.function_body(
                &ast.entry_block,
                (type_id, ast.global_variable_for_entry_block),
                &mut replace_map,
                *ret,
            );
            entry_block.pop();
            FunctionBody {
                basic_blocks: entry_block,
            }
        };
        debug_assert_eq!(memo.job_stack.len(), 1);
        while let Some(j) = memo.job_stack.pop() {
            memo.handle_job(j);
        }
        let mut variable_names = FxHashMap::default();
        for v in &memo.monomorphized_variables {
            variable_names.insert(v.decl_id, v.name.to_string());
        }
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
            entry_block,
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
}

#[derive(Debug, PartialEq, Clone)]
struct FnId {
    arg_t: TypeForHash,
    ret_t: TypeForHash,
    lambda_id: LambdaId<TypeForHash>,
}

struct Env<'a, 'b> {
    variable_decls: FxHashMap<GlobalVariable, &'b ast_step1::VariableDecl<'a>>,
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
    c_type_for_hash_memo_with_tag: FxHashMap<(TypePointer, u32), CTypeForHash>,
    c_type_definitions: Vec<CTypeScheme<CType>>,
    normalizer_for_c_type: UnionFind<PointerForCType>,
    job_stack: Vec<Job>,
}

struct Job {
    original_decl_id: GlobalVariable,
    root_t: Root,
    decl_id: GlobalVariableId,
    p: TypePointer,
    t_for_hash: TypeForHash,
    replace_map: ReplaceMap,
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

pub type TypeUnique = id_generator::Id<TypeIdTag>;
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

    fn assign(&mut self, v: LocalVariable, e: Expr) {
        self.instructions.push(Instruction::Assign(v, e));
    }
}

impl<'a, 'b> Env<'a, 'b> {
    fn new(
        variable_decls: FxHashMap<GlobalVariable, &'b ast_step1::VariableDecl<'a>>,
        local_variable_types: LocalVariableTypes,
        map: PaddedTypeMap,
        constructor_names: ConstructorNames,
    ) -> Self {
        let mut c_type_memo_from_hash: Collector<_> = Default::default();
        c_type_memo_from_hash
            .get_or_insert(CTypeForHash(vec![CTypeForHashUnit::Aggregate(Vec::new())]));
        let c_type_definitions = vec![CTypeScheme::Aggregate(Vec::new())];
        Env {
            variable_decls,
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
            c_type_for_hash_memo_with_tag: Default::default(),
            c_type_definitions,
            normalizer_for_c_type: Default::default(),
            job_stack: Vec::with_capacity(20),
        }
    }

    fn monomorphize_decl_rec(
        &mut self,
        decl_id: GlobalVariable,
        p: TypePointer,
        replace_map: ReplaceMap,
    ) -> GlobalVariableId {
        debug_assert!(self.map.is_terminal(p));
        let t_for_hash = self.get_type_for_hash(p);
        let t_id = self
            .type_memo
            .type_id_generator
            .get_or_insert(t_for_hash.clone());
        let root_t = (t_id, decl_id);
        if let Some(d) = self.monomorphized_variable_map.get(&root_t) {
            *d
        } else {
            let new_decl_id = GlobalVariableId(self.global_variable_count);
            self.global_variable_count += 1;
            self.monomorphized_variable_map.insert(root_t, new_decl_id);
            self.job_stack.push(Job {
                original_decl_id: decl_id,
                root_t,
                decl_id: new_decl_id,
                p,
                t_for_hash,
                replace_map,
            });
            new_decl_id
        }
    }

    fn handle_job(&mut self, mut j: Job) {
        let d = *self.variable_decls.get(&j.original_decl_id).unwrap();
        let (instructions, _) = self.function_body(&d.value, j.root_t, &mut j.replace_map, d.ret);
        let p = PointerForCType::from(j.p);
        let d = VariableDecl {
            value: FunctionBody {
                basic_blocks: instructions,
            },
            decl_id: j.decl_id,
            original_decl_id: j.original_decl_id,
            name: d.name,
            t: self.get_type(p).unwrap(),
            c_t: self.c_type(p),
            t_for_hash: j.t_for_hash,
        };
        self.monomorphized_variables.push(d);
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
            self.new_variable(PointerForCType::from(t))
        }
    }

    fn get_defined_variable_id(
        &mut self,
        v: &ast_step1::VariableId,
        root_t: Root,
        replace_map: &mut ReplaceMap,
    ) -> VariableId {
        match v {
            ast_step1::VariableId::Local(d) => {
                VariableId::Local(self.get_defined_local_variable(*d, root_t, replace_map))
            }
            ast_step1::VariableId::Global(d, r, p) => {
                let p1 = self.map.clone_pointer(*p, replace_map);
                let r = replace_map.clone().merge(r, &mut self.map);
                #[cfg(debug_assertions)]
                let mut r = r;
                #[cfg(debug_assertions)]
                {
                    let p2 = self.map.clone_pointer(*p, &mut r);
                    assert_eq!(p1, p2);
                }
                VariableId::Global(self.monomorphize_decl_rec(*d, p1, r))
            }
        }
    }

    fn block(
        &mut self,
        block: &ast_step1::Block,
        catch_label: usize,
        root_t: Root,
        replace_map: &mut ReplaceMap,
        basic_block_env: &mut BasicBlockEnv,
    ) -> Result<(), EndInstruction> {
        for i in &block.instructions {
            self.instruction(i, catch_label, root_t, replace_map, basic_block_env)?;
        }
        Ok(())
    }

    fn function_body(
        &mut self,
        block: &ast_step1::Block,
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
                &ast_step1::VariableId::Local(ret),
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

    fn dummy_function_body(
        &mut self,
        replace_map: &mut ReplaceMap,
        ret: ast_step1::LocalVariable,
    ) -> (Vec<BasicBlock>, VariableId) {
        let t = self.local_variable_types_old.get(ret);
        let t = self.map.clone_pointer(t, replace_map);
        let ret = self.new_variable(PointerForCType::from(t));
        (
            vec![BasicBlock {
                instructions: Vec::new(),
                end_instruction: EndInstruction::Panic {
                    msg: "unexpected".to_string(),
                },
            }],
            ret.into(),
        )
    }

    // Returns true if exited with a error
    fn instruction(
        &mut self,
        instruction: &ast_step1::Instruction,
        catch_label: usize,
        root_t: Root,
        replace_map: &mut ReplaceMap,
        basic_block_env: &mut BasicBlockEnv,
    ) -> Result<(), EndInstruction> {
        match instruction {
            ast_step1::Instruction::Assign(v, e) => {
                let p = self.local_variable_types_old.get(*v);
                let p = self.map.clone_pointer(p, replace_map);
                let i = self.c_type(PointerForCType::from(p)).i.0;
                let new_v = if let Some(v) = self.local_variable_replace_map.get(&(*v, root_t)) {
                    *v
                } else {
                    let new_v = self.new_variable(PointerForCType::from(p));
                    self.local_variable_replace_map.insert((*v, root_t), new_v);
                    new_v
                };
                let e = self.expr(
                    e,
                    p,
                    new_v,
                    root_t,
                    replace_map,
                    basic_block_env,
                    catch_label,
                );
                if let Err(msg) = e {
                    Err(EndInstruction::Panic { msg })
                } else if let CTypeScheme::Diverge = self.c_type_definitions[i] {
                    Err(EndInstruction::Panic {
                        msg: "unexpected".to_string(),
                    })
                } else {
                    Ok(())
                }
            }
            ast_step1::Instruction::Test(ast_step1::Tester::I64 { value }, l) => {
                let type_id = TypeId::Intrinsic(IntrinsicTypeTag::I64);
                let p = self
                    .map
                    .clone_pointer(self.local_variable_types_old.get(*l), replace_map);
                let a = self.downcast(
                    *l,
                    p,
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
                            tester: Tester::I64 { value: *value },
                            operand: a.into(),
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
                    .clone_pointer(self.local_variable_types_old.get(*a), replace_map);
                let a = self.get_defined_local_variable(*a, root_t, replace_map);
                match self.get_tag_normal(p, *id) {
                    GetTagNormalResult::Tagged(tag) => {
                        basic_block_env.instructions.push(Instruction::Test {
                            tester: Tester::Tag { tag },
                            operand: VariableId::Local(a),
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
            ast_step1::Instruction::Panic { msg } => {
                Err(EndInstruction::Panic { msg: msg.clone() })
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn downcast(
        &mut self,
        a: ast_step1::LocalVariable,
        p: TypePointer,
        root_t: Root,
        type_id: TypeId,
        replace_map: &mut ReplaceMap,
        instructions: &mut Vec<Instruction>,
        test_instead_of_panic: bool,
        catch_label: usize,
    ) -> Result<LocalVariable, String> {
        let a = self.get_defined_local_variable(a, root_t, replace_map);
        match self.get_tag_normal(p, type_id) {
            GetTagNormalResult::Tagged(tag) => {
                if test_instead_of_panic {
                    instructions.push(Instruction::Test {
                        tester: Tester::Tag { tag },
                        operand: a.into(),
                        catch_label,
                    });
                };
                Ok(self.expr_to_variable(
                    Expr::Downcast {
                        tag,
                        value: a.into(),
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

    fn fn_call(
        &mut self,
        v: LocalVariable,
        f: PossibleFunction,
        a: VariableId,
        ctx: VariableId,
        ctx_box_point: &[Option<bool>],
        basic_block_env: &mut BasicBlockEnv,
    ) {
        use Expr::*;
        let mut args = vec![a];
        for (i, (c, b)) in f.ctx.iter().zip(ctx_box_point).enumerate() {
            let l = self.new_variable(PointerForCType::from(*c));
            basic_block_env.assign(
                l,
                BasicCall {
                    args: vec![ctx],
                    id: BasicFunction::FieldAccessor {
                        field: i as u32,
                        boxed: b.unwrap(),
                    },
                },
            );
            args.push(VariableId::Local(l));
        }
        basic_block_env.assign(
            v,
            Call {
                args,
                f: f.lambda_id,
                tail_call: RefCell::new(false),
            },
        )
    }

    #[allow(clippy::too_many_arguments)]
    /// Returns `Err` if type error
    fn expr(
        &mut self,
        e: &ast_step1::Expr,
        p: TypePointer,
        v: LocalVariable,
        root_t: Root,
        replace_map: &mut ReplaceMap,
        basic_block_env: &mut BasicBlockEnv,
        catch_label: usize,
    ) -> Result<(), String> {
        use Expr::*;
        match e {
            ast_step1::Expr::Lambda {
                lambda_id,
                parameter,
                body,
                ret,
                context,
            } => {
                let (possible_functions, tag_len) = self.get_possible_functions(p);
                let parameter = self.local_variable_def_replace(*parameter, root_t, replace_map);
                let (_, parameter_ct) = self.local_variable_collector.get_type(parameter);
                let parameter_ct = &self.c_type_definitions[parameter_ct.i.0];
                let (basic_blocks, ret) = if matches!(parameter_ct, CTypeScheme::Diverge) {
                    self.dummy_function_body(replace_map, *ret)
                } else {
                    self.function_body(body, root_t, replace_map, *ret)
                };
                let lambda_id = LambdaId {
                    id: lambda_id.id,
                    root_t: root_t.0,
                };
                let FunctionEntry::Placeholder(fx_lambda_id) =
                    *self.functions.get(&lambda_id).unwrap()
                else {
                    panic!()
                };
                let box_point = &self.map.dereference_without_find(p).box_point;
                let i = possible_functions
                    .binary_search_by_key(&fx_lambda_id, |l| l.lambda_id)
                    .unwrap();
                let f = &possible_functions[i];
                let tag = TypeTagForBoxPoint::Lambda(f.index_in_type_map);
                let BoxPoint::Boxed(pss) = box_point else {
                    panic!()
                };
                let bs = pss[&tag].clone();
                let parameters = std::iter::once(parameter)
                    .chain(
                        context
                            .iter()
                            .map(|l| self.get_defined_local_variable(*l, root_t, replace_map)),
                    )
                    .collect_vec();
                let context = parameters[1..]
                    .iter()
                    .zip(bs)
                    .map(|(l, boxed)| {
                        if boxed.unwrap() {
                            let (_, lt) = *self.local_variable_collector.get_type(*l);
                            let d = self
                                .local_variable_collector
                                .new_variable((None, CType { boxed: true, ..lt }));
                            basic_block_env
                                .instructions
                                .push(Instruction::Assign(d, Expr::Ref(VariableId::Local(*l))));
                            VariableId::Local(d)
                        } else {
                            VariableId::Local(*l)
                        }
                    })
                    .collect();
                let l = BasicCall {
                    args: context,
                    id: BasicFunction::Construction,
                };
                if possible_functions.len() == 1 && tag_len == 1 {
                    basic_block_env.assign(v, l);
                } else {
                    let d = self.local_variable_collector.new_variable((None, f.c_type));
                    basic_block_env.instructions.push(Instruction::Assign(d, l));
                    basic_block_env.assign(
                        v,
                        Upcast {
                            tag: f.tag,
                            value: VariableId::Local(d),
                        },
                    );
                };
                self.functions.insert(
                    lambda_id,
                    FunctionEntry::Function(Function {
                        id: fx_lambda_id,
                        parameters,
                        body: FunctionBody { basic_blocks },
                        ret,
                    }),
                );
            }
            ast_step1::Expr::I64(s) => {
                let e = self.add_tags_to_expr(
                    I64(*s),
                    p,
                    TypeId::Intrinsic(IntrinsicTypeTag::I64),
                    &mut basic_block_env.instructions,
                );
                basic_block_env.assign(v, e)
            }
            ast_step1::Expr::U8(s) => {
                let e = self.add_tags_to_expr(
                    U8(*s),
                    p,
                    TypeId::Intrinsic(IntrinsicTypeTag::U8),
                    &mut basic_block_env.instructions,
                );
                basic_block_env.assign(v, e)
            }
            ast_step1::Expr::Str(s) => {
                let e = self.add_tags_to_expr(
                    Str(s.clone()),
                    p,
                    TypeId::Intrinsic(IntrinsicTypeTag::Ptr),
                    &mut basic_block_env.instructions,
                );
                basic_block_env.assign(v, e)
            }
            ast_step1::Expr::Ident(l) => {
                #[cfg(debug_assertions)]
                match l {
                    ast_step1::VariableId::Local(_) => (),
                    ast_step1::VariableId::Global(_, _, p2) => {
                        let p2 = self.map.clone_pointer(*p2, replace_map);
                        assert_eq!(p, p2);
                    }
                }
                let l = self.get_defined_variable_id(l, root_t, replace_map);
                basic_block_env.assign(v, Ident(l));
            }
            ast_step1::Expr::Call { f, a } => {
                let f_t = self.local_variable_types_old.get(*f);
                let f_t_p = self.map.clone_pointer(f_t, replace_map);
                let (possible_functions, tag_len) = self.get_possible_functions(f_t_p);
                let f = VariableId::Local(self.get_defined_local_variable(*f, root_t, replace_map));
                let a = VariableId::Local(self.get_defined_local_variable(*a, root_t, replace_map));
                let BoxPoint::Boxed(box_point_of_f) =
                    &self.map.dereference_without_find(f_t_p).box_point
                else {
                    panic!()
                };
                if possible_functions.is_empty() {
                    return Err("not a function".to_string());
                }
                if possible_functions.len() == 1 && tag_len == 1 {
                    let possible_function = possible_functions[0].clone();
                    let tag = TypeTagForBoxPoint::Lambda(possible_function.index_in_type_map);
                    let ctx_box_point = box_point_of_f[&tag].clone();
                    self.fn_call(v, possible_function, a, f, &ctx_box_point, basic_block_env);
                } else {
                    let box_point_of_f = box_point_of_f.clone();
                    let skip = basic_block_env.new_label();
                    for possible_function in possible_functions {
                        let next = basic_block_env.new_label();
                        basic_block_env.instructions.push(Instruction::Test {
                            tester: Tester::Tag {
                                tag: possible_function.tag,
                            },
                            operand: f,
                            catch_label: next,
                        });
                        let new_f = self
                            .local_variable_collector
                            .new_variable((None, possible_function.c_type));
                        basic_block_env.instructions.push(Instruction::Assign(
                            new_f,
                            Downcast {
                                tag: possible_function.tag,
                                value: f,
                                check: false,
                            },
                        ));
                        let tag = TypeTagForBoxPoint::Lambda(possible_function.index_in_type_map);
                        self.fn_call(
                            v,
                            possible_function,
                            a,
                            VariableId::Local(new_f),
                            &box_point_of_f[&tag],
                            basic_block_env,
                        );
                        basic_block_env.end_current_block(EndInstruction::Goto { label: skip });
                        basic_block_env.current_basic_block = Some(next);
                    }
                    basic_block_env.end_current_block(EndInstruction::Panic {
                        msg: "not a function".to_string(),
                    });
                    basic_block_env.current_basic_block = Some(skip);
                }
            }
            ast_step1::Expr::BasicCall {
                args,
                id: ast_step1::BasicFunction::Construction(id),
            } => {
                let box_point = self.map.dereference_without_find(p).box_point.clone();
                let args = if let BoxPoint::Boxed(b) = box_point {
                    args.iter()
                        .zip(&b[&TypeTagForBoxPoint::Normal(TypeId::UserDefined(*id))])
                        .map(|(a, boxed)| {
                            let a = self.get_defined_local_variable(*a, root_t, replace_map);
                            VariableId::Local(if boxed.unwrap() {
                                let (_, ct) = self.local_variable_collector.get_type(a);
                                debug_assert!(!ct.boxed);
                                let d = self.local_variable_collector.new_variable((
                                    None,
                                    CType {
                                        i: ct.i,
                                        boxed: true,
                                    },
                                ));
                                basic_block_env
                                    .instructions
                                    .push(Instruction::Assign(d, Expr::Ref(VariableId::Local(a))));
                                d
                            } else {
                                a
                            })
                        })
                        .collect()
                } else {
                    args.iter()
                        .map(|a| {
                            let a = self.get_defined_local_variable(*a, root_t, replace_map);
                            VariableId::Local(a)
                        })
                        .collect()
                };
                let e = BasicCall {
                    args,
                    id: BasicFunction::Construction,
                };
                let instructions: &mut Vec<Instruction> = &mut basic_block_env.instructions;
                let e = match self.get_tag_normal(p, TypeId::UserDefined(*id)) {
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
                    GetTagNormalResult::Impossible => panic!(),
                };
                basic_block_env.assign(v, e);
            }
            ast_step1::Expr::BasicCall {
                args,
                id: ast_step1::BasicFunction::IntrinsicConstruction(id),
            } => {
                debug_assert!(args.is_empty());
                let e = self.add_tags_to_expr(
                    BasicCall {
                        args: Vec::new(),
                        id: BasicFunction::Construction,
                    },
                    p,
                    TypeId::Intrinsic((*id).into()),
                    &mut basic_block_env.instructions,
                );
                basic_block_env.assign(v, e)
            }
            ast_step1::Expr::BasicCall {
                args,
                id: ast_step1::BasicFunction::FieldAccessor { constructor, field },
            } => {
                debug_assert_eq!(args.len(), 1);
                let a = args.iter().next().unwrap();
                let p = self
                    .map
                    .clone_pointer(self.local_variable_types_old.get(*a), replace_map);
                let a = self.downcast(
                    *a,
                    p,
                    root_t,
                    TypeId::UserDefined(*constructor),
                    replace_map,
                    &mut basic_block_env.instructions,
                    false,
                    catch_label,
                )?;
                let deref = match &self.map.dereference(p).box_point {
                    BoxPoint::NotSure => panic!(),
                    BoxPoint::Diverging => false,
                    BoxPoint::Boxed(pss) => pss
                        [&TypeTagForBoxPoint::Normal(TypeId::UserDefined(*constructor))]
                        [*field as usize]
                        .unwrap(),
                };
                basic_block_env.assign(
                    v,
                    BasicCall {
                        args: vec![a.into()],
                        id: BasicFunction::FieldAccessor {
                            field: *field,
                            boxed: deref,
                        },
                    },
                )
            }
            ast_step1::Expr::BasicCall {
                args,
                id: ast_step1::BasicFunction::Intrinsic(id),
            } => {
                let arg_restrictions = id.runtime_arg_type_restriction();
                let mut args_new = Vec::with_capacity(args.len());
                let mut arg_ts = Vec::with_capacity(args.len());
                for (a, param_t) in args.iter().zip_eq(arg_restrictions) {
                    let a = if let Some(param_t) = param_t {
                        let p = self
                            .map
                            .clone_pointer(self.local_variable_types_old.get(*a), replace_map);
                        self.downcast(
                            *a,
                            p,
                            root_t,
                            param_t,
                            replace_map,
                            &mut basic_block_env.instructions,
                            false,
                            catch_label,
                        )?
                    } else {
                        self.get_defined_local_variable(*a, root_t, replace_map)
                    };
                    args_new.push(a.into());
                    arg_ts.push(self.local_variable_collector.get_type(a).1);
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
                    .get_or_insert((*id, arg_ts, ret_t));
                let e = BasicCall {
                    args: args_new,
                    id: BasicFunction::Intrinsic {
                        v: *id,
                        id: count as u32,
                    },
                };
                let e = match id.runtime_return_type() {
                    Some(rt) => self.add_tags_to_expr(
                        e,
                        p,
                        TypeId::Intrinsic(rt),
                        &mut basic_block_env.instructions,
                    ),
                    None => e,
                };
                basic_block_env.assign(v, e);
            }
        };
        Ok(())
    }

    fn get_possible_functions(&mut self, ot: TypePointer) -> (Vec<PossibleFunction>, u32) {
        let ot = self.map.find(ot);
        self.c_type(PointerForCType::from(ot));
        let mut fs = Vec::new();
        let type_map = &self.map.dereference_without_find(ot).type_map;
        let normals_len = type_map.len()
            - type_map
                .get(&TypeId::Intrinsic(IntrinsicTypeTag::Fn))
                .is_some() as usize;
        let ls = self.type_memo.get_lambda_ids_pointer(ot, &mut self.map);
        let ls_len = ls.len();
        let mut tag = normals_len as u32;
        for (index_in_type_map, lambda_id, ctx) in ls
            .iter()
            .map(|(l, (i, ctx))| (*i, *l, ctx.clone()))
            .collect_vec()
        {
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
                modifier: if normals_len == 0 && ls_len == 1 {
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
            fs.push(PossibleFunction {
                tag,
                lambda_id: id,
                c_type: CType {
                    i: StructId(ct),
                    boxed: false,
                },
                index_in_type_map,
                ctx,
            });
            tag += 1;
        }
        (fs, tag)
    }

    fn get_type(&mut self, p: PointerForCType) -> Option<Type> {
        match p.modifier {
            PointerModifier::Normal => {
                self.collect_box_points(p.p);
                let t = self.type_memo.get_type(p.p, &mut self.map);
                Some(t)
            }
            PointerModifier::UnionMember(_) => None,
            PointerModifier::Boxed => None,
        }
    }

    fn get_type_for_hash(&mut self, p: TypePointer) -> TypeForHash {
        self.collect_box_points(p);
        self.type_memo.get_type_for_hash(p, &mut self.map)
    }

    fn expr_to_variable(
        &mut self,
        e: Expr,
        t: PointerForCType,
        instructions: &mut Vec<Instruction>,
    ) -> LocalVariable {
        let d = self.new_variable(t);
        instructions.push(Instruction::Assign(d, e));
        d
    }

    fn add_tags_to_expr(
        &mut self,
        e: Expr,
        p: TypePointer,
        id: TypeId,
        instructions: &mut Vec<Instruction>,
    ) -> Expr {
        match self.get_tag_normal(p, id) {
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
        }
    }

    fn get_tag_normal(&mut self, ot: TypePointer, type_id: TypeId) -> GetTagNormalResult {
        debug_assert_ne!(type_id, TypeId::Intrinsic(IntrinsicTypeTag::Fn));
        let mut tag = 0;
        let mut result = None;
        let terminal = self.map.dereference(ot);
        let mut ids = terminal.type_map.keys();
        for id in &mut ids {
            if let TypeId::Intrinsic(IntrinsicTypeTag::Fn) = id {
                break;
            } else if *id == type_id {
                debug_assert!(result.is_none());
                result = Some(tag);
            }
            tag += 1;
        }
        debug_assert!(ids.next().is_none());
        match result {
            Some(tag_of_t) => {
                if tag == 1 && terminal.functions.is_empty() {
                    GetTagNormalResult::NotTagged
                } else {
                    GetTagNormalResult::Tagged(tag_of_t as u32)
                }
            }
            None => GetTagNormalResult::Impossible,
        }
    }

    pub fn c_type(&mut self, p: PointerForCType) -> CType {
        debug_assert_ne!(p.modifier, PointerModifier::Boxed);
        let p = self.normalizer_for_c_type.find(PointerForCType {
            p: self.map.find(p.p),
            ..p
        });
        if let Some(t) = self.c_type_memo.get(&p) {
            *t
        } else {
            debug_assert!(!self.normalizer_for_c_type.contains(p));
            self.collect_box_points(p.p);
            self.map.minimize(p.p);
            if let Some(t) = self.c_type_from_memo(p) {
                return CType {
                    i: StructId(t),
                    boxed: false,
                };
            }
            let mut partitions = Default::default();
            self.collect_pointers(p.p, &mut partitions);
            let c_type_schemes = partitions
                .keys()
                .map(|p| (*p, self.get_c_type_scheme_from_pointer(*p)))
                .collect();
            let (partitions, c_type_defs) = CTypeEnv(&c_type_schemes).split_partitions(partitions);
            let partition_rev: FxHashMap<_, _> = partitions.iter().map(|(k, v)| (*v, *k)).collect();
            let c_type_defs_rev: FxHashMap<_, _> =
                c_type_defs.iter().map(|(k, v)| (*v, k)).collect();
            for (t, p) in &partitions {
                debug_assert!(self.map.is_terminal(t.p));
                let r = partition_rev[p];
                debug_assert!(self.map.is_terminal(r.p));
                debug_assert_ne!(
                    self.map.dereference_without_find(t.p).box_point,
                    BoxPoint::NotSure
                );
                debug_assert_ne!(
                    self.map.dereference_without_find(r.p).box_point,
                    BoxPoint::NotSure
                );
                if *t != r {
                    self.normalizer_for_c_type.union(*t, r)
                }
            }
            let mut new_c_type_defs = Vec::new();
            for (g, t) in &partition_rev {
                let t = self.normalizer_for_c_type.find(*t);
                let for_hash = self.c_type_for_hash(t);
                if let Some(c_type) = self.c_type_memo_from_hash.get(&for_hash) {
                    self.c_type_memo.insert(
                        t,
                        CType {
                            i: StructId(c_type),
                            boxed: false,
                        },
                    );
                } else {
                    let c_type = self.c_type_memo_from_hash.get_or_insert(for_hash);
                    self.c_type_memo.insert(
                        t,
                        CType {
                            i: StructId(c_type),
                            boxed: false,
                        },
                    );
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
                    let boxed = a.boxed;
                    let a = partition_rev[&(a.i.0 as u32)];
                    let a = self.normalizer_for_c_type.find(a);
                    let for_hash = self.c_type_for_hash(a);
                    CType {
                        i: StructId(self.c_type_memo_from_hash.get(&for_hash).unwrap()),
                        boxed,
                    }
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

    fn c_type_for_hash(&mut self, p: PointerForCType) -> CTypeForHash {
        #[cfg(debug_assertions)]
        if self.map.minimize_types {
            let p = self.map.find(p.p);
            assert!(self.map.minimized_pointers.contains(&p))
        }
        match p.modifier {
            PointerModifier::Normal => self.c_type_for_hash_inner(p.p),
            PointerModifier::UnionMember(tag) => self.c_type_for_hash_inner_with_tag(p.p, tag),
            PointerModifier::Boxed => {
                let t = self.c_type_for_hash_inner(p.p);
                CTypeForHash(vec![CTypeForHashUnit::Ref(CTypeForHashInner::Type(t))])
            }
        }
    }

    fn c_type_from_memo(&self, p: PointerForCType) -> Option<usize> {
        #[cfg(debug_assertions)]
        if self.map.minimize_types {
            let p = self.map.find_imm(p.p);
            assert!(self.map.minimized_pointers.contains(&p))
        }
        match p.modifier {
            PointerModifier::Normal => self
                .c_type_for_hash_memo
                .get(&p.p)
                .and_then(|t| self.c_type_memo_from_hash.get(t)),
            PointerModifier::UnionMember(tag) => {
                let p = self.map.find_imm(p.p);
                let p = self
                    .normalizer_for_c_type
                    .find_imm(PointerForCType::from(p));
                debug_assert_eq!(p.modifier, PointerModifier::Normal);
                let p = p.p;
                self.c_type_for_hash_memo_with_tag
                    .get(&(p, tag))
                    .and_then(|t| self.c_type_memo_from_hash.get(t))
            }
            PointerModifier::Boxed => self.c_type_for_hash_memo.get(&p.p).and_then(|t| {
                let t = CTypeForHash(vec![CTypeForHashUnit::Ref(CTypeForHashInner::Type(
                    t.clone(),
                ))]);
                self.c_type_memo_from_hash.get(&t)
            }),
        }
    }

    fn collect_args(
        &mut self,
        args: &[TypePointer],
        boxing: &[Option<bool>],
        trace: &mut FxHashMap<TypePointer, u32>,
    ) -> Vec<CTypeForHashInner> {
        args.iter()
            .zip(boxing)
            .map(|(p, boxed)| {
                let t = self.c_type_for_hash_inner_aux(*p, trace);
                if boxed.unwrap() {
                    CTypeForHashInner::Type(CTypeForHash(vec![CTypeForHashUnit::Ref(t)]))
                } else {
                    t
                }
            })
            .collect()
    }

    fn collect_hash_unit(
        &mut self,
        p: TypePointer,
        boxing: &BTreeMap<TypeTagForBoxPoint, Vec<Option<bool>>>,
        ts: &mut Vec<CTypeForHashUnit>,
        trace: &mut FxHashMap<TypePointer, u32>,
    ) {
        let type_map = self.map.dereference_without_find(p).type_map.clone();
        for (type_id, args) in type_map {
            match type_id {
                TypeId::Intrinsic(tag) => match tag {
                    IntrinsicTypeTag::Ptr => ts.push(CTypeForHashUnit::Ptr),
                    IntrinsicTypeTag::I64 => ts.push(CTypeForHashUnit::I64),
                    IntrinsicTypeTag::U8 => ts.push(CTypeForHashUnit::U8),
                    IntrinsicTypeTag::Unit => ts.push(CTypeForHashUnit::Aggregate(Vec::new())),
                    IntrinsicTypeTag::Fn => {}
                    IntrinsicTypeTag::Mut => {
                        let t = self.c_type_for_hash_inner_aux(args[0], trace);
                        ts.push(CTypeForHashUnit::Ref(t));
                    }
                },
                TypeId::UserDefined(_) => {
                    let args = self.collect_args(
                        &args,
                        &boxing[&TypeTagForBoxPoint::Normal(type_id)],
                        trace,
                    );
                    ts.push(CTypeForHashUnit::Aggregate(args));
                }
            }
        }
        let ids = self.type_memo.get_lambda_ids_pointer(p, &mut self.map);
        for (index_in_type_map, args) in ids.values().cloned().collect_vec() {
            let args = self.collect_args(
                &args,
                &boxing[&TypeTagForBoxPoint::Lambda(index_in_type_map)],
                trace,
            );
            ts.push(CTypeForHashUnit::Aggregate(args));
        }
    }

    fn c_type_for_hash_inner_aux(
        &mut self,
        p: TypePointer,
        trace: &mut FxHashMap<TypePointer, u32>,
    ) -> CTypeForHashInner {
        let p = self.map.find(p);
        let p = self.normalizer_for_c_type.find(PointerForCType::from(p));
        debug_assert_eq!(p.modifier, PointerModifier::Normal);
        let p = p.p;
        let reference_point = self.map.dereference_without_find(p).box_point.clone();
        debug_assert_ne!(reference_point, BoxPoint::NotSure);
        if reference_point == BoxPoint::Diverging {
            return CTypeForHashInner::Type(CTypeForHash(vec![CTypeForHashUnit::Diverge]));
        }
        if let Some(d) = trace.get(&p) {
            return CTypeForHashInner::Index(trace.len() as u32 - *d - 1);
        }
        trace.insert(p, trace.len() as u32);
        let mut ts = Vec::new();
        let BoxPoint::Boxed(reference_point) = reference_point else {
            panic!()
        };
        self.collect_hash_unit(p, &reference_point, &mut ts, trace);
        let t = CTypeForHash(ts);
        CTypeForHashInner::Type(t)
    }

    fn c_type_for_hash_inner(&mut self, p: TypePointer) -> CTypeForHash {
        if let Some(t) = self.c_type_for_hash_memo.get(&p) {
            t.clone()
        } else {
            let CTypeForHashInner::Type(t) =
                self.c_type_for_hash_inner_aux(p, &mut Default::default())
            else {
                panic!()
            };
            self.c_type_for_hash_memo.insert(p, t.clone());
            t
        }
    }

    fn collect_hash_unit_with_tag(
        &mut self,
        p: TypePointer,
        boxing: &BTreeMap<TypeTagForBoxPoint, Vec<Option<bool>>>,
        trace: &mut FxHashMap<TypePointer, u32>,
        tag: usize,
    ) -> CTypeForHashUnit {
        let type_map = self.map.dereference_without_find(p).type_map.clone();
        if type_map.len()
            > tag + type_map.contains_key(&TypeId::Intrinsic(IntrinsicTypeTag::Fn)) as usize
        {
            let (type_id, args) = type_map.iter().nth(tag).unwrap();
            match type_id {
                TypeId::Intrinsic(tag) => match tag {
                    IntrinsicTypeTag::Ptr => CTypeForHashUnit::Ptr,
                    IntrinsicTypeTag::I64 => CTypeForHashUnit::I64,
                    IntrinsicTypeTag::U8 => CTypeForHashUnit::U8,
                    IntrinsicTypeTag::Unit => CTypeForHashUnit::Aggregate(Vec::new()),
                    IntrinsicTypeTag::Fn => panic!(),
                    IntrinsicTypeTag::Mut => {
                        let t = self.c_type_for_hash_inner_aux(args[0], trace);
                        CTypeForHashUnit::Ref(t)
                    }
                },
                TypeId::UserDefined(_) => {
                    let args = self.collect_args(
                        args,
                        &boxing[&TypeTagForBoxPoint::Normal(*type_id)],
                        trace,
                    );
                    CTypeForHashUnit::Aggregate(args)
                }
            }
        } else {
            let ids = self.type_memo.get_lambda_ids_pointer(p, &mut self.map);
            let (index_in_type_map, args) =
                ids.values().nth(tag + 1 - type_map.len()).unwrap().clone();
            let args = self.collect_args(
                &args,
                &boxing[&TypeTagForBoxPoint::Lambda(index_in_type_map)],
                trace,
            );
            CTypeForHashUnit::Aggregate(args)
        }
    }

    fn c_type_for_hash_inner_with_tag(&mut self, p: TypePointer, tag: u32) -> CTypeForHash {
        let p = self.map.find(p);
        let p = self.normalizer_for_c_type.find(PointerForCType::from(p));
        debug_assert_eq!(p.modifier, PointerModifier::Normal);
        let p = p.p;
        if let Some(t) = self.c_type_for_hash_memo_with_tag.get(&(p, tag)) {
            t.clone()
        } else {
            let reference_point = &self.map.dereference_without_find(p).box_point;
            let boxing = match reference_point {
                BoxPoint::Diverging => return CTypeForHash(vec![CTypeForHashUnit::Diverge]),
                BoxPoint::Boxed(boxing) => boxing.clone(),
                BoxPoint::NotSure => panic!(),
            };
            let t =
                self.collect_hash_unit_with_tag(p, &boxing, &mut Default::default(), tag as usize);
            let t = CTypeForHash(vec![t]);
            self.c_type_for_hash_memo_with_tag
                .insert((p, tag), t.clone());
            t
        }
    }

    pub fn get_c_type_scheme_from_pointer(
        &mut self,
        node: PointerForCType,
    ) -> CTypeScheme<PointerForCType> {
        debug_assert!(self.map.is_terminal(node.p));
        debug_assert_ne!(node.modifier, PointerModifier::Boxed);
        let reference_point = &self.map.dereference_without_find(node.p).box_point;
        let boxing = match reference_point {
            BoxPoint::Diverging => return CTypeScheme::Diverge,
            BoxPoint::Boxed(boxing) => boxing.clone(),
            BoxPoint::NotSure => panic!(),
        };
        let mut ts = Vec::new();
        let type_map = self.map.dereference(node.p).type_map.clone();
        for (id, args) in type_map {
            match id {
                TypeId::Intrinsic(tag) => match tag {
                    IntrinsicTypeTag::Ptr => ts.push(CTypeScheme::Ptr),
                    IntrinsicTypeTag::I64 => ts.push(CTypeScheme::I64),
                    IntrinsicTypeTag::U8 => ts.push(CTypeScheme::U8),
                    IntrinsicTypeTag::Unit => ts.push(CTypeScheme::Aggregate(Vec::new())),
                    IntrinsicTypeTag::Fn => (),
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
                            .zip(&boxing[&TypeTagForBoxPoint::Normal(id)])
                            .map(|(p, boxed)| {
                                let modifier = if boxed.unwrap() {
                                    PointerModifier::Boxed
                                } else {
                                    PointerModifier::Normal
                                };
                                PointerForCType {
                                    p: self.map.find_imm(p),
                                    modifier,
                                }
                            })
                            .collect(),
                    ));
                }
            }
        }
        let ids = self.type_memo.get_lambda_ids_pointer(node.p, &mut self.map);
        for (index_in_type_map, args) in ids.values() {
            ts.push(CTypeScheme::Aggregate(
                args.iter()
                    .copied()
                    .zip(&boxing[&TypeTagForBoxPoint::Lambda(*index_in_type_map)])
                    .map(|(p, boxed)| {
                        let modifier = if boxed.unwrap() {
                            PointerModifier::Boxed
                        } else {
                            PointerModifier::Normal
                        };
                        PointerForCType {
                            p: self.map.find_imm(p),
                            modifier,
                        }
                    })
                    .collect(),
            ));
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

    pub fn collect_box_points(&mut self, p: TypePointer) {
        self.collect_box_points_aux(
            p,
            None,
            &mut Default::default(),
            &mut Vec::with_capacity(5),
            None,
        )
    }

    fn collect_pointers(&mut self, p: TypePointer, pointers: &mut FxHashMap<PointerForCType, u32>) {
        let p = self.map.find_imm(p);
        let contains = pointers.insert(PointerForCType::from(p), 0).is_some();
        if contains {
            return;
        }
        let terminal = self.map.dereference_without_find(p);
        let mut tag = 0;
        let mut add_args = |slf: &mut Env<'_, '_>, args: &[TypePointer]| {
            for t in args {
                slf.collect_pointers(*t, pointers);
            }
            tag += 1;
        };
        for (id, args) in terminal.type_map.clone() {
            match id {
                TypeId::Intrinsic(IntrinsicTypeTag::Fn) => {}
                _ => {
                    add_args(self, &args);
                }
            }
        }
        for (_, ctx) in self
            .type_memo
            .get_lambda_ids_pointer(p, &mut self.map)
            .values()
            .cloned()
            .collect_vec()
        {
            add_args(self, &ctx);
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

    fn collect_box_points_aux(
        &mut self,
        p: TypePointer,
        parent_of_p: Option<(TypePointer, TypeTagForBoxPoint, u32)>,
        trace_map: &mut FxHashSet<TypePointer>,
        non_union_trace: &mut Vec<TypePointer>,
        mut divergent_stopper: Option<DivergentStopper>,
    ) {
        let p = self.map.find_imm(p);
        if let Some((p, i, j)) = parent_of_p {
            let t = self.map.dereference_without_find(p);
            if let BoxPoint::Boxed(b) = &t.box_point {
                if b[&i][j as usize].is_some() {
                    return;
                }
            }
        }
        let terminal = self.map.dereference_without_find_mut(p);
        if terminal.box_point == BoxPoint::NotSure {
            let mut pss: BTreeMap<_, _> = terminal
                .type_map
                .iter()
                .map(|(id, fields)| {
                    (
                        TypeTagForBoxPoint::Normal(*id),
                        fields.iter().map(|_| None).collect_vec(),
                    )
                })
                .collect();
            for (i, (_, args)) in terminal.functions.iter().enumerate() {
                let o = pss.insert(
                    TypeTagForBoxPoint::Lambda(i as u32),
                    args.iter().map(|_| None).collect_vec(),
                );
                debug_assert!(o.is_none());
            }
            terminal.box_point = BoxPoint::Boxed(pss)
        }
        let type_map = terminal.type_map.clone();
        let functions = terminal.functions.clone();
        let normal_len = type_map.len()
            - type_map
                .get(&TypeId::Intrinsic(IntrinsicTypeTag::Fn))
                .is_some() as usize;
        let ids: FxHashSet<_> = functions.iter().map(|(l, _)| l.id).collect();
        let is_union = normal_len + ids.len() > 1;
        if is_union {
            if let Some((p, union_index, field)) = parent_of_p {
                divergent_stopper = Some(DivergentStopper::Union {
                    p,
                    union_index,
                    field,
                });
            }
        }
        if trace_map.contains(&p) {
            if non_union_trace.contains(&p) {
                for u in non_union_trace {
                    self.map.dereference_without_find_mut(*u).box_point = BoxPoint::Diverging;
                }
            } else if let DivergentStopper::Union {
                p,
                union_index,
                field,
            } = divergent_stopper.unwrap()
            {
                let terminal = self.map.dereference_without_find_mut(p);
                let BoxPoint::Boxed(pss) = &mut terminal.box_point else {
                    panic!()
                };
                pss.get_mut(&union_index).unwrap()[field as usize] = Some(true);
            }
            if let Some((p, i, j)) = parent_of_p {
                let t = self.map.dereference_without_find_mut(p);
                if let BoxPoint::Boxed(b) = &mut t.box_point {
                    b.get_mut(&i).unwrap()[j as usize].get_or_insert(false);
                }
            }
            return;
        }
        let mut new_trace;
        let non_union_trace = if is_union {
            new_trace = Vec::new();
            &mut new_trace
        } else {
            non_union_trace.push(p);
            non_union_trace
        };
        trace_map.insert(p);
        for (id, ts) in type_map {
            match id {
                TypeId::Intrinsic(_) => {
                    for (j, t) in ts.into_iter().enumerate() {
                        self.collect_box_points_aux(
                            t,
                            Some((p, TypeTagForBoxPoint::Normal(id), j as u32)),
                            trace_map,
                            &mut Vec::new(),
                            Some(DivergentStopper::Indirect),
                        );
                        #[cfg(debug_assertions)]
                        if let BoxPoint::Boxed(b) = &self.map.dereference_without_find(p).box_point
                        {
                            assert!(b[&TypeTagForBoxPoint::Normal(id)][j].is_some())
                        }
                    }
                }
                TypeId::UserDefined(_) => {
                    for (j, t) in ts.into_iter().enumerate() {
                        self.collect_box_points_aux(
                            t,
                            Some((p, TypeTagForBoxPoint::Normal(id), j as u32)),
                            trace_map,
                            non_union_trace,
                            divergent_stopper,
                        );
                    }
                }
            }
        }
        for (i, (l, args)) in functions.into_iter().enumerate() {
            self.collect_box_points_aux(
                l.root_t,
                None,
                trace_map,
                &mut Vec::new(),
                Some(DivergentStopper::Indirect),
            );
            for (j, t) in args.iter().enumerate() {
                self.collect_box_points_aux(
                    *t,
                    Some((p, TypeTagForBoxPoint::Lambda(i as u32), j as u32)),
                    trace_map,
                    non_union_trace,
                    divergent_stopper,
                );
            }
        }
        if !is_union {
            non_union_trace.pop().unwrap();
        }
        trace_map.remove(&p);
        if let Some((p, i, j)) = parent_of_p {
            let t = self.map.dereference_without_find_mut(p);
            if let BoxPoint::Boxed(b) = &mut t.box_point {
                b.get_mut(&i).unwrap()[j as usize].get_or_insert(false);
            }
        }
    }
}

#[derive(Debug, Clone)]
struct PossibleFunction {
    tag: u32,
    lambda_id: FxLambdaId,
    index_in_type_map: u32,
    c_type: CType,
    ctx: Vec<TypePointer>,
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

#[derive(Debug, Clone, Copy)]
enum DivergentStopper {
    Indirect,
    Union {
        p: TypePointer,
        union_index: TypeTagForBoxPoint,
        field: u32,
    },
}

impl From<LocalVariable> for VariableId {
    fn from(value: LocalVariable) -> Self {
        Self::Local(value)
    }
}
