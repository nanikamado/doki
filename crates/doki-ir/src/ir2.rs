pub mod c_type;
mod intrinsic_debug;
mod local_variable;
mod type_converter;
mod type_memo;
mod union_find;

use self::c_type::{CTypeEnv, CTypeScheme, PointerForCType};
pub use self::intrinsic_debug::PrinterCollector;
pub use self::local_variable::{LocalVariable, LocalVariableCollector};
use self::type_converter::ConverterCollector;
pub use self::type_converter::{ConvertOp, ConvertOpRef, UnionOp};
use self::type_memo::TypeMemo;
pub use self::type_memo::{DisplayTypeWithEnvStruct, DisplayTypeWithEnvStructOption, Type};
use self::union_find::UnionFind;
use crate::intrinsics::{IntrinsicTypeTag, IntrinsicVariable};
use crate::ir1::{
    self, ConstructorNames, GlobalVariable, LambdaId, LocalVariableTypes, PaddedTypeMap,
    ReplaceMap, TypeId, TypePointer,
};
use crate::ir2::c_type::PointerModifier;
use crate::util::collector::Collector;
use crate::util::dfa_minimization::Dfa;
use crate::util::id_generator;
use crate::CodegenOptions;
use itertools::Itertools;
use petgraph::algo::find_negative_cycle;
use petgraph::graph::NodeIndex;
use petgraph::Graph;
use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::fmt::{Debug, Display};
use std::iter::once;

#[derive(Debug)]
pub struct Ast<'a> {
    pub original_variables: FxHashMap<GlobalVariableId, VariableDecl<'a>>,
    pub original_variable_usage: FxHashMap<GlobalVariableId, bool>,
    pub cloned_variables: FxHashMap<GlobalVariableId, ClonedVariable<'a>>,
    pub original_variables_map: FxHashMap<GlobalVariable, (GlobalVariableId, TypePointer)>,
    pub entry_block: FunctionBody,
    pub entry_block_ret_t: CType,
    pub functions: Vec<Function>,
    pub variable_types: LocalVariableCollector<Types>,
    pub constructor_names: ConstructorNames,
    pub local_variable_replace_map: FxHashMap<(ir1::LocalVariable, Root), LocalVariable>,
    pub used_intrinsic_variables: Collector<(IntrinsicVariable, Vec<CType>, CType)>,
    pub printer_collector: PrinterCollector,
    pub printer_c_type: FxHashMap<TypePointer, CType>,
    pub c_type_definitions: Vec<CTypeScheme<CType>>,
    pub codegen_options: CodegenOptions,
    pub type_converter: FxHashMap<(TypePointer, TypePointer), TypeConverter>,
}

#[derive(Debug)]
pub struct Types {
    pub type_for_display: Option<Type>,
    pub c_type: CType,
    type_pointer: Option<TypePointer>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct StructId(pub usize);

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct CType {
    pub i: StructId,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct GlobalVariableId(usize);

#[derive(Debug, PartialEq, Clone)]
pub struct VariableDecl<'a> {
    pub name: &'a str,
    pub value: FunctionBody,
    pub original_decl_id: GlobalVariable,
    pub c_t: CType,
    pub type_: Type,
    pub root_t: Root,
}

#[derive(Debug, PartialEq, Clone)]
pub struct ClonedVariable<'a> {
    pub name: &'a str,
    pub original_decl_id: GlobalVariable,
    pub c_t: CType,
    pub converter: u32,
    pub type_: Type,
    pub root_t: Root,
}

#[derive(Debug, PartialEq, Clone)]
pub struct OriginalVariableDecl {
    pub value: FunctionBody,
    p: TypePointer,
    pub c_t: CType,
}

#[derive(Debug, PartialEq, Clone)]
pub struct FunctionBody {
    pub basic_blocks: Vec<BasicBlock>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct BasicBlock {
    pub instructions: Vec<Instruction>,
    pub end_instruction: EndInstruction,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Tester {
    Tag { tag: u32 },
    I64 { value: i64 },
}

#[derive(Debug, PartialEq, Clone)]
pub enum Instruction {
    Assign(LocalVariable, Expr),
    Test {
        tester: Tester,
        operand: LocalVariable,
        catch_label: usize,
    },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum EndInstruction {
    Ret(LocalVariable),
    Goto { label: usize },
    Panic { msg: String },
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    I64(i64),
    F64(f64),
    U8(u8),
    Str(String),
    GlobalIdent(GlobalVariableId),
    LocalIdent(LocalVariable),
    Call {
        args: Vec<LocalVariable>,
        f: FxLambdaId,
        tail_call: RefCell<bool>,
        span: String,
    },
    BasicCall {
        args: Vec<LocalVariable>,
        id: BasicFunction,
    },
    Upcast {
        tag: u32,
        value: LocalVariable,
    },
    Downcast {
        tag: u32,
        value: LocalVariable,
        check: bool,
        boxed: bool,
    },
}

#[derive(Debug, PartialEq, Clone, Copy, Eq)]
pub enum BasicFunction {
    Intrinsic { v: IntrinsicVariable, id: u32 },
    DebugPrint { p: TypePointer },
    Construction,
    FieldAccessor { field: u32 },
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
    pub ret: LocalVariable,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeConverter {
    pub id: u32,
    pub op: ConvertOp,
    pub c_type_from: CType,
    pub c_type_to: CType,
}

impl<'a> Ast<'a> {
    pub fn from(ast: ir1::Ast<'a>) -> Self {
        let variable_decls = ast.variable_decls.iter().map(|d| (d.decl_id, d)).collect();
        let mut memo = Env::new(
            variable_decls,
            ast.local_variable_types,
            ast.type_map,
            ast.constructor_names,
        );
        let original_variables_map = memo.collect_original_global_variables();
        let (entry_block, entry_block_ret_t) = {
            let mut replace_map = Default::default();
            let ir1::Instruction::Assign(ret, _) = ast.entry_block.instructions.last().unwrap()
            else {
                panic!()
            };
            let p = memo.map.new_pointer();
            let t = memo.get_type_for_hash(p);
            let type_id = memo.type_memo.type_id_generator.get_or_insert(t);
            let (basic_blocks, ret) =
                memo.function_body(&ast.entry_block, type_id, &mut replace_map, *ret, false);
            let t = memo.local_variable_collector.get_type(ret);
            (FunctionBody { basic_blocks }, t.c_type)
        };
        let mut type_converter = type_converter::ConverterCollector::new();
        while let Some(j) = memo.job_stack.pop() {
            memo.handle_stack(j, &original_variables_map, &mut type_converter);
        }
        let type_converter = type_converter
            .into_inner()
            .into_iter()
            .map(|((a, b), c)| {
                (
                    (a, b),
                    TypeConverter {
                        id: c.id,
                        op: c.op,
                        c_type_from: memo.c_type(PointerForCType::from(a)),
                        c_type_to: memo.c_type(PointerForCType::from(b)),
                    },
                )
            })
            .collect();
        let printer_c_type = memo
            .printer_collector
            .inner()
            .keys()
            .copied()
            .collect_vec()
            .into_iter()
            .map(|p| (p, memo.c_type(PointerForCType::from(p))))
            .collect();
        let functions = memo
            .functions
            .into_values()
            .flat_map(|f| match f {
                FunctionEntry::Placeholder(e) => {
                    if let Some((ret, parameters)) = memo.fn_signatures_for_dummy_fns.remove(&e) {
                        // this function is only called from unreachable code which is not deleted
                        let basic_blocks = vec![BasicBlock {
                            instructions: Vec::new(),
                            end_instruction: EndInstruction::Panic {
                                msg: "unexpected".to_string(),
                            },
                        }];
                        Some(Function {
                            id: e,
                            parameters,
                            body: FunctionBody { basic_blocks },
                            ret,
                        })
                    } else {
                        // this function is only called from unreachable code which is not deleted
                        None
                    }
                }
                FunctionEntry::Function(f) => Some(f),
            })
            .collect();
        Self {
            original_variables: memo.original_variables,
            original_variable_usage: memo.original_variable_usage,
            cloned_variables: memo.cloned_variables,
            original_variables_map,
            entry_block,
            entry_block_ret_t,
            functions,
            variable_types: memo.local_variable_collector,
            constructor_names: memo.constructor_names,
            local_variable_replace_map: memo.local_variable_replace_map,
            used_intrinsic_variables: memo.used_intrinsic_variables,
            c_type_definitions: memo.c_type_definitions,
            codegen_options: ast.codegen_options,
            type_converter,
            printer_collector: memo.printer_collector,
            printer_c_type,
        }
    }
}

struct Env<'a, 'b> {
    variable_decls: FxHashMap<GlobalVariable, &'b ir1::VariableDecl<'a>>,
    monomorphized_variable_map: FxHashMap<(ir1::GlobalVariable, Root), GlobalVariableId>,
    original_variables: FxHashMap<GlobalVariableId, VariableDecl<'a>>,
    original_variable_usage: FxHashMap<GlobalVariableId, bool>,
    cloned_variables: FxHashMap<GlobalVariableId, ClonedVariable<'a>>,
    map: PaddedTypeMap,
    functions: FxHashMap<(LambdaId, Vec<Type>), FunctionEntry>,
    type_memo: TypeMemo,
    local_variable_types_old: LocalVariableTypes,
    local_variable_replace_map: FxHashMap<(ir1::LocalVariable, Root), LocalVariable>,
    local_variable_collector: LocalVariableCollector<Types>,
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
    fn_signatures_for_dummy_fns: FxHashMap<FxLambdaId, (LocalVariable, Vec<LocalVariable>)>,
    printer_collector: PrinterCollector,
}

struct Job {
    original_decl_id: GlobalVariable,
    root_t: Root,
    decl_id: GlobalVariableId,
    p: TypePointer,
    t_for_hash: Type,
    replace_map: ReplaceMap,
    cloned: bool,
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
type Root = TypeUnique;

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
        variable_decls: FxHashMap<GlobalVariable, &'b ir1::VariableDecl<'a>>,
        local_variable_types: LocalVariableTypes,
        map: PaddedTypeMap,
        constructor_names: ConstructorNames,
    ) -> Self {
        let mut c_type_memo_from_hash: Collector<_> = Default::default();
        c_type_memo_from_hash.get_or_insert(CTypeForHash(vec![(
            CTypeForHashUnit::Aggregate(Vec::new()),
            false,
        )]));
        let c_type_definitions = vec![CTypeScheme::Aggregate(Vec::new())];
        Env {
            variable_decls,
            monomorphized_variable_map: Default::default(),
            original_variables: Default::default(),
            original_variable_usage: Default::default(),
            cloned_variables: Default::default(),
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
            fn_signatures_for_dummy_fns: Default::default(),
            printer_collector: Default::default(),
        }
    }

    fn monomorphize_decl(
        &mut self,
        decl_id: GlobalVariable,
        p: TypePointer,
        replace_map: ReplaceMap,
    ) -> GlobalVariableId {
        debug_assert!(self.map.is_terminal(p));
        let t_for_hash = self.get_type_for_hash(p);
        let root_t = self
            .type_memo
            .type_id_generator
            .get_or_insert(t_for_hash.clone());
        let k = (decl_id, root_t);
        if let Some(d) = self.monomorphized_variable_map.get(&k) {
            if self.original_variable_usage.contains_key(d) {
                self.original_variable_usage.insert(*d, true);
            }
            *d
        } else {
            let new_decl_id = GlobalVariableId(self.global_variable_count);
            self.global_variable_count += 1;
            self.monomorphized_variable_map.insert(k, new_decl_id);
            self.job_stack.push(Job {
                original_decl_id: decl_id,
                root_t,
                decl_id: new_decl_id,
                p,
                t_for_hash,
                replace_map,
                cloned: true,
            });
            new_decl_id
        }
    }

    fn monomorphize_original_decl(
        &mut self,
        decl_id: GlobalVariable,
        p: TypePointer,
        replace_map: ReplaceMap,
    ) -> GlobalVariableId {
        debug_assert!(self.map.is_terminal(p));
        let t_for_hash = self.get_type_for_hash(p);
        let root_t = self
            .type_memo
            .type_id_generator
            .get_or_insert(t_for_hash.clone());
        let k = (decl_id, root_t);
        let new_decl_id = GlobalVariableId(self.global_variable_count);
        self.global_variable_count += 1;
        let o = self.monomorphized_variable_map.insert(k, new_decl_id);
        debug_assert!(o.is_none());
        self.job_stack.push(Job {
            original_decl_id: decl_id,
            root_t,
            decl_id: new_decl_id,
            p,
            t_for_hash,
            replace_map,
            cloned: false,
        });
        let o = self.original_variable_usage.insert(new_decl_id, false);
        debug_assert!(o.is_none());
        new_decl_id
    }

    fn handle_stack(
        &mut self,
        mut j: Job,
        original_variables: &FxHashMap<GlobalVariable, (GlobalVariableId, TypePointer)>,
        type_converter: &mut ConverterCollector,
    ) {
        let d = *self.variable_decls.get(&j.original_decl_id).unwrap();
        j.p = self.map.find(j.p);
        let (instructions, _) =
            self.function_body(&d.value, j.root_t, &mut j.replace_map, d.ret, j.cloned);
        let p = PointerForCType::from(j.p);
        if j.cloned {
            let converter = type_converter.add(original_variables[&d.decl_id].1, j.p, self);
            let d = ClonedVariable {
                original_decl_id: j.original_decl_id,
                name: d.name,
                c_t: self.c_type(p),
                converter,
                type_: j.t_for_hash,
                root_t: j.root_t,
            };
            self.cloned_variables.insert(j.decl_id, d);
        } else {
            let d = VariableDecl {
                value: FunctionBody {
                    basic_blocks: instructions,
                },
                original_decl_id: j.original_decl_id,
                name: d.name,
                c_t: self.c_type(p),
                type_: j.t_for_hash,
                root_t: j.root_t,
            };
            self.original_variables.insert(j.decl_id, d);
        }
    }

    fn collect_original_global_variables(
        &mut self,
    ) -> FxHashMap<GlobalVariable, (GlobalVariableId, TypePointer)> {
        let mut vs =
            FxHashMap::with_capacity_and_hasher(self.variable_decls.len(), Default::default());
        let vs_original = self.variable_decls.values().copied().collect_vec();
        for d in vs_original {
            let mut replace_map = Default::default();
            let p = self.local_variable_types_old.get(d.ret);
            let p = self.map.clone_pointer(p, &mut replace_map);
            let new_id = self.monomorphize_original_decl(d.decl_id, p, replace_map);
            vs.insert(d.decl_id, (new_id, p));
        }
        vs
    }

    fn new_variable(&mut self, p: PointerForCType) -> LocalVariable {
        let ct = self.c_type(p);
        let t = self.get_type(p);
        self.local_variable_collector.new_variable(Types {
            type_for_display: t,
            c_type: ct,
            type_pointer: if p.modifier == PointerModifier::Normal {
                Some(p.p)
            } else {
                None
            },
        })
    }

    fn local_variable_def_replace(
        &mut self,
        v: ir1::LocalVariable,
        root_t: Root,
        replace_map: &mut ReplaceMap,
    ) -> (LocalVariable, TypePointer) {
        debug_assert!(!self.local_variable_replace_map.contains_key(&(v, root_t)));
        let t = self.local_variable_types_old.get(v);
        let t = self.map.clone_pointer(t, replace_map);
        let new_v = self.new_variable(PointerForCType::from(t));
        self.local_variable_replace_map.insert((v, root_t), new_v);
        (new_v, t)
    }

    fn get_defined_local_variable(&self, v: ir1::LocalVariable, root_t: Root) -> LocalVariable {
        *self.local_variable_replace_map.get(&(v, root_t)).unwrap()
    }

    fn block(
        &mut self,
        block: &ir1::Block,
        catch_label: Option<usize>,
        root_t: Root,
        replace_map: &mut ReplaceMap,
        basic_block_env: &mut BasicBlockEnv,
        only_fn: bool,
    ) -> Result<(), EndInstruction> {
        for i in &block.instructions {
            self.instruction(
                i,
                catch_label,
                root_t,
                replace_map,
                basic_block_env,
                only_fn,
            )?;
        }
        Ok(())
    }
}

impl<'a, 'b> Env<'a, 'b> {
    fn function_body(
        &mut self,
        block: &ir1::Block,
        root_t: Root,
        replace_map: &mut ReplaceMap,
        ret: ir1::LocalVariable,
        only_fn: bool,
    ) -> (Vec<BasicBlock>, LocalVariable) {
        let mut block_env = BasicBlockEnv {
            basic_blocks: vec![None],
            instructions: Vec::new(),
            current_basic_block: Some(0),
        };
        let (end, ret) = if let Err(end) =
            self.block(block, None, root_t, replace_map, &mut block_env, only_fn)
        {
            let t = self.local_variable_types_old.get(ret);
            let t = self.map.clone_pointer(t, replace_map);
            let ret = self.new_variable(PointerForCType::from(t));
            (end, ret)
        } else {
            let ret = self.get_defined_local_variable(ret, root_t);
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

    fn dummy_function_body(&mut self, ret_p: TypePointer) -> (Vec<BasicBlock>, LocalVariable) {
        let ret = self.new_variable(PointerForCType::from(ret_p));
        (
            vec![BasicBlock {
                instructions: Vec::new(),
                end_instruction: EndInstruction::Panic {
                    msg: "unexpected".to_string(),
                },
            }],
            ret,
        )
    }

    fn instruction(
        &mut self,
        instruction: &ir1::Instruction,
        catch_label: Option<usize>,
        root_t: Root,
        replace_map: &mut ReplaceMap,
        basic_block_env: &mut BasicBlockEnv,
        only_fn: bool,
    ) -> Result<(), EndInstruction> {
        if only_fn && matches!(instruction, ir1::Instruction::Test(_, _)) {
            return Ok(());
        }
        match instruction {
            ir1::Instruction::Assign(v, e) => {
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
                let e = self.expr(e, p, new_v, root_t, replace_map, basic_block_env, only_fn);
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
            ir1::Instruction::Test(ir1::Tester::I64 { value }, l) => {
                let catch_label = catch_label.unwrap();
                let type_id = TypeId::Intrinsic(IntrinsicTypeTag::I64);
                let p = self
                    .map
                    .clone_pointer(self.local_variable_types_old.get(*l), replace_map);
                let a = self.downcast(
                    *l,
                    p,
                    root_t,
                    type_id,
                    &mut basic_block_env.instructions,
                    Some(catch_label),
                );
                match a {
                    Ok(operand) => {
                        basic_block_env.instructions.push(Instruction::Test {
                            tester: Tester::I64 { value: *value },
                            operand,
                            catch_label,
                        });
                        Ok(())
                    }
                    Err(_) => Err(EndInstruction::Goto { label: catch_label }),
                }
            }
            ir1::Instruction::Test(ir1::Tester::Constructor { id }, a) => {
                let catch_label = catch_label.unwrap();
                let p = self
                    .map
                    .clone_pointer(self.local_variable_types_old.get(*a), replace_map);
                let operand = self.get_defined_local_variable(*a, root_t);
                match self.get_tag_normal(p, *id) {
                    GetTagNormalResult::Tagged { tag, boxed: _ } => {
                        basic_block_env.instructions.push(Instruction::Test {
                            tester: Tester::Tag { tag },
                            operand,
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
            ir1::Instruction::TryCatch(a, b) => {
                let catch = basic_block_env.new_label();
                let mut next = None;
                let end_instruction = if let Err(end) = self.block(
                    a,
                    Some(catch),
                    root_t,
                    replace_map,
                    basic_block_env,
                    only_fn,
                ) {
                    end
                } else {
                    let l = basic_block_env.new_label();
                    next = Some(l);
                    EndInstruction::Goto { label: l }
                };
                basic_block_env.end_current_block(end_instruction);
                basic_block_env.current_basic_block = Some(catch);
                let end_instruction = if let Err(end) = self.block(
                    b,
                    catch_label,
                    root_t,
                    replace_map,
                    basic_block_env,
                    only_fn,
                ) {
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
            ir1::Instruction::FailTest => Err(EndInstruction::Goto {
                label: catch_label.unwrap(),
            }),
            ir1::Instruction::Panic { msg } => Err(EndInstruction::Panic { msg: msg.clone() }),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn downcast(
        &mut self,
        a: ir1::LocalVariable,
        p: TypePointer,
        root_t: Root,
        type_id: TypeId,
        instructions: &mut Vec<Instruction>,
        catch_label: Option<usize>,
    ) -> Result<LocalVariable, String> {
        let a = self.get_defined_local_variable(a, root_t);
        match self.get_tag_normal(p, type_id) {
            GetTagNormalResult::Tagged { tag, boxed } => {
                if let Some(catch_label) = catch_label {
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
                        check: catch_label.is_none(),
                        boxed,
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

    #[allow(clippy::too_many_arguments)]
    fn fn_call(
        &mut self,
        v: LocalVariable,
        f: PossibleFunction,
        a: LocalVariable,
        ctx: LocalVariable,
        span: &str,
        basic_block_env: &mut BasicBlockEnv,
    ) {
        use Expr::*;
        let mut args = vec![a];
        for (i, c) in f.ctx.iter().enumerate() {
            let l = self.new_variable(PointerForCType::from(*c));
            basic_block_env.assign(
                l,
                BasicCall {
                    args: vec![ctx],
                    id: BasicFunction::FieldAccessor { field: i as u32 },
                },
            );
            args.push(l);
        }
        self.fn_signatures_for_dummy_fns
            .entry(f.lambda_id)
            .or_insert_with(|| (v, args.clone()));
        basic_block_env.assign(
            v,
            Call {
                args,
                f: f.lambda_id,
                tail_call: RefCell::new(false),
                span: span.to_string(),
            },
        )
    }

    #[allow(clippy::too_many_arguments)]
    /// Returns `Err` if type error
    fn expr(
        &mut self,
        e: &ir1::Expr,
        p: TypePointer,
        v: LocalVariable,
        root_t: Root,
        replace_map: &mut ReplaceMap,
        basic_block_env: &mut BasicBlockEnv,
        only_fn: bool,
    ) -> Result<(), String> {
        use Expr::*;
        if only_fn && !matches!(e, ir1::Expr::Lambda { .. } | ir1::Expr::GlobalIdent(..)) {
            return Ok(());
        }
        match e {
            ir1::Expr::Lambda {
                lambda_id,
                parameter,
                body,
                ret,
                context,
            } => {
                let (new_parameter, parameter_p) =
                    self.local_variable_def_replace(*parameter, root_t, replace_map);
                let parameter_t = self.get_type_for_hash(parameter_p);
                let ret_p = self.local_variable_types_old.get(*ret);
                let ret_p = self.map.clone_pointer(ret_p, replace_map);
                let ret_t = self.get_type_for_hash(ret_p);
                let mut parameters = context
                    .iter()
                    .map(|l| self.get_defined_local_variable(*l, root_t))
                    .collect_vec();
                let lambda_id_with_ctx = (
                    *lambda_id,
                    once(parameter_t)
                        .chain(once(ret_t))
                        .chain(parameters.iter().map(|a| {
                            let t = self.local_variable_collector.get_type(*a);
                            self.get_type_for_hash(t.type_pointer.unwrap())
                        }))
                        .collect_vec(),
                );
                if !only_fn {
                    let type_id = TypeId::Function(*lambda_id);
                    let l = BasicCall {
                        args: parameters.clone(),
                        id: BasicFunction::Construction,
                    };
                    let e = self.add_tags_to_expr(l, p, type_id, &mut basic_block_env.instructions);
                    basic_block_env.assign(v, e);
                }
                let e = if let Some(e) = self.functions.get(&lambda_id_with_ctx) {
                    e
                } else {
                    let e = FunctionEntry::Placeholder(FxLambdaId(self.functions.len() as u32));
                    self.functions
                        .entry(lambda_id_with_ctx.clone())
                        .or_insert(e)
                };
                if let FunctionEntry::Placeholder(fx_lambda_id) = *e {
                    parameters.insert(0, new_parameter);
                    let parameter_t = self.local_variable_collector.get_type(new_parameter);
                    let parameter_ct = &self.c_type_definitions[parameter_t.c_type.i.0];
                    let (basic_blocks, ret) = if matches!(parameter_ct, CTypeScheme::Diverge) {
                        self.dummy_function_body(ret_p)
                    } else {
                        self.function_body(body, root_t, replace_map, *ret, false)
                    };
                    let o = self.functions.insert(
                        lambda_id_with_ctx,
                        FunctionEntry::Function(Function {
                            id: fx_lambda_id,
                            parameters,
                            body: FunctionBody { basic_blocks },
                            ret,
                        }),
                    );
                    debug_assert!(matches!(o.unwrap(), FunctionEntry::Placeholder(_)));
                };
            }
            ir1::Expr::I64(s) => {
                let e = self.add_tags_to_expr(
                    I64(*s),
                    p,
                    TypeId::Intrinsic(IntrinsicTypeTag::I64),
                    &mut basic_block_env.instructions,
                );
                basic_block_env.assign(v, e)
            }
            ir1::Expr::U8(s) => {
                let e = self.add_tags_to_expr(
                    U8(*s),
                    p,
                    TypeId::Intrinsic(IntrinsicTypeTag::U8),
                    &mut basic_block_env.instructions,
                );
                basic_block_env.assign(v, e)
            }
            ir1::Expr::F64(s) => {
                let e = self.add_tags_to_expr(
                    F64(*s),
                    p,
                    TypeId::Intrinsic(IntrinsicTypeTag::F64),
                    &mut basic_block_env.instructions,
                );
                basic_block_env.assign(v, e)
            }
            ir1::Expr::Str(s) => {
                let e = self.add_tags_to_expr(
                    Str(s.clone()),
                    p,
                    TypeId::Intrinsic(IntrinsicTypeTag::Ptr),
                    &mut basic_block_env.instructions,
                );
                basic_block_env.assign(v, e)
            }
            ir1::Expr::LocalIdent(d) => {
                let l = self.get_defined_local_variable(*d, root_t);
                basic_block_env.assign(v, LocalIdent(l));
            }
            ir1::Expr::GlobalIdent(d, r, p) => {
                let p1 = self.map.clone_pointer(*p, replace_map);
                let r = replace_map.clone().merge(r, &mut self.map);
                #[cfg(debug_assertions)]
                let mut r = r;
                #[cfg(debug_assertions)]
                {
                    let p2 = self.map.clone_pointer(*p, &mut r);
                    assert_eq!(p1, p2);
                }
                let l = self.monomorphize_decl(*d, p1, r);
                basic_block_env.assign(v, GlobalIdent(l));
            }
            ir1::Expr::Call { f, a, err_msg } => {
                let f_t = self.local_variable_types_old.get(*f);
                let f_t_p = self.map.clone_pointer(f_t, replace_map);
                let (possible_functions, tag_len) = self.get_possible_functions(f_t_p);
                let f = self.get_defined_local_variable(*f, root_t);
                let a = self.get_defined_local_variable(*a, root_t);
                if possible_functions.is_empty() {
                    return Err(format!("not a function\n{err_msg}"));
                }
                if possible_functions.len() == 1 && tag_len == 1 {
                    let possible_function = possible_functions[0].clone();
                    self.fn_call(v, possible_function, a, f, err_msg, basic_block_env);
                } else {
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
                        let new_f = self.local_variable_collector.new_variable(Types {
                            type_for_display: None,
                            c_type: possible_function.c_type,
                            type_pointer: None,
                        });
                        basic_block_env.instructions.push(Instruction::Assign(
                            new_f,
                            Downcast {
                                tag: possible_function.tag,
                                value: f,
                                check: false,
                                boxed: possible_function.boxed,
                            },
                        ));
                        self.fn_call(v, possible_function, a, new_f, err_msg, basic_block_env);
                        basic_block_env.end_current_block(EndInstruction::Goto { label: skip });
                        basic_block_env.current_basic_block = Some(next);
                    }
                    basic_block_env.end_current_block(EndInstruction::Panic {
                        msg: format!("not a function\n{err_msg}"),
                    });
                    basic_block_env.current_basic_block = Some(skip);
                }
            }
            ir1::Expr::BasicCall {
                args,
                id: ir1::BasicFunction::Construction(id),
            } => {
                let type_id = TypeId::UserDefined(*id);
                let args = args
                    .iter()
                    .map(|a| *self.local_variable_replace_map.get(&(*a, root_t)).unwrap())
                    .collect();
                let l = BasicCall {
                    args,
                    id: BasicFunction::Construction,
                };
                let e = self.add_tags_to_expr(l, p, type_id, &mut basic_block_env.instructions);
                basic_block_env.assign(v, e);
            }
            ir1::Expr::BasicCall {
                args,
                id: ir1::BasicFunction::IntrinsicConstruction(id),
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
            ir1::Expr::BasicCall {
                args,
                id: ir1::BasicFunction::FieldAccessor { constructor, field },
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
                    &mut basic_block_env.instructions,
                    None,
                )?;
                let t = &self.map.dereference(p);
                debug_assert!(!t.diverged.unwrap());
                basic_block_env.assign(
                    v,
                    BasicCall {
                        args: vec![a],
                        id: BasicFunction::FieldAccessor { field: *field },
                    },
                )
            }
            ir1::Expr::BasicCall {
                args,
                id: ir1::BasicFunction::Intrinsic(IntrinsicVariable::Debug),
            } => {
                let args = args
                    .iter()
                    .map(|a| self.get_defined_local_variable(*a, root_t))
                    .collect_vec();
                let p = self
                    .local_variable_collector
                    .get_type(args[0])
                    .type_pointer
                    .unwrap();
                let p = self.map.find(p);
                self.printer_collector.add(p, &mut self.map);
                let e = BasicCall {
                    args,
                    id: BasicFunction::DebugPrint { p },
                };
                basic_block_env.assign(v, e);
            }
            ir1::Expr::BasicCall {
                args,
                id: ir1::BasicFunction::Intrinsic(id),
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
                            &mut basic_block_env.instructions,
                            None,
                        )?
                    } else {
                        self.get_defined_local_variable(*a, root_t)
                    };
                    args_new.push(a);
                    arg_ts.push(self.local_variable_collector.get_type(a).c_type);
                }
                let ct_p = if let Some(rt) = id.runtime_return_type() {
                    match self.get_tag_normal(p, TypeId::Intrinsic(rt)) {
                        GetTagNormalResult::NotTagged => PointerForCType::from(p),
                        GetTagNormalResult::Tagged { tag, boxed: _ } => PointerForCType {
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
        let t = &self.map.dereference_without_find(ot);
        debug_assert!(!t.diverged.unwrap());
        let type_map = &t.type_map;
        let Some((fn_type, _fn_boxed)) = type_map
            .get(&TypeId::Intrinsic(IntrinsicTypeTag::Fn))
            .cloned()
        else {
            return (Vec::new(), type_map.len() as u32);
        };
        debug_assert_eq!(
            *type_map.last_key_value().unwrap().0,
            TypeId::Intrinsic(IntrinsicTypeTag::Fn)
        );
        let type_map_len = type_map.len();
        for (tag, (id, (ctx, ctx_boxed))) in type_map
            .iter()
            .take(type_map_len - 1)
            .map(|(id, ctx)| (*id, ctx.clone()))
            .collect_vec()
            .into_iter()
            .enumerate()
        {
            if let TypeId::Function(original_lambda_id) = id {
                let len = self.functions.len() as u32;
                let lambda_id = (
                    original_lambda_id,
                    fn_type
                        .iter()
                        .chain(&ctx)
                        .map(|a| self.get_type_for_hash(*a))
                        .collect_vec(),
                );
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
                    modifier: if type_map_len == 2 {
                        PointerModifier::Normal
                    } else {
                        PointerModifier::UnionMember(tag as u32)
                    },
                };
                let p = self.normalizer_for_c_type.find(p);
                let ctx_hash = self.c_type_for_hash(p);
                let ct = self.c_type_memo_from_hash.get(&ctx_hash).unwrap();
                debug_assert_eq!(
                    self.c_type_definitions.len(),
                    self.c_type_memo_from_hash.len()
                );
                fs.push(PossibleFunction {
                    tag: tag as u32,
                    lambda_id: id,
                    c_type: CType { i: StructId(ct) },
                    ctx,
                    boxed: ctx_boxed,
                });
            }
        }
        (fs, type_map_len as u32 - 1)
    }

    fn get_type(&mut self, p: PointerForCType) -> Option<Type> {
        match p.modifier {
            PointerModifier::Normal => {
                self.collect_box_points(p.p);
                let t = self.type_memo.get_type(p.p, &mut self.map);
                Some(t)
            }
            PointerModifier::UnionMember(_) => None,
        }
    }

    fn get_type_for_hash(&mut self, p: TypePointer) -> Type {
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
            GetTagNormalResult::Tagged { tag, boxed: _ } => {
                let value = self.new_variable(PointerForCType {
                    p,
                    modifier: PointerModifier::UnionMember(tag),
                });
                instructions.push(Instruction::Assign(value, e));
                Expr::Upcast { tag, value }
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
        let mut ids = terminal.type_map.iter();
        for (id, (_, boxed)) in &mut ids {
            if let TypeId::Intrinsic(IntrinsicTypeTag::Fn) = id {
                break;
            } else if *id == type_id {
                debug_assert!(result.is_none());
                result = Some((tag, boxed));
            }
            tag += 1;
        }
        debug_assert!(ids.next().is_none());
        match result {
            Some((tag_of_t, boxed)) => {
                if tag == 1 {
                    GetTagNormalResult::NotTagged
                } else {
                    GetTagNormalResult::Tagged {
                        tag: tag_of_t as u32,
                        boxed: *boxed,
                    }
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
            return *t;
        }
        debug_assert!(!self.normalizer_for_c_type.contains(p));
        self.collect_box_points(p.p);
        self.map.minimize(p.p);
        debug_assert!(!self.c_type_memo.contains_key(&p));
        if let Some(t) = self.c_type_from_memo(p) {
            return CType { i: StructId(t) };
        }
        let mut partitions = Default::default();
        self.collect_pointers_for_c_type(p.p, &mut partitions);
        let c_type_schemes = partitions
            .keys()
            .map(|p| (*p, self.get_c_type_scheme_from_pointer(*p)))
            .collect();
        let (partitions, c_type_defs) = CTypeEnv(&c_type_schemes).split_partitions(partitions);
        let partition_rev: FxHashMap<_, _> = partitions.iter().map(|(k, v)| (*v, *k)).collect();
        let c_type_defs_rev: FxHashMap<_, _> = c_type_defs.iter().map(|(k, v)| (*v, k)).collect();
        for (t, p) in &partitions {
            debug_assert!(self.map.is_terminal(t.p));
            let r = partition_rev[p];
            debug_assert!(self.map.is_terminal(r.p));
            debug_assert!(self.map.dereference_without_find(t.p).diverged.is_some());
            debug_assert!(self.map.dereference_without_find(r.p).diverged.is_some());
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
                    },
                );
            } else {
                let c_type = self.c_type_memo_from_hash.get_or_insert(for_hash.clone());
                self.c_type_memo.insert(
                    t,
                    CType {
                        i: StructId(c_type),
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
                let a = partition_rev[&(a.i.0 as u32)];
                let a = self.normalizer_for_c_type.find(a);
                let for_hash = self.c_type_for_hash(a);
                CType {
                    i: StructId(self.c_type_memo_from_hash.get(&for_hash).unwrap()),
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

    fn c_type_for_hash(&mut self, p: PointerForCType) -> CTypeForHash {
        #[cfg(debug_assertions)]
        if self.map.minimize_types {
            let p = self.map.find(p.p);
            assert!(self.map.minimized_pointers.contains(&p))
        }
        match p.modifier {
            PointerModifier::Normal => self.c_type_for_hash_inner(p.p),
            PointerModifier::UnionMember(tag) => self.c_type_for_hash_inner_with_tag(p.p, tag),
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
        }
    }

    fn collect_args(
        &mut self,
        args: &[TypePointer],
        trace: &mut FxHashMap<TypePointer, u32>,
    ) -> Vec<CTypeForHashInner> {
        args.iter()
            .map(|p| self.c_type_for_hash_inner_aux(*p, trace))
            .collect()
    }

    fn collect_hash_unit(
        &mut self,
        p: TypePointer,
        ts: &mut Vec<(CTypeForHashUnit, bool)>,
        trace: &mut FxHashMap<TypePointer, u32>,
    ) {
        let t = &self.map.dereference_without_find(p);
        debug_assert!(t.diverged.is_some());
        for (type_id, (args, boxed)) in t.type_map.clone() {
            if let Some(t) = match type_id {
                TypeId::Intrinsic(tag) => match tag {
                    IntrinsicTypeTag::Ptr => Some(CTypeForHashUnit::Ptr),
                    IntrinsicTypeTag::I64 => Some(CTypeForHashUnit::I64),
                    IntrinsicTypeTag::F64 => Some(CTypeForHashUnit::F64),
                    IntrinsicTypeTag::U8 => Some(CTypeForHashUnit::U8),
                    IntrinsicTypeTag::Unit => Some(CTypeForHashUnit::Aggregate(Vec::new())),
                    IntrinsicTypeTag::Fn => None,
                    IntrinsicTypeTag::Mut => {
                        let t = self.c_type_for_hash_inner_aux(args[0], trace);
                        Some(CTypeForHashUnit::Ref(t))
                    }
                },
                TypeId::UserDefined(_) | TypeId::Function(_) => {
                    let args = CTypeForHashUnit::Aggregate(self.collect_args(&args, trace));
                    Some(args)
                }
            } {
                ts.push((t, boxed));
            }
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
        let p = self.map.find(p.p);
        let reference_point = self.map.dereference_without_find(p).diverged;
        if reference_point.unwrap() {
            return CTypeForHashInner::Type(CTypeForHash(vec![(CTypeForHashUnit::Diverge, false)]));
        }
        if let Some(d) = trace.get(&p) {
            return CTypeForHashInner::Index(trace.len() as u32 - *d - 1);
        }
        trace.insert(p, trace.len() as u32);
        let mut ts = Vec::new();
        self.collect_hash_unit(p, &mut ts, trace);
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
        trace: &mut FxHashMap<TypePointer, u32>,
        tag: usize,
    ) -> CTypeForHashUnit {
        let t = self.map.dereference_without_find(p);
        debug_assert!(t.diverged.is_some());
        let (type_id, (args, _)) = t.type_map.iter().nth(tag).unwrap();
        let type_id = *type_id;
        let args = args.clone();
        match type_id {
            TypeId::Intrinsic(tag) => match tag {
                IntrinsicTypeTag::Ptr => CTypeForHashUnit::Ptr,
                IntrinsicTypeTag::I64 => CTypeForHashUnit::I64,
                IntrinsicTypeTag::F64 => CTypeForHashUnit::F64,
                IntrinsicTypeTag::U8 => CTypeForHashUnit::U8,
                IntrinsicTypeTag::Unit => CTypeForHashUnit::Aggregate(Vec::new()),
                IntrinsicTypeTag::Fn => panic!(),
                IntrinsicTypeTag::Mut => {
                    let t = self.c_type_for_hash_inner_aux(args[0], trace);
                    CTypeForHashUnit::Ref(t)
                }
            },
            TypeId::UserDefined(_) | TypeId::Function(_) => {
                let args = self.collect_args(&args, trace);
                CTypeForHashUnit::Aggregate(args)
            }
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
            let t = self.collect_hash_unit_with_tag(p, &mut Default::default(), tag as usize);
            let t = CTypeForHash(vec![(t, false)]);
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
        let t = &self.map.dereference_without_find(node.p);
        match t.diverged {
            None => panic!(),
            Some(true) => {
                return CTypeScheme::Diverge;
            }
            Some(false) => (),
        }
        let mut ts = Vec::new();
        let mut bs = Vec::new();
        for (id, (args, boxed)) in &t.type_map {
            if !matches!(id, TypeId::Intrinsic(IntrinsicTypeTag::Fn)) {
                bs.push(*boxed);
            }
            match id {
                TypeId::Intrinsic(tag) => match tag {
                    IntrinsicTypeTag::Ptr => ts.push(CTypeScheme::Ptr),
                    IntrinsicTypeTag::I64 => ts.push(CTypeScheme::I64),
                    IntrinsicTypeTag::F64 => ts.push(CTypeScheme::F64),
                    IntrinsicTypeTag::U8 => ts.push(CTypeScheme::U8),
                    IntrinsicTypeTag::Unit => ts.push(CTypeScheme::Aggregate(Vec::new())),
                    IntrinsicTypeTag::Fn => (),
                    IntrinsicTypeTag::Mut => {
                        ts.push(CTypeScheme::Mut(PointerForCType::from(
                            self.map.find_imm(args[0]),
                        )));
                    }
                },
                TypeId::UserDefined(_) | TypeId::Function(_) => {
                    ts.push(CTypeScheme::Aggregate(
                        args.iter()
                            .map(|p| PointerForCType {
                                modifier: PointerModifier::Normal,
                                p: self.map.find_imm(*p),
                            })
                            .collect(),
                    ));
                }
            }
        }
        if let PointerModifier::UnionMember(tag) = node.modifier {
            ts.into_iter().nth(tag as usize).unwrap()
        } else if ts.len() == 1 {
            ts.pop().unwrap()
        } else {
            CTypeScheme::Union(
                bs.iter()
                    .enumerate()
                    .map(|(i, boxed)| {
                        (
                            PointerForCType {
                                modifier: PointerModifier::UnionMember(i as u32),
                                p: node.p,
                            },
                            *boxed,
                        )
                    })
                    .collect(),
            )
        }
    }

    fn collect_pointers_for_c_type(
        &mut self,
        p: TypePointer,
        pointers: &mut FxHashMap<PointerForCType, u32>,
    ) {
        let p = self.map.find_imm(p);
        let contains = pointers.insert(PointerForCType::from(p), 0).is_some();
        if contains {
            return;
        }
        let terminal = self.map.dereference_without_find(p);
        let mut tag = 0;
        for (id, (args, _boxed)) in terminal.type_map.clone() {
            match id {
                TypeId::Intrinsic(IntrinsicTypeTag::Fn) => {}
                _ => {
                    for t in &args {
                        self.collect_pointers_for_c_type(*t, pointers);
                    }
                    tag += 1;
                }
            }
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

    pub fn collect_box_points(&mut self, p: TypePointer) {
        let p = self.map.find_imm(p);
        if self.map.dereference_without_find(p).diverged.is_some() {
            return;
        }
        fn pointer_to_node(
            map: &PaddedTypeMap,
            p: TypePointer,
            p_to_n: &mut FxHashMap<TypePointer, NodeIndex>,
            g: &mut Graph<TypePointer, f64>,
            diverged_mut: &mut Vec<TypePointer>,
        ) -> Option<NodeIndex> {
            let p = map.find_imm(p);
            if let Some(n) = p_to_n.get(&p) {
                return Some(*n);
            }
            let terminal = map.dereference_without_find(p);
            if terminal.diverged.is_some() {
                return None;
            }
            let n = g.add_node(p);
            p_to_n.insert(p, n);
            for (id, (args, boxed)) in &terminal.type_map {
                match id {
                    TypeId::Intrinsic(id) => {
                        for a in args {
                            pointer_to_node(map, *a, p_to_n, g, diverged_mut);
                        }
                        if matches!(id, IntrinsicTypeTag::Mut)
                            && terminal.type_map.len() == 1
                            && p == map.find_imm(args[0])
                        {
                            diverged_mut.push(p)
                        }
                    }
                    _ => {
                        debug_assert!(!boxed);
                        for a in args {
                            if let Some(to) = pointer_to_node(map, *a, p_to_n, g, diverged_mut) {
                                g.update_edge(n, to, -1.);
                            }
                        }
                    }
                }
            }
            Some(n)
        }
        let mut g = Graph::new();
        let mut p_to_n = FxHashMap::default();
        let mut diverged_mut = Vec::new();
        pointer_to_node(&self.map, p, &mut p_to_n, &mut g, &mut diverged_mut);
        for p in diverged_mut {
            self.map.dereference_without_find_mut(p).diverged = Some(true);
        }
        for (p, n) in &p_to_n {
            while let Some(cycle) = find_negative_cycle(&g, *n) {
                if let Some(pos) = cycle
                    .iter()
                    .position(|c| self.map.len_for_c_type(*g.node_weight(*c).unwrap()) > 1)
                {
                    let a = cycle[pos];
                    let b = if pos + 1 == cycle.len() {
                        *cycle.first().unwrap()
                    } else {
                        cycle[pos + 1]
                    };
                    g.remove_edge(g.find_edge(a, b).unwrap());
                    let a = *g.node_weight(a).unwrap();
                    let b = *g.node_weight(b).unwrap();
                    debug_assert!(self.map.is_terminal(b));
                    let t = self.map.dereference_without_find(a);
                    let new_type_map = t
                        .type_map
                        .iter()
                        .map(|(id, (args, boxed))| {
                            let args = args.iter().map(|a| self.map.find_imm(*a)).collect_vec();
                            let boxed = *boxed || args.contains(&b);
                            (*id, (args, boxed))
                        })
                        .collect();
                    let t = &mut self.map.dereference_without_find_mut(a);
                    if t.diverged != Some(true) {
                        t.type_map = new_type_map;
                    }
                } else {
                    for (a, b) in cycle.iter().circular_tuple_windows() {
                        g.remove_edge(g.find_edge(*a, *b).unwrap());
                        let a = *g.node_weight(*a).unwrap();
                        self.map.dereference_without_find_mut(a).diverged = Some(true);
                    }
                }
            }
            let t = &mut self.map.dereference_without_find_mut(*p);
            if t.diverged.is_none() {
                t.diverged = Some(false);
            }
        }
    }
}

#[derive(Debug, Clone)]
struct PossibleFunction {
    tag: u32,
    lambda_id: FxLambdaId,
    c_type: CType,
    ctx: Vec<TypePointer>,
    boxed: bool,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum CTypeForHashInner {
    Type(CTypeForHash),
    Index(u32),
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct CTypeForHash(Vec<(CTypeForHashUnit, bool)>);

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum CTypeForHashUnit {
    I64,
    U8,
    F64,
    Ptr,
    Aggregate(Vec<CTypeForHashInner>),
    Ref(CTypeForHashInner),
    Diverge,
}

pub enum GetTagNormalResult {
    NotTagged,
    Impossible,
    Tagged { tag: u32, boxed: bool },
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
