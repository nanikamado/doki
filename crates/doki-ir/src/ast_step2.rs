mod local_variable;
mod type_memo;

pub use self::local_variable::{LocalVariable, LocalVariableCollector};
use self::type_memo::{get_tag_normal, GetTagNormalResult, TypeMemo};
pub use self::type_memo::{
    DisplayTypeWithEnv, DisplayTypeWithEnvStruct, Type, TypeForHash, TypeInner, TypeInnerForHash,
    TypeInnerOf, TypeOf, TypeUnit, TypeUnitForHash, TypeUnitOf,
};
use crate::ast_step1::{
    self, BasicFunction, ConstructorNames, GlobalVariable, LambdaId, LocalVariableTypes,
    PaddedTypeMap, ReplaceMap, TypeId, TypePointer,
};
use crate::ast_step2::type_memo::BrokenLinkCheck;
use crate::id_generator::{self, IdGenerator};
use crate::intrinsics::IntrinsicType;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use std::fmt::{Debug, Display};

#[derive(Debug)]
pub struct Ast {
    pub variable_decls: Vec<VariableDecl>,
    pub entry_point: FxLambdaId,
    pub variable_names: FxHashMap<VariableId, String>,
    pub functions: Vec<Function>,
    pub type_map: PaddedTypeMap,
    pub variable_types: LocalVariableCollector<Type>,
    pub fx_type_map: FxHashMap<LambdaId<id_generator::Id<TypeIdTag>>, FxLambdaId>,
    pub constructor_names: ConstructorNames,
    pub type_id_generator: IdGenerator<TypeForHash, TypeIdTag>,
    pub local_variable_replace_map: FxHashMap<(ast_step1::LocalVariable, Root), LocalVariable>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct GlobalVariableId(usize);

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl {
    pub name: String,
    pub value: Block,
    pub ret: VariableId,
    pub decl_id: GlobalVariableId,
    pub original_decl_id: GlobalVariable,
    pub t: Type,
    pub t_for_hash: TypeForHash,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Block {
    pub instructions: Vec<Instruction>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Tester {
    Tag { tag: u32 },
    I64 { value: String },
    Str { value: String },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Instruction {
    Assign(LocalVariable, Expr),
    Test(Tester, VariableId),
    FailTest,
    Panic { msg: String },
    TryCatch(Block, Block),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    Lambda {
        lambda_id: FxLambdaId,
        context: Vec<LocalVariable>,
    },
    I64(String),
    Str(String),
    Ident(VariableId),
    Call {
        f: VariableId,
        a: VariableId,
        real_function: FxLambdaId,
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
    pub body: Block,
    pub ret: VariableId,
}

impl Ast {
    pub fn from(ast: ast_step1::Ast, minimize_type: bool) -> Self {
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
        match &b.instructions[0] {
            Instruction::Assign(_, Expr::Lambda { lambda_id, context }) => {
                debug_assert!(context.is_empty());
                let entry_point = *lambda_id;
                let mut functions = Vec::new();
                let mut fx_type_map = FxHashMap::default();
                for (id, f) in memo.functions {
                    if let FunctionEntry::Function(f) = f {
                        functions.push(f.clone());
                        fx_type_map.insert(id, f.id);
                    } else {
                        panic!()
                    }
                }
                Self {
                    variable_decls: memo.monomorphized_variables,
                    entry_point,
                    functions,
                    variable_names,
                    type_map: memo.map,
                    variable_types: memo.local_variable_collector,
                    fx_type_map,
                    constructor_names: memo.constructor_names,
                    type_id_generator: memo.type_id_generator,
                    local_variable_replace_map: memo.local_variable_replace_map,
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

pub struct Env {
    variable_decls: FxHashMap<GlobalVariable, ast_step1::VariableDecl>,
    monomorphized_variable_map: FxHashMap<Root, GlobalVariableId>,
    monomorphized_variables: Vec<VariableDecl>,
    map: PaddedTypeMap,
    functions: FxHashMap<LambdaId<TypeUnique>, FunctionEntry>,
    type_memo: TypeMemo,
    local_variable_types_old: LocalVariableTypes,
    local_variable_replace_map: FxHashMap<(ast_step1::LocalVariable, Root), LocalVariable>,
    local_variable_collector: LocalVariableCollector<Type>,
    global_variable_count: usize,
    constructor_names: ConstructorNames,
    type_id_generator: IdGenerator<TypeForHash, TypeIdTag>,
    minimize_type: bool,
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

impl Env {
    pub fn new(
        variable_decls: Vec<ast_step1::VariableDecl>,
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
            type_id_generator: Default::default(),
            minimize_type,
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
        let t_id = self.type_id_generator.get_or_insert(t_for_hash.clone());
        let t = self.get_type(p);
        let root = (t_id, decl_id);
        if let Some(d) = self.monomorphized_variable_map.get(&root) {
            *d
        } else {
            let new_decl_id = GlobalVariableId(self.global_variable_count);
            self.global_variable_count += 1;
            let d = self.variable_decls.get(&decl_id).unwrap().clone();
            self.monomorphized_variable_map.insert(root, new_decl_id);
            let (b, _) = self.block(d.value, root, replace_map);
            let d = VariableDecl {
                value: b,
                decl_id: new_decl_id,
                original_decl_id: decl_id,
                ret: self.get_defined_variable_id(
                    ast_step1::VariableId::Local(d.ret),
                    root,
                    replace_map,
                ),
                name: d.name,
                t,
                t_for_hash,
            };
            self.monomorphized_variables.push(d);
            new_decl_id
        }
    }

    fn new_variable(&mut self, t: Type) -> LocalVariable {
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
            self.local_variable_collector.new_variable(t)
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
        root_t: Root,
        replace_map: &mut ReplaceMap,
    ) -> (Block, bool) {
        let mut instructions = Vec::new();
        let mut unreachable_block = false;
        for i in block.instructions {
            if self.instruction(i, root_t, replace_map, &mut instructions) {
                unreachable_block = true;
                break;
            }
        }
        (Block { instructions }, unreachable_block)
    }

    // Returns true if exited with a error
    fn instruction(
        &mut self,
        instruction: ast_step1::Instruction,
        root_t: Root,
        replace_map: &mut ReplaceMap,
        instructions: &mut Vec<Instruction>,
    ) -> bool {
        match instruction {
            ast_step1::Instruction::Assign(v, e) => {
                let t = self
                    .map
                    .clone_pointer(self.local_variable_types_old.get(v), replace_map);
                let t = self.map.clone_pointer(t, replace_map);
                let t = self.get_type(t);
                let e = self.expr(e, &t, root_t, replace_map, instructions);
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
                        instructions.push(Instruction::Assign(new_v, e));
                        false
                    }
                    Err(msg) => {
                        instructions.push(Instruction::Panic { msg });
                        true
                    }
                }
            }
            ast_step1::Instruction::Test(ast_step1::Tester::I64 { value }, l) => {
                let type_id = TypeId::Intrinsic(IntrinsicType::I64);
                let a = self.downcast(l, root_t, type_id, replace_map, instructions, true);
                match a {
                    Ok(a) => instructions.push(Instruction::Test(Tester::I64 { value }, a)),
                    Err(_) => {
                        instructions.push(Instruction::FailTest);
                    }
                }
                false
            }
            ast_step1::Instruction::Test(ast_step1::Tester::Str { value }, a) => {
                let type_id = TypeId::Intrinsic(IntrinsicType::String);
                let a = self.downcast(a, root_t, type_id, replace_map, instructions, true);
                match a {
                    Ok(a) => instructions.push(Instruction::Test(Tester::Str { value }, a)),
                    Err(_) => {
                        instructions.push(Instruction::FailTest);
                    }
                }
                false
            }
            ast_step1::Instruction::Test(ast_step1::Tester::Constructor { id }, a) => {
                let t = self
                    .map
                    .clone_pointer(self.local_variable_types_old.get(a), replace_map);
                let t = self.get_type(t);
                let a = self.get_defined_local_variable(a, root_t, replace_map);
                match get_tag_normal(&t, id) {
                    GetTagNormalResult::Tagged(tag, _untagged_t) => {
                        let a = self.deref(VariableId::Local(a), &t, instructions);
                        instructions.push(Instruction::Test(Tester::Tag { tag }, a));
                    }
                    GetTagNormalResult::NotTagged => (),
                    GetTagNormalResult::Impossible => {
                        instructions.push(Instruction::FailTest);
                    }
                }
                false
            }
            ast_step1::Instruction::TryCatch(b1, b2) => {
                let (b1, u1) = self.block(b1, root_t, replace_map);
                let (b2, u2) = self.block(b2, root_t, replace_map);
                instructions.push(Instruction::TryCatch(b1, b2));
                u1 && u2
            }
            ast_step1::Instruction::FailTest => {
                instructions.push(Instruction::FailTest);
                false
            }
            ast_step1::Instruction::Panic { msg } => {
                instructions.push(Instruction::Panic { msg });
                true
            }
        }
    }

    fn downcast(
        &mut self,
        a: ast_step1::LocalVariable,
        root_t: Root,
        type_id: TypeId,
        replace_map: &mut ReplaceMap,
        instructions: &mut Vec<Instruction>,
        test_instead_of_panic: bool,
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
                    instructions.push(Instruction::Test(Tester::Tag { tag }, a));
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
                "expected {type_id} but found {}. cannot downcast.",
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
        instructions: &mut Vec<Instruction>,
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
                let new_parameter = self.local_variable_def_replace(parameter, root_t, replace_map);
                let (b, _) = self.block(body, root_t, replace_map);
                let ret = self.get_defined_variable_id(
                    ast_step1::VariableId::Local(ret),
                    root_t,
                    replace_map,
                );
                let f = Function {
                    parameter: new_parameter,
                    body: b,
                    id: FxLambdaId(0),
                    context: context.clone(),
                    ret,
                };
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
                    ..f
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
                    instructions.push(Instruction::Assign(
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
                    debug_assert!(t.recursive);
                    let v = self.expr_to_variable(e, t.clone().deref(), instructions);
                    Expr::Ref(v)
                } else {
                    e
                }
            }
            ast_step1::Expr::I64(s) => self.add_tags_to_expr(
                I64(s),
                t,
                TypeId::Intrinsic(IntrinsicType::I64),
                instructions,
            ),
            ast_step1::Expr::Str(s) => self.add_tags_to_expr(
                Str(s),
                t,
                TypeId::Intrinsic(IntrinsicType::String),
                instructions,
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
                let f = self.deref(VariableId::Local(f), &f_t, instructions);
                let a = VariableId::Local(self.get_defined_local_variable(a, root_t, replace_map));
                if possible_functions.is_empty() {
                    return Err("not a function".to_string());
                }
                if possible_functions.len() == 1 && possible_functions[0].0 == 0 {
                    Call {
                        f,
                        a,
                        real_function: possible_functions[0].1,
                    }
                } else {
                    let ret_v = self.new_variable(t.clone());
                    let mut b = vec![Instruction::Panic {
                        msg: "not a function".to_string(),
                    }];
                    for (tag, id, casted_t) in possible_functions {
                        let mut b2 = vec![Instruction::Test(Tester::Tag { tag: tag as u32 }, f)];
                        let new_f = self.new_variable(casted_t);
                        b2.push(Instruction::Assign(
                            new_f,
                            Expr::Downcast {
                                tag: tag as u32,
                                value: f,
                                check: false,
                            },
                        ));
                        b2.push(Instruction::Assign(
                            ret_v,
                            Expr::Call {
                                f: VariableId::Local(new_f),
                                a,
                                real_function: id,
                            },
                        ));
                        b = vec![Instruction::TryCatch(
                            Block { instructions: b2 },
                            Block { instructions: b },
                        )];
                    }
                    instructions.append(&mut b);
                    Ident(VariableId::Local(ret_v))
                }
            }
            ast_step1::Expr::BasicCall {
                args,
                id: BasicFunction::Construction(id),
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
                    instructions,
                )
            }
            ast_step1::Expr::BasicCall {
                args,
                id: BasicFunction::IntrinsicConstruction(id),
            } => {
                debug_assert!(args.is_empty());
                self.add_tags_to_expr(
                    BasicCall {
                        args: Vec::new(),
                        id: BasicFunction::IntrinsicConstruction(id),
                    },
                    t,
                    TypeId::Intrinsic(id.into()),
                    instructions,
                )
            }
            ast_step1::Expr::BasicCall {
                args,
                id:
                    id @ BasicFunction::FieldAccessor {
                        constructor,
                        field: _,
                    },
            } => {
                debug_assert_eq!(args.len(), 1);
                let a = args.into_iter().next().unwrap();
                let a = self.downcast(
                    a,
                    root_t,
                    TypeId::UserDefined(constructor),
                    replace_map,
                    instructions,
                    false,
                )?;
                BasicCall { args: vec![a], id }
            }
            ast_step1::Expr::BasicCall {
                args,
                id: BasicFunction::Intrinsic(id),
            } => {
                let rt = id.runtime_return_type();
                let arg_ts = id.runtime_arg_type_id();
                let args = args
                    .into_iter()
                    .zip_eq(arg_ts)
                    .map(|(a, param_t)| {
                        self.downcast(a, root_t, param_t, replace_map, instructions, false)
                    })
                    .collect::<Result<_, _>>()?;
                self.add_tags_to_expr(
                    BasicCall {
                        args,
                        id: BasicFunction::Intrinsic(id),
                    },
                    t,
                    TypeId::Intrinsic(rt),
                    instructions,
                )
            }
        };
        Ok(e)
    }

    fn get_possible_functions(&mut self, ot: &Type) -> Vec<(i32, FxLambdaId, Type)> {
        let mut fs = Vec::new();
        let mut tag = 0;
        for t in ot.iter() {
            let t = if ot.recursive {
                t.clone().replace_index(ot, 0)
            } else {
                t.clone()
            };
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
                            .entry(id_type_inner)
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
        if self.minimize_type && !self.type_memo.replace_map.contains_key(&p) {
            use std::collections::hash_map::Entry::*;
            for (from, to) in self.map.minimize(p) {
                match self.type_memo.replace_map.entry(from) {
                    Occupied(mut e) => {
                        let v = e.get();
                        if to < *v {
                            e.insert(to);
                        }
                    }
                    Vacant(e) => {
                        e.insert(to);
                    }
                }
            }
        }
    }

    fn get_type(&mut self, p: TypePointer) -> Type {
        self.minimize(p);
        self.type_memo
            .get_type(p, &mut self.map, &mut self.type_id_generator)
    }

    fn get_type_for_hash(&mut self, p: TypePointer) -> TypeForHash {
        self.minimize(p);
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
            debug_assert!(t.recursive);
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
