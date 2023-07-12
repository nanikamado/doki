mod padded_type_map;

#[cfg(debug_assertions)]
pub use self::padded_type_map::JsonDebug;
pub use self::padded_type_map::{PaddedTypeMap, ReplaceMap, Terminal, TypeId, TypePointer};
use crate::intrinsics::{IntrinsicConstructor, IntrinsicTypeTag, IntrinsicVariable};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use std::fmt::{Debug, Display};
use std::mem;

#[derive(Debug)]
pub struct Ast {
    pub variable_decls: Vec<VariableDecl>,
    pub entry_point: GlobalVariable,
    pub type_of_entry_point: TypePointer,
    pub local_variable_types: LocalVariableTypes,
    pub type_map: PaddedTypeMap,
    pub constructor_names: ConstructorNames,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct LocalVariable(usize);

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct GlobalVariable(usize);

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct ConstructorId(usize);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum VariableId {
    Local(LocalVariable),
    Global(GlobalVariable, ReplaceMap, TypePointer),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct LambdaId<T> {
    pub id: u32,
    pub root_t: T,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDecl {
    pub value: Block,
    pub ret: LocalVariable,
    pub decl_id: GlobalVariable,
    pub name: String,
}

#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct Block {
    pub instructions: Vec<Instruction>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Tester {
    Constructor { id: TypeId },
    I64 { value: String },
    Str { value: String },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Instruction {
    Assign(LocalVariable, Expr),
    Test(Tester, LocalVariable),
    FailTest,
    Panic { msg: String },
    TryCatch(Block, Block),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    Lambda {
        lambda_id: LambdaId<TypePointer>,
        parameter: LocalVariable,
        body: Block,
        ret: LocalVariable,
        context: Vec<LocalVariable>,
    },
    I64(String),
    U8(u8),
    Str(String),
    Ident(VariableId),
    Call {
        f: LocalVariable,
        a: LocalVariable,
    },
    BasicCall {
        args: Vec<LocalVariable>,
        id: BasicFunction,
    },
}

#[derive(Debug, PartialEq, Clone, Copy, Eq)]
pub enum BasicFunction {
    Intrinsic(IntrinsicVariable),
    Construction(ConstructorId),
    IntrinsicConstruction(IntrinsicConstructor),
    FieldAccessor {
        constructor: ConstructorId,
        field: usize,
    },
}

struct TypeInfEnv {
    type_map: PaddedTypeMap,
    global_variable_types: FxHashMap<GlobalVariable, GlobalVariableType>,
    local_variable_types: LocalVariableTypes,
    global_variables_before_type_inf: FxHashMap<GlobalVariable, VariableDecl>,
    global_variables_done: Vec<VariableDecl>,
    trace: FxHashMap<GlobalVariable, TypePointer>,
    field_len: Vec<usize>,
    used_local_variables: FxHashSet<LocalVariable>,
    defined_local_variables: FxHashSet<LocalVariable>,
    unreplicatable_pointers: Vec<TypePointer>,
    unfixed_unreplicatable_pointer_in_local_variables: FxHashMap<LocalVariable, Vec<TypePointer>>,
    unfixed_unreplicatable_pointers: Vec<TypePointer>,
}

struct GlobalVariableType {
    t: TypePointer,
    unreplicatable: Vec<TypePointer>,
    unfixed_unreplicatable_pointers: Vec<TypePointer>,
}

enum IsRecursive {
    True,
    False {
        unreplicatable_pointers: Vec<TypePointer>,
        unfixed_unreplicatable_pointers: Vec<TypePointer>,
    },
}

impl TypeInfEnv {
    fn get_type_global(&mut self, decl_id: GlobalVariable) -> (TypePointer, IsRecursive) {
        if let Some(p) = self.trace.get(&decl_id) {
            (*p, IsRecursive::True)
        } else if let Some(t) = self.global_variable_types.get(&decl_id) {
            (
                t.t,
                IsRecursive::False {
                    unreplicatable_pointers: t.unreplicatable.clone(),
                    unfixed_unreplicatable_pointers: t.unfixed_unreplicatable_pointers.clone(),
                },
            )
        } else {
            let mut d = self
                .global_variables_before_type_inf
                .remove(&decl_id)
                .unwrap();
            let root_t = self.local_variable_types.get(d.ret);
            self.trace.insert(decl_id, root_t);
            let unreplicatable_pointers_tmp = std::mem::take(&mut self.unreplicatable_pointers);
            let unfixed_unreplicatable_pointers_tmp =
                std::mem::take(&mut self.unfixed_unreplicatable_pointers);
            self.block(&mut d.value, root_t, true);
            let unreplicatable_pointers = std::mem::replace(
                &mut self.unreplicatable_pointers,
                unreplicatable_pointers_tmp,
            );
            let unfixed_unreplicatable_pointers = std::mem::replace(
                &mut self.unfixed_unreplicatable_pointers,
                unfixed_unreplicatable_pointers_tmp,
            );
            self.trace.remove(&decl_id);
            self.global_variable_types.insert(
                decl_id,
                GlobalVariableType {
                    t: root_t,
                    unreplicatable: unreplicatable_pointers.clone(),
                    unfixed_unreplicatable_pointers: unfixed_unreplicatable_pointers.clone(),
                },
            );
            self.global_variables_done.push(d);
            (
                root_t,
                IsRecursive::False {
                    unreplicatable_pointers,
                    unfixed_unreplicatable_pointers,
                },
            )
        }
    }

    fn block(&mut self, block: &mut Block, root_t: TypePointer, outside_of_fn: bool) {
        for i in &mut block.instructions {
            match i {
                Instruction::Assign(v, e) => {
                    let t = self.local_variable_types.get(*v);
                    match e {
                        Expr::Lambda {
                            lambda_id,
                            parameter,
                            body,
                            ret,
                            context,
                        } => {
                            let used_local_variables_tmp =
                                mem::take(&mut self.used_local_variables);
                            let defined_local_variables_tmp =
                                mem::take(&mut self.defined_local_variables);
                            self.defined_local_variables.insert(*parameter);
                            let arg = self.local_variable_types.get(*parameter);
                            let ret = self.local_variable_types.get(*ret);
                            let fn_id = self.type_map.new_lambda_id_pointer();
                            self.block(body, root_t, false);
                            *context = self
                                .used_local_variables
                                .iter()
                                .copied()
                                .filter(|v| !self.defined_local_variables.contains(v))
                                .collect_vec();
                            self.type_map.insert_lambda_id(
                                fn_id,
                                LambdaId {
                                    id: lambda_id.id,
                                    root_t,
                                },
                                context
                                    .iter()
                                    .map(|p| self.local_variable_types.get(*p))
                                    .collect(),
                            );
                            self.type_map.insert_function(t, arg, ret, fn_id);
                            self.used_local_variables.extend(used_local_variables_tmp);
                            self.defined_local_variables
                                .extend(defined_local_variables_tmp);
                        }
                        Expr::I64(_) => {
                            self.type_map.insert_normal(
                                t,
                                TypeId::Intrinsic(IntrinsicTypeTag::I64),
                                Vec::new(),
                            );
                        }
                        Expr::U8(_) => {
                            self.type_map.insert_normal(
                                t,
                                TypeId::Intrinsic(IntrinsicTypeTag::U8),
                                Vec::new(),
                            );
                        }
                        Expr::Str(_) => {
                            self.type_map.insert_normal(
                                t,
                                TypeId::Intrinsic(IntrinsicTypeTag::String),
                                Vec::new(),
                            );
                        }
                        Expr::Ident(VariableId::Global(decl_id, replace_map, pp)) => {
                            debug_assert!(replace_map.is_empty());
                            let (p, is_recursive) = self.get_type_global(*decl_id);
                            match is_recursive {
                                IsRecursive::True => {
                                    self.type_map.union(p, t);
                                    *pp = p;
                                }
                                IsRecursive::False {
                                    unreplicatable_pointers,
                                    unfixed_unreplicatable_pointers,
                                } => {
                                    replace_map.add_unreplicatable(
                                        unreplicatable_pointers
                                            .iter()
                                            .map(|p| self.type_map.find(*p)),
                                    );
                                    let v_cloned = self.type_map.clone_pointer(p, replace_map);
                                    self.type_map.union(t, v_cloned);
                                    *pp = t;
                                    let mut unfixed_unreplicatable_pointers =
                                        unfixed_unreplicatable_pointers
                                            .into_iter()
                                            .map(|p| self.type_map.clone_pointer(p, replace_map))
                                            .collect_vec();
                                    if !unfixed_unreplicatable_pointers.is_empty() {
                                        self.unfixed_unreplicatable_pointer_in_local_variables
                                            .insert(*v, unfixed_unreplicatable_pointers.clone());
                                    }
                                    self.unfixed_unreplicatable_pointers
                                        .append(&mut unfixed_unreplicatable_pointers);
                                }
                            }
                        }
                        Expr::Ident(VariableId::Local(d)) => {
                            self.used_local_variables.insert(*d);
                            let t2 = self.local_variable_types.get(*d);
                            self.type_map.union(t, t2);
                        }
                        Expr::Call { f, a } => {
                            if let Some(unfixed_unreplicatables) = self
                                .unfixed_unreplicatable_pointer_in_local_variables
                                .get(f)
                            {
                                if outside_of_fn {
                                    self.unreplicatable_pointers
                                        .extend(unfixed_unreplicatables.iter())
                                }
                            }
                            self.used_local_variables.insert(*f);
                            self.used_local_variables.insert(*a);
                            let f_t = self.local_variable_types.get(*f);
                            let a_t = self.local_variable_types.get(*a);
                            let (f_arg_t, ret_t, _) = self.type_map.get_fn(f_t);
                            self.type_map.union(f_arg_t, a_t);
                            self.type_map.union(t, ret_t);
                        }
                        Expr::BasicCall {
                            args,
                            id: BasicFunction::Construction(d),
                        } => {
                            self.type_map.insert_normal(
                                t,
                                TypeId::UserDefined(*d),
                                args.iter()
                                    .map(|a| {
                                        self.used_local_variables.insert(*a);
                                        self.local_variable_types.get(*a)
                                    })
                                    .collect(),
                            );
                        }
                        Expr::BasicCall {
                            args,
                            id: BasicFunction::IntrinsicConstruction(d),
                        } => {
                            self.type_map.insert_normal(
                                t,
                                TypeId::Intrinsic((*d).into()),
                                args.iter()
                                    .map(|a| {
                                        self.used_local_variables.insert(*a);
                                        self.local_variable_types.get(*a)
                                    })
                                    .collect(),
                            );
                        }
                        Expr::BasicCall {
                            args,
                            id: BasicFunction::FieldAccessor { constructor, field },
                        } => {
                            debug_assert_eq!(args.len(), 1);
                            let fields_p = (0..self.field_len[constructor.0])
                                .map(|_| self.type_map.new_pointer())
                                .collect_vec();
                            self.type_map.union(t, fields_p[*field]);
                            self.used_local_variables.insert(args[0]);
                            self.type_map.insert_normal(
                                self.local_variable_types.get(args[0]),
                                TypeId::UserDefined(*constructor),
                                fields_p,
                            );
                        }
                        Expr::BasicCall {
                            args,
                            id: BasicFunction::Intrinsic(v),
                        } => {
                            let mut arg_types = Vec::with_capacity(args.len());
                            for a in args {
                                self.used_local_variables.insert(*a);
                                arg_types.push(self.local_variable_types.get(*a));
                            }
                            let mut p = Vec::new();
                            v.insert_return_type(t, &mut self.type_map, &arg_types, &mut p);
                            if outside_of_fn {
                                self.unreplicatable_pointers.append(&mut p.clone())
                            }
                            self.unfixed_unreplicatable_pointers.append(&mut p);
                        }
                    }
                    self.defined_local_variables.insert(*v);
                }
                Instruction::Test(_, l) => {
                    self.used_local_variables.insert(*l);
                }
                Instruction::FailTest | Instruction::Panic { .. } => (),
                Instruction::TryCatch(a, b) => {
                    self.block(a, root_t, outside_of_fn);
                    self.block(b, root_t, outside_of_fn);
                }
            }
        }
    }
}

#[derive(Debug, Default)]
pub struct LocalVariableTypes(Vec<TypePointer>);

impl LocalVariableTypes {
    pub fn get(&self, v: LocalVariable) -> TypePointer {
        self.0[v.0]
    }
}

pub struct Lambda<'a> {
    pub parameter: LocalVariable,
    pub ret: LocalVariable,
    pub body: &'a mut Block,
}

#[derive(Debug, Default)]
pub struct ConstructorNames(Vec<String>);

impl ConstructorNames {
    pub fn get(&self, c: ConstructorId) -> &str {
        &self.0[c.0]
    }
}

#[derive(Debug, Default)]
pub struct Env {
    type_map: PaddedTypeMap,
    local_variable_types: LocalVariableTypes,
    lambda_count: u32,
    global_variable_count: usize,
    global_variables_done: FxHashMap<GlobalVariable, VariableDecl>,
    field_len: Vec<usize>,
    constructor_names: ConstructorNames,
}

impl Env {
    pub fn lambda<'b>(&mut self, block: &'b mut Block, assign_v: LocalVariable) -> Lambda<'b> {
        let parameter = self.new_local_variable();
        let lambda_id = LambdaId {
            id: self.lambda_count,
            root_t: PaddedTypeMap::null_pointer(),
        };
        self.lambda_count += 1;
        let ret = self.new_local_variable();
        let e = Expr::Lambda {
            lambda_id,
            parameter,
            body: Block::default(),
            ret,
            context: Vec::new(),
        };
        block.instructions.push(Instruction::Assign(assign_v, e));
        let body = if let Instruction::Assign(_, Expr::Lambda { body, .. }) =
            block.instructions.last_mut().unwrap()
        {
            body
        } else {
            panic!()
        };
        Lambda {
            parameter,
            ret,
            body,
        }
    }

    pub fn new_global_variable(&mut self) -> GlobalVariable {
        self.global_variable_count += 1;
        GlobalVariable(self.global_variable_count - 1)
    }

    pub fn global_variable(&mut self, ret: LocalVariable, v: GlobalVariable, block: &mut Block) {
        block.assign(
            ret,
            Expr::Ident(VariableId::Global(
                v,
                Default::default(),
                PaddedTypeMap::null_pointer(),
            )),
        );
    }

    pub fn string(&mut self, ret: LocalVariable, a: String, block: &mut Block) {
        block.assign(ret, Expr::Str(a));
    }

    pub fn i64(&mut self, ret: LocalVariable, a: String, block: &mut Block) {
        block.assign(ret, Expr::I64(a));
    }

    pub fn u8(&mut self, ret: LocalVariable, a: u8, block: &mut Block) {
        block.assign(ret, Expr::U8(a));
    }

    pub fn local_variable(&mut self, ret: LocalVariable, a: LocalVariable, block: &mut Block) {
        block.assign(ret, Expr::Ident(VariableId::Local(a)));
    }

    pub fn call(
        &mut self,
        f: LocalVariable,
        a: LocalVariable,
        ret: LocalVariable,
        block: &mut Block,
    ) {
        block.assign(ret, Expr::Call { f, a });
    }

    pub fn intrinsic_call(
        &mut self,
        ret: LocalVariable,
        args: Vec<LocalVariable>,
        v: IntrinsicVariable,
        block: &mut Block,
    ) {
        block.assign(
            ret,
            Expr::BasicCall {
                args,
                id: BasicFunction::Intrinsic(v),
            },
        )
    }

    pub fn field_access(
        &mut self,
        ret: LocalVariable,
        arg: LocalVariable,
        constructor_id: ConstructorId,
        field: usize,
        block: &mut Block,
    ) {
        block.assign(
            ret,
            Expr::BasicCall {
                args: vec![arg],
                id: BasicFunction::FieldAccessor {
                    constructor: constructor_id,
                    field,
                },
            },
        );
    }

    pub fn construction(
        &mut self,
        ret: LocalVariable,
        args: Vec<LocalVariable>,
        constructor_id: ConstructorId,
        block: &mut Block,
    ) {
        block.assign(
            ret,
            Expr::BasicCall {
                args,
                id: BasicFunction::Construction(constructor_id),
            },
        );
    }

    pub fn intrinsic_construction(
        &mut self,
        ret: LocalVariable,
        constructor_id: IntrinsicConstructor,
        block: &mut Block,
    ) {
        block.assign(
            ret,
            Expr::BasicCall {
                args: Vec::new(),
                id: BasicFunction::IntrinsicConstruction(constructor_id),
            },
        );
    }

    pub fn new_local_variable(&mut self) -> LocalVariable {
        let t = self.type_map.new_pointer();
        self.local_variable_types.0.push(t);
        LocalVariable(self.local_variable_types.0.len() - 1)
    }

    pub fn new_block(&mut self) -> Block {
        Block::default()
    }

    pub fn set_global_variable(&mut self, d: VariableDecl) {
        self.global_variables_done.insert(d.decl_id, d);
    }

    pub fn new_constructor(&mut self, field_len: usize, name: String) -> ConstructorId {
        self.field_len.push(field_len);
        self.constructor_names.0.push(name);
        ConstructorId(self.field_len.len() - 1)
    }

    pub(crate) fn build(self, entry_point: GlobalVariable) -> Ast {
        let mut env_next = TypeInfEnv {
            type_map: self.type_map,
            global_variable_types: Default::default(),
            local_variable_types: self.local_variable_types,
            global_variables_before_type_inf: self.global_variables_done,
            trace: Default::default(),
            global_variables_done: Default::default(),
            field_len: self.field_len,
            used_local_variables: Default::default(),
            defined_local_variables: Default::default(),
            unreplicatable_pointers: Default::default(),
            unfixed_unreplicatable_pointers: Default::default(),
            unfixed_unreplicatable_pointer_in_local_variables: Default::default(),
        };
        let (type_of_entry_point, rec) = env_next.get_type_global(entry_point);
        debug_assert!(matches!(rec, IsRecursive::False { .. }));
        let (p, _, _) = env_next.type_map.get_fn(type_of_entry_point);
        env_next
            .type_map
            .insert_normal(p, TypeId::Intrinsic(IntrinsicTypeTag::Unit), Vec::new());
        let type_map = env_next.type_map;
        let local_variable_types_old = env_next.local_variable_types;
        Ast {
            variable_decls: env_next.global_variables_done,
            entry_point,
            type_of_entry_point,
            local_variable_types: local_variable_types_old,
            type_map,
            constructor_names: self.constructor_names,
        }
    }
}

impl Block {
    pub fn append(&mut self, mut other: Block) {
        self.instructions.append(&mut other.instructions);
    }

    fn assign(&mut self, v: LocalVariable, e: Expr) {
        self.instructions.push(Instruction::Assign(v, e));
    }

    pub fn test_string(&mut self, v: LocalVariable, value: String) {
        self.instructions
            .push(Instruction::Test(Tester::Str { value }, v));
    }

    pub fn test_number(&mut self, v: LocalVariable, value: String) {
        self.instructions
            .push(Instruction::Test(Tester::I64 { value }, v));
    }

    pub fn test_constructor(&mut self, v: LocalVariable, constructor: TypeId) {
        self.instructions.push(Instruction::Test(
            Tester::Constructor { id: constructor },
            v,
        ));
    }

    pub fn test_fail(&mut self) {
        self.instructions.push(Instruction::FailTest);
    }

    pub fn panic(&mut self, msg: String) {
        self.instructions.push(Instruction::Panic { msg });
    }

    pub fn try_catch(self, other: Block) -> Block {
        Block {
            instructions: vec![Instruction::TryCatch(self, other)],
        }
    }
}

impl<T: Debug> Display for LambdaId<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "f{}({:?})", self.id, self.root_t)
    }
}

impl From<LocalVariable> for VariableId {
    fn from(value: LocalVariable) -> Self {
        VariableId::Local(value)
    }
}

impl Display for LocalVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
