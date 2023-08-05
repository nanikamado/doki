mod padded_type_map;

#[cfg(debug_assertions)]
pub use self::padded_type_map::JsonDebug;
pub use self::padded_type_map::{PaddedTypeMap, ReplaceMap, Terminal, TypeId, TypePointer};
use crate::intrinsics::{IntrinsicConstructor, IntrinsicTypeTag, IntrinsicVariable};
use crate::util::scc;
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use std::fmt::{Debug, Display};
use std::mem;

#[derive(Debug)]
pub struct Ast<'a> {
    pub variable_decls: Vec<VariableDecl<'a>>,
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
pub struct VariableDecl<'a> {
    pub value: Block,
    pub ret: LocalVariable,
    pub decl_id: GlobalVariable,
    pub name: &'a str,
}

#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct Block {
    pub instructions: Vec<Instruction>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Tester {
    Constructor { id: TypeId },
    I64 { value: i64 },
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
    I64(i64),
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

struct TypeInfEnv<'a> {
    type_map: PaddedTypeMap,
    unreplicatable_pointers: FxHashMap<GlobalVariable, UnreplicatablePointers>,
    local_variable_types: LocalVariableTypes,
    global_variables_before_type_inf: FxHashMap<GlobalVariable, VariableDecl<'a>>,
    global_variables: Vec<VariableDecl<'a>>,
    global_variable_types: FxHashMap<GlobalVariable, TypePointer>,
    field_len: Vec<usize>,
    used_local_variables: FxHashSet<LocalVariable>,
    defined_local_variables: FxHashSet<LocalVariable>,
    unreplicatable_pointers_of_current_scc: Vec<TypePointer>,
    unfixed_unreplicatable_pointers_in_local_variables: FxHashMap<LocalVariable, Vec<TypePointer>>,
    unfixed_unreplicatable_pointers_of_current_scc: Vec<TypePointer>,
    scc: FxHashMap<GlobalVariable, u32>,
    current_scc_id: u32,
}

struct UnreplicatablePointers {
    fixed: Vec<TypePointer>,
    unfixed: Vec<TypePointer>,
}

impl TypeInfEnv<'_> {
    fn get_type_global(&mut self, decl_id: GlobalVariable) {
        let mut d = self
            .global_variables_before_type_inf
            .remove(&decl_id)
            .unwrap();
        let root_t = self.global_variable_types[&decl_id];
        let unreplicatable_pointers_tmp =
            std::mem::take(&mut self.unreplicatable_pointers_of_current_scc);
        let unfixed_unreplicatable_pointers_tmp =
            std::mem::take(&mut self.unfixed_unreplicatable_pointers_of_current_scc);
        self.block(&mut d.value, root_t, true);
        let unreplicatable_pointers = std::mem::replace(
            &mut self.unreplicatable_pointers_of_current_scc,
            unreplicatable_pointers_tmp,
        );
        let unfixed_unreplicatable_pointers = std::mem::replace(
            &mut self.unfixed_unreplicatable_pointers_of_current_scc,
            unfixed_unreplicatable_pointers_tmp,
        );
        self.unreplicatable_pointers.insert(
            decl_id,
            UnreplicatablePointers {
                fixed: unreplicatable_pointers.clone(),
                unfixed: unfixed_unreplicatable_pointers.clone(),
            },
        );
        self.global_variables.push(d);
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
                                TypeId::Intrinsic(IntrinsicTypeTag::Ptr),
                                Vec::new(),
                            );
                        }
                        Expr::Ident(VariableId::Global(decl_id, replace_map, pp)) => {
                            debug_assert!(replace_map.is_empty());
                            let p = self.global_variable_types[decl_id];
                            if self.scc[decl_id] == self.current_scc_id {
                                // same scc
                                self.type_map.union(p, t);
                                *pp = p;
                            } else {
                                let unreplicatables =
                                    self.unreplicatable_pointers.get(decl_id).unwrap();
                                replace_map.add_unreplicatable(
                                    unreplicatables.fixed.iter().map(|p| self.type_map.find(*p)),
                                );
                                let v_cloned = self.type_map.clone_pointer(p, replace_map);
                                self.type_map.union(t, v_cloned);
                                *pp = t;
                                let mut unfixed = unreplicatables
                                    .unfixed
                                    .iter()
                                    .map(|p| self.type_map.clone_pointer(*p, replace_map))
                                    .collect_vec();
                                if !unfixed.is_empty() {
                                    self.unfixed_unreplicatable_pointers_in_local_variables
                                        .insert(*v, unfixed.clone());
                                }
                                self.unfixed_unreplicatable_pointers_of_current_scc
                                    .append(&mut unfixed);
                            }
                        }
                        Expr::Ident(VariableId::Local(d)) => {
                            self.used_local_variables.insert(*d);
                            let t2 = self.local_variable_types.get(*d);
                            self.type_map.union(t, t2);
                        }
                        Expr::Call { f, a } => {
                            if let Some(unfixed_unreplicatables) = self
                                .unfixed_unreplicatable_pointers_in_local_variables
                                .get(f)
                            {
                                if outside_of_fn {
                                    self.unreplicatable_pointers_of_current_scc
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
                                self.unreplicatable_pointers_of_current_scc
                                    .append(&mut p.clone())
                            }
                            self.unfixed_unreplicatable_pointers_of_current_scc
                                .append(&mut p);
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
pub struct Env<'a> {
    type_map: PaddedTypeMap,
    local_variable_types: LocalVariableTypes,
    lambda_count: u32,
    global_variable_count: usize,
    global_variables: FxHashMap<GlobalVariable, VariableDecl<'a>>,
    field_len: Vec<usize>,
    constructor_names: ConstructorNames,
}

impl<'a> Env<'a> {
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

    pub fn i64(&mut self, ret: LocalVariable, a: i64, block: &mut Block) {
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

    pub fn set_global_variable(&mut self, d: VariableDecl<'a>) {
        self.global_variables.insert(d.decl_id, d);
    }

    pub fn new_constructor(&mut self, field_len: usize, name: String) -> ConstructorId {
        self.field_len.push(field_len);
        self.constructor_names.0.push(name);
        ConstructorId(self.field_len.len() - 1)
    }

    pub(crate) fn build(self, entry_point: GlobalVariable) -> Ast<'a> {
        let scc_v = scc(entry_point, &self.global_variables);
        let mut scc = FxHashMap::default();
        for (i, c) in scc_v.iter().enumerate() {
            for v in c {
                scc.insert(*v, i as u32);
            }
        }
        let mut env_next = TypeInfEnv {
            type_map: self.type_map,
            unreplicatable_pointers: Default::default(),
            local_variable_types: self.local_variable_types,
            global_variables_before_type_inf: self.global_variables,
            global_variable_types: Default::default(),
            global_variables: Default::default(),
            field_len: self.field_len,
            used_local_variables: Default::default(),
            defined_local_variables: Default::default(),
            unreplicatable_pointers_of_current_scc: Default::default(),
            unfixed_unreplicatable_pointers_of_current_scc: Default::default(),
            unfixed_unreplicatable_pointers_in_local_variables: Default::default(),
            scc,
            current_scc_id: 0,
        };
        for c in scc_v.into_iter().rev() {
            env_next.current_scc_id = env_next.scc[&c[0]];
            for v in &c {
                let ret = env_next.global_variables_before_type_inf[v].ret;
                let t = env_next.local_variable_types.get(ret);
                env_next.global_variable_types.insert(*v, t);
            }
            for v in c {
                env_next.get_type_global(v);
            }
        }
        let type_of_entry_point = env_next.global_variable_types[&entry_point];
        let (p, _, _) = env_next.type_map.get_fn(type_of_entry_point);
        env_next
            .type_map
            .insert_normal(p, TypeId::Intrinsic(IntrinsicTypeTag::Unit), Vec::new());
        let type_map = env_next.type_map;
        let local_variable_types_old = env_next.local_variable_types;
        Ast {
            variable_decls: env_next.global_variables,
            entry_point,
            type_of_entry_point,
            local_variable_types: local_variable_types_old,
            type_map,
            constructor_names: self.constructor_names,
        }
    }
}

fn scc(
    entry_point: GlobalVariable,
    global_variables: &FxHashMap<GlobalVariable, VariableDecl>,
) -> Vec<Vec<GlobalVariable>> {
    let mut g = FxHashMap::default();
    let mut rg: FxHashMap<_, FxHashSet<_>> = FxHashMap::default();
    for v in global_variables.keys() {
        let mut ws = FxHashSet::default();
        global_variables[v].value.collect_global_variables(&mut ws);
        for w in &ws {
            rg.entry(*w).or_default().insert(*v);
        }
        g.insert(*v, ws);
    }
    rg.entry(entry_point).or_default();
    scc::scc(entry_point, &g, rg)
}

impl Block {
    fn collect_global_variables(&self, vs: &mut FxHashSet<GlobalVariable>) {
        for i in &self.instructions {
            match i {
                Instruction::Assign(_, e) => match e {
                    Expr::Lambda { body, .. } => body.collect_global_variables(vs),
                    Expr::Ident(VariableId::Global(v, _, _)) => {
                        vs.insert(*v);
                    }
                    _ => (),
                },
                Instruction::TryCatch(a, b) => {
                    a.collect_global_variables(vs);
                    b.collect_global_variables(vs);
                }
                _ => (),
            }
        }
    }

    pub fn append(&mut self, mut other: Block) {
        self.instructions.append(&mut other.instructions);
    }

    fn assign(&mut self, v: LocalVariable, e: Expr) {
        self.instructions.push(Instruction::Assign(v, e));
    }

    pub fn test_number(&mut self, v: LocalVariable, value: i64) {
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
