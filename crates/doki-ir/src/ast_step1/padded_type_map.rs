mod minimize;

pub use self::replace_map::ReplaceMap;
use super::{ConstructorId, LambdaId};
use crate::intrinsics::IntrinsicTypeTag;
use itertools::Itertools;
use rustc_hash::FxHashSet;
use std::collections::BTreeMap;
use std::fmt::Display;
use std::mem;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeId {
    UserDefined(ConstructorId),
    Intrinsic(IntrinsicTypeTag),
}

#[derive(Debug, PartialEq, Clone, Eq, PartialOrd, Ord, Copy, Hash)]
pub struct TypePointer(u32);

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord, Copy)]
pub enum TypeTagForBoxPoint {
    Normal(TypeId),
    Lambda(u32),
}

#[derive(Debug, PartialEq, Clone, Eq, PartialOrd, Ord, Hash, Default)]
pub enum BoxPoint {
    #[default]
    NotSure,
    Diverging,
    Boxed(BTreeMap<TypeTagForBoxPoint, Vec<Option<bool>>>),
}

#[derive(Debug, PartialEq, Clone, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Terminal {
    pub type_map: BTreeMap<TypeId, Vec<TypePointer>>,
    pub functions: Vec<(LambdaId<TypePointer>, Vec<TypePointer>)>,
    pub box_point: BoxPoint,
    /// Cloning is not allowed
    pub fixed: bool,
}

#[derive(Debug, PartialEq, Clone, Eq, PartialOrd, Ord, Hash)]
enum Node {
    Pointer(TypePointer),
    Terminal(Terminal),
    Null,
}

#[derive(Debug, Clone)]
pub struct PaddedTypeMap {
    map: Vec<Node>,
    pub minimize_types: bool,
    pub minimized_pointers: FxHashSet<TypePointer>,
}

impl PaddedTypeMap {
    pub fn new(minimize_types: bool) -> Self {
        Self {
            map: vec![Node::Null],
            minimize_types,
            minimized_pointers: Default::default(),
        }
    }
    pub fn new_pointer(&mut self) -> TypePointer {
        let p = self.map.len() as u32;
        self.map.push(Node::Terminal(Terminal::default()));
        TypePointer(p)
    }

    pub fn null_pointer() -> TypePointer {
        TypePointer(0)
    }

    pub fn union(&mut self, a: TypePointer, b: TypePointer) {
        let a = self.find(a);
        let b = self.find(b);
        let (a, b) = if a < b { (a, b) } else { (b, a) };
        if a != b {
            let b_t = mem::replace(&mut self.map[b.0 as usize], Node::Pointer(a));
            let mut pairs = Vec::new();
            let (Node::Terminal(a_t), Node::Terminal(b_t)) = (&mut self.map[a.0 as usize], b_t)
            else {
                panic!()
            };
            debug_assert_eq!(a_t.box_point, b_t.box_point);
            let fix_b = a_t.fixed && !b_t.fixed;
            let mut fix = Vec::new();
            for (b_id, b_normal) in b_t.type_map {
                if let Some(a_normal) = a_t.type_map.get(&b_id) {
                    for (a, b) in a_normal.iter().zip(b_normal) {
                        pairs.push((*a, b));
                    }
                } else {
                    debug_assert_eq!(b_t.box_point, BoxPoint::NotSure);
                    if fix_b {
                        fix.extend(&b_normal);
                    }
                    a_t.type_map.insert(b_id, b_normal.clone());
                }
            }
            if fix_b {
                fix.extend(b_t.functions.iter().flat_map(|(_, ps)| ps));
            }
            a_t.functions.extend(b_t.functions);
            let fix_a = !a_t.fixed && b_t.fixed;
            for (a, b) in pairs {
                self.union(a, b);
            }
            if fix_a {
                self.fix_pointer(a);
                debug_assert!(fix.is_empty());
            } else {
                for p in fix {
                    self.fix_pointer(p)
                }
            }
        }
    }

    pub fn insert_lambda_id(
        &mut self,
        p: TypePointer,
        id: LambdaId<TypePointer>,
        lambda_ctx: Vec<TypePointer>,
    ) {
        let t = self.dereference_mut(p);
        t.functions.push((id, lambda_ctx.clone()));
        if t.fixed {
            for p in lambda_ctx {
                self.fix_pointer(p)
            }
        }
    }

    pub fn insert_normal(&mut self, p: TypePointer, id: TypeId, args: Vec<TypePointer>) {
        let t = self.dereference_mut(p);
        if let Some(t) = t.type_map.get(&id) {
            for (a, b) in t.clone().into_iter().zip(args) {
                self.union(a, b);
            }
        } else {
            t.type_map.insert(id, args.clone());
            if t.fixed {
                for p in args {
                    self.fix_pointer(p)
                }
            }
        }
    }

    pub fn find(&mut self, p: TypePointer) -> TypePointer {
        let next_p = match &self.map[p.0 as usize] {
            Node::Pointer(p) => *p,
            Node::Terminal(_) => {
                return p;
            }
            Node::Null => panic!(),
        };
        let next_p = self.find(next_p);
        self.map[p.0 as usize] = Node::Pointer(next_p);
        debug_assert_ne!(p, next_p);
        next_p
    }

    pub fn is_terminal(&self, p: TypePointer) -> bool {
        matches!(self.map[p.0 as usize], Node::Terminal(_))
    }

    pub fn find_imm(&self, mut p: TypePointer) -> TypePointer {
        while let Node::Pointer(p_next) = self.map[p.0 as usize] {
            p = p_next;
        }
        debug_assert!(!matches!(self.map[p.0 as usize], Node::Null));
        p
    }

    pub fn get_fn(&mut self, p: TypePointer) -> (TypePointer, TypePointer) {
        let p = self.find(p);
        self.dereference_without_find(p)
            .type_map
            .get(&TypeId::Intrinsic(IntrinsicTypeTag::Fn))
            .map(|f| (f[0], f[1]))
            .unwrap_or_else(|| {
                let a = self.new_pointer();
                let b = self.new_pointer();
                self.insert_normal(p, TypeId::Intrinsic(IntrinsicTypeTag::Fn), vec![a, b]);
                (a, b)
            })
    }

    pub fn dereference(&mut self, p: TypePointer) -> &Terminal {
        let p = self.find(p);
        if let Node::Terminal(t) = &self.map[p.0 as usize] {
            t
        } else {
            panic!()
        }
    }

    pub fn dereference_imm(&self, p: TypePointer) -> &Terminal {
        let p = self.find_imm(p);
        if let Node::Terminal(t) = &self.map[p.0 as usize] {
            t
        } else {
            panic!()
        }
    }

    pub fn dereference_without_find(&self, p: TypePointer) -> &Terminal {
        if let Node::Terminal(t) = &self.map[p.0 as usize] {
            t
        } else {
            panic!()
        }
    }

    pub fn dereference_without_find_mut(&mut self, p: TypePointer) -> &mut Terminal {
        if let Node::Terminal(t) = &mut self.map[p.0 as usize] {
            t
        } else {
            panic!()
        }
    }

    fn dereference_mut(&mut self, p: TypePointer) -> &mut Terminal {
        let p = self.find(p);
        if let Node::Terminal(t) = &mut self.map[p.0 as usize] {
            t
        } else {
            panic!()
        }
    }

    pub fn clone_pointer(&mut self, p: TypePointer, replace_map: &mut ReplaceMap) -> TypePointer {
        let p = self.find(p);
        if self.dereference_without_find(p).fixed {
            return p;
        }
        if let Some(p) = replace_map.get(p, self) {
            return p;
        }
        let new_p = self.new_pointer();
        replace_map.insert(p, new_p);
        let t = self.dereference_without_find(p).clone();
        debug_assert_eq!(t.box_point, BoxPoint::NotSure);
        let type_map = t
            .type_map
            .into_iter()
            .map(|(id, t)| {
                let t = t
                    .iter()
                    .map(|p| self.clone_pointer(*p, replace_map))
                    .collect_vec();
                (id, t)
            })
            .collect();
        let functions = t
            .functions
            .into_iter()
            .map(|(LambdaId { id, root_t }, args)| {
                let args = args
                    .iter()
                    .map(|p| self.clone_pointer(*p, replace_map))
                    .collect_vec();
                (
                    LambdaId {
                        id,
                        root_t: self.clone_pointer(root_t, replace_map),
                    },
                    args,
                )
            })
            .collect();
        self.map[new_p.0 as usize] = Node::Terminal(Terminal {
            type_map,
            box_point: BoxPoint::NotSure,
            functions,
            fixed: false,
        });
        new_p
    }

    pub fn minimize(&mut self, root: TypePointer) {
        minimize::minimize(root, self)
    }

    pub fn fix_pointer(&mut self, p: TypePointer) {
        let terminal = &mut self.dereference_mut(p);
        if terminal.fixed {
            return;
        }
        terminal.fixed = true;
        let type_map = terminal.type_map.values().cloned().collect_vec();
        let functions = terminal.functions.clone();
        for ps in type_map {
            for p in ps {
                self.fix_pointer(p)
            }
        }
        for (id, ps) in functions {
            self.fix_pointer(id.root_t);
            for p in ps {
                self.fix_pointer(p)
            }
        }
    }

    #[cfg(debug_assertions)]
    pub fn json_debug(
        &self,
        f: &mut impl std::fmt::Write,
        p: TypePointer,
        visited_pointers: &FxHashSet<TypePointer>,
    ) -> Result<(), std::fmt::Error> {
        let mut visited_pointers = visited_pointers.clone();
        if visited_pointers.contains(&p) {
            return write!(f, r#"{{p:"{p}",type:rec}}"#);
        } else {
            visited_pointers.insert(p);
        }
        write!(f, r#"{{p:"{p}","#)?;
        match &self.map[p.0 as usize] {
            Node::Pointer(p2) => {
                write!(
                    f,
                    r#"pointer:{}}}"#,
                    JsonDebugRec(self, *p2, &visited_pointers)
                )
            }
            Node::Terminal(t) => {
                let m = t.type_map.iter().format_with(",", |(id, ps), f| {
                    f(&format_args!(
                        r#"{id}:[{}]"#,
                        ps.iter().format_with(",", |p, f| f(&JsonDebugRec(
                            self,
                            *p,
                            &visited_pointers
                        )))
                    ))
                });
                let n = t.functions.iter().format_with("", |(id, args), f| {
                    f(&format_args!(
                        r#",lambda:{{id:{},root_t:{},args:[{}]}}"#,
                        id.id,
                        JsonDebugRec(self, id.root_t, &visited_pointers),
                        args.iter().format_with(",", |p, f| f(&JsonDebugRec(
                            self,
                            *p,
                            &visited_pointers
                        )))
                    ))
                });
                let fixed = if t.fixed {
                    if t.type_map.is_empty() {
                        "fixed:true"
                    } else {
                        ",fixed:true"
                    }
                } else {
                    ""
                };
                write!(f, r#"type_map:{{{m}{n}{fixed}}}}}"#)
            }
            Node::Null => write!(f, r#"type:null}}"#),
        }
    }
}

#[cfg(debug_assertions)]
struct JsonDebugRec<'a>(
    pub &'a PaddedTypeMap,
    pub TypePointer,
    pub &'a FxHashSet<TypePointer>,
);

#[cfg(debug_assertions)]
impl Display for JsonDebugRec<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.json_debug(f, self.1, self.2)
    }
}

#[cfg(debug_assertions)]
pub struct JsonDebug<'a>(pub &'a PaddedTypeMap, pub TypePointer);

#[cfg(debug_assertions)]
impl Display for JsonDebug<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.json_debug(f, self.1, &FxHashSet::default())
    }
}

impl<T> LambdaId<T> {
    pub fn map_type<U>(self, mut f: impl FnMut(T) -> U) -> LambdaId<U> {
        LambdaId {
            id: self.id,
            root_t: f(self.root_t),
        }
    }

    pub fn map_type_ref<U>(&self, mut f: impl FnMut(&T) -> U) -> LambdaId<U> {
        LambdaId {
            id: self.id,
            root_t: f(&self.root_t),
        }
    }
}

impl Display for TypePointer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "p{}", self.0)
    }
}

mod replace_map {
    use super::{PaddedTypeMap, TypePointer};
    use rustc_hash::{FxHashMap, FxHashSet};

    #[derive(Debug, Default, Clone, PartialEq, Eq)]
    pub struct ReplaceMap {
        map: FxHashMap<TypePointer, TypePointer>,
        replaced: FxHashSet<TypePointer>,
    }

    impl ReplaceMap {
        pub fn merge(mut self, new: &Self, map: &mut PaddedTypeMap) -> Self {
            let mut new_map: FxHashMap<_, _> = new
                .map
                .iter()
                .map(|(from, to)| (*from, map.clone_pointer(*to, &mut self)))
                .collect();
            for (from, to) in self.map {
                let o = new_map.insert(from, to);
                debug_assert!(o.is_none());
            }
            Self {
                map: new_map,
                replaced: self.replaced,
            }
        }

        pub fn get(&mut self, p: TypePointer, map: &mut PaddedTypeMap) -> Option<TypePointer> {
            debug_assert!(map.is_terminal(p));
            if let Some(&p2) = self.map.get(&p) {
                #[cfg(debug_assertions)]
                {
                    assert!(!self.replaced.contains(&p));
                    let p2 = map.find(p2);
                    assert_ne!(p, p2);
                }
                let p2 = map.clone_pointer(p2, self);
                debug_assert_ne!(p, p2);
                self.map.insert(p, p2);
                Some(p2)
            } else if self.replaced.contains(&p) {
                Some(p)
            } else {
                None
            }
        }

        pub fn insert(&mut self, from: TypePointer, to: TypePointer) {
            debug_assert_ne!(from, to);
            let o = self.map.insert(from, to);
            debug_assert!(o.is_none());
            self.replaced.insert(to);
        }

        pub fn is_empty(&self) -> bool {
            self.map.is_empty() && self.replaced.is_empty()
        }
    }
}

impl Display for Terminal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.type_map.len() == 1 {
            let (id, args) = self.type_map.first_key_value().unwrap();
            write!(f, "{id}({})", args.iter().format(", "))
        } else {
            write!(
                f,
                "({})",
                self.type_map.iter().format_with(" | ", |(id, args), f| {
                    f(&format_args!("{id}({})", args.iter().format(", ")))
                })
            )
        }
    }
}

impl Display for TypeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeId::UserDefined(a) => write!(f, "{a}"),
            TypeId::Intrinsic(a) => write!(f, "{a:?}"),
        }
    }
}

impl Display for ConstructorId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "c{}", self.0)
    }
}
