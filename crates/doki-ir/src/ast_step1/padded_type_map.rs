mod minimize;

pub use self::replace_map::ReplaceMap;
use super::{ConstructorId, LambdaId};
use crate::intrinsics::IntrinsicTypeTag;
use itertools::Itertools;
#[cfg(debug_assertions)]
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
pub struct TypePointer(usize);

#[derive(Debug, PartialEq, Clone, Default, Eq, PartialOrd, Ord, Hash)]
pub struct TypeMap {
    pub normals: BTreeMap<TypeId, Vec<TypePointer>>,
}

#[derive(Debug, PartialEq, Clone, Eq, PartialOrd, Ord, Hash)]
pub enum Terminal {
    TypeMap(TypeMap),
    LambdaId(BTreeMap<LambdaId<TypePointer>, Vec<TypePointer>>),
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
}

impl Default for PaddedTypeMap {
    fn default() -> Self {
        Self {
            map: vec![Node::Null],
        }
    }
}

impl PaddedTypeMap {
    pub fn new_pointer(&mut self) -> TypePointer {
        let p = self.map.len();
        self.map
            .push(Node::Terminal(Terminal::TypeMap(TypeMap::default())));
        TypePointer(p)
    }

    pub fn null_pointer() -> TypePointer {
        TypePointer(0)
    }

    pub fn new_lambda_id_pointer(&mut self) -> TypePointer {
        let p = self.map.len();
        self.map
            .push(Node::Terminal(Terminal::LambdaId(BTreeMap::default())));
        TypePointer(p)
    }

    pub fn union(&mut self, a: TypePointer, b: TypePointer) {
        let a = self.find(a);
        let b = self.find(b);
        let (a, b) = if a < b { (a, b) } else { (b, a) };
        if a != b {
            let b_t = mem::replace(&mut self.map[b.0], Node::Pointer(a));
            let mut pairs = Vec::new();
            if let (Node::Terminal(a_t), Node::Terminal(b_t)) = (&mut self.map[a.0], b_t) {
                match (a_t, b_t) {
                    (Terminal::TypeMap(a_t), Terminal::TypeMap(b_t)) => {
                        for (b_id, b_normal) in b_t.normals {
                            if let Some(a_normal) = a_t.normals.get(&b_id) {
                                for (a, b) in a_normal.iter().zip(b_normal) {
                                    pairs.push((*a, b));
                                }
                            } else {
                                a_t.normals.insert(b_id, b_normal);
                            }
                        }
                    }
                    (Terminal::LambdaId(a), Terminal::LambdaId(b)) => a.extend(b),
                    _ => panic!(),
                }
            } else {
                panic!()
            };
            for (a, b) in pairs {
                self.union(a, b);
            }
        }
    }

    pub fn insert_function(
        &mut self,
        p: TypePointer,
        arg: TypePointer,
        ret: TypePointer,
        fn_id: TypePointer,
    ) {
        debug_assert!(matches!(self.dereference(fn_id), Terminal::LambdaId(_)));
        let t = self.dereference_mut(p);
        let Terminal::TypeMap(t) = t else {
            panic!()
        };
        if let Some(f) = t.normals.get(&TypeId::Intrinsic(IntrinsicTypeTag::Fn)) {
            let f_0 = f[0];
            let f_1 = f[1];
            let f_2 = f[2];
            self.union(f_0, arg);
            self.union(f_1, ret);
            self.union(f_2, fn_id);
        } else {
            t.normals.insert(
                TypeId::Intrinsic(IntrinsicTypeTag::Fn),
                vec![arg, ret, fn_id],
            );
        }
    }

    pub fn insert_lambda_id(
        &mut self,
        p: TypePointer,
        id: LambdaId<TypePointer>,
        lambda_ctx: Vec<TypePointer>,
    ) {
        let t = self.dereference_mut(p);
        let Terminal::LambdaId(t) = t else {
            panic!()
        };
        t.insert(id, lambda_ctx);
    }

    pub fn get_lambda_id(
        &mut self,
        p: TypePointer,
    ) -> &BTreeMap<LambdaId<TypePointer>, Vec<TypePointer>> {
        let t = self.dereference(p);
        let Terminal::LambdaId(t) = t else {
            panic!()
        };
        t
    }

    pub fn insert_normal(&mut self, p: TypePointer, id: TypeId, args: Vec<TypePointer>) {
        let t = self.dereference_mut(p);
        let Terminal::TypeMap(t) = t else {
            panic!()
        };
        if let Some(t) = t.normals.get(&id) {
            for (a, b) in t.clone().into_iter().zip(args) {
                self.union(a, b);
            }
        } else {
            t.normals.insert(id, args);
        }
    }

    pub fn find(&mut self, p: TypePointer) -> TypePointer {
        let next_p = match &self.map[p.0] {
            Node::Pointer(p) => *p,
            Node::Terminal(_) => {
                return p;
            }
            Node::Null => panic!(),
        };
        let next_p = self.find(next_p);
        self.map[p.0] = Node::Pointer(next_p);
        debug_assert_ne!(p, next_p);
        next_p
    }

    pub fn get_fn(&mut self, p: TypePointer) -> (TypePointer, TypePointer, TypePointer) {
        let p = self.find(p);
        if let Terminal::TypeMap(t) = &self.dereference_without_find(p) {
            t.normals
                .get(&TypeId::Intrinsic(IntrinsicTypeTag::Fn))
                .map(|f| (f[0], f[1], f[2]))
        } else {
            panic!()
        }
        .unwrap_or_else(|| {
            let a = self.new_pointer();
            let b = self.new_pointer();
            let fn_id = self.new_lambda_id_pointer();
            self.insert_function(p, a, b, fn_id);
            (a, b, fn_id)
        })
    }

    pub fn dereference(&mut self, p: TypePointer) -> &Terminal {
        let p = self.find(p);
        if let Node::Terminal(t) = &self.map[p.0] {
            t
        } else {
            panic!()
        }
    }

    pub fn dereference_without_find(&self, p: TypePointer) -> &Terminal {
        if let Node::Terminal(t) = &self.map[p.0] {
            t
        } else {
            panic!()
        }
    }

    fn dereference_mut(&mut self, p: TypePointer) -> &mut Terminal {
        let p = self.find(p);
        if let Node::Terminal(t) = &mut self.map[p.0] {
            t
        } else {
            panic!()
        }
    }

    pub fn clone_pointer(&mut self, p: TypePointer, replace_map: &mut ReplaceMap) -> TypePointer {
        let p = self.find(p);
        if let Some(p) = replace_map.get(p, self) {
            return p;
        }
        let new_p = self.new_pointer();
        replace_map.insert(p, new_p);
        let t = self.dereference_without_find(p).clone();
        let t = match t {
            Terminal::TypeMap(t) => Terminal::TypeMap(TypeMap {
                normals: t
                    .normals
                    .iter()
                    .map(|(id, t)| {
                        (
                            *id,
                            t.iter()
                                .map(|p| self.clone_pointer(*p, replace_map))
                                .collect(),
                        )
                    })
                    .collect(),
            }),
            Terminal::LambdaId(t) => Terminal::LambdaId(
                t.into_iter()
                    .map(|(t, ctx)| {
                        (
                            LambdaId {
                                id: t.id,
                                root_t: self.clone_pointer(t.root_t, replace_map),
                            },
                            ctx.into_iter()
                                .map(|c| self.clone_pointer(c, replace_map))
                                .collect(),
                        )
                    })
                    .collect(),
            ),
        };
        self.map[new_p.0] = Node::Terminal(t);
        new_p
    }

    pub fn minimize(&mut self, root: TypePointer, minimized_pointers: &mut FxHashSet<TypePointer>) {
        minimize::minimize(root, self, minimized_pointers)
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
            return write!(f, r#"{{"p":"{p}","type":"rec"}}"#);
        } else {
            visited_pointers.insert(p);
        }
        write!(f, r#"{{"p":"{p}","#)?;
        match &self.map[p.0] {
            Node::Pointer(p2) => {
                write!(
                    f,
                    r#""type":"pointer","v":{}}}"#,
                    JsonDebugRec(self, *p2, &visited_pointers)
                )
            }
            Node::Terminal(t) => match t {
                Terminal::TypeMap(m) => {
                    let m = m.normals.iter().format_with(",", |(tag, ps), f| {
                        f(&format_args!(
                            r#""{tag}":[{}]"#,
                            ps.iter().format_with(",", |p, f| f(&JsonDebugRec(
                                self,
                                *p,
                                &visited_pointers
                            )))
                        ))
                    });
                    write!(f, r#""type":"type_map","v":{{{}}}}}"#, m)
                }
                Terminal::LambdaId(ls) => {
                    write!(
                        f,
                        r#""type":"lambda_id","v":[{}]}}"#,
                        ls.iter().format_with(",", |(l, ctx), f| f(&format_args!(
                            r#"{{id:{},root_t:{},ctx:[{}]}}"#,
                            l.id,
                            JsonDebugRec(self, l.root_t, &visited_pointers),
                            ctx.iter().format_with(",", |c, f| f(&JsonDebugRec(
                                self,
                                *c,
                                &visited_pointers
                            )))
                        )))
                    )
                }
            },
            Node::Null => write!(f, r#""type":"null"}}"#),
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
        pub fn merge(mut self, new: Self, map: &mut PaddedTypeMap) -> Self {
            let mut new_map: FxHashMap<_, _> = new
                .map
                .into_iter()
                .map(|(from, to)| (from, map.clone_pointer(to, &mut self)))
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
            if let Some(p2) = self.map.get(&p) {
                debug_assert!(!self.replaced.contains(&p));
                let p2 = map.clone_pointer(*p2, self);
                self.map.insert(p, p2);
                Some(p2)
            } else if self.replaced.contains(&p) {
                Some(p)
            } else {
                None
            }
        }

        pub fn insert(&mut self, from: TypePointer, to: TypePointer) {
            let o = self.map.insert(from, to);
            debug_assert!(o.is_none());
            self.replaced.insert(to);
        }

        pub fn is_empty(&self) -> bool {
            self.map.is_empty() && self.replaced.is_empty()
        }

        pub fn add_unreplicatable(&mut self, i: impl IntoIterator<Item = TypePointer>) {
            self.replaced.extend(i)
        }
    }
}

impl Display for Terminal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Terminal::TypeMap(tm) => {
                if tm.normals.len() == 1 {
                    let (id, args) = tm.normals.first_key_value().unwrap();
                    write!(f, "{id}({})", args.iter().format(", "))
                } else {
                    write!(
                        f,
                        "({})",
                        tm.normals.iter().format_with(" | ", |(id, args), f| {
                            f(&format_args!("{id}({})", args.iter().format(", ")))
                        })
                    )
                }
            }
            Terminal::LambdaId(l) => {
                write!(f, "lambda({})", l.keys().format(" | "))
            }
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
