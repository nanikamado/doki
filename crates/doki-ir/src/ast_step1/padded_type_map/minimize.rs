use super::{PaddedTypeMap, Terminal, TypeMap, TypePointer};
use crate::ast_step1::LambdaId;
use crate::util::dfa_minimization::{Dfa, DfaTransition};
use multimap::MultiMap;
use rustc_hash::{FxHashMap, FxHashSet, FxHasher};

pub fn minimize(
    root: TypePointer,
    m: &mut PaddedTypeMap,
    minimized_pointers: &mut FxHashSet<TypePointer>,
) {
    let mut partitions = FxHashMap::default();
    collect_points(root, m, &mut partitions);
    let partitions = Dfa::split_partitions(m, partitions);
    let partitions_rev: MultiMap<_, _, std::hash::BuildHasherDefault<FxHasher>> =
        partitions.into_iter().map(|(a, b)| (b, a)).collect();
    for (_, mut v) in partitions_rev {
        v.sort_unstable();
        if v.len() >= 2 {
            let p = v[0];
            minimized_pointers.insert(p);
            for p2 in &v[1..] {
                m.union(p, *p2);
            }
        }
    }
}

fn collect_points(
    p: TypePointer,
    map: &mut PaddedTypeMap,
    points: &mut FxHashMap<TypePointer, usize>,
) {
    if points.contains_key(&p) {
        return;
    }
    let p = map.find(p);
    points.insert(p, 0);
    match map.dereference_without_find(p) {
        Terminal::TypeMap(t) => {
            for ps in t.normals.clone().values() {
                for p in ps {
                    collect_points(*p, map, points)
                }
            }
        }
        Terminal::LambdaId(ls) => {
            for (l, ctx) in ls.clone() {
                collect_points(l.root_t, map, points);
                for c in ctx {
                    collect_points(c, map, points);
                }
            }
        }
    }
}

impl Dfa for PaddedTypeMap {
    type Transition = Terminal;
    type Node = TypePointer;

    fn get(&self, node: Self::Node) -> &Self::Transition {
        self.dereference_without_find(node)
    }
}

impl DfaTransition for Terminal {
    type D = PaddedTypeMap;

    fn replace(&self, points: &FxHashMap<<Self::D as Dfa>::Node, usize>, map: &Self::D) -> Self {
        match self {
            Terminal::LambdaId(ls) => {
                let ls = ls
                    .iter()
                    .map(|(l, ctx)| {
                        let ctx = ctx
                            .iter()
                            .map(|p| TypePointer(points[&map.find_without_mut(*p)]))
                            .collect();
                        (
                            LambdaId {
                                id: l.id,
                                root_t: TypePointer(points[&map.find_without_mut(l.root_t)]),
                            },
                            ctx,
                        )
                    })
                    .collect();
                Terminal::LambdaId(ls)
            }
            Terminal::TypeMap(m) => {
                let normals = m
                    .normals
                    .iter()
                    .map(|(id, ps)| {
                        let ps = ps
                            .iter()
                            .map(|p| TypePointer(points[&map.find_without_mut(*p)]))
                            .collect();
                        (*id, ps)
                    })
                    .collect();
                Terminal::TypeMap(TypeMap { normals })
            }
        }
    }
}
