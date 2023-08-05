use super::{PaddedTypeMap, Terminal, TypeMap, TypePointer};
use crate::ast_step1::LambdaId;
use crate::util::dfa_minimization::Dfa;
use multimap::MultiMap;
use rustc_hash::{FxHashMap, FxHasher};

pub fn minimize(root: TypePointer, m: &mut PaddedTypeMap) {
    if m.minimize_types && !m.minimized_pointers.contains(&root) {
        let mut partitions = FxHashMap::default();
        collect_points(root, m, &mut partitions);
        let partitions = Dfa::split_partitions(m, partitions).0;
        let partitions_rev: MultiMap<_, _, std::hash::BuildHasherDefault<FxHasher>> =
            partitions.into_iter().map(|(a, b)| (b, a)).collect();
        for (_, mut v) in partitions_rev {
            v.sort_unstable();
            if v.len() >= 2 {
                let p = v[0];
                for p2 in &v[1..] {
                    m.union(p, *p2);
                }
            }
            let p = v[0];
            m.minimized_pointers.insert(p);
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

    fn get(
        &self,
        node: Self::Node,
        points: &FxHashMap<<PaddedTypeMap as Dfa>::Node, usize>,
    ) -> Self::Transition {
        let t = self.dereference_without_find(node);
        match t {
            Terminal::LambdaId(ls) => {
                let ls = ls
                    .iter()
                    .map(|(l, ctx)| {
                        let ctx = ctx
                            .iter()
                            .map(|p| TypePointer(points[&self.find_imm(*p)]))
                            .collect();
                        (
                            LambdaId {
                                id: l.id,
                                root_t: TypePointer(points[&self.find_imm(l.root_t)]),
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
                            .map(|p| TypePointer(points[&self.find_imm(*p)]))
                            .collect();
                        (*id, ps)
                    })
                    .collect();
                Terminal::TypeMap(TypeMap { normals })
            }
        }
    }
}
