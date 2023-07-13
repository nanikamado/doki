use super::{Node, PaddedTypeMap, Terminal, TypeMap, TypePointer};
use crate::ast_step1::LambdaId;
use multimap::MultiMap;
use rustc_hash::{FxHashMap, FxHashSet, FxHasher};

pub fn minimize(
    root: TypePointer,
    m: &mut PaddedTypeMap,
    minimized_pointers: &mut FxHashSet<TypePointer>,
) {
    let map = m
        .map
        .clone()
        .into_iter()
        .map(|n| match n {
            Node::Terminal(Terminal::TypeMap(t)) => {
                let normals = t
                    .normals
                    .into_iter()
                    .map(|(id, ps)| {
                        let ps = ps.into_iter().map(|p| m.find(p)).collect();
                        (id, ps)
                    })
                    .collect();
                Node::Terminal(Terminal::TypeMap(TypeMap { normals }))
            }
            Node::Terminal(Terminal::LambdaId(ls)) => {
                let ls = ls
                    .into_iter()
                    .map(|(l, ctx)| {
                        (
                            LambdaId {
                                id: l.id,
                                root_t: m.find(l.root_t),
                            },
                            ctx.into_iter().map(|c| m.find(c)).collect(),
                        )
                    })
                    .collect();
                Node::Terminal(Terminal::LambdaId(ls))
            }
            a => a,
        })
        .collect();
    let refined_m = PaddedTypeMap { map };
    let mut points = FxHashMap::default();
    collect_points(root, &refined_m, &mut points);
    let mut collector_len = 1;
    let mut collector = FxHashMap::default();
    loop {
        let mut next_points = FxHashMap::default();
        collector.clear();
        for i in points.keys() {
            let s = refined_m.map[*i].replace(&points);
            use std::collections::hash_map::Entry::*;
            let collector_len = collector.len();
            let new_i = match collector.entry(s) {
                Occupied(e) => *e.get(),
                Vacant(e) => {
                    e.insert(collector_len);
                    collector_len
                }
            };
            next_points.insert(*i, new_i);
        }
        if collector_len == collector.len() {
            break;
        } else {
            points = next_points;
            collector_len = collector.len();
        }
    }
    let points_rev: MultiMap<_, _, std::hash::BuildHasherDefault<FxHasher>> =
        points.into_iter().map(|(a, b)| (b, a)).collect();
    for (_, mut v) in points_rev {
        v.sort_unstable();
        if v.len() >= 2 {
            let p = TypePointer(v[0]);
            minimized_pointers.insert(p);
            for p2 in &v[1..] {
                m.union(p, TypePointer(*p2));
            }
        }
    }
}

fn collect_points(p: TypePointer, map: &PaddedTypeMap, points: &mut FxHashMap<usize, usize>) {
    if points.contains_key(&p.0) {
        return;
    }
    match &map.map[p.0] {
        Node::Pointer(p) => collect_points(*p, map, points),
        Node::Terminal(t) => {
            points.insert(p.0, 0);
            match t {
                Terminal::TypeMap(t) => {
                    for ps in t.normals.values() {
                        for p in ps {
                            collect_points(*p, map, points)
                        }
                    }
                }
                Terminal::LambdaId(ls) => {
                    for (l, ctx) in ls {
                        collect_points(l.root_t, map, points);
                        for c in ctx {
                            collect_points(*c, map, points);
                        }
                    }
                }
            }
        }
        Node::Null => panic!(),
    }
}

impl Node {
    fn replace(&self, points: &FxHashMap<usize, usize>) -> Self {
        match self {
            Node::Terminal(Terminal::LambdaId(ls)) => {
                let ls = ls
                    .iter()
                    .map(|(l, ctx)| {
                        let ctx = ctx.iter().map(|p| TypePointer(points[&p.0])).collect();
                        (
                            LambdaId {
                                id: l.id,
                                root_t: TypePointer(points[&l.root_t.0]),
                            },
                            ctx,
                        )
                    })
                    .collect();
                Node::Terminal(Terminal::LambdaId(ls))
            }
            Node::Terminal(Terminal::TypeMap(m)) => {
                let normals = m
                    .normals
                    .iter()
                    .map(|(id, ps)| {
                        let ps = ps.iter().map(|p| TypePointer(points[&p.0])).collect();
                        (*id, ps)
                    })
                    .collect();
                Node::Terminal(Terminal::TypeMap(TypeMap { normals }))
            }
            Node::Null | Node::Pointer(_) => panic!(),
        }
    }
}
