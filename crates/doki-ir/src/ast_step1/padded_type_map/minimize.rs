use super::{PaddedTypeMap, Terminal, TypeMap, TypePointer};
use crate::ast_step1::LambdaId;
use multimap::MultiMap;
use rustc_hash::{FxHashMap, FxHashSet, FxHasher};

pub fn minimize(
    root: TypePointer,
    m: &mut PaddedTypeMap,
    minimized_pointers: &mut FxHashSet<TypePointer>,
) {
    let mut points = FxHashMap::default();
    collect_points(root, m, &mut points);
    let mut collector_len = 1;
    let mut collector = FxHashMap::default();
    loop {
        let mut next_points = FxHashMap::default();
        collector.clear();
        for i in points.keys() {
            let s = m
                .dereference_without_find(TypePointer(*i))
                .replace(&points, m);
            let collector_len = collector.len();
            let new_i = *collector.entry(s).or_insert(collector_len);
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

fn collect_points(p: TypePointer, map: &mut PaddedTypeMap, points: &mut FxHashMap<usize, usize>) {
    if points.contains_key(&p.0) {
        return;
    }
    let p = map.find(p);
    points.insert(p.0, 0);
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

impl Terminal {
    fn replace(&self, points: &FxHashMap<usize, usize>, map: &PaddedTypeMap) -> Self {
        match self {
            Terminal::LambdaId(ls) => {
                let ls = ls
                    .iter()
                    .map(|(l, ctx)| {
                        let ctx = ctx
                            .iter()
                            .map(|p| TypePointer(points[&map.find_without_mut(*p).0]))
                            .collect();
                        (
                            LambdaId {
                                id: l.id,
                                root_t: TypePointer(points[&map.find_without_mut(l.root_t).0]),
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
                            .map(|p| TypePointer(points[&map.find_without_mut(*p).0]))
                            .collect();
                        (*id, ps)
                    })
                    .collect();
                Terminal::TypeMap(TypeMap { normals })
            }
        }
    }
}
