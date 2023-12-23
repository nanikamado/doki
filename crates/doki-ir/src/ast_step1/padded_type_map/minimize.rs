use super::{BoxPoint, PaddedTypeMap, TypePointer};
use crate::util::dfa_minimization::Dfa;
use crate::TypeId;
use multimap::MultiMap;
use rustc_hash::{FxHashMap, FxHasher};
use std::collections::BTreeMap;

pub fn minimize(root: TypePointer, m: &mut PaddedTypeMap) {
    let root = m.find(root);
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
                    m.union_without_insertion(p, *p2);
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
    points: &mut FxHashMap<TypePointer, u32>,
) {
    let p = map.find(p);
    if points.contains_key(&p) {
        return;
    }
    points.insert(p, 0);
    let terminal = map.dereference_without_find(p);
    let type_map = terminal.type_map.clone();
    for (_, ps) in type_map {
        for p in ps {
            collect_points(p, map, points)
        }
    }
}

#[derive(Debug, PartialEq, Clone, Eq, PartialOrd, Ord, Hash)]
pub struct TerminalRef<'a> {
    pub type_map: BTreeMap<TypeId, Vec<TypePointer>>,
    pub reference_point: &'a BoxPoint,
    pub fixed: bool,
}

impl Dfa for PaddedTypeMap {
    type Transition<'a> = TerminalRef<'a>;
    type Node = TypePointer;

    fn get<'a>(
        &'a self,
        node: Self::Node,
        points: &FxHashMap<<PaddedTypeMap as Dfa>::Node, u32>,
    ) -> Self::Transition<'a> {
        let t = self.dereference_without_find(node);
        let type_map = t
            .type_map
            .iter()
            .map(|(id, ps)| {
                let ps = ps
                    .iter()
                    .map(|p| TypePointer(points[&self.find_imm(*p)]))
                    .collect();
                (*id, ps)
            })
            .collect();
        TerminalRef {
            type_map,
            reference_point: &t.box_point,
            fixed: t.fixed,
        }
    }
}
