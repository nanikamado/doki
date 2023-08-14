use super::{PaddedTypeMap, Terminal, TypePointer, TypeTag};
use crate::ast_step1::LambdaId;
use crate::util::dfa_minimization::Dfa;
use multimap::MultiMap;
use rustc_hash::{FxHashMap, FxHasher};

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
    points: &mut FxHashMap<TypePointer, u32>,
) {
    let p = map.find(p);
    if points.contains_key(&p) {
        return;
    }
    points.insert(p, 0);
    for (tag, ps) in map.dereference_without_find(p).type_map.clone() {
        if let TypeTag::Lambda(LambdaId { id: _, root_t }) = tag {
            collect_points(root_t, map, points)
        }
        for p in ps {
            collect_points(p, map, points)
        }
    }
}

impl Dfa for PaddedTypeMap {
    type Transition = Terminal;
    type Node = TypePointer;

    fn get(
        &self,
        node: Self::Node,
        points: &FxHashMap<<PaddedTypeMap as Dfa>::Node, u32>,
    ) -> Self::Transition {
        let t = self.dereference_without_find(node);
        let type_map = t
            .type_map
            .iter()
            .map(|(id, ps)| {
                let id = match id {
                    TypeTag::Normal(tag) => TypeTag::Normal(*tag),
                    TypeTag::Lambda(LambdaId { id, root_t }) => TypeTag::Lambda(LambdaId {
                        id: *id,
                        root_t: TypePointer(points[&self.find_imm(*root_t)]),
                    }),
                };
                let ps = ps
                    .iter()
                    .map(|p| TypePointer(points[&self.find_imm(*p)]))
                    .collect();
                (id, ps)
            })
            .collect();
        Terminal { type_map }
    }
}
