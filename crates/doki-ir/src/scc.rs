use rustc_hash::{FxHashMap, FxHashSet};

fn pre_sort<T: PartialOrd + Eq + std::hash::Hash + Copy>(
    v: T,
    g: &FxHashMap<T, FxHashSet<T>>,
    sorted: &mut Vec<T>,
    done: &mut FxHashSet<T>,
) {
    if !done.contains(&v) {
        done.insert(v);
        for v in &g[&v] {
            pre_sort(*v, g, sorted, done);
        }
        sorted.push(v);
    }
}

fn collect_scc<T: PartialOrd + Eq + std::hash::Hash + Copy>(
    v: T,
    rg: &mut FxHashMap<T, FxHashSet<T>>,
    c: &mut Vec<T>,
) {
    if let Some(ws) = rg.remove(&v) {
        c.push(v);
        for w in ws {
            collect_scc(w, rg, c);
        }
    }
}

pub fn scc<T: PartialOrd + Eq + std::hash::Hash + Copy>(
    entry_point: T,
    g: &FxHashMap<T, FxHashSet<T>>,
    mut rg: FxHashMap<T, FxHashSet<T>>,
) -> Vec<Vec<T>> {
    let mut sorted = Vec::new();
    pre_sort(entry_point, g, &mut sorted, &mut FxHashSet::default());
    let mut cs = Vec::new();
    for v in sorted.into_iter().rev() {
        if rg.contains_key(&v) {
            let mut c = Vec::new();
            collect_scc(v, &mut rg, &mut c);
            cs.push(c);
        }
    }
    cs
}

#[cfg(test)]
mod tests {
    use super::scc;
    use itertools::Itertools;
    use rustc_hash::{FxHashMap, FxHashSet};

    #[test]
    fn scc_1() {
        let mut g: FxHashMap<u32, FxHashSet<u32>> = FxHashMap::default();
        let mut rg: FxHashMap<u32, FxHashSet<u32>> = FxHashMap::default();
        for (v, w) in &[
            (0, 1),
            (1, 2),
            (2, 3),
            (3, 2),
            (3, 8),
            (8, 3),
            (9, 8),
            (3, 4),
            (4, 5),
            (5, 6),
            (6, 5),
            (5, 7),
            (7, 5),
            (7, 6),
            (6, 7),
        ] {
            g.entry(*v).or_default().insert(*w);
            rg.entry(*w).or_default().insert(*v);
        }
        rg.entry(0).or_default();
        let scc = scc(0, &g, rg)
            .into_iter()
            .map(|mut vs| {
                vs.sort_unstable();
                vs
            })
            .collect_vec();
        let correct: &[&[_]] = &[&[0], &[1], &[2, 3, 8], &[4], &[5, 6, 7]];
        let correct = correct
            .iter()
            .map(|vs| vs.iter().copied().collect_vec())
            .collect_vec();
        assert_eq!(scc, correct);
    }
}
