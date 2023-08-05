use itertools::Itertools;
use rustc_hash::FxHashMap;
use std::fmt::Debug;
use std::hash::Hash;

pub trait Dfa: Sized {
    type Transition: Hash + Eq + Debug;
    type Node: Hash + Eq + Copy + Debug;

    fn get(&self, node: Self::Node, points: &FxHashMap<Self::Node, usize>) -> Self::Transition;

    fn split_partitions(
        &mut self,
        mut partition: FxHashMap<Self::Node, usize>,
    ) -> (
        FxHashMap<Self::Node, usize>,
        FxHashMap<Self::Transition, usize>,
    ) {
        let nodes = partition.keys().copied().collect_vec();
        let mut collector_len = 1;
        let mut collector =
            FxHashMap::with_capacity_and_hasher(partition.len(), Default::default());
        let mut next_partition =
            FxHashMap::with_capacity_and_hasher(partition.len(), Default::default());
        loop {
            next_partition.clear();
            collector.clear();
            for i in &nodes {
                let s = self.get(*i, &partition);
                let collector_len = collector.len();
                let new_i = *collector.entry(s).or_insert(collector_len);
                next_partition.insert(*i, new_i);
            }
            std::mem::swap(&mut partition, &mut next_partition);
            if collector_len == collector.len() {
                debug_assert_eq!(partition, next_partition);
                break;
            } else {
                collector_len = collector.len();
            }
        }
        (partition, collector)
    }
}
