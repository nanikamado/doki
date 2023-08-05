use rustc_hash::FxHashMap;
use std::hash::Hash;

pub trait Dfa {
    type Transition: DfaTransition<D = Self> + Hash + Eq;
    type Node: Hash + Eq + Copy;

    fn get(&self, node: Self::Node) -> &Self::Transition;

    fn split_partitions(
        &mut self,
        mut partition: FxHashMap<Self::Node, usize>,
    ) -> FxHashMap<Self::Node, usize> {
        let mut collector_len = 1;
        let mut collector = FxHashMap::default();
        loop {
            let mut next_points = FxHashMap::default();
            collector.clear();
            for i in partition.keys() {
                let s = self.get(*i).replace(&partition, self);
                let collector_len = collector.len();
                let new_i = *collector.entry(s).or_insert(collector_len);
                next_points.insert(*i, new_i);
            }
            if collector_len == collector.len() {
                break;
            } else {
                partition = next_points;
                collector_len = collector.len();
            }
        }
        partition
    }
}

pub trait DfaTransition {
    type D: Dfa;

    fn replace(&self, points: &FxHashMap<<Self::D as Dfa>::Node, usize>, dfa: &Self::D) -> Self;
}
