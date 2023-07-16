use rustc_hash::FxHashMap;
use std::hash::Hash;

#[derive(Debug, Clone)]
pub struct Collector<T: Eq + Hash> {
    map: FxHashMap<T, usize>,
    map_rev: FxHashMap<usize, T>,
    len: usize,
}

impl<T: Eq + Hash + Clone> Collector<T> {
    pub fn get(&self, t: T) -> usize {
        self.map[&t]
    }

    pub fn get_or_insert(&mut self, t: T) -> usize {
        *self.map.entry(t.clone()).or_insert_with(|| {
            self.len += 1;
            let i = self.len - 1;
            self.map_rev.insert(i, t);
            i
        })
    }

    pub fn get_empty_id(&mut self) -> usize {
        self.len += 1;
        self.len - 1
    }

    pub fn get_or_insert_with_id(&mut self, t: T, id: usize) -> usize {
        *self.map.entry(t.clone()).or_insert_with(|| {
            self.map_rev.insert(id, t);
            id
        })
    }

    pub fn get_rev(&self, id: usize) -> Option<&T> {
        self.map_rev.get(&id)
    }

    pub fn as_raw(&self) -> &FxHashMap<T, usize> {
        &self.map
    }

    pub fn rev_map_as_raw(&self) -> &FxHashMap<usize, T> {
        &self.map_rev
    }
}

impl<T: Eq + Hash> Default for Collector<T> {
    fn default() -> Self {
        Self {
            map: Default::default(),
            map_rev: Default::default(),
            len: 0,
        }
    }
}
