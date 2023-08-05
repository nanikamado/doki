use rustc_hash::FxHashMap;
use std::hash::Hash;
use std::ops::Index;

#[derive(Debug, Clone)]
pub struct Collector<T: Eq + Hash> {
    map: FxHashMap<T, usize>,
    map_rev: FxHashMap<usize, T>,
    len: usize,
}

impl<T: Eq + Hash + Clone> Collector<T> {
    pub fn get(&self, t: &T) -> Option<usize> {
        self.map.get(t).copied()
    }

    pub fn get_or_insert(&mut self, t: T) -> usize {
        if let Some(i) = self.map.get(&t) {
            *i
        } else {
            self.len += 1;
            let i = self.len - 1;
            self.map.insert(t.clone(), i);
            self.map_rev.insert(i, t);
            i
        }
    }

    pub fn get_empty_id(&mut self) -> usize {
        self.len += 1;
        self.len - 1
    }

    pub fn get_or_insert_with_id(&mut self, t: T, id: usize) -> usize {
        if let Some(i) = self.map.get(&t) {
            *i
        } else {
            self.map.insert(t.clone(), id);
            self.map_rev.insert(id, t);
            id
        }
    }

    pub fn contains(&self, t: &T) -> bool {
        self.map.contains_key(t)
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

    pub fn len(&self) -> usize {
        self.len
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

impl<T: Eq + Hash> Index<T> for Collector<T> {
    type Output = usize;

    fn index(&self, index: T) -> &Self::Output {
        &self.map[&index]
    }
}
