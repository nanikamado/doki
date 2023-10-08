use rustc_hash::FxHashMap;
use std::hash::Hash;
use std::ops::Index;

#[derive(Debug, Clone)]
pub struct Collector<T: Eq + Hash> {
    map: FxHashMap<T, usize>,
    len: usize,
}

impl<T: Eq + Hash + Clone> Collector<T> {
    pub fn get(&self, t: &T) -> Option<usize> {
        self.map.get(t).copied()
    }

    pub fn get_or_insert(&mut self, t: T) -> usize {
        *self.map.entry(t).or_insert_with(|| {
            let i = self.len;
            self.len += 1;
            i
        })
    }

    pub fn get_empty_id(&mut self) -> usize {
        self.len += 1;
        self.len - 1
    }

    pub fn get_or_insert_with_id(&mut self, t: T, id: usize) -> usize {
        if let Some(i) = self.map.get(&t) {
            *i
        } else {
            self.map.insert(t, id);
            id
        }
    }

    pub fn contains(&self, t: &T) -> bool {
        self.map.contains_key(t)
    }

    pub fn as_raw(&self) -> &FxHashMap<T, usize> {
        &self.map
    }

    pub fn len(&self) -> usize {
        self.len
    }
}

impl<T: Eq + Hash> Default for Collector<T> {
    fn default() -> Self {
        Self {
            map: Default::default(),
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
