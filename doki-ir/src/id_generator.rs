use rustc_hash::FxHashMap;
use std::marker::PhantomData;

#[derive(Debug, Clone, Copy)]
pub struct Id<T> {
    id: usize,
    phantom: PhantomData<T>,
}

#[derive(Debug)]
pub struct IdGenerator<T, U>(FxHashMap<T, Id<U>>);

impl<T: std::hash::Hash + Eq, U: Copy> IdGenerator<T, U> {
    pub fn get(&mut self, value: T) -> Id<U> {
        use std::collections::hash_map::Entry::*;
        let len = self.0.len();
        match self.0.entry(value) {
            Occupied(e) => *e.get(),
            Vacant(e) => *e.insert(Id {
                id: len,
                phantom: PhantomData,
            }),
        }
    }
}

impl<T, U> Default for IdGenerator<T, U> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<T> PartialEq for Id<T> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<T> Eq for Id<T> {}

impl<T> Ord for Id<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

impl<T> PartialOrd for Id<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.id.partial_cmp(&other.id)
    }
}

impl<T> std::hash::Hash for Id<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}
