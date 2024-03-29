use rustc_hash::FxHashMap;
use std::marker::PhantomData;

#[derive(Clone, Copy)]
pub struct Id<T> {
    id: usize,
    phantom: PhantomData<T>,
}

#[derive(Debug)]
pub struct IdGenerator<T, U>(FxHashMap<T, Id<U>>);

impl<T: std::hash::Hash + Eq, U: Copy> IdGenerator<T, U> {
    pub fn get_or_insert(&mut self, value: T) -> Id<U> {
        let len = self.0.len();
        *self.0.entry(value).or_insert(Id {
            id: len,
            phantom: PhantomData,
        })
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
        Some(self.id.cmp(&other.id))
    }
}

impl<T> std::hash::Hash for Id<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl<T> std::fmt::Debug for Id<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.id)
    }
}
