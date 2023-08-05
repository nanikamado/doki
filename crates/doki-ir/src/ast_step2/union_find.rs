use rustc_hash::FxHashMap;
use std::hash::Hash;

#[derive(Debug)]
pub struct UnionFind<T>(FxHashMap<T, T>);

impl<T: Hash + Eq + Ord + Copy> UnionFind<T> {
    pub fn find(&mut self, v: T) -> T {
        if let Some(n) = self.0.get(&v) {
            let w = self.find(*n);
            self.0.insert(v, w);
            w
        } else {
            v
        }
    }

    pub fn union(&mut self, a: T, b: T) {
        let a = self.find(a);
        let b = self.find(b);
        match a.cmp(&b) {
            std::cmp::Ordering::Less => {
                self.0.insert(b, a);
            }
            std::cmp::Ordering::Equal => (),
            std::cmp::Ordering::Greater => {
                self.0.insert(a, b);
            }
        }
    }

    pub fn contains(&self, v: T) -> bool {
        self.0.contains_key(&v)
    }
}

impl<T> Default for UnionFind<T> {
    fn default() -> Self {
        Self(Default::default())
    }
}
