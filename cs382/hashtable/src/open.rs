use std::mem;
use std::hash::{Hash, Hasher, BuildHasher};
use std::collections::hash_map::RandomState;

use capacity::close_prime;

enum Entry<K, V> {
    Empty,
    Deleted,
    Item { key: K, value: V }
}

pub struct HashMap<K, V> {
    /// This makes the table more resistant to DOS attacks by introducing
    /// random state into the HashMap.
    hash_state: RandomState,
    /// This is also named m, must be prime
    capacity:   usize,
    /// Number of elements in table
    length:     usize,
    vec:        Vec<Entry<K, V>>
}

impl<K, V> HashMap<K, V>
    where
    K: Eq + Hash,
{
    pub fn new() -> Self {
        HashMap::with_capacity(11)
    }

    pub fn with_capacity(lower_bound: usize) -> Self {
        let capacity = close_prime(lower_bound);
        let vec = (0..capacity).map(|_| Entry::Empty).collect();
        HashMap {
            hash_state: RandomState::new(),
            capacity,
            length: 0,
            vec
        }
    }

    fn hash(&self, key: &K, t: usize) -> usize {
        let mut hasher = self.hash_state.build_hasher();
        key.hash(&mut hasher);
        let hash = hasher.finish() as usize;
        let h1 = hash % self.capacity;
        let h2 = (1 + hash) % (self.capacity - 1);
        (h1 + t * h2) % self.capacity
    }


    fn resize(&mut self) {
        let old_capacity = self.capacity;
        let old = mem::replace(self, HashMap::with_capacity(2 * old_capacity));
        for entry in old.vec {
            match entry {
                Entry::Empty => {}
                Entry::Deleted => {}
                Entry::Item { key, value } => {
                    self.insert(key, value);
                }
            }
        }
    }


    /// Determines if the load factor is too high
    fn should_resize(&self) -> bool {
        const THRESHOLD : f64 = 0.3;
        THRESHOLD < self.length as f64 / self.capacity as f64
    }

    /// Inserts the key-value pair into the map
    /// If the map had a value at that key the old key is returned
    /// INSERT + UPDATE
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        if self.should_resize() {
            self.resize()
        }
        let mut ret = None;
        for t in 0 .. self.capacity {
            let hash = self.hash(&key, t);
            let e = &mut self.vec[hash];
            match *e {
                Entry::Empty => {
                    *e = Entry::Item { key, value };
                    break
                }
                Entry::Deleted => {
                    *e = Entry::Item { key, value };
                    break
                }
                Entry::Item { key: ref cur_key, value: ref mut cur_value } => {
                    if *cur_key == key {
                        let old_value = mem::replace(cur_value, value);
                        ret = Some(old_value);
                        break
                    }
                }
            }
        }
        if ret.is_none() {
            self.length += 1;
        }
        ret
    }

    /// Looks up the key in the map
    /// LOOKUP
    pub fn get(&self, key: &K) -> Option<&V> {
        let mut ret = None;
        for t in 0 .. self.capacity {
            let hash = self.hash(&key, t);
            let e = &self.vec[hash];
            match *e {
                Entry::Empty => break,
                Entry::Deleted => {}
                Entry::Item { key: ref cur_key, value: ref cur_value } => {
                    if *cur_key == *key {
                        ret = Some(cur_value)
                    }
                }
            }
        }
        ret
    }

    pub fn contains_key(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    /// Removes the key from the map
    /// If the key was in the map it returns the associated value
    /// DELETE
    pub fn remove(&mut self, key: &K) -> Option<V> {
        let mut ret = None;
        for t in 0 .. self.capacity {
            let hash = self.hash(&key, t);
            let e = &mut self.vec[hash];
            // If e is an `Entry::Item` we need to take ownership of the value inside
            // in order to return it. Then we need to set e to `Entry::Deleted`. It
            // is hard (impossible?) to match on e and do both of those things. So I
            // replace e with `Entry::Deleted` then take ownership of the entire enum
            // stored at e. If it isn't a `Entry::Item` then we swap the value back.
            let owned_e = mem::replace(e, Entry::Deleted);
            match owned_e {
                Entry::Empty => {
                    mem::replace(e, owned_e);
                    break
                },
                Entry::Deleted => {}
                Entry::Item { key: cur_key, value: cur_value } => {
                    if cur_key == *key {
                        ret = Some(cur_value);
                        break;
                    } else {
                        mem::replace(e, Entry::Item { key: cur_key, value: cur_value });
                    }
                }
            }
        }
        if ret.is_some() {
            self.length -= 1;
        }
        ret
    }

    pub fn len(&self) -> usize {
        self.length
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn small_unit() {
        let mut m: HashMap<usize, String> = HashMap::new();
        m.insert(1, "foobar".to_string());
        assert_eq!(Some(&"foobar".to_string()), m.get(&1));
        assert_eq!(1, m.len());
        m.remove(&1);
        assert_eq!(None, m.get(&1));
        assert_eq!(0, m.len());
    }

    #[test]
    fn large_unit() {
        let mut m = HashMap::new();
        for _ in 0..10 {
            assert!(m.is_empty());
            for i in 1..1001 {
                assert!(m.insert(i, i).is_none());
                for j in 1..i + 1 {
                    let r = m.get(&j);
                    assert_eq!(r, Some(&j));
                }
                for j in i + 1..1001 {
                    let r = m.get(&j);
                    assert_eq!(r, None);
                }
            }
            for i in 1001..2001 {
                assert!(!m.contains_key(&i));
            }
            for i in 1..1001 {
                assert!(m.remove(&i).is_some());

                for j in 1..i + 1 {
                    assert!(!m.contains_key(&j));
                }

                for j in i + 1..1001 {
                    assert!(m.contains_key(&j));
                }
            }
            for i in 1..1001 {
                assert!(!m.contains_key(&i));
            }

            for i in 1..1001 {
                assert!(m.insert(i, i).is_none());
            }
            for i in (1..1001).rev() {
                assert!(m.remove(&i).is_some());

                for j in i..1001 {
                    assert!(!m.contains_key(&j));
                }

                for j in 1..i {
                    assert!(m.contains_key(&j));
                }
            }
        }
    }
}
