use std::mem;
use std::hash::{Hash, Hasher, BuildHasher};
use std::collections::LinkedList;
use std::collections::hash_map::RandomState;

use capacity::close_prime;

struct Entry<K, V> {
    key:   K,
    value: V
}

struct Bucket<K, V> {
    list: LinkedList<Entry<K, V>>
}

impl<K, V> Bucket<K, V>
    where
    K: Eq + Hash
{
    fn new() -> Bucket<K, V> {
        Bucket {
            list: LinkedList::new()
        }
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        for e in self.list.iter_mut() {
            if e.key == key {
                return Some(mem::replace(&mut e.value, value))
            }
        }
        self.list.push_front(Entry { key, value });
        None
    }

    fn lookup(&self, key: &K) -> Option<&V> {
        for e in self.list.iter() {
            if e.key == *key {
                return Some(&e.value)
            }
        }
        None
    }

    fn delete(&mut self, key: &K) -> Option<V> {
        let mut old_list = mem::replace(&mut self.list, LinkedList::new());
        while let Some(e) = old_list.pop_front() {
            if e.key == *key {
                self.list.append(&mut old_list);
                return Some(e.value)
            } else {
                self.list.push_front(e)
            }
        }
        None
    }
}

pub struct HashMap<K, V> {
    /// This makes the table more resistant to DOS attacks by introducing
    /// random state into the HashMap.
    hash_state: RandomState,
    /// This is also named m, must be prime
    capacity:   usize,
    /// Number of elements in table
    length:     usize,
    vec:        Vec<Bucket<K, V>>
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
        let vec : Vec<Bucket<K, V>> = (0..capacity).map(|_| Bucket::new()).collect();
        HashMap {
            hash_state: RandomState::new(),
            capacity,
            length: 0,
            vec
        }
    }

    fn hash(&self, key: &K) -> usize {
        let mut hasher = self.hash_state.build_hasher();
        key.hash(&mut hasher);
        hasher.finish() as usize % self.capacity
    }


    fn resize(&mut self) {
        let old_capacity = self.capacity;
        let old = mem::replace(self, HashMap::with_capacity(2 * old_capacity));
        for bucket in old.vec {
            for Entry { key, value } in bucket.list {
                self.insert(key, value);
            }
        }
    }


    /// Determines if the load factor is too high
    fn should_resize(&self) -> bool {
        const THRESHOLD : f64 = 1.2;
        THRESHOLD < self.length as f64 / self.capacity as f64
    }

    /// Inserts the key-value pair into the map
    /// If the map had a value at that key the old key is returned
    /// INSERT + UPDATE
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        if self.should_resize() {
            self.resize()
        }
        let hash = self.hash(&key);
        let ret = self.vec[hash].insert(key, value);
        if ret.is_none() {
            self.length += 1;
        }
        ret
    }

    /// Looks up the key in the map
    /// LOOKUP
    pub fn get(&self, key: &K) -> Option<&V> {
        let hash = self.hash(key);
        self.vec[hash].lookup(key)
    }

    pub fn contains_key(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    /// Removes the key from the map
    /// If the key was in the map it returns the associated value
    /// DELETE
    pub fn remove(&mut self, key: &K) -> Option<V> {
        let hash = self.hash(key);
        let ret = self.vec[hash].delete(key);
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
