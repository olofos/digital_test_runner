use std::collections::HashMap;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct FramedMap<K, V> {
    values: Vec<(K, V)>,
    frame_stack: Vec<usize>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct FramedSet<K> {
    map: FramedMap<K, ()>,
}

impl<K, V> FramedMap<K, V> {
    pub(crate) fn new() -> Self {
        Self {
            values: vec![],
            frame_stack: vec![],
        }
    }

    pub(crate) fn push_frame(&mut self) {
        self.frame_stack.push(self.values.len())
    }

    pub(crate) fn pop_frame(&mut self) {
        let len = self.frame_stack.pop().unwrap_or(0);
        self.values.truncate(len);
    }
}

impl<K: std::hash::Hash + Eq + Clone, V: Copy> FramedMap<K, V> {
    pub(crate) fn flatten(&self) -> HashMap<K, V> {
        let mut values = HashMap::new();

        for (key, value) in self.values.iter().rev() {
            if !values.contains_key(key) {
                values.insert(key.clone(), *value);
            }
        }

        values
    }
}

impl<K: Eq, V: Copy> FramedMap<K, V> {
    pub(crate) fn set(&mut self, key: impl Into<K>, value: V) {
        let key = key.into();
        let frame_start = *self.frame_stack.last().unwrap_or(&0);
        if let Some((_, entry_value)) = self.values[frame_start..]
            .iter_mut()
            .find(|entry| entry.0 == key)
        {
            *entry_value = value;
        } else {
            self.values.push((key, value));
        }
    }

    pub(crate) fn get<Q>(&self, key: &Q) -> Option<V>
    where
        K: std::borrow::Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.values
            .iter()
            .rev()
            .find(|entry| entry.0.borrow() == key)
            .map(|entry| entry.1)
    }
}

impl<K> FramedSet<K> {
    pub(crate) fn new() -> Self {
        Self {
            map: FramedMap::new(),
        }
    }
}

impl<K: Eq> FramedSet<K> {
    pub(crate) fn push_frame(&mut self) {
        self.map.push_frame()
    }

    pub(crate) fn pop_frame(&mut self) {
        self.map.pop_frame()
    }

    pub(crate) fn insert(&mut self, key: impl Into<K>) {
        self.map.set(key, ())
    }

    pub(crate) fn contains<Q>(&self, key: &Q) -> bool
    where
        K: std::borrow::Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.map.get(key).is_some()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn framed_map_works() {
        let mut map = FramedMap::<&str, i64>::new();
        map.set("a", 1);
        map.set("b", 2);
        map.set("c", 3);
        assert_eq!(map.get("a"), Some(1));
        assert_eq!(map.get("b"), Some(2));
        assert_eq!(map.get("c"), Some(3));
        map.set("a", 4);
        assert_eq!(map.get("a"), Some(4));
        assert_eq!(map.get("b"), Some(2));
        assert_eq!(map.get("c"), Some(3));

        map.push_frame();
        map.set("a", 5);
        map.set("b", 6);
        assert_eq!(map.get("a"), Some(5));
        assert_eq!(map.get("b"), Some(6));
        assert_eq!(map.get("c"), Some(3));

        map.push_frame();
        map.set("a", 7);
        map.set("c", 8);
        assert_eq!(map.get("a"), Some(7));
        assert_eq!(map.get("b"), Some(6));
        assert_eq!(map.get("c"), Some(8));

        map.set("c", 9);
        assert_eq!(map.get("a"), Some(7));
        assert_eq!(map.get("b"), Some(6));
        assert_eq!(map.get("c"), Some(9));

        map.pop_frame();
        assert_eq!(map.get("a"), Some(5));
        assert_eq!(map.get("b"), Some(6));
        assert_eq!(map.get("c"), Some(3));

        map.pop_frame();
        assert_eq!(map.get("a"), Some(4));
        assert_eq!(map.get("b"), Some(2));
        assert_eq!(map.get("c"), Some(3));
    }

    #[test]
    fn framed_set_works() {
        let mut set = FramedSet::<&str>::new();

        set.insert("a");
        set.insert("b");
        assert!(set.contains("a"));
        assert!(set.contains("b"));
        assert!(!set.contains("c"));

        set.push_frame();
        set.insert("c");
        assert!(set.contains("a"));
        assert!(set.contains("b"));
        assert!(set.contains("c"));

        set.pop_frame();
        assert!(set.contains("a"));
        assert!(set.contains("b"));
        assert!(!set.contains("c"));
    }
}
