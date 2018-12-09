use core::{
    borrow::Borrow,
    cmp::Ordering,
    fmt,
    marker::PhantomData,
    mem::{drop, MaybeUninit},
    ops::Drop,
    ptr::{self, copy, copy_nonoverlapping},
};

pub const TABLE_SIZE: usize = 16;

/// A table that holds key-value pairs, sorted by key.
pub struct Table<K, V> {
    size: u16,
    keys: MaybeUninit<[K; TABLE_SIZE]>,
    vals: MaybeUninit<[V; TABLE_SIZE]>,
    _marker: PhantomData<(K, V)>,
}

impl<K, V> Table<K, V>
where
    K: Ord,
{
    /// Split key-value pairs in this table into the other. `other` must be an empty table.
    ///
    /// # Safety
    ///
    /// This function will panic when `self` is empty.
    pub unsafe fn split(&mut self, other: &mut Table<K, V>) {
        debug_assert!(other.is_empty());
        debug_assert!(self.is_full());
        let mid = self.size() / 2;
        let count = self.size() - mid;
        copy_nonoverlapping(
            (self.keys.as_ptr() as *const K).add(mid),
            other.keys.as_ptr() as *mut K,
            count,
        );
        copy_nonoverlapping(
            (self.vals.as_ptr() as *const V).add(mid),
            other.vals.as_ptr() as *mut V,
            count,
        );
        self.size -= count as u16;
        other.size = count as u16;
    }
}

impl<K, V> Table<K, V> {
    pub fn new() -> Table<K, V> {
        Table {
            size: 0,
            keys: MaybeUninit::uninitialized(),
            vals: MaybeUninit::uninitialized(),
            _marker: PhantomData,
        }
    }

    pub fn size(&self) -> usize {
        self.size as usize
    }

    fn is_empty(&self) -> bool {
        self.size == 0
    }

    pub fn is_full(&self) -> bool {
        self.size == TABLE_SIZE as u16
    }

    /// Returns the smallest key in this table.
    /// Unsafe because it causes undefined behavior when called on uninitialized table.
    pub unsafe fn min(&self) -> &K {
        &self.keys.get_ref()[0]
    }

    /// Returns tha largest key in this table.
    /// Unsafe because it causes undefined behavior when called on uninitialized table.
    pub unsafe fn max(&self) -> &K {
        &self.keys.get_ref()[self.size() - 1]
    }

    /// Find an index where the given key should be inserted to.
    /// Unsafe because it causes an out-of-bound access when called on filled table.
    unsafe fn find_insert_index<Q>(&self, key: &Q) -> usize
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        for (i, k) in self.keys().enumerate() {
            match key.cmp(k.borrow()) {
                Ordering::Less => return i,
                _ => continue,
            }
        }
        self.size()
    }

    /// Shifts keys and values by `offset`, starting on the given `index`.
    /// Unsafe because this causes an out-of-bound access when called on full
    /// table or when the given index is larger than the `size` of this table.
    pub unsafe fn shiftr_table(&mut self, index: usize, offset: usize) {
        // debug_assert!(self.size  as usize + index + offset <= TABLE_SIZE);
        copy(
            (self.keys.as_ptr() as *const K).add(index),
            (self.keys.as_mut_ptr() as *mut K).add(index + offset),
            self.size() - index,
        );
        copy(
            (self.vals.as_ptr() as *mut V).add(index),
            (self.vals.as_mut_ptr() as *mut V).add(index + offset),
            self.size() - index,
        );
    }

    pub unsafe fn shiftl_table(&mut self, index: usize, offset: usize) {
        copy(
            (self.keys.get_ref().as_ptr()).add(index + offset),
            (self.keys.get_mut().as_mut_ptr() as *mut K).add(index),
            self.size() - index - 1,
        );
        copy(
            (self.vals.get_ref().as_ptr()).add(index + offset),
            (self.vals.get_mut().as_mut_ptr()).add(index),
            self.size() - index - 1,
        );
    }

    pub unsafe fn move_kvs(&mut self, other: &mut Table<K, V>, index: usize, offset: usize) {
        copy(
            (self.keys.as_ptr() as *const K).add(index),
            other.keys.as_mut_ptr() as *mut K,
            offset,
        );
        copy(
            (self.vals.as_ptr() as *const K).add(index),
            other.vals.as_mut_ptr() as *mut K,
            offset,
        );
        self.size -= offset as u16;
        other.size += offset as u16;
        debug_assert!(
            self.size <= TABLE_SIZE as u16,
            "self table size too big: {}",
            self.size
        );
        debug_assert!(
            other.size <= TABLE_SIZE as u16,
            "other table size too big: {}",
            other.size
        );
    }

    /// Returns a stored value paired with the given key, if such pair is
    /// available in this table.
    pub fn find<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        Some(unsafe { self.get_unchecked(self.search_key(key).to_index()?) })
    }

    /// Returns true if a key-value pair with the given key is stored in this
    /// table.
    pub fn contains<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.search_key(key).to_index().is_some()
    }

    /// Returns true if the given key is within the range of this table. If the table has less than
    /// two keys, then this function always returns true.
    pub fn within<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if self.size() < 2 {
            true
        } else {
            unsafe {
                key.cmp(self.min().borrow()) != Ordering::Less
                    && key.cmp(self.max().borrow()) != Ordering::Greater
            }
        }
    }

    /// Insert a new key-value pair to this table.
    /// Returns the index if succeeds.
    pub fn insert(&mut self, key: K, val: V) -> Option<usize>
    where
        K: Ord,
    {
        // FIXME: This check should be removed, and mark this function as `unsafe`.
        if self.is_full() {
            return None;
        }

        let index = unsafe {
            let index = self.find_insert_index(&key);
            if index < self.size as usize {
                self.shiftr_table(index, 1);
            }
            index
        };
        self.size += 1;
        self.set(index, key, val);

        Some(index)
    }

    pub fn increment(&mut self) {
        self.size += 1;
    }

    pub unsafe fn insert_with_shift(
        &mut self,
        index: usize,
        key: K,
        val: V,
        increment: bool,
    ) -> &mut V {
        self.shiftr_table(index, 1);
        if increment {
            self.size += 1;
        }
        self.set(index, key, val);
        self.get_mut_unchecked(index)
    }

    pub unsafe fn insert_with_index(
        &mut self,
        index: usize,
        key: K,
        val: V,
        increment: bool,
    ) -> &mut V {
        if increment {
            self.size += 1;
        }
        self.set(index, key, val);
        self.get_mut_unchecked(index)
    }

    unsafe fn read_key(&self, index: usize) -> K {
        debug_assert!(index < self.size());
        ptr::read(self.keys.get_ref().get_unchecked(index))
    }

    unsafe fn read(&self, index: usize) -> V {
        debug_assert!(index < self.size());
        ptr::read(self.vals.get_ref().get_unchecked(index))
    }

    /// Delete a key-value pair with the given key from this table.
    /// Returns `true` if succeeds.
    pub fn delete(&mut self, key: &K) -> Option<(K, V)>
    where
        K: Ord,
    {
        self.search_key(key)
            .to_index()
            .map(|index| unsafe { self.delete_with_index(index) })
    }

    pub unsafe fn delete_with_index(&mut self, index: usize) -> (K, V) {
        let key = self.read_key(index);
        let val = self.read(index);
        unsafe {
            self.shiftl_table(index, 1);
        }
        self.size -= 1;
        (key, val)
    }

    pub unsafe fn get_unchecked(&self, index: usize) -> &V {
        self.vals.get_ref().get_unchecked(index)
    }

    pub unsafe fn get_mut_unchecked(&mut self, index: usize) -> &mut V {
        self.vals.get_mut().get_unchecked_mut(index)
    }

    pub unsafe fn get_pair_unchecked(&self, index: usize) -> (&K, &V) {
        (
            self.keys.get_ref().get_unchecked(index),
            self.vals.get_ref().get_unchecked(index),
        )
    }

    /// Set a key-value pair to the given index. When necessary, the caller must
    /// increment the `size` of this table before calling this method.
    fn set(&mut self, index: usize, key: K, val: V) {
        debug_assert!(index < self.size as usize, "{} {}", index, self.size);
        unsafe {
            self.keys.get_mut()[index] = key;
            self.vals.get_mut()[index] = val;
        }
    }

    /// Returns an iterator of the keys stored in this table.
    fn keys(&self) -> impl Iterator<Item = (&K)> {
        unsafe { self.keys.get_ref()[..self.size()].iter() }
    }

    /// Returns an iterator of the values stored in this table.
    fn vals(&self) -> impl Iterator<Item = (&V)> {
        unsafe { self.vals.get_ref()[..self.size()].iter() }
    }

    pub fn search_key<Q>(&self, key: &Q) -> TableSearchResult
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        for (i, k) in self.keys().enumerate() {
            match key.cmp(k.borrow()) {
                Ordering::Equal => return TableSearchResult::Found(i),
                Ordering::Less => {
                    return if i == 0 {
                        TableSearchResult::Less(self.is_full())
                    } else {
                        TableSearchResult::Within(i, self.is_full())
                    };
                }
                Ordering::Greater => continue,
            }
        }
        TableSearchResult::Greater(self.size(), self.is_full())
    }

    pub fn drop_table(&mut self) {
        for i in 0..self.size() {
            drop(unsafe { self.read(i) });
            drop(unsafe { self.read_key(i) });
        }
    }
}

/// The result of `Table::search`.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum TableSearchResult {
    /// Found an index to the key.
    Found(usize),
    /// The key is within the range of this table.
    Within(usize, bool /* true if the table is full */),
    /// The key is greater then the max key of this table.
    Greater(usize, bool /* true if the table is full */),
    /// The key is smaller than the min key of this table.
    Less(bool /* true if the table is full */),
}

impl TableSearchResult {
    fn to_index(&self) -> Option<usize> {
        match *self {
            TableSearchResult::Found(i) => Some(i),
            _ => None,
        }
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for Table<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Table {{\n  size: {},\n", self.size)?;
        write!(f, "  keys: [")?;
        for k in self.keys() {
            write!(f, "{:?} ", k)?;
        }
        write!(f, "],\n  vals: [")?;
        for v in self.vals() {
            write!(f, "{:?} ", v)?;
        }
        write!(f, "],\n}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::string::String;

    struct Foo {
        s: String,
    }

    impl Drop for Foo {
        fn drop(&mut self) {
            println!("Foo::drop called");
            drop(unsafe { ptr::read(&self.s) });
        }
    }

    #[test]
    fn test_shift() {
        unsafe {
            let mut table = Table::new();
            let size = 8;
            table.size = size as u16;
            for i in 0..size {
                table.keys.get_mut()[i] = i;
                table.vals.get_mut()[i] = i;
            }
            table.shiftr_table(0, 1);
            for i in 1..size + 1 {
                assert_eq!(table.keys.get_ref()[i], i - 1);
                assert_eq!(table.vals.get_ref()[i], i - 1);
            }
            table.size += 1;
            table.shiftl_table(0, 1);
            table.size -= 1;
            for i in 0..size {
                assert_eq!(table.keys.get_ref()[i], i);
                assert_eq!(table.vals.get_ref()[i], i);
            }
        }
        unsafe {
            let mut table = Table::new();
            table.size = 1;
            table.keys.get_mut()[0] = 1024;
            table.vals.get_mut()[0] = 1024;
            table.shiftl_table(0, 1);
        }
    }

    #[test]
    fn table_test() {
        let mut table = Table::new();
        assert!(table.delete(&0).is_none());
        for i in 0..TABLE_SIZE {
            assert!(
                table.insert(i, format!("{}", i)).is_some(),
                format!("{} th insert failed", i)
            );
            assert_eq!(
                table.find(&i),
                Some(&format!("{}", i)),
                "{} not found\n{:?}",
                i,
                table
            );
        }
        for i in 0..TABLE_SIZE {
            println!("i: {}", i);
            assert_eq!(
                table.find(&i),
                Some(&format!("{}", i)),
                "key {} not found",
                i
            );
            assert_eq!(table.delete(&i), Some((i, format!("{}", i))));
            assert!(
                table.find(&i).is_none(),
                format!("key {} found after delete", i)
            );
        }
    }

    #[test]
    fn table_random_test() {
        use crate::std::collections::HashMap;
        use rand::{rngs::SmallRng, FromEntropy, Rng};

        let mut rng = SmallRng::from_entropy();

        let mut map = HashMap::new();
        let mut table = Table::new();
        let test_size = 1000;
        for _ in 0..test_size {
            for i in 0..TABLE_SIZE {
                map.insert(i, rng.gen::<usize>());
                table.insert(i, map[&i]);
            }
            assert!(!table.insert(0, 0).is_some());

            for i in 0..TABLE_SIZE {
                assert_eq!(*table.find(&i).unwrap(), map[&i]);
            }

            for i in 0..TABLE_SIZE {
                assert!(table.delete(&i).is_some());
            }

            for i in 0..TABLE_SIZE {
                assert!(!table.contains(&i));
            }
        }
    }

    #[test]
    fn test_search_key() {
        {
            let mut table = Table::new();
            for i in 0..TABLE_SIZE {
                table.insert(i, i);
                assert_eq!(table.search_key(&i), TableSearchResult::Found(i));
                assert_eq!(
                    table.search_key(&(i + 1)),
                    TableSearchResult::Greater(i + 1, i + 1 == TABLE_SIZE),
                );
            }
        }
        {
            let mut table = Table::new();
            for &i in &[1, 3, 5, 7, 9, 11] {
                table.insert(i, i);
            }
            for (i, &v) in [0, 2, 4, 6, 8, 10, 13].iter().enumerate() {
                let result = table.search_key(&v);
                assert_eq!(
                    result,
                    if v == 0 {
                        TableSearchResult::Less(false)
                    } else if v == 13 {
                        TableSearchResult::Greater(6, false)
                    } else {
                        TableSearchResult::Within(i, false)
                    }
                );
            }
            for (_, &v) in [0, 2, 4, 6, 8, 10, 13].iter().enumerate() {
                match table.search_key(&v) {
                    TableSearchResult::Within(i, false) => assert_eq!(table.insert(v, v), Some(i)),
                    TableSearchResult::Less(false) => assert_eq!(table.insert(0, v), Some(v)),
                    _ => (),
                }
            }
            for i in 0..table.size() {
                assert!(table.contains(&i));
                assert_eq!(table.search_key(&i), TableSearchResult::Found(i));
            }
        }
    }

    #[test]
    fn test_table_split() {
        let mut table = Table::new();
        for i in 0..TABLE_SIZE {
            table.insert(i, i);
        }
        let mut other = Table::new();
        unsafe {
            table.split(&mut other);
        }
        assert_eq!(table.size(), TABLE_SIZE / 2);
        assert_eq!(other.size(), TABLE_SIZE / 2);
        for i in 0..TABLE_SIZE {
            if i < TABLE_SIZE / 2 {
                assert_eq!(*unsafe { table.get_unchecked(i) }, i);
            } else {
                assert_eq!(*unsafe { other.get_unchecked(i - TABLE_SIZE / 2) }, i);
            }
        }
    }
}
