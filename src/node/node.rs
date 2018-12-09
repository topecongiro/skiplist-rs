use core::{
    borrow::Borrow,
    fmt,
    mem::{self, size_of},
    ptr::{self, NonNull},
};

use crate::alloc::alloc::{alloc, dealloc, Layout};

use crate::node::{
    table::{Table, TableSearchResult, TABLE_SIZE},
    tower::{random_height, Tower},
};

const CACHE_LINE_SIZE: usize = 32;

#[repr(C)]
pub struct Node<K, V> {
    /// A pointer to the prev node.
    prev: *mut Node<K, V>,
    /// Key-value pairs.
    table: Table<K, V>,
    /// The tower of this node.
    tower: Tower<K, V>,
}

#[derive(Debug)]
pub struct Handle<K, V> {
    pub index: usize,
    pub node: NonNull<Node<K, V>>,
}

impl<'a, K: 'a, V: 'a> Handle<K, V> {
    pub fn get_mut(&'a mut self) -> &'a mut V {
        unsafe { (&mut *self.node.as_ptr()).get_mut(self.index) }
    }

    pub fn into_value(self) -> &'a V {
        unsafe { (&*self.node.as_ptr()).get_unchecked(self.index) }
    }

    pub fn into_key_value(self) -> (&'a K, &'a V) {
        unsafe { (&*self.node.as_ptr()).get_pair_unchecked(self.index) }
    }

    pub fn into_mut(self) -> &'a mut V {
        unsafe { (&mut *self.node.as_ptr()).get_mut(self.index) }
    }

    pub fn insert_with_shift(self, key: K, val: V) -> &'a mut V {
        unsafe {
            (&mut *self.node.as_ptr())
                .table
                .insert_with_shift(self.index, key, val, true)
        }
    }

    fn insert_with_index_inner(self, key: K, val: V, increment: bool) -> &'a mut V {
        unsafe {
            (&mut *self.node.as_ptr())
                .table
                .insert_with_index(self.index, key, val, increment)
        }
    }

    pub fn insert_with_index(self, key: K, val: V) -> &'a mut V {
        self.insert_with_index_inner(key, val, true)
    }

    pub fn split(self, offset: usize, key: K, val: V) -> &'a mut V {
        let mut other = unsafe { self.node.as_ref().next_at(0) }.unwrap();
        unsafe {
            (&mut *self.node.as_ptr()).move_kvs(other.as_mut(), offset);
            self.insert_with_shift(key, val)
        }
    }

    pub fn delete(self) -> V {
        unsafe {
            (&mut *self.node.as_ptr())
                .table
                .delete_with_index(self.index)
                .1
        }
    }

    pub fn map<F, T>(&self, f: F) -> T
    where
        F: Fn(&Node<K, V>) -> T,
    {
        unsafe { f(self.node.as_ref()) }
    }

    pub fn map_mut<F, T: 'a>(&'a mut self, f: F) -> T
    where
        F: Fn(&mut Node<K, V>) -> T,
    {
        unsafe { f(&mut *self.node.as_ptr()) }
    }

    pub fn map_or_next<F, T>(&self, height: usize, default: T, f: F) -> T
    where
        F: Fn(&Node<K, V>) -> T,
    {
        unsafe {
            self.node
                .as_ref()
                .next_at(height)
                .map_or(default, |n| f(n.as_ref()))
        }
    }
}

impl<K, V> Node<K, V> {
    pub fn height(&self) -> usize {
        self.tower.height()
    }
}

impl<K, V> Node<K, V>
where
    K: Ord,
{
    pub fn insert(&mut self, key: K, val: V) -> Option<usize> {
        self.table.insert(key, val)
    }

    pub unsafe fn split(&mut self, key: K, val: V, mut other: NonNull<Node<K, V>>) -> &mut V {
        self.table.split(&mut other.as_mut().table);
        if key < *self.table.max() {
            let index = self.table.insert(key, val).unwrap();
            self.table.get_mut_unchecked(index)
        } else {
            let index = other.as_mut().table.insert(key, val).unwrap();
            (&mut *other.as_ptr()).get_mut(index)
        }
    }
}

impl<K, V> Node<K, V> {
    pub fn contains_key<Q>(&self, key: &Q) -> Option<usize>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        match self.search_key(key) {
            TableSearchResult::Found(i) => Some(i),
            _ => None,
        }
    }

    pub fn search_key<Q>(&self, key: &Q) -> TableSearchResult
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.table.search_key(key)
    }
}

impl<K, V> Node<K, V> {
    pub fn new() -> NonNull<Node<K, V>> {
        Self::new_inner(random_height())
    }

    pub fn len(&self) -> usize {
        self.table.size()
    }

    pub(crate) fn new_with_height(height: usize) -> NonNull<Node<K, V>> {
        Self::new_inner(height)
    }

    pub fn available_spaces(&self) -> usize {
        TABLE_SIZE - self.len()
    }

    pub fn is_full(&self) -> bool {
        self.table.is_full()
    }

    pub unsafe fn get_unchecked(&self, index: usize) -> &V {
        self.table.get_unchecked(index)
    }

    pub unsafe fn get_pair_unchecked(&self, index: usize) -> (&K, &V) {
        self.table.get_pair_unchecked(index)
    }

    pub unsafe fn get_mut(&mut self, index: usize) -> &mut V {
        self.table.get_mut_unchecked(index)
    }

    pub fn prev(&self) -> Option<&Node<K, V>> {
        unsafe { self.prev.as_ref() }
    }

    pub fn prev_as_mut(&self) -> Option<&mut Node<K, V>> {
        unsafe { self.prev.as_mut() }
    }

    pub fn set_prev(&mut self, node: NonNull<Node<K, V>>) {
        self.prev = node.as_ptr();
    }

    pub fn next_at(&self, height: usize) -> Option<NonNull<Node<K, V>>> {
        NonNull::new(unsafe { self.tower.next_at(height) })
    }

    pub fn set_next_at(&mut self, height: usize, node: Option<NonNull<Node<K, V>>>) {
        unsafe {
            self.tower
                .set_next_at(height, node.map_or(ptr::null_mut(), |n| n.as_ptr()));
        }
    }

    /// You must call this function from `Handle`.
    pub unsafe fn insert_with_index(
        &mut self,
        index: usize,
        key: K,
        val: V,
        increment: bool,
    ) -> &mut V {
        self.table.insert_with_index(index, key, val, increment)
    }

    pub fn min(&self) -> &K {
        unsafe { self.table.min() }
    }

    pub fn max(&self) -> &K {
        unsafe { self.table.max() }
    }

    pub fn next_min(&self, height: usize) -> Option<&K> {
        Some(unsafe { (&*self.next_at(height)?.as_ptr()).table.min() })
    }

    pub unsafe fn move_kvs(&mut self, other: &mut Node<K, V>, offset: usize) {
        other.table.shiftr_table(0, offset);
        self.table
            .move_kvs(&mut other.table, self.len() - offset, offset);
    }

    /// Calculate the size of bytes necessary for the node with the given height.
    fn mem_size(height: usize) -> usize {
        size_of::<Node<K, V>>() + size_of::<*mut Node<K, V>>() * height
    }

    fn new_inner(height: usize) -> NonNull<Node<K, V>> {
        let ptr = unsafe {
            alloc(
                Layout::from_size_align(Self::mem_size(height), CACHE_LINE_SIZE)
                    .expect("Memory allocation has failed"),
            ) as *mut Node<K, V>
        };
        unsafe {
            let mut node = NonNull::new_unchecked(ptr);
            let tower_ptr = (ptr as *mut *const Node<K, V>).add(1);
            let tower_ptr = (tower_ptr as *mut Table<K, V>).add(1) as *mut Tower<K, V>;
            node.as_mut().prev = ptr::null_mut();
            node.as_mut().table = Table::new();
            node.as_mut().tower = Tower::new(tower_ptr, height);
            node
        }
    }

    pub fn dealloc_node(node: &mut Node<K, V>) {
        node.table.drop_table();
        unsafe {
            dealloc(
                node as *mut Node<K, V> as *mut u8,
                Layout::from_size_align(Self::mem_size(node.tower.height()), CACHE_LINE_SIZE)
                    .expect("Invalid cache line size?"),
            );
        }
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for Node<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "({:?})\n{:?}\n{:?}",
            self as *const Node<K, V>, self.table, self.tower
        )
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::node::table::TABLE_SIZE;

    #[test]
    fn test_node_new() {
        // Check whether accessing to tower or table of a new node
        // does not cause an invalid memory access.
        for height in 0..63 {
            let mut node_ptr: NonNull<Node<usize, usize>> = Node::new_with_height(height);
            for i in 0..height {
                unsafe {
                    // node_ptr.as_mut().set_next_at(height, None);
                    node_ptr.as_mut().next_at(i);
                }
            }
            for i in 0..TABLE_SIZE {
                unsafe { node_ptr.as_mut().table.insert(i, i) };
            }
            for i in 0..TABLE_SIZE {
                unsafe { assert_eq!(*node_ptr.as_ref().table.find(&i).unwrap(), i) };
            }
        }
    }

    #[test]
    fn test_node_mem_size() {
        for i in 0..64 {
            let mem_size = Node::<usize, usize>::mem_size(i);
            assert_eq!(mem_size % 2, 0);
            assert_eq!(mem_size % 4, 0);
            assert_eq!(mem_size % 8, 0);
            assert_eq!(
                mem_size,
                size_of::<Node<usize, usize>>() + i as usize * 8,
                "height: {}",
                i
            );
        }
    }
}
