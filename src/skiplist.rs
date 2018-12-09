use core::{
    borrow::Borrow,
    cmp::Ordering,
    fmt::{self, Debug},
    marker::PhantomData,
    mem,
    ops::{Drop, Index, RangeBounds},
    ptr::NonNull,
};

use crate::{
    alloc::alloc::dealloc,
    node::{Handle, Node, MAX_TOWER_HEIGHT},
    visitor::{SkipListVisitor, VisitMode, VisitSkipListResult},
};

/// A map based on a Skip List.
pub struct SkipListMap<K, V> {
    /// Number of key-value pairs in this skip list.
    pub(crate) len: usize,
    pub(crate) height: usize,
    /// A root tower.
    pub(crate) root_tower: [Option<NonNull<Node<K, V>>>; MAX_TOWER_HEIGHT],
}

impl<K, V> SkipListMap<K, V> {
    pub fn len(&self) -> usize {
        self.len
    }

    pub(crate) fn height(&self) -> usize {
        self.height
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub(crate) fn root(&self) -> Option<NonNull<Node<K, V>>> {
        self.root_tower[0]
    }
}

impl<K, V> Drop for SkipListMap<K, V> {
    fn drop(&mut self) {
        let mut node_opt = self.root();
        while let Some(mut node) = node_opt {
            Node::dealloc_node(unsafe { node.as_mut() });
            node_opt = unsafe { node.as_ref().next_at(0) };
        }
    }
}

impl<K: Debug, V: Debug> SkipListMap<K, V>
where
    K: Ord,
{
    fn insert_debug<Q>(&mut self, key: K, val: V) -> Result<Option<V>, SkipListValidationError>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let result = self.insert(key, val);
        self.validate().map(|_| result)
    }
}
impl<K, V> SkipListMap<K, V>
where
    K: Ord,
{
    pub fn new() -> SkipListMap<K, V> {
        SkipListMap {
            len: 0,
            height: 0,
            root_tower: [None; MAX_TOWER_HEIGHT],
        }
    }

    pub fn clear(&mut self) {}

    fn visit<Q>(
        &self,
        key: &Q,
        visit_mode: VisitMode,
        prev_nodes: Option<&mut [Option<NonNull<Node<K, V>>>]>,
    ) -> VisitSkipListResult<K, V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut visitor = SkipListVisitor::new(self, visit_mode, prev_nodes);
        visitor.visit_skip_list(key.borrow())
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        match self.visit(key, VisitMode::ReadOnly, None) {
            VisitSkipListResult::Found(handle) => Some(handle.into_value()),
            _ => None,
        }
    }

    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        match self.visit(key, VisitMode::ReadOnly, None) {
            VisitSkipListResult::Found(handle) => Some(handle.into_key_value()),
            _ => None,
        }
    }

    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        match self.visit(key, VisitMode::ReadOnly, None) {
            VisitSkipListResult::Found(..) => true,
            _ => false,
        }
    }

    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        match self.visit(key, VisitMode::ReadOnly, None) {
            VisitSkipListResult::Found(handle) => Some(handle.into_mut()),
            _ => None,
        }
    }

    pub fn insert<Q>(&mut self, key: K, val: V) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        match self.entry(key) {
            Entry::Occupied(mut entry) => Some(entry.insert(val)),
            Entry::Vacant(entry) => {
                entry.insert(val);
                None
            }
        }
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut prev_nodes = [None; MAX_TOWER_HEIGHT];
        match self.visit(key, VisitMode::Delete, Some(&mut prev_nodes)) {
            VisitSkipListResult::Found(handle) => Some(handle.delete()),
            VisitSkipListResult::FoundSingle(handle) => Some(
                OccupiedEntry {
                    length: &mut self.len,
                    kind: OccupiedEntryKind::FoundSingle {
                        handle,
                        snapshot: SkipListSnapshot {
                            height: &mut self.height,
                            prev_nodes,
                            root_tower: &mut self.root_tower,
                        },
                    },
                    _marker: PhantomData,
                }
                .remove(),
            ),
            _ => None,
        }
    }

    pub fn append(&mut self, _other: &mut SkipListMap<K, V>) {}

    pub fn range<T, R>(&self, _range: R) -> Range<K, V>
    where
        K: Borrow<T>,
        R: RangeBounds<T>,
        T: Ord + ?Sized,
    {
        unimplemented!()
    }

    pub fn range_mut<T, R>(&mut self, _range: R) -> RangeMut<K, V>
    where
        K: Borrow<T>,
        R: RangeBounds<T>,
        T: Ord + ?Sized,
    {
        unimplemented!()
    }

    pub fn entry(&mut self, key: K) -> Entry<K, V> {
        let mut prev_nodes = [None; MAX_TOWER_HEIGHT];
        match self.visit(key.borrow(), VisitMode::Write, Some(&mut prev_nodes)) {
            VisitSkipListResult::Found(handle) => Entry::Occupied(OccupiedEntry {
                length: &mut self.len,
                kind: OccupiedEntryKind::Found { handle },
                _marker: PhantomData,
            }),
            VisitSkipListResult::FoundSingle(handle) => Entry::Occupied(OccupiedEntry {
                length: &mut self.len,
                kind: OccupiedEntryKind::FoundSingle {
                    handle,
                    snapshot: SkipListSnapshot {
                        height: &mut self.height,
                        prev_nodes,
                        root_tower: &mut self.root_tower,
                    },
                },
                _marker: PhantomData,
            }),
            VisitSkipListResult::Insertable(handle, split_required) => Entry::Vacant(VacantEntry {
                key,
                length: &mut self.len,
                kind: VacantEntryKind::Insertable {
                    handle,
                    split_required,
                },
                _marker: PhantomData,
            }),
            VisitSkipListResult::Split(handle, shift) => Entry::Vacant(VacantEntry {
                key,
                length: &mut self.len,
                kind: VacantEntryKind::Split {
                    handle,
                    offset: shift,
                },
                _marker: PhantomData,
            }),
            VisitSkipListResult::NewNode => Entry::Vacant(VacantEntry {
                key,
                length: &mut self.len,
                kind: VacantEntryKind::NewNode {
                    snapshot: SkipListSnapshot {
                        height: &mut self.height,
                        prev_nodes,
                        root_tower: &mut self.root_tower,
                    },
                },
                _marker: PhantomData,
            }),
            VisitSkipListResult::NotFound => Entry::Vacant(VacantEntry {
                key,
                length: &mut self.len,
                kind: VacantEntryKind::NewNode {
                    snapshot: SkipListSnapshot {
                        height: &mut self.height,
                        prev_nodes: [None; MAX_TOWER_HEIGHT],
                        root_tower: &mut self.root_tower,
                    },
                },
                _marker: PhantomData,
            }),
        }
    }

    fn count_nodes(&self) -> usize {
        let mut node_num = 0;
        let mut node = self.root();
        while node.is_some() {
            node_num += 1;
            node = node.as_ref().and_then(|n| unsafe { n.as_ref().next_at(0) });
        }
        node_num
    }

    fn validate_height(&self, height: usize) -> bool {
        let node_opt = self.root_tower[height];
        if node_opt.is_none() {
            return true;
        }
        let mut node = node_opt.unwrap();
        loop {
            let next_node = match unsafe { node.as_ref().next_at(height) } {
                Some(n) => n,
                None => break,
            };
            unsafe {
                if next_node.as_ref().min() <= node.as_ref().max() {
                    return false;
                }
            }
            node = next_node;
        }
        true
    }

    fn validate(&self) -> Result<(), SkipListValidationError> {
        for height in 0..self.height {
            if !self.validate_height(height) {
                return Err(SkipListValidationError::InvalidHeight(height));
            }
        }
        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq)]
enum SkipListValidationError {
    InvalidNodeNum(usize, usize),
    InvalidHeight(usize),
}

/// An iterator over a sub-range of entries in a `SkipListMap`.
pub struct Range<K, V> {
    _key: PhantomData<K>,
    _val: PhantomData<V>,
}

/// A mutable iterator over a sub-range of entries in a `SkipListMap`.
pub struct RangeMut<K, V> {
    _key: PhantomData<K>,
    _val: PhantomData<V>,
}

/// A view to the single key-value pair inside skip list. `Entry` is used to update `SkipList`.
// FIXME: Use generics over enums internally to save memory.
pub enum Entry<'a, K, V> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

pub struct OccupiedEntry<'a, K, V> {
    length: &'a mut usize,
    kind: OccupiedEntryKind<'a, K, V>,

    _marker: PhantomData<&'a mut (K, V)>,
}

pub struct VacantEntry<'a, K, V> {
    key: K,
    length: &'a mut usize,
    kind: VacantEntryKind<'a, K, V>,

    _marker: PhantomData<&'a mut (K, V)>,
}

enum VacantEntryKind<'a, K, V> {
    Insertable {
        handle: Handle<K, V>,
        split_required: bool,
    },
    Split {
        handle: Handle<K, V>,
        offset: usize,
    },
    NewNode {
        snapshot: SkipListSnapshot<'a, K, V>,
    },
}

enum OccupiedEntryKind<'a, K, V> {
    Found {
        handle: Handle<K, V>,
    },
    FoundSingle {
        handle: Handle<K, V>,
        snapshot: SkipListSnapshot<'a, K, V>,
    },
}

impl<'a, K, V> OccupiedEntryKind<'a, K, V> {
    fn handle(&'a mut self) -> &'a mut Handle<K, V> {
        match self {
            OccupiedEntryKind::Found { ref mut handle } => handle,
            OccupiedEntryKind::FoundSingle { ref mut handle, .. } => handle,
        }
    }
}

/// A snapshot of a skip list. Used to update the skip list.
struct SkipListSnapshot<'a, K, V> {
    height: &'a mut usize,
    root_tower: &'a mut [Option<NonNull<Node<K, V>>>; MAX_TOWER_HEIGHT],
    prev_nodes: [Option<NonNull<Node<K, V>>>; MAX_TOWER_HEIGHT], // FIXME: Avoid fixed-size allocation.
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    fn get_mut(&'a mut self) -> &'a mut V {
        self.handle().get_mut()
    }

    pub fn insert(&'a mut self, val: V) -> V {
        mem::replace(self.get_mut(), val)
    }

    pub fn remove(self) -> V {
        *self.length -= 1;
        match self.kind {
            OccupiedEntryKind::Found { handle } => handle.delete(),
            OccupiedEntryKind::FoundSingle { .. } => unimplemented!(),
        }
    }

    fn handle(&'a mut self) -> &'a mut Handle<K, V> {
        self.kind.handle()
    }
}

impl<'a, K: Ord, V> VacantEntry<'a, K, V> {
    pub fn insert(self, val: V) -> &'a mut V {
        // N.B. This is the only place where we insert a new node.
        *self.length += 1;

        match self.kind {
            VacantEntryKind::Split { handle, offset } => handle.split(offset, self.key, val),
            VacantEntryKind::Insertable {
                handle,
                split_required: true,
            } => handle.insert_with_shift(self.key, val),
            VacantEntryKind::Insertable {
                handle,
                split_required: false,
            } => handle.insert_with_index(self.key, val),
            VacantEntryKind::NewNode { snapshot } => snapshot.add_node(self.key, val),
        }
    }
}

impl<'a, K, V> SkipListSnapshot<'a, K, V>
where
    K: Ord,
{
    fn set_next_nodes(&self, new_node: &mut Node<K, V>) {
        for height in 0..new_node.height() {
            let next_node = match self.prev_nodes[height] {
                None => self.root_tower[height],
                Some(prev_node) => unsafe { prev_node.as_ref().next_at(height) },
            };
            new_node.set_next_at(height, next_node);
        }
    }

    fn update_next_nodes_of_prev_nodes(&mut self, new_node: NonNull<Node<K, V>>) {
        for height in 0..unsafe { new_node.as_ref().height() } {
            if let Some(mut prev_node) = self.prev_nodes[height] {
                unsafe {
                    prev_node.as_mut().set_next_at(height, Some(new_node));
                }
            } else {
                self.root_tower[height] = Some(new_node);
            }
        }
    }

    fn add_node(mut self, key: K, val: V) -> &'a mut V {
        let mut new_node = Node::new();
        let new_node_height = unsafe { new_node.as_ref().height() };
        if *self.height < new_node_height {
            *self.height = new_node_height;
        }
        let prev_node_opt = self.prev_nodes[0];
        self.set_next_nodes(unsafe { new_node.as_mut() });
        self.update_next_nodes_of_prev_nodes(new_node);

        if let Some(prev_node) = prev_node_opt {
            debug_assert!(unsafe { prev_node.as_ref().is_full() });
            unsafe { (&mut *prev_node.as_ptr()).split(key, val, new_node) }
        } else {
            unsafe {
                let index = new_node.as_mut().insert(key, val).unwrap();
                (&mut *new_node.as_ptr()).get_mut(index)
            }
        }
    }
}

unsafe impl<K: Send, V: Send> Send for SkipListMap<K, V> {}
unsafe impl<K: Sync, V: Sync> Sync for SkipListMap<K, V> {}

impl<K: PartialEq, V: PartialEq> PartialEq for SkipListMap<K, V> {
    fn eq(&self, _: &SkipListMap<K, V>) -> bool {
        unimplemented!()
    }
}

impl<K: Eq, V: Eq> Eq for SkipListMap<K, V> {}

impl<K: PartialOrd, V: PartialOrd> PartialOrd for SkipListMap<K, V> {
    fn partial_cmp(&self, _: &SkipListMap<K, V>) -> Option<Ordering> {
        unimplemented!()
    }
}

impl<K: Ord, V: Ord> Ord for SkipListMap<K, V> {
    fn cmp(&self, _: &SkipListMap<K, V>) -> Ordering {
        unimplemented!()
    }
}

impl<K: Debug, V: Debug> Debug for SkipListMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut node = self.root_tower[0];
        let mut i = 1;

        write!(f, "root_tower: [\n")?;
        for i in 0..self.height {
            let height = self.height - i;
            write!(
                f,
                "  {}: {:?},\n",
                height,
                self.root_tower[height - 1].unwrap()
            )?;
        }
        write!(f, "]\n")?;
        while let Some(n) = node {
            write!(f, "Node {} {:?}\n", i, unsafe { n.as_ref() })?;
            node = unsafe { n.as_ref().next_at(0) };
            i += 1;
        }
        write!(f, "")
    }
}

impl<'a, K: Ord, Q: ?Sized, V> Index<&'a Q> for SkipListMap<K, V>
where
    K: Borrow<Q>,
    Q: Ord,
{
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("no entry found for the given key")
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_insert() {
        let mut skip_list = SkipListMap::new();
        skip_list.insert_debug(1, 1).unwrap();
        assert!(skip_list.root().is_some());
        assert_eq!(skip_list.len(), 1);
        assert!(unsafe {
            skip_list
                .root()
                .unwrap()
                .as_ref()
                .contains_key(&1)
                .is_some()
        });
        assert_eq!(skip_list.get(&1).unwrap(), &1);

        for j in 2..128 {
            assert!(
                skip_list.insert_debug(j, j).is_ok(),
                "skip list invariants broke after insert ({})\n{:?}",
                j,
                skip_list,
            );
            assert_eq!(skip_list.validate(), Ok(()));
            for i in 1..=j {
                assert!(
                    skip_list.get(&i).is_some(),
                    "{} not found, loop {}\n{:?}",
                    i,
                    j,
                    skip_list,
                );
                assert_eq!(
                    skip_list.get(&i).unwrap(),
                    &i,
                    "{:?}\n{} has a wrong value",
                    skip_list,
                    i
                );
            }
        }
    }

    #[test]
    fn test_random_insert() {
        use rand::{rngs::SmallRng, FromEntropy, Rng};

        let mut rng = SmallRng::from_entropy();
        let mut skip_list = SkipListMap::new();
        let mut kvs = vec![];
        let test_size = 4096;
        for _ in 0..test_size {
            loop {
                let key = rng.gen::<u16>();
                let val = rng.gen::<u16>();
                if kvs.iter().any(|&kv: &(u16, u16)| kv.0 == key) {
                    continue;
                }
                kvs.push((key, val));
                break;
            }
        }
        for i in 0..test_size {
            assert!(
                skip_list.insert_debug(kvs[i].0, kvs[i].1).is_ok(),
                "skip list invariants broke after insert `{:?}`\n{:?}\n{:?}",
                kvs[i],
                &kvs[..i + 1],
                skip_list,
            );
            for j in 0..i + 1 {
                let v = skip_list.get(&kvs[j].0);
                assert!(
                    v.is_some(),
                    "({}) {:?} not found\n{:?}\n{:?}",
                    i + 1,
                    kvs[j],
                    &kvs[..i + 1],
                    skip_list,
                );
                assert_eq!(
                    *v.unwrap(),
                    kvs[j].1,
                    "({}) value of {:?} did not match\n{:?}\n{:?}",
                    i + 1,
                    kvs[j],
                    &kvs[..i + 1],
                    skip_list
                );
            }
        }
        println!("{:?}", skip_list);
    }

    #[test]
    fn test_remove() {
        let mut skip_list = SkipListMap::new();
        skip_list.insert(1, 1);
        skip_list.insert(2, 2);
        //assert_eq!(skip_list.remove(&1), Some(1));
        //assert_eq!(skip_list.remove(&128), None);
    }
}
