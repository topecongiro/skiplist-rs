use core::{borrow::Borrow, fmt, ptr::NonNull};

use crate::{
    node::{Handle, Node, TableSearchResult, TABLE_SIZE},
    SkipListMap,
};

use self::VisitSkipListResult::*;

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum VisitMode {
    ReadOnly,
    Write,
    Insert,
    Delete,
}

impl VisitMode {
    fn may_insert(&self) -> bool {
        match self {
            VisitMode::Write | VisitMode::Insert => true,
            _ => false,
        }
    }

    fn may_delete(&self) -> bool {
        match self {
            VisitMode::Write | VisitMode::Delete => true,
            _ => false,
        }
    }
}

/// Walks a skip list and creates an entry to the given key. If `collect_node` is set to `true`,
/// the visitor will collect each node that she visited last on each height. These nodes wil be used
/// when inserting a new node to the skip list.
pub struct SkipListVisitor<'a, K, V> {
    /// The highest height of the skip list this visitor is visiting.
    height: usize,
    visit_mode: VisitMode,
    /// A temporal view to the root tower of the skip list.
    root_tower: &'a [Option<NonNull<Node<K, V>>>],
    /// The last-visited node.
    prev_node: Option<NonNull<Node<K, V>>>,
    /// A list of previous nodes.
    prev_nodes: Option<&'a mut [Option<NonNull<Node<K, V>>>]>,
}

/// The result of the `visit_skip_list`.
pub enum VisitSkipListResult<K, V> {
    /// There is a node with the given key.
    ///
    /// # Invariants
    ///
    /// - The node must have more than one key-value paris.
    Found(Handle<K, V>),
    /// There is a node which only contains the given key.
    ///
    /// # Invariants
    ///
    /// - The node must only have a single key-value pair, and its key must match the given key.
    FoundSingle(Handle<K, V>),
    /// There is a node which has a room for the key.
    ///
    /// # Invariants
    ///
    /// - The node must not be full.
    /// - One of the followings must hold:
    ///     - The given key is larger than the node's min key and smaller than its max key.
    ///     - The given key is larger than the node's max key and smaller than the next node's min key.
    Insertable(
        Handle<K, V>,
        bool, /* true if the insert requires a table shift */
    ),

    /// Key-value pairs must be moved-around in order to make a room for the key.
    ///
    /// # Invariants
    ///
    /// - The node must be full.
    /// - The next node must not be full.
    /// - The index will be the given key's index. That is, the following must hold:
    ///   `table[index - 1] <  key < table[index + 1]`.
    Split(Handle<K, V>, usize),

    /// We need to create a new node in order to add the given key.
    ///
    /// # Invariants
    ///
    /// - The node must be full.
    /// - The next node must be full.
    NewNode,
    /// This value is returned when the skip list is empty or the given key was not found
    /// on a read-only traversal.
    NotFound,
}

impl<'b, 'a: 'b, K: 'a, V: 'a> SkipListVisitor<'a, K, V>
where
    K: Ord,
{
    pub fn new(
        skip_list: &'a SkipListMap<K, V>,
        visit_mode: VisitMode,
        prev_nodes: Option<&'a mut [Option<NonNull<Node<K, V>>>]>,
    ) -> Self {
        SkipListVisitor {
            height: skip_list.height(),
            visit_mode,
            root_tower: &skip_list.root_tower,
            prev_node: None,
            prev_nodes,
        }
    }

    fn set_prev_nodes_at(&mut self, prev_node: Option<NonNull<Node<K, V>>>, height: usize) {
        if let Some(prev_nodes) = self.prev_nodes.as_mut() {
            prev_nodes[height] = prev_node
        }
    }

    /// Returns the next node which we should visit next on the given height.
    fn next_node(&self, height: usize) -> Option<NonNull<Node<K, V>>> {
        self.prev_node.map_or(self.root_tower[height], |n| unsafe {
            n.as_ref().next_at(height)
        })
    }

    pub fn visit_skip_list<Q>(&'a mut self, key: &Q) -> VisitSkipListResult<K, V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut height = self.height;
        while height > 0 {
            if let Some(result) = self.visit_height(key.borrow(), height - 1) {
                return result;
            }
            height -= 1;
            self.set_prev_nodes_at(self.prev_node, height);
        }

        if self.visit_mode == VisitMode::ReadOnly || self.prev_node.is_none() {
            VisitSkipListResult::NotFound
        } else {
            unreachable!();
        }
    }

    fn is_prev_node_full(&self) -> bool {
        self.prev_node
            .map_or(true, |n| unsafe { n.as_ref().is_full() })
    }

    fn handle(&self) -> Handle<K, V> {
        let index = unsafe { self.prev_node.unwrap().as_ref().len() };
        debug_assert!(index < TABLE_SIZE);
        Handle {
            node: self.prev_node.unwrap(),
            index,
        }
    }

    /// Walk the given height, starting with the current node.
    // FIXME: Refactor this.
    fn visit_height<Q>(&mut self, key: &Q, height: usize) -> Option<VisitSkipListResult<K, V>>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        loop {
            let node_opt = self.next_node(height);
            let node = match node_opt {
                None if height == 0 => {
                    // FIXME: Refactor this thank you very much.
                    self.set_prev_nodes_at(self.prev_node, 0);
                    return Some(if self.is_prev_node_full() {
                        NewNode
                    } else {
                        Insertable(self.handle(), false)
                    });
                }
                None => return None,
                Some(n) => n,
            };
            let node_ref = unsafe { node.as_ref() };
            match node_ref.search_key(key) {
                TableSearchResult::Found(index) => {
                    return Some(if self.visit_mode.may_delete() && node_ref.len() == 1 {
                        self.collect_prev_nodes(node, height);
                        FoundSingle(Handle { node, index: 0 })
                    } else {
                        Found(Handle { node, index })
                    });
                }
                TableSearchResult::Within(..) if !self.visit_mode.may_insert() => {
                    return Some(NotFound);
                }
                TableSearchResult::Within(index, false) => {
                    return Some(Insertable(Handle { node, index }, true));
                }
                TableSearchResult::Within(_index, true) => {
                    return Some(match node_ref.next_at(0) {
                        // FIXME: Implement splitting table.
                        //Some(next_node) if unsafe { next_node.as_ref().available_spaces() >= 2 } => {
                        //   Split(Handle { node, index }, unsafe {
                        //     next_node.as_ref().available_spaces() / 2
                        //})
                        //}
                        _ => {
                            // Insert a new node after the `node`.
                            self.prev_node = node_opt;
                            for h in 0..=height {
                                self.set_prev_nodes_at(self.prev_node, h);
                            }
                            NewNode
                        }
                    });
                }
                TableSearchResult::Greater(..) => {
                    self.prev_node = Some(node);
                }
                TableSearchResult::Less(true) if height == 0 => {
                    return Some(if self.is_prev_node_full() {
                        self.set_prev_nodes_at(self.prev_node, 0);
                        NewNode
                    } else {
                        Insertable(self.handle(), false)
                    });
                }
                TableSearchResult::Less(false) if height == 0 => {
                    return Some(Insertable(Handle { node, index: 0 }, true));
                }
                TableSearchResult::Less(..) => {
                    return None;
                }
            }
        }
    }

    /// Starting from the `prev_node`, on each height, collect the previous nodes of the
    /// `target_node`.
    ///
    /// ### Invariants
    ///
    /// - `self.prev_node.height() >= target_node.height()`, because we reached to the `target_node`
    ///   from `self.prev_node` while traversing `max_height`.
    fn collect_prev_nodes(&mut self, target_node: NonNull<Node<K, V>>, mut height: usize) {
        loop {
            if let Some(mut prev_node) = self.prev_node.or(self.root_tower[height]) {
                match unsafe { prev_node.as_ref().next_at(height) } {
                    Some(mut prev_next_node) => {
                        while prev_next_node.as_ptr() != target_node.as_ptr() {
                            prev_node = prev_next_node;
                            prev_next_node = unsafe { prev_node.as_ref().next_at(height) }.unwrap();
                        }
                        self.set_prev_nodes_at(Some(prev_node), height);
                        self.prev_node = Some(prev_node);
                    }
                    None => {
                        self.set_prev_nodes_at(Some(prev_node), height);
                    }
                }
            } else {
                self.set_prev_nodes_at(None, height);
            }
            if height == 0 {
                break;
            }
            height -= 1;
        }
    }
}

impl<K, V> fmt::Debug for VisitSkipListResult<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Found(..) => "Found",
                FoundSingle(..) => "FoundSingle",
                NewNode => "NewNode",
                Insertable(..) => "Insertable",
                NotFound => "NotFound",
                Split(..) => "Split",
            }
        )
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{node::MAX_TOWER_HEIGHT, SkipListMap};

    fn set_up_skip_list() -> SkipListMap<usize, usize> {
        let mut list: SkipListMap<usize, usize> = SkipListMap::new();
        let mut prev_nodes = [None; MAX_TOWER_HEIGHT];
        let mut visitor = SkipListVisitor::new(&mut list, VisitMode::Insert, Some(&mut prev_nodes));
        if let VisitSkipListResult::NotFound = visitor.visit_skip_list(&3) {
            // ok
        } else {
            unreachable!("Expected NotFound");
        }
        list.root_tower[0] = Some(Node::new_with_height(1));
        list.len = 3;
        list.height = 1;
        unsafe {
            list.root().unwrap().as_mut().insert(1, 1);
            list.root().unwrap().as_mut().insert(3, 3);
            list.root().unwrap().as_mut().insert(5, 5);
        }
        list
    }

    fn single_skip_list() -> SkipListMap<usize, usize> {
        let mut skip_list = SkipListMap::new();
        skip_list.root_tower[0] = Some(Node::new_with_height(2));
        skip_list.root_tower[1] = skip_list.root_tower[0];
        skip_list.len = 16;
        skip_list.height = 2;
        for i in 0..16 {
            unsafe {
                skip_list.root().unwrap().as_mut().insert(i, i);
            }
        }
        skip_list
    }

    #[test]
    fn test_full_node_visit() {
        let mut skip_list = single_skip_list();
        let mut prev_nodes = [None; MAX_TOWER_HEIGHT];
        let mut visitor =
            SkipListVisitor::new(&mut skip_list, VisitMode::Insert, Some(&mut prev_nodes));
        let result = visitor.visit_skip_list(&16);
        if let VisitSkipListResult::NewNode = result {
            // ok
        } else {
            unreachable!("Expected 'NewNode', found '{:?}'", result);
        }
    }

    #[test]
    fn test_visitor() {
        let mut skip_list = set_up_skip_list();
        let keys = &[1, 3, 5];
        let mut prev_nodes = [None; MAX_TOWER_HEIGHT];
        for key in keys {
            let mut visitor =
                SkipListVisitor::new(&mut skip_list, VisitMode::Insert, Some(&mut prev_nodes));
            if let VisitSkipListResult::Found(..) = visitor.visit_skip_list(key) {
                // ok
            } else {
                unreachable!("key {} not found", key);
            }
        }
        for (i, key) in [0, 2, 4, 8].iter().enumerate() {
            let mut visitor =
                SkipListVisitor::new(&mut skip_list, VisitMode::Insert, Some(&mut prev_nodes));
            match visitor.visit_skip_list(key) {
                VisitSkipListResult::Insertable(handle, ..) => {
                    assert_eq!(handle.index, i, "handle index for {} is wrong", key)
                }
                VisitSkipListResult::NotFound => {
                    unreachable!("Expected insertable for {}, got not found", key)
                }
                VisitSkipListResult::Found(..) => {
                    unreachable!("Expected insertable, but found a {}", key)
                }
                VisitSkipListResult::FoundSingle(..) => {
                    unreachable!("FoundSingle should not be returned on Insert mode: {}", key)
                }
                VisitSkipListResult::NewNode => unreachable!(
                    "Expected insertable, but got new node while the node has an empty space: {}",
                    key
                ),
                VisitSkipListResult::Split(..) => {
                    unreachable!("Expected insertable for {}, got split", key)
                }
            }
        }
    }
}
