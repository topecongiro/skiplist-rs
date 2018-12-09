use core::{
    fmt,
    marker::PhantomData,
    mem::size_of,
    ptr,
    slice::{from_raw_parts, from_raw_parts_mut},
};

use parking_lot::Mutex;
use rand::{rngs::SmallRng, FromEntropy, Rng};

use crate::node::Node;

lazy_static! {
    static ref small_rng: Mutex<SmallRng> = Mutex::new(SmallRng::from_entropy());
}

pub const MAX_TOWER_HEIGHT: usize = 64;

/// Generates a random height of a tower. The return value could be 0 and
/// must be smaller than `MAX_TOWER_HEIGHT`.
pub fn random_height() -> usize {
    let mut rng = small_rng.lock();
    let random_number: u64 = rng.gen();
    let height = (random_number.trailing_zeros() as usize) % MAX_TOWER_HEIGHT + 1;
    debug_assert!(height < MAX_TOWER_HEIGHT);
    height
}

/// `Tower` represents a list of pointer to the next node.
/// Note that the every pointer held by the tower must be initialized upon
/// creating a new `Tower`: they must be either a pointer to the valid node
/// or the sentinel node.
pub struct Tower<K, V> {
    /// A height of this node.
    height: usize,
    phantom: PhantomData<*mut Node<K, V>>,
}

impl<K, V> Tower<K, V> {
    /// Creates a new tower. This is extremely unsafe, as it initializes
    /// memory locations outside of `Tower` itself. The caller must make
    /// sure that the memory is pre-allocated before calling this function.
    pub unsafe fn new(tower_ptr: *const Tower<K, V>, height: usize) -> Tower<K, V> {
        let tower = Tower {
            height,
            phantom: PhantomData,
        };

        let ptr = Self::_tower_ptr(tower_ptr);
        for count in 0..height {
            ptr.add(count as usize).write(ptr::null_mut());
        }

        tower
    }

    /// Returns the height of the tower.
    pub fn height(&self) -> usize {
        self.height as usize
    }

    unsafe fn _tower_ptr(ptr: *const Tower<K, V>) -> *mut *mut Node<K, V> {
        ptr.offset(1) as *mut *mut Node<K, V>
    }

    fn tower_ptr(&self) -> *mut *mut Node<K, V> {
        unsafe { Self::_tower_ptr(self as *const Tower<K, V>) }
    }

    /// Returns a pointer to the node at the given height.
    ///
    /// # Safety
    ///
    /// This function is unsafe as if the given `height` is larger than the
    /// height of the tower, it may access an invalid memory address.
    pub unsafe fn next_at(&self, height: usize) -> *mut Node<K, V> {
        debug_assert!(
            height < self.height as usize,
            "height < self.height failed, height: {}, self.height: {}",
            height,
            self.height
        );
        let mut tower_ptr = self.tower_ptr() as usize;
        tower_ptr += height * size_of::<*mut *mut Node<K, V>>();
        (tower_ptr as *mut *mut Node<K, V>).read()
    }

    /// Set a pointer to the next node at the given height.
    /// Returns the previously stored pointer if available.
    ///
    /// # Safety
    ///
    /// This function is unsafe as if the given `height` is larger than the
    /// height of the tower, it may access an invalid memory address.
    pub unsafe fn set_next_at(&mut self, height: usize, ptr: *mut Node<K, V>) {
        debug_assert!(
            height < self.height as usize,
            "height < self.height failed, height: {}, self.height: {}",
            height,
            self.height
        );
        let mut tower_ptr = self.tower_ptr() as usize;
        tower_ptr += height * size_of::<*mut *mut Node<K, V>>();
        (tower_ptr as *mut *mut Node<K, V>).write(ptr);
    }
}

impl<K, V> fmt::Debug for Tower<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Tower {{\n  height: {},\n  pointers: {{\n", self.height)?;
        for i in 0..self.height {
            let height = self.height - i;
            write!(f, "    {}: {:?}\n", (height), unsafe {
                self.next_at(height - 1)
            })?;
        }
        write!(f, "  }},\n}}")
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_random_height() {
        use crate::std::collections::BTreeMap;
        let mut map = BTreeMap::new();
        for _ in 0..100000 {
            let height = random_height();
            assert_ne!(height, 0);
            assert!(height <= MAX_TOWER_HEIGHT);
            let counter = map.entry(height).or_insert(0);
            *counter += 1;
        }

        // Run `cargo test test_random_height -- --nocapture` to see the height distribution.
        for (k, v) in map {
            println!("{0: >2} appeared {1: >5} times", k, v);
        }
    }

    #[test]
    fn test_set_next_at() {
        use crate::node::Node;
        use core::ptr::NonNull;
        // FIXME: The test breaks when we use 63 as height.
        let height = MAX_TOWER_HEIGHT;
        let mut node_ptr: NonNull<Node<usize, usize>> = Node::new_with_height(height);
        let mut nodes = vec![];
        for _ in 0..height {
            nodes.push(Node::<usize, usize>::new())
        }
        for i in 0..height {
            unsafe {
                node_ptr.as_mut().set_next_at(i, Some(nodes[i]));
            }
        }
        for i in 0..height {
            unsafe {
                assert_eq!(nodes[i], node_ptr.as_ref().next_at(i).unwrap(), "i = {}", i);
            }
        }
    }
}
