#![no_std]
#![feature(alloc)]
#![feature(maybe_uninit)]

extern crate alloc;

#[macro_use]
extern crate lazy_static;

#[cfg(test)]
#[macro_use]
extern crate std;

mod node;
mod skiplist;
mod visitor;

pub use self::skiplist::SkipListMap;
