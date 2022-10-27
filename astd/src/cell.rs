//! Shareable mutable containers.
//!
//! This module re-exports the atomic RefCell implementation in [`atomic_refcell`].
//! This is a more performant alternative than RwLock.

pub use atomic_refcell::{AtomicRef, AtomicRefCell, AtomicRefMut};
