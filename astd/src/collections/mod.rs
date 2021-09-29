//! Statically-Sized Collections.
//!
//! This module contains statically-sized implementations of common data structures.
//! The Atmosphere kernel does not perform dynamic memory allocation, and all data structures
//! required for the kernel are created in advance.
//!
//! For some data structures, we re-export existing implementations like
//! [StaticVec](https://github.com/slightlyoutofphase/staticvec).

pub mod vec;
pub mod string;
pub mod deque;
