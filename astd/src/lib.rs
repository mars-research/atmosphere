#![no_std]
#![forbid(unsafe_code)]
#![feature(const_fn_trait_bound)]

#![deny(missing_docs)]

//! `astd` provides common data structures and utilities for use in the Atmosphere kernel.
//! It provides statically-sized implementations of common data structures, as well as
//! synchronization-related primitives like mutexes.

pub mod capability;
pub mod sync;
pub mod collections;
