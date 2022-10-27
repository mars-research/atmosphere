#![no_std]
#![forbid(unsafe_code)]
#![deny(missing_docs)]
// Common lint configs
#![deny(
    asm_sub_register,
    dead_code,
    deprecated,
    missing_abi,
    rustdoc::bare_urls,
    unused_imports,
    unused_must_use,
    unused_mut,
    unused_unsafe,
    unused_variables
)]

//! `astd` provides common data structures and utilities for use in the Atmosphere kernel.
//! It provides statically-sized implementations of common data structures, as well as
//! synchronization-related primitives like mutexes.

pub mod capability;
pub mod cell;
pub mod collections;
pub mod sync;
