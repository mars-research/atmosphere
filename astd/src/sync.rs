//! Synchronization.
//!
//! We re-export `spin` types.

pub use spin::{
    Mutex, MutexGuard, Once, RwLock, RwLockReadGuard, RwLockUpgradableGuard, RwLockWriteGuard,
};
