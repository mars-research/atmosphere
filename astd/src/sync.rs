//! Synchronization.
//!
//! We re-export `spin` types.

pub use spin::{
    Once,

    Mutex,
    MutexGuard,

    RwLock,
    RwLockReadGuard,
    RwLockUpgradableGuard,
    RwLockWriteGuard,
};
