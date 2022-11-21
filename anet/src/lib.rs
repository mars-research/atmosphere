#![no_std]

extern crate alloc;

pub mod arp;
pub mod layer;
pub mod netmanager;
pub mod nic;
pub mod stack;
pub mod util;

#[cfg(test)]
#[macro_use]
extern crate std;

#[cfg(test)]
mod tests;

pub type Result<T> = core::result::Result<T, ErrorKind>;

pub type RpcResult<T> = core::result::Result<T, RpcError>;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[allow(deprecated)]
#[non_exhaustive]

pub enum ErrorKind {
    RpcError,
}

/// A wrapper that hides the ErrorEnum
#[derive(Debug, Copy, Clone)]
pub struct RpcError {
    error: ErrorEnum,
}

impl RpcError {
    pub unsafe fn panic() -> Self {
        Self {
            error: ErrorEnum::PanicUnwind,
        }
    }
}

#[derive(Debug, Copy, Clone)]

enum ErrorEnum {
    /// Callee domain is panicked and unwinded
    PanicUnwind,
}
