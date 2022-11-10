#![no_std]

extern crate alloc;

pub mod arp;
pub mod layer;
pub mod stack;
pub mod util;
pub mod netmanager;

#[cfg(test)]
#[macro_use]
extern crate std;

#[cfg(test)]
mod tests;

pub struct DummyNic;
