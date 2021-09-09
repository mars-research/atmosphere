//! The CPU capability.
//!
//! A CPU capability points to a kernel object that provides space
//! for per-CPU data, allowing a new SMP core to be started.

use core::alloc::Layout;
// use crate::cpu::Cpu;

use super::{CapResult, CData};

// pub const OBJECT_LAYOUT: Layout = Layout::new::<Cpu>();
pub const OBJECT_LAYOUT: Layout = Layout::new::<()>();

pub fn new_capability(_object: *const u8) -> CapResult<CData> {
    Ok(CData::Cpu(CpuCap {}))
}

#[derive(Debug)]
pub struct CpuCap {
}
