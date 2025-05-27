#![no_std]

extern crate alloc;

pub mod device;
pub mod kernel_config;

pub mod sync_irq;
pub mod memory_structs;
pub mod memory;
pub mod pci;
pub mod mlx_ethernet;
pub mod nic_initialization;
pub mod nic_buffers;
