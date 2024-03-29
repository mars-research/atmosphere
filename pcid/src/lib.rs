#![no_std]
#![feature(asm_const)]
#![crate_name = "pcid"]
#![crate_type = "lib"]

#[macro_use]
extern crate bitflags;
extern crate byteorder;
#[macro_use]
extern crate serde_derive;

pub use log::info as println;

mod bar;
mod bus;
mod class;
mod dev;
pub mod func;
pub mod header;
pub mod pci;
pub mod utils;

pub use crate::bar::PciBar;
pub use crate::bus::{PciBus, PciBusIter};
pub use crate::class::PciClass;
pub use crate::dev::{PciDev, PciDevIter};
pub use crate::func::PciFunc;
pub use crate::header::{PciHeader, PciHeaderError, PciHeaderType};
