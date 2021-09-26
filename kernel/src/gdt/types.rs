//! Types.
//!
//! Well, most of this doesn't matter at all in Long Mode anyways ¯\_(ツ)_/¯

use core::convert::TryFrom;

use bitfield::bitfield;

use crate::error::{Error, Result};

bitfield! {
    /// The Access Byte for Code and Data descriptors.
    ///
    /// This struct is only for Code and Data descriptors.
    /// The meaning of bits 0-3 is different for System descriptors (e.g., TSS),
    /// and you should use [SystemAccessByte] instead.
    pub struct AccessByte(u8);
    impl Debug;

    /// The Present bit.
    #[inline]
    present, set_present: 7;

    /// The descriptor privilege level.
    #[inline]
    pub privilege, set_privilege: 6, 5;

    /// Whether this segment is Code or Data.
    ///
    /// This should be 1.
    /// The meaning of bits 0-3 is different for System descriptors (e.g., TSS),
    /// and you should use [SystemAccessByte] instead.
    #[inline]
    code_data, set_code_data: 4;

    /// Whether this segment is executable.
    #[inline]
    pub executable, set_executable: 3;

    /// The Direction (Data) or Conforming (Code) bit.
    ///
    /// For data segments, this is the Direction bit.
    /// 0 means that the segment grows up.
    ///
    /// For code segments, this is the Confirming bit.
    /// 0 means that the segment can only be executed from the ring set in DPL.
    /// 1 means that the segment can only be executed from a ring equal or lower than DPL.
    #[inline]
    pub direction, set_direction: 2;

    /// The Writable (Data) or Readable (Code) bit.
    ///
    /// For data segments, this is the Writable bit.
    /// For code segments, this is the Readable bit.
    #[inline]
    pub read_write, set_read_write: 1;

    /// The Accessed bit.
    ///
    /// The processor will set it to 1 internally.
    ///
    /// ## VT-x
    ///
    /// When setting the Access Bytes of a segment in the Guest-State Area,
    /// this bit must be 1. This is because you are directly setting the
    /// segment descriptor cache in the internal processor state.
    #[inline]
    accessed, set_accessed: 0;
}

impl AccessByte {
    pub fn new() -> Self {
        let mut access = Self(0);
        access.set_present(true);
        access.set_code_data(true);
        access
    }

    pub const fn not_present() -> Self {
        Self(0)
    }
}

bitfield! {
    /// The Access Byte for System descriptors.
    pub struct SystemAccessByte(u8);
    impl Debug;

    /// The Present bit.
    #[inline]
    present, set_present: 7;

    /// The descriptor privilege level.
    #[inline]
    pub privilege, set_privilege: 6, 5;

    /// Whether this segment is Code or Data.
    ///
    /// This should be 0.
    /// The meaning of bits 0-3 is different for Code and Data descriptors,
    /// and you should use [AccessByte] instead.
    #[inline]
    code_data, set_code_data: 4;

    /// Type of the descriptor.
    real_descriptor_type, set_real_descriptor_type: 3, 0;
}

impl SystemAccessByte {
    pub fn new(descriptor_type: SystemDescriptorType) -> Self {
        let mut access = Self(0);
        access.set_present(true);
        access.set_code_data(false);
        access.set_descriptor_type(descriptor_type);
        access
    }

    pub const fn not_present() -> Self {
        Self(0)
    }

    pub fn set_descriptor_type(&mut self, descriptor_type: SystemDescriptorType) {
        self.set_real_descriptor_type(descriptor_type.into());
    }
}

/// The type of a System descriptor.
#[derive(Debug, Copy, Clone)]
pub enum SystemDescriptorType {
    /// An available TSS.
    AvailableTss,

    /// A busy TSS.
    BusyTss,
}

impl Into<u8> for SystemDescriptorType {
    fn into(self) -> u8 {
        match self {
            Self::AvailableTss => 0b1001,
            Self::BusyTss => 0b1011,
        }
    }
}

impl TryFrom<u8> for SystemDescriptorType {
    type Error = Error;

    fn try_from(descriptor_type: u8) -> Result<Self> {
        match descriptor_type {
            0b1001 => Ok(Self::AvailableTss),
            0b1011 => Ok(Self::BusyTss),
            _ => Err(Error::InvalidDescriptorType { descriptor_type }),
        }
    }
}
