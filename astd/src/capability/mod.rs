//! Public capability interface.

/// Result of a capability call.
pub type CapResult<T> = Result<T, CapError>;

/// An error from a capability call.
#[derive(Debug, Clone, Copy)]
pub enum CapError {
    /// There is insufficient memory to perform the action.
    InsufficientMemory,

    /// The capability depth is invalid.
    InvalidDepth,

    /// The supplied capability pointer is invalid.
    InvalidPointer,

    /// The attempted retype operation is not supported.
    NotRetypable,

    /// There is insufficient permission to perform the action.
    PermissionDenied,

    /// The destination capability slot is already taken.
    SlotInUse,
}

/// Type of a capability.
#[repr(u32)]
#[derive(PartialEq, Debug, Clone, Copy)]
pub enum CapType {
    /// CNode.
    CNode,

    /// Untyped memory.
    Untyped,

    /// CPU.
    Cpu,
}

/// A reference to a capability in a CSpace.
#[repr(transparent)]
#[derive(Debug, Clone, Copy)]
pub struct CapPointer(u32);

impl From<u32> for CapPointer {
    fn from(val: u32) -> Self {
        Self(val)
    }
}

impl CapPointer {
    /// Extracts a number of bits from a specified offset from MSB.
    pub fn get_bits(&self, bit_offset: u8, bits: u8) -> Option<u32> {
        if bit_offset + bits > 32 {
            return None;
        }

        let shifted = self.0 >> (32 - bit_offset - bits);
        let mask = (1 << bits) - 1;

        Some(shifted & mask)
    }
}

/// A permission.
#[derive(Debug, Clone, Copy)]
pub enum Permission {
    /// Permission to read.
    Read,

    /// Permission to write.
    Write,

    /// Permission to derive sub-objects.
    Derive,
}

impl Permission {
    /// Returns the bit offset of this permission.
    pub fn bit_offset(&self) -> u32 {
        match self {
            Self::Read => 1,
            Self::Write => 2,
            Self::Derive => 3,
        }
    }

    /// Returns the bitmask of this permission.
    pub fn mask(&self) -> u32 {
        1 << self.bit_offset()
    }
}

/// A set of permissions.
#[derive(PartialEq, Debug, Clone, Copy)]
#[repr(transparent)]
pub struct PermissionSet(u32);

impl PermissionSet {
    /// Returns a permission set with all permissions.
    pub fn maximum() -> Self {
        Self(u32::MAX)
    }

    /// Returns a permission set with no permissions.
    pub fn minimum() -> Self {
        Self(0)
    }

    /// Checks whether a permission is allowed.
    pub fn check(&self, permission: Permission) -> CapResult<()> {
        let mask = 1 << permission.bit_offset();
        if mask & self.0 != 0 {
            Ok(())
        } else {
            Err(CapError::PermissionDenied)
        }
    }

    /// Grants a permission.
    pub fn grant(&mut self, permission: Permission) {
        let mask = 1 << permission.bit_offset();
        self.0 |= mask;
    }
}
