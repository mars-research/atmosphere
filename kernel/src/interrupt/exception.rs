//! X86 Exceptions.

use core::convert::TryFrom;

pub const EXCEPTION_MAX: usize = 31;

/// An exception.
#[derive(Copy, Clone, Debug)]
pub enum Exception {
    /// Device-By-Zero (#DE)
    DivideByZero,

    /// Debug (`#DB`)
    Debug,

    /// Non-Maskable Interrupt
    NonMaskableInterrupt,

    /// Breakpoint (`#BP`)
    Breakpoint,

    /// Overflow (`#OF`)
    Overflow,

    /// Bound-Range Exception (`#BR`)
    BoundRangeExceeded,

    /// Invalid Opcode (`#UD`)
    InvalidOpcode,

    /// Device Not Available (`#NM`)
    DeviceNotAvailable,

    /// Double Fault (`#DF`)
    DoubleFault,

    /// Invalid TSS (`#TS`)
    InvalidTss,

    /// Segment Not Present (`#NP`)
    SegmentNotPresent,

    /// Stack Segment Fault (`#SS`)
    StackSegmentFault,

    /// General Protection Fault (`#GP`)
    GeneralProtectionFault,

    /// Page Fault (`#PF`)
    PageFault,

    /// X87 Floating-Point Exception (`#MF`)
    X87FloatingPoint,

    /// Alignment Check (`#AC`)
    AlignmentCheck,

    /// Machine Check (`#MC`)
    MachineCheck,

    /// SIMD Floating-Point (`#XM`)
    SimdFloatingPoint,

    /// Virtualization (`#VE`)
    Virtualization,

    /// Security (`#SX`)
    Security,

    /// Reserved
    ///
    /// This can be one of:
    /// - 0x9 - Obsolete exception used for "Co-processor Segment Overrun"
    /// - 0xf
    /// - 0x15 to 0x1d, inclusive
    /// - 0x1f
    Reserved(usize),
}

impl From<Exception> for usize {
    fn from(exception: Exception) -> usize {
        use Exception::*;

        match exception {
            DivideByZero => 0x0,
            Debug => 0x1,
            NonMaskableInterrupt => 0x2,
            Breakpoint => 0x3,
            Overflow => 0x4,
            BoundRangeExceeded => 0x5,
            InvalidOpcode => 0x6,
            DeviceNotAvailable => 0x7,
            DoubleFault => 0x8,
            InvalidTss => 0xa,
            SegmentNotPresent => 0xb,
            StackSegmentFault => 0xc,
            GeneralProtectionFault => 0xd,
            PageFault => 0xe,
            X87FloatingPoint => 0x10,
            AlignmentCheck => 0x11,
            MachineCheck => 0x12,
            SimdFloatingPoint => 0x13,
            Virtualization => 0x14,
            Security => 0x1e,
            Reserved(num) => num,
        }
    }
}

impl TryFrom<usize> for Exception {
    type Error = &'static str;

    fn try_from(num: usize) -> Result<Self, Self::Error> {
        use Exception::*;

        if num >= EXCEPTION_MAX {
            return Err("Not an exception");
        }

        match num {
            0x0 => Ok(DivideByZero),
            0x1 => Ok(Debug),
            0x2 => Ok(NonMaskableInterrupt),
            0x3 => Ok(Breakpoint),
            0x4 => Ok(Overflow),
            0x5 => Ok(BoundRangeExceeded),
            0x6 => Ok(InvalidOpcode),
            0x7 => Ok(DeviceNotAvailable),
            0x8 => Ok(DoubleFault),
            0xa => Ok(InvalidTss),
            0xb => Ok(SegmentNotPresent),
            0xc => Ok(StackSegmentFault),
            0xd => Ok(GeneralProtectionFault),
            0xe => Ok(PageFault),
            0x10 => Ok(X87FloatingPoint),
            0x11 => Ok(AlignmentCheck),
            0x12 => Ok(MachineCheck),
            0x13 => Ok(SimdFloatingPoint),
            0x14 => Ok(Virtualization),
            0x1e => Ok(Security),
            num => Ok(Reserved(num)),
        }
    }
}
