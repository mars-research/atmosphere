//! Error handling.

pub type Result<T> = core::result::Result<T, Error>;

use snafu::Snafu;

use crate::vmx::VmxError;
use crate::boot::command_line::Component as CommandLineComponent;

/// An error.
#[non_exhaustive]
#[derive(Clone, Debug, Snafu)]
pub enum Error {
    /// VT-x subsystem error.
    #[snafu(display("VT-x subsystem error: {}", error))]
    Vmx { error: VmxError },

    /// No such script is defined.
    NoSuchScript,

    /// Invalid kernel command-line.
    #[snafu(display("Invalid kernel command-line component: {:?}", component))]
    InvalidCommandLineOption { component: CommandLineComponent<'static> },

    /// Invalid descriptor type.
    #[snafu(display("Invalid descriptor type: {:#x}", descriptor_type))]
    InvalidDescriptorType { descriptor_type: u8 },

    /// Other error.
    #[snafu(display("Other error: {}", description))]
    Other { description: &'static str },
}

impl From<VmxError> for Error {
    fn from(error: VmxError) -> Self {
        Self::Vmx { error }
    }
}
