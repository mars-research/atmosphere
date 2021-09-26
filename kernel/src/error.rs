//! Error handling.

pub type Result<T> = core::result::Result<T, Error>;

use displaydoc::Display;

use crate::vmx::VmxError;
use crate::boot::command_line::Component as CommandLineComponent;

/// An error.
#[non_exhaustive]
#[derive(Clone, Debug, Display)]
pub enum Error {
    /// VT-x subsystem error: {0}
    Vmx(VmxError),

    /// No such script is defined.
    NoSuchScript,

    /// Invalid kernel command-line component: {0:?}
    InvalidCommandLineOption(CommandLineComponent<'static>),

    /// Invalid descriptor type: {0}
    InvalidDescriptorType(u8),

    /// Other error.
    Other(&'static str),
}

impl From<VmxError> for Error {
    fn from(error: VmxError) -> Self {
        Self::Vmx(error)
    }
}
