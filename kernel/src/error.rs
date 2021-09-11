//! Error handling.

pub type Result<T> = core::result::Result<T, Error>;

use super::vmx::VmxError;

use snafu::Snafu;

/// An error.
#[non_exhaustive]
#[derive(Clone, Debug, Snafu)]
pub enum Error {
    /// VT-x subsystem error.
    #[snafu(display("VT-x subsystem error: {}", error))]
    Vmx { error: VmxError },

    /// No such script is defined.
    NoSuchScript,

    /// Other error.
    #[snafu(display("Other error: {}", description))]
    Other { description: &'static str },
}

impl From<VmxError> for Error {
    fn from(error: VmxError) -> Self {
        Self::Vmx { error }
    }
}
