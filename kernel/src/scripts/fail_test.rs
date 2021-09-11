//! Fail test script.

use crate::error::{Error, Result};

pub unsafe fn run() -> Result<()> {
    Err(Error::Other {
        description: "test failure",
    })
}
