//! Capability tests (std).

pub use std::prelude::v1::*;

use super::*;

/// A CSpace with backing storage.
struct AllocCSpace {
    cspace: CSpace,
    _memory: Vec<u8>,
}

impl Deref for AllocCSpace {
    type Target = CSpace;

    fn deref(&self) -> &Self::Target {
        &self.cspace
    }
}

impl DerefMut for AllocCSpace {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.cspace
    }
}

impl AllocCSpace {
    /// Create a new CSpace.
    fn new() -> Self {
        let size = 10 * 1024 * 1024; // 10MiB
        let memory = Vec::with_capacity(size);
        let cspace = unsafe {
            CSpace::bootstrap_system(memory.as_ptr(), size).unwrap()
        };

        Self {
            cspace,
            _memory: memory,
        }
    }
}

#[test]
fn test_cspace_init() {
    AllocCSpace::new();
}

#[test]
fn test_cspace_sanity() {
    let cspace = AllocCSpace::new();
    println!("Initial CSpace: {}", *cspace);

    let cnode = cspace.root_object();

    cnode.get(0)
        .expect("Slot 0 must exist")
        .as_ref()
        .expect("Slot 0 must not be empty")
        .as_untyped()
        .expect("Slot 0 must be an Untyped");
}

#[test]
fn test_untyped_retype() {
    let cspace = AllocCSpace::new();
    let cnode = cspace.root_object();
    let untyped = cnode.get(0).unwrap().as_ref().unwrap().as_untyped().unwrap();

    let destination = {
        let first_layer = 1;
        (first_layer << (32 - 8)).into()
    };
    untyped.retype(CapType::Cpu, &cspace, destination)
        .expect("Failed to retype");

    cnode.get(1)
        .expect("Slot 1 must exist")
        .as_ref()
        .expect("Slot 1 must not be empty")
        .as_cpu()
        .expect("Slot 1 must be a Cpu");
}
