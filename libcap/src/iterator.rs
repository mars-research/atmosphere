//! Capability iterators.

use core::iter::Iterator;
use core::marker::PhantomData;
use core::ptr;

use super::Capability;

#[derive(Debug, Clone, Copy)]
pub enum CapIterType {
    /// Sibling capabilities at a certain depth.
    ///
    /// We will traverse through all capabilities with the same depth, skipping capabilities
    /// with greater depths and stopping at a capability with a lesser depth.
    Sibling(usize),

    /// All siblings and their recursive children at or below a certain depth.
    SiblingAndRecursiveChildren(usize),
}

/// An immutable iterator to traverse in a CSpace.
pub struct CapIter<'a> {
    /// Type of iteration.
    iter_type: CapIterType,

    /// The next capability in the iteration.
    next: Option<*const Capability>,
    _phantom: PhantomData<&'a Capability>,
}

impl<'a> CapIter<'a> {
    /// Creates an empty iterator.
    pub fn empty() -> Self {
        Self {
            iter_type: CapIterType::Sibling(0),
            next: None,
            _phantom: PhantomData,
        }
    }

    /// Creates a new iterator.
    pub(super) unsafe fn new(iter_type: CapIterType, next: *const Capability) -> Self {
        assert_ne!(next, ptr::null());

        Self {
            iter_type,
            next: Some(next),
            _phantom: PhantomData,
        }
    }
}

impl<'a> Iterator for CapIter<'a> {
    type Item = &'a Capability;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.map(|cap| {
            let cap = unsafe { &*cap };

            let mut next = cap.next;

            loop {
                match unsafe { next.as_ref() } {
                    None => {
                        self.next = None;
                        break;
                    }
                    Some(next_cap) => {
                        match self.iter_type {
                            CapIterType::Sibling(depth) => {
                                if next_cap.depth > depth {
                                    // skip
                                    next = next_cap.next;
                                    continue;
                                }

                                if next_cap.depth == depth {
                                    self.next = Some(next);
                                    break;
                                }

                                if next_cap.depth < depth {
                                    self.next = None;
                                    break;
                                }
                            }
                            CapIterType::SiblingAndRecursiveChildren(depth) => {
                                self.next = if next_cap.depth < depth {
                                    None
                                } else {
                                    Some(next)
                                };

                                break;
                            }
                        }
                    }
                }
            }

            cap
        })
    }
}
