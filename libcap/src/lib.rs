//! Capabilities.
//!
//! We implement capabilities in an seL4-inspired manner, with several adaptations
//! to make their use more ergonomic in Rust and to take advantage of Rust's
//! lifetime and ownership system. Most structures here are internal to the
//! microkernel, and currently we do not implement guards in CNodes.
//!
//! The naming here is a bit of a mess. For consistency, data structures usable
//! in [`astd`] are prefixed by Cap-, like [`CapResult`] and [`CapPointer`].
//!
//! Each capability may correspond to a type of kernel object with the layout
//! defined as `OBJECT_LAYOUT` in its module (e.g., [`cpu::OBJECT_LAYOUT`]).
//! Having a layout allows the capability to be derived from an Untyped capability
//! via the retype operation. Retyping is not possible for capabilities that
//! require special parameters to initialize.

#![no_std]

#![feature(
    arbitrary_self_types,
)]

#![deny(
    asm_sub_register,
    dead_code,
    deprecated,
    missing_abi,
    rustdoc::bare_urls,
    unused_imports,
    unused_must_use,
    unused_mut,
    unused_unsafe,
    unused_variables,
)]

#[cfg(test)]
#[macro_use]
extern crate std;

pub mod iterator;

pub mod cpu;
pub mod untyped;

#[cfg(test)]
mod tests;

use core::fmt;
use core::mem;
use core::ptr;
use core::alloc::Layout;
use core::ops::Deref;
use core::ops::DerefMut;
use core::marker::PhantomData;

use astd::capability::{
    CapResult,
    CapError,
    CapType,
    CapPointer,
};
use iterator::{CapIter, CapIterType};

pub type CSlot = Option<Capability>;

macro_rules! downcast_method {
    ($name:ident, $cap_name:expr, $cap_type:path, $inner_type:path) => {
        #[doc = "Downcasts the capability if it's a"]
        #[doc = $cap_name]
        pub fn $name<'cap>(&'cap self) -> Option<DowncastedCap<'cap, $inner_type>> {
            if self.data.capability_type() == $cap_type {
                Some(unsafe { DowncastedCap::new_unchecked(
                    self as *const Capability,
                    self.data.data(),
                ) })
            } else {
                None
            }
        }
    };
    ($name:ident, $cap_type:path, $inner_type:path) => {
        downcast_method!($name, stringify!($cap_type), $cap_type, $inner_type);
    };
}

/// A capability space.
#[derive(Debug)]
pub struct CSpace {
    /// The root CNode.
    root: *const CNode,
}

impl CSpace {
    /// Resolves a CapPointer and returns a reference to the CSlot.
    pub fn resolve(&self, pointer: CapPointer) -> Option<&mut CSlot> {
        let resolution = CapPointerResolution::new(pointer);
        self.root_object().resolve_ptr(resolution).map(|p| unsafe { &mut *p })
    }

    /// Bootstraps a CSpace with system-level capabilities.
    ///
    /// You need to supply a range of memory to hold the initial CNode. The
    /// remaining space will be usable through an Untyped capability.
    pub unsafe fn bootstrap_system(base: *const u8, size: usize) -> CapResult<CSpace> {
        let radix = 8; // 256 slots
        let cnode_size = CNode::mem_required(radix);

        if size < cnode_size {
            return Err(CapError::InsufficientMemory);
        }

        let cnode_base = base as *const _ as *mut CNode;

        let cnode = CNode::with_radix(cnode_base, radix);
        let untyped = untyped::UntypedCap::new(size - cnode_size);
        let cap = Capability {
            object: base.add(cnode_size),
            data: CData::Untyped(untyped),
            // permissions: PermissionSet::maximum(),
            prev: ptr::null(),
            next: ptr::null(),
            depth: 0,
        };
        cnode.insert(cap).unwrap();

        Ok(CSpace {
            root: cnode as *const CNode,
        })
    }

    #[inline]
    const fn root_object(&self) -> &CNode {
        unsafe { &*self.root }
    }
}

impl fmt::Display for CSpace {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let state = CSpaceDisplay {
            depth: 0,
        };
        writeln!(f, "[CSpace]")?;
        self.root_object().display_recursive(f, state)
    }
}

/// State for `Display`-ing a CSpace.
#[derive(Debug)]
struct CSpaceDisplay {
    depth: usize,
}

impl CSpaceDisplay {
    /// Displays a range of empty CSlots.
    ///
    /// The start and end indices are inclusive.
    fn display_empty(&self, f: &mut fmt::Formatter, start: usize, end: usize) -> fmt::Result {
        self.display_indentation(f)?;

        if start == end {
            writeln!(f, "{}: Empty", start)?;
        } else {
            writeln!(f, "{}..{}: Empty", start, end)?;
        }

        Ok(())
    }

    /// Displays the depth-based indentation.
    fn display_indentation(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for _ in 0..self.depth {
            write!(f, "  ")?;
        }
        write!(f, "▶ ")
    }

    /// Returns a copy with depth 1 level deeper.
    fn child(&self) -> Self {
        Self {
            depth: self.depth + 1,
        }
    }
}

/// An in-progress CapPointer resolution.
///
/// We keep track of how many bits have already been resolved.
struct CapPointerResolution {
    pointer: CapPointer,
    bit_offset: u8,
}

impl CapPointerResolution {
    fn new(pointer: CapPointer) -> Self {
        Self {
            pointer,
            bit_offset: 0,
        }
    }

    /// Extract a number of bits from the not-yet-resolved end of MSB.
    fn take_bits(&mut self, bits: u8) -> Option<u32> {
        let r = self.pointer.get_bits(self.bit_offset, bits);
        self.bit_offset += bits;
        r
    }
}

/// A capability node which contains a variable number of CSlots.
///
/// The memory CNodes reside in is managed by capabilities ([`CNodeCap`]).
/// This structure is internal to the microkernel.
#[repr(C)]
pub struct CNode {
    /// The number of slots this CNode holds, in powers of 2.
    ///
    /// A value of 2 means that this CNode has 2^2 = 4 nodes.
    radix: u8,

    /// Unused.
    _pad: u8,

    // What follows are (2^radix) CSlots.
}

impl CNode {
    /// Construct a CNode with a given radix.
    pub unsafe fn with_radix(address: *mut CNode, radix: u8) -> &'static mut CNode {
        let cnode = CNode {
            radix,
            _pad: 0,
        };

        ptr::write_volatile(address, cnode);
        let cnode = &mut *address;

        // FIXME: Slow
        for i in 0..cnode.capacity() {
            let slot = cnode.get_ptr(i).unwrap() as *mut CSlot;
            ptr::write_unaligned(slot, None);
        }

        &mut *address
    }

    /// Returns the required size of a CNode with given radix.
    pub fn mem_required(radix: u8) -> usize {
        mem::size_of::<CNode>() + mem::size_of::<CSlot>() * (1 << radix)
    }

    /// Returns the CNode's size in memory.
    #[inline]
    pub fn mem_size(&self) -> usize {
        mem::size_of::<CNode>() + mem::size_of::<CSlot>() * self.capacity()
    }

    /// Returns the total number of CSlots.
    #[inline]
    pub fn capacity(&self) -> usize {
        1 << self.radix
    }

    /// Returns a reference to the nth element in the CNode.
    fn get(&self, index: usize) -> Option<&CSlot> {
        self.get_ptr(index).map(|address| {
            unsafe { &*address }
        })
    }

    /// Returns a mutable reference to the nth element in the CNode.
    fn get_mut(&mut self, index: usize) -> Option<&mut CSlot> {
        self.get_ptr(index).map(|address| {
            unsafe { &mut *(address as *mut CSlot) }
        })
    }

    /// Resolve a CapPointer and returns a pointer to the CSlot.
    fn resolve_ptr(&self, mut resolution: CapPointerResolution) -> Option<*mut CSlot> {
        let index = resolution.take_bits(self.radix)?;

        let slot = self.get(index as usize)?;
        if let Some(cap) = &slot {
            if let Some(cnode_cap) = cap.as_cnode() {
                return cnode_cap.cnode_object().resolve_ptr(resolution);
            }
        }

        Some(slot as *const CSlot as *mut CSlot)
    }

    /// Returns the index of the first empty CSlot in this CNode, if it exists.
    fn first_empty(&mut self) -> Option<usize> {
        for slot in 0..self.capacity() {
            if self.get(slot).unwrap().is_none() {
                return Some(slot);
            }
        }

        None
    }

    /// Insert a capability into the first empty CSlot, returning its index and address.
    unsafe fn insert(&mut self, capability: Capability) -> Option<(usize, *const Capability)> {
        let slot = self.first_empty()?;
        let slot_opt = self.get_mut(slot).unwrap();
        slot_opt.replace(capability);

        let addr = slot_opt.as_ref().unwrap() as *const Capability;
        Some((slot, addr))
    }

    /// Returns the pointer to the nth CSlot.
    #[inline]
    fn get_ptr(&self, index: usize) -> Option<*const CSlot> {
        if index >= self.capacity() {
            return None;
        }

        unsafe {
            let base = (self as *const CNode).offset(1) as *const CSlot;
            Some(base.add(index))
        }
    }

    fn display_recursive(&self, f: &mut fmt::Formatter, state: CSpaceDisplay) -> fmt::Result {
        let mut consecutive_empty = None;
        for slot in 0..self.capacity() {
            match self.get(slot).unwrap() {
                Some(cap) => {
                    if let Some(first_empty) = consecutive_empty {
                        consecutive_empty = None;
                        state.display_empty(f, first_empty, slot)?;
                    }

                    writeln!(f, "▶ {}: {}", slot, cap)?;

                    if let Some(cnode_cap) = cap.as_cnode() {
                        let new_state = state.child();
                        cnode_cap.cnode_object().display_recursive(f, new_state)?;
                    }
                }
                None => {
                    if consecutive_empty.is_none() {
                        consecutive_empty = Some(slot);
                    }
                }
            }
        }

        if let Some(first_empty) = consecutive_empty {
            state.display_empty(f, first_empty, self.capacity() - 1)?;
        }

        Ok(())
    }
}

/// A capability that grants specific access to a resource.
///
/// A resource may or may not be memory-mapped. An example of a resource that is not
/// memory-mapped is the IoPort capability. In such cases the object pointer will be
/// zero. We rely on the pointer to reclaim memory back to Untyped objects when
/// derived objects are deleted.
#[derive(Debug)]
pub struct Capability {
    /// Raw pointer to the object referred to by the capability.
    object: *const u8,

    /// Type-specific data of the capability.
    data: CData,

    /*
    /// Permissions afforded by the capability.
    permissions: PermissionSet,
    */

    /// The previous capability in pre-order traversal.
    prev: *const Capability,

    /// The next capability in pre-order traversal.
    next: *const Capability,

    /// The depth of this capability relative to root.
    depth: usize,
}

impl Capability {
    /// Returns the type of the capability.
    pub const fn capability_type(&self) -> CapType {
        self.data.capability_type()
    }

    /// Returns an iterator over the capability's direct children.
    pub fn children(&self) -> CapIter {
        match unsafe { self.next.as_ref() } {
            None => CapIter::empty(),
            Some(cap) => {
                if cap.depth > self.depth {
                    assert_eq!(cap.depth, self.depth + 1);

                    unsafe { CapIter::new(CapIterType::Sibling(cap.depth), self.next) }
                } else {
                    CapIter::empty()
                }
            }
        }
    }

    /// Returns whether we have any children.
    pub fn has_children(&self) -> bool {
        if self.next.is_null() {
            return false;
        }

        // should we check that the child's depth is exactly self.depth + 1?
        unsafe {
            self.next.as_ref().unwrap().depth > self.depth
        }
    }

    /// Insert a child capability into the CDT.
    ///
    /// Children of a capability are sorted by the value of its
    /// object pointer. The caller must ensure that the depth
    /// is set correctly in the specified capability.
    pub unsafe fn insert_child(&mut self, capability: *mut Capability) -> CapResult<()> {
        let cap_ref = capability.as_mut().unwrap();

        if self.has_children() {
            let mut insertion_point: Option<&mut Capability> = None;

            for child in self.children() {
                if child.object as usize > cap_ref.object as usize {
                    break;
                }
                insertion_point.replace(child.as_mut());
            }

            if let Some(cap) = insertion_point {
                cap.insert_sibling(capability)?;
            } else {
                // insert as first child
                self.insert_next(capability);
            }
        } else {
            // insert as first child
            self.insert_next(capability);
        }

        Ok(())
    }

    /// Insert a sibling after this capability into the CDT.
    pub unsafe fn insert_sibling(&mut self, capability: *mut Capability) -> CapResult<()> {
        let cap_ref = capability.as_mut().unwrap();
        if cap_ref.depth != self.depth {
            return Err(CapError::InvalidDepth);
        }

        let mut insertion_point: *mut Capability = self as *mut Capability;

        // Keep traversing the CDT until we see the first non-child or null pointer
        loop {
            let ip = insertion_point.as_mut().unwrap();

            if let Some(cap) = (ip.next as *mut Capability).as_mut() {
                if cap.depth > self.depth {
                    // our (grand)parent - stop here
                    break;
                }

                insertion_point = cap as *mut Capability;
            } else {
                // null - stop here
                break;
            }
        }

        insertion_point.as_mut().unwrap().insert_next(capability);

        Ok(())
    }

    /// Insert a capability between this and the next capability.
    ///
    /// This method does not consider ancestry.
    unsafe fn insert_next(&mut self, capability: *mut Capability) {
        let mut cap_ref = capability.as_mut().unwrap();

        if let Some(next_cap) = (self.next as *mut Capability).as_mut() {
            next_cap.prev = capability;
        }

        cap_ref.prev = self as *const Capability;
        cap_ref.next = self.next;
        self.next = capability;
    }

    /// Returns a mutable reference to this capability.
    ///
    /// # Safety
    ///
    /// This method steals a mutable reference unsafely.
    /// You must make sure that you have exclusive access to this capability.
    #[allow(clippy::mut_from_ref)]
    unsafe fn as_mut(&self) -> &mut Capability {
        (self as *const Capability as *mut Capability).as_mut().unwrap()
    }

    downcast_method!(as_cnode, CapType::CNode, CNodeCap);
    downcast_method!(as_untyped, CapType::Untyped, untyped::UntypedCap);
    downcast_method!(as_cpu, CapType::Cpu, cpu::CpuCap);
}

impl fmt::Display for Capability {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Cap({:?})", self.data)
    }
}

/// Metadata of a capability.
///
/// The memory layout of the enum is equivalent to the following C struct:
///
/// ```c
/// #include <stdint.h>
///
/// struct CData {
///   uint16_t discriminator;
///   union TypeSpecificData data;
/// }
/// ```
#[non_exhaustive]
#[repr(u32)]
#[derive(Debug)]
pub enum CData {
    CNode(CNodeCap),
    Untyped(untyped::UntypedCap),
    Cpu(cpu::CpuCap),
}

impl CData {
    /// Returns the pointer to the underlying data, forcibly interpreting it as T.
    #[inline]
    const unsafe fn data<T: Sized>(&self) -> *const T {
        let own = self as *const CData as *const u8;
        own.add(mem::size_of::<u32>()) as *const T
    }

    /// Returns the type of the capability.
    const fn capability_type(&self) -> CapType {
        match self {
            CData::CNode(_) => CapType::CNode,
            CData::Untyped(_) => CapType::Untyped,
            CData::Cpu(_) => CapType::Cpu,
        }
    }
}

/// A downcasted view of a capability.
///
/// This is here to make it easier for the inner struct to manipulate fields in the
/// Capability. `DowncastedCap`s can only be constructed by Capability using a
/// method.
#[derive(Debug)]
pub struct DowncastedCap<'cap, T: 'cap> {
    capability: *const Capability,
    data: *const T,
    _phantom: PhantomData<&'cap T>,
}

impl<'cap, T> DowncastedCap<'cap, T> {
    /// Create a downcasted view of a capability without checking the type.
    #[inline]
    const unsafe fn new_unchecked(capability: *const Capability, data: *const T) -> DowncastedCap<'cap, T> {
        DowncastedCap {
            capability,
            data,
            _phantom: PhantomData,
        }
    }
}

impl<'cap, T> Deref for DowncastedCap<'cap, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.data }
    }
}

impl<'cap, T> DerefMut for DowncastedCap<'cap, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *(self.data as *mut Self::Target) }
    }
}

impl<'cap, T> DowncastedCap<'cap, T> {
    /// Returns a reference to the Capability.
    #[inline]
    const fn capability(&self) -> &Capability {
        unsafe { &*self.capability }
    }
}

/// The CNode capability.
#[derive(Debug)]
pub struct CNodeCap {}

impl CNodeCap {
    /// Returns a reference to the CNode.
    #[inline]
    const fn cnode_object<'cap>(self: &DowncastedCap<'cap, CNodeCap>) -> &'cap CNode {
        unsafe { &*(self.capability().object as *const CNode) }
    }
}

/// Returns the layout of the kernel object for the specified capability type.
///
/// TODO: This function should be generated.
const fn kernel_layout(capability_type: CapType) -> Option<Layout> {
    match capability_type {
        CapType::Cpu => Some(cpu::OBJECT_LAYOUT),
        _ => None,
    }
}

/// Returns a new capability of a specified type.
///
/// TODO: This function should be generated.
fn new_capability(capability_type: CapType, object: *const u8) -> CapResult<CData> {
    match capability_type {
        CapType::Cpu => cpu::new_capability(object),
        _ => Err(CapError::NotRetypable),
    }
}
