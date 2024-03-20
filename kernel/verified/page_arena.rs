use vstd::prelude::*;
verus! {
use vstd::ptr::PPtr;

use crate::mem::size_of;

use crate::define::*;



// Why 4096 instead of PAGE_SZ in some places?
//
// https://github.com/verus-lang/verus/issues/587

/// An arena of the size of a page.
///
/// It splits a page into an array of `T`s followed by an optional
/// per-page metadata value.
///
/// Sadly, Verus cannot handle generics with a default type yet, so
/// do `PageArena<T, ()>` if you don't use the metadata.
///
/// Alternatively, for ergonomics we could rename the struct to
/// `PageArenaWithMeta<T, MT>` and have `PageArena<T>` be the type
/// alias.
pub tracked struct PageArena<T, MT> {
    pptr: PagePPtr,

    perm: Tracked<PagePerm>,
    values: Seq<T>,
    metadata: MT,
}

/// A pointer to an element in a page arena.
pub struct PageElementPtr<T> {
    page_pptr: PagePPtr,
    index: usize,

    // PhantomData makes the type opaque
    phantom: Ghost<Option<T>>,
}

// A pointer to the per-page metadata in a page arena.
pub struct PageMetadataPtr<MT> {
    page_pptr: PagePPtr,

    // PhantomData makes the type opaque
    phantom: Ghost<Option<MT>>,
}

impl<T> PageArena<T, ()> {
    /// Creates an arena without metadata.
    pub fn from_page(
        pptr: PagePPtr,
        perm: Tracked<PagePerm>,
        f: impl FnMut() -> T,
    ) -> (pa: Option<Tracked<Self>>)
        requires
            pptr.id() === perm@@.pptr,
            f.requires(()),
        ensures
            pa.is_Some() ==> (
                pa.get_Some_0()@.wf()
                && pa.get_Some_0()@.page_base() == pptr.id()
                && pa.get_Some_0()@.spec_init(&f)
            ),
    {
        // This will be optimized out
        let capacity = if let Some(capacity) = Self::capacity_opt() {
            capacity
        } else {
            return None;
        };

        let arena = Self::init_ghost(pptr.clone(), perm, ());
        let tracked mut arena = arena.get();

        Self::init_array(Tracked(&mut arena.values), pptr, f);

        Some(Tracked(arena))
    }
}

impl<T, MT> PageArena<T, MT> {
    /// Creates an arena with metadata.
    pub fn from_page_with_metadata(
        pptr: PagePPtr,
        perm: Tracked<PagePerm>,
        metadata: MT,
        f: impl FnMut() -> T,
    ) -> (pa: Option<Tracked<Self>>)
        requires
            pptr.id() === perm@@.pptr
        ensures
            pa.is_Some() ==> (
                pa.get_Some_0()@.wf()
                && pa.get_Some_0()@.page_base() == pptr.id()
                && pa.get_Some_0()@.metadata() == metadata
                && pa.get_Some_0()@.spec_init(&f)
            ),
    {
        // This will be optimized out
        if Self::capacity_opt().is_none() {
            return None;
        }

        let arena = Self::init_ghost(pptr.clone(), perm, metadata);
        let tracked mut arena = arena.get();

        Self::init_array(Tracked(&mut arena.values), pptr, f);

        Some(Tracked(arena))
    }

    /// Returns the PageElementPtr associated with an index.
    ///
    /// Since PageArena is entirely ghost, the real page PPtr
    /// needs to be specified.
    pub fn get_element_ptr(Tracked(arena): Tracked<&Self>, page_pptr: PagePPtr, i: usize) -> (ep: PageElementPtr<T>)
        requires
            arena.wf(),
            0 <= i < Self::capacity(),
            page_pptr.id() == arena.page_base(),
        ensures
            ep.index() == i,
            arena.has_element(&ep),
    {
        PageElementPtr {
            page_pptr,
            index: i,

            phantom: Ghost(None),
        }
    }

    /// Returns the PageMetadataPtr associated with this page.
    pub fn get_metadata_ptr(Tracked(arena): Tracked<&Self>, page_pptr: PagePPtr) -> (mp: PageMetadataPtr<MT>)
        requires
            arena.wf(),
    {
        PageMetadataPtr {
            page_pptr,

            phantom: Ghost(None),
        }
    }

    const fn capacity_opt() -> (ret: Option<usize>)
        ensures
            ret.is_Some() ==> (
                Self::type_is_storable()
                && Self::spec_capacity() == ret.get_Some_0()
            ),
    {
        let type_size = size_of::<T>();
        let metadata_size = size_of::<MT>();

        if metadata_size > 4096 {
            // In reality, metadata_size == PAGE_SZ is also unacceptable
            // and will fail the following check
            return None;
        }

        let remaining_size = 4096 - metadata_size;
        if type_size == 0 || type_size > remaining_size {
            None
        } else {
            Some(remaining_size / type_size)
        }
    }

    // Specs

    pub open spec fn wf(&self) -> bool {
        Self::type_is_storable()
    }

    pub open spec fn type_is_storable() -> bool {
        let type_size = size_of::<T>();
        let metadata_size = size_of::<MT>();
        let remaining_size: usize = (4096usize - metadata_size) as usize;

        &&& metadata_size <= 4096
        &&& 0 < type_size <= remaining_size
    }

    #[verifier(when_used_as_spec(spec_capacity))]
    pub const fn capacity() -> (ret: usize)
        requires
            Self::type_is_storable(),
        ensures
            ret == Self::spec_capacity(),
    {
        let type_size = size_of::<T>();
        let metadata_size = size_of::<MT>();
        let remaining_size = 4096usize - metadata_size;

        remaining_size / size_of::<T>()
    }

    pub open spec fn spec_capacity() -> usize {
        let type_size = size_of::<T>();
        let metadata_size = size_of::<MT>();
        let remaining_size: usize = (4096usize - metadata_size) as usize;

        remaining_size / size_of::<T>()
    }

    #[verifier(when_used_as_spec(spec_metadata_offset))]
    pub const fn metadata_offset() -> (ret: usize)
        by (nonlinear_arith)
        requires
            Self::type_is_storable(),
        ensures
            ret == Self::spec_metadata_offset(),
            ret + size_of::<MT>() <= 4096,
    {
        let type_size = size_of::<T>();
        let capacity = Self::capacity();

        type_size * capacity
    }

    pub open spec fn spec_metadata_offset() -> usize {
        let type_size = size_of::<T>();
        let capacity = Self::capacity();

        (type_size * capacity) as usize
    }

    pub open spec fn has_element(&self, element: &PageElementPtr<T>) -> bool {
        self.page_base() == element.page_base() && element.index() < Self::capacity()
    }

    pub open spec fn same_arena(&self, arena: &Self) -> bool {
        // Type system ensures identical element types and therefore capacity
        self.page_base() == arena.page_base()
    }

    pub closed spec fn values(&self) -> Seq<T> {
        self.values
    }

    // maybe remove?
    pub open spec fn value_at(&self, index: nat) -> &T {
        &self.values()[index as int]
    }

    // maybe remove?
    pub open spec fn value_at_opt(&self, index: nat) -> Option<&T> {
        Some(self.value_at(index))
    }

    pub closed spec fn metadata(&self) -> &MT {
        &self.metadata
    }

    pub closed spec fn page_base(&self) -> int {
        self.pptr.id()
    }

    // Trusted methods

    #[verifier(external_body)]
    fn init_ghost(
        pptr: PagePPtr,
        perm: Tracked<PagePerm>,
        metadata: MT,
    ) -> (ret: Tracked<Self>)
        requires
            pptr.id() === perm@@.pptr
        ensures
            ret@.perm === perm,
            ret@.pptr === pptr,
            ret@.page_base() === pptr.id(),
            ret@.metadata === metadata,
    {
        Tracked::assume_new()
    }

    #[verifier(external_body)]
    fn init_array(Tracked(values): Tracked<&mut Seq<T>>, pptr: PagePPtr, f: impl FnMut() -> T)
        ensures
            values.len() == Self::capacity(),
            forall |i: int| 0 <= i < Self::capacity() ==>
                f.ensures((), #[trigger] values[i]),
    {
        let slice = unsafe {
            core::slice::from_raw_parts_mut(pptr.to_usize() as *mut T, Self::capacity())
        };

        slice.fill_with(f);
    }

    pub open spec fn spec_init(&self, f: &impl FnMut() -> T) -> bool {
        forall |i: int| 0 <= i < Self::capacity() ==>
            f.ensures((), #[trigger] self.values()[i])
    }
}


impl<T> PageElementPtr<T> {
    pub fn clone(&self) -> (ep: Self)
        ensures
            self.same_ptr(&ep),
    {
        Self {
            page_pptr: self.page_pptr.clone(),
            index: self.index,

            phantom: self.phantom,
        }
    }

    // pub closed spec fn spec_clone(&self) -> (ep: Self)
    //     ensures
    //         self.same_ptr(&ep),
    // {
    //     Self {
    //         page_pptr: self.page_pptr.clone(),
    //         index: self.index,

    //         phantom: self.phantom,
    //     }
    // }

    // Specs

    pub open spec fn same_ptr(&self, other: &Self) -> bool {
        &&& self.page_pptr().id() === other.page_pptr().id()
        &&& self.index() == other.index()
        &&& self.page_base() === other.page_base()
    }

    pub closed spec fn page_pptr(&self) -> PagePPtr {
        self.page_pptr
    }

    pub closed spec fn page_base(&self) -> int {
        self.page_pptr.id()
    }

    pub closed spec fn index(&self) -> nat {
        self.index as nat
    }

    // Lukas: Temporary, used for linked list
    pub fn page_pptr_concrete(&self) -> PagePPtr {
        self.page_pptr
    }

    pub fn index_concrete(&self) -> usize {
        self.index
    }

    // Trusted methods

    #[verifier(external_body)]
    #[inline(always)]
    pub fn borrow<'a, MT>(&self, Tracked(arena): Tracked<&'a PageArena<T, MT>>) -> (result: &'a T)
        requires
            arena.wf(),
            arena.has_element(self),
        ensures
            result == arena.value_at(self.index()),
    {
        unsafe {
            let slice = core::slice::from_raw_parts(self.page_pptr.to_usize() as *const T, PageArena::<T, MT>::capacity());
            &slice[self.index]
        }
    }

    #[verifier(external_body)]
    #[inline(always)]
    pub fn put<MT>(&self, Tracked(arena): Tracked<&mut PageArena<T, MT>>, value: T)
        requires
            old(arena).wf(),
            old(arena).has_element(self),
        ensures
            arena.wf(),
            arena.same_arena(&*old(arena)),

            // The element was changed
            arena.value_at(self.index()) == value,

            // Everything else was unchanged
            forall |i: nat|
                i < PageArena::<T, MT>::capacity() && i != self.index() ==>
                    #[trigger] old(arena).value_at(i) == arena.value_at(i),
    {
        unsafe {
            let slice = core::slice::from_raw_parts_mut(self.page_pptr.to_usize() as *mut T, PageArena::<T, MT>::capacity());
            slice[self.index] = value;
        }
    }
}

impl<MT> PageMetadataPtr<MT> {
    pub fn clone(&self) -> (ep: Self)
        ensures
            self.same_ptr(&ep),
    {
        Self {
            page_pptr: self.page_pptr.clone(),

            phantom: self.phantom,
        }
    }

    // Specs

    pub open spec fn same_ptr(&self, other: &Self) -> bool {
        self.page_pptr().id() === other.page_pptr().id()
    }

    pub closed spec fn page_pptr(&self) -> PagePPtr {
        self.page_pptr
    }

    pub closed spec fn page_base(&self) -> int {
        self.page_pptr.id()
    }

    // Trusted methods

    #[verifier(external_body)]
    #[inline(always)]
    pub fn borrow<'a, T>(&self, Tracked(arena): Tracked<&'a PageArena<T, MT>>) -> (result: &'a MT)
        requires
            arena.wf(),
        ensures
            result == arena.metadata(),
    {
        // FIXME: Might overflow?
        let ptr = self.page_pptr.to_usize() + PageArena::<T, MT>::metadata_offset();
        unsafe {
            &*(ptr as *const MT)
        }
    }

    #[verifier(external_body)]
    #[inline(always)]
    pub fn put<T>(&self, Tracked(arena): Tracked<&mut PageArena<T, MT>>, value: MT)
        requires
            old(arena).wf(),
        ensures
            arena.same_arena(&*old(arena)),

            // The metadata was changed
            arena.metadata() == value,

            // Everything else was unchanged
            forall |i: nat|
                i < PageArena::<T, MT>::capacity() ==>
                    #[trigger] old(arena).value_at(i) == arena.value_at(i),
    {
        // FIXME: Might overflow?
        let ptr = self.page_pptr.to_usize() + PageArena::<T, MT>::metadata_offset();
        unsafe {
            *(ptr as *mut MT) = value;
        }
    }
}

#[verifier::external_fn_specification]
pub fn ex_usize_checked_mul(lhs: usize, rhs: usize) -> (result: Option<usize>)
    ensures
        lhs * rhs > usize::MAX ==> result.is_None(),
        lhs * rhs <= usize::MAX ==> (
            result == Some((lhs * rhs) as usize) // usize
            && (lhs as usize) * (rhs as usize) <= usize::MAX
            && result.get_Some_0() == lhs * rhs  // nat
        ),
{
    lhs.checked_mul(rhs)
}

mod spec_tests {
    use super::*;

    use vstd::ptr::BootPage;

    #[repr(transparent)]
    struct SomeStruct(u64);

    /// A simple arena of usize without metadata.
    type UsizeArena = PageArena<usize, ()>;

    /// An arena with per-page metadata.
    type MetaArena = PageArena<usize, SomeStruct>;

    fn test_element_ptr(pptr: PagePPtr) {
        // assumptions
        if usize::MAX - pptr.to_usize() < 4096 { return; }

        let first: PageElementPtr<SomeStruct> = PageElementPtr {
            page_pptr: pptr,
            index: 0,

            phantom: Ghost(None),
        };
    }

    fn test_boot_page(page1: BootPage, page2: BootPage) {
        let (pptr1, perm1) = PPtr::from_boot_page(page1);
        let (pptr2, perm2) = PPtr::from_boot_page(page2);

        let initializer = || -> (ret: usize)
            ensures ret == 0
        {
            0
        };

        let mut arena1 = if let Some(arena) = UsizeArena::from_page(pptr1.clone(), perm1, initializer) {
            arena
        } else {
            return;
        };
        let tracked mut arena1 = arena1.get();

        let arena2 = if let Some(arena) = UsizeArena::from_page(pptr2.clone(), perm2, initializer) {
            arena
        } else {
            return;
        };
        let tracked mut arena2 = arena2.get();

        if UsizeArena::capacity() < 5 {
            return;
        }

        assert(arena1.values()[0] == 0);
        assert(initializer.ensures((), arena1.values()[0]));

        let p1 = UsizeArena::get_element_ptr(Tracked(&arena1), pptr1.clone(), 0);
        let p2 = UsizeArena::get_element_ptr(Tracked(&arena1), pptr1.clone(), 1);

        let p3 = UsizeArena::get_element_ptr(Tracked(&arena2), pptr2.clone(), 0);
        let p4 = UsizeArena::get_element_ptr(Tracked(&arena2), pptr2.clone(), 1);
        //let bad = UsizeArena::get_element_ptr(&arena2, pptr1.clone(), 3);

        p1.put::<()>(Tracked(&mut arena1), 123);
        p2.put::<()>(Tracked(&mut arena1), 233);
        assert(arena1.wf());
        let p2_clone = p2.clone();

        let v1 = p1.borrow::<()>(Tracked(&arena1));
        let v2 = p2.borrow::<()>(Tracked(&arena1));
        assert(v1 == 123);
        assert(v2 == 233);

        p2_clone.put::<()>(Tracked(&mut arena1), 666);
        let v2 = p2.borrow::<()>(Tracked(&arena1));
        assert(v2 == 666);
    }

    fn test_metadata(page: BootPage) {
        let (pptr, perm) = PPtr::from_boot_page(page);

        let mut arena = if let Some(arena) = MetaArena::from_page_with_metadata(pptr.clone(), perm, SomeStruct(123), || 0) {
            arena
        } else {
            return;
        };
        let tracked mut arena: MetaArena = arena.get();

        let mp = MetaArena::get_metadata_ptr(Tracked(&arena), pptr.clone());
        let mp_clone = MetaArena::get_metadata_ptr(Tracked(&arena), pptr);
        let meta = mp.borrow::<usize>(Tracked(&arena));
        assert(meta.0 == 123);

        mp_clone.put::<usize>(Tracked(&mut arena), SomeStruct(233));
        let meta = mp.borrow::<usize>(Tracked(&arena));
        assert(meta.0 == 233);
    }
}

}
