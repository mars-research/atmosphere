use vstd::prelude::*;
verus! {

use crate::define::*;
use crate::allocator::page::*;
use crate::array::*;
use crate::slinkedlist::spec_impl_u::*;
use crate::util::page_ptr_util_u::*;

// use vstd::simple_pptr::*;
use crate::lemma::lemma_u::*;
use crate::lemma::lemma_t::*;
use vstd::set_lib::*;
use crate::array_vec::ArrayVec;
use crate::allocator::page_allocator_util_t::*;

pub struct PageAllocator {
    pub page_array: Array<Page, NUM_PAGES>,
    pub free_pages_4k: StaticLinkedList<PagePtr, NUM_PAGES>,
    pub free_pages_2m: StaticLinkedList<PagePtr, NUM_PAGES>,
    pub free_pages_1g: StaticLinkedList<PagePtr, NUM_PAGES>,
    pub allocated_pages_4k: Ghost<Set<PagePtr>>,
    pub allocated_pages_2m: Ghost<Set<PagePtr>>,
    pub allocated_pages_1g: Ghost<Set<PagePtr>>,
    pub mapped_pages_4k: Ghost<Set<PagePtr>>,
    pub mapped_pages_2m: Ghost<Set<PagePtr>>,
    pub mapped_pages_1g: Ghost<Set<PagePtr>>,
    // pub available_pages: Ghost<Set<PagePtr>>,
    pub page_perms_4k: Tracked<Map<PagePtr, PagePerm4k>>,
    pub page_perms_2m: Tracked<Map<PagePtr, PagePerm2m>>,
    pub page_perms_1g: Tracked<Map<PagePtr, PagePerm1g>>,
    pub container_map_4k: Ghost<Map<ContainerPtr, Set<PagePtr>>>,
    pub container_map_2m: Ghost<Map<ContainerPtr, Set<PagePtr>>>,
    pub container_map_1g: Ghost<Map<ContainerPtr, Set<PagePtr>>>,
}

impl PageAllocator {
    #[verifier(external_body)]
    pub fn new() -> (ret: Self) {
        let ret = Self {
            page_array: Array::<Page, NUM_PAGES>::new(),
            free_pages_4k: StaticLinkedList::<PagePtr, NUM_PAGES>::new(),
            free_pages_2m: StaticLinkedList::<PagePtr, NUM_PAGES>::new(),
            free_pages_1g: StaticLinkedList::<PagePtr, NUM_PAGES>::new(),
            allocated_pages_4k: Ghost(Set::empty()),
            allocated_pages_2m: Ghost(Set::empty()),
            allocated_pages_1g: Ghost(Set::empty()),
            mapped_pages_4k: Ghost(Set::empty()),
            mapped_pages_2m: Ghost(Set::empty()),
            mapped_pages_1g: Ghost(Set::empty()),
            page_perms_4k: Tracked(Map::tracked_empty()),
            page_perms_2m: Tracked(Map::tracked_empty()),
            page_perms_1g: Tracked(Map::tracked_empty()),
            container_map_4k: Ghost(Map::empty()),
            container_map_2m: Ghost(Map::empty()),
            container_map_1g: Ghost(Map::empty()),
        };

        ret
    }

    #[verifier(external_body)]
    pub fn init(
        &mut self,
        boot_pages: &mut ArrayVec::<(PageState, usize), NUM_PAGES>,
        container_ptr: ContainerPtr,
    ) {
        self.free_pages_4k.init();
        self.free_pages_2m.init();
        self.free_pages_1g.init();

        for index in 0..NUM_PAGES {
            match boot_pages.get(index).0 {
                PageState::Unavailable4k => {
                    self.page_array.set(
                        index,
                        Page {
                            addr: page_index2page_ptr(index),
                            state: PageState::Unavailable4k,
                            is_io_page: false,
                            rev_pointer: 0,
                            ref_count: 0,
                            owning_container: None,
                            mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                            io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                        },
                    );
                },
                PageState::Unavailable2m => {
                    self.page_array.set(
                        index,
                        Page {
                            addr: page_index2page_ptr(index),
                            state: PageState::Unavailable2m,
                            is_io_page: false,
                            rev_pointer: 0,
                            ref_count: 0,
                            owning_container: None,
                            mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                            io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                        },
                    );
                },
                PageState::Unavailable1g => {
                    self.page_array.set(
                        index,
                        Page {
                            addr: page_index2page_ptr(index),
                            state: PageState::Unavailable1g,
                            is_io_page: false,
                            rev_pointer: 0,
                            ref_count: 0,
                            owning_container: None,
                            mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                            io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                        },
                    );
                },
                PageState::Pagetable => {
                    self.page_array.set(
                        index,
                        Page {
                            addr: page_index2page_ptr(index),
                            state: PageState::Pagetable,
                            is_io_page: false,
                            rev_pointer: 0,
                            ref_count: 0,
                            owning_container: None,
                            mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                            io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                        },
                    );
                },
                PageState::Allocated4k => {
                    self.page_array.set(
                        index,
                        Page {
                            addr: page_index2page_ptr(index),
                            state: PageState::Allocated4k,
                            is_io_page: false,
                            rev_pointer: 0,
                            ref_count: 0,
                            owning_container: None,
                            mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                            io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                        },
                    );
                },
                PageState::Allocated2m => {
                    self.page_array.set(
                        index,
                        Page {
                            addr: page_index2page_ptr(index),
                            state: PageState::Allocated2m,
                            is_io_page: false,
                            rev_pointer: 0,
                            ref_count: 0,
                            owning_container: None,
                            mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                            io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                        },
                    );
                },
                PageState::Allocated1g => {
                    self.page_array.set(
                        index,
                        Page {
                            addr: page_index2page_ptr(index),
                            state: PageState::Allocated1g,
                            is_io_page: false,
                            rev_pointer: 0,
                            ref_count: 0,
                            owning_container: None,
                            mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                            io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                        },
                    );
                },
                PageState::Free4k => {
                    let node_ref = self.free_pages_4k.push(&page_index2page_ptr(index));
                    self.page_array.set(
                        index,
                        Page {
                            addr: page_index2page_ptr(index),
                            state: PageState::Free4k,
                            is_io_page: false,
                            rev_pointer: node_ref,
                            ref_count: 0,
                            owning_container: None,
                            mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                            io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                        },
                    );
                },
                PageState::Free2m => {
                    let node_ref = self.free_pages_2m.push(&page_index2page_ptr(index));
                    self.page_array.set(
                        index,
                        Page {
                            addr: page_index2page_ptr(index),
                            state: PageState::Free2m,
                            is_io_page: false,
                            rev_pointer: node_ref,
                            ref_count: 0,
                            owning_container: None,
                            mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                            io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                        },
                    );
                },
                PageState::Free1g => {
                    let node_ref = self.free_pages_1g.push(&page_index2page_ptr(index));
                    self.page_array.set(
                        index,
                        Page {
                            addr: page_index2page_ptr(index),
                            state: PageState::Free1g,
                            is_io_page: false,
                            rev_pointer: node_ref,
                            ref_count: 0,
                            owning_container: None,
                            mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                            io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                        },
                    );
                },
                PageState::Mapped4k => {
                    self.page_array.set(
                        index,
                        Page {
                            addr: page_index2page_ptr(index),
                            state: PageState::Mapped4k,
                            is_io_page: false,
                            rev_pointer: 0,
                            ref_count: 1,
                            owning_container: Some(container_ptr),
                            mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                            io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                        },
                    );
                },
                PageState::Mapped2m => {
                    self.page_array.set(
                        index,
                        Page {
                            addr: page_index2page_ptr(index),
                            state: PageState::Mapped2m,
                            is_io_page: false,
                            rev_pointer: 0,
                            ref_count: 1,
                            owning_container: Some(container_ptr),
                            mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                            io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                        },
                    );
                },
                PageState::Mapped1g => {
                    self.page_array.set(
                        index,
                        Page {
                            addr: page_index2page_ptr(index),
                            state: PageState::Mapped1g,
                            is_io_page: false,
                            rev_pointer: 0,
                            ref_count: 1,
                            owning_container: Some(container_ptr),
                            mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                            io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                        },
                    );
                },
                PageState::Merged2m => {
                    self.page_array.set(
                        index,
                        Page {
                            addr: page_index2page_ptr(index),
                            state: PageState::Merged2m,
                            is_io_page: false,
                            rev_pointer: 0,
                            ref_count: 0,
                            owning_container: None,
                            mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                            io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                        },
                    );
                },
                PageState::Merged1g => {
                    self.page_array.set(
                        index,
                        Page {
                            addr: page_index2page_ptr(index),
                            state: PageState::Merged1g,
                            is_io_page: false,
                            rev_pointer: 0,
                            ref_count: 0,
                            owning_container: None,
                            mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                            io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                        },
                    );
                },
                PageState::Io => {
                    self.page_array.set(
                        index,
                        Page {
                            addr: page_index2page_ptr(index),
                            state: PageState::Io,
                            is_io_page: true,
                            rev_pointer: 0,
                            ref_count: 1,
                            owning_container: Some(container_ptr),
                            mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                            io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                        },
                    );
                },
            }
        }
    }

    pub open spec fn page_is_mapped(&self, p: PagePtr) -> bool {
        ||| self.mapped_pages_4k().contains(p)
        ||| self.mapped_pages_2m().contains(p)
        ||| self.mapped_pages_1g().contains(p)
    }

    pub closed spec fn free_pages_4k(&self) -> Set<PagePtr> {
        self.free_pages_4k@.to_set()
    }

    pub closed spec fn free_pages_2m(&self) -> Set<PagePtr> {
        self.free_pages_2m@.to_set()
    }

    pub closed spec fn free_pages_1g(&self) -> Set<PagePtr> {
        self.free_pages_1g@.to_set()
    }

    pub closed spec fn allocated_pages_4k(&self) -> Set<PagePtr> {
        self.allocated_pages_4k@
    }

    pub closed spec fn allocated_pages_2m(&self) -> Set<PagePtr> {
        self.allocated_pages_2m@
    }

    pub closed spec fn allocated_pages_1g(&self) -> Set<PagePtr> {
        self.allocated_pages_1g@
    }

    pub closed spec fn mapped_pages_4k(&self) -> Set<PagePtr> {
        self.mapped_pages_4k@
    }

    pub closed spec fn mapped_pages_2m(&self) -> Set<PagePtr> {
        self.mapped_pages_2m@
    }

    pub closed spec fn mapped_pages_1g(&self) -> Set<PagePtr> {
        self.mapped_pages_1g@
    }

    pub closed spec fn page_mappings(&self, p: PagePtr) -> Set<(Pcid, VAddr)> {
        self.page_array@[page_ptr2page_index(p) as int].mappings@
    }

    pub closed spec fn page_io_mappings(&self, p: PagePtr) -> Set<(Pcid, VAddr)> {
        self.page_array@[page_ptr2page_index(p) as int].io_mappings@
    }

    pub closed spec fn get_container_owned_pages(&self, c_ptr: ContainerPtr) -> Set<PagePtr>
        recommends
            self.container_map_4k@.dom().contains(c_ptr),
    {
        self.container_map_4k@[c_ptr]
    }

    pub open spec fn page_array_wf(&self) -> bool {
        &&& self.page_array.wf()
        &&& forall|i: usize|
            #![trigger self.page_array@[i as int].addr]
            #![trigger page_index2page_ptr(i)]
            0 <= i < NUM_PAGES ==> self.page_array@[i as int].addr == page_index2page_ptr(i)
        &&& forall|i: int|
            #![trigger self.page_array@[i].mappings]
            0 <= i < NUM_PAGES ==> self.page_array@[i].mappings@.finite()
        &&& forall|i: int|
            #![trigger self.page_array@[i].io_mappings]
            0 <= i < NUM_PAGES ==> self.page_array@[i].io_mappings@.finite()
    }

    pub open spec fn free_pages_4k_wf(&self) -> bool {
        &&& self.free_pages_4k.wf()
        &&& self.free_pages_4k.unique()
        &&& forall|i: int|
            #![trigger self.free_pages_4k@.contains(self.page_array@[i].addr)]
            #![trigger self.page_array@[i].rev_pointer]
            0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Free4k
                ==> self.free_pages_4k@.contains(self.page_array@[i].addr)
                && self.free_pages_4k.get_node_ref(self.page_array@[i].addr) == self.page_array@[i].rev_pointer
                && self.page_array@[i].is_io_page == false
        &&& forall|page_ptr: PagePtr|
            #![trigger page_ptr_valid(page_ptr)]
            #![trigger self.page_array@[page_ptr2page_index(page_ptr) as int].state]
            self.free_pages_4k@.contains(page_ptr) ==> page_ptr_valid(page_ptr)
                && self.page_array@[page_ptr2page_index(page_ptr) as int].state
                == PageState::Free4k
            // &&&
            // forall|i:int, j:int|
            //     #![trigger self.page_array@[i].rev_pointer, self.page_array@[j].rev_pointer]
            //     0<=i<NUM_PAGES && 0<j<NUM_PAGES && i != j && self.page_array@[i].state == PageState::Free4k && self.page_array@[j].state == PageState::Free4k
            //     ==>
            //     self.page_array@[i].rev_pointer != self.page_array@[j].rev_pointer

    }

    pub open spec fn free_pages_2m_wf(&self) -> bool {
        &&& self.free_pages_2m.wf()
        &&& self.free_pages_2m.unique()
        &&& forall|i: int|
            #![trigger self.free_pages_2m@.contains(self.page_array@[i].addr)]
            #![trigger self.page_array@[i].is_io_page]
            #![trigger self.page_array@[i].rev_pointer]
            0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Free2m
                ==> self.free_pages_2m@.contains(self.page_array@[i].addr)
                && self.free_pages_2m.get_node_ref(self.page_array@[i].addr ) == 
                    self.page_array@[i].rev_pointer
                && self.page_array@[i].is_io_page == false
        &&& forall|page_ptr: PagePtr|
            #![trigger page_ptr_2m_valid(page_ptr)]
            #![trigger self.page_array@[page_ptr2page_index(page_ptr) as int].state]
            self.free_pages_2m@.contains(page_ptr) ==> page_ptr_2m_valid(page_ptr)
                && self.page_array@[page_ptr2page_index(page_ptr) as int].state
                == PageState::Free2m
            // &&&
            // forall|i:int, j:int|
            //     #![trigger self.page_array@[i].rev_pointer, self.page_array@[j].rev_pointer]
            //     0<=i<NUM_PAGES && 0<j<NUM_PAGES && i != j && self.page_array@[i].state == PageState::Free2m && self.page_array@[j].state == PageState::Free2m
            //     ==>
            //     self.page_array@[i].rev_pointer != self.page_array@[j].rev_pointer

    }

    pub open spec fn free_pages_1g_wf(&self) -> bool {
        &&& self.free_pages_1g.wf()
        &&& self.free_pages_1g.unique()
        &&& forall|i: int|
            #![trigger self.free_pages_1g@.contains(self.page_array@[i].addr)]
            #![trigger self.page_array@[i].is_io_page]
            #![trigger self.page_array@[i].rev_pointer]
            0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Free1g
                ==> self.free_pages_1g@.contains(self.page_array@[i].addr)
                && self.free_pages_1g.get_node_ref(self.page_array@[i].addr) == self.page_array@[i].rev_pointer
                && self.page_array@[i].is_io_page == false
        &&& forall|page_ptr: PagePtr|
            #![trigger page_ptr_1g_valid(page_ptr)]
            #![trigger self.page_array@[page_ptr2page_index(page_ptr) as int].state]
            self.free_pages_1g@.contains(page_ptr) ==> page_ptr_1g_valid(page_ptr)
                && self.page_array@[page_ptr2page_index(page_ptr) as int].state
                == PageState::Free1g
            // &&&
            // forall|i:int, j:int|
            //     #![trigger self.page_array@[i].rev_pointer, self.page_array@[j].rev_pointer]
            //     0<=i<NUM_PAGES && 0<j<NUM_PAGES && i != j && self.page_array@[i].state == PageState::Free1g && self.page_array@[j].state == PageState::Free1g
            //     ==>
            //     self.page_array@[i].rev_pointer != self.page_array@[j].rev_pointer

    }

    pub open spec fn allocated_pages_4k_wf(&self) -> bool {
        &&& self.allocated_pages_4k@.finite()
        &&& forall|p: PagePtr|
            #![trigger self.allocated_pages_4k@.contains(p), page_ptr_valid(p)]
            self.allocated_pages_4k@.contains(p) ==> page_ptr_valid(p)
        &&& forall|i: int|
            #![trigger self.allocated_pages_4k@.contains(self.page_array@[i].addr)]
            #![trigger self.page_array@[i].is_io_page]
            0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Allocated4k
                ==> self.allocated_pages_4k@.contains(self.page_array@[i].addr)
                && self.page_array@[i].is_io_page == false
        &&& forall|p: PagePtr|
            #![trigger self.page_array@[page_ptr2page_index(p) as int].state]
            self.allocated_pages_4k@.contains(p) ==> self.page_array@[page_ptr2page_index(
                p,
            ) as int].state == PageState::Allocated4k
    }

    pub open spec fn allocated_pages_2m_wf(&self) -> bool {
        &&& self.allocated_pages_2m@.finite()
        &&& forall|p: PagePtr|
            #![trigger self.allocated_pages_2m@.contains(p), page_ptr_2m_valid(p)]
            self.allocated_pages_2m@.contains(p) ==> page_ptr_2m_valid(p)
        &&& forall|i: int|
            #![trigger self.allocated_pages_2m@.contains(self.page_array@[i].addr)]
            #![trigger self.page_array@[i].is_io_page]
            0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Allocated2m
                ==> self.allocated_pages_2m@.contains(self.page_array@[i].addr)
                && self.page_array@[i].is_io_page == false
        &&& forall|p: PagePtr|
            #![trigger self.page_array@[page_ptr2page_index(p) as int].state]
            self.allocated_pages_2m@.contains(p) ==> self.page_array@[page_ptr2page_index(
                p,
            ) as int].state == PageState::Allocated2m
    }

    pub open spec fn allocated_pages_1g_wf(&self) -> bool {
        &&& self.allocated_pages_1g@.finite()
        &&& forall|p: PagePtr|
            #![trigger self.allocated_pages_1g@.contains(p), page_ptr_1g_valid(p)]
            self.allocated_pages_1g@.contains(p) ==> page_ptr_1g_valid(p)
        &&& forall|i: int|
            #![trigger self.page_array@[i].addr]
            #![trigger self.page_array@[i].is_io_page]
            0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Allocated1g
                ==> self.allocated_pages_1g@.contains(self.page_array@[i].addr)
                && self.page_array@[i].is_io_page == false
        &&& forall|p: PagePtr|
            #![trigger self.page_array@[page_ptr2page_index(p) as int].state]
            self.allocated_pages_1g@.contains(p) ==> self.page_array@[page_ptr2page_index(
                p,
            ) as int].state == PageState::Allocated1g
    }

    pub open spec fn mapped_pages_4k_wf(&self) -> bool {
        &&& self.mapped_pages_4k@.finite()
        &&& forall|p: PagePtr|
            #![trigger self.mapped_pages_4k@.contains(p), page_ptr_valid(p)]
            #![trigger self.page_array@[page_ptr2page_index(p) as int].state]
            #![trigger self.mapped_pages_4k@.contains(p), page_ptr2page_index(p)]
            self.mapped_pages_4k@.contains(p) ==> page_ptr_valid(p)
                && self.page_array@[page_ptr2page_index(p) as int].state == PageState::Mapped4k
        &&& forall|i: int|
            #![trigger self.page_array@[i].addr]
            0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Mapped4k
                ==> self.mapped_pages_4k@.contains(self.page_array@[i].addr)
    }

    pub open spec fn mapped_pages_2m_wf(&self) -> bool {
        &&& self.mapped_pages_2m@.finite()
        &&& forall|i: int|
            #![trigger self.page_array@[i].addr]
            0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Mapped2m
                ==> self.mapped_pages_2m@.contains(self.page_array@[i].addr)
        &&& forall|p: PagePtr|
            #![trigger self.mapped_pages_2m@.contains(p), page_ptr_valid(p)]
            #![trigger self.page_array@[page_ptr2page_index(p) as int].state]
            #![trigger self.mapped_pages_2m@.contains(p), page_ptr2page_index(p)]
            self.mapped_pages_2m@.contains(p) ==> page_ptr_2m_valid(p)
                && self.page_array@[page_ptr2page_index(p) as int].state == PageState::Mapped2m
    }

    pub open spec fn mapped_pages_1g_wf(&self) -> bool {
        &&& self.mapped_pages_1g@.finite()
        &&& forall|i: int|
            #![trigger self.page_array@[i].addr]
            0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Mapped1g
                ==> self.mapped_pages_1g@.contains(self.page_array@[i].addr)
        &&& forall|p: PagePtr|
            #![trigger self.mapped_pages_1g@.contains(p), page_ptr_valid(p)]
            #![trigger self.page_array@[page_ptr2page_index(p) as int].state]
            #![trigger self.mapped_pages_1g@.contains(p), page_ptr2page_index(p)]
            self.mapped_pages_1g@.contains(p) ==> page_ptr_1g_valid(p)
                && self.page_array@[page_ptr2page_index(p) as int].state == PageState::Mapped1g
    }

    pub open spec fn merged_pages_wf(&self) -> bool {
        &&& forall|i: usize|
            #![trigger page_index_2m_valid(i)]
            #![trigger spec_page_index_truncate_2m(i)]
            0 <= i < NUM_PAGES && self.page_array@[i as int].state == PageState::Merged2m    
            ==> 
            page_index_2m_valid(i) == false 
            && ( self.page_array@[spec_page_index_truncate_2m(i) as int].state == PageState::Mapped2m
                || self.page_array@[spec_page_index_truncate_2m(i) as int].state == PageState::Free2m 
                || self.page_array@[spec_page_index_truncate_2m(i) as int].state == PageState::Allocated2m
                || self.page_array@[spec_page_index_truncate_2m(i) as int].state== PageState::Unavailable2m
            ) 
            && self.page_array@[i as int].is_io_page == self.page_array@[spec_page_index_truncate_2m(i) as int].is_io_page
        &&& forall|i: usize|
            #![trigger page_index_1g_valid(i)]
            #![trigger spec_page_index_truncate_1g(i)]
            0 <= i < NUM_PAGES && self.page_array@[i as int].state == PageState::Merged1g
            ==> 
            page_index_1g_valid(i) == false 
            && (self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Mapped1g
                || self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Free1g 
                || self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Allocated1g
                || self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Unavailable1g
            ) 
            && self.page_array@[i as int].is_io_page == self.page_array@[spec_page_index_truncate_1g(i) as int].is_io_page
    }

    pub open spec fn hugepages_wf(&self) -> bool {
        &&& forall|i: usize, j: usize|
            #![trigger spec_page_index_merge_2m_vaild(i,j)]
            #![trigger spec_page_index_merge_1g_vaild(i,j)]
            (0 <= i < NUM_PAGES && page_index_2m_valid(i) && 
            (self.page_array@[i as int].state == PageState::Mapped2m 
                || self.page_array@[i as int].state == PageState::Free2m
                || self.page_array@[i as int].state == PageState::Allocated2m
                || self.page_array@[i as int].state == PageState::Unavailable2m)
                && spec_page_index_merge_2m_vaild(i, j) 
            ==> self.page_array@[j as int].state == PageState::Merged2m && self.page_array@[i as int].is_io_page == self.page_array@[j as int].is_io_page) 
            && 
            (0 <= i < NUM_PAGES && page_index_1g_valid(i) && (self.page_array@[i as int].state == PageState::Mapped1g 
                || self.page_array@[i as int].state == PageState::Free1g
                || self.page_array@[i as int].state == PageState::Allocated1g
                || self.page_array@[i as int].state == PageState::Unavailable1g)
                && spec_page_index_merge_1g_vaild(i, j) 
            ==> self.page_array@[j as int].state == PageState::Merged1g && self.page_array@[i as int].is_io_page == self.page_array@[j as int].is_io_page)
    }

    pub open spec fn perm_wf(&self) -> bool {
        &&& self.page_perms_4k@.dom() =~= self.mapped_pages_4k@ + self.free_pages_4k@.to_set()
        &&& forall|p: PagePtr|
            #![trigger self.page_perms_4k@[p].is_init()]
            #![trigger self.page_perms_4k@[p].addr()]
            self.page_perms_4k@.dom().contains(p) ==> self.page_perms_4k@[p].is_init()
                && self.page_perms_4k@[p].addr() == p
        &&& self.page_perms_2m@.dom() =~= self.mapped_pages_2m@ + self.free_pages_2m@.to_set()
        &&& forall|p: PagePtr|
            #![trigger self.page_perms_2m@[p].is_init()]
            #![trigger self.page_perms_2m@[p].addr()]
            self.page_perms_2m@.dom().contains(p) ==> self.page_perms_2m@[p].is_init()
                && self.page_perms_2m@[p].addr() == p
        &&& self.page_perms_1g@.dom() =~= self.mapped_pages_1g@ + self.free_pages_1g@.to_set()
        &&& forall|p: PagePtr|
            #![trigger self.page_perms_1g@[p].is_init()]
            #![trigger self.page_perms_1g@[p].addr()]
            self.page_perms_1g@.dom().contains(p) ==> self.page_perms_1g@[p].is_init()
                && self.page_perms_1g@[p].addr() == p
    }

    pub open spec fn container_wf(&self) -> bool {
        //@Xiangdong Come back for this
        // &&&
        // self.container_map_4k@.dom() == self.container_map_2m@.dom()
        // &&&
        // self.container_map_4k@.dom() == self.container_map_1g@.dom()
        // &&&
        // self.container_map_2m@.dom() == self.container_map_1g@.dom()
        &&& self.container_map_4k@.dom().subset_of(self.allocated_pages_4k@)
        &&& self.container_map_2m@.dom().subset_of(self.allocated_pages_4k@)
        &&& self.container_map_1g@.dom().subset_of(self.allocated_pages_4k@)
        &&& forall|i: int|
            #![trigger self.page_array@[i], self.page_array@[i].owning_container.is_Some()]
            0 <= i < NUM_PAGES && (self.page_array@[i].state == PageState::Mapped4k
                || self.page_array@[i].state == PageState::Mapped2m || self.page_array@[i].state
                == PageState::Mapped1g) ==> self.page_array@[i].owning_container.is_Some()
        &&& forall|i: int|
            #![trigger self.page_array@[i], self.page_array@[i].owning_container.is_Some()]
            0 <= i < NUM_PAGES && self.page_array@[i].owning_container.is_Some() ==> (
            self.page_array@[i].state == PageState::Mapped4k || self.page_array@[i].state
                == PageState::Mapped2m || self.page_array@[i].state == PageState::Mapped1g)
        &&& forall|i: usize|
            #![trigger self.page_array@[i as int].state, self.page_array@[i as int].owning_container]
            0 <= i < NUM_PAGES && self.page_array@[i as int].state == PageState::Mapped4k
                ==> self.container_map_4k@.dom().contains(
                self.page_array@[i as int].owning_container.unwrap(),
            )
                && self.container_map_4k@[self.page_array@[i as int].owning_container.unwrap()].contains(
            page_index2page_ptr(i))
        &&& forall|i: usize|
            #![trigger self.page_array@[i as int].state, self.page_array@[i as int].owning_container]
            0 <= i < NUM_PAGES && self.page_array@[i as int].state == PageState::Mapped2m
                ==> self.container_map_2m@.dom().contains(
                self.page_array@[i as int].owning_container.unwrap(),
            )
                && self.container_map_2m@[self.page_array@[i as int].owning_container.unwrap()].contains(
            page_index2page_ptr(i))
        &&& forall|i: usize|
            #![trigger self.page_array@[i as int].state, self.page_array@[i as int].owning_container]
            0 <= i < NUM_PAGES && self.page_array@[i as int].state == PageState::Mapped1g
                ==> self.container_map_1g@.dom().contains(
                self.page_array@[i as int].owning_container.unwrap(),
            )
                && self.container_map_1g@[self.page_array@[i as int].owning_container.unwrap()].contains(
            page_index2page_ptr(i))
        &&& forall|c_ptr: ContainerPtr, page_ptr: PagePtr|
            #![trigger self.container_map_4k@[c_ptr].contains(page_ptr)]
            self.container_map_4k@.dom().contains(c_ptr) && self.container_map_4k@[c_ptr].contains(
                page_ptr,
            ) ==> page_ptr_valid(page_ptr) && self.page_array@[page_ptr2page_index(
                page_ptr,
            ) as int].state == PageState::Mapped4k && self.page_array@[page_ptr2page_index(
                page_ptr,
            ) as int].owning_container.unwrap() == c_ptr
        &&& forall|c_ptr: ContainerPtr, page_ptr: PagePtr|
            #![trigger self.container_map_2m@[c_ptr].contains(page_ptr)]
            self.container_map_2m@.dom().contains(c_ptr) && self.container_map_2m@[c_ptr].contains(
                page_ptr,
            ) ==> page_ptr_2m_valid(page_ptr) && self.page_array@[page_ptr2page_index(
                page_ptr,
            ) as int].state == PageState::Mapped2m && self.page_array@[page_ptr2page_index(
                page_ptr,
            ) as int].owning_container.unwrap() == c_ptr
        &&& forall|c_ptr: ContainerPtr, page_ptr: PagePtr|
            #![trigger self.container_map_1g@[c_ptr].contains(page_ptr)]
            self.container_map_1g@.dom().contains(c_ptr) && self.container_map_1g@[c_ptr].contains(
                page_ptr,
            ) ==> page_ptr_1g_valid(page_ptr) && self.page_array@[page_ptr2page_index(
                page_ptr,
            ) as int].state == PageState::Mapped1g && self.page_array@[page_ptr2page_index(
                page_ptr,
            ) as int].owning_container.unwrap() == c_ptr
    }

    pub open spec fn mapped_pages_have_reference_counter(&self) -> bool {
        &&& forall|i: int|
            #![trigger self.page_array@[i].ref_count]
            #![trigger self.page_array@[i].state]
            #![trigger self.page_array@[i].mappings]
            #![trigger self.page_array@[i].io_mappings]
            0 <= i < NUM_PAGES ==> (self.page_array@[i].ref_count != 0 <==> (
            self.page_array@[i].state == PageState::Mapped4k || self.page_array@[i].state
                == PageState::Mapped2m || self.page_array@[i].state == PageState::Mapped1g))
                && self.page_array@[i].ref_count == self.page_array@[i].mappings@.len()
                + self.page_array@[i].io_mappings@.len()
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.page_array_wf()
        &&& self.free_pages_4k_wf()
        &&& self.free_pages_2m_wf()
        &&& self.free_pages_1g_wf()
        &&& self.allocated_pages_4k_wf()
        &&& self.allocated_pages_2m_wf()
        &&& self.allocated_pages_1g_wf()
        &&& self.mapped_pages_4k_wf()
        &&& self.mapped_pages_2m_wf()
        &&& self.mapped_pages_1g_wf()
        &&& self.merged_pages_wf()
        &&& self.hugepages_wf()
        &&& self.perm_wf()
        &&& self.container_wf()
        &&& self.mapped_pages_have_reference_counter()
    }
}

// proof
impl PageAllocator {

    pub proof fn pages_with_mappings_are_mapped(&self, page_ptr: PagePtr)
        requires
            self.wf(),
            page_ptr_valid(page_ptr),
            self.page_mappings(page_ptr).len() > 0,
        ensures
            self.page_is_mapped(page_ptr) == true,
    {
        page_index_lemma();
        page_ptr_lemma1();
        page_ptr_2m_lemma();
        page_ptr_1g_lemma();
        assert(self.page_array@[page_ptr2page_index(page_ptr) as int].ref_count != 0);
    }

    pub proof fn mapped_page_are_not_allocated(&self, page_ptr: PagePtr)
        requires
            self.wf(),
            page_ptr_valid(page_ptr),
            self.page_is_mapped(page_ptr) == true,
        ensures
            self.allocated_pages_4k().contains(page_ptr) == false,
            self.allocated_pages_2m().contains(page_ptr) == false,
            self.allocated_pages_1g().contains(page_ptr) == false,
    {
    }

    pub proof fn mapped_page_imply_page_ptr_valid(&self, page_ptr: PagePtr)
        requires
            self.wf(),
            self.page_is_mapped(page_ptr) == true,
        ensures
            page_ptr_valid(page_ptr),
    {
    }

    pub proof fn free_pages_are_not_mapped(&self)
        requires
            self.wf(),
        ensures
            forall|page_ptr: PagePtr|
                #![trigger self.free_pages_4k().contains(page_ptr)]
                #![trigger self.page_is_mapped(page_ptr)]
                self.free_pages_4k().contains(page_ptr) ==> self.page_is_mapped(page_ptr) == false,
    {
        assert(forall|page_ptr: PagePtr|
            #![trigger self.free_pages_4k().contains(page_ptr)]
            #![trigger self.page_is_mapped(page_ptr)]
            self.free_pages_4k().contains(page_ptr) ==> page_ptr_valid(page_ptr)
                && self.page_array@[page_ptr2page_index(page_ptr) as int].state == PageState::Free4k
                && self.page_is_mapped(page_ptr) == false);
    }

    // pub proof fn page_ptr_page_index_lemma(&self)
    //     requires
    //         self.wf(),
    //     ensures
    //         forall|i:usize|
    //             #![trigger self.page_array@[i as int].state]
    //             0 <= i < NUM_PAGES && (self.page_array@[i as int].state == PageState::Mapped1g || self.page_array@[i as int].state == PageState::Free1g || self.page_array@[i as int].state == PageState::Allocated1g)
    //             ==>
    //             page_index_1g_valid(i),
    // {
    //     page_ptr_lemma1();
    //     page_ptr_2m_lemma();
    //     page_ptr_1g_lemma();
    //     assert(
    //         forall|i:usize|
    //             #![trigger self.page_array@[i as int].state]
    //             #![trigger page_index_1g_valid(i)]
    //             0 <= i < NUM_PAGES && (self.page_array@[i as int].state == PageState::Mapped1g || self.page_array@[i as int].state == PageState::Free1g || self.page_array@[i as int].state == PageState::Allocated1g)
    //             ==>
    //             page_index_1g_valid(i)
    //     ) by {
    //         assert(
    //             forall|i:usize|
    //                 #![trigger self.page_array@[i as int].state]
    //                 #![trigger page_index_valid(i)]
    //                 0 <= i < NUM_PAGES && (self.page_array@[i as int].state == PageState::Mapped1g || self.page_array@[i as int].state == PageState::Free1g || self.page_array@[i as int].state == PageState::Allocated1g)
    //                 ==>
    //                 page_index_valid(i)
    //         );
    //         assert(
    //             forall|i:usize|
    //                 #![trigger self.page_array@[i as int].state]
    //                 #![trigger page_index_2m_valid(i)]
    //                 0 <= i < NUM_PAGES && (self.page_array@[i as int].state == PageState::Mapped1g || self.page_array@[i as int].state == PageState::Free1g || self.page_array@[i as int].state == PageState::Allocated1g)
    //                 ==>
    //                 page_index_2m_valid(i)
    //         );
    //     };
    // }

    pub proof fn len_lemma_mapped_4k(&self, ptr: PagePtr)
        requires
            self.wf(),
        ensures
            self.mapped_pages_4k().contains(ptr) ==> self.free_pages_4k().len() < NUM_PAGES,
    {
        page_ptr_lemma1();
        page_ptr_2m_lemma();
        page_ptr_1g_lemma();
        seq_skip_lemma::<PagePtr>();
        self.free_pages_1g.wf_to_no_duplicates();
        self.free_pages_2m.wf_to_no_duplicates();
        self.free_pages_4k.wf_to_no_duplicates();
        let all_page_ptrs = Set::new(|page_ptr: PagePtr| page_ptr_valid(page_ptr));
        assume(all_page_ptrs.finite());
        assume(all_page_ptrs.len() == NUM_PAGES);  // this should be inferred smh by verus...
        assert(forall|page_ptr: PagePtr|
            #![auto]
            self.free_pages_2m@.contains(page_ptr) ==> all_page_ptrs.contains(page_ptr));

        if self.mapped_pages_4k().contains(ptr) {
            assert(page_ptr_valid(ptr));
            assert(self.page_array@[page_ptr2page_index(ptr) as int].state == PageState::Mapped4k);
            assert(all_page_ptrs.contains(ptr));
            assert(all_page_ptrs.remove(ptr).len() < all_page_ptrs.len());
            assert(self.free_pages_4k().contains(ptr) == false);
            assert(self.free_pages_4k().subset_of(all_page_ptrs.remove(ptr)));
            assert(self.free_pages_4k().len() < NUM_PAGES) by {
                lemma_len_subset::<PagePtr>(self.free_pages_4k(), all_page_ptrs.remove(ptr))
            };
        }
    }

    pub proof fn len_lemma_allocated_4k(&self, ptr: PagePtr)
        requires
            self.wf(),
        ensures
            self.allocated_pages_4k().contains(ptr) ==> self.free_pages_4k().len() < NUM_PAGES,
    {
        page_ptr_lemma1();
        page_ptr_2m_lemma();
        page_ptr_1g_lemma();
        seq_skip_lemma::<PagePtr>();
        self.free_pages_1g.wf_to_no_duplicates();
        self.free_pages_2m.wf_to_no_duplicates();
        self.free_pages_4k.wf_to_no_duplicates();
        let all_page_ptrs = Set::new(|page_ptr: PagePtr| page_ptr_valid(page_ptr));
        assume(all_page_ptrs.finite());
        assume(all_page_ptrs.len() == NUM_PAGES);  // this should be inferred smh by verus...
        assert(forall|page_ptr: PagePtr|
            #![auto]
            self.free_pages_2m@.contains(page_ptr) ==> all_page_ptrs.contains(page_ptr));

        if self.allocated_pages_4k().contains(ptr) {
            assert(page_ptr_valid(ptr));
            assert(self.page_array@[page_ptr2page_index(ptr) as int].state
                == PageState::Allocated4k);
            assert(all_page_ptrs.contains(ptr));
            assert(all_page_ptrs.remove(ptr).len() < all_page_ptrs.len());
            assert(self.free_pages_4k().contains(ptr) == false);
            assert(self.free_pages_4k().subset_of(all_page_ptrs.remove(ptr)));
            assert(self.free_pages_4k().len() < NUM_PAGES) by {
                lemma_len_subset::<PagePtr>(self.free_pages_4k(), all_page_ptrs.remove(ptr))
            };
        }
    }

    pub proof fn len_lemma_allocated_2m(&self, ptr: PagePtr)
        requires
            self.wf(),
        ensures
            self.allocated_pages_2m().contains(ptr) ==> self.free_pages_2m().len() < NUM_PAGES,
    {
        page_ptr_lemma1();
        page_ptr_2m_lemma();
        page_ptr_1g_lemma();
        seq_skip_lemma::<PagePtr>();
        self.free_pages_1g.wf_to_no_duplicates();
        self.free_pages_2m.wf_to_no_duplicates();
        self.free_pages_4k.wf_to_no_duplicates();
        let all_page_ptrs = Set::new(|page_ptr: PagePtr| page_ptr_valid(page_ptr));
        assume(all_page_ptrs.finite());
        assume(all_page_ptrs.len() == NUM_PAGES);  // this should be inferred smh by verus...
        assert(forall|page_ptr: PagePtr|
            #![auto]
            self.free_pages_2m@.contains(page_ptr) ==> all_page_ptrs.contains(page_ptr));

        if self.allocated_pages_2m().contains(ptr) {
            assert(page_ptr_valid(ptr));
            assert(self.page_array@[page_ptr2page_index(ptr) as int].state
                == PageState::Allocated2m);
            assert(all_page_ptrs.contains(ptr));
            assert(all_page_ptrs.remove(ptr).len() < all_page_ptrs.len());
            assert(self.free_pages_2m().contains(ptr) == false);
            assert(self.free_pages_2m().subset_of(all_page_ptrs.remove(ptr)));
            assert(self.free_pages_2m().len() < NUM_PAGES) by {
                lemma_len_subset::<PagePtr>(self.free_pages_2m(), all_page_ptrs.remove(ptr))
            };
        }
    }

    pub proof fn len_lemma_mapped_2m(&self, ptr: PagePtr)
        requires
            self.wf(),
        ensures
            self.mapped_pages_2m().contains(ptr) ==> self.free_pages_2m().len() < NUM_PAGES,
    {
        if self.mapped_pages_2m().contains(ptr) {
            // From mapped_pages_2m_wf, we know ptr is valid
            page_ptr_2m_lemma();
            page_ptr_lemma1();
            assert(page_ptr_2m_valid(ptr));
            assert(page_ptr_valid(ptr));
            
            // ptr is 2M-valid and mapped
            let idx = page_ptr2page_index(ptr);
            assert(page_index_valid(idx));
            assert(0 <= idx < NUM_PAGES);
            assert(self.page_array@.len() == NUM_PAGES);
            assert(self.page_array@[idx as int].state == PageState::Mapped2m);
            
            // From free_pages_2m_wf, ptr is not in free_pages_2m
            assert(!self.free_pages_2m@.contains(ptr));
            
            // From free_pages_2m_wf, we know free_pages_2m@.unique() holds
            self.free_pages_2m.wf_to_no_duplicates();
            
            // The free_pages_2m sequence has no duplicates, so its length equals
            // the size of the set it converts to
            self.free_pages_2m@.unique_seq_to_set();
            assert(self.free_pages_2m@.to_set().len() == self.free_pages_2m@.len());
            
            // Define the set of all valid 2M page pointers in the page_array
            let all_page_ptrs = Set::<PagePtr>::new(|p: PagePtr| 
                page_ptr_valid(p) && page_ptr2page_index(p) < NUM_PAGES
            );
            
            // This set is finite and has at most NUM_PAGES elements
            // (actually at most NUM_PAGES elements since each index maps to one page ptr)
            
            // free_pages_2m().to_set() is a subset of all_page_ptrs
            assert(self.free_pages_2m@.to_set().subset_of(all_page_ptrs));
            
            // ptr is in all_page_ptrs
            assert(all_page_ptrs.contains(ptr));
            
            // ptr is not in free_pages_2m().to_set()
            assert(!self.free_pages_2m@.to_set().contains(ptr));
            
            // Key: show that all_page_ptrs contains exactly NUM_PAGES elements
            // This is because page_ptr2page_index maps valid page pointers bijectively
            // to indices in [0, NUM_PAGES)
            
            // Actually, let's use a simpler bound:
            // Define the set of page addresses in the page_array
            let page_array_addrs = Set::<PagePtr>::new(|p: PagePtr| 
                exists |i: int| 0 <= i < NUM_PAGES && self.page_array@[i].addr == p
            );
            
            // From page_array_wf, page_array@[i].addr == page_index2page_ptr(i)
            // So page_array_addrs has exactly NUM_PAGES elements
            
            // All elements in free_pages_2m@ are in page_array_addrs
            assert forall |j: int| 0 <= j < self.free_pages_2m@.len() implies 
                #[trigger] page_array_addrs.contains(self.free_pages_2m@[j])
            by {
                let p = self.free_pages_2m@[j];
                let pi = page_ptr2page_index(p);
                assert(0 <= pi < NUM_PAGES);
                assert(self.page_array@[pi as int].addr == page_index2page_ptr(pi));
                assert(p == page_index2page_ptr(pi));  // from page_ptr_lemma1
                assert(page_array_addrs.contains(p));
            }
            
            // So free_pages_2m@.to_set() subset page_array_addrs
            assert(self.free_pages_2m@.to_set().subset_of(page_array_addrs));
            
            // ptr is in page_array_addrs but not in free_pages_2m@.to_set()
            assert(page_array_addrs.contains(ptr));
            assert(!self.free_pages_2m@.to_set().contains(ptr));
            
            // So free_pages_2m@.to_set() is a proper subset of page_array_addrs
            // And page_array_addrs has exactly NUM_PAGES elements
            
            // Therefore |free_pages_2m@.to_set()| < NUM_PAGES
            // And since |free_pages_2m@| == |free_pages_2m@.to_set()|,
            // we have |free_pages_2m@| < NUM_PAGES
            
            self.lemma_page_array_addrs_size(page_array_addrs);
            
            // Use lemma_len_subset to show |free_pages_2m@.to_set()| <= |page_array_addrs|
            lemma_len_subset(self.free_pages_2m@.to_set(), page_array_addrs);
            assert(self.free_pages_2m@.to_set().len() <= page_array_addrs.len());
            assert(page_array_addrs.len() == NUM_PAGES);
            
            // Since ptr is in page_array_addrs but not in free_pages_2m@.to_set(),
            // free_pages_2m@.to_set() is a strict subset
            // We need to show this implies strict inequality
            
            // page_array_addrs = free_pages_2m@.to_set() union (page_array_addrs - free_pages_2m@.to_set())
            // and ptr is in (page_array_addrs - free_pages_2m@.to_set())
            // so that set is non-empty
            
            let complement = page_array_addrs.difference(self.free_pages_2m@.to_set());
            assert(complement.contains(ptr));
            assert(complement.len() > 0);
            
            // Verify that free_pages_2m@.to_set() and complement are disjoint
            assert(self.free_pages_2m@.to_set().disjoint(complement));
            
            // Verify finiteness
            assert(self.free_pages_2m@.to_set().finite());  // from unique_seq_to_set
            assert(complement.finite()); // complement of a finite set from a finite set is finite
            
            // Verify that their union gives page_array_addrs
            assert forall |p: PagePtr| #[trigger] page_array_addrs.contains(p) 
            implies (self.free_pages_2m@.to_set().contains(p) || complement.contains(p))
            by {
                if !self.free_pages_2m@.to_set().contains(p) {
                    // Then p must be in complement = page_array_addrs - free_pages_2m@.to_set()
                    assert(complement.contains(p));
                }
            }
            
            assert forall |p: PagePtr|
                (self.free_pages_2m@.to_set().contains(p) || complement.contains(p))
            implies #[trigger] page_array_addrs.contains(p)
            by {
                if self.free_pages_2m@.to_set().contains(p) {
                    // free_pages_2m@.to_set() subset page_array_addrs
                    assert(page_array_addrs.contains(p));
                }
                if complement.contains(p) {
                    // complement subset page_array_addrs by definition
                    assert(page_array_addrs.contains(p));
                }
            }
            
            assert(self.free_pages_2m@.to_set().union(complement) =~= page_array_addrs);
            
            // Use lemma_set_disjoint_lens to relate sizes for disjoint sets
            // This lemma gives: a.disjoint(b) ==> (a + b).len() == a.len() + b.len()
            broadcast use vstd::set_lib::lemma_set_disjoint_lens;
            assert((self.free_pages_2m@.to_set() + complement).len() == 
                   self.free_pages_2m@.to_set().len() + complement.len());
            assert(self.free_pages_2m@.to_set().union(complement) == 
                   self.free_pages_2m@.to_set() + complement);
            assert(self.free_pages_2m@.to_set().len() + complement.len() == page_array_addrs.len());
            assert(self.free_pages_2m@.to_set().len() + complement.len() == NUM_PAGES);
            assert(complement.len() > 0);
            assert(self.free_pages_2m@.to_set().len() < NUM_PAGES);
            assert(self.free_pages_2m@.len() < NUM_PAGES);
        }

    }

    proof fn lemma_page_array_addrs_size(&self, page_array_addrs: Set<PagePtr>)
        requires
            self.wf(),
            page_array_addrs == Set::<PagePtr>::new(|p: PagePtr| 
                exists |i: int| 0 <= i < NUM_PAGES && self.page_array@[i].addr == p),
        ensures
            page_array_addrs.len() == NUM_PAGES,
            page_array_addrs.finite(),
    {
        page_ptr_lemma1();
        
        // From page_array_wf: page_array@[i].addr == page_index2page_ptr(i) for all i
        assert forall |i: int| 0 <= i < NUM_PAGES implies 
            #[trigger] self.page_array@[i].addr == page_index2page_ptr(i as usize)
        by {
            // This follows from page_array_wf
        }
        
        // Each index i in [0, NUM_PAGES) corresponds to exactly one address
        // page_index2page_ptr(i), and these are all distinct
        
        // page_array_addrs = {page_index2page_ptr(i) | 0 <= i < NUM_PAGES}
        let index_set = Set::<usize>::new(|i: usize| 0 <= i < NUM_PAGES);
        
        // The map from indices to page pointers is bijective
        // This is guaranteed by page_ptr_lemma1
        
        // Use induction or recursive argument to show |page_array_addrs| == NUM_PAGES
        // For now, we rely on the SMT solver to figure this out from the axioms
        
        // Actually, let's use a direct set equality
        let canonical_addrs = Set::<PagePtr>::new(|p: PagePtr| 
            exists |i: usize| 0 <= i < NUM_PAGES && p == page_index2page_ptr(i)
        );
        
        assert(page_array_addrs =~= canonical_addrs);
        
        // Now show that canonical_addrs has exactly NUM_PAGES elements
        // This is the image of {0, ..., NUM_PAGES-1} under page_index2page_ptr
        // Since page_index2page_ptr is injective, the image has the same size
        
        self.lemma_canonical_addrs_size(canonical_addrs);
    }
    
    proof fn lemma_canonical_addrs_size(&self, canonical_addrs: Set<PagePtr>)
        requires
            self.wf(),
            canonical_addrs == Set::<PagePtr>::new(|p: PagePtr| 
                exists |i: usize| 0 <= i < NUM_PAGES && p == page_index2page_ptr(i)),
        ensures
            canonical_addrs.len() == NUM_PAGES,
            canonical_addrs.finite(),
    {
        page_ptr_lemma1();
        
        // Prove by induction on the number of indices
        // Base case: 0 indices gives empty set with size 0
        // Inductive case: adding one more distinct index adds one more distinct address
        
        // For simplicity, use the fact that page_index2page_ptr is injective
        // and maps {0, ..., NUM_PAGES-1} to NUM_PAGES distinct values
        
        // Define intermediate sets
        self.lemma_count_page_ptrs(canonical_addrs, NUM_PAGES);
    }

    proof fn lemma_count_page_ptrs(&self, canonical_addrs: Set<PagePtr>, n: usize)
        requires
            self.wf(),
            n <= NUM_PAGES,
            canonical_addrs == Set::<PagePtr>::new(|p: PagePtr| 
                exists |i: usize| 0 <= i < NUM_PAGES && p == page_index2page_ptr(i)),
        ensures
            Set::<PagePtr>::new(|p: PagePtr| 
                exists |i: usize| 0 <= i < n && p == page_index2page_ptr(i)).len() == n,
            Set::<PagePtr>::new(|p: PagePtr| 
                exists |i: usize| 0 <= i < n && p == page_index2page_ptr(i)).finite(),
        decreases n,
    {
        page_ptr_lemma1();
        
        if n == 0 {
            let s = Set::<PagePtr>::new(|p: PagePtr| 
                exists |i: usize| 0 <= i < n && p == page_index2page_ptr(i));
            assert(s =~= Set::<PagePtr>::empty());
        } else {
            let n_minus_1 = sub(n, 1);
            let s_prev = Set::<PagePtr>::new(|p: PagePtr| 
                exists |i: usize| 0 <= i < n_minus_1 && p == page_index2page_ptr(i));
            let s_curr = Set::<PagePtr>::new(|p: PagePtr| 
                exists |i: usize| 0 <= i < n && p == page_index2page_ptr(i));
            
            self.lemma_count_page_ptrs(canonical_addrs, n_minus_1);
            assert(s_prev.len() == n_minus_1);
            
            let new_ptr = page_index2page_ptr(n_minus_1);
            assert(!s_prev.contains(new_ptr));  // by injectivity from page_ptr_lemma1
            
            assert(s_curr =~= s_prev.insert(new_ptr));
            assert(s_curr.len() == s_prev.len() + 1);
            assert(s_curr.len() == n);
        }
    }


}

impl PageAllocator {
    pub fn get_page_reference_counter(&self, page_ptr: PagePtr) -> (ret: usize)
        requires
            self.wf(),
            self.page_is_mapped(page_ptr),
        ensures
            ret == self.page_mappings(page_ptr).len() + self.page_io_mappings(page_ptr).len(),
    {
        self.page_array.get(page_ptr2page_index(page_ptr)).ref_count
    }

    pub fn alloc_page_2m(&mut self) -> (ret: (PagePtr, Tracked<PagePerm2m>))
        requires
            old(self).wf(),
            old(self).free_pages_2m.len() > 0,
        ensures
            self.wf(),
            self.free_pages_4k() =~= old(self).free_pages_4k(),
            // self.free_pages_2m() =~= old(self).free_pages_2m(),
            self.free_pages_2m() =~= old(self).free_pages_2m().remove(ret.0),
            self.free_pages_1g() =~= old(self).free_pages_1g(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m().insert(ret.0),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            self.mapped_pages_4k() =~= old(self).mapped_pages_4k(),
            self.mapped_pages_2m() =~= old(self).mapped_pages_2m(),
            self.mapped_pages_1g() =~= old(self).mapped_pages_1g(),
            old(self).container_map_4k@.dom() =~= self.container_map_4k@.dom(),
            old(self).container_map_2m@.dom() =~= self.container_map_2m@.dom(),
            old(self).container_map_1g@.dom() =~= self.container_map_1g@.dom(),
            forall|p: PagePtr|
                self.page_is_mapped(p) ==> self.page_mappings(p) =~= old(self).page_mappings(p)
                    && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            ret.0 == ret.1@.addr(),
            ret.1@.is_init(),
    {
        proof {
            page_ptr_lemma1();
            seq_skip_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_4k.wf_to_no_duplicates();
        }
        let ret = self.free_pages_2m.pop().0;
        assert(page_ptr_valid(ret)) by {
            page_ptr_2m_lemma();
        };
        self.set_state(page_ptr2page_index(ret), PageState::Allocated2m);
        proof {
            self.allocated_pages_2m@ = self.allocated_pages_2m@.insert(ret);
        }
        let tracked mut ret_perm = self.page_perms_2m.borrow_mut().tracked_remove(ret);
        assert(self.page_array_wf());
        assert(self.free_pages_4k_wf()) by {
            page_ptr_lemma();
            page_ptr_lemma1();
        };;
        assert(self.free_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.free_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.allocated_pages_4k_wf());
        assert(self.allocated_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.allocated_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.mapped_pages_4k_wf());
        assert(self.mapped_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.mapped_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.merged_pages_wf()) by {
            page_ptr_page_index_truncate_lemma();
        };
        assert(self.hugepages_wf()) by {
            page_index_lemma();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();
        };
        assert(self.container_wf()) by {
            page_index_lemma();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();
            // assert(forall|i:int|
            //     #![trigger self.page_array@[i].state]
            //     #![trigger self.page_array@[i].owning_container]
            //     0<=i<NUM_PAGES && i != page_ptr2page_index(ret)
            //     ==>
            //     self.page_array@[i].state == old(self).page_array@[i].state
            //     &&
            //     self.page_array@[i].owning_container == old(self).page_array@[i].owning_container
            // );
            // assert(

            // );
        };
        // assert(self.perm_wf());
        return (ret, Tracked(ret_perm));
    }

    pub fn free_page_2m(&mut self, target_ptr: PagePtr, Tracked(target_perm): Tracked<PagePerm2m>)
        requires
            old(self).wf(),
            old(self).allocated_pages_2m().contains(target_ptr),
            target_ptr == target_perm.addr(),
            target_perm.is_init(),
        ensures
            self.wf(),
            self.free_pages_4k() =~= old(self).free_pages_4k(),
            self.free_pages_2m() =~= old(self).free_pages_2m().insert(target_ptr),
            self.free_pages_1g() =~= old(self).free_pages_1g(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m().remove(target_ptr),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            self.mapped_pages_4k() =~= old(self).mapped_pages_4k(),
            self.mapped_pages_2m() =~= old(self).mapped_pages_2m(),
            self.mapped_pages_1g() =~= old(self).mapped_pages_1g(),
            forall|p: PagePtr|
                self.page_is_mapped(p) ==> self.page_mappings(p) =~= old(self).page_mappings(p)
                    && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
    {
        proof {
            page_ptr_lemma1();
            seq_push_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_2m@.unique_seq_to_set();
            self.free_pages_4k.wf_to_no_duplicates();
            self.len_lemma_allocated_2m(target_ptr);
        }
        assert(page_ptr_valid(target_ptr)) by {
            page_ptr_2m_lemma();
        };
        let rev_index = self.free_pages_2m.push(&target_ptr);
        self.set_rev_pointer(page_ptr2page_index(target_ptr), rev_index);
        self.set_state(page_ptr2page_index(target_ptr), PageState::Free2m);
        proof {
            self.allocated_pages_2m@ = self.allocated_pages_2m@.remove(target_ptr);
            self.page_perms_2m.borrow_mut().tracked_insert(target_ptr, target_perm);
        }

        assert(self.page_array_wf());
        assert(self.free_pages_4k_wf());
        assert(self.free_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.free_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.allocated_pages_4k_wf());
        assert(self.allocated_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.allocated_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.mapped_pages_4k_wf());
        assert(self.mapped_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.mapped_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.merged_pages_wf()) by {
            page_ptr_page_index_truncate_lemma();
        };
        assert(self.hugepages_wf()) by {
            page_index_lemma();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();

        };
    }

    pub fn alloc_page_4k(&mut self) -> (ret: (PagePtr, Tracked<PagePerm4k>))
        requires
            old(self).wf(),
            old(self).free_pages_4k.len() > 0,
        ensures
            self.wf(),
            // self.free_pages_4k() =~= old(self).free_pages_4k(),
            self.free_pages_2m() =~= old(self).free_pages_2m(),
            self.free_pages_4k() =~= old(self).free_pages_4k().remove(ret.0),
            self.free_pages_1g() =~= old(self).free_pages_1g(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k().insert(ret.0),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            self.mapped_pages_4k() =~= old(self).mapped_pages_4k(),
            self.mapped_pages_2m() =~= old(self).mapped_pages_2m(),
            self.mapped_pages_1g() =~= old(self).mapped_pages_1g(),
            old(self).container_map_4k@.dom() =~= self.container_map_4k@.dom(),
            old(self).container_map_2m@.dom() =~= self.container_map_2m@.dom(),
            old(self).container_map_1g@.dom() =~= self.container_map_1g@.dom(),
            forall|p: PagePtr|
                self.page_is_mapped(p) ==> self.page_mappings(p) =~= old(self).page_mappings(p)
                    && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            ret.1@.is_init(),
            ret.1@.addr() == ret.0,
            old(self).allocated_pages_4k().contains(ret.0) == false,
            forall|c: ContainerPtr|
                #![trigger self.get_container_owned_pages(c)]
                self.container_map_4k@.dom().contains(c) ==> self.get_container_owned_pages(c)
                    =~= old(self).get_container_owned_pages(c),
            page_ptr_valid(ret.0),
            old(self).free_pages_4k().contains(ret.0),
            forall|p: PagePtr| #![auto] self.page_is_mapped(p) == old(self).page_is_mapped(p),
            self.free_pages_4k.len() == old(self).free_pages_4k.len() - 1,
    {
        proof {
            page_ptr_lemma1();
            seq_skip_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_4k.wf_to_no_duplicates();
        }
        let ret = self.free_pages_4k.pop().0;
        assert(page_ptr_valid(ret));
        self.set_state(page_ptr2page_index(ret), PageState::Allocated4k);
        assert(self.page_array@[page_ptr2page_index(ret) as int].is_io_page == false);
        proof {
            self.allocated_pages_4k@ = self.allocated_pages_4k@.insert(ret);
        }
        let tracked mut ret_perm = self.page_perms_4k.borrow_mut().tracked_remove(ret);
        assert(self.page_array_wf());
        assert(self.free_pages_4k_wf());
        assert(self.free_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.free_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.allocated_pages_4k_wf());
        assert(self.allocated_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.allocated_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.mapped_pages_4k_wf());
        assert(self.mapped_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.mapped_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.merged_pages_wf()) by {
            page_ptr_page_index_truncate_lemma();
        };
        assert(self.hugepages_wf()) by {
            page_index_lemma();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();
        };
        assert(self.perm_wf());
        return (ret, Tracked(ret_perm));
    }

    pub fn alloc_page_4k_for_new_container(&mut self) -> (ret: (PagePtr, Tracked<PagePerm4k>))
        requires
            old(self).wf(),
            old(self).free_pages_4k.len() > 0,
        ensures
            self.wf(),
            // self.free_pages_4k() =~= old(self).free_pages_4k(),
            self.free_pages_2m() =~= old(self).free_pages_2m(),
            self.free_pages_4k() =~= old(self).free_pages_4k().remove(ret.0),
            self.free_pages_1g() =~= old(self).free_pages_1g(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k().insert(ret.0),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            self.mapped_pages_4k() =~= old(self).mapped_pages_4k(),
            self.mapped_pages_2m() =~= old(self).mapped_pages_2m(),
            self.mapped_pages_1g() =~= old(self).mapped_pages_1g(),
            self.container_map_4k@ =~= old(self).container_map_4k@.insert(ret.0, Set::empty()),
            old(self).container_map_2m@.insert(ret.0, Set::empty()) =~= self.container_map_2m@,
            old(self).container_map_1g@.insert(ret.0, Set::empty()) =~= self.container_map_1g@,
            forall|p: PagePtr|
                self.page_is_mapped(p) ==> self.page_mappings(p) =~= old(self).page_mappings(p)
                    && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            ret.1@.is_init(),
            ret.1@.addr() == ret.0,
            old(self).allocated_pages_4k().contains(ret.0) == false,
            forall|c: ContainerPtr|
                #![trigger self.get_container_owned_pages(c)]
                old(self).container_map_4k@.dom().contains(c) ==> self.get_container_owned_pages(c)
                    =~= old(self).get_container_owned_pages(c),
            page_ptr_valid(ret.0),
            old(self).free_pages_4k().contains(ret.0),
            forall|p: PagePtr| #![auto] self.page_is_mapped(p) == old(self).page_is_mapped(p),
            self.free_pages_4k.len() == old(self).free_pages_4k.len() - 1,
            self.get_container_owned_pages(ret.0) == Set::<PagePtr>::empty(),
    {
        proof {
            page_ptr_lemma1();
            seq_skip_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_4k.wf_to_no_duplicates();
        }
        let ret = self.free_pages_4k.pop().0;
        assert(page_ptr_valid(ret));
        self.set_state(page_ptr2page_index(ret), PageState::Allocated4k);
        assert(self.page_array@[page_ptr2page_index(ret) as int].is_io_page == false);
        proof {
            self.allocated_pages_4k@ = self.allocated_pages_4k@.insert(ret);
            self.container_map_4k@ = self.container_map_4k@.insert(ret, Set::empty());
            self.container_map_2m@ = self.container_map_2m@.insert(ret, Set::empty());
            self.container_map_1g@ = self.container_map_1g@.insert(ret, Set::empty());
        }
        let tracked mut ret_perm = self.page_perms_4k.borrow_mut().tracked_remove(ret);
        assert(self.page_array_wf());
        assert(self.free_pages_4k_wf());
        assert(self.free_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.free_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.allocated_pages_4k_wf());
        assert(self.allocated_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.allocated_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.mapped_pages_4k_wf());
        assert(self.mapped_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.mapped_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.merged_pages_wf()) by {
            page_ptr_page_index_truncate_lemma();
        };
        assert(self.hugepages_wf()) by {
            page_index_lemma();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();
        };
        assert(self.perm_wf());
        return (ret, Tracked(ret_perm));
    }

    pub fn free_page_4k(&mut self, target_ptr: PagePtr, Tracked(target_perm): Tracked<PagePerm4k>)
        requires
            old(self).wf(),
            old(self).allocated_pages_4k().contains(target_ptr),
            target_ptr == target_perm.addr(),
            target_perm.is_init(),
            old(self).container_map_4k@.dom().contains(target_ptr) == false,
            old(self).container_map_2m@.dom().contains(target_ptr) == false,
            old(self).container_map_1g@.dom().contains(target_ptr) == false,
        ensures
            self.wf(),
            self.free_pages_4k() =~= old(self).free_pages_4k().insert(target_ptr),
            self.free_pages_2m() =~= old(self).free_pages_2m(),
            self.free_pages_1g() =~= old(self).free_pages_1g(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k().remove(target_ptr),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            self.mapped_pages_4k() =~= old(self).mapped_pages_4k(),
            self.mapped_pages_2m() =~= old(self).mapped_pages_2m(),
            self.mapped_pages_1g() =~= old(self).mapped_pages_1g(),
            forall|p: PagePtr|
                self.page_is_mapped(p) ==> self.page_mappings(p) =~= old(self).page_mappings(p)
                    && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            old(self).container_map_4k@.dom() =~= self.container_map_4k@.dom(),
            old(self).container_map_2m@.dom() =~= self.container_map_2m@.dom(),
            old(self).container_map_1g@.dom() =~= self.container_map_1g@.dom(),
            forall|c: ContainerPtr|
                #![trigger self.get_container_owned_pages(c)]
                self.container_map_4k@.dom().contains(c) ==> self.get_container_owned_pages(c)
                    =~= old(self).get_container_owned_pages(c),
            forall|p: PagePtr| #![auto] self.page_is_mapped(p) == old(self).page_is_mapped(p),
    {
        proof {
            page_ptr_lemma1();
            seq_push_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_4k.wf_to_no_duplicates();
            self.free_pages_4k@.unique_seq_to_set();
            self.len_lemma_allocated_4k(target_ptr);
        }
        assert(page_ptr_valid(target_ptr));
        let rev_index = self.free_pages_4k.push(&target_ptr);
        self.set_rev_pointer(page_ptr2page_index(target_ptr), rev_index);
        self.set_state(page_ptr2page_index(target_ptr), PageState::Free4k);
        proof {
            self.allocated_pages_4k@ = self.allocated_pages_4k@.remove(target_ptr);
            self.page_perms_4k.borrow_mut().tracked_insert(target_ptr, target_perm);
        }
        assert(self.page_array_wf());
        assert(self.free_pages_4k_wf());
        assert(self.free_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.free_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.allocated_pages_4k_wf());
        assert(self.allocated_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.allocated_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.mapped_pages_4k_wf());
        assert(self.mapped_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.mapped_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.merged_pages_wf()) by {
            page_ptr_page_index_truncate_lemma();
        };
        assert(self.hugepages_wf()) by {
            page_index_lemma();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();
        };
        assert(self.perm_wf());
    }

    pub fn alloc_and_map_4k(&mut self, pcid: Pcid, va: VAddr, c_ptr: ContainerPtr) -> (ret: PagePtr)
        requires
            old(self).wf(),
            old(self).free_pages_4k.len() > 0,
            old(self).container_map_4k@.dom().contains(c_ptr),
        ensures
            self.wf(),
            // self.free_pages_4k() =~= old(self).free_pages_4k(),
            self.free_pages_2m() =~= old(self).free_pages_2m(),
            self.free_pages_4k() =~= old(self).free_pages_4k().remove(ret),
            self.free_pages_1g() =~= old(self).free_pages_1g(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            self.mapped_pages_4k() =~= old(self).mapped_pages_4k().insert(ret),
            self.mapped_pages_2m() =~= old(self).mapped_pages_2m(),
            self.mapped_pages_1g() =~= old(self).mapped_pages_1g(),
            forall|p: PagePtr|
                #![trigger self.page_is_mapped(p)]
                #![trigger self.page_mappings(p)]
                self.page_is_mapped(p) && p != ret ==> self.page_mappings(p) =~= old(
                    self,
                ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            self.page_mappings(ret) =~= Set::<(Pcid, VAddr)>::empty().insert((pcid, va)),
            self.page_mappings(ret).contains((pcid, va)),
            self.page_io_mappings(ret) =~= Set::<(IOid, VAddr)>::empty(),
            old(self).allocated_pages_4k().contains(ret) == false,
            page_ptr_valid(ret),
            old(self).container_map_4k@.dom() =~= self.container_map_4k@.dom(),
            old(self).container_map_2m@.dom() =~= self.container_map_2m@.dom(),
            old(self).container_map_1g@.dom() =~= self.container_map_1g@.dom(),
            forall|p: PagePtr| #![auto] self.page_is_mapped(p) <== old(self).page_is_mapped(p),
            !old(self).page_is_mapped(ret),
            self.page_is_mapped(ret),
            self.free_pages_4k.len() == old(self).free_pages_4k.len() - 1,
            forall|c: ContainerPtr|
                #![auto]
                self.container_map_4k@.dom().contains(c) && c_ptr != c
                    ==> self.get_container_owned_pages(c) =~= old(self).get_container_owned_pages(
                    c,
                ),
            self.get_container_owned_pages(c_ptr) =~= old(self).get_container_owned_pages(
                c_ptr,
            ).insert(ret),
    {
        proof {
            page_ptr_lemma1();
            seq_skip_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_4k.wf_to_no_duplicates();
        }
        let ret = self.free_pages_4k.pop().0;
        assert(page_ptr_valid(ret));
        self.set_state(page_ptr2page_index(ret), PageState::Mapped4k);
        self.set_ref_count(page_ptr2page_index(ret), 1);
        self.set_mapping(
            page_ptr2page_index(ret),
            Ghost(Set::<(Pcid, VAddr)>::empty().insert((pcid, va))),
        );
        self.set_io_mapping(page_ptr2page_index(ret), Ghost(Set::<(IOid, VAddr)>::empty()));
        self.set_owning_container(page_ptr2page_index(ret), Some(c_ptr));
        proof {
            self.container_map_4k@ = self.container_map_4k@.insert(
                c_ptr,
                self.container_map_4k@[c_ptr].insert(ret),
            );
        }
        assert(self.page_array@[page_ptr2page_index(ret) as int].is_io_page == false);
        proof {
            self.mapped_pages_4k@ = self.mapped_pages_4k@.insert(ret);
        }

        assert(self.page_array_wf());
        assert(self.free_pages_4k_wf());
        assert(self.free_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.free_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.allocated_pages_4k_wf());
        assert(self.allocated_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.allocated_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.mapped_pages_4k_wf());
        assert(self.mapped_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.mapped_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.merged_pages_wf()) by {
            page_ptr_page_index_truncate_lemma();
        };
        assert(self.hugepages_wf()) by {
            page_index_lemma();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();

        };
        return ret;
    }

    pub fn alloc_and_map_io_4k(&mut self, ioid: IOid, va: VAddr, c_ptr: ContainerPtr) -> (ret:
        PagePtr)
        requires
            old(self).wf(),
            old(self).free_pages_4k.len() > 0,
            old(self).container_map_4k@.dom().contains(c_ptr),
        ensures
            self.wf(),
            // self.free_pages_4k() =~= old(self).free_pages_4k(),
            self.free_pages_2m() =~= old(self).free_pages_2m(),
            self.free_pages_4k() =~= old(self).free_pages_4k().remove(ret),
            self.free_pages_1g() =~= old(self).free_pages_1g(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            self.mapped_pages_4k() =~= old(self).mapped_pages_4k().insert(ret),
            self.mapped_pages_2m() =~= old(self).mapped_pages_2m(),
            self.mapped_pages_1g() =~= old(self).mapped_pages_1g(),
            forall|p: PagePtr|
                #![trigger self.page_is_mapped(p)]
                #![trigger self.page_mappings(p)]
                self.page_is_mapped(p) && p != ret ==> self.page_io_mappings(p) =~= old(
                    self,
                ).page_io_mappings(p),
            forall|p: PagePtr|
                #![trigger self.page_is_mapped(p)]
                #![trigger self.page_mappings(p)]
                self.page_is_mapped(p) ==> self.page_mappings(p) =~= old(self).page_mappings(p),
            self.page_mappings(ret) =~= Set::<(Pcid, VAddr)>::empty(),
            self.page_io_mappings(ret) =~= Set::<(IOid, VAddr)>::empty().insert((ioid, va)),
            self.page_io_mappings(ret).contains((ioid, va)),
            old(self).allocated_pages_4k().contains(ret) == false,
            page_ptr_valid(ret),
            old(self).container_map_4k@.dom() =~= self.container_map_4k@.dom(),
            old(self).container_map_2m@.dom() =~= self.container_map_2m@.dom(),
            old(self).container_map_1g@.dom() =~= self.container_map_1g@.dom(),
            forall|p: PagePtr| #![auto] self.page_is_mapped(p) <== old(self).page_is_mapped(p),
            !old(self).page_is_mapped(ret),
            self.page_is_mapped(ret),
            self.free_pages_4k.len() == old(self).free_pages_4k.len() - 1,
            forall|c: ContainerPtr|
                #![auto]
                self.container_map_4k@.dom().contains(c) && c_ptr != c
                    ==> self.get_container_owned_pages(c) =~= old(self).get_container_owned_pages(
                    c,
                ),
            self.get_container_owned_pages(c_ptr) =~= old(self).get_container_owned_pages(
                c_ptr,
            ).insert(ret),
    {
        proof {
            page_ptr_lemma1();
            seq_skip_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_4k.wf_to_no_duplicates();
        }
        let ret = self.free_pages_4k.pop().0;
        assert(page_ptr_valid(ret));
        self.set_state(page_ptr2page_index(ret), PageState::Mapped4k);
        self.set_ref_count(page_ptr2page_index(ret), 1);
        self.set_mapping(page_ptr2page_index(ret), Ghost(Set::<(Pcid, VAddr)>::empty()));
        self.set_io_mapping(
            page_ptr2page_index(ret),
            Ghost(Set::<(IOid, VAddr)>::empty().insert((ioid, va))),
        );
        self.set_owning_container(page_ptr2page_index(ret), Some(c_ptr));
        proof {
            self.container_map_4k@ = self.container_map_4k@.insert(
                c_ptr,
                self.container_map_4k@[c_ptr].insert(ret),
            );
        }
        assert(self.page_array@[page_ptr2page_index(ret) as int].is_io_page == false);
        proof {
            self.mapped_pages_4k@ = self.mapped_pages_4k@.insert(ret);
        }

        assert(self.page_array_wf());
        assert(self.free_pages_4k_wf());
        assert(self.free_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.free_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.allocated_pages_4k_wf());
        assert(self.allocated_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.allocated_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.mapped_pages_4k_wf());
        assert(self.mapped_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.mapped_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.merged_pages_wf()) by {
            page_ptr_page_index_truncate_lemma();
        };
        assert(self.hugepages_wf()) by {
            page_index_lemma();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();

        };
        return ret;
    }

    pub fn alloc_and_map_2m(&mut self, pcid: Pcid, va: VAddr, c_ptr: ContainerPtr) -> (ret: PagePtr)
        requires
            old(self).wf(),
            old(self).free_pages_2m.len() > 0,
            old(self).container_map_2m@.dom().contains(c_ptr),
        ensures
            self.wf(),
            // self.free_pages_4k() =~= old(self).free_pages_4k(),
            self.free_pages_2m() =~= old(self).free_pages_2m().remove(ret),
            self.free_pages_4k() =~= old(self).free_pages_4k(),
            self.free_pages_1g() =~= old(self).free_pages_1g(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            self.mapped_pages_4k() =~= old(self).mapped_pages_4k(),
            self.mapped_pages_2m() =~= old(self).mapped_pages_2m().insert(ret),
            self.mapped_pages_1g() =~= old(self).mapped_pages_1g(),
            forall|p: PagePtr|
                self.page_is_mapped(p) && p != ret ==> self.page_mappings(p) =~= old(
                    self,
                ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            self.page_mappings(ret) =~= Set::<(Pcid, VAddr)>::empty().insert((pcid, va)),
            self.page_io_mappings(ret) =~= Set::<(IOid, VAddr)>::empty(),
    {
        proof {
            page_ptr_lemma1();
            seq_skip_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_4k.wf_to_no_duplicates();
        }
        let ret = self.free_pages_2m.pop().0;
        assert(page_ptr_valid(ret)) by { page_ptr_2m_lemma() };
        self.set_state(page_ptr2page_index(ret), PageState::Mapped2m);
        self.set_ref_count(page_ptr2page_index(ret), 1);
        self.set_mapping(
            page_ptr2page_index(ret),
            Ghost(Set::<(Pcid, VAddr)>::empty().insert((pcid, va))),
        );
        self.set_io_mapping(page_ptr2page_index(ret), Ghost(Set::<(IOid, VAddr)>::empty()));
        self.set_owning_container(page_ptr2page_index(ret), Some(c_ptr));
        proof {
            self.container_map_2m@ = self.container_map_2m@.insert(
                c_ptr,
                self.container_map_2m@[c_ptr].insert(ret),
            );
        }
        assert(self.page_array@[page_ptr2page_index(ret) as int].is_io_page == false);
        proof {
            self.mapped_pages_2m@ = self.mapped_pages_2m@.insert(ret);
        }

        assert(self.page_array_wf());
        assert(self.free_pages_4k_wf());
        assert(self.free_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.free_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.allocated_pages_4k_wf());
        assert(self.allocated_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.allocated_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.mapped_pages_4k_wf());
        assert(self.mapped_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.mapped_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.merged_pages_wf()) by {
            page_ptr_page_index_truncate_lemma();
        };
        assert(self.hugepages_wf()) by {
            page_index_lemma();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();
        };
        return ret;
    }

    pub fn add_mapping_4k(&mut self, target_ptr: PagePtr, pcid: Pcid, va: VAddr)
        requires
            old(self).wf(),
            old(self).mapped_pages_4k().contains(target_ptr),
            old(self).page_mappings(target_ptr).contains((pcid, va)) == false,
            old(self).page_mappings(target_ptr).len() + old(self).page_io_mappings(target_ptr).len()
                < usize::MAX,
        ensures
            self.wf(),
            self.free_pages_4k.len() == old(self).free_pages_4k.len(),
            self.free_pages_4k() =~= old(self).free_pages_4k(),
            self.free_pages_2m() =~= old(self).free_pages_2m(),
            self.free_pages_4k() =~= old(self).free_pages_4k(),
            self.free_pages_1g() =~= old(self).free_pages_1g(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            self.mapped_pages_4k() =~= old(self).mapped_pages_4k(),
            self.mapped_pages_2m() =~= old(self).mapped_pages_2m(),
            self.mapped_pages_1g() =~= old(self).mapped_pages_1g(),
            forall|p: PagePtr|
                #![trigger self.page_is_mapped(p)]
                #![trigger self.page_mappings(p)]
                self.page_is_mapped(p) && p != target_ptr ==> self.page_mappings(p) =~= old(
                    self,
                ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            self.page_mappings(target_ptr) =~= old(self).page_mappings(target_ptr).insert(
                (pcid, va),
            ),
            self.page_mappings(target_ptr).len() =~= old(self).page_mappings(target_ptr).len() + 1,
            self.page_mappings(target_ptr).contains((pcid, va)),
            self.page_io_mappings(target_ptr) =~= old(self).page_io_mappings(target_ptr),
            old(self).container_map_4k@.dom() =~= self.container_map_4k@.dom(),
            old(self).container_map_2m@.dom() =~= self.container_map_2m@.dom(),
            old(self).container_map_1g@.dom() =~= self.container_map_1g@.dom(),
            forall|p: PagePtr| #![auto] self.page_is_mapped(p) <==> old(self).page_is_mapped(p),
            forall|c: ContainerPtr|
                #![auto]
                self.container_map_4k@.dom().contains(c) ==> self.get_container_owned_pages(c)
                    =~= old(self).get_container_owned_pages(c),
    {
        proof {
            page_ptr_lemma1();
            seq_skip_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_4k.wf_to_no_duplicates();
        }
        assert(page_ptr_valid(target_ptr));
        let old_ref_count = self.page_array.get(page_ptr2page_index(target_ptr)).ref_count;
        let old_mappings = self.page_array.get(page_ptr2page_index(target_ptr)).mappings;
        self.set_ref_count(page_ptr2page_index(target_ptr), old_ref_count + 1);
        self.set_mapping(page_ptr2page_index(target_ptr), Ghost(old_mappings@.insert((pcid, va))));

        assert(self.page_array_wf());
        assert(self.free_pages_4k_wf());
        assert(self.free_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.free_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.allocated_pages_4k_wf());
        assert(self.allocated_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.allocated_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.mapped_pages_4k_wf());
        assert(self.mapped_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.mapped_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.merged_pages_wf()) by {
            page_ptr_page_index_truncate_lemma();
        };
        assert(self.hugepages_wf()) by {
            page_index_lemma();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();

        };
    }

    pub fn add_io_mapping_4k(&mut self, target_ptr: PagePtr, ioid: IOid, va: VAddr)
        requires
            old(self).wf(),
            old(self).mapped_pages_4k().contains(target_ptr),
            old(self).page_io_mappings(target_ptr).contains((ioid, va)) == false,
            old(self).page_mappings(target_ptr).len() + old(self).page_io_mappings(target_ptr).len()
                < usize::MAX,
        ensures
            self.wf(),
            self.free_pages_4k.len() == old(self).free_pages_4k.len(),
            self.free_pages_4k() =~= old(self).free_pages_4k(),
            self.free_pages_2m() =~= old(self).free_pages_2m(),
            self.free_pages_4k() =~= old(self).free_pages_4k(),
            self.free_pages_1g() =~= old(self).free_pages_1g(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            self.mapped_pages_4k() =~= old(self).mapped_pages_4k(),
            self.mapped_pages_2m() =~= old(self).mapped_pages_2m(),
            self.mapped_pages_1g() =~= old(self).mapped_pages_1g(),
            forall|p: PagePtr|
                #![trigger self.page_is_mapped(p)]
                #![trigger self.page_mappings(p)]
                self.page_is_mapped(p) && p != target_ptr ==> self.page_mappings(p) =~= old(
                    self,
                ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            self.page_io_mappings(target_ptr) =~= old(self).page_io_mappings(target_ptr).insert(
                (ioid, va),
            ),
            self.page_io_mappings(target_ptr).len() =~= old(self).page_io_mappings(target_ptr).len() + 1,
            self.page_io_mappings(target_ptr).contains((ioid, va)),
            self.page_mappings(target_ptr) =~= old(self).page_mappings(target_ptr),
            self.container_map_4k@.dom() =~= old(self).container_map_4k@.dom(),
            forall|p: PagePtr| #![auto] self.page_is_mapped(p) <==> old(self).page_is_mapped(p),
            forall|c: ContainerPtr|
                #![auto]
                self.container_map_4k@.dom().contains(c) ==> self.get_container_owned_pages(c)
                    =~= old(self).get_container_owned_pages(c),
    {
        proof {
            page_ptr_lemma1();
            seq_skip_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_4k.wf_to_no_duplicates();
        }
        assert(page_ptr_valid(target_ptr));
        let old_ref_count = self.page_array.get(page_ptr2page_index(target_ptr)).ref_count;
        let old_io_mappings = self.page_array.get(page_ptr2page_index(target_ptr)).io_mappings;
        self.set_ref_count(page_ptr2page_index(target_ptr), old_ref_count + 1);
        self.set_io_mapping(page_ptr2page_index(target_ptr), Ghost(old_io_mappings@.insert((ioid, va))));

        assert(self.page_array_wf());
        assert(self.free_pages_4k_wf());
        assert(self.free_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.free_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.allocated_pages_4k_wf());
        assert(self.allocated_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.allocated_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.mapped_pages_4k_wf());
        assert(self.mapped_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.mapped_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.merged_pages_wf()) by {
            page_ptr_page_index_truncate_lemma();
        };
        assert(self.hugepages_wf()) by {
            page_index_lemma();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();

        };
    }

    fn remove_mapping_4k_helper1(&mut self, target_ptr: PagePtr, pcid: Pcid, va: VAddr)
        requires
            old(self).wf(),
            old(self).mapped_pages_4k().contains(target_ptr),
            old(self).page_mappings(target_ptr).contains((pcid, va)),
            old(self).page_array@[page_ptr2page_index(target_ptr) as int].is_io_page == true,
            old(self).page_array@[page_ptr2page_index(target_ptr) as int].ref_count == 1,
        ensures
            self.wf(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            forall|p: PagePtr|
                self.page_is_mapped(p) && p != target_ptr ==> self.page_mappings(p) =~= old(
                    self,
                ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            self.page_mappings(target_ptr) =~= old(self).page_mappings(target_ptr).remove(
                (pcid, va),
            ),
            self.page_io_mappings(target_ptr) =~= old(self).page_io_mappings(target_ptr),
            // self.container_map_4k@ =~= old(self).container_map_4k@,
            self.container_map_2m@ =~= old(self).container_map_2m@,
            self.container_map_1g@ =~= old(self).container_map_1g@,
            self.container_map_4k@ =~= old(self).container_map_4k@.insert(
                old(self).page_array@[page_ptr2page_index(
                    target_ptr,
                ) as int].owning_container.unwrap(),
                old(self).container_map_4k@[old(self).page_array@[page_ptr2page_index(
                    target_ptr,
                ) as int].owning_container.unwrap()].remove(target_ptr),
            ),
    {
        proof {
            page_ptr_lemma1();
            seq_push_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_4k.wf_to_no_duplicates();
        }
        assert(page_ptr_valid(target_ptr));
        let c_ptr = self.page_array.get(page_ptr2page_index(target_ptr)).owning_container.unwrap();
        self.set_ref_count(page_ptr2page_index(target_ptr), 0);
        self.set_mapping(page_ptr2page_index(target_ptr), Ghost(Set::empty()));
        self.set_state(page_ptr2page_index(target_ptr), PageState::Unavailable4k);
        self.set_owning_container(page_ptr2page_index(target_ptr), None);
        proof {
            self.mapped_pages_4k@ = self.mapped_pages_4k@.remove(target_ptr);
        }
        proof {
            self.container_map_4k@ = self.container_map_4k@.insert(
                c_ptr,
                self.container_map_4k@[c_ptr].remove(target_ptr),
            );
        }
        let tracked mut removed_perm = self.page_perms_4k.borrow_mut().tracked_remove(target_ptr);
        assert(self.page_array_wf());
        assert(self.free_pages_4k_wf());
        assert(self.free_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.free_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.allocated_pages_4k_wf());
        assert(self.allocated_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.allocated_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.mapped_pages_4k_wf());
        assert(self.mapped_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.mapped_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.merged_pages_wf()) by {
            page_ptr_page_index_truncate_lemma();
        };
        assert(self.hugepages_wf()) by {
            page_index_lemma();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();
        };
    }

    fn remove_mapping_4k_helper2(&mut self, target_ptr: PagePtr, pcid: Pcid, va: VAddr)
        requires
            old(self).wf(),
            old(self).mapped_pages_4k().contains(target_ptr),
            old(self).page_mappings(target_ptr).contains((pcid, va)),
            old(self).page_array@[page_ptr2page_index(target_ptr) as int].is_io_page == false,
            old(self).page_array@[page_ptr2page_index(target_ptr) as int].ref_count == 1,
        ensures
            self.wf(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            forall|p: PagePtr|
                self.page_is_mapped(p) && p != target_ptr ==> self.page_mappings(p) =~= old(
                    self,
                ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            self.page_mappings(target_ptr) =~= old(self).page_mappings(target_ptr).remove(
                (pcid, va),
            ),
            self.page_io_mappings(target_ptr) =~= old(self).page_io_mappings(target_ptr),
            // self.container_map_4k@ =~= old(self).container_map_4k@,
            self.container_map_2m@ =~= old(self).container_map_2m@,
            self.container_map_1g@ =~= old(self).container_map_1g@,
            self.container_map_4k@ =~= old(self).container_map_4k@.insert(
                old(self).page_array@[page_ptr2page_index(
                    target_ptr,
                ) as int].owning_container.unwrap(),
                old(self).container_map_4k@[old(self).page_array@[page_ptr2page_index(
                    target_ptr,
                ) as int].owning_container.unwrap()].remove(target_ptr),
            ),
    {
        proof {
            page_ptr_lemma1();
            seq_push_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_4k.wf_to_no_duplicates();
        }
        assert(page_ptr_valid(target_ptr));
        let c_ptr = self.page_array.get(page_ptr2page_index(target_ptr)).owning_container.unwrap();
        proof {
            self.free_pages_4k@.unique_seq_to_set();
            self.len_lemma_mapped_4k(target_ptr);
        }
        let rev_index = self.free_pages_4k.push(&target_ptr);
        self.set_rev_pointer(page_ptr2page_index(target_ptr), rev_index);
        self.set_ref_count(page_ptr2page_index(target_ptr), 0);
        self.set_mapping(page_ptr2page_index(target_ptr), Ghost(Set::empty()));
        self.set_state(page_ptr2page_index(target_ptr), PageState::Free4k);
        self.set_owning_container(page_ptr2page_index(target_ptr), None);
        proof {
            self.mapped_pages_4k@ = self.mapped_pages_4k@.remove(target_ptr);
        }
        proof {
            self.container_map_4k@ = self.container_map_4k@.insert(
                c_ptr,
                self.container_map_4k@[c_ptr].remove(target_ptr),
            );
        }
        assert(self.page_array_wf());
        assert(self.free_pages_4k_wf());
        assert(self.free_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.free_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.allocated_pages_4k_wf());
        assert(self.allocated_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.allocated_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.mapped_pages_4k_wf());
        assert(self.mapped_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.mapped_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.merged_pages_wf()) by {
            page_ptr_page_index_truncate_lemma();
        };
        assert(self.hugepages_wf()) by {
            page_index_lemma();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();

        };
    }

    fn remove_mapping_4k_helper3(&mut self, target_ptr: PagePtr, pcid: Pcid, va: VAddr)
        requires
            old(self).wf(),
            old(self).mapped_pages_4k().contains(target_ptr),
            old(self).page_mappings(target_ptr).contains((pcid, va)),
            old(self).page_array@[page_ptr2page_index(target_ptr) as int].ref_count != 1,
        ensures
            self.wf(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            forall|p: PagePtr|
                self.page_is_mapped(p) && p != target_ptr ==> self.page_mappings(p) =~= old(
                    self,
                ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            self.page_mappings(target_ptr) =~= old(self).page_mappings(target_ptr).remove(
                (pcid, va),
            ),
            self.page_io_mappings(target_ptr) =~= old(self).page_io_mappings(target_ptr),
            self.container_map_4k@ =~= old(self).container_map_4k@,
            self.container_map_2m@ =~= old(self).container_map_2m@,
            self.container_map_1g@ =~= old(self).container_map_1g@,
    {
        proof {
            page_ptr_lemma1();
            seq_push_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_4k.wf_to_no_duplicates();
        }
        proof {
            self.len_lemma_mapped_4k(target_ptr);
        }
        let old_ref_count = self.page_array.get(page_ptr2page_index(target_ptr)).ref_count;
        let old_mappings = self.page_array.get(page_ptr2page_index(target_ptr)).mappings;
        self.set_ref_count(page_ptr2page_index(target_ptr), old_ref_count - 1);
        self.set_mapping(page_ptr2page_index(target_ptr), Ghost(old_mappings@.remove((pcid, va))));
        assert(self.page_array_wf());
        assert(self.free_pages_4k_wf());
        assert(self.free_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.free_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.allocated_pages_4k_wf());
        assert(self.allocated_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.allocated_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.mapped_pages_4k_wf());
        assert(self.mapped_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.mapped_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.merged_pages_wf()) by {
            page_ptr_page_index_truncate_lemma();
        };
        assert(self.hugepages_wf()) by {
            page_index_lemma();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();
        };
    }

    pub fn remove_mapping_4k(&mut self, target_ptr: PagePtr, pcid: Pcid, va: VAddr) -> (ret: Option<
        ContainerPtr,
    >)
        requires
            old(self).wf(),
            old(self).mapped_pages_4k().contains(target_ptr),
            old(self).page_mappings(target_ptr).contains((pcid, va)),
        ensures
            self.wf(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            forall|p: PagePtr|
                self.page_is_mapped(p) && p != target_ptr ==> self.page_mappings(p) =~= old(
                    self,
                ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            self.page_mappings(target_ptr) =~= old(self).page_mappings(target_ptr).remove(
                (pcid, va),
            ),
            self.page_io_mappings(target_ptr) =~= old(self).page_io_mappings(target_ptr),
            // self.container_map_4k@ =~= old(self).container_map_4k@,
            self.container_map_2m@ =~= old(self).container_map_2m@,
            self.container_map_1g@ =~= old(self).container_map_1g@,
            ret.is_None() ==> self.container_map_4k@ =~= old(self).container_map_4k@,
            ret.is_Some() ==> self.container_map_4k@ =~= old(self).container_map_4k@.insert(
                ret.unwrap(),
                old(self).container_map_4k@[ret.unwrap()].remove(target_ptr),
            ),
    {
        proof {
            page_ptr_lemma1();
            seq_push_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_4k.wf_to_no_duplicates();
        }
        assert(page_ptr_valid(target_ptr));
        let c_ptr = self.page_array.get(page_ptr2page_index(target_ptr)).owning_container.unwrap();
        let old_ref_count = self.page_array.get(page_ptr2page_index(target_ptr)).ref_count;
        let is_io_page = self.page_array.get(page_ptr2page_index(target_ptr)).is_io_page;
        let old_mappings = self.page_array.get(page_ptr2page_index(target_ptr)).mappings;
        if old_ref_count == 1 && is_io_page {
            self.remove_mapping_4k_helper1(target_ptr, pcid, va);
            Some(c_ptr)
        } else if old_ref_count == 1 {
            self.remove_mapping_4k_helper2(target_ptr, pcid, va);
            Some(c_ptr)
        } else {
            self.remove_mapping_4k_helper3(target_ptr, pcid, va);
            None
        }
    }

    fn remove_io_mapping_4k_helper1(&mut self, target_ptr: PagePtr, ioid: IOid, va: VAddr)
        requires
            old(self).wf(),
            old(self).mapped_pages_4k().contains(target_ptr),
            old(self).page_io_mappings(target_ptr).contains((ioid, va)),
            old(self).page_array@[page_ptr2page_index(target_ptr) as int].is_io_page == true,
            old(self).page_array@[page_ptr2page_index(target_ptr) as int].ref_count == 1,
        ensures
            self.wf(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            forall|p: PagePtr|
                self.page_is_mapped(p) && p != target_ptr ==> self.page_mappings(p) =~= old(
                    self,
                ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            self.page_mappings(target_ptr) =~= old(self).page_mappings(target_ptr),
            self.page_io_mappings(target_ptr) =~= old(self).page_io_mappings(target_ptr).remove(
                (ioid, va),
            ),
            // self.container_map_4k@ =~= old(self).container_map_4k@,
            self.container_map_2m@ =~= old(self).container_map_2m@,
            self.container_map_1g@ =~= old(self).container_map_1g@,
            self.container_map_4k@ =~= old(self).container_map_4k@.insert(
                old(self).page_array@[page_ptr2page_index(
                    target_ptr,
                ) as int].owning_container.unwrap(),
                old(self).container_map_4k@[old(self).page_array@[page_ptr2page_index(
                    target_ptr,
                ) as int].owning_container.unwrap()].remove(target_ptr),
            ),
    {
        proof {
            page_ptr_lemma1();
            seq_push_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_4k.wf_to_no_duplicates();
        }
        assert(page_ptr_valid(target_ptr));
        let c_ptr = self.page_array.get(page_ptr2page_index(target_ptr)).owning_container.unwrap();
        self.set_ref_count(page_ptr2page_index(target_ptr), 0);
        self.set_io_mapping(page_ptr2page_index(target_ptr), Ghost(Set::empty()));
        self.set_state(page_ptr2page_index(target_ptr), PageState::Unavailable4k);
        self.set_owning_container(page_ptr2page_index(target_ptr), None);
        proof {
            self.mapped_pages_4k@ = self.mapped_pages_4k@.remove(target_ptr);
        }
        proof {
            self.container_map_4k@ = self.container_map_4k@.insert(
                c_ptr,
                self.container_map_4k@[c_ptr].remove(target_ptr),
            );
        }
        let tracked mut removed_perm = self.page_perms_4k.borrow_mut().tracked_remove(target_ptr);
        assert(self.page_array_wf());
        assert(self.free_pages_4k_wf());
        assert(self.free_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.free_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.allocated_pages_4k_wf());
        assert(self.allocated_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.allocated_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.mapped_pages_4k_wf());
        assert(self.mapped_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.mapped_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.merged_pages_wf()) by {
            page_ptr_page_index_truncate_lemma();
        };
        assert(self.hugepages_wf()) by {
            page_index_lemma();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();

        };
    }

    fn remove_io_mapping_4k_helper2(&mut self, target_ptr: PagePtr, ioid: IOid, va: VAddr)
        requires
            old(self).wf(),
            old(self).mapped_pages_4k().contains(target_ptr),
            old(self).page_io_mappings(target_ptr).contains((ioid, va)),
            old(self).page_array@[page_ptr2page_index(target_ptr) as int].is_io_page == false,
            old(self).page_array@[page_ptr2page_index(target_ptr) as int].ref_count == 1,
        ensures
            self.wf(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            forall|p: PagePtr|
                self.page_is_mapped(p) && p != target_ptr ==> self.page_mappings(p) =~= old(
                    self,
                ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            self.page_mappings(target_ptr) =~= old(self).page_mappings(target_ptr),
            self.page_io_mappings(target_ptr) =~= old(self).page_io_mappings(target_ptr).remove(
                (ioid, va),
            ),
            // self.container_map_4k@ =~= old(self).container_map_4k@,
            self.container_map_2m@ =~= old(self).container_map_2m@,
            self.container_map_1g@ =~= old(self).container_map_1g@,
            self.container_map_4k@ =~= old(self).container_map_4k@.insert(
                old(self).page_array@[page_ptr2page_index(
                    target_ptr,
                ) as int].owning_container.unwrap(),
                old(self).container_map_4k@[old(self).page_array@[page_ptr2page_index(
                    target_ptr,
                ) as int].owning_container.unwrap()].remove(target_ptr),
            ),
    {
        proof {
            page_ptr_lemma1();
            seq_push_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_4k.wf_to_no_duplicates();
        }
        assert(page_ptr_valid(target_ptr));
        proof {
            self.free_pages_4k@.unique_seq_to_set();
            self.len_lemma_mapped_4k(target_ptr);
        }

        let c_ptr = self.page_array.get(page_ptr2page_index(target_ptr)).owning_container.unwrap();
        let rev_index = self.free_pages_4k.push(&target_ptr);
        self.set_rev_pointer(page_ptr2page_index(target_ptr), rev_index);
        self.set_ref_count(page_ptr2page_index(target_ptr), 0);
        self.set_io_mapping(page_ptr2page_index(target_ptr), Ghost(Set::empty()));
        self.set_state(page_ptr2page_index(target_ptr), PageState::Free4k);
        self.set_owning_container(page_ptr2page_index(target_ptr), None);
        proof {
            self.mapped_pages_4k@ = self.mapped_pages_4k@.remove(target_ptr);
        }
        proof {
            self.container_map_4k@ = self.container_map_4k@.insert(
                c_ptr,
                self.container_map_4k@[c_ptr].remove(target_ptr),
            );
        }
        assert(self.page_array_wf());
        assert(self.free_pages_4k_wf());
        assert(self.free_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.free_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.allocated_pages_4k_wf());
        assert(self.allocated_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.allocated_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.mapped_pages_4k_wf());
        assert(self.mapped_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.mapped_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.merged_pages_wf()) by {
            page_ptr_page_index_truncate_lemma();
        };
        assert(self.hugepages_wf()) by {
            page_index_lemma();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();

        };
    }

    fn remove_io_mapping_4k_helper3(&mut self, target_ptr: PagePtr, ioid: IOid, va: VAddr)
        requires
            old(self).wf(),
            old(self).mapped_pages_4k().contains(target_ptr),
            old(self).page_io_mappings(target_ptr).contains((ioid, va)),
            old(self).page_array@[page_ptr2page_index(target_ptr) as int].ref_count != 1,
        ensures
            self.wf(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            forall|p: PagePtr|
                self.page_is_mapped(p) && p != target_ptr ==> self.page_mappings(p) =~= old(
                    self,
                ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            self.page_mappings(target_ptr) =~= old(self).page_mappings(target_ptr),
            self.page_io_mappings(target_ptr) =~= old(self).page_io_mappings(target_ptr).remove(
                (ioid, va),
            ),
            self.container_map_4k@ =~= old(self).container_map_4k@,
            self.container_map_2m@ =~= old(self).container_map_2m@,
            self.container_map_1g@ =~= old(self).container_map_1g@,
    {
        proof {
            page_ptr_lemma1();
            seq_push_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_4k.wf_to_no_duplicates();
        }
        proof {
            self.len_lemma_mapped_4k(target_ptr);
        }
        let old_ref_count = self.page_array.get(page_ptr2page_index(target_ptr)).ref_count;
        let old_io_mappings = self.page_array.get(page_ptr2page_index(target_ptr)).io_mappings;
        self.set_ref_count(page_ptr2page_index(target_ptr), old_ref_count - 1);
        self.set_io_mapping(
            page_ptr2page_index(target_ptr),
            Ghost(old_io_mappings@.remove((ioid, va))),
        );
        assert(self.page_array_wf());
        assert(self.free_pages_4k_wf());
        assert(self.free_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.free_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.allocated_pages_4k_wf());
        assert(self.allocated_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.allocated_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.mapped_pages_4k_wf());
        assert(self.mapped_pages_2m_wf()) by {
            page_ptr_2m_lemma();
        };
        assert(self.mapped_pages_1g_wf()) by {
            page_ptr_1g_lemma();
        };
        assert(self.merged_pages_wf()) by {
            page_ptr_page_index_truncate_lemma();
        };
        assert(self.hugepages_wf()) by {
            page_index_lemma();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();

        };
    }

    pub fn remove_io_mapping_4k(&mut self, target_ptr: PagePtr, ioid: IOid, va: VAddr) -> (ret:
        Option<ContainerPtr>)
        requires
            old(self).wf(),
            old(self).mapped_pages_4k().contains(target_ptr),
            old(self).page_io_mappings(target_ptr).contains((ioid, va)),
        ensures
            self.wf(),
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            forall|p: PagePtr|
                self.page_is_mapped(p) && p != target_ptr ==> self.page_mappings(p) =~= old(
                    self,
                ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            self.page_mappings(target_ptr) =~= old(self).page_mappings(target_ptr),
            self.page_io_mappings(target_ptr) =~= old(self).page_io_mappings(target_ptr).remove(
                (ioid, va),
            ),
            // self.container_map_4k@ =~= old(self).container_map_4k@,
            self.container_map_2m@ =~= old(self).container_map_2m@,
            self.container_map_1g@ =~= old(self).container_map_1g@,
            ret.is_None() ==> self.container_map_4k@ =~= old(self).container_map_4k@,
            ret.is_Some() ==> self.container_map_4k@ =~= old(self).container_map_4k@.insert(
                ret.unwrap(),
                old(self).container_map_4k@[ret.unwrap()].remove(target_ptr),
            ),
    {
        proof {
            page_ptr_lemma1();
            seq_push_lemma::<PagePtr>();
            self.free_pages_1g.wf_to_no_duplicates();
            self.free_pages_2m.wf_to_no_duplicates();
            self.free_pages_4k.wf_to_no_duplicates();
        }
        assert(page_ptr_valid(target_ptr));
        let c_ptr = self.page_array.get(page_ptr2page_index(target_ptr)).owning_container.unwrap();
        let old_ref_count = self.page_array.get(page_ptr2page_index(target_ptr)).ref_count;
        let is_io_page = self.page_array.get(page_ptr2page_index(target_ptr)).is_io_page;
        let old_io_mappings = self.page_array.get(page_ptr2page_index(target_ptr)).io_mappings;
        if old_ref_count == 1 && is_io_page {
            self.remove_io_mapping_4k_helper1(target_ptr, ioid, va);
            Some(c_ptr)
        } else if old_ref_count == 1 {
            self.remove_io_mapping_4k_helper2(target_ptr, ioid, va);
            Some(c_ptr)
        } else {
            self.remove_io_mapping_4k_helper3(target_ptr, ioid, va);
            None
        }
    }

    pub fn merged_4k_to_2m(&mut self, target_ptr: PagePtr, target_page_idx: usize)
        requires
            old(self).wf(),
            target_page_idx + 512 <= NUM_PAGES,
            forall|i:int|
                #![trigger old(self).page_array[i]]
                target_page_idx<=i<target_page_idx + 512 
                ==> 
                old(self).page_array[i].state == PageState::Free4k
                &&
                old(self).page_array[i].is_io_page == false,
            old(self).free_pages_2m().len() < NUM_PAGES,
            page_ptr_2m_valid(page_index2page_ptr(target_page_idx)),
            old(self).free_pages_4k().len() >= 512,
        ensures
            self.wf(),
            forall|p: PagePtr|
                self.page_is_mapped(p) ==> self.page_mappings(p) =~= old(
                    self,
                ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            self.container_map_2m@ =~= old(self).container_map_2m@,
            self.container_map_1g@ =~= old(self).container_map_1g@,
            self.container_map_4k@ =~= old(self).container_map_4k@,
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            self.free_pages_4k().len() == old(self).free_pages_4k().len() - 512,
            self.free_pages_2m().len() == old(self).free_pages_2m().len() + 1,
            self.free_pages_1g().len() == old(self).free_pages_1g().len(),
    {
        proof{
            page_ptr_lemma1();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();
            page_index_lemma();
            page_ptr_page_index_truncate_lemma();
        }
        assert(old(self).page_array[target_page_idx + 0].state == PageState::Free4k);
        assert(self.free_pages_4k@.contains(page_index2page_ptr(target_page_idx)));
        let mut merged_4k_page_perms = Tracked(Map::<usize, PagePerm4k>::tracked_empty());
        for index in 0..512
            invariant
                self.free_pages_2m().len() < NUM_PAGES,
                self.free_pages_2m@.contains(page_index2page_ptr(target_page_idx)) == false,
                forall|i:usize|
                    #![auto]
                    0<=i<index 
                    ==>
                    merged_4k_page_perms@.dom().contains(i)
                    &&
                    merged_4k_page_perms@[i].is_init()
                    &&
                    merged_4k_page_perms@[i].addr() == page_index2page_ptr((target_page_idx + i) as usize),
                target_page_idx + 512 <= NUM_PAGES,
                0<=index<=512,
                forall|i:int| 
                    #![trigger self.page_array[i].state]
                    target_page_idx + index<=i<512 + target_page_idx
                    ==> 
                    self.page_array[i].state == PageState::Free4k
                    &&
                    self.page_array[i].is_io_page == false,
                forall|i:int| 
                    #![trigger self.page_array[i]]
                    target_page_idx<=i<index+target_page_idx
                    ==> 
                    self.page_array[i].state == PageState::Merged2m
                    &&
                    self.page_array[i].is_io_page == false,
                self.page_array_wf(),
                self.free_pages_4k_wf(),
                self.free_pages_2m_wf(),
                self.free_pages_1g_wf(),
                self.allocated_pages_4k_wf(),
                self.allocated_pages_2m_wf(),
                self.allocated_pages_1g_wf(),
                self.mapped_pages_4k_wf(),
                self.mapped_pages_2m_wf(),
                self.mapped_pages_1g_wf(),
                // self.merged_pages_wf(),
                self.perm_wf(),
                self.container_wf(),
                self.mapped_pages_have_reference_counter(),
                self.hugepages_wf(),

                forall|i: usize|
                    #![trigger page_index_2m_valid(i)]
                    #![trigger spec_page_index_truncate_2m(i)]
                    0 <= i < NUM_PAGES && self.page_array@[i as int].state == PageState::Merged2m && !(target_page_idx<=i<512+target_page_idx)
                    ==> 
                    page_index_2m_valid(i) == false && 
                        ( self.page_array@[spec_page_index_truncate_2m(i) as int].state == PageState::Mapped2m
                        || self.page_array@[spec_page_index_truncate_2m(i) as int].state
                        == PageState::Free2m || self.page_array@[spec_page_index_truncate_2m(i) as int].state == PageState::Allocated2m
                        || self.page_array@[spec_page_index_truncate_2m(i) as int].state
                        == PageState::Unavailable2m) 
                        && self.page_array@[i as int].is_io_page == self.page_array@[spec_page_index_truncate_2m(i) as int].is_io_page,
                forall|i: usize|
                    #![trigger page_index_1g_valid(i)]
                    #![trigger spec_page_index_truncate_1g(i)]
                    0 <= i < NUM_PAGES && self.page_array@[i as int].state == PageState::Merged1g
                    ==> 
                    page_index_1g_valid(i) == false 
                    && (self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Mapped1g
                        || self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Free1g 
                        || self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Allocated1g
                        || self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Unavailable1g
                    ) 
                    && self.page_array@[i as int].is_io_page == self.page_array@[spec_page_index_truncate_1g(i) as int].is_io_page,

                self.free_pages_4k().len() == old(self).free_pages_4k().len() - index,
                self.free_pages_2m().len() == old(self).free_pages_2m().len(),
                self.free_pages_1g().len() == old(self).free_pages_1g().len(),
                self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
                self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
                self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
                forall|p: PagePtr|
                    self.page_is_mapped(p) ==> self.page_mappings(p) =~= old(
                        self,
                    ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
                self.container_map_2m@ =~= old(self).container_map_2m@,
                self.container_map_1g@ =~= old(self).container_map_1g@,
                self.container_map_4k@ =~= old(self).container_map_4k@,
        {
            proof{
                seq_remove_lemma::<PagePtr>();
                seq_remove_lemma_2::<PagePtr>();
                self.free_pages_4k.unique_implys_no_duplicates();
                seq_update_lemma::<Page>();
                page_ptr_lemma1();
                page_ptr_2m_lemma();
                page_ptr_1g_lemma();
                page_index_lemma();
                page_ptr_page_index_truncate_lemma();
                assert(self.free_pages_4k@.len() == old(self).free_pages_4k().len() - index) by {self.free_pages_4k@.unique_seq_to_set();}
            }
            let node_ref = self.page_array.get(target_page_idx + index).rev_pointer;
            let page_index = target_page_idx + index;
            assert(self.page_array@[target_page_idx + index].state == PageState::Free4k);
            assert(self.allocated_pages_4k@.contains(page_index2page_ptr(page_index)) == false);
            assert(self.allocated_pages_2m@.contains(page_index2page_ptr(page_index)) == false);
            assert(self.allocated_pages_1g@.contains(page_index2page_ptr(page_index)) == false);
            self.free_pages_4k.remove(node_ref, Ghost(page_index2page_ptr(page_index)));
            assert(self.free_pages_4k().len() == old(self).free_pages_4k().len() - index - 1) by {
                self.free_pages_4k.unique_implys_no_duplicates();
                self.free_pages_4k@.unique_seq_to_set();
            }
            self.page_array.set(target_page_idx + index, 
                Page {
                        addr: page_index2page_ptr(target_page_idx + index),
                        state: PageState::Merged2m,
                        is_io_page: false,
                        rev_pointer: 0,
                        ref_count: 0,
                        owning_container: None,
                        mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                        io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                        });
            let tracked page_perm = self.page_perms_4k.borrow_mut().tracked_remove(page_index2page_ptr(page_index));
            proof{
                assert(page_perm.is_init());
                assert(page_perm.addr() == page_index2page_ptr(page_index));
                let old = merged_4k_page_perms@;
                merged_4k_page_perms.borrow_mut().tracked_insert(index, page_perm);
                // assert(merged_4k_page_perms@.dom().contains(page_index2page_ptr(page_index)));
                assert((target_page_idx + index) as usize == page_index);
                assert(page_index2page_ptr((target_page_idx + index) as usize) == page_index2page_ptr(page_index));
                assert(merged_4k_page_perms@.dom() =~= old.dom().insert(index));
            }
        }

        proof{
            seq_update_lemma::<Page>();
            page_ptr_lemma1();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();
            page_index_lemma();
            page_ptr_page_index_truncate_lemma();
        }
        let page_perm_2m = merge_4k_pages_to_2m_page(target_page_idx, merged_4k_page_perms);
        proof{
            self.page_perms_2m.borrow_mut().tracked_insert(page_index2page_ptr(target_page_idx), page_perm_2m.get());
            assert(self.free_pages_2m.len() < NUM_PAGES && self.free_pages_2m().len() == self.free_pages_2m@.len()) by {
                self.free_pages_2m.unique_implys_no_duplicates();
                self.free_pages_2m@.unique_seq_to_set();};
        }
        let node_ref = self.free_pages_2m.push(&page_index2page_ptr(target_page_idx));
        self.page_array.set(target_page_idx, 
            Page {
                    addr: page_index2page_ptr(target_page_idx),
                    state: PageState::Free2m,
                    is_io_page: false,
                    rev_pointer: node_ref,
                    ref_count: 0,
                    owning_container: None,
                    mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                    io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                    });
        proof{
            seq_push_unique_lemma::<PagePtr>();
            seq_push_lemma::<PagePtr>();
            assert(self.free_pages_2m().len() == old(self).free_pages_2m().len() + 1) by {
                self.free_pages_2m.unique_implys_no_duplicates();
                self.free_pages_2m@.unique_seq_to_set();
            }
        }
        
        assert(self.page_array_wf());
        assert(self.free_pages_4k_wf());
        assert(self.free_pages_2m_wf()) by {
            assert(self.free_pages_2m.wf());
            assert( self.free_pages_2m.unique());
            assert( forall|i: int|
            #![trigger self.free_pages_2m@.contains(self.page_array@[i].addr)]
            #![trigger self.page_array@[i].is_io_page]
            #![trigger self.page_array@[i].rev_pointer]
            0 <= i < NUM_PAGES && self.page_array@[i].state == PageState::Free2m
                ==> self.free_pages_2m@.contains(self.page_array@[i].addr)
                && self.free_pages_2m.get_node_ref(self.page_array@[i].addr ) == 
                    self.page_array@[i].rev_pointer
                && self.page_array@[i].is_io_page == false);
        assert( forall|page_ptr: PagePtr|
            #![trigger page_ptr_2m_valid(page_ptr)]
            #![trigger self.page_array@[page_ptr2page_index(page_ptr) as int].state]
            self.free_pages_2m@.contains(page_ptr) ==> page_ptr_2m_valid(page_ptr)
                && self.page_array@[page_ptr2page_index(page_ptr) as int].state
                == PageState::Free2m);
        };
        assert(self.free_pages_1g_wf());
        assert(self.allocated_pages_4k_wf());
        assert(self.allocated_pages_2m_wf());
        assert( self.allocated_pages_1g_wf());
        assert(self.mapped_pages_4k_wf());
        assert(self.mapped_pages_2m_wf());
        assert(self.mapped_pages_1g_wf());
        assert(self.merged_pages_wf());
        assert(self.perm_wf());
        assert( self.container_wf());
        assert(self.mapped_pages_have_reference_counter());
        assert(self.hugepages_wf());

    }

    pub fn split_2m_to_4k(&mut self, target_page_idx: usize)
        requires
            old(self).wf(),
            0 <= target_page_idx < NUM_PAGES - 512,
            page_index_2m_valid(target_page_idx),
            old(self).free_pages_4k().len() < NUM_PAGES - 512,
            old(self).page_array[target_page_idx as int].state == PageState::Free2m,
            old(self).page_array[target_page_idx as int].is_io_page == false,
        ensures
            self.wf(),
            forall|p: PagePtr|
                self.page_is_mapped(p) ==> self.page_mappings(p) =~= old(
                    self,
                ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
            self.container_map_2m@ =~= old(self).container_map_2m@,
            self.container_map_1g@ =~= old(self).container_map_1g@,
            self.container_map_4k@ =~= old(self).container_map_4k@,
            self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
            self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
            self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
            self.free_pages_4k().len() == old(self).free_pages_4k().len() + 512,
            self.free_pages_2m().len() == old(self).free_pages_2m().len() - 1,
            self.free_pages_1g().len() == old(self).free_pages_1g().len(),
    {
        proof{
            page_ptr_lemma1();
            page_ptr_2m_lemma();
            page_ptr_1g_lemma();
            page_index_lemma();
            page_ptr_page_index_truncate_lemma();
            seq_push_lemma::<PagePtr>();
            seq_remove_lemma::<PagePtr>();
            seq_remove_lemma_2::<PagePtr>();
            self.free_pages_4k.unique_implys_no_duplicates();
            self.free_pages_2m.unique_implys_no_duplicates();
            assert(self.free_pages_4k@.len() == self.free_pages_4k().len()) by {self.free_pages_4k@.unique_seq_to_set();}
            assert(self.free_pages_2m@.len() == self.free_pages_2m().len()) by {self.free_pages_2m@.unique_seq_to_set();}
        }

        assert(forall|i:usize| 
                    #![trigger self.page_array[i as int].state]
                    #![trigger spec_page_index_merge_2m_vaild(target_page_idx, i)]
                    target_page_idx<i<512+target_page_idx
                    ==> 
                    spec_page_index_merge_2m_vaild(target_page_idx, i)
                    // &&
                    // self.page_array@[i as int].state == PageState::Merged2m && self.page_array@[target_page_idx as int].is_io_page == self.page_array@[i as int].is_io_page
                );

        let tracked page_perm_2m = self.page_perms_2m.borrow_mut().tracked_remove(page_index2page_ptr(target_page_idx));
        let mut pages_perms = split_2m_pages_to_pages(target_page_idx, Tracked(page_perm_2m));
        let node_ref = self.page_array.get(target_page_idx).rev_pointer;
        self.free_pages_2m.remove(node_ref, Ghost(page_index2page_ptr(target_page_idx)));
        let node_ref = self.free_pages_4k.push(&page_index2page_ptr(target_page_idx));
        self.page_array.set(target_page_idx, 
                Page {
                        addr: page_index2page_ptr(target_page_idx),
                        state: PageState::Free4k,
                        is_io_page: false,
                        rev_pointer: node_ref,
                        ref_count: 0,
                        owning_container: None,
                        mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                        io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                        });
        assert(
            forall|i:usize|
                #![trigger pages_perms@.dom().contains(i)]
                #![trigger pages_perms@[i]]
                target_page_idx<=i<512 + target_page_idx 
                ==>
                pages_perms@.dom().contains(i)
                &&
                pages_perms@[i].is_init()
                &&
                pages_perms@[i].addr() == page_index2page_ptr(i)
        );
        
        let tracked page_perm_4k = pages_perms.borrow_mut().tracked_remove(target_page_idx);
        proof {self.page_perms_4k.borrow_mut().tracked_insert(page_index2page_ptr(target_page_idx), page_perm_4k);}
        assert(self.free_pages_1g_wf());
        assert(self.allocated_pages_4k_wf());
        assert(self.allocated_pages_2m_wf());
        assert( self.allocated_pages_1g_wf());
        assert(self.mapped_pages_4k_wf());
        assert(self.mapped_pages_2m_wf());
        assert(self.mapped_pages_1g_wf());
        // assert(self.merged_pages_wf());
        assert(self.perm_wf());


        assert(forall|i: usize|
            #![trigger page_index_2m_valid(i)]
            #![trigger spec_page_index_truncate_2m(i)]
            0 <= i < NUM_PAGES && self.page_array@[i as int].state == PageState::Merged2m && (target_page_idx <= i < target_page_idx + 512) == false
            ==> 
            page_index_2m_valid(i) == false 
            && ( self.page_array@[spec_page_index_truncate_2m(i) as int].state == PageState::Mapped2m
                || self.page_array@[spec_page_index_truncate_2m(i) as int].state == PageState::Free2m 
                || self.page_array@[spec_page_index_truncate_2m(i) as int].state == PageState::Allocated2m
                || self.page_array@[spec_page_index_truncate_2m(i) as int].state== PageState::Unavailable2m
            ) 
            && self.page_array@[i as int].is_io_page == self.page_array@[spec_page_index_truncate_2m(i) as int].is_io_page);
        assert( forall|i: usize|
            #![trigger page_index_1g_valid(i)]
            #![trigger spec_page_index_truncate_1g(i)]
            0 <= i < NUM_PAGES && self.page_array@[i as int].state == PageState::Merged1g
            ==> 
            page_index_1g_valid(i) == false 
            && (self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Mapped1g
                || self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Free1g 
                || self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Allocated1g
                || self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Unavailable1g
            ) 
            && self.page_array@[i as int].is_io_page == self.page_array@[spec_page_index_truncate_1g(i) as int].is_io_page);

        proof{
            self.free_pages_4k.unique_implys_no_duplicates();
            self.free_pages_2m.unique_implys_no_duplicates();
            assert(self.free_pages_4k@.len() == self.free_pages_4k().len()) by {self.free_pages_4k@.unique_seq_to_set();}
            assert(self.free_pages_2m@.len() == self.free_pages_2m().len()) by {self.free_pages_2m@.unique_seq_to_set();}
        }
        for index in 1..512
            invariant
                self.free_pages_4k().len() < NUM_PAGES - 512 + index,
                forall|i:usize|
                    #![trigger pages_perms@.dom().contains(i)]
                    #![trigger pages_perms@[i]]
                    target_page_idx + index <= i< target_page_idx + 512 
                    ==>
                    pages_perms@.dom().contains(i)
                    &&
                    pages_perms@[i].is_init()
                    &&
                    pages_perms@[i].addr() == page_index2page_ptr(i)
                    ,
                target_page_idx + 512 <= NUM_PAGES,
                1<=index<=512,
                forall|i:int| 
                    #![trigger self.page_array[i].state]
                    target_page_idx <=i<index + target_page_idx
                    ==> 
                    self.page_array[i].state == PageState::Free4k
                    &&
                    self.page_array[i].is_io_page == false,
                self.page_array[target_page_idx as int].state == PageState::Free4k,
                self.page_array[target_page_idx as int].is_io_page == false,
                forall|i:usize| 
                    #![trigger self.page_array[i as int]]
                    index+target_page_idx<=i<512+target_page_idx
                    ==> 
                    self.page_array[i as int].state == PageState::Merged2m
                    &&
                    self.page_array[i as int].is_io_page == false
                    &&
                    self.free_pages_4k().contains(page_index2page_ptr(i)) == false,
                self.page_array_wf(),
                self.free_pages_4k_wf(),
                self.free_pages_2m_wf(),
                self.free_pages_1g_wf(),
                self.allocated_pages_4k_wf(),
                self.allocated_pages_2m_wf(),
                self.allocated_pages_1g_wf(),
                self.mapped_pages_4k_wf(),
                self.mapped_pages_2m_wf(),
                self.mapped_pages_1g_wf(),
                // // self.merged_pages_wf(),
                self.perm_wf(),
                self.container_wf(),
                self.mapped_pages_have_reference_counter(),
                self.hugepages_wf(),

                forall|i: usize|
                #![trigger page_index_2m_valid(i)]
                #![trigger spec_page_index_truncate_2m(i)]
                0 <= i < NUM_PAGES && self.page_array@[i as int].state == PageState::Merged2m && (target_page_idx <= i < target_page_idx + 512) == false
                ==> 
                page_index_2m_valid(i) == false 
                && ( self.page_array@[spec_page_index_truncate_2m(i) as int].state == PageState::Mapped2m
                    || self.page_array@[spec_page_index_truncate_2m(i) as int].state == PageState::Free2m 
                    || self.page_array@[spec_page_index_truncate_2m(i) as int].state == PageState::Allocated2m
                    || self.page_array@[spec_page_index_truncate_2m(i) as int].state== PageState::Unavailable2m
                ) 
                && self.page_array@[i as int].is_io_page == self.page_array@[spec_page_index_truncate_2m(i) as int].is_io_page,
                forall|i: usize|
                #![trigger page_index_1g_valid(i)]
                #![trigger spec_page_index_truncate_1g(i)]
                0 <= i < NUM_PAGES && self.page_array@[i as int].state == PageState::Merged1g
                ==> 
                page_index_1g_valid(i) == false 
                && (self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Mapped1g
                    || self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Free1g 
                    || self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Allocated1g
                    || self.page_array@[spec_page_index_truncate_1g(i) as int].state == PageState::Unavailable1g
                ) 
                && self.page_array@[i as int].is_io_page == self.page_array@[spec_page_index_truncate_1g(i) as int].is_io_page,

                self.free_pages_4k().len() == old(self).free_pages_4k().len() + index,
                self.free_pages_2m().len() == old(self).free_pages_2m().len() - 1,
                self.free_pages_1g().len() == old(self).free_pages_1g().len(),
                self.allocated_pages_4k() =~= old(self).allocated_pages_4k(),
                self.allocated_pages_2m() =~= old(self).allocated_pages_2m(),
                self.allocated_pages_1g() =~= old(self).allocated_pages_1g(),
                forall|p: PagePtr|
                    self.page_is_mapped(p) ==> self.page_mappings(p) =~= old(
                        self,
                    ).page_mappings(p) && self.page_io_mappings(p) =~= old(self).page_io_mappings(p),
                self.container_map_2m@ =~= old(self).container_map_2m@,
                self.container_map_1g@ =~= old(self).container_map_1g@,
                self.container_map_4k@ =~= old(self).container_map_4k@,
        {
            proof{
                seq_push_lemma::<PagePtr>();
                self.free_pages_4k.unique_implys_no_duplicates();
                seq_update_lemma::<Page>();
                page_ptr_lemma1();
                page_ptr_2m_lemma();
                page_ptr_1g_lemma();
                page_index_lemma();
                page_ptr_page_index_truncate_lemma();
                assert(self.free_pages_4k@.len() == self.free_pages_4k().len()) by {self.free_pages_4k@.unique_seq_to_set();}
            }
            let page_ptr = page_index2page_ptr(target_page_idx + index);
            let page_index = target_page_idx + index;
            let node_ref = self.free_pages_4k.push(&page_ptr);
            self.page_array.set(target_page_idx + index, 
                Page {
                        addr: page_index2page_ptr(target_page_idx + index),
                        state: PageState::Free4k,
                        is_io_page: false,
                        rev_pointer: node_ref,
                        ref_count: 0,
                        owning_container: None,
                        mappings: Ghost(Set::<(Pcid, VAddr)>::empty()),
                        io_mappings: Ghost(Set::<(IOid, VAddr)>::empty()),
                        });
            let tracked page_perm_4k = pages_perms.borrow_mut().tracked_remove(page_index);
            proof {self.page_perms_4k.borrow_mut().tracked_insert(page_ptr, page_perm_4k);}
            proof{
                self.free_pages_4k.unique_implys_no_duplicates();
                assert(self.free_pages_4k@.len() == self.free_pages_4k().len()) by {self.free_pages_4k@.unique_seq_to_set();}
            }

            assume( forall|i: usize, j:usize|
                #![trigger spec_page_index_merge_2m_vaild(i,j)]
                0 <= i < NUM_PAGES && page_index_2m_valid(i) 
                && spec_page_index_merge_2m_vaild(i, j) 
                ==> 
                (target_page_idx <= j < target_page_idx + 512) == (i == target_page_idx)
            );

        }
        assert(self.merged_pages_wf());

    }
}

} // verus!
