use vstd::prelude::*;
verus! {

// use crate::array_vec::*;
use crate::proc::*;
use crate::page_alloc::*;
use crate::mmu::*;
use crate::cpu::*;
use crate::mars_array::MarsArray;
use crate::pagetable::*;
use crate::define::*;
// use vstd::ptr::*;
// use crate::trap::Registers;
// use crate::iommutable::*;

// use core::mem::MaybeUninit;

#[cfg(verus_keep_ghost)]
use vstd::set_lib::lemma_set_properties;

pub struct Kernel{
    pub proc_man : ProcessManager,
    pub page_alloc: PageAllocator,
    pub mmu_man: MMUManager,
    pub cpu_list: MarsArray<Cpu,NUM_CPUS>,
    pub cpu_stacks: CPUStackList,

    pub kernel_pml4_entry: PageEntry,
}
// ALL the sub-felids the kernel is concerned with are
// proc_man: get_pcid_closure(), get_ioid_closure(), get_proc_ptrs(), get_thread_ptrs(), get_thread(x).state, get_proc_man_page_closure()
// page_alloc: get_page_mappings(), get_page_io_mappings(), get_page_table_pages(), get_allocated_pages(),
// mmu_man: get_pagetable_mapping_by_pcid(), get_iommutable_mapping_by_ioid(), get_free_ioids_as_set(), get_free_pcids_as_set(),
// cpu_list:
impl Kernel{

    #[verifier(inline)]
    pub open spec fn kernel_mmu_page_alloc_pagetable_wf(&self) -> bool{
        &&&
        (
            forall|pcid:Pcid, va:usize| #![auto] (0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some()) ==>
            (
                self.page_alloc.get_page_mappings(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0().addr).contains((pcid,va))
            )
        )
        &&&
        (
            forall|pa:PAddr, pcid:Pcid, va:usize| #![auto]  self.page_alloc.get_available_pages().contains(pa) && self.page_alloc.get_page_mappings(pa).contains((pcid,va)) ==>
                (0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some() &&  self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0().addr == pa)
        )
    }
    #[verifier(inline)]
    pub open spec fn kernel_mmu_page_alloc_iommutable_wf(&self) -> bool{
        &&&
        (
            forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) && self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].is_Some() ==>
            (
                self.page_alloc.get_page_io_mappings(self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].get_Some_0().addr).contains((ioid,va))
            )
        )
        &&&
        (
            forall|pa:PAddr, ioid:IOid, va:usize| #![auto]  self.page_alloc.get_available_pages().contains(pa) && self.page_alloc.get_page_io_mappings(pa).contains((ioid,va)) ==>
                (0<=ioid<IOID_MAX && spec_va_valid(va) && self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].is_Some() &&  self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].get_Some_0().addr == pa)
        )
    }
    #[verifier(inline)]
    pub open spec fn kernel_proc_mmu_wf(&self) -> bool{
        &&&
        (forall|pcid:Pcid|#![auto] self.proc_man.get_pcid_closure().contains(pcid) ==>
            (0 <= pcid< PCID_MAX && self.mmu_man.get_free_pcids_as_set().contains(pcid) == false))
        &&&
        (forall|pcid:Pcid|#![auto] self.mmu_man.get_free_pcids_as_set().contains(pcid) ==>
            (self.proc_man.get_pcid_closure().contains(pcid) == false))
        &&&
        (forall|ioid:Pcid|#![auto] self.proc_man.get_ioid_closure().contains(ioid) ==>
            (0 <= ioid< IOID_MAX && self.mmu_man.get_free_ioids_as_set().contains(ioid) == false))
        &&&
        (forall|ioid:Pcid|#![auto] self.mmu_man.get_free_ioids_as_set().contains(ioid) ==>
            (self.proc_man.get_ioid_closure().contains(ioid) == false))
    }
    #[verifier(inline)]
    pub open spec fn kernel_proc_no_thread_in_transit(&self) -> bool{
        &&&
        (forall|thread_ptr:ThreadPtr|#![auto] self.proc_man.get_thread_ptrs().contains(thread_ptr) ==>
            self.proc_man.get_thread(thread_ptr).state != TRANSIT)
    }
    #[verifier(inline)]
    pub open spec fn kernel_mem_layout_wf(&self) -> bool {
        // all pages used to construct pagetable/iommutables are marked correctly in page allocator
        &&&
        (self.page_alloc.get_page_table_pages() =~= self.mmu_man.get_mmu_page_closure())
        &&&
        (self.page_alloc.get_allocated_pages() =~= self.proc_man.get_proc_man_page_closure())
    }
    #[verifier(inline)]
    pub open spec fn kernel_cpu_list_wf(&self) -> bool {
        &&&
        (
            forall|cpu_id:CPUID| #![auto] 0 <= cpu_id < NUM_CPUS
                ==> (
                    self.cpu_list[cpu_id as int].wf()
                    )
        )
        &&&
        (
            forall|cpu_id:CPUID| #![auto] 0 <= cpu_id < NUM_CPUS && self.cpu_list[cpu_id as int].get_is_idle() == false
                ==> (
                    self.proc_man.get_thread_ptrs().contains(self.cpu_list[cpu_id as int].get_current_thread().unwrap())
                    &&
                    self.proc_man.get_thread(self.cpu_list[cpu_id as int].get_current_thread().unwrap()).state == RUNNING
                    )
        )
        &&&
        (
            forall|cpu_id_i:CPUID,cpu_id_j:CPUID| #![auto] 0 <= cpu_id_i < NUM_CPUS && 0 <= cpu_id_j < NUM_CPUS  && cpu_id_i != cpu_id_j
                && self.cpu_list[cpu_id_i as int].get_is_idle() == false && self.cpu_list[cpu_id_j as int].get_is_idle() == false
                ==> (
                    self.cpu_list[cpu_id_i as int].get_current_thread().unwrap() !=
                    self.cpu_list[cpu_id_j as int].get_current_thread().unwrap()
                    )
        )
    }
    #[verifier(inline)]
    pub open spec fn kernel_tlb_wf(&self) -> bool {
        &&&
        (
            forall|cpu_id:CPUID, pcid:Pcid| #![auto] 0 <= cpu_id < NUM_CPUS && 0<=pcid<PCID_MAX && self.mmu_man.get_free_pcids_as_set().contains(pcid)
                ==> (
                    self.cpu_list[cpu_id as int].get_tlb_for_pcid(pcid) =~= Map::empty()
                )
        )
        &&&
        (
            forall|cpu_id:CPUID, pcid:Pcid, va:VAddr| #![auto] 0 <= cpu_id < NUM_CPUS && 0<=pcid<PCID_MAX && self.mmu_man.get_free_pcids_as_set().contains(pcid) == false
                && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_None()
                ==> (
                    self.cpu_list[cpu_id as int].get_tlb_for_pcid(pcid).dom().contains(va) == false

                )
        )
        &&&
        (
            forall|cpu_id:CPUID, pcid:Pcid, va:VAddr| #![auto] 0 <= cpu_id < NUM_CPUS && 0<=pcid<PCID_MAX && self.mmu_man.get_free_pcids_as_set().contains(pcid) == false
                && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some()
                ==> (
                    (self.cpu_list[cpu_id as int].get_tlb_for_pcid(pcid).dom().contains(va) == false)
                    ||
                    (self.cpu_list[cpu_id as int].get_tlb_for_pcid(pcid)[va] =~= self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0())
                )
        )
    }
    #[verifier(inline)]
    pub open spec fn wf(&self) -> bool{
        &&&
        (
            self.proc_man.wf()
        )
        &&&
        (
            self.mmu_man.wf()
        )
        &&&
        (
            self.page_alloc.wf()
        )
        &&&
        (
            self.cpu_list.wf()
        )
        &&&
        (
            self.kernel_cpu_list_wf()
        )
        &&&
        (
            self.kernel_mem_layout_wf()
        )
        &&&
        (
            self.kernel_mmu_page_alloc_pagetable_wf()
        )
        &&&
        (
            self.kernel_mmu_page_alloc_iommutable_wf()
        )
        &&&
        (self.kernel_proc_mmu_wf())
        &&&
        (self.kernel_proc_no_thread_in_transit())
        &&&
        (self.kernel_tlb_wf())
    }

    pub proof fn pagetable_mem_wf_derive(&self)
        requires
            self.wf(),
            self.kernel_mmu_page_alloc_pagetable_wf(),
        ensures
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).subset_of(self.page_alloc.get_mapped_pages()),
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).disjoint(self.page_alloc.get_page_table_pages()),
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).disjoint(self.page_alloc.get_free_pages_as_set()),
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).disjoint(self.page_alloc.get_allocated_pages()),
            forall|pcid:Pcid, pa:PAddr| #![auto] 0<=pcid<PCID_MAX && page_ptr_valid(pa) && self.mmu_man.get_pagetable_by_pcid(pcid).get_pagetable_mapped_pages().contains(pa) ==>
            (
                self.page_alloc.get_mapped_pages().contains(pa)
            ),
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some() ==>
            (
                self.page_alloc.get_mapped_pages().contains(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0().addr)
            )
    {
        lemma_set_properties::<Set<PagePtr>>();
        assert(
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some() ==>
            (
                self.page_alloc.get_page_mappings(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0().addr).len() > 0
            )
        );
        assert(
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some() ==>
            (
                self.page_alloc.get_page(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0().addr).state == MAPPED
            )
        );
        assert(
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some() ==>
            (
                self.page_alloc.get_mapped_pages().contains(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0().addr)
            )
        );
        assert(
            forall|pcid:Pcid, pa:PAddr| #![auto] 0<=pcid<PCID_MAX && page_ptr_valid(pa) && self.mmu_man.get_pagetable_by_pcid(pcid).get_pagetable_mapped_pages().contains(pa) ==>
            (
                exists|va:usize| #![auto] spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some() && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0().addr =~= pa
            )
        );
        assert(
            forall|pcid:Pcid, pa:PAddr| #![auto] 0<=pcid<PCID_MAX && page_ptr_valid(pa) && self.mmu_man.get_pagetable_by_pcid(pcid).get_pagetable_mapped_pages().contains(pa) ==>
            (
                self.page_alloc.get_mapped_pages().contains(pa)
            )
        );
        assert(
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid) =~= self.mmu_man.get_pagetable_by_pcid(pcid).get_pagetable_mapped_pages()
        );
        assert(forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).subset_of(self.page_alloc.get_mapped_pages()));
        assert(forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).disjoint(self.page_alloc.get_page_table_pages()));
        assert(forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).disjoint(self.page_alloc.get_free_pages_as_set()));
        assert(forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).disjoint(self.page_alloc.get_allocated_pages()));
    }


    pub proof fn iommutable_mem_wf_derive(&self)
    requires
        self.wf(),
        self.kernel_mmu_page_alloc_iommutable_wf(),
    ensures
        forall|ioid:Pcid| #![auto] 0<=ioid<IOID_MAX ==> self.mmu_man.get_iommutable_mapped_pages_by_ioid(ioid).subset_of(self.page_alloc.get_mapped_pages()),
        forall|ioid:Pcid| #![auto] 0<=ioid<IOID_MAX ==> self.mmu_man.get_iommutable_mapped_pages_by_ioid(ioid).disjoint(self.page_alloc.get_page_table_pages()),
        forall|ioid:Pcid| #![auto] 0<=ioid<IOID_MAX ==> self.mmu_man.get_iommutable_mapped_pages_by_ioid(ioid).disjoint(self.page_alloc.get_free_pages_as_set()),
        forall|ioid:Pcid| #![auto] 0<=ioid<IOID_MAX ==> self.mmu_man.get_iommutable_mapped_pages_by_ioid(ioid).disjoint(self.page_alloc.get_allocated_pages()),
    {
    lemma_set_properties::<Set<PagePtr>>();
    assert(
        forall|ioid:Pcid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) && self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].is_Some() ==>
        (
            self.page_alloc.get_page_io_mappings(self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].get_Some_0().addr).len() > 0
        )
    );
    assert(
        forall|ioid:Pcid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) && self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].is_Some() ==>
        (
            self.page_alloc.get_page(self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].get_Some_0().addr).state == MAPPED
        )
    );
    assert(
        forall|ioid:Pcid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) && self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].is_Some() ==>
        (
            self.page_alloc.get_mapped_pages().contains(self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].get_Some_0().addr)
        )
    );
    assert(
        forall|ioid:Pcid, pa:PAddr| #![auto] 0<=ioid<IOID_MAX && page_ptr_valid(pa) && self.mmu_man.get_iommutable_by_ioid(ioid).get_iommutable_mapped_pages().contains(pa) ==>
        (
            exists|va:usize| #![auto] spec_va_valid(va) && self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].is_Some() && spec_va_valid(va) && self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].get_Some_0().addr =~= pa
        )
    );
    assert(
        forall|ioid:Pcid, pa:PAddr| #![auto] 0<=ioid<IOID_MAX && page_ptr_valid(pa) && self.mmu_man.get_iommutable_by_ioid(ioid).get_iommutable_mapped_pages().contains(pa) ==>
        (
            self.page_alloc.get_mapped_pages().contains(pa)
        )
    );
    assert(
        forall|ioid:Pcid| #![auto] 0<=ioid<IOID_MAX ==> self.mmu_man.get_iommutable_mapped_pages_by_ioid(ioid) =~= self.mmu_man.get_iommutable_by_ioid(ioid).get_iommutable_mapped_pages()
    );
    assert(forall|ioid:Pcid| #![auto] 0<=ioid<IOID_MAX ==> self.mmu_man.get_iommutable_mapped_pages_by_ioid(ioid).subset_of(self.page_alloc.get_mapped_pages()));
    assert(forall|ioid:Pcid| #![auto] 0<=ioid<IOID_MAX ==> self.mmu_man.get_iommutable_mapped_pages_by_ioid(ioid).disjoint(self.page_alloc.get_page_table_pages()));
    assert(forall|ioid:Pcid| #![auto] 0<=ioid<IOID_MAX ==> self.mmu_man.get_iommutable_mapped_pages_by_ioid(ioid).disjoint(self.page_alloc.get_free_pages_as_set()));
    assert(forall|ioid:Pcid| #![auto] 0<=ioid<IOID_MAX ==> self.mmu_man.get_iommutable_mapped_pages_by_ioid(ioid).disjoint(self.page_alloc.get_allocated_pages()));
    }

    pub proof fn kernel_pagetable_none_infer_none_in_page_alloc(&self)
        requires
            self.wf()
        ensures
            forall|pa:PAddr, pcid:Pcid, va:usize| #![auto]  self.page_alloc.get_available_pages().contains(pa) && 0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_None() ==>
                (self.page_alloc.get_page_mappings(pa).contains((pcid,va)) == false)
    {

    }

    pub proof fn kernel_iommutable_none_infer_none_in_page_alloc(&self)
        requires
            self.wf()
        ensures
            forall|pa:PAddr, ioid:IOid, va:usize| #![auto]  self.page_alloc.get_available_pages().contains(pa) && 0<=ioid<IOID_MAX && spec_va_valid(va) && self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].is_None() ==>
                (self.page_alloc.get_page_io_mappings(pa).contains((ioid,va)) == false)
    {

    }

}

}
