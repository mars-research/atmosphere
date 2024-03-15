use vstd::prelude::*;
verus! {

// use crate::array_vec::*;
// use crate::proc::*;
// use crate::page_alloc::*;
// use crate::mmu::*;
// use crate::cpu::{Cpu,CPUID};
// use crate::mars_array::MarsArray;
use crate::pagetable::*;
use crate::define::*;

use crate::kernel::*;

impl Kernel{

    pub fn kernel_map_new_page_by_pcid(&mut self, pcid: Pcid, va: usize, perm_bits:usize)
        requires
            old(self).wf(),
            0<=pcid<PCID_MAX,
            spec_va_valid(va),
            old(self).page_alloc.free_pages.len() >= 1,
            old(self).mmu_man.get_free_pcids_as_set().contains(pcid) == false,
            old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_None(),
            spec_va_perm_bits_valid(perm_bits),
            old(self).mmu_man.get_pagetable_by_pcid(pcid).is_va_entry_exist(va),
        ensures
            self.wf(),
            self.proc_man =~= old(self).proc_man,
            self.cpu_list =~= old(self).cpu_list,
            self.mmu_man.free_pcids =~= old(self).mmu_man.free_pcids,
            self.mmu_man.free_ioids =~= old(self).mmu_man.free_ioids,
            self.page_alloc.free_pages.len() == old(self).page_alloc.free_pages.len() - 1,
            self.mmu_man.free_pcids =~= old(self).mmu_man.free_pcids,
            forall|i:Pcid| #![auto] 0<=i<PCID_MAX && i !=pcid ==> self.mmu_man.get_pagetable_mapping_by_pcid(i) =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(i),
            forall|i:IOid| #![auto] 0<=i<IOID_MAX ==> self.mmu_man.get_iommutable_mapping_by_ioid(i) =~= old(self).mmu_man.get_iommutable_mapping_by_ioid(i),
            forall|_va:VAddr| #![auto] spec_va_valid(_va) && va != _va ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[_va] =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[_va],
            self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some(),
    {
        let pa = self.page_alloc.alloc_page_and_map((pcid,va),RWX);
        assert(old(self).page_alloc.get_free_pages_as_set().contains(pa));
        assert(self.mmu_man.get_mmu_page_closure().contains(pa) == false);
        let result = self.mmu_man.map_pagetable_page(pcid, va, PageEntry{addr:pa,perm:perm_bits});
        assert(result == true);


        assert(
            self.proc_man.wf()
        );
        assert(
            self.mmu_man.wf()
        );
        assert(
            self.page_alloc.wf()
        );
        assert(
            self.cpu_list.wf()
        );
        assert(
            self.kernel_cpu_list_wf()
        );
        assert(
            self.kernel_mem_layout_wf()
        );
        assert(
            self.kernel_mmu_page_alloc_pagetable_wf()
        );
        assert(
            self.kernel_mmu_page_alloc_iommutable_wf()
        );
        assert(self.kernel_proc_mmu_wf());
        assert(self.kernel_proc_no_thread_in_transit());
        assert(self.kernel_tlb_wf());
        assert(self.wf());
    }

    pub fn kernel_create_and_map_range_new_pages(&mut self, pcid: Pcid, va: usize, perm_bits:usize, range: usize)
        requires
            old(self).wf(),
            0<=pcid<PCID_MAX,
            // spec_va_valid(va),
            old(self).page_alloc.free_pages.len() >= 4*range,
            old(self).mmu_man.get_free_pcids_as_set().contains(pcid) == false,
            spec_va_perm_bits_valid(perm_bits),
            forall|i:usize| #![auto] 0<=i<range ==> spec_va_valid(spec_va_add_range(va,i)),
            forall|i:usize| #![auto] 0<=i<range ==> old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,i)].is_None(),
        ensures
            self.wf(),
            self.proc_man =~= old(self).proc_man,
            self.cpu_list =~= old(self).cpu_list,
            self.mmu_man.free_pcids =~= old(self).mmu_man.free_pcids,
            self.mmu_man.free_ioids =~= old(self).mmu_man.free_ioids,
            forall|_pcid:Pcid| #![auto] 0<=_pcid<PCID_MAX && self.mmu_man.get_free_pcids_as_set().contains(_pcid) == false && _pcid != pcid ==>
                self.mmu_man.get_pagetable_mapping_by_pcid(_pcid) =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(_pcid),
            forall|ioid:IOid| #![auto] 0<=ioid<IOID_MAX && self.mmu_man.get_free_ioids_as_set().contains(ioid) == false ==>
                self.mmu_man.get_iommutable_mapping_by_ioid(ioid) =~= old(self).mmu_man.get_iommutable_mapping_by_ioid(ioid),
            forall|j:usize| #![auto] 0<=j<range ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_Some(),
            forall|_va:VAddr| #![auto] spec_va_valid(_va) &&
            (
                forall|j:usize| #![auto] 0<=j<range ==> spec_va_add_range(va,j) != _va
            )
            ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[_va] == old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[_va],
    {
        let mut i = 0;
        while i != range
            invariant
                0<=i<=range,
                self.wf(),
                0<=pcid<PCID_MAX,
                // spec_va_valid(va),
                self.page_alloc.free_pages.len() >= 4*(range - i),
                self.mmu_man.get_free_pcids_as_set().contains(pcid) == false,
                self.proc_man =~= old(self).proc_man,
                self.cpu_list =~= old(self).cpu_list,
                self.mmu_man.free_pcids =~= old(self).mmu_man.free_pcids,
                self.mmu_man.free_ioids =~= old(self).mmu_man.free_ioids,
                forall|_pcid:Pcid| #![auto] 0<=_pcid<PCID_MAX && _pcid != pcid ==>
                    self.mmu_man.get_pagetable_mapping_by_pcid(_pcid) =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(_pcid),
                forall|ioid:IOid| #![auto] 0<=ioid<IOID_MAX ==>
                    self.mmu_man.get_iommutable_mapping_by_ioid(ioid) =~= old(self).mmu_man.get_iommutable_mapping_by_ioid(ioid),
                spec_va_perm_bits_valid(perm_bits),
                forall|i:usize| #![auto] 0<=i<range ==> spec_va_valid(spec_va_add_range(va,i)),
                forall|j:usize| #![auto] i<=j<range ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_None(),
                forall|j:usize| #![auto] 0<=j<i ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_Some(),
                // Seq::new(i, |j: usize| spec_va_add_range(va,j)).contains(_va) == false
                forall|_va:VAddr| #![auto] spec_va_valid(_va) &&
                    (
                        forall|j:usize| #![auto] 0<=j<i ==> spec_va_add_range(va,j) != _va
                    )
                    ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[_va] == old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[_va],
            ensures
                i == range,
                self.wf(),
                self.proc_man =~= old(self).proc_man,
                self.cpu_list =~= old(self).cpu_list,
                self.mmu_man.free_pcids =~= old(self).mmu_man.free_pcids,
                self.mmu_man.free_ioids =~= old(self).mmu_man.free_ioids,
                forall|_pcid:Pcid| #![auto] 0<=_pcid<PCID_MAX && _pcid != pcid ==>
                    self.mmu_man.get_pagetable_mapping_by_pcid(_pcid) =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(_pcid),
                forall|ioid:IOid| #![auto] 0<=ioid<IOID_MAX ==>
                    self.mmu_man.get_iommutable_mapping_by_ioid(ioid) =~= old(self).mmu_man.get_iommutable_mapping_by_ioid(ioid),
                forall|j:usize| #![auto] 0<=j<range ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_Some(),
                forall|_va:VAddr| #![auto] spec_va_valid(_va) &&
                (
                    forall|j:usize| #![auto] 0<=j<i ==> spec_va_add_range(va,j) != _va
                )
                ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[_va] == old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[_va],
        {
            // TODO: @Xiangdong prove or make this a lemma
            assume(forall|i:usize, j:usize| #![auto] i != j ==>  spec_va_add_range(va,i) != spec_va_add_range(va,j));
            self.kernel_create_va_entry_by_pcid(pcid,va_add_range(va,i));
            self.kernel_map_new_page_by_pcid(pcid,va_add_range(va,i),perm_bits);
            // assert(forall|j:usize| #![auto] i<=j<range &&  ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_None());
            i = i + 1;
        }
    }

}
}
