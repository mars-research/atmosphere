use vstd::prelude::*;
verus! {

// use crate::array_vec::*;
// use crate::proc::*;
use crate::page_alloc::*;
// use crate::mmu::*;
// use crate::cpu::{Cpu,CPUID};
// use crate::mars_array::MarsArray;
use crate::pagetable::*;
use crate::define::*;

use crate::kernel::*;

impl Kernel{
    pub fn kernel_map_pagetable_page_to_pagetable(&mut self, pcid: Pcid, va_src: VAddr, target: Pcid, va_dst: VAddr,perm_bits:usize)
        requires
            old(self).wf(),
            0<=pcid<PCID_MAX,
            0<=target<PCID_MAX,
            // pcid != target,
            spec_va_valid(va_src),
            spec_va_valid(va_dst),
            old(self).page_alloc.free_pages.len() >= 3,
            old(self).mmu_man.get_free_pcids_as_set().contains(pcid) == false,
            old(self).mmu_man.get_free_pcids_as_set().contains(target) == false,
            old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[va_src].is_Some(),
            old(self).page_alloc.page_array@[
                page_ptr2page_index(old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[va_src].get_Some_0().addr) as int].rf_count < usize::MAX,
            old(self).mmu_man.get_pagetable_mapping_by_pcid(target)[va_dst].is_None(),
            spec_va_perm_bits_valid(perm_bits),
        ensures
            self.wf(),
            self.page_alloc.free_pages.len() >= old(self).page_alloc.free_pages.len() - 3,
            self.page_alloc.page_array@[page_ptr2page_index(old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[va_src].get_Some_0().addr) as int].rf_count ==
                old(self).page_alloc.page_array@[page_ptr2page_index(old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[va_src].get_Some_0().addr) as int].rf_count + 1,
            forall|i:int|#![auto] 0<=i<NUM_PAGES && i != page_ptr2page_index(old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[va_src].get_Some_0().addr)
                ==> self.page_alloc.page_array@[i].rf_count == old(self).page_alloc.page_array@[i].rf_count,
            self.mmu_man.free_pcids =~= old(self).mmu_man.free_pcids,
            self.mmu_man.free_ioids =~= old(self).mmu_man.free_ioids,
            forall|i:IOid| #![auto] 0<=i<PCID_MAX ==> self.mmu_man.get_iommutable_mapping_by_ioid(i) =~= old(self).mmu_man.get_iommutable_mapping_by_ioid(i),
            forall|i:Pcid| #![auto] 0<=i<PCID_MAX && i != target ==> self.mmu_man.get_pagetable_mapping_by_pcid(i) =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(i),
            forall|_va:VAddr| #![auto] spec_va_valid(_va) && va_dst != _va ==> self.mmu_man.get_pagetable_mapping_by_pcid(target)[_va] =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(target)[_va],
            self.mmu_man.get_pagetable_mapping_by_pcid(target)[va_dst].is_Some(),
            self.mmu_man.get_pagetable_mapping_by_pcid(target)[va_dst].get_Some_0().addr =~= self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va_src].get_Some_0().addr,
            self.cpu_list =~= old(self).cpu_list,
            self.proc_man =~= old(self).proc_man,
    {
        proof{
            self.pagetable_mem_wf_derive();
            self.kernel_pagetable_none_infer_none_in_page_alloc();
        }
        let option = self.mmu_man.mmu_get_va_entry_by_pcid(pcid,va_src);
        assert(option.is_Some());
        let entry = option.unwrap();
        assert(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va_src].is_Some());
        assert(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va_src].get_Some_0().addr =~= entry.addr);
        assert(self.page_alloc.get_mapped_pages().contains(entry.addr) == true);
        assert(self.page_alloc.get_page_table_pages().contains(entry.addr) == false);
        assert(self.mmu_man.get_mmu_page_closure().contains(entry.addr) == false);
        self.kernel_create_va_entry_by_pcid(target,va_dst);
        assert(self.wf());
        assert(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va_src].is_Some());
        assert(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va_src].get_Some_0().addr =~= entry.addr);
        assert(self.page_alloc.get_mapped_pages().contains(entry.addr) == true);
        assert(self.page_alloc.get_page_table_pages().contains(entry.addr) == false);
        assert(self.mmu_man.get_mmu_page_closure().contains(entry.addr) == false);
        self.kernel_map_pagetable_page(target,va_dst,PageEntry{addr:entry.addr, perm: perm_bits});

        assert(self.wf());
    }

    pub fn kernel_map_pagetable_range_page_to_pagetable(&mut self, pcid: Pcid, target: Pcid, va_src: usize, va_dst: usize,perm_bits:usize, range: usize)
        requires
            old(self).wf(),
            0<=pcid<PCID_MAX,
            0<=target<IOID_MAX,
            // pcid != target,
            forall|i:usize| #![auto] 0<=i<range ==> spec_va_valid(spec_va_add_range(va_src,i)),
            forall|i:usize| #![auto] 0<=i<range ==> spec_va_valid(spec_va_add_range(va_dst,i)),
            old(self).page_alloc.free_pages.len() >= 3 * range,
            old(self).mmu_man.get_free_pcids_as_set().contains(pcid) == false,
            old(self).mmu_man.get_free_pcids_as_set().contains(target) == false,
            forall|i:usize| #![auto] 0<=i<range ==> old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va_src,i)].is_Some(),
            forall|i:usize| #![auto] 0<=i<range ==>  old(self).page_alloc.page_array@[
                page_ptr2page_index(old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va_src,i)].get_Some_0().addr) as int].rf_count < usize::MAX - range,
            forall|i:usize| #![auto] 0<=i<range ==> old(self).mmu_man.get_pagetable_mapping_by_pcid(target)[spec_va_add_range(va_dst,i)].is_None(),
            spec_va_perm_bits_valid(perm_bits),
        ensures
            self.wf(),
            forall|j:usize| #![auto] 0<=j<range ==> self.mmu_man.get_pagetable_mapping_by_pcid(target)[spec_va_add_range(va_dst,j)].is_Some(),
            forall|j:usize| #![auto] 0<=j<range  ==> self.mmu_man.get_pagetable_mapping_by_pcid(target)[spec_va_add_range(va_dst,j)].get_Some_0().addr =~= self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va_src,j)].get_Some_0().addr,
            forall|i:IOid| #![auto] 0<=i<PCID_MAX ==> self.mmu_man.get_iommutable_mapping_by_ioid(i) =~= old(self).mmu_man.get_iommutable_mapping_by_ioid(i),
            forall|i:Pcid| #![auto] 0<=i<PCID_MAX && i != target ==> self.mmu_man.get_pagetable_mapping_by_pcid(i) =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(i),
            self.cpu_list =~= old(self).cpu_list,
            self.proc_man =~= old(self).proc_man,
    {
        let mut i = 0;
        while i != range
            invariant
                0<=i<=range,
                self.wf(),
                0<=pcid<PCID_MAX,
                0<=target<IOID_MAX,
                // pcid != target,
                forall|i:usize| #![auto] 0<=i<range ==> spec_va_valid(spec_va_add_range(va_src,i)),
                forall|i:usize| #![auto] 0<=i<range ==> spec_va_valid(spec_va_add_range(va_dst,i)),
                self.page_alloc.free_pages.len() >= 3 * (range - i),
                self.mmu_man.get_free_pcids_as_set().contains(pcid) == false,
                self.mmu_man.get_free_pcids_as_set().contains(target) == false,
                forall|i:usize| #![auto] 0<=i<range ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va_src,i)].is_Some(),
                forall|j:usize| #![auto] i<=j<range ==> self.page_alloc.page_array@[
                    page_ptr2page_index(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va_src,j)].get_Some_0().addr) as int].rf_count < usize::MAX - range + i,
                forall|j:usize| #![auto] i<=j<range  ==> self.mmu_man.get_pagetable_mapping_by_pcid(target)[spec_va_add_range(va_dst,j)].is_None(),
                forall|j:usize| #![auto] 0<=j<i  ==> self.mmu_man.get_pagetable_mapping_by_pcid(target)[spec_va_add_range(va_dst,j)].is_Some(),
                spec_va_perm_bits_valid(perm_bits),
                forall|j:usize| #![auto] 0<=j<i  ==> self.mmu_man.get_pagetable_mapping_by_pcid(target)[spec_va_add_range(va_dst,j)].get_Some_0().addr =~= self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va_src,j)].get_Some_0().addr,
                forall|i:IOid| #![auto] 0<=i<PCID_MAX ==> self.mmu_man.get_iommutable_mapping_by_ioid(i) =~= old(self).mmu_man.get_iommutable_mapping_by_ioid(i),
                forall|i:Pcid| #![auto] 0<=i<PCID_MAX && i != target ==> self.mmu_man.get_pagetable_mapping_by_pcid(i) =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(i),
                self.cpu_list =~= old(self).cpu_list,
                self.proc_man =~= old(self).proc_man,
            ensures
                i == range,
                self.wf(),
                forall|j:usize| #![auto] 0<=j<i  ==> self.mmu_man.get_pagetable_mapping_by_pcid(target)[spec_va_add_range(va_dst,j)].is_Some(),
                forall|j:usize| #![auto] 0<=j<i  ==> self.mmu_man.get_pagetable_mapping_by_pcid(target)[spec_va_add_range(va_dst,j)].get_Some_0().addr =~= self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va_src,j)].get_Some_0().addr,
                forall|i:IOid| #![auto] 0<=i<PCID_MAX ==> self.mmu_man.get_iommutable_mapping_by_ioid(i) =~= old(self).mmu_man.get_iommutable_mapping_by_ioid(i),
                forall|i:Pcid| #![auto] 0<=i<PCID_MAX && i != target ==> self.mmu_man.get_pagetable_mapping_by_pcid(i) =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(i),
                self.cpu_list =~= old(self).cpu_list,
                self.proc_man =~= old(self).proc_man,
        {
            // TODO: @Xiangdong prove or make this a lemma
            assume(forall|i:usize, j:usize| #![auto] i != j ==>  spec_va_add_range(va_dst,i) != spec_va_add_range(va_dst,j));
            assume(forall|i:usize, j:usize| #![auto] i != j ==>  spec_va_add_range(va_src,i) != spec_va_add_range(va_src,j));
            self.kernel_map_pagetable_page_to_pagetable(pcid,va_add_range(va_src,i),target,va_add_range(va_dst,i),perm_bits);
            i = i + 1;
        }
    }
}
}
