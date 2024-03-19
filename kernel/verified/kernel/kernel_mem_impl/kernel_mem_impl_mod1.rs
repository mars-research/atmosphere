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
    pub fn kernel_map_pagetable_page(&mut self, pcid:Pcid, va: usize, dst:PageEntry)
        requires
            old(self).wf(),
            0<=pcid<PCID_MAX,
            old(self).mmu_man.get_free_pcids_as_set().contains(pcid) == false,
            spec_va_valid(va),
            old(self).mmu_man.get_mmu_page_closure().contains(dst.addr) == false,
            old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_None(),
            page_ptr_valid(dst.addr),
            spec_va_perm_bits_valid(dst.perm),
            old(self).page_alloc.get_mapped_pages().contains(dst.addr),
            old(self).page_alloc.get_page_mappings(dst.addr).contains((pcid,va)) == false,
            old(self).page_alloc.page_array@[page_ptr2page_index(dst.addr) as int].rf_count < usize::MAX,
            old(self).mmu_man.get_pagetable_by_pcid(pcid).is_va_entry_exist(va),
        ensures
            self.wf(),
            self.page_alloc.free_pages.len() =~= old(self).page_alloc.free_pages.len(),
            self.page_alloc.page_array@[page_ptr2page_index(dst.addr) as int].rf_count ==
                old(self).page_alloc.page_array@[page_ptr2page_index(dst.addr) as int].rf_count + 1,
            forall|i:int|#![auto] 0<=i<NUM_PAGES && i != page_ptr2page_index(dst.addr)
                ==> self.page_alloc.page_array@[i].rf_count == old(self).page_alloc.page_array@[i].rf_count,
            self.mmu_man.free_pcids =~= old(self).mmu_man.free_pcids,
            self.mmu_man.free_ioids =~= old(self).mmu_man.free_ioids,
            forall|i:Pcid| #![auto] 0<=i<PCID_MAX && i !=pcid ==> self.mmu_man.get_pagetable_mapping_by_pcid(i) =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(i),
            forall|i:IOid| #![auto] 0<=i<IOID_MAX ==> self.mmu_man.get_iommutable_mapping_by_ioid(i) =~= old(self).mmu_man.get_iommutable_mapping_by_ioid(i),
            forall|i:Pcid,_va:VAddr| #![auto] 0<=i<PCID_MAX && i !=pcid && spec_va_valid(_va) ==> self.mmu_man.get_pagetable_mapping_by_pcid(i)[_va] =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(i)[_va],
            forall|i:IOid,_va:VAddr| #![auto] 0<=i<IOID_MAX && spec_va_valid(_va) ==> self.mmu_man.get_iommutable_mapping_by_ioid(i)[_va] =~= old(self).mmu_man.get_iommutable_mapping_by_ioid(i)[_va],
            forall|_va:VAddr| #![auto] spec_va_valid(_va) && va != _va ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[_va] =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[_va],
            self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some(),
            self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0().addr == dst.addr,
            self.cpu_list =~= old(self).cpu_list,
            self.proc_man =~= old(self).proc_man,
    {
        let result = self.mmu_man.map_pagetable_page(pcid,va,dst);
        assert(result == true);
        assert(old(self).page_alloc.get_available_pages().contains(dst.addr));
        self.page_alloc.map_user_page(dst.addr,(pcid,va),RWX);
        // assert(self.page_alloc.get_page_table_pages() =~= self.mmu_man.get_mmu_page_closure());

        proof{page_ptr_lemma();}
        assert(self.kernel_mmu_page_alloc_iommutable_wf());
        assert(self.kernel_mmu_page_alloc_pagetable_wf());
        assert(self.kernel_tlb_wf());
        assert(self.wf());
    }

    pub fn kernel_map_iommutable_page(&mut self, ioid:IOid, va: usize, dst:PageEntry)
        requires
            old(self).wf(),
            0<=ioid<IOID_MAX,
            old(self).mmu_man.get_free_ioids_as_set().contains(ioid) == false,
            spec_va_valid(va),
            old(self).mmu_man.get_mmu_page_closure().contains(dst.addr) == false,
            old(self).mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].is_None(),
            page_ptr_valid(dst.addr),
            spec_va_perm_bits_valid(dst.perm),
            old(self).page_alloc.get_mapped_pages().contains(dst.addr),
            old(self).page_alloc.get_page_io_mappings(dst.addr).contains((ioid,va)) == false,
            old(self).page_alloc.page_array@[page_ptr2page_index(dst.addr) as int].rf_count < usize::MAX,
            old(self).mmu_man.get_iommutable_by_ioid(ioid).dummy.is_va_entry_exist(va),
        ensures
            self.wf(),
            self.page_alloc.free_pages.len() =~= old(self).page_alloc.free_pages.len(),
            self.page_alloc.page_array@[page_ptr2page_index(dst.addr) as int].rf_count ==
                old(self).page_alloc.page_array@[page_ptr2page_index(dst.addr) as int].rf_count + 1,
            forall|i:int|#![auto] 0<=i<NUM_PAGES && i != page_ptr2page_index(dst.addr)
                ==> self.page_alloc.page_array@[i].rf_count == old(self).page_alloc.page_array@[i].rf_count,
            self.mmu_man.free_pcids =~= old(self).mmu_man.free_pcids,
            self.mmu_man.free_ioids =~= old(self).mmu_man.free_ioids,
            forall|i:Pcid| #![auto] 0<=i<PCID_MAX ==> self.mmu_man.get_pagetable_mapping_by_pcid(i) =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(i),
            forall|i:IOid| #![auto] 0<=i<IOID_MAX && i !=ioid ==> self.mmu_man.get_iommutable_mapping_by_ioid(i) =~= old(self).mmu_man.get_iommutable_mapping_by_ioid(i),
            forall|_va:VAddr| #![auto] spec_va_valid(_va) && va != _va ==> self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[_va] =~= old(self).mmu_man.get_iommutable_mapping_by_ioid(ioid)[_va],
            self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].is_Some(),
    {
        let result = self.mmu_man.map_iommutable_page(ioid,va,dst);
        assert(result == true);
        assert(old(self).page_alloc.get_available_pages().contains(dst.addr));
        self.page_alloc.map_user_io_page(dst.addr,(ioid,va),RWX);
        // assert(self.page_alloc.get_page_table_pages() =~= self.mmu_man.get_mmu_page_closure());

        proof{page_ptr_lemma();}
        assert(self.kernel_mmu_page_alloc_iommutable_wf());
        assert(self.kernel_mmu_page_alloc_pagetable_wf());
        assert(self.kernel_tlb_wf());
        assert(self.wf());
    }

    pub fn kernel_unmap_pagetable_page(&mut self, pcid:Pcid, va: usize) -> (ret:Option<PageEntry>)
        requires
            old(self).wf(),
            old(self).kernel_mmu_page_alloc_pagetable_wf(),
            0<=pcid<PCID_MAX,
            spec_va_valid(va),
            old(self).mmu_man.get_free_pcids_as_set().contains(pcid) == false,
    {
        let ret = self.mmu_man.unmap_pagetable_page(pcid,va);
        if ret.is_none() {
            assert(old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_None());
            assert(self.wf());
        }
        else{
            assert(page_ptr_valid(ret.get_Some_0().addr));
            assert(spec_va_perm_bits_valid(ret.get_Some_0().perm));
            assert(self.page_alloc.get_page_mappings(ret.get_Some_0().addr).contains((pcid,va)));
            self.page_alloc.unmap_user_page(ret.unwrap().addr,(pcid,va));
            self.cpu_list.flush_address(pcid,va);

            // assert(
            //     self.proc_man.wf()
            // );
            // assert(
            //     self.mmu_man.wf()
            // );
            // assert(
            //     self.page_alloc.wf()
            // );
            // assert(
            //     self.cpu_list.wf()
            // );
            // assert(
            //     self.kernel_cpu_list_wf()
            // );
            // assert(
            //     self.kernel_mem_layout_wf()
            // );
            // assert(
            //     self.kernel_mmu_page_alloc_pagetable_wf()
            // );
            // assert(
            //     self.kernel_mmu_page_alloc_iommutable_wf()
            // );
            // assert(self.kernel_proc_mmu_wf());
            // assert(self.kernel_proc_no_thread_in_transit());
            // assert(self.kernel_tlb_wf());
            assert(self.wf());
        }

        return ret;
    }


    pub fn kernel_create_va_entry_by_pcid(&mut self, pcid: Pcid, va: usize)
        requires
            old(self).wf(),
            0<=pcid<PCID_MAX,
            spec_va_valid(va),
            old(self).page_alloc.free_pages.len() >= 3,
            old(self).mmu_man.get_free_pcids_as_set().contains(pcid) == false,
        ensures
            self.wf(),
            self.proc_man =~= old(self).proc_man,
            self.cpu_list =~= old(self).cpu_list,
            self.mmu_man.free_pcids =~= old(self).mmu_man.free_pcids,
            self.mmu_man.free_ioids =~= old(self).mmu_man.free_ioids,
            // page_alloc.wf(),
            self.page_alloc.get_mapped_pages() =~= old(self).page_alloc.get_mapped_pages(),
            self.page_alloc.get_allocated_pages() =~= old(self).page_alloc.get_allocated_pages(),
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> self.page_alloc.get_page_mappings(page_ptr) =~= old(self).page_alloc.get_page_mappings(page_ptr),
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> self.page_alloc.get_page_io_mappings(page_ptr) =~= old(self).page_alloc.get_page_io_mappings(page_ptr),
            forall|i:Pcid| #![auto] 0<=i<PCID_MAX ==> self.mmu_man.get_pagetable_mapping_by_pcid(i) =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(i),
            forall|i:IOid| #![auto] 0<=i<IOID_MAX ==> self.mmu_man.get_iommutable_mapping_by_ioid(i) =~= old(self).mmu_man.get_iommutable_mapping_by_ioid(i),
            forall|i:Pcid, va:VAddr| #![auto] 0<=i<PCID_MAX && spec_va_valid(va) ==> self.mmu_man.get_pagetable_mapping_by_pcid(i)[va] =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(i)[va],
            forall|i:IOid, va:VAddr| #![auto] 0<=i<IOID_MAX && spec_va_valid(va) ==> self.mmu_man.get_iommutable_mapping_by_ioid(i)[va] =~= old(self).mmu_man.get_iommutable_mapping_by_ioid(i)[va],
            // self.resolve_mapping_l2(l4i,l3i,l2i).is_Some(),
            self.mmu_man.get_pagetable_by_pcid(pcid).is_va_entry_exist(va),
            self.page_alloc.free_pages.len() >= old(self).page_alloc.free_pages.len() - 3,
            self.cpu_list =~= old(self).cpu_list,
            self.proc_man =~= old(self).proc_man,

    {
        proof{
            self.pagetable_mem_wf_derive();
            self.iommutable_mem_wf_derive();
        }
        self.mmu_man.create_pagetable_va_entry(pcid,va,&mut self.page_alloc);

        // assert(
        //     self.proc_man.wf()
        // );
        // assert(
        //     self.mmu_man.wf()
        // );
        // assert(
        //     self.page_alloc.wf()
        // );
        // assert(
        //     self.cpu_list.wf()
        // );
        // assert(
        //     self.kernel_cpu_list_wf()
        // );
        // assert(
        //     self.kernel_mem_layout_wf()
        // );
        // assert(
        //     self.kernel_mmu_page_alloc_pagetable_wf()
        // );
        // assert(
        //     self.kernel_mmu_page_alloc_iommutable_wf()
        // );
        // assert(self.kernel_proc_mmu_wf());
        // assert(self.kernel_proc_no_thread_in_transit());
        // assert(self.kernel_tlb_wf());
        assert(self.wf());
    }

    pub fn kernel_create_va_entry_by_ioid(&mut self, ioid: IOid, va: usize)
        requires
            old(self).wf(),
            0<=ioid<IOID_MAX,
            spec_va_valid(va),
            old(self).page_alloc.free_pages.len() >= 3,
            old(self).mmu_man.get_free_ioids_as_set().contains(ioid) == false,
        ensures
            self.wf(),
            self.mmu_man.free_pcids =~= old(self).mmu_man.free_pcids,
            self.mmu_man.free_ioids =~= old(self).mmu_man.free_ioids,
            // page_alloc.wf(),
            // page_alloc.get_mapped_pages() =~= old(page_alloc).get_mapped_pages(),
            // page_alloc.get_allocated_pages() =~= old(page_alloc).get_allocated_pages(),
            forall|i:int|#![auto] 0<=i<NUM_PAGES ==> self.page_alloc.page_array@[i].rf_count == old(self).page_alloc.page_array@[i].rf_count,
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> self.page_alloc.get_page_mappings(page_ptr) =~= old(self).page_alloc.get_page_mappings(page_ptr),
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> self.page_alloc.get_page_io_mappings(page_ptr) =~= old(self).page_alloc.get_page_io_mappings(page_ptr),
            forall|i:Pcid| #![auto] 0<=i<PCID_MAX ==> self.mmu_man.get_pagetable_mapping_by_pcid(i) =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(i),
            forall|i:IOid| #![auto] 0<=i<IOID_MAX ==> self.mmu_man.get_iommutable_mapping_by_ioid(i) =~= old(self).mmu_man.get_iommutable_mapping_by_ioid(i),
            // self.resolve_mapping_l2(l4i,l3i,l2i).is_Some(),
            self.mmu_man.get_iommutable_by_ioid(ioid).is_va_entry_exist(va),
            self.page_alloc.free_pages.len() >= old(self).page_alloc.free_pages.len() - 3,

    {
        proof{
            self.pagetable_mem_wf_derive();
            self.iommutable_mem_wf_derive();
        }
        self.mmu_man.create_iommutable_va_entry(ioid,va,&mut self.page_alloc);

        // assert(
        //     self.proc_man.wf()
        // );
        // assert(
        //     self.mmu_man.wf()
        // );
        // assert(
        //     self.page_alloc.wf()
        // );
        // assert(
        //     self.cpu_list.wf()
        // );
        // assert(
        //     self.kernel_cpu_list_wf()
        // );
        // assert(
        //     self.kernel_mem_layout_wf()
        // );
        // assert(
        //     self.kernel_mmu_page_alloc_pagetable_wf()
        // );
        // assert(
        //     self.kernel_mmu_page_alloc_iommutable_wf()
        // );
        // assert(self.kernel_proc_mmu_wf());
        // assert(self.kernel_proc_no_thread_in_transit());
        // assert(self.kernel_tlb_wf());
        assert(self.wf());
    }
}
}
