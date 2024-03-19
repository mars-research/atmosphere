use vstd::prelude::*;
verus! {
// use vstd::ptr::PointsTo;

use crate::pagetable::*;
use crate::page_alloc::*;
use crate::define::*;
// use crate::iommutable::*;
// use vstd::ptr::PointsTo;

use crate::mmu::*;


impl MMUManager{
    pub fn map_pagetable_page(&mut self, pcid:Pcid, va: usize, dst:PageEntry) -> (ret: bool)
        requires
            0<=pcid<PCID_MAX,
            old(self).wf(),
            old(self).get_free_pcids_as_set().contains(pcid) == false,
            spec_va_valid(va),
            old(self).get_mmu_page_closure().contains(dst.addr) == false,
            old(self).get_pagetable_mapping_by_pcid(pcid)[va].is_None(),
            page_ptr_valid(dst.addr),
            spec_va_perm_bits_valid(dst.perm),
        ensures
            self.wf(),
            self.free_pcids =~= old(self).free_pcids,
            // self.page_tables =~= old(self).page_tables,
            self.page_table_pages =~= old(self).page_table_pages,
            self.free_ioids =~= old(self).free_ioids,
            self.iommu_tables =~= old(self).iommu_tables,
            self.iommu_table_pages =~= old(self).iommu_table_pages,
            forall|_pcid:Pcid| #![auto] 0<=_pcid<PCID_MAX && _pcid != pcid ==> self.get_pagetable_by_pcid(_pcid) =~= old(self).get_pagetable_by_pcid(_pcid),
            self.get_pagetable_page_closure_by_pcid(pcid) =~= old(self).get_pagetable_page_closure_by_pcid(pcid),
            old(self).get_pagetable_by_pcid(pcid).is_va_entry_exist(va) == ret,
            old(self).get_pagetable_by_pcid(pcid).is_va_entry_exist(va) ==>
                self.get_pagetable_mapping_by_pcid(pcid) =~= old(self).get_pagetable_mapping_by_pcid(pcid).insert(va,Some(dst)),
            !old(self).get_pagetable_by_pcid(pcid).is_va_entry_exist(va) ==>
                self.get_pagetable_mapping_by_pcid(pcid) =~= old(self).get_pagetable_mapping_by_pcid(pcid),
            forall|_ioid:IOid| #![auto] 0<=_ioid<IOID_MAX ==> self.get_iommutable_by_ioid(_ioid) =~= old(self).get_iommutable_by_ioid(_ioid),
            forall|_ioid:IOid| #![auto] 0<=_ioid<IOID_MAX ==> self.get_iommutable_mapping_by_ioid(_ioid) =~= old(self).get_iommutable_mapping_by_ioid(_ioid),
    {
        let ret = self.page_tables.map_pagetable_page_by_pcid(pcid,va,dst);
        assert(self.wf());
        return ret;
    }

    pub fn unmap_pagetable_page(&mut self, pcid:Pcid, va: usize) -> (ret: Option<PageEntry>)
        requires
            0<=pcid<PCID_MAX,
            old(self).wf(),
            old(self).get_free_pcids_as_set().contains(pcid) == false,
            spec_va_valid(va),
        ensures
            self.wf(),
            self.free_pcids =~= old(self).free_pcids,
            // self.page_tables =~= old(self).page_tables,
            self.page_table_pages =~= old(self).page_table_pages,
            self.free_ioids =~= old(self).free_ioids,
            self.iommu_tables =~= old(self).iommu_tables,
            self.iommu_table_pages =~= old(self).iommu_table_pages,
            forall|_pcid:Pcid| #![auto] 0<=_pcid<PCID_MAX && _pcid != pcid ==> self.get_pagetable_by_pcid(_pcid) =~= old(self).get_pagetable_by_pcid(_pcid),
            self.get_pagetable_page_closure_by_pcid(pcid) =~= old(self).get_pagetable_page_closure_by_pcid(pcid),
            old(self).get_pagetable_mapping_by_pcid(pcid)[va] == ret,
            ret.is_None() ==> self.get_pagetable_mapping_by_pcid(pcid) =~= old(self).get_pagetable_mapping_by_pcid(pcid),
            ret.is_Some() ==> self.get_pagetable_mapping_by_pcid(pcid) =~= old(self).get_pagetable_mapping_by_pcid(pcid).insert(va,None),
    {
        let ret = self.page_tables.unmap_pagetable_page_by_pcid(pcid,va);
        assert(self.wf());
        return ret;
    }

    pub fn map_iommutable_page(&mut self, ioid:IOid, va: usize, dst:PageEntry) -> (ret: bool)
        requires
            0<=ioid<IOID_MAX,
            old(self).wf(),
            old(self).get_free_ioids_as_set().contains(ioid) == false,
            spec_va_valid(va),
            old(self).get_mmu_page_closure().contains(dst.addr) == false,
            old(self).get_iommutable_mapping_by_ioid(ioid)[va].is_None(),
            page_ptr_valid(dst.addr),
            spec_va_perm_bits_valid(dst.perm),
        ensures
            self.wf(),
            self.free_pcids =~= old(self).free_pcids,
            self.page_tables =~= old(self).page_tables,
            self.page_table_pages =~= old(self).page_table_pages,
            self.free_ioids =~= old(self).free_ioids,
            // self.page_tables =~= old(self).page_tables,
            self.iommu_table_pages =~= old(self).iommu_table_pages,
            forall|_ioid:IOid| #![auto] 0<=_ioid<IOID_MAX && _ioid != ioid ==> self.get_iommutable_by_ioid(_ioid) =~= old(self).get_iommutable_by_ioid(_ioid),
            self.get_iommutable_page_closure_by_ioid(ioid) =~= old(self).get_iommutable_page_closure_by_ioid(ioid),
            old(self).get_iommutable_by_ioid(ioid).dummy.is_va_entry_exist(va) == ret,
            old(self).get_iommutable_by_ioid(ioid).dummy.is_va_entry_exist(va) ==>
                self.get_iommutable_mapping_by_ioid(ioid) =~= old(self).get_iommutable_mapping_by_ioid(ioid).insert(va,Some(dst)),
            !old(self).get_iommutable_by_ioid(ioid).dummy.is_va_entry_exist(va) ==>
                self.get_iommutable_mapping_by_ioid(ioid) =~= old(self).get_iommutable_mapping_by_ioid(ioid),
            forall|_pcid:Pcid| #![auto] 0<=_pcid<PCID_MAX ==> self.get_pagetable_by_pcid(_pcid) =~= old(self).get_pagetable_by_pcid(_pcid),
            forall|_pcid:Pcid| #![auto] 0<=_pcid<PCID_MAX ==> self.get_pagetable_mapping_by_pcid(_pcid) =~= old(self).get_pagetable_mapping_by_pcid(_pcid),
        {
        let ret = self.iommu_tables.map_iommutable_page_by_ioid(ioid,va,dst);
        assert(self.wf());
        return ret;
        }

    pub fn new_pagetable(&mut self, page_ptr: PagePtr, page_perm: Tracked<PagePerm>,kernel_pml4_entry: Option<PageEntry>) -> (ret:Pcid)
        requires
            old(self).wf(),
            old(self).free_pcids.len() > 0,
            old(self).get_mmu_page_closure().contains(page_ptr) == false,
            page_ptr != 0,
            page_perm@@.pptr == page_ptr,
            page_perm@@.value.is_Some(),
        ensures
            self.wf(),
            self.get_free_pcids_as_set() =~= old(self).get_free_pcids_as_set().remove(ret),
            old(self).get_free_pcids_as_set().contains(ret),
            self.free_ioids =~= old(self).free_ioids,
            self.iommu_tables =~= old(self).iommu_tables,
            self.iommu_table_pages =~= old(self).iommu_table_pages,
            self.get_mmu_page_closure() =~= old(self).get_mmu_page_closure().insert(page_ptr),
            forall|i:Pcid|#![auto] 0<=i<PCID_MAX ==> self.get_pagetable_mapping_by_pcid(i) =~= old(self).get_pagetable_mapping_by_pcid(i),
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> self.get_pagetable_mapping_by_pcid(pcid)[va] =~= old(self).get_pagetable_mapping_by_pcid(pcid)[va],
            forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> self.get_iommutable_mapping_by_ioid(ioid)[va] =~= old(self).get_iommutable_mapping_by_ioid(ioid)[va],
            forall|va:VAddr| #![auto] spec_va_valid(va) ==> self.page_tables[ret as int].get_pagetable_mapping()[va].is_None(),
    {
        let ret = self.free_pcids.pop_unique();
        assert(0<=ret<PCID_MAX);
        assert(forall|va:VAddr| #![auto] spec_va_valid(va) ==> self.page_tables[ret as int].get_pagetable_mapping()[va].is_None());
        assert(self.page_tables[ret as int].get_pagetable_page_closure() =~= Set::empty());

        self.page_tables.init_into_wf_by_pcid(ret,page_ptr,page_perm,kernel_pml4_entry);

        proof{
            self.page_table_pages@ = self.page_table_pages@.insert(page_ptr);
        }
        assert(self.wf());
        return ret;
    }

    pub fn new_iommutable(&mut self, page_ptr: PagePtr, page_perm: Tracked<PagePerm>) -> (ret:IOid)
        requires
            old(self).wf(),
            old(self).free_ioids.len() > 0,
            old(self).get_mmu_page_closure().contains(page_ptr) == false,
            page_ptr != 0,
            page_perm@@.pptr == page_ptr,
            page_perm@@.value.is_Some(),
        ensures
            self.wf(),
            self.get_free_ioids_as_set() =~= old(self).get_free_ioids_as_set().remove(ret),
            ret == old(self).free_ioids@[old(self).free_ioids@.len() - 1],
            old(self).get_free_ioids_as_set().contains(ret),
            self.free_pcids =~= old(self).free_pcids,
            self.page_tables =~= old(self).page_tables,
            self.page_table_pages =~= old(self).page_table_pages,
            self.root_table =~= old(self).root_table,
            self.get_mmu_page_closure() =~= old(self).get_mmu_page_closure().insert(page_ptr),
            forall|i:Pcid|#![auto] 0<=i<PCID_MAX ==> self.get_pagetable_mapping_by_pcid(i) =~= old(self).get_pagetable_mapping_by_pcid(i),
            forall|ioid:IOid| #![auto] 0<=ioid<IOID_MAX ==> self.get_iommutable_mapping_by_ioid(ioid) =~= old(self).get_iommutable_mapping_by_ioid(ioid),
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> self.get_pagetable_mapping_by_pcid(pcid)[va] =~= old(self).get_pagetable_mapping_by_pcid(pcid)[va],
            forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> self.get_iommutable_mapping_by_ioid(ioid)[va] =~= old(self).get_iommutable_mapping_by_ioid(ioid)[va],
            forall|va:VAddr| #![auto] spec_va_valid(va) ==> self.iommu_tables[ret as int].get_iommutable_mapping()[va].is_None(),
    {
        let ret = self.free_ioids.pop_unique();
        assert(0<=ret<IOID_MAX);
        assert(forall|va:VAddr| #![auto] spec_va_valid(va) ==> self.iommu_tables[ret as int].get_iommutable_mapping()[va].is_None());
        assert(self.iommu_tables[ret as int].get_iommutable_page_closure() =~= Set::empty());

        self.iommu_tables.init_into_wf_by_ioid(ret,page_ptr,page_perm);

        proof{
            self.iommu_table_pages@ = self.iommu_table_pages@.insert(page_ptr);
        }
        assert(self.wf());
        return ret;
    }

    pub fn create_pagetable_va_entry(&mut self, pcid:Pcid, va:VAddr, page_alloc:&mut PageAllocator) -> (ret:Ghost<Set<PagePtr>>)
        requires
            0<=pcid<PCID_MAX,
            old(self).wf(),
            old(self).get_free_pcids_as_set().contains(pcid) == false,
            spec_va_valid(va),
            old(page_alloc).wf(),
            old(page_alloc).free_pages.len() >= 3,
            spec_va_valid(va),
            old(page_alloc).get_free_pages_as_set().disjoint(old(self).get_mmu_page_closure()),
            forall|pcid:Pcid|#![auto] 0<=pcid<PCID_MAX ==> old(self).get_pagetable_page_closure_by_pcid(pcid).disjoint(old(page_alloc).get_free_pages_as_set()),
            forall|pcid:Pcid|#![auto] 0<=pcid<PCID_MAX ==> old(self).get_pagetable_mapped_pages_by_pcid(pcid).disjoint(old(page_alloc).get_free_pages_as_set()),
        ensures
            self.wf(),
            self.free_pcids =~= old(self).free_pcids,
            self.free_ioids =~= old(self).free_ioids,
            page_alloc.wf(),
            page_alloc.get_mapped_pages() =~= old(page_alloc).get_mapped_pages(),
            page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@,
            page_alloc.get_page_table_pages() =~= old(page_alloc).get_page_table_pages() + ret@,
            page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@,
            page_alloc.get_allocated_pages() =~= old(page_alloc).get_allocated_pages(),
            ret@.subset_of(old(page_alloc).get_free_pages_as_set()),
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> page_alloc.get_page_mappings(page_ptr) =~= old(page_alloc).get_page_mappings(page_ptr),
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> page_alloc.get_page_io_mappings(page_ptr) =~= old(page_alloc).get_page_io_mappings(page_ptr),
            forall|i:Pcid| #![auto] 0<=i<PCID_MAX ==> self.get_pagetable_mapping_by_pcid(i) =~= old(self).get_pagetable_mapping_by_pcid(i),
            forall|i:IOid| #![auto] 0<=i<IOID_MAX ==> self.get_iommutable_mapping_by_ioid(i) =~= old(self).get_iommutable_mapping_by_ioid(i),
            self.get_mmu_page_closure() =~= old(self).get_mmu_page_closure() + ret@,
            // self.resolve_mapping_l2(l4i,l3i,l2i).is_Some(),
            self.get_pagetable_by_pcid(pcid).is_va_entry_exist(va),
            page_alloc.free_pages.len() >= old(page_alloc).free_pages.len() - 3,
    {
        let ret = self.page_tables.create_va_entry_by_pcid(pcid,va,page_alloc);
        proof{
            self.page_table_pages@ = self.page_table_pages@ + ret@;
        }

        assert(
            forall|i:int,| #![auto] 0<=i<PCID_MAX && i != pcid ==> self.page_tables[i].get_pagetable_page_closure().disjoint(ret@)
        );
        assert(
            forall|i:int,| #![auto] 0<=i<PCID_MAX && i != pcid ==> self.page_tables[i].get_pagetable_page_closure().disjoint(old(self).page_tables[pcid as int].get_pagetable_page_closure())
        );

        assert(
            self.pagetables_wf()
        );
        assert(
            self.iommutables_wf()
        );
        assert(
            self.pagetable_iommutable_disjoint()
        );
        ret
    }

    pub fn create_iommutable_va_entry(&mut self, ioid:IOid, va:VAddr, page_alloc:&mut PageAllocator) -> (ret:Ghost<Set<PagePtr>>)
        requires
            0<=ioid<IOID_MAX,
            old(self).wf(),
            old(self).get_free_ioids_as_set().contains(ioid) == false,
            spec_va_valid(va),
            old(page_alloc).wf(),
            old(page_alloc).free_pages.len() >= 3,
            spec_va_valid(va),
            old(page_alloc).get_free_pages_as_set().disjoint(old(self).get_mmu_page_closure()),
            forall|ioid:IOid|#![auto] 0<=ioid<IOID_MAX ==> old(self).get_iommutable_page_closure_by_ioid(ioid).disjoint(old(page_alloc).get_free_pages_as_set()),
            forall|ioid:IOid|#![auto] 0<=ioid<IOID_MAX ==> old(self).get_iommutable_mapped_pages_by_ioid(ioid).disjoint(old(page_alloc).get_free_pages_as_set()),
        ensures
            self.wf(),
            self.free_pcids =~= old(self).free_pcids,
            self.free_ioids =~= old(self).free_ioids,
            page_alloc.wf(),
            page_alloc.get_mapped_pages() =~= old(page_alloc).get_mapped_pages(),
            page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@,
            page_alloc.get_page_table_pages() =~= old(page_alloc).get_page_table_pages() + ret@,
            page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@,
            page_alloc.get_allocated_pages() =~= old(page_alloc).get_allocated_pages(),
            ret@.subset_of(old(page_alloc).get_free_pages_as_set()),
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> page_alloc.get_page_mappings(page_ptr) =~= old(page_alloc).get_page_mappings(page_ptr),
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> page_alloc.get_page_io_mappings(page_ptr) =~= old(page_alloc).get_page_io_mappings(page_ptr),
            forall|i:Pcid| #![auto] 0<=i<PCID_MAX ==> self.get_pagetable_mapping_by_pcid(i) =~= old(self).get_pagetable_mapping_by_pcid(i),
            forall|i:IOid| #![auto] 0<=i<IOID_MAX ==> self.get_iommutable_mapping_by_ioid(i) =~= old(self).get_iommutable_mapping_by_ioid(i),
            self.get_mmu_page_closure() =~= old(self).get_mmu_page_closure() + ret@,
            // self.resolve_mapping_l2(l4i,l3i,l2i).is_Some(),
            self.get_iommutable_by_ioid(ioid).dummy.is_va_entry_exist(va),
            page_alloc.free_pages.len() >= old(page_alloc).free_pages.len() - 3,
    {
        let ret = self.iommu_tables.create_va_entry_by_ioid(ioid,va,page_alloc);
        proof{
            self.iommu_table_pages@ = self.iommu_table_pages@ + ret@;
        }

        assert(
            forall|i:int,| #![auto] 0<=i<IOID_MAX && i != ioid ==> self.iommu_tables[i].get_iommutable_page_closure().disjoint(ret@)
        );
        assert(
            forall|i:int,| #![auto] 0<=i<IOID_MAX && i != ioid ==> self.iommu_tables[i].get_iommutable_page_closure().disjoint(old(self).iommu_tables[ioid as int].get_iommutable_page_closure())
        );

        assert(
            self.pagetables_wf()
        );
        assert(
            self.iommutables_wf()
        );
        assert(
            self.pagetable_iommutable_disjoint()
        );
        ret
    }

    pub fn mmu_get_va_entry_by_pcid(&self, pcid: Pcid, va:VAddr) -> (ret:Option<PageEntry>)
        requires
            self.wf(),
            0<=pcid<PCID_MAX,
            spec_va_valid(va),
            self.get_free_pcids_as_set().contains(pcid) == false,
        ensures
            ret =~= self.get_pagetable_mapping_by_pcid(pcid)[va],
            ret.is_Some() ==> page_ptr_valid(ret.unwrap().addr),
    {
        assert(self.get_pagetable_by_pcid(pcid).wf());
        self.page_tables.get(pcid).get_va_entry(va)
    }

    pub fn mmu_get_va_entry_by_ioid(&self, ioid: IOid, va:VAddr) -> (ret:Option<PageEntry>)
        requires
            self.wf(),
            0<=ioid<IOID_MAX,
            spec_va_valid(va),
            self.get_free_ioids_as_set().contains(ioid) == false,
        ensures
            ret =~= self.get_iommutable_mapping_by_ioid(ioid)[va],
    {
        self.iommu_tables.get(ioid).dummy.get_va_entry(va)
    }

    pub fn mmu_get_pci_dev_by_ioid(&self, ioid:IOid, bus:u8,dev:u8,fun:u8) -> (ret:bool)
        requires
            self.wf(),
            self.get_free_ioids_as_set().contains(ioid) == false,
            0<=ioid<IOID_MAX,
            0<=bus<256 && 0<=dev<32 && 0<=fun<8,
        ensures
            ret =~= self.pci_bitmap@[(ioid, bus,dev,fun)],
    {
        return self.pci_bitmap.get(ioid, bus,dev,fun);
    }

    pub fn mmu_send_pci_dev_by_ioid(&mut self, ioid:IOid, bus:u8,dev:u8,fun:u8)
        requires
            old(self).wf(),
            old(self).get_free_ioids_as_set().contains(ioid) == false,
            0<=ioid<IOID_MAX,
            0<=bus<256 && 0<=dev<32 && 0<=fun<8,
        ensures
            self.wf(),
            self.get_free_ioids_as_set() =~= old(self).get_free_ioids_as_set(),
            self.get_free_pcids_as_set() =~= old(self).get_free_pcids_as_set(),
            self.get_mmu_page_closure() =~= old(self).get_mmu_page_closure(),
            forall|i:Pcid|#![auto] 0<=i<PCID_MAX ==> self.get_pagetable_mapping_by_pcid(i) =~= old(self).get_pagetable_mapping_by_pcid(i),
            forall|ioid:IOid| #![auto] 0<=ioid<IOID_MAX ==> self.get_iommutable_mapping_by_ioid(ioid) =~= old(self).get_iommutable_mapping_by_ioid(ioid),
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> self.get_pagetable_mapping_by_pcid(pcid)[va] =~= old(self).get_pagetable_mapping_by_pcid(pcid)[va],
            forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> self.get_iommutable_mapping_by_ioid(ioid)[va] =~= old(self).get_iommutable_mapping_by_ioid(ioid)[va],
            self.pci_bitmap@ =~= old(self).pci_bitmap@.insert((ioid, bus,dev,fun),true),
    {
        self.pci_bitmap.set(ioid, bus,dev,fun,true);

    }

    pub fn mmu_register_pci_dev(&mut self, ioid:IOid, bus:u8,dev:u8,fun:u8)
        requires
            old(self).wf(),
            old(self).get_free_ioids_as_set().contains(ioid) == false,
            0<=ioid<IOID_MAX,
            0<=bus<256 && 0<=dev<32 && 0<=fun<8,
            old(self).root_table.resolve(bus,dev,fun).is_None(),
            old(self).pci_bitmap@[(ioid, bus,dev,fun)] == true,
        ensures
            self.wf(),
            self.free_pcids =~= old(self).free_pcids,
            self.free_ioids =~= old(self).free_ioids,
            forall|_bus:u8,_dev:u8,_fun:u8|#![auto] 0<=_bus<256 && 0<=_dev<32 && 0<=_fun<8 &&
                (_bus != bus || _dev != dev || _fun != fun)
                ==> self.root_table.resolve(_bus,_dev,_fun) =~= old(self).root_table.resolve(_bus,_dev,_fun),
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> self.get_pagetable_mapping_by_pcid(pcid)[va] =~= old(self).get_pagetable_mapping_by_pcid(pcid)[va],
            forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> self.get_iommutable_mapping_by_ioid(ioid)[va] =~= old(self).get_iommutable_mapping_by_ioid(ioid)[va],
            self.get_mmu_page_closure() =~= old(self).get_mmu_page_closure(),
            self.root_table.resolve(bus,dev,fun).is_Some() && self.root_table.resolve(bus,dev,fun).get_Some_0().0 == ioid,
    {
        assert(self.root_table_cache@[bus as int][dev as int][fun as int].is_None());
        let cr3 = self.get_cr3_by_ioid(ioid);
        self.root_table.set(bus,dev,fun, Some((ioid,cr3)));
    }

}

}
