use vstd::prelude::*;
verus! {

// use vstd::ptr::PointsTo;
use crate::array_vec::ArrayVec;
use crate::define::*;
use crate::array::Array;
use crate::memory_manager::*;
use crate::pagetable::pagetable_spec_impl::PageTable;
use crate::pagetable::entry::*;
use crate::util::page_ptr_util_u::*;
use vstd::simple_pptr::PointsTo;
use crate::pagetable::pagemap::PageMap;
use crate::pagetable::pagemap_util_t::*;
use crate::lemma::lemma_u::*;
use crate::lemma::lemma_t::*;
use crate::allocator::page_allocator_spec_impl::PageAllocator;

pub struct MemoryManager {
    pub kernel_entries: Array<usize, KERNEL_MEM_END_L4INDEX>,
    pub kernel_entries_ghost: Ghost<Seq<PageEntry>>,
    pub free_pcids: ArrayVec<Pcid, PCID_MAX>,
    pub pcid_to_proc_ptr: Array<Option<ProcPtr>, PCID_MAX>,
    pub page_tables: Array<Option<PageTable>, PCID_MAX>,
    pub page_table_pages: Ghost<Map<PagePtr, Pcid>>,
    pub free_ioids: ArrayVec<IOid, IOID_MAX>,  //actual owners are procs
    pub ioid_to_proc_ptr: Array<Option<ProcPtr>, IOID_MAX>,
    pub iommu_tables: Array<Option<PageTable>, IOID_MAX>,
    pub iommu_table_pages: Ghost<Map<PagePtr, IOid>>,
    pub root_table: RootTable,
    pub root_table_cache: Ghost<Seq<Seq<Seq<Option<(IOid, usize)>>>>>,
    // pub device_table:MarsArray<MarsArray<Option<(u8,u8,u8)>,256>,IOID_MAX>,
    // pub ioid_device_table: Ghost<Seq<Set<(u8,u8,u8)>>>,
    pub pci_bitmap: PCIBitMap,
}

impl MemoryManager {
    pub open spec fn pcid_to_proc_ptr(&self, pcid: Pcid) -> ProcPtr
        recommends
            self.pcid_active(pcid),
    {
        self.pcid_to_proc_ptr@[pcid as int].unwrap()
    }

    pub open spec fn pcid_active(&self, pcid: Pcid) -> bool {
        &&& 0 <= pcid < PCID_MAX
        &&& self.get_free_pcids_as_set().contains(pcid) == false
    }

    pub open spec fn ioid_to_proc_ptr(&self, ioid: IOid) -> ProcPtr
        recommends
            self.ioid_active(ioid),
    {
        self.ioid_to_proc_ptr@[ioid as int].unwrap()
    }

    pub open spec fn ioid_active(&self, ioid: IOid) -> bool {
        &&& 0 <= ioid < IOID_MAX
        &&& self.get_free_ioids_as_set().contains(ioid) == false
    }

    pub open spec fn pagetables_wf(&self) -> bool {
        &&& self.free_pcids.wf()
        &&& self.free_pcids@.no_duplicates()
        &&& forall|i: int|
            #![trigger self.free_pcids@[i]]
            0 <= i < self.free_pcids.len() ==> self.free_pcids@[i] < PCID_MAX
        &&& self.page_tables.wf()
        &&& forall|pcid: Pcid|
            #![trigger self.page_tables@[pcid as int].unwrap()]
            0 <= pcid < PCID_MAX ==> self.page_tables@[pcid as int].is_Some() && (
            self.get_free_pcids_as_set().contains(pcid)
                ==> self.page_tables@[pcid as int].unwrap().is_empty())
                && self.page_tables@[pcid as int].unwrap().wf()
                && self.page_tables@[pcid as int].unwrap().pcid =~= Some(pcid)
                && self.page_tables@[pcid as int].unwrap().page_closure().subset_of(
                self.page_table_pages@.dom(),
            ) && self.page_tables@[pcid as int].unwrap().kernel_entries@
                =~= self.kernel_entries_ghost@
                && self.page_tables@[pcid as int].unwrap().kernel_l4_end
                == KERNEL_MEM_END_L4INDEX
            // for now, we disable hugepages
             && self.page_tables@[pcid as int].unwrap().mapping_2m().dom() == Set::<VAddr>::empty()
                && self.page_tables@[pcid as int].unwrap().mapping_1g().dom() == Set::<
                VAddr,
            >::empty()
        &&& forall|pcid_i: Pcid, pcid_j: Pcid|
            #![trigger self.page_tables@[pcid_i as int].unwrap().page_closure(), self.page_tables@[pcid_j as int].unwrap().page_closure()]
            0 <= pcid_i < PCID_MAX && 0 <= pcid_j < PCID_MAX && pcid_i != pcid_j
                ==> self.page_tables@[pcid_i as int].unwrap().page_closure().disjoint(
                self.page_tables@[pcid_j as int].unwrap().page_closure(),
            )
    }

    pub open spec fn iommutables_wf(&self) -> bool {
        &&& self.free_ioids.wf()
        &&& self.free_ioids@.no_duplicates()
        &&& forall|i: int|
            #![trigger self.free_ioids@[i]]
            0 <= i < self.free_ioids.len() ==> self.free_ioids@[i] < IOID_MAX
        &&& self.iommu_tables.wf()
        &&& forall|ioid: IOid|
            #![trigger self.iommu_tables@[ioid as int].unwrap()]
            0 <= ioid < IOID_MAX ==> self.iommu_tables@[ioid as int].is_Some() && (
            self.get_free_ioids_as_set().contains(ioid)
                ==> self.iommu_tables@[ioid as int].unwrap().is_empty())
                && self.iommu_tables@[ioid as int].unwrap().wf()
                && self.iommu_tables@[ioid as int].unwrap().ioid =~= Some(ioid)
                && self.iommu_tables@[ioid as int].unwrap().page_closure().subset_of(
                self.iommu_table_pages@.dom(),
            ) && self.iommu_tables@[ioid as int].unwrap().kernel_l4_end
                == 0  // for now, we disable hugepages
             && self.iommu_tables@[ioid as int].unwrap().mapping_2m().dom() == Set::<VAddr>::empty()
                && self.iommu_tables@[ioid as int].unwrap().mapping_1g().dom() == Set::<
                VAddr,
            >::empty()
        &&& forall|ioid_i: IOid, ioid_j: IOid|
            #![trigger self.iommu_tables@[ioid_i as int].unwrap().page_closure(), self.iommu_tables@[ioid_j as int].unwrap().page_closure()]
            0 <= ioid_i < IOID_MAX && 0 <= ioid_j < IOID_MAX && ioid_i != ioid_j
                ==> self.iommu_tables@[ioid_i as int].unwrap().page_closure().disjoint(
                self.iommu_tables@[ioid_j as int].unwrap().page_closure(),
            )
    }

    pub open spec fn no_memory_leak(&self) -> bool {
        &&&
        forall|p:PagePtr| 
         #![trigger self.page_table_pages@.dom().contains(p), self.page_table_pages@[p]]
            self.page_table_pages@.dom().contains(p)
            ==>
            0 <= self.page_table_pages@[p] < PCID_MAX
            &&
            self.get_pagetable_page_closure_by_pcid(self.page_table_pages@[p]).contains(p)
        &&&
        forall|p:PagePtr| 
         #![trigger self.iommu_table_pages@.dom().contains(p), self.iommu_table_pages@[p]]
            self.iommu_table_pages@.dom().contains(p)
            ==>
            0 <= self.iommu_table_pages@[p] < IOID_MAX
            &&
            self.get_iommu_table_page_closure_by_ioid(self.iommu_table_pages@[p]).contains(p)
    }

    pub open spec fn pagetable_iommu_table_disjoint(&self) -> bool {
        self.page_table_pages@.dom().disjoint(self.iommu_table_pages@.dom())
    }

    pub open spec fn kernel_entries_wf(&self) -> bool {
        &&& self.kernel_entries.wf()
        &&& self.kernel_entries_ghost@.len() == KERNEL_MEM_END_L4INDEX
        &&& forall|i: int|
            #![trigger self.kernel_entries@[i]]
            #![trigger self.kernel_entries_ghost@[i]]
            0 <= i < KERNEL_MEM_END_L4INDEX ==> self.kernel_entries_ghost@[i] =~= usize2page_entry(
                self.kernel_entries@[i],
            )
    }

    /// @Xiangdong TODO fix
    pub open spec fn root_table_wf(&self) -> bool {
        &&& self.root_table.wf()
        &&& self.pci_bitmap.wf()
        // &&& forall|bus: u8, dev: u8, fun: u8|
        //     #![auto]
        //     0 <= bus < 256 && 0 <= dev < 32 && 0 <= fun < 8 && self.root_table.resolve(
        //         bus,
        //         dev,
        //         fun,
        //     ).is_Some() ==> 0 <= self.root_table.resolve(bus, dev, fun).get_Some_0().0 < IOID_MAX
        //         && self.get_free_ioids_as_set().contains(
        //         self.root_table.resolve(bus, dev, fun).get_Some_0().0,
        //     ) == false && self.root_table.resolve(bus, dev, fun).get_Some_0().1
        //         == self.get_iommu_table_by_ioid(
        //         self.root_table.resolve(bus, dev, fun).get_Some_0().0,
        //     ).unwrap().cr3
        // &&& forall|bus: u8, dev: u8, fun: u8|
        //     #![auto]
        //     0 <= bus < 256 && 0 <= dev < 32 && 0 <= fun < 8 && self.root_table.resolve(
        //         bus,
        //         dev,
        //         fun,
        //     ).is_Some() ==> self.pci_bitmap@[(
        //         self.root_table.resolve(bus, dev, fun).get_Some_0().0,
        //         bus,
        //         dev,
        //         fun,
        //     )] == true
        // &&& forall|ioid: IOid, bus: u8, dev: u8, fun: u8|
        //     #![auto]
        //     0 <= ioid < IOID_MAX && self.get_free_ioids_as_set().contains(ioid) && 0 <= bus < 256
        //         && 0 <= dev < 32 && 0 <= fun < 8 ==> self.pci_bitmap@[(ioid, bus, dev, fun)]
        //         == false
        // &&
        // self.ioid_device_table@.len() == IOID_MAX
        // &&
        // forall|ioid:Pcid| #![auto] 0<=ioid<IOID_MAX ==> self.ioid_device_table@[ioid as int].finite()
        // &&
        // forall|ioid:Pcid, i:int| #![auto] 0<=ioid<IOID_MAX && 0<=i<256 && self.device_table@[ioid as int]@[i].is_Some() ==>
        //     (
        //         0<=self.device_table@[ioid as int]@[i].get_Some_0().0<256
        //         &&
        //         0<=self.device_table@[ioid as int]@[i].get_Some_0().1<32
        //         &&
        //         0<=self.device_table@[ioid as int]@[i].get_Some_0().2<8
        //         // &&
        //         // self.ioid_device_table@[ioid as int].contains(self.device_table@[ioid as int]@[i].get_Some_0())
        //     )
        // &&
        // forall|ioid:Pcid, dev:(u8,u8,u8)| #![auto] 0<=ioid<IOID_MAX && self.ioid_device_table@[ioid as int].contains(dev) ==>
        //     (
        //         0<=dev.0<256
        //         &&
        //         0<=dev.1<32
        //         &&
        //         0<=dev.2<8
        //         &&
        //         exists|_ioid:Pcid, _i:int| #![auto] 0<=_ioid<IOID_MAX && 0<=_i<256 && self.device_table@[ioid as int]@[i].is_Some() && dev =~= self.device_table@[ioid as int]@[i].get_Some_0()
        //     )
        // &&
        // forall|ioid:Pcid, i:int, j:int| #![auto] 0<=ioid<IOID_MAX && 0<=i<256 && 0<=j<256 && self.device_table@[ioid as int]@[i].is_Some() && self.device_table@[ioid as int]@[j].is_Some()==>
        // (
        //     self.device_table@[ioid as int]@[i].get_Some_0() =~= self.device_table@[ioid as int]@[j].get_Some_0() == false
        // )
        // &&
        // forall|bus:u8,dev:u8,fun:u8|#![auto] 0<=bus<256 && 0<=dev<32 && 0<=fun<8 && self.root_table.resolve(bus,dev,fun).is_Some() ==>
        //     (
        //         exists|i:int|#![auto]  0<i<256 && self.device_table@[self.root_table.resolve(bus,dev,fun).get_Some_0().0 as int][i].is_Some()
        //             && self.device_table@[self.root_table.resolve(bus,dev,fun).get_Some_0().0 as int][i].get_Some_0() =~= (bus,dev,fun)
        //     )

    }

    pub open spec fn root_table_cache_wf(&self) -> bool {
        &&& self.root_table_cache@.len() == 256
        &&& forall|bus: u8|
            #![auto]
            0 <= bus < 256 ==> self.root_table_cache@[bus as int].len() == 32
        &&& forall|bus: u8, dev: u8|
            #![auto]
            0 <= bus < 256 && 0 <= dev < 32 ==> self.root_table_cache@[bus as int][dev as int].len()
                == 8
        &&& forall|bus: u8, dev: u8, fun: u8|
            #![auto]
            0 <= bus < 256 && 0 <= dev < 32 && 0 <= fun < 8
                && self.root_table_cache@[bus as int][dev as int][fun as int].is_Some()
                ==> self.root_table_cache@[bus as int][dev as int][fun as int]
                =~= self.root_table.resolve(bus, dev, fun)
    }

    pub open spec fn page_closure(&self) -> Set<PagePtr> {
        self.iommu_table_pages@.dom() + self.page_table_pages@.dom()
    }

    pub open spec fn get_pagetable_by_pcid(&self, pcid: Pcid) -> Option<PageTable>
        recommends
            0 <= pcid < PCID_MAX,
    {
        self.page_tables@[pcid as int]
    }

    pub open spec fn get_pagetable_mapping_by_pcid(&self, pcid: Pcid) -> Map<VAddr, MapEntry>
        recommends
            0 <= pcid < PCID_MAX,
            self.get_pagetable_by_pcid(pcid).is_Some(),
    {
        self.page_tables@[pcid as int].unwrap().mapping_4k()
    }

    pub open spec fn get_pagetable_page_closure_by_pcid(&self, pcid: Pcid) -> Set<PagePtr>
        recommends
            0 <= pcid < PCID_MAX,
            self.get_pagetable_by_pcid(pcid).is_Some(),
    {
        self.page_tables[pcid as int].unwrap().page_closure()
    }

    pub open spec fn get_free_pcids_as_set(&self) -> Set<IOid> {
        self.free_pcids@.to_set()
    }

    pub open spec fn get_free_ioids_as_set(&self) -> Set<IOid> {
        self.free_ioids@.to_set()
    }

    pub open spec fn get_iommu_table_by_ioid(&self, ioid: IOid) -> Option<PageTable>
        recommends
            0 <= ioid < IOID_MAX,
    {
        self.iommu_tables[ioid as int]
    }

    pub open spec fn get_iommu_table_mapping_by_ioid(&self, ioid: IOid) -> Map<VAddr, MapEntry>
        recommends
            0 <= ioid < IOID_MAX,
            self.get_iommu_table_by_ioid(ioid).is_Some(),
    {
        self.iommu_tables[ioid as int].unwrap().mapping_4k()
    }

    pub open spec fn get_iommu_table_page_closure_by_ioid(&self, ioid: IOid) -> Set<PagePtr>
        recommends
            0 <= ioid < IOID_MAX,
            self.get_iommu_table_by_ioid(ioid).is_Some(),
    {
        self.iommu_tables[ioid as int].unwrap().page_closure()
    }

    pub fn get_cr3_by_pcid(&self, pcid: Pcid) -> (ret: usize)
        requires
            self.wf(),
            0 <= pcid < PCID_MAX,
            self.get_free_pcids_as_set().contains(pcid) == false,
    {
        return self.page_tables.get(pcid).as_ref().unwrap().cr3;
    }

    pub fn get_cr3_by_ioid(&self, ioid: IOid) -> (ret: usize)
        requires
            self.wf(),
            0 <= ioid < IOID_MAX,
            self.get_free_ioids_as_set().contains(ioid) == false,
            self.get_iommu_table_by_ioid(ioid).is_Some(),
        ensures
            self.get_iommu_table_by_ioid(ioid).unwrap().cr3 == ret,
    {
        return self.iommu_tables.get(ioid).as_ref().unwrap().cr3;
    }

    pub fn get_pci_binding(&self, bus: u8, dev: u8, fun: u8) -> (ret: Option<(IOid, usize)>)
        requires
            0 <= bus < 256 && 0 <= dev < 32 && 0 <= fun < 8,
            self.wf(),
        ensures
            ret =~= self.root_table.resolve(bus, dev, fun),
    {
        return self.root_table.get_ioid(bus, dev, fun);
    }

    pub open spec fn pcid_to_proc_wf(&self) -> bool {
        &&& self.pcid_to_proc_ptr.wf()
        &&& forall|pcid: Pcid|
            #![trigger self.pcid_active(pcid)]
            #![trigger self.pcid_to_proc_ptr@[pcid as int]]
            0 <= pcid < PCID_MAX ==> self.pcid_active(pcid)
                == self.pcid_to_proc_ptr@[pcid as int].is_Some()
    }

    pub open spec fn ioid_to_proc_wf(&self) -> bool {
        &&& self.ioid_to_proc_ptr.wf()
        &&& forall|ioid: IOid|
            #![trigger self.ioid_active(ioid)]
            #![trigger self.ioid_to_proc_ptr@[ioid as int]]
            0 <= ioid < IOID_MAX ==> self.ioid_active(ioid)
                == self.ioid_to_proc_ptr@[ioid as int].is_Some()
    }

    // #[verifier(inline)]
    pub open spec fn wf(&self) -> bool {
        &&& self.pagetables_wf()
        &&& self.iommutables_wf()
        &&& self.pagetable_iommu_table_disjoint()
        &&& self.root_table_wf()
        &&& self.root_table_cache_wf()
        &&& self.kernel_entries_wf()
        &&& self.pcid_to_proc_wf()
        &&& self.ioid_to_proc_wf()
        &&& self.no_memory_leak()
    }

    #[verifier(external_body)]
    pub fn new() -> (ret: Self) {
        Self {
            kernel_entries: Array::<usize, KERNEL_MEM_END_L4INDEX>::new(),
            kernel_entries_ghost: Ghost(Seq::<PageEntry>::empty()),
            free_pcids: ArrayVec::<Pcid, PCID_MAX>::new(),
            pcid_to_proc_ptr: Array::<Option<ProcPtr>, PCID_MAX>::new(),
            page_tables: Array::<Option<PageTable>, PCID_MAX>::new(),
            page_table_pages: Ghost(Map::<PagePtr, Pcid>::empty()),
            free_ioids: ArrayVec::<IOid, IOID_MAX>::new(),  //actual owners are procs
            ioid_to_proc_ptr: Array::<Option<ProcPtr>, IOID_MAX>::new(),
            iommu_tables: Array::<Option<PageTable>, IOID_MAX>::new(),
            iommu_table_pages: Ghost(Map::<PagePtr, IOid>::empty()),
            root_table: RootTable::new(),
            root_table_cache: Ghost(Seq::<Seq<Seq<Option<(IOid, usize)>>>>::empty()),
            // pub device_table:MarsArray<MarsArray<Option<(u8,u8,u8)>,256>,IOID_MAX>,
            // pub ioid_device_table: Ghost<Seq<Set<(u8,u8,u8)>>>,
            pci_bitmap: PCIBitMap::new(),
        }
    }

    pub fn get_pagetable_l4_entry(&self, pcid: Pcid, l4i: L4Index) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            KERNEL_MEM_END_L4INDEX <= l4i < 512,
            self.pcid_active(pcid),
        ensures
            ret =~= self.get_pagetable_by_pcid(pcid).unwrap().spec_resolve_mapping_l4(l4i),
            forall|l3i: L3Index, l2i: L2Index, l1i: L1Index|
                #![trigger spec_index2va((l4i, l3i, l2i, l1i))]
                #![trigger self.page_tables@[pcid as int].unwrap().spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 && ret.is_None()
                    ==> self.get_pagetable_by_pcid(pcid).unwrap().spec_resolve_mapping_4k_l1(
                    l4i,
                    l3i,
                    l2i,
                    l1i,
                ).is_None() && self.get_pagetable_by_pcid(
                    pcid,
                ).unwrap().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                    == false,
    {
        proof {
            va_lemma();
        }
        let ret = self.page_tables.get(pcid).as_ref().unwrap().get_entry_l4(l4i);
        assert(self.page_tables@[pcid as int].unwrap().spec_resolve_mapping_l4(l4i) == ret);
        assert(forall|l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger spec_index2va((l4i, l3i, l2i, l1i))]
            #![trigger self.page_tables@[pcid as int].unwrap().spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
            0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 && ret.is_None()
                ==> self.page_tables@[pcid as int].unwrap().spec_resolve_mapping_4k_l1(
                l4i,
                l3i,
                l2i,
                l1i,
            ).is_None() && self.page_tables@[pcid as int].unwrap().mapping_4k().dom().contains(
                spec_index2va((l4i, l3i, l2i, l1i)),
            ) == false);
        return ret;
    }

    pub fn get_iommu_table_l4_entry(&self, ioid: IOid, l4i: L4Index) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            0 <= l4i < 512,
            self.ioid_active(ioid),
        ensures
            ret =~= self.get_iommu_table_by_ioid(ioid).unwrap().spec_resolve_mapping_l4(l4i),
            forall|l3i: L3Index, l2i: L2Index, l1i: L1Index|
                #![trigger spec_index2va((l4i, l3i, l2i, l1i))]
                #![trigger self.iommu_tables@[ioid as int].unwrap().spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 && ret.is_None()
                    ==> self.get_iommu_table_by_ioid(ioid).unwrap().spec_resolve_mapping_4k_l1(
                    l4i,
                    l3i,
                    l2i,
                    l1i,
                ).is_None() && self.get_iommu_table_by_ioid(
                    ioid,
                ).unwrap().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                    == false,
    {
        proof {
            va_lemma();
        }
        let ret = self.iommu_tables.get(ioid).as_ref().unwrap().get_entry_l4(l4i);
        assert(self.iommu_tables@[ioid as int].unwrap().spec_resolve_mapping_l4(l4i) == ret);
        assert(forall|l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger spec_index2va((l4i, l3i, l2i, l1i))]
            #![trigger self.iommu_tables@[ioid as int].unwrap().spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
            0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 && ret.is_None()
                ==> self.iommu_tables@[ioid as int].unwrap().spec_resolve_mapping_4k_l1(
                l4i,
                l3i,
                l2i,
                l1i,
            ).is_None() && self.iommu_tables@[ioid as int].unwrap().mapping_4k().dom().contains(
                spec_index2va((l4i, l3i, l2i, l1i)),
            ) == false);
        return ret;
    }

    pub fn create_pagetable_l4_entry(
        &mut self,
        target_pcid: Pcid,
        target_l4i: L4Index,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    )
        requires
            old(self).wf(),
            old(self).pcid_active(target_pcid),
            KERNEL_MEM_END_L4INDEX <= target_l4i < 512,
            old(self).get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_l4(
                target_l4i,
            ).is_None(),
            page_ptr_valid(page_map_ptr),
            old(self).page_closure().contains(page_map_ptr) == false,
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0 <= i < 512 ==> page_map_perm.value()[i].is_empty(),
            forall|pcid: Pcid, va: VAddr|
                #![trigger old(self).get_pagetable_mapping_by_pcid(pcid).dom().contains(va)]
                #![trigger old(self).get_pagetable_mapping_by_pcid(pcid)[va]]
                old(self).pcid_active(pcid) && old(self).get_pagetable_mapping_by_pcid(
                    pcid,
                ).dom().contains(va) ==> old(self).get_pagetable_mapping_by_pcid(pcid)[va].addr
                    != page_map_ptr,
        ensures
            self.wf(),
            self.kernel_entries =~= old(self).kernel_entries,
            self.kernel_entries_ghost =~= old(self).kernel_entries_ghost,
            self.free_pcids =~= old(self).free_pcids,
            // self.page_tables =~= old(self).page_tables,
            // self.page_table_pages =~= old(self).page_table_pages,
            self.free_ioids =~= old(self).free_ioids,
            self.iommu_tables =~= old(self).iommu_tables,
            self.iommu_table_pages =~= old(self).iommu_table_pages,
            self.root_table =~= old(self).root_table,
            self.root_table_cache =~= old(self).root_table_cache,
            self.pci_bitmap =~= old(self).pci_bitmap,
            self.page_table_pages@.dom() =~= old(self).page_table_pages@.dom().insert(page_map_ptr),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                self.pcid_active(p) == old(self).pcid_active(p),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.get_pagetable_mapping_by_pcid(p)]
                self.pcid_active(p) ==> old(self).get_pagetable_mapping_by_pcid(p)
                    == self.get_pagetable_mapping_by_pcid(p),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                #![trigger self.get_iommu_table_mapping_by_ioid(i)]
                self.ioid_active(i) ==> old(self).get_iommu_table_mapping_by_ioid(i)
                    == self.get_iommu_table_mapping_by_ioid(i),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.pcid_to_proc_ptr(p)]
                self.pcid_active(p) ==> old(self).pcid_to_proc_ptr(p) == self.pcid_to_proc_ptr(p),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                self.ioid_active(i) == old(self).ioid_active(i),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                #![trigger self.ioid_to_proc_ptr(i)]
                self.ioid_active(i) ==> old(self).ioid_to_proc_ptr(i) == self.ioid_to_proc_ptr(i),
            self.get_pagetable_by_pcid(target_pcid).is_Some(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().wf(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().pcid == old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().pcid,
            self.get_pagetable_by_pcid(target_pcid).unwrap().kernel_l4_end == old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().kernel_l4_end,
            self.get_pagetable_by_pcid(target_pcid).unwrap().page_closure() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().page_closure().insert(page_map_ptr),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapping_4k() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapping_4k(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapping_2m() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapping_2m(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapping_1g() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapping_1g(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapped_4k_pages() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapped_4k_pages(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapped_2m_pages() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapped_2m_pages(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapped_1g_pages() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapped_1g_pages(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_l4(
                target_l4i,
            ).is_Some(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_l4(
                target_l4i,
            ).get_Some_0().addr == page_map_ptr,
            self.get_pagetable_by_pcid(target_pcid).unwrap().kernel_entries =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().kernel_entries,
    {
        assert(old(self).get_pagetable_mapping_by_pcid(target_pcid) =~= old(
            self,
        ).page_tables@[target_pcid as int].unwrap().mapping_4k());
        assert(forall|va: VAddr|
            #![trigger old(self).page_tables@[target_pcid as int].unwrap().mapping_4k().dom().contains(va)]
            #![trigger old(self).page_tables@[target_pcid as int].unwrap().mapping_4k()[va]]
            old(self).page_tables@[target_pcid as int].unwrap().mapping_4k().dom().contains(va)
                ==> old(self).page_tables@[target_pcid as int].unwrap().mapping_4k()[va].addr
                != page_map_ptr);
        assert(forall|va: VAddr|
            #![trigger old(self).page_tables@[target_pcid as int].unwrap().mapping_2m().dom().contains(va)]
            #![trigger old(self).page_tables@[target_pcid as int].unwrap().mapping_2m()[va]]
            old(self).page_tables@[target_pcid as int].unwrap().mapping_2m().dom().contains(va)
                ==> old(self).page_tables@[target_pcid as int].unwrap().mapping_2m()[va].addr
                != page_map_ptr);
        assert(forall|va: VAddr|
            #![trigger old(self).page_tables@[target_pcid as int].unwrap().mapping_1g().dom().contains(va)]
            #![trigger old(self).page_tables@[target_pcid as int].unwrap().mapping_1g()[va]]
            old(self).page_tables@[target_pcid as int].unwrap().mapping_1g().dom().contains(va)
                ==> old(self).page_tables@[target_pcid as int].unwrap().mapping_1g()[va].addr
                != page_map_ptr);

        assert(self.get_pagetable_by_pcid(target_pcid).is_Some());
        assert(self.get_pagetable_by_pcid(target_pcid).unwrap().wf());
        proof {
            self.get_pagetable_by_pcid(target_pcid).unwrap().no_mapping_infer_not_mapped(
                page_map_ptr,
            );
        }
        self.page_tables.pagetable_array_create_pagetable_l4_entry_t(
            target_pcid,
            target_l4i,
            page_map_ptr,
            Tracked(page_map_perm),
        );
        proof {
            self.page_table_pages@ = self.page_table_pages@.insert(page_map_ptr, target_pcid);
        }
        assert(self.wf()) by {
            assert(self.pagetables_wf()) by {
                assert(forall|pcid: Pcid|
                    #![trigger self.page_tables@[pcid as int]]
                    #![trigger self.get_free_pcids_as_set().contains(pcid)]
                    0 <= pcid < PCID_MAX ==> self.page_tables@[pcid as int].is_Some() && (
                    self.get_free_pcids_as_set().contains(pcid)
                        ==> self.page_tables@[pcid as int].unwrap().is_empty()));
            };
            assert(self.iommutables_wf());
            assert(self.pagetable_iommu_table_disjoint());
            assert(self.root_table_wf());
            assert(self.root_table_cache_wf());
            assert(self.kernel_entries_wf());
        };
    }

    pub fn create_iommu_table_l4_entry(
        &mut self,
        target_ioid: IOid,
        target_l4i: L4Index,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    )
        requires
            old(self).wf(),
            old(self).ioid_active(target_ioid),
            0 <= target_l4i < 512,
            old(self).get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_l4(
                target_l4i,
            ).is_None(),
            page_ptr_valid(page_map_ptr),
            old(self).page_closure().contains(page_map_ptr) == false,
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0 <= i < 512 ==> page_map_perm.value()[i].is_empty(),
            forall|ioid: IOid, va: VAddr|
                #![trigger old(self).get_iommu_table_mapping_by_ioid(ioid).dom().contains(va)]
                #![trigger old(self).get_iommu_table_mapping_by_ioid(ioid)[va]]
                old(self).ioid_active(ioid) && old(self).get_iommu_table_mapping_by_ioid(
                    ioid,
                ).dom().contains(va) ==> old(self).get_iommu_table_mapping_by_ioid(ioid)[va].addr
                    != page_map_ptr,
        ensures
            self.wf(),
            self.kernel_entries =~= old(self).kernel_entries,
            self.kernel_entries_ghost =~= old(self).kernel_entries_ghost,
            self.free_ioids =~= old(self).free_ioids,
            // self.iommu_tables =~= old(self).iommu_tables,
            // self.iommu_table_pages =~= old(self).iommu_table_pages,
            self.free_ioids =~= old(self).free_ioids,
            self.page_tables =~= old(self).page_tables,
            self.page_table_pages =~= old(self).page_table_pages,
            self.root_table =~= old(self).root_table,
            self.root_table_cache =~= old(self).root_table_cache,
            self.pci_bitmap =~= old(self).pci_bitmap,
            self.iommu_table_pages@.dom() =~= old(self).iommu_table_pages@.dom().insert(page_map_ptr),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                self.pcid_active(p) == old(self).pcid_active(p),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.pcid_to_proc_ptr(p)]
                self.pcid_active(p) ==> old(self).pcid_to_proc_ptr(p) == self.pcid_to_proc_ptr(p),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                self.ioid_active(i) == old(self).ioid_active(i),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                self.ioid_active(i) ==> old(self).ioid_to_proc_ptr(i) == self.ioid_to_proc_ptr(i),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                #![trigger self.get_iommu_table_mapping_by_ioid(i)]
                self.ioid_active(i) ==> old(self).get_iommu_table_mapping_by_ioid(i)
                    == self.get_iommu_table_mapping_by_ioid(i),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.get_pagetable_mapping_by_pcid(p)]
                self.pcid_active(p) ==> old(self).get_pagetable_mapping_by_pcid(p)
                    == self.get_pagetable_mapping_by_pcid(p),
            self.get_iommu_table_by_ioid(target_ioid).is_Some(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().wf(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().ioid == old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().ioid,
            self.get_iommu_table_by_ioid(target_ioid).unwrap().kernel_l4_end == old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().kernel_l4_end,
            self.get_iommu_table_by_ioid(target_ioid).unwrap().page_closure() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().page_closure().insert(page_map_ptr),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapping_4k() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapping_4k(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapping_2m() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapping_2m(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapping_1g() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapping_1g(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapped_4k_pages() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapped_4k_pages(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapped_2m_pages() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapped_2m_pages(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapped_1g_pages() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapped_1g_pages(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_l4(
                target_l4i,
            ).is_Some(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_l4(
                target_l4i,
            ).get_Some_0().addr == page_map_ptr,
            self.get_iommu_table_by_ioid(target_ioid).unwrap().kernel_entries =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().kernel_entries,
    {
        assert(old(self).get_iommu_table_mapping_by_ioid(target_ioid) =~= old(
            self,
        ).iommu_tables@[target_ioid as int].unwrap().mapping_4k());
        assert(forall|va: VAddr|
            #![trigger old(self).iommu_tables@[target_ioid as int].unwrap().mapping_4k().dom().contains(va)]
            #![trigger old(self).iommu_tables@[target_ioid as int].unwrap().mapping_4k()[va]]
            old(self).iommu_tables@[target_ioid as int].unwrap().mapping_4k().dom().contains(va)
                ==> old(self).iommu_tables@[target_ioid as int].unwrap().mapping_4k()[va].addr
                != page_map_ptr);
        assert(forall|va: VAddr|
            #![trigger old(self).iommu_tables@[target_ioid as int].unwrap().mapping_2m().dom().contains(va)]
            #![trigger old(self).iommu_tables@[target_ioid as int].unwrap().mapping_2m()[va]]
            old(self).iommu_tables@[target_ioid as int].unwrap().mapping_2m().dom().contains(va)
                ==> old(self).iommu_tables@[target_ioid as int].unwrap().mapping_2m()[va].addr
                != page_map_ptr);
        assert(forall|va: VAddr|
            #![trigger old(self).iommu_tables@[target_ioid as int].unwrap().mapping_1g().dom().contains(va)]
            #![trigger old(self).iommu_tables@[target_ioid as int].unwrap().mapping_1g()[va]]
            old(self).iommu_tables@[target_ioid as int].unwrap().mapping_1g().dom().contains(va)
                ==> old(self).iommu_tables@[target_ioid as int].unwrap().mapping_1g()[va].addr
                != page_map_ptr);

        assert(self.get_iommu_table_by_ioid(target_ioid).is_Some());
        assert(self.get_iommu_table_by_ioid(target_ioid).unwrap().wf());
        proof {
            self.get_iommu_table_by_ioid(target_ioid).unwrap().no_mapping_infer_not_mapped(
                page_map_ptr,
            );
        }
        self.iommu_tables.iommu_table_array_create_iommu_table_l4_entry_t(
            target_ioid,
            target_l4i,
            page_map_ptr,
            Tracked(page_map_perm),
        );
        proof {
            self.iommu_table_pages@ = self.iommu_table_pages@.insert(page_map_ptr, target_ioid);
        }
        assert(self.wf()) by {
            assert(self.iommutables_wf()) by {
                assert(forall|ioid: IOid|
                    #![trigger self.iommu_tables@[ioid as int]]
                    #![trigger self.get_free_ioids_as_set().contains(ioid)]
                    0 <= ioid < PCID_MAX ==> self.iommu_tables@[ioid as int].is_Some() && (
                    self.get_free_ioids_as_set().contains(ioid)
                        ==> self.iommu_tables@[ioid as int].unwrap().is_empty()));
            };

            assert(self.pagetables_wf());
            assert(self.pagetable_iommu_table_disjoint());
            assert(self.root_table_wf());
            assert(self.root_table_cache_wf());
            assert(self.kernel_entries_wf());
            assert(self.no_memory_leak());
        };
    }

    pub fn get_pagetable_l3_entry(
        &self,
        pcid: Pcid,
        target_l4i: L4Index,
        target_l3i: L3Index,
        l4_entry: &PageEntry,
    ) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            KERNEL_MEM_END_L4INDEX <= target_l4i < 512,
            0 <= target_l3i < 512,
            self.pcid_active(pcid),
            self.get_pagetable_by_pcid(pcid).unwrap().spec_resolve_mapping_l4(target_l4i) =~= Some(
                *l4_entry,
            ),
        ensures
            self.get_pagetable_by_pcid(pcid).unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ) =~= ret,
            ret.is_Some() ==> self.get_pagetable_by_pcid(pcid).unwrap().spec_resolve_mapping_1g_l3(
                target_l4i,
                target_l3i,
            ).is_None(),
            forall|l2i: L2Index, l1i: L1Index|
                #![trigger spec_index2va((target_l4i, target_l3i, l2i, l1i))]
                #![trigger self.get_pagetable_by_pcid(pcid).unwrap().spec_resolve_mapping_4k_l1(target_l4i, target_l3i, l2i, l1i)]
                0 <= l2i < 512 && 0 <= l1i < 512 && ret.is_None() ==> self.get_pagetable_by_pcid(
                    pcid,
                ).unwrap().spec_resolve_mapping_4k_l1(target_l4i, target_l3i, l2i, l1i).is_None()
                    && self.get_pagetable_by_pcid(pcid).unwrap().mapping_4k().dom().contains(
                    spec_index2va((target_l4i, target_l3i, l2i, l1i)),
                ) == false,
    {
        self.page_tables.get(pcid).as_ref().unwrap().get_entry_l3(target_l4i, target_l3i, l4_entry)
    }

    pub fn get_iommu_table_l3_entry(
        &self,
        ioid: IOid,
        target_l4i: L4Index,
        target_l3i: L3Index,
        l4_entry: &PageEntry,
    ) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            0 <= target_l4i < 512,
            0 <= target_l3i < 512,
            self.ioid_active(ioid),
            self.get_iommu_table_by_ioid(ioid).unwrap().spec_resolve_mapping_l4(target_l4i)
                =~= Some(*l4_entry),
        ensures
            self.get_iommu_table_by_ioid(ioid).unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ) =~= ret,
            ret.is_Some() ==> self.get_iommu_table_by_ioid(
                ioid,
            ).unwrap().spec_resolve_mapping_1g_l3(target_l4i, target_l3i).is_None(),
            forall|l2i: L2Index, l1i: L1Index|
                #![trigger spec_index2va((target_l4i, target_l3i, l2i, l1i))]
                #![trigger self.get_iommu_table_by_ioid(ioid).unwrap().spec_resolve_mapping_4k_l1(target_l4i, target_l3i, l2i, l1i)]
                0 <= l2i < 512 && 0 <= l1i < 512 && ret.is_None() ==> self.get_iommu_table_by_ioid(
                    ioid,
                ).unwrap().spec_resolve_mapping_4k_l1(target_l4i, target_l3i, l2i, l1i).is_None()
                    && self.get_iommu_table_by_ioid(ioid).unwrap().mapping_4k().dom().contains(
                    spec_index2va((target_l4i, target_l3i, l2i, l1i)),
                ) == false,
    {
        self.iommu_tables.get(ioid).as_ref().unwrap().get_entry_l3(target_l4i, target_l3i, l4_entry)
    }

    pub fn create_pagetable_l3_entry(
        &mut self,
        target_pcid: Pcid,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l3_p: PageMapPtr,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    )
        requires
            old(self).wf(),
            old(self).pcid_active(target_pcid),
            KERNEL_MEM_END_L4INDEX <= target_l4i < 512,
            0 <= target_l3i < 512,
            old(self).get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_l4(
                target_l4i,
            ).is_Some(),
            old(self).get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_l4(
                target_l4i,
            ).unwrap().addr == target_l3_p,
            page_ptr_valid(page_map_ptr),
            old(self).page_closure().contains(page_map_ptr) == false,
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0 <= i < 512 ==> page_map_perm.value()[i].is_empty(),
            forall|pcid: Pcid, va: VAddr|
                #![trigger old(self).get_pagetable_mapping_by_pcid(pcid).dom().contains(va)]
                #![trigger old(self).get_pagetable_mapping_by_pcid(pcid)[va]]
                old(self).pcid_active(pcid) && old(self).get_pagetable_mapping_by_pcid(
                    pcid,
                ).dom().contains(va) ==> old(self).get_pagetable_mapping_by_pcid(pcid)[va].addr
                    != page_map_ptr,
        ensures
            self.wf(),
            self.kernel_entries =~= old(self).kernel_entries,
            self.kernel_entries_ghost =~= old(self).kernel_entries_ghost,
            self.free_pcids =~= old(self).free_pcids,
            // self.page_tables =~= old(self).page_tables,
            // self.page_table_pages =~= old(self).page_table_pages,
            self.free_ioids =~= old(self).free_ioids,
            self.iommu_tables =~= old(self).iommu_tables,
            self.iommu_table_pages =~= old(self).iommu_table_pages,
            self.root_table =~= old(self).root_table,
            self.root_table_cache =~= old(self).root_table_cache,
            self.pci_bitmap =~= old(self).pci_bitmap,
            self.page_table_pages@.dom() =~= old(self).page_table_pages@.dom().insert(page_map_ptr),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                self.pcid_active(p) == old(self).pcid_active(p),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.get_pagetable_mapping_by_pcid(p)]
                self.pcid_active(p) ==> old(self).get_pagetable_mapping_by_pcid(p)
                    == self.get_pagetable_mapping_by_pcid(p),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                #![trigger self.get_iommu_table_mapping_by_ioid(i)]
                self.ioid_active(i) ==> old(self).get_iommu_table_mapping_by_ioid(i)
                    == self.get_iommu_table_mapping_by_ioid(i),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.pcid_to_proc_ptr(p)]
                self.pcid_active(p) ==> old(self).pcid_to_proc_ptr(p) == self.pcid_to_proc_ptr(p),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                self.ioid_active(i) == old(self).ioid_active(i),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                #![trigger self.ioid_to_proc_ptr(i)]
                self.ioid_active(i) ==> old(self).ioid_to_proc_ptr(i) == self.ioid_to_proc_ptr(i),
            self.get_pagetable_by_pcid(target_pcid).is_Some(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().wf(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().pcid == old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().pcid,
            self.get_pagetable_by_pcid(target_pcid).unwrap().kernel_l4_end == old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().kernel_l4_end,
            self.get_pagetable_by_pcid(target_pcid).unwrap().page_closure() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().page_closure().insert(page_map_ptr),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapping_4k() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapping_4k(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapping_2m() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapping_2m(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapping_1g() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapping_1g(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapped_4k_pages() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapped_4k_pages(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapped_2m_pages() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapped_2m_pages(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapped_1g_pages() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapped_1g_pages(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_l4(target_l4i)
                == old(self).get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_l4(
                target_l4i,
            ),
            self.get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ).is_Some(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ).get_Some_0().addr == page_map_ptr,
            self.get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_1g_l3(
                target_l4i,
                target_l3i,
            ).is_None(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().kernel_entries =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().kernel_entries,
    {
        assert(old(self).get_pagetable_mapping_by_pcid(target_pcid) =~= old(
            self,
        ).page_tables@[target_pcid as int].unwrap().mapping_4k());
        assert(forall|va: VAddr|
            #![trigger old(self).page_tables@[target_pcid as int].unwrap().mapping_4k().dom().contains(va)]
            #![trigger old(self).page_tables@[target_pcid as int].unwrap().mapping_4k()[va]]
            old(self).page_tables@[target_pcid as int].unwrap().mapping_4k().dom().contains(va)
                ==> old(self).page_tables@[target_pcid as int].unwrap().mapping_4k()[va].addr
                != page_map_ptr);
        assert(forall|va: VAddr|
            #![trigger old(self).page_tables@[target_pcid as int].unwrap().mapping_2m().dom().contains(va)]
            #![trigger old(self).page_tables@[target_pcid as int].unwrap().mapping_2m()[va]]
            old(self).page_tables@[target_pcid as int].unwrap().mapping_2m().dom().contains(va)
                ==> old(self).page_tables@[target_pcid as int].unwrap().mapping_2m()[va].addr
                != page_map_ptr);
        assert(forall|va: VAddr|
            #![trigger old(self).page_tables@[target_pcid as int].unwrap().mapping_1g().dom().contains(va)]
            #![trigger old(self).page_tables@[target_pcid as int].unwrap().mapping_1g()[va]]
            old(self).page_tables@[target_pcid as int].unwrap().mapping_1g().dom().contains(va)
                ==> old(self).page_tables@[target_pcid as int].unwrap().mapping_1g()[va].addr
                != page_map_ptr);

        assert(self.get_pagetable_by_pcid(target_pcid).is_Some());
        assert(self.get_pagetable_by_pcid(target_pcid).unwrap().wf());
        proof {
            self.get_pagetable_by_pcid(target_pcid).unwrap().no_mapping_infer_not_mapped(
                page_map_ptr,
            );
        }
        self.page_tables.pagetable_array_create_pagetable_l3_entry_t(
            target_pcid,
            target_l4i,
            target_l3i,
            target_l3_p,
            page_map_ptr,
            Tracked(page_map_perm),
        );
        proof {
            self.page_table_pages@ = self.page_table_pages@.insert(page_map_ptr, target_pcid);
        }
        assert(self.wf()) by {
            assert(self.pagetables_wf());
            assert(self.iommutables_wf());
            assert(self.pagetable_iommu_table_disjoint());
            assert(self.root_table_wf());
            assert(self.root_table_cache_wf());
            assert(self.kernel_entries_wf());
        };
    }

    pub fn create_iommu_table_l3_entry(
        &mut self,
        target_ioid: IOid,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l3_p: PageMapPtr,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    )
        requires
            old(self).wf(),
            old(self).ioid_active(target_ioid),
            0 <= target_l4i < 512,
            0 <= target_l3i < 512,
            old(self).get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_l4(
                target_l4i,
            ).is_Some(),
            old(self).get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_l4(
                target_l4i,
            ).unwrap().addr == target_l3_p,
            page_ptr_valid(page_map_ptr),
            old(self).page_closure().contains(page_map_ptr) == false,
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0 <= i < 512 ==> page_map_perm.value()[i].is_empty(),
            forall|ioid: IOid, va: VAddr|
                #![trigger old(self).get_iommu_table_mapping_by_ioid(ioid).dom().contains(va)]
                #![trigger old(self).get_iommu_table_mapping_by_ioid(ioid)[va]]
                old(self).ioid_active(ioid) && old(self).get_iommu_table_mapping_by_ioid(
                    ioid,
                ).dom().contains(va) ==> old(self).get_iommu_table_mapping_by_ioid(ioid)[va].addr
                    != page_map_ptr,
        ensures
            self.wf(),
            self.kernel_entries =~= old(self).kernel_entries,
            self.kernel_entries_ghost =~= old(self).kernel_entries_ghost,
            self.free_ioids =~= old(self).free_ioids,
            self.page_tables =~= old(self).page_tables,
            self.page_table_pages =~= old(self).page_table_pages,
            self.free_ioids =~= old(self).free_ioids,
            // self.iommu_tables =~= old(self).iommu_tables,
            // self.iommu_table_pages =~= old(self).iommu_table_pages,
            self.root_table =~= old(self).root_table,
            self.root_table_cache =~= old(self).root_table_cache,
            self.pci_bitmap =~= old(self).pci_bitmap,
            self.iommu_table_pages@.dom() =~= old(self).iommu_table_pages@.dom().insert(page_map_ptr),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                self.pcid_active(p) == old(self).pcid_active(p),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.pcid_to_proc_ptr(p)]
                self.pcid_active(p) ==> old(self).pcid_to_proc_ptr(p) == self.pcid_to_proc_ptr(p),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                self.ioid_active(i) == old(self).ioid_active(i),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                self.ioid_active(i) ==> old(self).ioid_to_proc_ptr(i) == self.ioid_to_proc_ptr(i),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                #![trigger self.get_iommu_table_mapping_by_ioid(i)]
                self.ioid_active(i) ==> old(self).get_iommu_table_mapping_by_ioid(i)
                    == self.get_iommu_table_mapping_by_ioid(i),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.get_pagetable_mapping_by_pcid(p)]
                self.pcid_active(p) ==> old(self).get_pagetable_mapping_by_pcid(p)
                    == self.get_pagetable_mapping_by_pcid(p),
            self.get_iommu_table_by_ioid(target_ioid).is_Some(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().wf(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().ioid == old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().ioid,
            self.get_iommu_table_by_ioid(target_ioid).unwrap().kernel_l4_end == old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().kernel_l4_end,
            self.get_iommu_table_by_ioid(target_ioid).unwrap().page_closure() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().page_closure().insert(page_map_ptr),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapping_4k() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapping_4k(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapping_2m() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapping_2m(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapping_1g() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapping_1g(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapped_4k_pages() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapped_4k_pages(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapped_2m_pages() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapped_2m_pages(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapped_1g_pages() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapped_1g_pages(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_l4(target_l4i)
                == old(self).get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_l4(
                target_l4i,
            ),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ).is_Some(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ).get_Some_0().addr == page_map_ptr,
            self.get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_1g_l3(
                target_l4i,
                target_l3i,
            ).is_None(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().kernel_entries =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().kernel_entries,
    {
        assert(old(self).get_iommu_table_mapping_by_ioid(target_ioid) =~= old(
            self,
        ).iommu_tables@[target_ioid as int].unwrap().mapping_4k());
        assert(forall|va: VAddr|
            #![trigger old(self).iommu_tables@[target_ioid as int].unwrap().mapping_4k().dom().contains(va)]
            #![trigger old(self).iommu_tables@[target_ioid as int].unwrap().mapping_4k()[va]]
            old(self).iommu_tables@[target_ioid as int].unwrap().mapping_4k().dom().contains(va)
                ==> old(self).iommu_tables@[target_ioid as int].unwrap().mapping_4k()[va].addr
                != page_map_ptr);
        assert(forall|va: VAddr|
            #![trigger old(self).iommu_tables@[target_ioid as int].unwrap().mapping_2m().dom().contains(va)]
            #![trigger old(self).iommu_tables@[target_ioid as int].unwrap().mapping_2m()[va]]
            old(self).iommu_tables@[target_ioid as int].unwrap().mapping_2m().dom().contains(va)
                ==> old(self).iommu_tables@[target_ioid as int].unwrap().mapping_2m()[va].addr
                != page_map_ptr);
        assert(forall|va: VAddr|
            #![trigger old(self).iommu_tables@[target_ioid as int].unwrap().mapping_1g().dom().contains(va)]
            #![trigger old(self).iommu_tables@[target_ioid as int].unwrap().mapping_1g()[va]]
            old(self).iommu_tables@[target_ioid as int].unwrap().mapping_1g().dom().contains(va)
                ==> old(self).iommu_tables@[target_ioid as int].unwrap().mapping_1g()[va].addr
                != page_map_ptr);

        assert(self.get_iommu_table_by_ioid(target_ioid).is_Some());
        assert(self.get_iommu_table_by_ioid(target_ioid).unwrap().wf());
        proof {
            self.get_iommu_table_by_ioid(target_ioid).unwrap().no_mapping_infer_not_mapped(
                page_map_ptr,
            );
        }
        self.iommu_tables.iommu_table_array_create_iommu_table_l3_entry_t(
            target_ioid,
            target_l4i,
            target_l3i,
            target_l3_p,
            page_map_ptr,
            Tracked(page_map_perm),
        );
        proof {
            self.iommu_table_pages@ = self.iommu_table_pages@.insert(page_map_ptr, target_ioid);
        }
        assert(self.wf()) by {
            assert(self.iommutables_wf());
            assert(self.pagetables_wf());
            assert(self.pagetable_iommu_table_disjoint());
            assert(self.root_table_wf());
            assert(self.root_table_cache_wf());
            assert(self.kernel_entries_wf());
        };
    }

    pub fn get_pagetable_l2_entry(
        &self,
        pcid: Pcid,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        l3_entry: &PageEntry,
    ) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.pcid_active(pcid),
            KERNEL_MEM_END_L4INDEX <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            self.get_pagetable_by_pcid(pcid).unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ) =~= Some(*l3_entry),
        ensures
            self.get_pagetable_by_pcid(pcid).unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ) =~= ret,
            forall|l1i: L1Index|
                #![trigger spec_index2va((target_l4i, target_l3i, target_l2i, l1i))]
                #![trigger self.get_pagetable_by_pcid(pcid).unwrap().spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, l1i)]
                0 <= l1i < 512 && ret.is_None() ==> self.get_pagetable_by_pcid(
                    pcid,
                ).unwrap().spec_resolve_mapping_4k_l1(
                    target_l4i,
                    target_l3i,
                    target_l2i,
                    l1i,
                ).is_None() && self.get_pagetable_by_pcid(
                    pcid,
                ).unwrap().mapping_4k().dom().contains(
                    spec_index2va((target_l4i, target_l3i, target_l2i, l1i)),
                ) == false,
    {
        self.page_tables.get(pcid).as_ref().unwrap().get_entry_l2(
            target_l4i,
            target_l3i,
            target_l2i,
            l3_entry,
        )
    }

    pub fn get_iommu_table_l2_entry(
        &self,
        ioid: IOid,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        l3_entry: &PageEntry,
    ) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.ioid_active(ioid),
            0 <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            self.get_iommu_table_by_ioid(ioid).unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ) =~= Some(*l3_entry),
        ensures
            self.get_iommu_table_by_ioid(ioid).unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ) =~= ret,
            forall|l1i: L1Index|
                #![trigger spec_index2va((target_l4i, target_l3i, target_l2i, l1i))]
                #![trigger self.get_iommu_table_by_ioid(ioid).unwrap().spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, l1i)]
                0 <= l1i < 512 && ret.is_None() ==> self.get_iommu_table_by_ioid(
                    ioid,
                ).unwrap().spec_resolve_mapping_4k_l1(
                    target_l4i,
                    target_l3i,
                    target_l2i,
                    l1i,
                ).is_None() && self.get_iommu_table_by_ioid(
                    ioid,
                ).unwrap().mapping_4k().dom().contains(
                    spec_index2va((target_l4i, target_l3i, target_l2i, l1i)),
                ) == false,
    {
        self.iommu_tables.get(ioid).as_ref().unwrap().get_entry_l2(
            target_l4i,
            target_l3i,
            target_l2i,
            l3_entry,
        )
    }

    pub fn get_pagetable_l1_entry(
        &self,
        pcid: Pcid,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l1i: L2Index,
        l2_entry: &PageEntry,
    ) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.pcid_active(pcid),
            KERNEL_MEM_END_L4INDEX <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            0 <= target_l1i < 512,
            self.get_pagetable_by_pcid(pcid).unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ) =~= Some(*l2_entry),
        ensures
            self.get_pagetable_by_pcid(pcid).unwrap().spec_resolve_mapping_4k_l1(
                target_l4i,
                target_l3i,
                target_l2i,
                target_l1i,
            ) =~= ret,
            self.get_pagetable_by_pcid(pcid).unwrap().mapping_4k().dom().contains(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ) =~= ret.is_Some(),
            ret.is_Some() ==> self.get_pagetable_by_pcid(pcid).unwrap().mapping_4k().dom().contains(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ) && self.get_pagetable_by_pcid(pcid).unwrap().mapping_4k()[spec_index2va(
                (target_l4i, target_l3i, target_l2i, target_l1i),
            )] == page_entry_to_map_entry(&ret.unwrap()),
    {
        self.page_tables.get(pcid).as_ref().unwrap().get_entry_l1(
            target_l4i,
            target_l3i,
            target_l2i,
            target_l1i,
            l2_entry,
        )
    }

    pub fn get_iommu_table_l1_entry(
        &self,
        ioid: IOid,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l1i: L2Index,
        l2_entry: &PageEntry,
    ) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.ioid_active(ioid),
            0 <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            0 <= target_l1i < 512,
            self.get_iommu_table_by_ioid(ioid).unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ) =~= Some(*l2_entry),
        ensures
            self.get_iommu_table_by_ioid(ioid).unwrap().spec_resolve_mapping_4k_l1(
                target_l4i,
                target_l3i,
                target_l2i,
                target_l1i,
            ) =~= ret,
            self.get_iommu_table_by_ioid(ioid).unwrap().mapping_4k().dom().contains(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ) =~= ret.is_Some(),
            ret.is_Some() ==> self.get_iommu_table_by_ioid(
                ioid,
            ).unwrap().mapping_4k().dom().contains(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ) && self.get_iommu_table_by_ioid(ioid).unwrap().mapping_4k()[spec_index2va(
                (target_l4i, target_l3i, target_l2i, target_l1i),
            )] == page_entry_to_map_entry(&ret.unwrap()),
    {
        self.iommu_tables.get(ioid).as_ref().unwrap().get_entry_l1(
            target_l4i,
            target_l3i,
            target_l2i,
            target_l1i,
            l2_entry,
        )
    }

    pub fn create_pagetable_l2_entry(
        &mut self,
        target_pcid: Pcid,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l2_p: PageMapPtr,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    )
        requires
            old(self).wf(),
            old(self).pcid_active(target_pcid),
            KERNEL_MEM_END_L4INDEX <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            old(self).get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ).is_Some(),
            old(self).get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_1g_l3(
                target_l4i,
                target_l3i,
            ).is_None(),
            old(self).get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ).unwrap().addr == target_l2_p,
            page_ptr_valid(page_map_ptr),
            old(self).page_closure().contains(page_map_ptr) == false,
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0 <= i < 512 ==> page_map_perm.value()[i].is_empty(),
            forall|pcid: Pcid, va: VAddr|
                #![trigger old(self).get_pagetable_mapping_by_pcid(pcid).dom().contains(va)]
                #![trigger old(self).get_pagetable_mapping_by_pcid(pcid)[va]]
                old(self).pcid_active(pcid) && old(self).get_pagetable_mapping_by_pcid(
                    pcid,
                ).dom().contains(va) ==> old(self).get_pagetable_mapping_by_pcid(pcid)[va].addr
                    != page_map_ptr,
        ensures
            self.wf(),
            self.kernel_entries =~= old(self).kernel_entries,
            self.kernel_entries_ghost =~= old(self).kernel_entries_ghost,
            self.free_pcids =~= old(self).free_pcids,
            // self.page_tables =~= old(self).page_tables,
            // self.page_table_pages =~= old(self).page_table_pages,
            self.free_ioids =~= old(self).free_ioids,
            self.iommu_tables =~= old(self).iommu_tables,
            self.iommu_table_pages =~= old(self).iommu_table_pages,
            self.root_table =~= old(self).root_table,
            self.root_table_cache =~= old(self).root_table_cache,
            self.pci_bitmap =~= old(self).pci_bitmap,
            self.page_table_pages@.dom() =~= old(self).page_table_pages@.dom().insert(page_map_ptr),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                self.pcid_active(p) == old(self).pcid_active(p),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.get_pagetable_mapping_by_pcid(p)]
                self.pcid_active(p) ==> old(self).get_pagetable_mapping_by_pcid(p)
                    == self.get_pagetable_mapping_by_pcid(p),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                #![trigger self.get_iommu_table_mapping_by_ioid(i)]
                self.ioid_active(i) ==> old(self).get_iommu_table_mapping_by_ioid(i)
                    == self.get_iommu_table_mapping_by_ioid(i),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.pcid_to_proc_ptr(p)]
                self.pcid_active(p) ==> old(self).pcid_to_proc_ptr(p) == self.pcid_to_proc_ptr(p),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                self.ioid_active(i) == old(self).ioid_active(i),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                #![trigger self.ioid_to_proc_ptr(i)]
                self.ioid_active(i) ==> old(self).ioid_to_proc_ptr(i) == self.ioid_to_proc_ptr(i),
            self.get_pagetable_by_pcid(target_pcid).is_Some(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().wf(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().pcid == old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().pcid,
            self.get_pagetable_by_pcid(target_pcid).unwrap().kernel_l4_end == old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().kernel_l4_end,
            self.get_pagetable_by_pcid(target_pcid).unwrap().page_closure() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().page_closure().insert(page_map_ptr),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapping_4k() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapping_4k(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapping_2m() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapping_2m(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapping_1g() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapping_1g(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapped_4k_pages() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapped_4k_pages(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapped_2m_pages() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapped_2m_pages(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapped_1g_pages() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapped_1g_pages(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_1g_l3(
                target_l4i,
                target_l3i,
            ) == old(self).get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_1g_l3(
                target_l4i,
                target_l3i,
            ),
            self.get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ) == old(self).get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ),
            self.get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).is_Some(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).get_Some_0().addr == page_map_ptr,
            self.get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_2m_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).is_None(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().kernel_entries =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().kernel_entries,
    {
        assert(old(self).get_pagetable_mapping_by_pcid(target_pcid) =~= old(
            self,
        ).page_tables@[target_pcid as int].unwrap().mapping_4k());
        assert(forall|va: VAddr|
            #![trigger old(self).page_tables@[target_pcid as int].unwrap().mapping_4k().dom().contains(va)]
            #![trigger old(self).page_tables@[target_pcid as int].unwrap().mapping_4k()[va]]
            old(self).page_tables@[target_pcid as int].unwrap().mapping_4k().dom().contains(va)
                ==> old(self).page_tables@[target_pcid as int].unwrap().mapping_4k()[va].addr
                != page_map_ptr);
        assert(forall|va: VAddr|
            #![trigger old(self).page_tables@[target_pcid as int].unwrap().mapping_2m().dom().contains(va)]
            #![trigger old(self).page_tables@[target_pcid as int].unwrap().mapping_2m()[va]]
            old(self).page_tables@[target_pcid as int].unwrap().mapping_2m().dom().contains(va)
                ==> old(self).page_tables@[target_pcid as int].unwrap().mapping_2m()[va].addr
                != page_map_ptr);
        assert(forall|va: VAddr|
            #![trigger old(self).page_tables@[target_pcid as int].unwrap().mapping_1g().dom().contains(va)]
            #![trigger old(self).page_tables@[target_pcid as int].unwrap().mapping_1g()[va]]
            old(self).page_tables@[target_pcid as int].unwrap().mapping_1g().dom().contains(va)
                ==> old(self).page_tables@[target_pcid as int].unwrap().mapping_1g()[va].addr
                != page_map_ptr);

        assert(self.get_pagetable_by_pcid(target_pcid).is_Some());
        assert(self.get_pagetable_by_pcid(target_pcid).unwrap().wf());
        proof {
            self.get_pagetable_by_pcid(target_pcid).unwrap().no_mapping_infer_not_mapped(
                page_map_ptr,
            );
        }
        self.page_tables.pagetable_array_create_pagetable_l2_entry_t(
            target_pcid,
            target_l4i,
            target_l3i,
            target_l2i,
            target_l2_p,
            page_map_ptr,
            Tracked(page_map_perm),
        );
        proof {
            self.page_table_pages@ = self.page_table_pages@.insert(page_map_ptr, target_pcid);
        }
        assert(self.wf()) by {
            assert(self.pagetables_wf());
            assert(self.iommutables_wf());
            assert(self.pagetable_iommu_table_disjoint());
            assert(self.root_table_wf());
            assert(self.root_table_cache_wf());
            assert(self.kernel_entries_wf());
        };
    }

    pub fn create_iommu_table_l2_entry(
        &mut self,
        target_ioid: IOid,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l2_p: PageMapPtr,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    )
        requires
            old(self).wf(),
            old(self).ioid_active(target_ioid),
            0 <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            old(self).get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ).is_Some(),
            old(self).get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_1g_l3(
                target_l4i,
                target_l3i,
            ).is_None(),
            old(self).get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ).unwrap().addr == target_l2_p,
            page_ptr_valid(page_map_ptr),
            old(self).page_closure().contains(page_map_ptr) == false,
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0 <= i < 512 ==> page_map_perm.value()[i].is_empty(),
            forall|ioid: IOid, va: VAddr|
                #![trigger old(self).get_iommu_table_mapping_by_ioid(ioid).dom().contains(va)]
                #![trigger old(self).get_iommu_table_mapping_by_ioid(ioid)[va]]
                old(self).ioid_active(ioid) && old(self).get_iommu_table_mapping_by_ioid(
                    ioid,
                ).dom().contains(va) ==> old(self).get_iommu_table_mapping_by_ioid(ioid)[va].addr
                    != page_map_ptr,
        ensures
            self.wf(),
            self.kernel_entries =~= old(self).kernel_entries,
            self.kernel_entries_ghost =~= old(self).kernel_entries_ghost,
            self.free_ioids =~= old(self).free_ioids,
            self.page_tables =~= old(self).page_tables,
            self.page_table_pages =~= old(self).page_table_pages,
            self.free_ioids =~= old(self).free_ioids,
            // self.iommu_tables =~= old(self).iommu_tables,
            // self.iommu_table_pages =~= old(self).iommu_table_pages,
            self.root_table =~= old(self).root_table,
            self.root_table_cache =~= old(self).root_table_cache,
            self.pci_bitmap =~= old(self).pci_bitmap,
            self.iommu_table_pages@.dom() =~= old(self).iommu_table_pages@.dom().insert(page_map_ptr),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                self.pcid_active(p) == old(self).pcid_active(p),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.pcid_to_proc_ptr(p)]
                self.pcid_active(p) ==> old(self).pcid_to_proc_ptr(p) == self.pcid_to_proc_ptr(p),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                self.ioid_active(i) == old(self).ioid_active(i),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                self.ioid_active(i) ==> old(self).ioid_to_proc_ptr(i) == self.ioid_to_proc_ptr(i),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                #![trigger self.get_iommu_table_mapping_by_ioid(i)]
                self.ioid_active(i) ==> old(self).get_iommu_table_mapping_by_ioid(i)
                    == self.get_iommu_table_mapping_by_ioid(i),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.get_pagetable_mapping_by_pcid(p)]
                self.pcid_active(p) ==> old(self).get_pagetable_mapping_by_pcid(p)
                    == self.get_pagetable_mapping_by_pcid(p),
            self.get_iommu_table_by_ioid(target_ioid).is_Some(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().wf(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().ioid == old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().ioid,
            self.get_iommu_table_by_ioid(target_ioid).unwrap().kernel_l4_end == old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().kernel_l4_end,
            self.get_iommu_table_by_ioid(target_ioid).unwrap().page_closure() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().page_closure().insert(page_map_ptr),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapping_4k() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapping_4k(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapping_2m() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapping_2m(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapping_1g() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapping_1g(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapped_4k_pages() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapped_4k_pages(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapped_2m_pages() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapped_2m_pages(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapped_1g_pages() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapped_1g_pages(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_1g_l3(
                target_l4i,
                target_l3i,
            ) == old(self).get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_1g_l3(
                target_l4i,
                target_l3i,
            ),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ) == old(self).get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).is_Some(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).get_Some_0().addr == page_map_ptr,
            self.get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_2m_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).is_None(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().kernel_entries =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().kernel_entries,
    {
        assert(old(self).get_iommu_table_mapping_by_ioid(target_ioid) =~= old(
            self,
        ).iommu_tables@[target_ioid as int].unwrap().mapping_4k());
        assert(forall|va: VAddr|
            #![trigger old(self).iommu_tables@[target_ioid as int].unwrap().mapping_4k().dom().contains(va)]
            #![trigger old(self).iommu_tables@[target_ioid as int].unwrap().mapping_4k()[va]]
            old(self).iommu_tables@[target_ioid as int].unwrap().mapping_4k().dom().contains(va)
                ==> old(self).iommu_tables@[target_ioid as int].unwrap().mapping_4k()[va].addr
                != page_map_ptr);
        assert(forall|va: VAddr|
            #![trigger old(self).iommu_tables@[target_ioid as int].unwrap().mapping_2m().dom().contains(va)]
            #![trigger old(self).iommu_tables@[target_ioid as int].unwrap().mapping_2m()[va]]
            old(self).iommu_tables@[target_ioid as int].unwrap().mapping_2m().dom().contains(va)
                ==> old(self).iommu_tables@[target_ioid as int].unwrap().mapping_2m()[va].addr
                != page_map_ptr);
        assert(forall|va: VAddr|
            #![trigger old(self).iommu_tables@[target_ioid as int].unwrap().mapping_1g().dom().contains(va)]
            #![trigger old(self).iommu_tables@[target_ioid as int].unwrap().mapping_1g()[va]]
            old(self).iommu_tables@[target_ioid as int].unwrap().mapping_1g().dom().contains(va)
                ==> old(self).iommu_tables@[target_ioid as int].unwrap().mapping_1g()[va].addr
                != page_map_ptr);

        assert(self.get_iommu_table_by_ioid(target_ioid).is_Some());
        assert(self.get_iommu_table_by_ioid(target_ioid).unwrap().wf());
        proof {
            self.get_iommu_table_by_ioid(target_ioid).unwrap().no_mapping_infer_not_mapped(
                page_map_ptr,
            );
        }
        self.iommu_tables.iommu_table_array_create_iommu_table_l2_entry_t(
            target_ioid,
            target_l4i,
            target_l3i,
            target_l2i,
            target_l2_p,
            page_map_ptr,
            Tracked(page_map_perm),
        );
        proof {
            self.iommu_table_pages@ = self.iommu_table_pages@.insert(page_map_ptr, target_ioid);
        }
        assert(self.wf()) by {
            assert(self.pagetables_wf());
            assert(self.iommutables_wf());
            assert(self.pagetable_iommu_table_disjoint());
            assert(self.root_table_wf());
            assert(self.root_table_cache_wf());
            assert(self.kernel_entries_wf());
        };
    }

    pub fn pagetable_map_4k_page(
        &mut self,
        target_pcid: Pcid,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l1i: L1Index,
        target_l1_p: PageMapPtr,
        target_entry: &MapEntry,
    )
        requires
            old(self).wf(),
            old(self).pcid_active(target_pcid),
            KERNEL_MEM_END_L4INDEX <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            0 <= target_l1i < 512,
            old(self).get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).is_Some(),
            old(self).get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).get_Some_0().addr == target_l1_p,
            old(self).get_pagetable_by_pcid(target_pcid).unwrap().spec_resolve_mapping_4k_l1(
                target_l4i,
                target_l3i,
                target_l2i,
                target_l1i,
            ).is_None() || old(self).get_pagetable_by_pcid(
                target_pcid,
            ).unwrap().mapping_4k().dom().contains(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ) == false,
            old(self).page_closure().contains(target_entry.addr) == false,
            page_ptr_valid(target_entry.addr),
        ensures
            self.wf(),
            self.kernel_entries =~= old(self).kernel_entries,
            self.kernel_entries_ghost =~= old(self).kernel_entries_ghost,
            self.free_pcids =~= old(self).free_pcids,
            // self.page_tables =~= old(self).page_tables,
            self.page_table_pages =~= old(self).page_table_pages,
            self.free_ioids =~= old(self).free_ioids,
            self.iommu_tables =~= old(self).iommu_tables,
            self.iommu_table_pages =~= old(self).iommu_table_pages,
            self.root_table =~= old(self).root_table,
            self.root_table_cache =~= old(self).root_table_cache,
            self.pci_bitmap =~= old(self).pci_bitmap,
            // self.page_table_pages@.dom() =~= old(self).page_table_pages@.dom().insert(page_map_ptr),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                self.pcid_active(p) == old(self).pcid_active(p),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.pcid_to_proc_ptr(p)]
                self.pcid_active(p) ==> old(self).pcid_to_proc_ptr(p) == self.pcid_to_proc_ptr(p),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.get_pagetable_mapping_by_pcid(p)]
                self.pcid_active(p) && p != target_pcid ==> old(self).get_pagetable_mapping_by_pcid(
                    p,
                ) == self.get_pagetable_mapping_by_pcid(p),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                self.ioid_active(i) == old(self).ioid_active(i),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                #![trigger self.ioid_to_proc_ptr(i)]
                self.ioid_active(i) ==> old(self).ioid_to_proc_ptr(i) == self.ioid_to_proc_ptr(i),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                #![trigger self.get_iommu_table_mapping_by_ioid(i)]
                self.ioid_active(i) ==> old(self).get_iommu_table_mapping_by_ioid(i)
                    == self.get_iommu_table_mapping_by_ioid(i),
            self.get_pagetable_by_pcid(target_pcid).is_Some(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().wf(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().pcid == old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().pcid,
            self.get_pagetable_by_pcid(target_pcid).unwrap().kernel_l4_end == old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().kernel_l4_end,
            self.get_pagetable_by_pcid(target_pcid).unwrap().page_closure() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().page_closure(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapping_4k() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapping_4k().insert(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
                *target_entry,
            ),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapping_2m() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapping_2m(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().mapping_1g() =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().mapping_1g(),
            self.get_pagetable_by_pcid(target_pcid).unwrap().kernel_entries =~= old(
                self,
            ).get_pagetable_by_pcid(target_pcid).unwrap().kernel_entries,
            self.get_pagetable_mapping_by_pcid(target_pcid) == old(
                self,
            ).get_pagetable_mapping_by_pcid(target_pcid).insert(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
                *target_entry,
            ),
            self.get_pagetable_mapping_by_pcid(target_pcid).dom() == old(
                self,
            ).get_pagetable_mapping_by_pcid(target_pcid).dom().insert(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ),
    {
        self.page_tables.pagetable_array_map_4k_page_t(
            target_pcid,
            target_l4i,
            target_l3i,
            target_l2i,
            target_l1i,
            target_l1_p,
            target_entry,
        );
        assert(self.wf()) by {
            assert(self.pagetables_wf());
            assert(self.iommutables_wf());
            assert(self.pagetable_iommu_table_disjoint());
            assert(self.root_table_wf());
            assert(self.root_table_cache_wf());
            assert(self.kernel_entries_wf());
        };
    }

    pub fn iommu_table_map_4k_page(
        &mut self,
        target_ioid: IOid,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l1i: L1Index,
        target_l1_p: PageMapPtr,
        target_entry: &MapEntry,
    )
        requires
            old(self).wf(),
            old(self).ioid_active(target_ioid),
            0 <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            0 <= target_l1i < 512,
            old(self).get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).is_Some(),
            old(self).get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).get_Some_0().addr == target_l1_p,
            old(self).get_iommu_table_by_ioid(target_ioid).unwrap().spec_resolve_mapping_4k_l1(
                target_l4i,
                target_l3i,
                target_l2i,
                target_l1i,
            ).is_None() || old(self).get_iommu_table_by_ioid(
                target_ioid,
            ).unwrap().mapping_4k().dom().contains(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ) == false,
            old(self).page_closure().contains(target_entry.addr) == false,
            page_ptr_valid(target_entry.addr),
        ensures
            self.wf(),
            self.kernel_entries =~= old(self).kernel_entries,
            self.kernel_entries_ghost =~= old(self).kernel_entries_ghost,
            self.free_pcids =~= old(self).free_pcids,
            self.page_tables =~= old(self).page_tables,
            self.page_table_pages =~= old(self).page_table_pages,
            self.free_ioids =~= old(self).free_ioids,
            // self.iommu_tables =~= old(self).iommu_tables,
            self.iommu_table_pages =~= old(self).iommu_table_pages,
            self.root_table =~= old(self).root_table,
            self.root_table_cache =~= old(self).root_table_cache,
            self.pci_bitmap =~= old(self).pci_bitmap,
            // self.page_table_pages@.dom() =~= old(self).page_table_pages@.dom().insert(page_map_ptr),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                self.pcid_active(p) == old(self).pcid_active(p),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.pcid_to_proc_ptr(p)]
                self.pcid_active(p) ==> old(self).pcid_to_proc_ptr(p) == self.pcid_to_proc_ptr(p),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                self.ioid_active(i) == old(self).ioid_active(i),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                self.ioid_active(i) ==> old(self).ioid_to_proc_ptr(i) == self.ioid_to_proc_ptr(i),
            forall|p: IOid|
                #![trigger self.ioid_active(p)]
                #![trigger self.get_iommu_table_mapping_by_ioid(p)]
                self.ioid_active(p) && p != target_ioid ==> old(
                    self,
                ).get_iommu_table_mapping_by_ioid(p) == self.get_iommu_table_mapping_by_ioid(p),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.get_pagetable_mapping_by_pcid(p)]
                self.pcid_active(p) ==> old(self).get_pagetable_mapping_by_pcid(p)
                    == self.get_pagetable_mapping_by_pcid(p),
            self.get_iommu_table_by_ioid(target_ioid).is_Some(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().wf(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().ioid == old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().ioid,
            self.get_iommu_table_by_ioid(target_ioid).unwrap().kernel_l4_end == old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().kernel_l4_end,
            self.get_iommu_table_by_ioid(target_ioid).unwrap().page_closure() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().page_closure(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapping_4k() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapping_4k().insert(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
                *target_entry,
            ),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapping_2m() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapping_2m(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().mapping_1g() =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().mapping_1g(),
            self.get_iommu_table_by_ioid(target_ioid).unwrap().kernel_entries =~= old(
                self,
            ).get_iommu_table_by_ioid(target_ioid).unwrap().kernel_entries,
            self.get_iommu_table_mapping_by_ioid(target_ioid) == old(
                self,
            ).get_iommu_table_mapping_by_ioid(target_ioid).insert(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
                *target_entry,
            ),
            self.get_iommu_table_mapping_by_ioid(target_ioid).dom() == old(
                self,
            ).get_iommu_table_mapping_by_ioid(target_ioid).dom().insert(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ),
    {
        self.iommu_tables.iommu_table_array_map_4k_page_t(
            target_ioid,
            target_l4i,
            target_l3i,
            target_l2i,
            target_l1i,
            target_l1_p,
            target_entry,
        );
        assert(self.wf()) by {
            assert(self.pagetables_wf());
            assert(self.iommutables_wf());
            assert(self.pagetable_iommu_table_disjoint());
            assert(self.root_table_wf());
            assert(self.root_table_cache_wf());
            assert(self.kernel_entries_wf());
        };
    }

    pub fn resolve_pagetable_mapping(&self, pcid: Pcid, va: VAddr) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.pcid_active(pcid),
            va_4k_valid(va),
        ensures
            self.get_pagetable_by_pcid(pcid).unwrap().mapping_4k().dom().contains(va)
                == ret.is_Some(),
            ret.is_Some() ==> self.get_pagetable_by_pcid(pcid).unwrap().mapping_4k().dom().contains(
                va,
            ) && self.get_pagetable_by_pcid(pcid).unwrap().mapping_4k()[va]
                == page_entry_to_map_entry(&ret.unwrap()),
    {
        proof {
            va_lemma();
        }
        // proof{self.get_pagetable_by_pcid(pcid).unwrap().no_mapping_infer_no_reslove();}
        let (l4i, l3i, l2i, l1i) = va2index(va);
        assert(spec_index2va((l4i, l3i, l2i, l1i)) == va);
        let l4_entry_op = self.get_pagetable_l4_entry(pcid, l4i);
        if l4_entry_op.is_none() {
            return None;
        }
        let l4_entry = l4_entry_op.unwrap();
        let l3_entry_op = self.get_pagetable_l3_entry(pcid, l4i, l3i, &l4_entry);
        if l3_entry_op.is_none() {
            return None;
        }
        let l3_entry = l3_entry_op.unwrap();
        let l2_entry_op = self.get_pagetable_l2_entry(pcid, l4i, l3i, l2i, &l3_entry);
        if l2_entry_op.is_none() {
            return None;
        }
        let l2_entry = l2_entry_op.unwrap();
        self.get_pagetable_l1_entry(pcid, l4i, l3i, l2i, l1i, &l2_entry)
    }

    pub fn resolve_iommu_table_mapping(&self, ioid: IOid, va: VAddr) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.ioid_active(ioid),
            va_4k_valid(va),
        ensures
            self.get_iommu_table_by_ioid(ioid).unwrap().mapping_4k().dom().contains(va)
                == ret.is_Some(),
            ret.is_Some() ==> self.get_iommu_table_by_ioid(
                ioid,
            ).unwrap().mapping_4k().dom().contains(va) && self.get_iommu_table_by_ioid(
                ioid,
            ).unwrap().mapping_4k()[va] == page_entry_to_map_entry(&ret.unwrap()),
    {
        proof {
            va_lemma();
        }
        // proof{self.get_iommu_table_by_ioid(ioid).unwrap().no_mapping_infer_no_reslove();}
        let (l4i, l3i, l2i, l1i) = va2index(va);
        assert(spec_index2va((l4i, l3i, l2i, l1i)) == va);
        let l4_entry_op = self.get_iommu_table_l4_entry(ioid, l4i);
        if l4_entry_op.is_none() {
            return None;
        }
        let l4_entry = l4_entry_op.unwrap();
        let l3_entry_op = self.get_iommu_table_l3_entry(ioid, l4i, l3i, &l4_entry);
        if l3_entry_op.is_none() {
            return None;
        }
        let l3_entry = l3_entry_op.unwrap();
        let l2_entry_op = self.get_iommu_table_l2_entry(ioid, l4i, l3i, l2i, &l3_entry);
        if l2_entry_op.is_none() {
            return None;
        }
        let l2_entry = l2_entry_op.unwrap();
        self.get_iommu_table_l1_entry(ioid, l4i, l3i, l2i, l1i, &l2_entry)
    }

    // pub fn pagetable_unmap_4k_page(&self, pcid:Pcid, va:VAddr) -> (ret: Option<PageEntry>)
    //     requires
    //         old(self).wf(),
    //         old(self).pcid_active(pcid),
    //         va_4k_valid(va),
    //     ensures
    //         !(self.get_pagetable_by_pcid(pcid).unwrap().mapping_4k().dom().contains(va)),
    //         self.wf(),
    //         self.pcid_active(pcid),
    // {
    //     proof{va_lemma();}
    //     let va: Vaddr = va_range.index(i);
    //     assert(spec_index2va((l4i, l3i, l2i, l1i)) == va);
    //     let (l4i, l3i, l2i, l1i) = va2index(va);
    //     let mut l4_entry_op = self.get_pagetable_l4_entry(target_pcid, l4i);
    //     if l4_entry_op.is_none() {
    //         return None;
    //     }
    //     let l4_entry = l4_entry_op.unwrap();
    //     let mut l3_entry_op = self.get_pagetable_l3_entry(target_pcid, l4i, l3i, &l4_entry);
    //     if l3_entry_op.is_none() {
    //         return None;
    //     }
    //     let l3_entry = l3_entry_op.unwrap();
    //     let mut l2_entry_op = self.get_pagetable_l2_entry(target_pcid, l4i, l3i, l2i, &l3_entry);
    //     if l2_entry_op.is_none() {
    //         return None;
    //     }
    //     let l2_entry = l2_entry_op.unwrap();
    //     let mut l1_entry_op = self.get_pagetable_l1_entry(target_pcid, l4i, l3i, l2i, l1i, &l2_entry);
    //     if(l1_entry_op.is_none()){
    //         return None;
    //     }
    //     let target_entry = l1_entry_op.unwrap();
    //     self.pagetable_unmap_4k_page(pcid, l4i, l3i, l2i, l1i, &l2_entry, target_entry);
    //     l1_entry_op
    // }
    // pub fn new_page_table(&mut self, new_proc_ptr:ProcPtr, page_map_ptr: PageMapPtr, mut page_map_perm: Tracked<PointsTo<PageMap>>) -> (ret:Pcid)
    //     requires
    //         old(self).wf(),
    //         old(self).page_closure().contains(page_map_ptr) == false,
    //         page_ptr_valid(page_map_ptr),
    //         page_map_perm@.addr() == page_map_ptr,
    //         page_map_perm@.is_init(),
    //         page_map_perm@.value().wf(),
    //         forall|i:usize|
    //             #![trigger page_map_perm@.value()[i].is_empty()]
    //             0<=i<512 ==> page_map_perm@.value()[i].is_empty(),
    //         old(self).free_pcids.len() > 0,
    //     ensures
    //         self.wf(),
    //         self.kernel_entries =~= old(self).kernel_entries,
    //         self.kernel_entries_ghost =~= old(self).kernel_entries_ghost,
    //         // self.free_pcids =~= old(self).free_pcids,
    //         // self.page_tables =~= old(self).page_tables,
    //         // self.page_table_pages =~= old(self).page_table_pages,
    //         self.free_ioids =~= old(self).free_ioids,
    //         self.iommu_tables =~= old(self).iommu_tables,
    //         self.iommu_table_pages =~= old(self).iommu_table_pages,
    //         self.root_table =~= old(self).root_table,
    //         self.root_table_cache =~= old(self).root_table_cache,
    //         self.pci_bitmap =~= old(self).pci_bitmap,
    //         self.page_table_pages@.dom() =~= old(self).page_table_pages@.dom().insert(page_map_ptr),
    //         forall|p:Pcid|
    //             #![trigger self.pcid_active(p)]
    //             p != ret ==>
    //             self.pcid_active(p) == old(self).pcid_active(p),
    //         forall|p:Pcid|
    //             #![trigger self.pcid_active(p)]
    //             #![trigger self.get_pagetable_mapping_by_pcid(p)]
    //             self.pcid_active(p) && p != ret
    //             ==>
    //             old(self).get_pagetable_mapping_by_pcid(p) == self.get_pagetable_mapping_by_pcid(p),
    //         forall|i:IOid|
    //             #![trigger self.ioid_active(i)]
    //             #![trigger self.get_iommu_table_mapping_by_ioid(i)]
    //             self.ioid_active(i)
    //             ==>
    //             old(self).get_iommu_table_mapping_by_ioid(i) == self.get_iommu_table_mapping_by_ioid(i),
    //         forall|p:Pcid|
    //             #![trigger self.pcid_active(p)]
    //             #![trigger self.pcid_to_proc_ptr(p)]
    //             self.pcid_active(p) && p != ret
    //             ==>
    //             old(self).pcid_to_proc_ptr(p) == self.pcid_to_proc_ptr(p),
    //         self.pcid_to_proc_ptr(ret) == new_proc_ptr,
    //         self.pcid_active(ret),
    //         !old(self).pcid_active(ret),
    //         self.get_pagetable_mapping_by_pcid(ret).dom() == Set::<PagePtr>::empty(),
    //         self.page_closure() == old(self).page_closure().insert(page_map_ptr),
    // {
    //     page_map_set_kernel_entry_range(&self.kernel_entries, page_map_ptr, Tracked(page_map_perm.borrow_mut()));
    //     let new_pcid = *self.free_pcids.pop_unique();
    //     self.page_tables.set(new_pcid, Some(PageTable::new(new_pcid, self.kernel_entries_ghost, page_map_ptr, page_map_perm)));
    //     self.pcid_to_proc_ptr.set(new_pcid,Some(new_proc_ptr));
    //     proof{
    //         set_lemma::<PagePtr>();
    //         self.page_table_pages@.dom() = self.page_table_pages@.dom().insert(page_map_ptr);
    //     }
    //     assert(self.pagetables_wf()) by {
    //         seq_pop_unique_lemma::<Pcid>();
    //         seq_update_lemma::<Option<PageTable>>();
    //         assert(forall|pcid:Pcid|
    //             pcid != new_pcid ==>
    //             old(self).get_free_pcids_as_set().contains(pcid) == self.get_free_pcids_as_set().contains(pcid));
    //     };
    //     assert(self.iommutables_wf());
    //     assert(self.pagetable_iommu_table_disjoint());
    //     assert(self.root_table_wf());
    //     assert(self.root_table_cache_wf());
    //     assert(self.kernel_entries_wf());
    //     assert(self.pcid_to_proc_wf());
    //     new_pcid
    // }
    pub fn alloc_page_table(&mut self, new_proc_ptr: ProcPtr) -> (ret: Pcid)
        requires
            old(self).wf(),
            old(self).free_pcids.len() > 0,
        ensures
            self.wf(),
            self.kernel_entries =~= old(self).kernel_entries,
            self.kernel_entries_ghost =~= old(self).kernel_entries_ghost,
            // self.free_pcids =~= old(self).free_pcids,
            self.page_tables =~= old(self).page_tables,
            self.page_table_pages =~= old(self).page_table_pages,
            self.free_ioids =~= old(self).free_ioids,
            self.iommu_tables =~= old(self).iommu_tables,
            self.iommu_table_pages =~= old(self).iommu_table_pages,
            self.root_table =~= old(self).root_table,
            self.root_table_cache =~= old(self).root_table_cache,
            self.pci_bitmap =~= old(self).pci_bitmap,
            self.page_table_pages@.dom() =~= old(self).page_table_pages@.dom(),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                p != ret ==> self.pcid_active(p) == old(self).pcid_active(p),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                self.ioid_active(i) == old(self).ioid_active(i),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.get_pagetable_mapping_by_pcid(p)]
                self.pcid_active(p) && p != ret ==> old(self).get_pagetable_mapping_by_pcid(p)
                    == self.get_pagetable_mapping_by_pcid(p),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                #![trigger self.get_iommu_table_mapping_by_ioid(i)]
                self.ioid_active(i) ==> old(self).get_iommu_table_mapping_by_ioid(i)
                    == self.get_iommu_table_mapping_by_ioid(i),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.pcid_to_proc_ptr(p)]
                self.pcid_active(p) && p != ret ==> old(self).pcid_to_proc_ptr(p)
                    == self.pcid_to_proc_ptr(p),
            forall|i: IOid|
                #![trigger self.ioid_active(i)]
                #![trigger self.ioid_to_proc_ptr(i)]
                self.ioid_active(i) ==> old(self).ioid_to_proc_ptr(i) == self.ioid_to_proc_ptr(i),
            self.pcid_to_proc_ptr(ret) == new_proc_ptr,
            self.pcid_active(ret),
            !old(self).pcid_active(ret),
            self.get_pagetable_mapping_by_pcid(ret).dom() == Set::<PagePtr>::empty(),
    {
        let new_pcid = *self.free_pcids.pop_unique();
        self.pcid_to_proc_ptr.set(new_pcid, Some(new_proc_ptr));
        assert(self.pagetables_wf()) by {
            seq_pop_unique_lemma::<Pcid>();
            seq_update_lemma::<Option<PageTable>>();
            assert(forall|pcid: Pcid|
                pcid != new_pcid ==> old(self).get_free_pcids_as_set().contains(pcid)
                    == self.get_free_pcids_as_set().contains(pcid));
        };
        assert(self.iommutables_wf());
        assert(self.pagetable_iommu_table_disjoint());
        assert(self.root_table_wf());
        assert(self.root_table_cache_wf());
        assert(self.kernel_entries_wf());
        assert(self.pcid_to_proc_wf()) by {
            set_lemma::<Pcid>();
            seq_pop_unique_lemma::<Pcid>();
            seq_update_lemma::<ProcPtr>();
            //    assert(
            //         forall|pcid:Pcid|
            //         #![trigger self.pcid_active(pcid)]
            //         #![trigger self.pcid_to_proc_ptr@[pcid as int]]
            //         pcid != new_pcid ==>
            //         self.pcid_active(pcid) == self.pcid_to_proc_ptr@[pcid as int].is_Some()
            //    );
        };
        assert(self.ioid_to_proc_wf());
        new_pcid
    }

    pub fn alloc_iommu_table(&mut self, new_proc_ptr: ProcPtr) -> (ret: IOid)
        requires
            old(self).wf(),
            old(self).free_ioids.len() > 0,
        ensures
            self.wf(),
            self.kernel_entries =~= old(self).kernel_entries,
            self.kernel_entries_ghost =~= old(self).kernel_entries_ghost,
            self.free_pcids =~= old(self).free_pcids,
            self.page_tables =~= old(self).page_tables,
            self.page_table_pages =~= old(self).page_table_pages,
            // self.free_ioids =~= old(self).free_ioids,
            self.iommu_tables =~= old(self).iommu_tables,
            self.iommu_table_pages =~= old(self).iommu_table_pages,
            self.root_table =~= old(self).root_table,
            self.root_table_cache =~= old(self).root_table_cache,
            self.pci_bitmap =~= old(self).pci_bitmap,
            self.page_table_pages@.dom() =~= old(self).page_table_pages@.dom(),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                self.pcid_active(p) == old(self).pcid_active(p),
            forall|p: IOid|
                #![trigger self.ioid_active(p)]
                p != ret ==> self.ioid_active(p) == old(self).ioid_active(p),
            forall|p: IOid|
                #![trigger self.ioid_active(p)]
                #![trigger self.get_iommu_table_mapping_by_ioid(p)]
                self.ioid_active(p) && p != ret ==> old(self).get_iommu_table_mapping_by_ioid(p)
                    == self.get_iommu_table_mapping_by_ioid(p),
            forall|i: Pcid|
                #![trigger self.pcid_active(i)]
                #![trigger self.get_pagetable_mapping_by_pcid(i)]
                self.pcid_active(i) ==> old(self).get_pagetable_mapping_by_pcid(i)
                    == self.get_pagetable_mapping_by_pcid(i),
            forall|p: Pcid|
                #![trigger self.pcid_active(p)]
                #![trigger self.pcid_to_proc_ptr(p)]
                self.pcid_active(p) ==> old(self).pcid_to_proc_ptr(p) == self.pcid_to_proc_ptr(p),
            forall|p: IOid|
                #![trigger self.ioid_active(p)]
                #![trigger self.ioid_to_proc_ptr(p)]
                self.ioid_active(p) && p != ret ==> old(self).ioid_to_proc_ptr(p)
                    == self.ioid_to_proc_ptr(p),
            self.ioid_to_proc_ptr(ret) == new_proc_ptr,
            self.ioid_active(ret),
            !old(self).ioid_active(ret),
            self.get_iommu_table_mapping_by_ioid(ret).dom() == Set::<PagePtr>::empty(),
    {
        let new_ioid = *self.free_ioids.pop_unique();
        self.ioid_to_proc_ptr.set(new_ioid, Some(new_proc_ptr));
        assert(self.pagetables_wf());
        assert(self.iommutables_wf()) by {
            seq_pop_unique_lemma::<IOid>();
            seq_update_lemma::<Option<PageTable>>();
            assert(forall|ioid: IOid|
                ioid != new_ioid ==> old(self).get_free_ioids_as_set().contains(ioid)
                    == self.get_free_ioids_as_set().contains(ioid));
        };
        assert(self.pagetable_iommu_table_disjoint());
        assert(self.root_table_wf());
        assert(self.root_table_cache_wf());
        assert(self.kernel_entries_wf());
        assert(self.ioid_to_proc_wf()) by {
            set_lemma::<IOid>();
            seq_pop_unique_lemma::<IOid>();
            seq_update_lemma::<ProcPtr>();
            //    assert(
            //         forall|pcid:Pcid|
            //         #![trigger self.pcid_active(pcid)]
            //         #![trigger self.pcid_to_proc_ptr@[pcid as int]]
            //         pcid != new_pcid ==>
            //         self.pcid_active(pcid) == self.pcid_to_proc_ptr@[pcid as int].is_Some()
            //    );
        };
        assert(self.pcid_to_proc_wf());
        new_ioid
    }

    #[verifier(external_body)]
    pub fn init(
        &mut self,
        dom0_page_map_ptr: PageMapPtr,
        kernel_entry: PageMapPtr,
        new_proc_ptr: ProcPtr,
        page_alloc: &mut PageAllocator,
        dom0_page_map_perm: Tracked<PointsTo<PageMap>>,
    ) {
        self.kernel_entries.set(0, kernel_entry);
        for i in 1..PCID_MAX {
            self.free_pcids.push(PCID_MAX - i);
            self.pcid_to_proc_ptr.set(PCID_MAX - i, None);
        }

        for i in 1..PCID_MAX {
            let (new_page_ptr, new_page_perm) = page_alloc.alloc_page_4k();
            let (page_map_ptr, Tracked(page_map_perm)) = page_perm_to_page_map(
                new_page_ptr,
                new_page_perm,
            );
            page_map_set_kernel_entry_range(
                &self.kernel_entries,
                page_map_ptr,
                Tracked(&mut page_map_perm),
            );
            self.page_tables.set(
                i,
                Some(
                    PageTable::new(
                        Some(i),
                        None,
                        self.kernel_entries_ghost,
                        page_map_ptr,
                        Tracked(page_map_perm),
                        KERNEL_MEM_END_L4INDEX,
                    ),
                ),
            );
        }

        for i in 1..IOID_MAX {
            self.free_ioids.push(IOID_MAX - i);
            self.ioid_to_proc_ptr.set(IOID_MAX - i, None);
        }

        for i in 1..IOID_MAX {
            let (new_page_ptr, new_page_perm) = page_alloc.alloc_page_4k();
            let (page_map_ptr, page_map_perm) = page_perm_to_page_map(new_page_ptr, new_page_perm);
            self.iommu_tables.set(
                i,
                Some(
                    PageTable::new(
                        None,
                        Some(i),
                        Ghost(Seq::<PageEntry>::empty()),
                        page_map_ptr,
                        page_map_perm,
                        0,
                    ),
                ),
            );
        }

        let (dom0_io_cr3, new_page_perm) = page_alloc.alloc_page_4k();
        let (page_map_ptr, page_map_perm) = page_perm_to_page_map(dom0_io_cr3, new_page_perm);
        self.iommu_tables.set(
            0,
            Some(
                PageTable::new(
                    None,
                    Some(0),
                    Ghost(Seq::<PageEntry>::empty()),
                    dom0_io_cr3,
                    page_map_perm,
                    0,
                ),
            ),
        );
        self.ioid_to_proc_ptr.set(0, Some(new_proc_ptr));

        self.pcid_to_proc_ptr.set(0, Some(new_proc_ptr));
        self.page_tables.set(
            0,
            Some(
                PageTable::new(
                    Some(0),
                    None,
                    self.kernel_entries_ghost,
                    dom0_page_map_ptr,
                    dom0_page_map_perm,
                    KERNEL_MEM_END_L4INDEX,
                ),
            ),
        );
    }
}

} // verus!
