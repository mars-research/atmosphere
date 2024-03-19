use vstd::prelude::*;
verus! {
// use vstd::ptr::PointsTo;
use core::mem::MaybeUninit;
use crate::pagetable::*;
use crate::mars_array::MarsArray;
use crate::array_vec::ArrayVec;
use crate::page_alloc::*;
use crate::define::*;
use crate::iommutable::*;
use crate::mmu::*;


impl MMUManager{

    pub fn mmu_man_init(&mut self)
        requires
            old(self).free_pcids.wf(),
            old(self).free_pcids.len() == 0,
            old(self).free_pcids@ =~= Seq::empty(),
            old(self).page_tables.wf(),
            old(self).page_table_pages@ =~= Set::empty(),
            old(self).free_ioids.wf(),
            old(self).free_ioids.len() == 0,
            old(self).free_ioids@ =~= Seq::empty(),
            old(self).iommu_tables.wf(),
            old(self).iommu_table_pages@ =~= Set::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<PCID_MAX && spec_va_valid(va) ==>  old(self).get_pagetable_mapping_by_pcid(i)[va].is_None(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].cr3 == 0,
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].l1_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).iommu_tables[i].dummy.cr3 == 0,
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).iommu_tables[i].dummy.l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).iommu_tables[i].dummy.l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).iommu_tables[i].dummy.l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).iommu_tables[i].dummy.l1_tables@ =~= Map::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<IOID_MAX && spec_va_valid(va) ==>  old(self).get_iommutable_mapping_by_ioid(i)[va].is_None(),

            old(self).root_table_cache@.len() == 256,
            forall|bus:u8|#![auto] 0<=bus<256 ==> old(self).root_table_cache@[bus as int].len() == 32,
            forall|bus:u8,dev:u8|#![auto] 0<=bus<256 && 0<=dev<32 ==> old(self).root_table_cache@[bus as int][dev as int].len() == 8,
            (forall|bus:u8,dev:u8,fun:u8|#![auto] 0<=bus<256 && 0<=dev<32 && 0<=fun<8 ==> old(self).root_table_cache@[bus as int][dev as int][fun as int].is_None()),
        ensures
            // self.wf(),
            self.pagetables_wf(),
            self.iommutables_wf(),
            self.pagetable_iommutable_disjoint(),
            self.root_table_wf(),

            self.free_pcids.wf(),
            self.free_pcids.unique(),
            self.free_pcids.len() == PCID_MAX,
            self.free_pcids@ =~= Seq::new(PCID_MAX as nat, |i:int| {(PCID_MAX - i - 1) as usize}),
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.get_free_pcids_as_set().contains(pcid),
            self.page_tables.wf(),
            self.page_table_pages@ =~= Set::empty(),
            self.free_ioids.wf(),
            self.free_ioids.unique(),
            self.free_ioids.len() == IOID_MAX,
            self.free_ioids@ =~= Seq::new(IOID_MAX as nat, |i:int| {(IOID_MAX - i - 1) as usize}),
            forall|ioid:IOid| #![auto] 0<=ioid<IOID_MAX ==> self.get_free_ioids_as_set().contains(ioid),
            self.iommu_tables.wf(),
            self.iommu_table_pages@ =~= Set::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<PCID_MAX && spec_va_valid(va) ==>  self.get_pagetable_mapping_by_pcid(i)[va].is_None(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].cr3 == 0,
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l1_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.cr3 == 0,
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l1_tables@ =~= Map::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<IOID_MAX && spec_va_valid(va) ==>  self.get_iommutable_mapping_by_ioid(i)[va].is_None(),

            self.root_table_cache@.len() == 256,
            forall|bus:u8|#![auto] 0<=bus<256 ==> self.root_table_cache@[bus as int].len() == 32,
            forall|bus:u8,dev:u8|#![auto] 0<=bus<256 && 0<=dev<32 ==> self.root_table_cache@[bus as int][dev as int].len() == 8,
            (forall|bus:u8,dev:u8,fun:u8|#![auto] 0<=bus<256 && 0<=dev<32 && 0<=fun<8 ==> self.root_table_cache@[bus as int][dev as int][fun as int].is_None()),
    {
        let mut i = 0;

        while i!= PCID_MAX
            invariant
                0<=i<=PCID_MAX,
                self.free_pcids.wf(),
                self.free_pcids.unique(),
                self.free_pcids.len() == i,
                self.free_pcids@ =~= Seq::new(i as nat, |i:int| {(PCID_MAX - i - 1) as usize}),
                forall|pcid:Pcid| #![auto] PCID_MAX>pcid>=(PCID_MAX - i) ==> self.get_free_pcids_as_set().contains(pcid),
                self.page_tables.wf(),
                self.page_table_pages@ =~= Set::empty(),
                self.free_ioids.wf(),
                self.free_ioids.unique(),
                self.free_ioids.len() == i,
                self.free_ioids@ =~= Seq::new(i as nat, |i:int| {(IOID_MAX - i - 1) as usize}),
                forall|ioid:IOid| #![auto] IOID_MAX>ioid>=(IOID_MAX - i) ==> self.get_free_ioids_as_set().contains(ioid),
                self.iommu_tables.wf(),
                self.iommu_table_pages@ =~= Set::empty(),
                forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l4_table@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l3_tables@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l2_tables@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l1_tables@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l4_table@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l3_tables@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l2_tables@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l1_tables@ =~= Map::empty(),

                self.root_table_cache@.len() == 256,
                forall|bus:u8|#![auto] 0<=bus<256 ==> self.root_table_cache@[bus as int].len() == 32,
                forall|bus:u8,dev:u8|#![auto] 0<=bus<256 && 0<=dev<32 ==> self.root_table_cache@[bus as int][dev as int].len() == 8,
                (forall|bus:u8,dev:u8,fun:u8|#![auto] 0<=bus<256 && 0<=dev<32 && 0<=fun<8 ==> self.root_table_cache@[bus as int][dev as int][fun as int].is_None()),
            ensures
                i==PCID_MAX,
                self.free_pcids.wf(),
                self.free_pcids.unique(),
                self.free_pcids.len() == i,
                self.free_pcids@ =~= Seq::new(i as nat, |i:int| {(PCID_MAX - i - 1) as usize}),
                forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.get_free_pcids_as_set().contains(pcid),
                self.page_tables.wf(),
                self.page_table_pages@ =~= Set::empty(),
                self.free_ioids.wf(),
                self.free_ioids.unique(),
                self.free_ioids.len() == i,
                self.free_ioids@ =~= Seq::new(i as nat, |i:int| {(IOID_MAX - i - 1) as usize}),
                forall|ioid:IOid| #![auto] IOID_MAX>ioid>=(IOID_MAX - i) ==> self.get_free_ioids_as_set().contains(ioid),
                self.iommu_tables.wf(),
                self.iommu_table_pages@ =~= Set::empty(),
                forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l4_table@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l3_tables@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l2_tables@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l1_tables@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l4_table@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l3_tables@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l2_tables@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l1_tables@ =~= Map::empty(),

                self.root_table_cache@.len() == 256,
                forall|bus:u8|#![auto] 0<=bus<256 ==> self.root_table_cache@[bus as int].len() == 32,
                forall|bus:u8,dev:u8|#![auto] 0<=bus<256 && 0<=dev<32 ==> self.root_table_cache@[bus as int][dev as int].len() == 8,
                (forall|bus:u8,dev:u8,fun:u8|#![auto] 0<=bus<256 && 0<=dev<32 && 0<=fun<8 ==> self.root_table_cache@[bus as int][dev as int][fun as int].is_None()),
        {
            self.free_pcids.push_unique(PCID_MAX - i - 1);
            self.free_ioids.push_unique(IOID_MAX - i - 1);
            i = i+1;
        }

        self.page_tables.init_all_pagetables();
        self.iommu_tables.init_all_iommutables();
        self.root_table.init();
        self.pci_bitmap.init();
        assert(self.pagetables_wf());
        assert(self.iommutables_wf());
        assert(self.pagetable_iommutable_disjoint());
    }

    pub fn adopt_dom0(&mut self, pagetable: PageTable)
        requires
            // old(self).wf(),
            old(self).pagetables_wf(),
            old(self).iommutables_wf(),
            old(self).pagetable_iommutable_disjoint(),
            old(self).root_table_wf(),
            old(self).free_pcids.wf(),
            old(self).free_pcids.unique(),
            old(self).free_pcids.len() == PCID_MAX,
            old(self).free_pcids@ =~= Seq::new(PCID_MAX as nat, |i:int| {(PCID_MAX - i - 1) as usize}),
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> old(self).get_free_pcids_as_set().contains(pcid),
            old(self).page_tables.wf(),
            old(self).page_table_pages@ =~= Set::empty(),
            old(self).free_ioids.wf(),
            old(self).free_ioids.unique(),
            old(self).free_ioids.len() == IOID_MAX,
            old(self).free_ioids@ =~= Seq::new(IOID_MAX as nat, |i:int| {(IOID_MAX - i - 1) as usize}),
            forall|ioid:IOid| #![auto] 0<=ioid<IOID_MAX ==> old(self).get_free_ioids_as_set().contains(ioid),
            old(self).iommu_tables.wf(),
            old(self).iommu_table_pages@ =~= Set::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<PCID_MAX && spec_va_valid(va) ==>  old(self).get_pagetable_mapping_by_pcid(i)[va].is_None(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].cr3 == 0,
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].l1_tables@ =~= Map::empty(),

            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).iommu_tables[i].dummy.cr3 == 0,
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).iommu_tables[i].dummy.l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).iommu_tables[i].dummy.l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).iommu_tables[i].dummy.l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).iommu_tables[i].dummy.l1_tables@ =~= Map::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<IOID_MAX && spec_va_valid(va) ==>  old(self).get_iommutable_mapping_by_ioid(i)[va].is_None(),

            pagetable.wf(),
            forall|va:usize| #![auto] spec_va_valid(va) && pagetable.get_pagetable_mapping()[va].is_Some() ==>
                page_ptr_valid(pagetable.get_pagetable_mapping()[va].get_Some_0().addr),
            forall|va:usize| #![auto] spec_va_valid(va) && pagetable.get_pagetable_mapping()[va].is_Some() ==>
                spec_va_perm_bits_valid(pagetable.get_pagetable_mapping()[va].get_Some_0().perm),

            forall|bus:u8,dev:u8,fun:u8|#![auto] 0<=bus<256 && 0<=dev<32 && 0<=fun<8 ==> old(self).root_table.resolve(bus,dev,fun).is_None(),

            old(self).root_table_cache@.len() == 256,
            forall|bus:u8|#![auto] 0<=bus<256 ==> old(self).root_table_cache@[bus as int].len() == 32,
            forall|bus:u8,dev:u8|#![auto] 0<=bus<256 && 0<=dev<32 ==> old(self).root_table_cache@[bus as int][dev as int].len() == 8,
            (forall|bus:u8,dev:u8,fun:u8|#![auto] 0<=bus<256 && 0<=dev<32 && 0<=fun<8 ==> old(self).root_table_cache@[bus as int][dev as int][fun as int].is_None()),
        ensures
            self.wf(),
            self.free_ioids.wf(),
            self.free_ioids.unique(),
            self.free_ioids.len() == IOID_MAX,
            self.free_ioids@ =~= Seq::new(IOID_MAX as nat, |i:int| {(IOID_MAX - i - 1) as usize}),
            forall|ioid:IOid| #![auto] 0<=ioid<IOID_MAX ==> self.get_free_ioids_as_set().contains(ioid),
            self.iommu_tables.wf(),
            self.iommu_table_pages@ =~= Set::empty(),
            forall|i:int|#![auto] 1<=i<PCID_MAX ==>  self.page_tables[i].cr3 == 0,
            forall|i:int|#![auto] 1<=i<PCID_MAX ==>  self.page_tables[i].l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 1<=i<PCID_MAX ==>  self.page_tables[i].l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 1<=i<PCID_MAX ==>  self.page_tables[i].l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 1<=i<PCID_MAX ==>  self.page_tables[i].l1_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.cr3 == 0,
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l1_tables@ =~= Map::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<IOID_MAX && spec_va_valid(va) ==>  self.get_iommutable_mapping_by_ioid(i)[va].is_None(),
            self.get_pagetable_by_pcid(0) =~= pagetable,
            self.get_pagetable_mapping_by_pcid(0) =~= pagetable.get_pagetable_mapping(),
            self.get_mmu_page_closure() =~= pagetable.get_pagetable_page_closure(),
            forall|i:usize, va: VAddr|#![auto] 1<=i<PCID_MAX && spec_va_valid(va) ==>  self.get_pagetable_mapping_by_pcid(i)[va].is_None(),
            self.get_free_pcids_as_set().contains(0) == false,

            forall|bus:u8,dev:u8,fun:u8|#![auto] 0<=bus<256 && 0<=dev<32 && 0<=fun<8 ==> self.root_table.resolve(bus,dev,fun).is_None(),

            self.root_table_cache@.len() == 256,
            forall|bus:u8|#![auto] 0<=bus<256 ==> self.root_table_cache@[bus as int].len() == 32,
            forall|bus:u8,dev:u8|#![auto] 0<=bus<256 && 0<=dev<32 ==> self.root_table_cache@[bus as int][dev as int].len() == 8,
            (forall|bus:u8,dev:u8,fun:u8|#![auto] 0<=bus<256 && 0<=dev<32 && 0<=fun<8 ==> self.root_table_cache@[bus as int][dev as int][fun as int].is_None()),
    {
        let pcid = self.free_pcids.pop_unique();
        assert(pcid == 0);
        proof{
            self.page_table_pages@ = pagetable.get_pagetable_page_closure();
        }
        self.page_tables.set(pcid, pagetable);
        assert(self.pagetables_wf());
        assert(self.iommutables_wf());
    }

    #[verifier(external_body)]
    pub fn new() -> (ret: MMUManager)
        ensures
            ret.free_pcids.wf(),
            ret.free_pcids@ =~= Seq::empty(),
            ret.page_tables.wf(),
            ret.page_table_pages@ =~= Set::empty(),
            ret.free_ioids.wf(),
            ret.free_ioids@ =~= Seq::empty(),
            ret.iommu_tables.wf(),
            ret.iommu_table_pages@ =~= Set::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.page_tables[i].cr3 == 0,
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.page_tables[i].l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.page_tables[i].l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.page_tables[i].l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.page_tables[i].l1_tables@ =~= Map::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<PCID_MAX && spec_va_valid(va) ==>  ret.get_pagetable_mapping_by_pcid(i)[va].is_None(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> ret.iommu_tables[i].dummy.cr3 == 0,
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> ret.iommu_tables[i].dummy.l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> ret.iommu_tables[i].dummy.l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> ret.iommu_tables[i].dummy.l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> ret.iommu_tables[i].dummy.l1_tables@ =~= Map::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<IOID_MAX && spec_va_valid(va) ==>  ret.get_iommutable_mapping_by_ioid(i)[va].is_None(),
            // ret.pci_bitmap.wf(),
            ret.root_table_cache@.len() == 256,
            forall|bus:u8|#![auto] 0<=bus<256 ==> ret.root_table_cache@[bus as int].len() == 32,
            forall|bus:u8,dev:u8|#![auto] 0<=bus<256 && 0<=dev<32 ==> ret.root_table_cache@[bus as int][dev as int].len() == 8,
            (forall|bus:u8,dev:u8,fun:u8|#![auto] 0<=bus<256 && 0<=dev<32 && 0<=fun<8 ==> ret.root_table_cache@[bus as int][dev as int][fun as int].is_None()),
    {
        unsafe{
        let ret = Self{
            free_pcids: ArrayVec::<Pcid,PCID_MAX>::new(),
            page_tables: MarsArray::<PageTable,PCID_MAX>::new(),
            page_table_pages:  Ghost(Set::empty()),
            free_ioids:  ArrayVec::<IOid,IOID_MAX>::new(),
            iommu_tables: MarsArray::<IOMMUTable,IOID_MAX>::new(),
            iommu_table_pages: Ghost(Set::empty()),
            root_table: RootTable::new(),
            root_table_cache: Ghost(Seq::empty()),
            // device_table: MaybeUninit::uninit().assume_init(),
            pci_bitmap:PCIBitMap::new(),
        };
        ret
        }
    }
}
}
