use vstd::prelude::*;
verus! {

use crate::array_vec::*;
use crate::proc::*;
use crate::page_alloc::*;
use crate::mmu::*;
use crate::cpu::*;
use crate::mars_array::MarsArray;
use crate::pagetable::*;
use crate::define::*;
// use vstd::ptr::*;
use crate::trap::PtRegs;
// use crate::iommutable::*;
use crate::kernel::*;


impl Kernel{

    #[verifier(external_body)]
    pub fn new() -> (ret: Kernel)
        ensures
            ret.proc_man.proc_ptrs.arr_seq@.len() == MAX_NUM_PROCS,
            ret.proc_man.proc_perms@ =~= Map::empty(),
            ret.proc_man.thread_ptrs@ =~= Set::empty(),
            ret.proc_man.thread_perms@ =~= Map::empty(),
            ret.proc_man.scheduler.arr_seq@.len() == MAX_NUM_THREADS,
            ret.proc_man.scheduler@ =~= Seq::empty(),
            ret.proc_man.endpoint_ptrs@ =~= Set::empty(),
            ret.proc_man.endpoint_perms@ =~= Map::empty(),
            ret.proc_man.pcid_closure@ =~= Set::empty(),
            ret.proc_man.ioid_closure@ =~= Set::empty(),

            ret.page_alloc.page_array.wf(),
            ret.page_alloc.free_pages.wf(),
            ret.page_alloc.free_pages.len() == 0,
            ret.page_alloc.page_table_pages@ =~= Set::empty(),
            ret.page_alloc.allocated_pages@ =~= Set::empty(),
            ret.page_alloc.mapped_pages@ =~= Set::empty(),
            ret.page_alloc.available_pages@ =~= Set::empty(),
            ret.page_alloc.page_perms@.dom() =~= Set::empty(),

            ret.mmu_man.free_pcids.wf(),
            ret.mmu_man.free_pcids@ =~= Seq::empty(),
            ret.mmu_man.page_tables.wf(),
            ret.mmu_man.page_table_pages@ =~= Set::empty(),
            ret.mmu_man.free_ioids.wf(),
            ret.mmu_man.free_ioids@ =~= Seq::empty(),
            ret.mmu_man.iommu_tables.wf(),
            ret.mmu_man.iommu_table_pages@ =~= Set::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<PCID_MAX && spec_va_valid(va) ==>  ret.mmu_man.get_pagetable_mapping_by_pcid(i)[va].is_None(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.mmu_man.page_tables[i].cr3 == 0,
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.mmu_man.page_tables[i].l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.mmu_man.page_tables[i].l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.mmu_man.page_tables[i].l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.mmu_man.page_tables[i].l1_tables@ =~= Map::empty(),

            forall|i:usize, va: VAddr|#![auto] 0<=i<IOID_MAX && spec_va_valid(va) ==>  ret.mmu_man.get_iommutable_mapping_by_ioid(i)[va].is_None(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> ret.mmu_man.iommu_tables[i].dummy.cr3 == 0,
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> ret.mmu_man.iommu_tables[i].dummy.l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> ret.mmu_man.iommu_tables[i].dummy.l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> ret.mmu_man.iommu_tables[i].dummy.l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> ret.mmu_man.iommu_tables[i].dummy.l1_tables@ =~= Map::empty(),

            ret.cpu_list.wf(),
    {
        let ret = Self {
            proc_man : ProcessManager::new(),
            page_alloc : PageAllocator::new(),
            mmu_man: MMUManager::new(),
            cpu_list: MarsArray::<Cpu,NUM_CPUS>::new(),
            cpu_stacks: CPUStackList::new(),
            kernel_pml4_entry: PageEntry{addr:0,perm:0},
        };
        ret
    }


    // #[verifier(external_body)]
    pub fn kernel_init(&mut self, boot_page_ptrs: &ArrayVec<(PageState,VAddr),NUM_PAGES>, mut boot_page_perms: Tracked<Map<PagePtr,PagePerm>>,
                        dom0_pagetable: PageTable, kernel_pml4_entry: PageEntry, dom0_pt_regs: PtRegs, init_pci_map: PCIBitMap) -> (ret: isize)
        requires
            old(self).proc_man.proc_ptrs.arr_seq@.len() == MAX_NUM_PROCS,
            old(self).proc_man.proc_perms@ =~= Map::empty(),
            old(self).proc_man.thread_ptrs@ =~= Set::empty(),
            old(self).proc_man.thread_perms@ =~= Map::empty(),
            old(self).proc_man.scheduler.arr_seq@.len() == MAX_NUM_THREADS,
            old(self).proc_man.scheduler.wf(),
            old(self).proc_man.scheduler@ =~= Seq::empty(),
            old(self).proc_man.endpoint_ptrs@ =~= Set::empty(),
            old(self).proc_man.endpoint_perms@ =~= Map::empty(),
            old(self).proc_man.pcid_closure@ =~= Set::empty(),
            old(self).proc_man.ioid_closure@ =~= Set::empty(),

            old(self).page_alloc.page_array.wf(),
            old(self).page_alloc.free_pages.wf(),
            old(self).page_alloc.free_pages.len() == 0,
            old(self).page_alloc.page_table_pages@ =~= Set::empty(),
            old(self).page_alloc.allocated_pages@ =~= Set::empty(),
            old(self).page_alloc.mapped_pages@ =~= Set::empty(),
            old(self).page_alloc.available_pages@ =~= Set::empty(),
            old(self).page_alloc.page_perms@.dom() =~= Set::empty(),

            old(self).mmu_man.free_pcids.wf(),
            old(self).mmu_man.free_pcids@ =~= Seq::empty(),
            old(self).mmu_man.page_tables.wf(),
            old(self).mmu_man.page_table_pages@ =~= Set::empty(),
            old(self).mmu_man.free_ioids.wf(),
            old(self).mmu_man.free_ioids@ =~= Seq::empty(),
            old(self).mmu_man.iommu_tables.wf(),
            old(self).mmu_man.iommu_table_pages@ =~= Set::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> old(self).mmu_man.page_tables[i].cr3 == 0,
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> old(self).mmu_man.page_tables[i].l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> old(self).mmu_man.page_tables[i].l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> old(self).mmu_man.page_tables[i].l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> old(self).mmu_man.page_tables[i].l1_tables@ =~= Map::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<PCID_MAX && spec_va_valid(va) ==>   old(self).mmu_man.get_pagetable_by_pcid(i).wf() && old(self).mmu_man.get_pagetable_mapping_by_pcid(i)[va].is_None(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).mmu_man.iommu_tables[i].dummy.cr3 == 0,
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).mmu_man.iommu_tables[i].dummy.l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).mmu_man.iommu_tables[i].dummy.l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).mmu_man.iommu_tables[i].dummy.l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).mmu_man.iommu_tables[i].dummy.l1_tables@ =~= Map::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<IOID_MAX && spec_va_valid(va) ==>   old(self).mmu_man.get_iommutable_by_ioid(i).wf() && old(self).mmu_man.get_iommutable_mapping_by_ioid(i)[va].is_None(),
            old(self).mmu_man.root_table_cache@.len() == 256,
            forall|bus:u8|#![auto] 0<=bus<256 ==> old(self).mmu_man.root_table_cache@[bus as int].len() == 32,
            forall|bus:u8,dev:u8|#![auto] 0<=bus<256 && 0<=dev<32 ==> old(self).mmu_man.root_table_cache@[bus as int][dev as int].len() == 8,
            (forall|bus:u8,dev:u8,fun:u8|#![auto] 0<=bus<256 && 0<=dev<32 && 0<=fun<8 ==> old(self).mmu_man.root_table_cache@[bus as int][dev as int][fun as int].is_None()),

            old(self).cpu_list.wf(),
            boot_page_ptrs.wf(),
            boot_page_ptrs.len() == NUM_PAGES,
            (forall|i:usize| #![auto] 0<=i<NUM_PAGES ==> boot_page_ptrs@[i as int].1 == page_index2page_ptr(i)),
            (forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> boot_page_ptrs@[page_ptr2page_index(page_ptr) as int].1 == page_ptr),
            (forall|i:usize| #![auto] 0<=i<NUM_PAGES ==> boot_page_ptrs@[i as int].0 <= IO),
            (forall|i:usize| #![auto] 0<=i<NUM_PAGES ==> boot_page_ptrs@[i as int].0 != ALLOCATED),
            (forall|i:usize| #![auto] 0<=i<NUM_PAGES && (boot_page_ptrs@[i as int].0 == FREE || boot_page_ptrs@[i as int].0 == MAPPED || boot_page_ptrs@[i as int].0 == IO)==>
                (boot_page_perms@.dom().contains(page_index2page_ptr(i))
                &&
                boot_page_perms@[page_index2page_ptr(i)]@.pptr == page_index2page_ptr(i)
                &&
                boot_page_perms@[page_index2page_ptr(i)]@.value.is_Some()
                &&
                spec_va_valid(boot_page_ptrs@[i as int].1)
                )
            ),
            NUM_PAGES * 4096 <= usize::MAX,

            dom0_pagetable.wf(),
            forall|va:usize| #![auto] spec_va_valid(va) && dom0_pagetable.get_pagetable_mapping()[va].is_Some() ==>
                page_ptr_valid(dom0_pagetable.get_pagetable_mapping()[va].get_Some_0().addr),
            forall|va:usize| #![auto] spec_va_valid(va) && dom0_pagetable.get_pagetable_mapping()[va].is_Some() ==>
                spec_va_perm_bits_valid(dom0_pagetable.get_pagetable_mapping()[va].get_Some_0().perm),

            forall|va:usize| #![auto] spec_va_valid(va) && dom0_pagetable.get_pagetable_mapping()[va].is_Some() ==>
                boot_page_ptrs[page_ptr2page_index(dom0_pagetable.get_pagetable_mapping()[va].get_Some_0().addr) as int].0 == MAPPED
                ||
                boot_page_ptrs[page_ptr2page_index(dom0_pagetable.get_pagetable_mapping()[va].get_Some_0().addr) as int].0 == IO,

            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) && (boot_page_ptrs@[page_ptr2page_index(page_ptr) as int].0 == MAPPED || boot_page_ptrs@[page_ptr2page_index(page_ptr) as int].0 == IO) ==>
                (
                    spec_va_valid(boot_page_ptrs@[page_ptr2page_index(page_ptr) as int].1)
                    &&
                    dom0_pagetable.get_pagetable_mapping()[boot_page_ptrs@[page_ptr2page_index(page_ptr) as int].1].is_Some()
                    &&
                    dom0_pagetable.get_pagetable_mapping()[boot_page_ptrs@[page_ptr2page_index(page_ptr) as int].1].get_Some_0().addr == page_ptr
                ),

            forall|va:usize| #![auto] spec_va_valid(va) && dom0_pagetable.get_pagetable_mapping()[va].is_Some() ==>
                boot_page_ptrs[page_ptr2page_index(dom0_pagetable.get_pagetable_mapping()[va].get_Some_0().addr) as int].1 == va,
            forall|page_ptr:PagePtr|#![auto] dom0_pagetable.get_pagetable_page_closure().contains(page_ptr)
                <==>
                (
                    page_ptr_valid(page_ptr)
                    &&
                    0<=page_ptr2page_index(page_ptr as usize)<NUM_PAGES
                    &&
                    boot_page_ptrs@[page_ptr2page_index(page_ptr as usize) as int].0 == PAGETABLE
                ),
            init_pci_map.wf(),
            (forall|ioid:IOid,bus:u8,dev:u8,fun:u8|#![auto] 1<=ioid<IOID_MAX && 0<=bus<256 && 0<=dev<32 && 0<=fun<8 ==>
                (
                    init_pci_map@[(ioid,bus,dev,fun)] == false
                )),
    {
        proof{page_ptr_lemma();}
        self.cpu_list.init_to_none();
        self.proc_man.proc_man_init();
        self.mmu_man.mmu_man_init();
        assert(self.proc_man.wf());
        // assert(self.mmu_man.wf());
        self.page_alloc.init(boot_page_ptrs,boot_page_perms);
        assert(forall|page_ptr:PagePtr|#![auto] self.page_alloc.get_page_table_pages().contains(page_ptr)
        <==>
        (
        page_ptr_valid(page_ptr)
        &&
        0<=page_ptr2page_index(page_ptr as usize)<NUM_PAGES
        &&
        boot_page_ptrs@[page_ptr2page_index(page_ptr as usize) as int].0 == PAGETABLE
        ) );
        assert(self.page_alloc.get_page_table_pages() =~= dom0_pagetable.get_pagetable_page_closure());
        assert(self.page_alloc.wf());
        self.mmu_man.adopt_dom0(dom0_pagetable);
        assert(self.kernel_mmu_page_alloc_pagetable_wf());
        assert(self.kernel_mmu_page_alloc_iommutable_wf());
        assert(self.page_alloc.get_page_table_pages() =~= self.mmu_man.get_mmu_page_closure());
        assert(self.page_alloc.get_allocated_pages() =~= self.proc_man.get_proc_man_page_closure());
        assert(self.kernel_mem_layout_wf());
        self.kernel_pml4_entry = kernel_pml4_entry;
        return self.kernel_init_helper(dom0_pt_regs,init_pci_map);

    }

    fn kernel_init_helper(&mut self, dom0_pt_regs: PtRegs, init_pci_map: PCIBitMap) -> isize
        requires
            old(self).proc_man.wf(),
            old(self).mmu_man.wf(),
            old(self).mmu_man.get_free_pcids_as_set().contains(0) == false,
            old(self).mmu_man.free_ioids@ =~= Seq::new(IOID_MAX as nat, |i:int| {(IOID_MAX - i - 1) as usize}),
            old(self).mmu_man.free_ioids.len() == IOID_MAX,
            old(self).page_alloc.wf(),
            old(self).kernel_mmu_page_alloc_pagetable_wf(),
            old(self).kernel_mmu_page_alloc_iommutable_wf(),
            old(self).kernel_mem_layout_wf(),
            old(self).proc_man.wf(),
            old(self).proc_man.proc_ptrs.arr_seq@.len() == MAX_NUM_PROCS,
            old(self).proc_man.proc_ptrs@ =~= Seq::empty(),
            old(self).proc_man.proc_perms@ =~= Map::empty(),
            old(self).proc_man.thread_ptrs@ =~= Set::empty(),
            old(self).proc_man.thread_perms@ =~= Map::empty(),
            old(self).proc_man.scheduler.arr_seq@.len() == MAX_NUM_THREADS,
            old(self).proc_man.scheduler@ =~= Seq::empty(),
            old(self).proc_man.scheduler.len() =~= 0,
            old(self).proc_man.endpoint_ptrs@ =~= Set::empty(),
            old(self).proc_man.endpoint_perms@ =~= Map::empty(),
            old(self).proc_man.get_pcid_closure() =~= Set::empty(),
            old(self).proc_man.ioid_closure@ =~= Set::empty(),
            old(self).cpu_list.wf(),
            forall|i:CPUID| #![auto] 0<=i<NUM_CPUS ==> old(self).cpu_list@[i as int].wf(),
            forall|i:CPUID| #![auto] 0<=i<NUM_CPUS ==> old(self).cpu_list@[i as int].get_is_idle() == true,
            forall|i:CPUID, pcid: Pcid| #![auto] 0<=i<NUM_CPUS && 0 <= pcid< PCID_MAX ==> old(self).cpu_list@[i as int].tlb@[pcid] =~= Map::empty(),
            forall|i:CPUID, ioid: IOid| #![auto] 0<=i<NUM_CPUS && 0 <= ioid< IOID_MAX ==> old(self).cpu_list@[i as int].iotlb@[ioid] =~= Map::empty(),
            forall|thread_ptr:ThreadPtr| #![auto] old(self).proc_man.get_thread_ptrs().contains(thread_ptr) ==> old(self).proc_man.get_thread(thread_ptr).state != TRANSIT,
            init_pci_map.wf(),
            (forall|ioid:IOid,bus:u8,dev:u8,fun:u8|#![auto] 1<=ioid<IOID_MAX && 0<=bus<256 && 0<=dev<32 && 0<=fun<8 ==>
                (
                    init_pci_map@[(ioid,bus,dev,fun)] == false
                )),
            forall|bus:u8,dev:u8,fun:u8|#![auto] 0<=bus<256 && 0<=dev<32 && 0<=fun<8 ==> old(self).mmu_man.root_table.resolve(bus,dev,fun).is_None(),
    {
        if self.page_alloc.free_pages.len() < 3{
            return -1;
        }
        else{
            let (page_ptr1, page_perm1) = self.page_alloc.alloc_kernel_mem();
            let (page_ptr2, page_perm2) = self.page_alloc.alloc_kernel_mem();
            let (page_ptr3, page_perm3) = self.page_alloc.alloc_pagetable_mem();
            let new_ioid = self.mmu_man.new_iommutable(page_ptr3,page_perm3);
            self.mmu_man.pci_bitmap = init_pci_map;
            assert(new_ioid == old(self).mmu_man.free_ioids@[IOID_MAX - 1]);
            assert(new_ioid == 0);
            let new_proc = self.proc_man.new_proc(page_ptr1, page_perm1, 0, Some(new_ioid));
            let new_thread = self.proc_man.new_thread(dom0_pt_regs,page_ptr2, page_perm2,new_proc);
            assert(
                self.proc_man.wf());
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
            return 0;
        }
    }
}
}
