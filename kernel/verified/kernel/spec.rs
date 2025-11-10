use vstd::prelude::*;
use vstd::set::fold::*;

verus! {

use crate::allocator::page_allocator_spec_impl::*;
use crate::memory_manager::spec_impl::*;
use crate::process_manager::spec_proof::*;
use crate::util::page_ptr_util_u::*;
use vstd::simple_pptr::PointsTo;
use crate::pagetable::pagemap::PageMap;
use crate::array_vec::ArrayVec;
use crate::define::*;
use crate::quota::Quota;

pub struct Kernel {
    pub page_alloc: PageAllocator,
    pub mem_man: MemoryManager,
    pub proc_man: ProcessManager,
    pub page_mapping: Ghost<Map<PagePtr, Set<(ProcPtr, VAddr)>>>,
    /// @Xiangdong fix
    pub page_io_mapping: Ghost<Map<PagePtr, Set<(ProcPtr, VAddr)>>>,
}

//spec
impl Kernel {
    //Leakage freedom and memory safety
    pub open spec fn memory_wf(&self) -> bool {
        //Additional safety specs are embedded in page_alloc's specs
        &&& self.mem_man.page_closure().disjoint(
            self.proc_man.page_closure(),
        )
        //Leakage freedom. Internel leakage freedom are embedded recursively in mem_man and proc_man
        &&& self.mem_man.page_closure() + self.proc_man.page_closure()
            == self.page_alloc.allocated_pages_4k()
        //We are not using hugepages for now.
        &&& self.page_alloc.mapped_pages_2m() =~= Set::empty()
        &&& self.page_alloc.mapped_pages_1g() =~= Set::empty()
        &&& self.page_alloc.allocated_pages_2m() =~= Set::empty()
        &&& self.page_alloc.allocated_pages_1g() =~= Set::empty()
        &&& self.page_alloc.container_map_4k@.dom() =~= self.proc_man.container_dom()
        &&& self.page_alloc.container_map_2m@.dom() =~= self.proc_man.container_dom()
        &&& self.page_alloc.container_map_1g@.dom() =~= self.proc_man.container_dom()
    }

    pub open spec fn page_mapping_wf(&self) -> bool {
        &&& self.page_mapping@.dom().subset_of(self.page_alloc.mapped_pages_4k())
        &&& self.page_io_mapping@.dom().subset_of(self.page_alloc.mapped_pages_4k())
        &&& forall|page_ptr: PagePtr, p_ptr: ProcPtr, va: VAddr|
            #![trigger self.page_mapping@[page_ptr].contains((p_ptr, va))]
            #![trigger self.page_alloc.page_mappings(page_ptr).contains((self.proc_man.get_proc(p_ptr).pcid, va))]
            self.page_mapping@.dom().contains(page_ptr) && self.page_mapping@[page_ptr].contains(
                (p_ptr, va),
            ) ==> self.page_alloc.page_is_mapped(page_ptr) && self.proc_man.proc_dom().contains(
                p_ptr,
            ) && self.page_alloc.page_mappings(page_ptr).contains(
                (self.proc_man.get_proc(p_ptr).pcid, va),
            )
        &&& forall|page_ptr: PagePtr, pcid: Pcid, va: VAddr|
            #![trigger self.page_alloc.page_mappings(page_ptr).contains((pcid, va))]
            #![trigger self.page_mapping@[page_ptr].contains((self.mem_man.pcid_to_proc_ptr(pcid), va))]
            self.page_alloc.page_is_mapped(page_ptr) && self.page_alloc.page_mappings(
                page_ptr,
            ).contains((pcid, va)) ==> self.page_mapping@.dom().contains(page_ptr)
                && self.page_mapping@[page_ptr].contains((self.mem_man.pcid_to_proc_ptr(pcid), va))
    }

    pub open spec fn mapping_wf(&self) -> bool {
        &&& forall|pcid: Pcid, va: VAddr|
            #![auto]
            #![trigger self.mem_man.get_pagetable_mapping_by_pcid(pcid).dom().contains(va)]
            #![trigger self.page_alloc.page_is_mapped(self.mem_man.get_pagetable_mapping_by_pcid(pcid)[va].addr)]
            #![trigger self.page_alloc.page_mappings(self.mem_man.get_pagetable_mapping_by_pcid(pcid)[va].addr).contains((pcid,va))]
            self.mem_man.pcid_active(pcid) && self.mem_man.get_pagetable_mapping_by_pcid(
                pcid,
            ).dom().contains(va) ==> self.page_alloc.page_is_mapped(
                self.mem_man.get_pagetable_mapping_by_pcid(pcid)[va].addr,
            ) && self.page_alloc.page_mappings(
                self.mem_man.get_pagetable_mapping_by_pcid(pcid)[va].addr,
            ).contains((pcid, va))
        &&& forall|page_ptr: PagePtr, pcid: Pcid, va: VAddr|
            #![trigger self.page_alloc.page_mappings(page_ptr).contains((pcid,va))]
            self.page_alloc.page_is_mapped(page_ptr) && self.page_alloc.page_mappings(
                page_ptr,
            ).contains((pcid, va)) ==> va_4k_valid(va) && self.mem_man.pcid_active(pcid)
                && self.mem_man.get_pagetable_mapping_by_pcid(pcid).dom().contains(va)
                && self.mem_man.get_pagetable_mapping_by_pcid(pcid)[va].addr == page_ptr
        &&& forall|ioid: IOid, va: VAddr|
            #![trigger self.mem_man.get_iommu_table_mapping_by_ioid(ioid).dom().contains(va)]
            #![trigger self.page_alloc.page_is_mapped(self.mem_man.get_iommu_table_mapping_by_ioid(ioid)[va].addr)]
            #![trigger self.page_alloc.page_io_mappings(self.mem_man.get_iommu_table_mapping_by_ioid(ioid)[va].addr).contains((ioid,va))]
            self.mem_man.ioid_active(ioid) && self.mem_man.get_iommu_table_mapping_by_ioid(
                ioid,
            ).dom().contains(va) ==> self.page_alloc.page_is_mapped(
                self.mem_man.get_iommu_table_mapping_by_ioid(ioid)[va].addr,
            ) && self.page_alloc.page_io_mappings(
                self.mem_man.get_iommu_table_mapping_by_ioid(ioid)[va].addr,
            ).contains((ioid, va))
        &&& forall|page_ptr: PagePtr, ioid: IOid, va: VAddr|
            #![trigger self.page_alloc.page_io_mappings(page_ptr).contains((ioid,va))]
            self.page_alloc.page_is_mapped(page_ptr) && self.page_alloc.page_io_mappings(
                page_ptr,
            ).contains((ioid, va)) ==> va_4k_valid(va) && self.mem_man.ioid_active(ioid)
                && self.mem_man.get_iommu_table_mapping_by_ioid(ioid).dom().contains(va)
    }

    pub open spec fn pcid_ioid_wf(&self) -> bool {
        &&& forall|proc_ptr: ProcPtr|
            #![trigger self.proc_man.get_proc(proc_ptr).pcid]
            self.proc_man.proc_dom().contains(proc_ptr) ==> self.mem_man.pcid_active(
                self.proc_man.get_proc(proc_ptr).pcid,
            ) && self.mem_man.pcid_to_proc_ptr(self.proc_man.get_proc(proc_ptr).pcid) == proc_ptr
        &&& forall|pcid: Pcid|
            #![trigger self.mem_man.pcid_to_proc_ptr(pcid)]
            self.mem_man.pcid_active(pcid) ==> self.proc_man.proc_dom().contains(
                self.mem_man.pcid_to_proc_ptr(pcid),
            ) && self.proc_man.get_proc(self.mem_man.pcid_to_proc_ptr(pcid)).pcid == pcid
        &&& forall|proc_ptr: ProcPtr|
            #![trigger self.proc_man.get_proc(proc_ptr).ioid]
            self.proc_man.proc_dom().contains(proc_ptr) && self.proc_man.get_proc(
                proc_ptr,
            ).ioid.is_Some() ==> self.mem_man.ioid_active(
                self.proc_man.get_proc(proc_ptr).ioid.unwrap(),
            ) && self.mem_man.ioid_to_proc_ptr(self.proc_man.get_proc(proc_ptr).ioid.unwrap())
                == proc_ptr
        &&& forall|ioid: Pcid|
            #![trigger self.mem_man.ioid_to_proc_ptr(ioid)]
            self.mem_man.ioid_active(ioid) ==> self.proc_man.proc_dom().contains(
                self.mem_man.ioid_to_proc_ptr(ioid),
            ) && self.proc_man.get_proc(self.mem_man.ioid_to_proc_ptr(ioid)).ioid.is_Some()
                && self.proc_man.get_proc(self.mem_man.ioid_to_proc_ptr(ioid)).ioid.unwrap() == ioid
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.mem_man.wf()
        &&& self.page_alloc.wf()
        &&& self.proc_man.wf()
        &&& self.memory_wf()
        &&& self.mapping_wf()
        &&& self.pcid_ioid_wf()
        &&& self.page_mapping_wf()
    }

    pub open spec fn total_mem_4k_quota_wf(&self) -> bool {
        &&& self.get_num_of_free_pages() == self.container_dom().fold(
            0,
            |e: int, a: ContainerPtr| e + self.get_container(a).quota.mem_4k,
        )
    }

    pub open spec fn total_pcid_quota_wf(&self) -> bool {
        &&& self.mem_man.free_pcids.len() == self.container_dom().fold(
            0,
            |e: int, a: ContainerPtr| e + self.get_container(a).quota.pcid,
        )
    }

    pub open spec fn total_ioid_quota_wf(&self) -> bool {
        &&& self.mem_man.free_ioids.len() == self.container_dom().fold(
            0,
            |e: int, a: ContainerPtr| e + self.get_container(a).quota.ioid,
        )
    }

    pub open spec fn total_wf(&self) -> bool {
        &&& self.wf()
        &&& self.total_mem_4k_quota_wf()
    }
}

impl Kernel {
    pub proof fn container_thread_inv_1(&self)
        requires
            self.wf(),
        ensures
            forall|c_ptr: ContainerPtr, t_ptr: ThreadPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && self.thread_dom().contains(t_ptr)
                    && self.get_container(c_ptr).owned_threads@.contains(t_ptr) == false
                    ==> self.get_thread(t_ptr).owning_container != c_ptr,
    {
        self.proc_man.container_thread_inv_1();
    }

    pub proof fn proc_thread_inv_1(&self)
        requires
            self.wf(),
        ensures
            forall|p_ptr: ProcPtr, t_ptr: ThreadPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) && self.thread_dom().contains(t_ptr)
                    && self.get_proc(p_ptr).owned_threads@.contains(t_ptr) == false
                    ==> self.get_thread(t_ptr).owning_proc != p_ptr,
    {
        self.proc_man.proc_thread_inv_1();
    }

    pub proof fn process_inv(&self)
        requires
            self.wf(),
        ensures
            forall|p_ptr: ProcPtr|
                #![trigger self.proc_dom().contains(p_ptr)]
                #![trigger self.get_proc(p_ptr)]
                self.proc_dom().contains(p_ptr) ==> self.container_dom().contains(
                    self.get_proc(p_ptr).owning_container,
                ),
    {
        self.proc_man.process_inv();
    }

    pub proof fn container_subtree_inv(&self)
        requires
            self.wf(),
        ensures
            forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.get_container(c_ptr)]
                self.container_dom().contains(c_ptr) ==> self.get_container(
                    c_ptr,
                ).subtree_set@.subset_of(self.container_dom()) && self.get_container(
                    c_ptr,
                ).subtree_set@.contains(c_ptr) == false,
    {
        self.proc_man.container_subtree_inv();
    }

    pub proof fn container_subtree_disjoint_inv(&self)
        requires
            self.wf(),
        ensures
            forall|c_ptr_i: ContainerPtr, c_ptr_j: ContainerPtr|
                #![trigger  self.get_container(c_ptr_i).subtree_set@.insert(c_ptr_i), self.get_container(c_ptr_j).subtree_set@.insert(c_ptr_j)]
                self.container_dom().contains(c_ptr_i) && self.container_dom().contains(c_ptr_j)
                    && c_ptr_i != c_ptr_j && self.get_container(c_ptr_i).depth
                    == self.get_container(c_ptr_j).depth ==> self.get_container(
                    c_ptr_i,
                ).subtree_set@.insert(c_ptr_i).disjoint(
                    self.get_container(c_ptr_j).subtree_set@.insert(c_ptr_j),
                ),
    {
        self.proc_man.container_subtree_disjoint_inv();
    }

    pub proof fn container_owned_procs_disjoint_inv(&self)
        requires
            self.wf(),
        ensures
            forall|c_ptr_i: ContainerPtr, c_ptr_j: ContainerPtr|
                #![trigger  self.get_container(c_ptr_i).owned_procs, self.get_container(c_ptr_j).owned_procs]
                self.container_dom().contains(c_ptr_i) && self.container_dom().contains(c_ptr_j)
                    && c_ptr_i != c_ptr_j ==> self.get_container(c_ptr_i).owned_procs@.disjoint(
                    self.get_container(c_ptr_j).owned_procs@,
                ),
    {
        self.proc_man.container_owned_procs_disjoint_inv();
    }

    pub proof fn container_owned_threads_disjoint_inv(&self)
        requires
            self.wf(),
        ensures
            forall|c_ptr_i: ContainerPtr, c_ptr_j: ContainerPtr|
                #![trigger  self.get_container(c_ptr_i).owned_threads, self.get_container(c_ptr_j).owned_threads]
                self.container_dom().contains(c_ptr_i) && self.container_dom().contains(c_ptr_j)
                    && c_ptr_i != c_ptr_j ==> self.get_container(c_ptr_i).owned_threads@.disjoint(
                    self.get_container(c_ptr_j).owned_threads@,
                ),
    {
        self.proc_man.container_owned_threads_disjoint_inv();
    }

    pub proof fn container_inv(&self)
        requires
            self.wf(),
        ensures
            forall|c_ptr: ContainerPtr|
                #![trigger self.container_dom().contains(c_ptr)]
                #![trigger self.get_container(c_ptr).owned_cpus.wf()]
                #![trigger self.get_container(c_ptr).scheduler.wf()]
                self.container_dom().contains(c_ptr) ==> self.get_container(c_ptr).owned_cpus.wf()
                    && self.get_container(c_ptr).scheduler.wf(),
            forall|c_ptr: ContainerPtr, p_ptr: ProcPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).owned_procs@.contains(p_ptr) ==> self.proc_dom().contains(p_ptr),
            forall|c_ptr: ContainerPtr, t_ptr: ThreadPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && self.get_container(
                    c_ptr,
                ).owned_threads@.contains(t_ptr) ==> self.thread_dom().contains(t_ptr),
            forall|c_ptr_i: ContainerPtr, c_ptr_j: ContainerPtr, t_ptr: ThreadPtr|
                #![auto]
                c_ptr_i != c_ptr_j && self.container_dom().contains(c_ptr_i)
                    && self.container_dom().contains(c_ptr_j) && self.get_container(
                    c_ptr_i,
                ).owned_threads@.contains(t_ptr) ==> self.get_container(
                    c_ptr_j,
                ).owned_threads@.contains(t_ptr) == false,
    {
        self.proc_man.container_inv();
    }

    pub proof fn thread_inv(&self)
        requires
            self.wf(),
        ensures
            forall|t_ptr: ThreadPtr|
                #![trigger self.thread_dom().contains(t_ptr)]
                #![trigger self.get_thread(t_ptr).owning_container]
                #![trigger self.get_thread(t_ptr).owning_proc]
                self.thread_dom().contains(t_ptr) ==> self.container_dom().contains(
                    self.get_thread(t_ptr).owning_container,
                ) && self.get_container(
                    self.get_thread(t_ptr).owning_container,
                ).owned_threads@.contains(t_ptr) && self.get_container(
                    self.get_thread(t_ptr).owning_container,
                ).owned_procs@.contains(self.get_thread(t_ptr).owning_proc)
                    && self.proc_dom().contains(self.get_thread(t_ptr).owning_proc)
                    && self.get_thread(t_ptr).endpoint_descriptors.wf() && (self.get_thread(
                    t_ptr,
                ).ipc_payload.get_payload_as_va_range().is_Some() ==> self.get_thread(
                    t_ptr,
                ).ipc_payload.get_payload_as_va_range().unwrap().wf()) && (forall|i: int|
                    #![auto]
                    0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS && self.get_thread(
                        t_ptr,
                    ).endpoint_descriptors@[i].is_Some() ==> self.endpoint_dom().contains(
                        self.get_thread(t_ptr).endpoint_descriptors@[i].unwrap(),
                    )) && self.get_proc(self.get_thread(t_ptr).owning_proc).owning_container
                    == self.get_thread(t_ptr).owning_container && (self.get_thread(t_ptr).state
                    == ThreadState::BLOCKED ==> self.get_thread(
                    t_ptr,
                ).blocking_endpoint_ptr.is_Some() && self.endpoint_dom().contains(
                    self.get_thread(t_ptr).blocking_endpoint_ptr.unwrap(),
                )),
    {
        self.proc_man.thread_inv();
    }

    // @TODO: prove this
    #[verifier(external_body)]
    pub proof fn fold_change_mem_4k_lemma(&self, old: Kernel, mod_c_ptr: ContainerPtr)
        requires
            self.container_dom() == old.container_dom(),
            self.container_dom().contains(mod_c_ptr),
            forall|c_ptr: ContainerPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && c_ptr != mod_c_ptr ==> self.get_container(
                    c_ptr,
                ).quota.mem_4k == old.get_container(c_ptr).quota.mem_4k,
        ensures
            self.container_dom().fold(
                0,
                |e: int, a: ContainerPtr| e + self.get_container(a).quota.mem_4k,
            ) == old.container_dom().fold(
                0,
                |e: int, a: ContainerPtr| e + old.get_container(a).quota.mem_4k,
            ) - old.get_container(mod_c_ptr).quota.mem_4k + self.get_container(
                mod_c_ptr,
            ).quota.mem_4k,
    {
    }

    // @TODO: prove this
    #[verifier(external_body)]
    pub proof fn fold_mem_4k_lemma(&self)
        ensures
            forall|c_ptr: ContainerPtr|
                #![auto]
                self.container_dom().contains(c_ptr) ==> self.container_dom().fold(
                    0,
                    |e: int, a: ContainerPtr| e + self.get_container(a).quota.mem_4k,
                ) >= self.get_container(c_ptr).quota.mem_4k,
    {
    }

    // @TODO: prove this
    #[verifier(external_body)]
    pub proof fn fold_change_pcid_lemma(&self, old: Kernel, mod_c_ptr: ContainerPtr)
        requires
            self.container_dom() == old.container_dom(),
            self.container_dom().contains(mod_c_ptr),
            forall|c_ptr: ContainerPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && c_ptr != mod_c_ptr ==> self.get_container(
                    c_ptr,
                ).quota.pcid == old.get_container(c_ptr).quota.pcid,
        ensures
            self.container_dom().fold(
                0,
                |e: int, a: ContainerPtr| e + self.get_container(a).quota.pcid,
            ) == old.container_dom().fold(
                0,
                |e: int, a: ContainerPtr| e + old.get_container(a).quota.pcid,
            ) - old.get_container(mod_c_ptr).quota.pcid + self.get_container(mod_c_ptr).quota.pcid,
    {
    }

    // @TODO: prove this
    #[verifier(external_body)]
    pub proof fn fold_pcid_lemma(&self)
        ensures
            forall|c_ptr: ContainerPtr|
                #![auto]
                self.container_dom().contains(c_ptr) ==> self.container_dom().fold(
                    0,
                    |e: int, a: ContainerPtr| e + self.get_container(a).quota.pcid,
                ) >= self.get_container(c_ptr).quota.pcid,
    {
    }

    // NOTE: This lemma requires self.container_dom().finite() as a precondition to verify.
    // This is necessary because the fold operation requires finite sets.
    // The original specification did not include this precondition, but it appears to be
    // a necessary condition for the postcondition to be meaningful (since the postcondition
    // itself uses fold, which requires finiteness).
    pub proof fn fold_change_ioid_lemma(&self, old: Kernel, mod_c_ptr: ContainerPtr)
        requires
            self.container_dom() == old.container_dom(),
            self.container_dom().contains(mod_c_ptr),
            self.container_dom().finite(), // Added: necessary for fold operations
            forall|c_ptr: ContainerPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && c_ptr != mod_c_ptr ==> self.get_container(
                    c_ptr,
                ).quota.ioid == old.get_container(c_ptr).quota.ioid,
        ensures
            self.container_dom().fold(
                0,
                |e: int, a: ContainerPtr| e + self.get_container(a).quota.ioid,
            ) == old.container_dom().fold(
                0,
                |e: int, a: ContainerPtr| e + old.get_container(a).quota.ioid,
            ) - old.get_container(mod_c_ptr).quota.ioid + self.get_container(mod_c_ptr).quota.ioid,
    {
        
        // The key insight: decompose the set by removing mod_c_ptr
        let dom = self.container_dom();
        let rest = dom.remove(mod_c_ptr);
        
        // Define the fold functions
        let f_self = |e: int, a: ContainerPtr| e + self.get_container(a).quota.ioid;
        let f_old = |e: int, a: ContainerPtr| e + old.get_container(a).quota.ioid;
        
        // Use fold lemmas from vstd to decompose the fold
        lemma_fold_insert(rest, 0, f_self, mod_c_ptr);
        lemma_fold_insert(rest, 0, f_old, mod_c_ptr);
        
        // Prove that the fold over rest is the same for both kernels
        lemma_fold_pointwise_equal(
            rest,
            0,
            f_self,
            f_old,
            |c_ptr: ContainerPtr| self.get_container(c_ptr).quota.ioid == old.get_container(c_ptr).quota.ioid
        );
        
    }


    // @TODO: prove this
    #[verifier(external_body)]
    pub proof fn fold_ioid_lemma(&self)
        ensures
            forall|c_ptr: ContainerPtr|
                #![auto]
                self.container_dom().contains(c_ptr) ==> self.container_dom().fold(
                    0,
                    |e: int, a: ContainerPtr| e + self.get_container(a).quota.ioid,
                ) >= self.get_container(c_ptr).quota.ioid,
    {
    }
}

// General helper lemma: if two functions agree on all elements, their folds are equal
proof fn lemma_fold_pointwise_equal<A>(
    s: Set<A>,
    z: int,
    f1: spec_fn(int, A) -> int,
    f2: spec_fn(int, A) -> int,
    property: spec_fn(A) -> bool,
)
    requires
        s.finite(),
        is_fun_commutative(f1),
        is_fun_commutative(f2),
        forall |a: A| #![auto] s.contains(a) ==> property(a),
        forall |a: A, b: int| s.contains(a) ==> #[trigger] f1(b, a) == #[trigger] f2(b, a),
    ensures
        s.fold(z, f1) == s.fold(z, f2),
    decreases s.len(),
{
    
    if s.len() == 0 {
        lemma_fold_empty(z, f1);
        lemma_fold_empty(z, f2);
        assert(s =~= Set::empty());
    } else {
        let a = s.choose();
        let smaller = s.remove(a);
        
        lemma_fold_insert(smaller, z, f1, a);
        lemma_fold_insert(smaller, z, f2, a);
        lemma_fold_pointwise_equal(smaller, z, f1, f2, property);
    }
}



impl Kernel {
    pub fn new() -> (ret: Self) {
        Kernel {
            page_alloc: PageAllocator::new(),
            mem_man: MemoryManager::new(),
            proc_man: ProcessManager::new(),
            page_mapping: Ghost(Map::<PagePtr, Set<(ProcPtr, VAddr)>>::empty()),
            page_io_mapping: Ghost(Map::<PagePtr, Set<(ProcPtr, VAddr)>>::empty()),
        }
    }

    #[verifier(external_body)]
    pub fn kernel_init(
        &mut self,
        dom_0_container_ptr: ContainerPtr,
        dom_0_proc_ptr: ProcPtr,
        dom_0_thread_ptr: ThreadPtr,
        boot_pages: &mut ArrayVec::<(PageState, usize), NUM_PAGES>,
        dom0_page_map_ptr: PageMapPtr,
        kernel_entry: PageMapPtr,
        page_perm_0: Tracked<PagePerm4k>,
        page_perm_1: Tracked<PagePerm4k>,
        page_perm_2: Tracked<PagePerm4k>,
        dom0_page_map_perm: Tracked<PointsTo<PageMap>>,
    ) {
        self.page_alloc.init(boot_pages, dom_0_container_ptr);
        self.mem_man.init(
            dom0_page_map_ptr,
            kernel_entry,
            dom_0_proc_ptr,
            &mut self.page_alloc,
            dom0_page_map_perm,
        );
        self.proc_man.init(
            dom_0_container_ptr,
            dom_0_proc_ptr,
            dom_0_thread_ptr,
            Quota {
                mem_4k: self.page_alloc.free_pages_4k.len(),
                mem_2m: 0,
                mem_1g: 0,
                pcid: 4095,
                ioid: 4096,
            },
            page_perm_0,
            page_perm_1,
            page_perm_2,
        );
    }
}

} // verus!
