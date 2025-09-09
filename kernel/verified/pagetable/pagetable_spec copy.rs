use vstd::prelude::*;

verus! {

use crate::define::*;
use vstd::simple_pptr::*;
use crate::util::page_ptr_util_u::*;
use crate::pagetable::pagemap_util_t::*;
use crate::pagetable::entry::*;
use crate::pagetable::pagemap::*;
use crate::lemma::lemma_u::*;

// pub open   spec fn map_entry_equals_to_page_entry_unwrapped(m:MapEntry, p:PageEntry) -> bool{
//     &&&
//     m.addr == p.addr
//     &&&
//     m.write == p.perm.write
//     &&&
//     m.execute_disable == p.perm.execute_disable
// }
// pub open   spec fn map_entry_equals_to_page_entry(m:MapEntry, p:Option<PageEntry>) -> bool {
//     if m.is_Some() != p.is_Some(){
//         return false;
//     }else if m.is_None() && p.is_None() {
//         return true;
//     }else{
//         return map_entry_equals_to_page_entry_unwrapped(m.get_Some_0(), p.get_Some_0());
//     }
// }
pub struct PageTable {
    pub cr3: PageMapPtr,
    pub pcid: Option<Pcid>,
    pub ioid: Option<IOid>,
    pub kernel_l4_end: usize,
    pub l4_table: Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    pub l3_rev_map: Ghost<Map<PageMapPtr, (L4Index)>>,
    pub l3_tables: Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    pub l2_rev_map: Ghost<Map<PageMapPtr, (L4Index, L3Index)>>,
    pub l2_tables: Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    pub l1_rev_map: Ghost<Map<PageMapPtr, (L4Index, L3Index, L2Index)>>,
    pub l1_tables: Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    pub mapping_4k: Ghost<Map<VAddr, MapEntry>>,
    pub mapping_2m: Ghost<Map<VAddr, MapEntry>>,
    pub mapping_1g: Ghost<Map<VAddr, MapEntry>>,
    pub kernel_entries: Ghost<Seq<PageEntry>>,
    pub tlb_mapping_4k: Ghost<Seq<Map<VAddr, MapEntry>>>,
    pub tlb_mapping_2m: Ghost<Seq<Map<VAddr, MapEntry>>>,
    pub tlb_mapping_1g: Ghost<Seq<Map<VAddr, MapEntry>>>,
}

impl PageTable {
    pub fn new(
        pcid: Option<Pcid>,
        ioid: Option<IOid>,
        kernel_entries_ghost: Ghost<Seq<PageEntry>>,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
        mem_end_l4_index: usize,
    ) -> (ret: Self)
        requires
            pcid.is_Some() != ioid.is_Some(),
            page_ptr_valid(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            kernel_entries_ghost@.len() == mem_end_l4_index,
            forall|i: usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                mem_end_l4_index <= i < 512 ==> page_map_perm.value()[i].is_empty(),
            forall|i: usize|
                #![trigger kernel_entries_ghost@[i as int]]
                #![trigger page_map_perm.value()[i]]
                0 <= i < mem_end_l4_index ==> kernel_entries_ghost@[i as int]
                    == page_map_perm.value()[i],
            0 <= mem_end_l4_index < 512,
        ensures
            ret.wf(),
            ret.pcid == pcid,
            ret.ioid == ioid,
            ret.kernel_l4_end == mem_end_l4_index,
            ret.page_closure() == Set::empty().insert(page_map_ptr),
            ret.mapping_4k() == Map::<VAddr, MapEntry>::empty(),
            ret.mapping_2m() == Map::<VAddr, MapEntry>::empty(),
            ret.mapping_1g() == Map::<VAddr, MapEntry>::empty(),
            ret.kernel_entries =~= kernel_entries_ghost,
            ret.is_empty(),
    {
        assert(forall|i: usize|
            #![trigger page_map_perm.value()[i].is_empty()]
            #![trigger page_map_perm.value()[i].perm.present]
            mem_end_l4_index <= i < 512 ==> page_map_perm.value()[i].is_empty()
                && page_map_perm.value()[i].perm.present == false
                && page_map_perm.value()[i].perm.write == false
                && page_map_perm.value()[i].perm.execute_disable == false);
        let mut ret = Self {
            cr3: page_map_ptr,
            pcid: pcid,
            ioid: ioid,
            kernel_l4_end: mem_end_l4_index,
            l4_table: Tracked(Map::<PageMapPtr, PointsTo<PageMap>>::tracked_empty()),
            l3_rev_map: Ghost(Map::<PageMapPtr, (L4Index)>::empty()),
            l3_tables: Tracked(Map::<PageMapPtr, PointsTo<PageMap>>::tracked_empty()),
            l2_rev_map: Ghost(Map::<PageMapPtr, (L4Index, L3Index)>::empty()),
            l2_tables: Tracked(Map::<PageMapPtr, PointsTo<PageMap>>::tracked_empty()),
            l1_rev_map: Ghost(Map::<PageMapPtr, (L4Index, L3Index, L2Index)>::empty()),
            l1_tables: Tracked(Map::<PageMapPtr, PointsTo<PageMap>>::tracked_empty()),
            mapping_4k: Ghost(Map::<VAddr, MapEntry>::empty()),
            mapping_2m: Ghost(Map::<VAddr, MapEntry>::empty()),
            mapping_1g: Ghost(Map::<VAddr, MapEntry>::empty()),
            kernel_entries: kernel_entries_ghost,
            tlb_mapping_4k: Ghost(
                Seq::new(NUM_CPUS as nat, |i: int| Map::<VAddr, MapEntry>::empty()),
            ),
            tlb_mapping_2m: Ghost(
                Seq::new(NUM_CPUS as nat, |i: int| Map::<VAddr, MapEntry>::empty()),
            ),
            tlb_mapping_1g: Ghost(
                Seq::new(NUM_CPUS as nat, |i: int| Map::<VAddr, MapEntry>::empty()),
            ),
        };
        assert(ret.l3_tables@.dom() == Set::<PageMapPtr>::empty());
        assert(ret.l2_tables@.dom() == Set::<PageMapPtr>::empty());
        assert(ret.l1_tables@.dom() == Set::<PageMapPtr>::empty());
        assert(ret.l4_table@.dom() == Set::<PageMapPtr>::empty());
        proof {
            ret.l4_table.borrow_mut().tracked_insert(page_map_ptr, page_map_perm);
        }
        assert(ret.l3_tables@.dom() == Set::<PageMapPtr>::empty());
        assert(ret.l2_tables@.dom() == Set::<PageMapPtr>::empty());
        assert(ret.l1_tables@.dom() == Set::<PageMapPtr>::empty());
        assert(ret.l4_table@.dom() == Set::<PageMapPtr>::empty().insert(page_map_ptr));
        assert(ret.page_closure() == Set::empty().insert(page_map_ptr));

        assert(ret.wf_l4());
        assert(ret.wf_l3());
        assert(ret.wf_l2());
        assert(ret.wf_l1());
        assert(ret.wf_mapping_4k());
        assert(ret.wf_mapping_2m());
        assert(ret.wf_mapping_1g());
        assert(ret.user_only());
        assert(ret.rwx_upper_level_entries());
        assert(ret.present_or_zero());
        assert(ret.table_pages_wf());
        assert(ret.kernel_entries_wf());
        assert(ret.pcid_ioid_wf());
        assert(ret.tlb_wf());
        assert(ret.tlb_submap_of_mapping());

        ret
    }

    pub open spec fn is_empty(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.l4_table@[self.cr3].value()[i].perm.present]
            self.kernel_l4_end <= i < 512 ==> self.l4_table@[self.cr3].value()[i].is_empty()
        &&& self.l3_tables@.dom() == Set::<PageMapPtr>::empty()
        &&& self.l2_tables@.dom() == Set::<PageMapPtr>::empty()
        &&& self.l1_tables@.dom() == Set::<PageMapPtr>::empty()
        &&& self.mapping_4k() == Map::<VAddr, MapEntry>::empty()
        &&& self.mapping_2m() == Map::<VAddr, MapEntry>::empty()
        &&& self.mapping_1g() == Map::<VAddr, MapEntry>::empty()
    }

    pub open   spec fn page_closure(&self) -> Set<PagePtr> {
        self.l3_tables@.dom() + self.l2_tables@.dom() + self.l1_tables@.dom() + self.l4_table@.dom()
    }

    pub open   spec fn mapping_4k(&self) -> Map<VAddr, MapEntry> {
        self.mapping_4k@
    }

    pub open   spec fn mapping_2m(&self) -> Map<VAddr, MapEntry> {
        self.mapping_2m@
    }

    pub open   spec fn mapping_1g(&self) -> Map<VAddr, MapEntry> {
        self.mapping_1g@
    }

    pub open   spec fn page_not_mapped(&self, pa: PAddr) -> bool {
        &&& self.mapped_4k_pages().contains(pa) == false
        &&& self.mapped_2m_pages().contains(pa) == false
        &&& self.mapped_1g_pages().contains(pa) == false
    }

    pub open   spec fn mapped_4k_pages(&self) -> Set<PAddr> {
        Set::<PAddr>::new(|pa: PAddr| self.is_4k_pa_mapped(pa))
    }

    pub open   spec fn is_4k_pa_mapped(&self, pa: PAddr) -> bool {
        exists|va: VAddr|
            #![auto]
            self.mapping_4k().dom().contains(va) && self.mapping_4k()[va].addr == pa
    }

    pub open   spec fn mapped_2m_pages(&self) -> Set<PAddr> {
        Set::<PAddr>::new(|pa: PAddr| self.is_2m_pa_mapped(pa))
    }

    pub open   spec fn is_2m_pa_mapped(&self, pa: PAddr) -> bool {
        exists|va: VAddr|
            #![auto]
            self.mapping_2m().dom().contains(va) && self.mapping_2m()[va].addr == pa
    }

    pub open   spec fn mapped_1g_pages(&self) -> Set<PAddr> {
        Set::<PAddr>::new(|pa: PAddr| self.is_1g_pa_mapped(pa))
    }

    pub open   spec fn is_1g_pa_mapped(&self, pa: PAddr) -> bool {
        exists|va: VAddr|
            #![auto]
            self.mapping_1g().dom().contains(va) && self.mapping_1g()[va].addr == pa
    }

    pub open   spec fn pcid_ioid_wf(&self) -> bool {
        self.pcid.is_Some() != self.ioid.is_Some()
    }

    pub open   spec fn tlb_wf(&self) -> bool {
        &&& self.tlb_mapping_4k@.len() == NUM_CPUS
        &&& self.tlb_mapping_2m@.len() == NUM_CPUS
        &&& self.tlb_mapping_1g@.len() == NUM_CPUS
    }

    pub open   spec fn tlb_submap_of_mapping(&self) -> bool {
        forall|cpu_id: CpuId|
            #![auto]
            0 <= cpu_id < NUM_CPUS ==> self.tlb_mapping_4k@[cpu_id as int].submap_of(
                self.mapping_4k@,
            ) && self.tlb_mapping_2m@[cpu_id as int].submap_of(self.mapping_2m@)
                && self.tlb_mapping_1g@[cpu_id as int].submap_of(self.mapping_1g@)
    }

    pub open   spec fn wf_l4(&self) -> bool {
        // &&&
        // self.cr3 != 0
        &&& self.l4_table@.dom() =~= Set::<PageMapPtr>::empty().insert(self.cr3)
        &&& self.cr3 == self.l4_table@[self.cr3].addr()
        &&& self.l4_table@[self.cr3].is_init()
        &&& self.l4_table@[self.cr3].value().wf()
        //L4 table only maps to L3
        &&& forall|i: L4Index, j: L4Index|
         // #![trigger self.l4_table@[self.cr3].value()[i].perm.present, self.l4_table@[self.cr3].value()[j].perm.present]
        //    #![trigger self.l4_table@[self.cr3].value()[i].perm.present, self.l4_table@[self.cr3].value()[j].perm.present, self.l4_table@[self.cr3].value()[i].addr, self.l4_table@[self.cr3].value()[j].addr]
            #![trigger self.l4_table@[self.cr3].value()[i], self.l4_table@[self.cr3].value()[j]]
            i != j && self.kernel_l4_end <= i < 512
                && self.l4_table@[self.cr3].value()[i].perm.present && self.kernel_l4_end <= j < 512
                && self.l4_table@[self.cr3].value()[j].perm.present
                ==> self.l4_table@[self.cr3].value()[i].addr
                != self.l4_table@[self.cr3].value()[j].addr
        &&& forall|i: L4Index|
         // #![trigger self.l4_table@[self.cr3].value()[i].perm.present]

            // #![trigger self.l2_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)]
            // #![trigger self.l1_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)]
            #![trigger self.l4_table@[self.cr3].value()[i]]
            self.kernel_l4_end <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present
                ==> self.l2_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)
                == false && self.l1_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)
                == false && self.cr3
                != self.l4_table@[self.cr3].value()[i].addr
        // no self mapping
        &&& forall|i: L4Index|
         // #![trigger self.l4_table@[self.cr3].value()[i].perm.present]

            // #![trigger self.l4_table@[self.cr3].value()[i].addr]
            #![trigger self.l4_table@[self.cr3].value()[i]]
            self.kernel_l4_end <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present
                ==> self.cr3
                != self.l4_table@[self.cr3].value()[i].addr
        //all l4 points to valid l3 tables
        &&& forall|i: L4Index|
            // #![trigger self.l3_tables@.dom().contains(self.l4_table@[self.cr3].value()[i].addr)]
            #![trigger self.l4_table@[self.cr3].value()[i]]
            self.kernel_l4_end <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present
                && !self.l4_table@[self.cr3].value()[i].perm.ps ==> self.l3_tables@.dom().contains(
                self.l4_table@[self.cr3].value()[i].addr,
            )
            //no hugepage in L4 (hardware limit)
        &&& forall|i: L4Index|
            #![trigger self.l4_table@[self.cr3].value()[i].perm.ps]
            self.kernel_l4_end <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present
                ==> !self.l4_table@[self.cr3].value()[i].perm.ps
    }

    pub open   spec fn wf_l3(&self) -> bool {
        // &&&
        // self.l3_tables@.dom().contains(0) == false
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables@[p].addr()]
            self.l3_tables@.dom().contains(p) ==> self.l3_tables@[p].addr() == p
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables@[p].is_init()]
            self.l3_tables@.dom().contains(p) ==> self.l3_tables@[p].is_init()
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables@[p].value().wf()]
            self.l3_tables@.dom().contains(p) ==> self.l3_tables@[p].value().wf()
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_rev_map@.dom().contains(p)]
            #![trigger self.l3_rev_map@[p]]
            self.l3_tables@.dom().contains(p) ==> self.kernel_l4_end <= self.l3_rev_map@[p] < 512
                && self.l3_rev_map@.dom().contains(p) && self.spec_resolve_mapping_l4(
                self.l3_rev_map@[p],
            ).is_Some() && self.spec_resolve_mapping_l4(self.l3_rev_map@[p]).get_Some_0().addr
                == p
            //L3 tables unique within
        &&& forall|p: PageMapPtr, l3i: L3Index, l3j: L3Index|
            // #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[l3i].addr, self.l3_tables@[p].value()[l3j].addr, self.l3_tables@[p].value()[l3i].perm.ps, self.l3_tables@[p].value()[l3j].perm.ps, self.l3_tables@[p].value()[l3i].addr, self.l3_tables@[p].value()[l3j].addr]
             #![trigger self.l3_tables@[p].value()[l3i], self.l3_tables@[p].value()[l3j]]
            self.l3_tables@.dom().contains(p) && l3i != l3j && 0 <= l3i < 512 && 0 <= l3j < 512
                && self.l3_tables@[p].value()[l3i].perm.present
                && self.l3_tables@[p].value()[l3j].perm.present
                && !self.l3_tables@[p].value()[l3i].perm.ps
                && !self.l3_tables@[p].value()[l3j].perm.ps ==> self.l3_tables@[p].value()[l3i].addr
                != self.l3_tables@[p].value()[l3j].addr
            //L3 tables are disjoint
        &&& forall|pi: PageMapPtr, pj: PageMapPtr, l3i: L3Index, l3j: L3Index|
            // #![trigger self.l3_tables@.dom().contains(pi), self.l3_tables@.dom().contains(pj), self.l3_tables@[pi].value()[l3i].addr, self.l3_tables@[pj].value()[l3j].addr, self.l3_tables@[pi].value()[l3i].perm.ps, self.l3_tables@[pj].value()[l3j].perm.ps, self.l3_tables@[pi].value()[l3i].perm.present, self.l3_tables@[pj].value()[l3j].perm.present]
            #![trigger self.l3_tables@[pi].value()[l3i], self.l3_tables@[pj].value()[l3j]]
            pi != pj && self.l3_tables@.dom().contains(pi) && self.l3_tables@.dom().contains(pj)
                && 0 <= l3i < 512 && 0 <= l3j < 512 && self.l3_tables@[pi].value()[l3i].perm.present
                && self.l3_tables@[pj].value()[l3j].perm.present
                && !self.l3_tables@[pi].value()[l3i].perm.ps
                && !self.l3_tables@[pj].value()[l3j].perm.ps
                ==> self.l3_tables@[pi].value()[l3i].addr
                != self.l3_tables@[pj].value()[l3j].addr
            //L3 tables does not map to L4 or L1
        &&& forall|p: PageMapPtr, i: L3Index|
            // #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)]
            // #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l1_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)]
            // #![trigger self.l3_tables@.dom().contains(p), self.l3_tables@[p].value()[i].perm.present, self.l3_tables@[p].value()[i].addr]
            #![trigger self.l3_tables@[p].value()[i]]
            self.l3_tables@.dom().contains(p) && 0 <= i < 512
                && self.l3_tables@[p].value()[i].perm.present ==> self.l3_tables@.dom().contains(
                self.l3_tables@[p].value()[i].addr,
            ) == false && self.l1_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)
                == false && self.cr3
                != self.l3_tables@[p].value()[i].addr
        // all l3 points to valid l2 tables
        &&& forall|p: PageMapPtr, i: L3Index|
            // #![trigger self.l3_tables@[p].value()[i].perm.present, self.l3_tables@[p].value()[i].perm.ps, self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)]
        // #![trigger self.l2_tables@.dom().contains(self.l3_tables@[p].value()[i].addr)]
            #![trigger self.l3_tables@[p].value()[i]]
            self.l3_tables@.dom().contains(p) && 0 <= i < 512
                && self.l3_tables@[p].value()[i].perm.present
                && !self.l3_tables@[p].value()[i].perm.ps ==> self.l2_tables@.dom().contains(
                self.l3_tables@[p].value()[i].addr,
            )
    }

    pub open   spec fn wf_l2(&self) -> bool {
        // &&&
        // self.l2_tables@.dom().contains(0) == false
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables@[p].addr()]
            self.l2_tables@.dom().contains(p) ==> self.l2_tables@[p].addr() == p
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables@[p].is_init()]
            self.l2_tables@.dom().contains(p) ==> self.l2_tables@[p].is_init()
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables@[p].value().wf()]
            self.l2_tables@.dom().contains(p)
                ==> self.l2_tables@[p].value().wf()
        // all l2 tables exist in l3 mapping
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_rev_map@[p]]
            #![trigger self.l2_rev_map@.dom().contains(p)]
            self.l2_tables@.dom().contains(p) ==> self.l2_rev_map@.dom().contains(p)
                && self.kernel_l4_end <= self.l2_rev_map@[p].0 < 512 && 0 <= self.l2_rev_map@[p].1
                < 512 && self.spec_resolve_mapping_l3(
                self.l2_rev_map@[p].0,
                self.l2_rev_map@[p].1,
            ).is_Some() && self.spec_resolve_mapping_l3(
                self.l2_rev_map@[p].0,
                self.l2_rev_map@[p].1,
            ).get_Some_0().addr == p
            // L2 mappings are unique within
        &&& forall|p: PageMapPtr, l2i: L2Index, l2j: L2Index|
            // #![trigger self.l2_tables@.dom().contains(p), self.l2_tables@[p].value()[l2i].perm.present, self.l2_tables@[p].value()[l2j].perm.present, self.l2_tables@[p].value()[l2i].perm.ps, self.l2_tables@[p].value()[l2j].perm.ps]
            #![trigger self.l2_tables@[p].value()[l2i], self.l2_tables@[p].value()[l2j]]
            self.l2_tables@.dom().contains(p) && l2i != l2j && 0 <= l2i < 512 && 0 <= l2j < 512
                && self.l2_tables@[p].value()[l2i].perm.present
                && self.l2_tables@[p].value()[l2j].perm.present
                && !self.l2_tables@[p].value()[l2i].perm.ps
                && !self.l2_tables@[p].value()[l2j].perm.ps ==> self.l2_tables@[p].value()[l2i].addr
                != self.l2_tables@[p].value()[l2j].addr
            // L2 mappings are unique
        &&& forall|pi: PageMapPtr, pj: PageMapPtr, l2i: L2Index, l2j: L2Index|
            // #![trigger self.l2_tables@.dom().contains(pi), self.l2_tables@.dom().contains(pj),
            //     self.l2_tables@[pi].value()[l2i].perm.present, self.l2_tables@[pj].value()[l2j].perm.present,
            //     self.l2_tables@[pi].value()[l2i].perm.ps, self.l2_tables@[pj].value()[l2j].perm.ps]
            #![trigger self.l2_tables@[pi].value()[l2i], self.l2_tables@[pj].value()[l2j]]
            pi != pj && self.l2_tables@.dom().contains(pi) && self.l2_tables@.dom().contains(pj)
                && 0 <= l2i < 512 && 0 <= l2j < 512 && self.l2_tables@[pi].value()[l2i].perm.present
                && self.l2_tables@[pj].value()[l2j].perm.present
                && !self.l2_tables@[pi].value()[l2i].perm.ps
                && !self.l2_tables@[pj].value()[l2j].perm.ps
                ==> self.l2_tables@[pi].value()[l2i].addr
                != self.l2_tables@[pj].value()[l2j].addr
            // L2 does not map to L4, L3, or self
        &&& forall|p: PageMapPtr, i: L2Index|
            // #![trigger self.l2_tables@.dom().contains(p), self.l2_tables@[p].value()[i].perm.present, self.l2_tables@.dom().contains(self.l2_tables@[p].value()[i].addr)]
            // #![trigger self.l2_tables@.dom().contains(p), self.l2_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l2_tables@[p].value()[i].addr)]
            // #![trigger self.l2_tables@.dom().contains(p), self.l2_tables@[p].value()[i].perm.present, self.l2_tables@[p].value()[i].addr]
            
            #![trigger self.l2_tables@[p].value()[i]]
            self.l2_tables@.dom().contains(p) && 0 <= i < 512
                && self.l2_tables@[p].value()[i].perm.present ==> self.l2_tables@.dom().contains(
                self.l2_tables@[p].value()[i].addr,
            ) == false && self.l3_tables@.dom().contains(self.l2_tables@[p].value()[i].addr)
                == false && self.cr3
                != self.l2_tables@[p].value()[i].addr
        // all l2 points to valid l1 tables
        &&& forall|p: PageMapPtr, i: L2Index|
            // #![trigger self.l1_tables@.dom().contains(self.l2_tables@[p].value()[i].addr), self.l2_tables@[p].value()[i].perm.present, self.l2_tables@[p].value()[i].perm.ps]
            #![trigger self.l2_tables@[p].value()[i]]
            self.l2_tables@.dom().contains(p) && 0 <= i < 512
                && self.l2_tables@[p].value()[i].perm.present
                && !self.l2_tables@[p].value()[i].perm.ps ==> self.l1_tables@.dom().contains(
                self.l2_tables@[p].value()[i].addr,
            )
    }

    pub open   spec fn wf_l1(&self) -> bool {
        // &&&
        // self.l1_tables@.dom().contains(0) == false
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables@[p].addr()]
            self.l1_tables@.dom().contains(p) ==> self.l1_tables@[p].addr() == p
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables@[p].is_init()]
            self.l1_tables@.dom().contains(p) ==> self.l1_tables@[p].is_init()
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables@[p].value().wf()]
            self.l1_tables@.dom().contains(p)
                ==> self.l1_tables@[p].value().wf()
        // all l1 tables exist in l2 mapping
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_rev_map@.dom().contains(p)]
            #![trigger self.l1_rev_map@[p]]
            self.l1_tables@.dom().contains(p) ==> self.l1_rev_map@.dom().contains(p)
                && self.kernel_l4_end <= self.l1_rev_map@[p].0 < 512 && 0 <= self.l1_rev_map@[p].1
                < 512 && 0 <= self.l1_rev_map@[p].2 < 512 && self.spec_resolve_mapping_l2(
                self.l1_rev_map@[p].0,
                self.l1_rev_map@[p].1,
                self.l1_rev_map@[p].2,
            ).is_Some() && self.spec_resolve_mapping_l2(
                self.l1_rev_map@[p].0,
                self.l1_rev_map@[p].1,
                self.l1_rev_map@[p].2,
            ).get_Some_0().addr == p
            // no l1 tables map to other levels
        &&& forall|p: PageMapPtr, i: L1Index|
            // #![trigger self.l1_tables@.dom().contains(p), self.l1_tables@[p].value()[i].perm.present, self.l2_tables@.dom().contains(self.l1_tables@[p].value()[i].addr)]
            // #![trigger self.l1_tables@.dom().contains(p), self.l1_tables@[p].value()[i].perm.present, self.l3_tables@.dom().contains(self.l1_tables@[p].value()[i].addr)]
            // #![trigger self.l1_tables@.dom().contains(p), self.l1_tables@[p].value()[i].perm.present, self.l1_tables@[p].value()[i].addr]
            #![trigger self.l1_tables@[p].value()[i]]
            self.l1_tables@.dom().contains(p) && 0 <= i < 512
                && self.l1_tables@[p].value()[i].perm.present ==> self.l2_tables@.dom().contains(
                self.l1_tables@[p].value()[i].addr,
            ) == false && self.l3_tables@.dom().contains(self.l1_tables@[p].value()[i].addr)
                == false && self.cr3
                != self.l1_tables@[p].value()[i].addr
        // no hugepage in l1
        &&& forall|p: PageMapPtr, i: L1Index|
            #![trigger self.l1_tables@[p].value()[i].perm.ps]
            self.l1_tables@.dom().contains(p) && 0 <= i < 512
                && self.l1_tables@[p].value()[i].perm.present
                ==> !self.l1_tables@[p].value()[i].perm.ps
    }

    pub open   spec fn user_only(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.l4_table@[self.cr3].value()[i].perm.user]
            self.kernel_l4_end <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present
                ==> self.l4_table@[self.cr3].value()[i].perm.user
        &&& forall|p: PageMapPtr, i: L3Index|
            #![trigger self.l3_tables@[p].value()[i].perm.user]
            self.l3_tables@.dom().contains(p) && 0 <= i < 512
                && self.l3_tables@[p].value()[i].perm.present
                ==> self.l3_tables@[p].value()[i].perm.user
        &&& forall|p: PageMapPtr, i: L2Index|
            #![trigger self.l2_tables@[p].value()[i].perm.user]
            self.l2_tables@.dom().contains(p) && 0 <= i < 512
                && self.l2_tables@[p].value()[i].perm.present
                ==> self.l2_tables@[p].value()[i].perm.user
        &&& forall|p: PageMapPtr, i: L1Index|
            #![trigger self.l1_tables@[p].value()[i].perm.user]
            self.l1_tables@.dom().contains(p) && 0 <= i < 512
                && self.l1_tables@[p].value()[i].perm.present
                ==> self.l1_tables@[p].value()[i].perm.user
    }

    pub open   spec fn present_or_zero(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.l4_table@[self.cr3].value()[i].is_empty()]
            self.kernel_l4_end <= i < 512 && !self.l4_table@[self.cr3].value()[i].perm.present
                ==> self.l4_table@[self.cr3].value()[i].is_empty()
        &&& forall|p: PageMapPtr, i: L3Index|
            #![trigger self.l3_tables@[p].value()[i].is_empty()]
            self.l3_tables@.dom().contains(p) && 0 <= i < 512
                && !self.l3_tables@[p].value()[i].perm.present
                ==> self.l3_tables@[p].value()[i].is_empty()
        &&& forall|p: PageMapPtr, i: L2Index|
            #![trigger self.l2_tables@[p].value()[i].is_empty()]
            self.l2_tables@.dom().contains(p) && 0 <= i < 512
                && !self.l2_tables@[p].value()[i].perm.present
                ==> self.l2_tables@[p].value()[i].is_empty()
        &&& forall|p: PageMapPtr, i: L1Index|
            #![trigger self.l1_tables@[p].value()[i].is_empty()]
            self.l1_tables@.dom().contains(p) && 0 <= i < 512
                && !self.l1_tables@[p].value()[i].perm.present
                ==> self.l1_tables@[p].value()[i].is_empty()
    }

    pub open   spec fn rwx_upper_level_entries(&self) -> bool {
        &&& forall|i: L4Index|
            #![trigger self.l4_table@[self.cr3].value()[i].perm.write]
            #![trigger self.l4_table@[self.cr3].value()[i].perm.execute_disable]
            self.kernel_l4_end <= i < 512 && self.l4_table@[self.cr3].value()[i].perm.present
                ==> self.l4_table@[self.cr3].value()[i].perm.write
                && !self.l4_table@[self.cr3].value()[i].perm.execute_disable
        &&& forall|p: PageMapPtr, i: L3Index|
            #![trigger self.l3_tables@[p].value()[i].perm.write]
            #![trigger self.l3_tables@[p].value()[i].perm.execute_disable]
            self.l3_tables@.dom().contains(p) && 0 <= i < 512
                && self.l3_tables@[p].value()[i].perm.present
                && !self.l3_tables@[p].value()[i].perm.ps
                ==> self.l3_tables@[p].value()[i].perm.write
                && !self.l3_tables@[p].value()[i].perm.execute_disable
        &&& forall|p: PageMapPtr, i: L2Index|
            #![trigger  self.l2_tables@[p].value()[i].perm.write]
            #![trigger self.l2_tables@[p].value()[i].perm.execute_disable]
            self.l2_tables@.dom().contains(p) && 0 <= i < 512
                && self.l2_tables@[p].value()[i].perm.present
                && !self.l2_tables@[p].value()[i].perm.ps
                ==> self.l2_tables@[p].value()[i].perm.write
                && !self.l2_tables@[p].value()[i].perm.execute_disable
    }

    pub open   spec fn table_pages_wf(&self) -> bool {
        &&& page_ptr_valid(self.cr3)
        &&& forall|p: PageMapPtr|
            #![trigger self.l3_tables@.dom().contains(p), page_ptr_valid(p)]
            self.l3_tables@.dom().contains(p) ==> page_ptr_valid(p)
        &&& forall|p: PageMapPtr|
            #![trigger self.l2_tables@.dom().contains(p), page_ptr_valid(p)]
            self.l2_tables@.dom().contains(p) ==> page_ptr_valid(p)
        &&& forall|p: PageMapPtr|
            #![trigger self.l1_tables@.dom().contains(p), page_ptr_valid(p)]
            self.l1_tables@.dom().contains(p) ==> page_ptr_valid(p)
    }

    pub open   spec fn no_self_mapping(&self) -> bool {
        &&& forall|va: VAddr|
            #![trigger self.mapping_1g@.dom().contains(va), self.page_closure().contains(self.mapping_1g@[va].addr)]
            self.mapping_1g@.dom().contains(va) ==> self.page_closure().contains(
                self.mapping_1g@[va].addr,
            ) == false
        &&& forall|va: VAddr|
            #![trigger self.mapping_2m@.dom().contains(va), self.page_closure().contains(self.mapping_2m@[va].addr)]
            self.mapping_2m@.dom().contains(va) ==> self.page_closure().contains(
                self.mapping_2m@[va].addr,
            ) == false
        &&& forall|va: VAddr|
            #![trigger self.mapping_4k@.dom().contains(va), self.page_closure().contains(self.mapping_4k@[va].addr)]
            self.mapping_4k@.dom().contains(va) ==> self.page_closure().contains(
                self.mapping_4k@[va].addr,
            ) == false
    }

    // #[verifier(inline)]
    pub open   spec fn spec_resolve_mapping_l4(&self, l4i: L4Index) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i < 512,
    {
        if self.l4_table@[self.cr3].value()[l4i].perm.present || l4i < self.kernel_l4_end {
            Some(self.l4_table@[self.cr3].value()[l4i])
        } else {
            None
        }
    }

    pub open   spec fn spec_resolve_mapping_1g_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<
        PageEntry,
    >
        recommends
            self.kernel_l4_end <= l4i < 512,
            0 <= l3i < 512,
    {
        if self.spec_resolve_mapping_l4(l4i).is_None() {
            None
        } else if !self.l3_tables@[self.spec_resolve_mapping_l4(
            l4i,
        ).get_Some_0().addr].value()[l3i].perm.present
            || !self.l3_tables@[self.spec_resolve_mapping_l4(
            l4i,
        ).get_Some_0().addr].value()[l3i].perm.ps {
            None
        } else {
            Some(self.l3_tables@[self.spec_resolve_mapping_l4(l4i).get_Some_0().addr].value()[l3i])
        }
    }

    pub open   spec fn spec_resolve_mapping_l3(&self, l4i: L4Index, l3i: L3Index) -> Option<
        PageEntry,
    >
        recommends
            self.kernel_l4_end <= l4i < 512,
            0 <= l3i < 512,
    {
        if self.spec_resolve_mapping_l4(l4i).is_None() {
            None
        } else if !self.l3_tables@[self.spec_resolve_mapping_l4(
            l4i,
        ).get_Some_0().addr].value()[l3i].perm.present
            || self.l3_tables@[self.spec_resolve_mapping_l4(
            l4i,
        ).get_Some_0().addr].value()[l3i].perm.ps {
            None
        } else {
            Some(self.l3_tables@[self.spec_resolve_mapping_l4(l4i).get_Some_0().addr].value()[l3i])
        }
    }

    pub open   spec fn spec_resolve_mapping_2m_l2(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
    ) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i < 512,
            0 <= l3i < 512,
            0 <= l2i < 512,
    {
        if self.spec_resolve_mapping_l3(l4i, l3i).is_None() {
            None
        } else if !self.l2_tables@[self.spec_resolve_mapping_l3(
            l4i,
            l3i,
        ).get_Some_0().addr].value()[l2i].perm.present
            || !self.l2_tables@[self.spec_resolve_mapping_l3(
            l4i,
            l3i,
        ).get_Some_0().addr].value()[l2i].perm.ps {
            None
        } else {
            Some(
                self.l2_tables@[self.spec_resolve_mapping_l3(
                    l4i,
                    l3i,
                ).get_Some_0().addr].value()[l2i],
            )
        }
    }

    pub open   spec fn spec_resolve_mapping_l2(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
    ) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i < 512,
            0 <= l3i < 512,
            0 <= l2i < 512,
    {
        if self.spec_resolve_mapping_l3(l4i, l3i).is_None() {
            None
        } else if !self.l2_tables@[self.spec_resolve_mapping_l3(
            l4i,
            l3i,
        ).get_Some_0().addr].value()[l2i].perm.present
            || self.l2_tables@[self.spec_resolve_mapping_l3(
            l4i,
            l3i,
        ).get_Some_0().addr].value()[l2i].perm.ps {
            None
        } else {
            Some(
                self.l2_tables@[self.spec_resolve_mapping_l3(
                    l4i,
                    l3i,
                ).get_Some_0().addr].value()[l2i],
            )
        }
    }

    pub open   spec fn spec_resolve_mapping_4k_l1(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
        l1i: L1Index,
    ) -> Option<PageEntry>
        recommends
            self.kernel_l4_end <= l4i < 512,
            0 <= l3i < 512,
            0 <= l2i < 512,
            0 <= l1i < 512,
    {
        if self.spec_resolve_mapping_l2(l4i, l3i, l2i).is_None() {
            None
        } else if !self.l1_tables@[self.spec_resolve_mapping_l2(
            l4i,
            l3i,
            l2i,
        ).get_Some_0().addr].value()[l1i].perm.present {
            None
        } else {
            Some(
                self.l1_tables@[self.spec_resolve_mapping_l2(
                    l4i,
                    l3i,
                    l2i,
                ).get_Some_0().addr].value()[l1i],
            )
        }

    }

    pub open   spec fn wf_mapping_4k(&self) -> bool {
        &&& forall|va: VAddr|
            #![trigger va_4k_valid(va), self.mapping_4k@.dom().contains(va)]
            self.mapping_4k@.dom().contains(va) ==> va_4k_valid(va)
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
            #![trigger self.mapping_4k@[spec_index2va((l4i,l3i,l2i,l1i))]]
            #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
            self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512
                ==> self.mapping_4k@.dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i).is_Some()
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
            #![trigger self.mapping_4k@[spec_index2va((l4i,l3i,l2i,l1i))]]
            self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512
                && self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i).is_Some()
                ==> self.mapping_4k@[spec_index2va((l4i, l3i, l2i, l1i))].addr
                == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i).get_Some_0().addr
                && self.mapping_4k@[spec_index2va((l4i, l3i, l2i, l1i))].write
                == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i).get_Some_0().perm.write
                && self.mapping_4k@[spec_index2va((l4i, l3i, l2i, l1i))].execute_disable
                == self.spec_resolve_mapping_4k_l1(
                l4i,
                l3i,
                l2i,
                l1i,
            ).get_Some_0().perm.execute_disable
        &&& forall|va: VAddr|
            #![trigger self.mapping_4k@.dom().contains(va), page_ptr_valid(self.mapping_4k@[va].addr)]
            self.mapping_4k@.dom().contains(va) ==> page_ptr_valid(self.mapping_4k@[va].addr)
    }

    pub open   spec fn wf_mapping_2m(&self) -> bool {
        &&& forall|va: VAddr|
            #![trigger va_2m_valid(va), self.mapping_2m@.dom().contains(va)]
            self.mapping_2m@.dom().contains(va) ==> va_2m_valid(va)
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger self.mapping_2m@[spec_index2va((l4i,l3i,l2i,0))]]
            #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
            self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512
                ==> self.mapping_2m@.dom().contains(spec_index2va((l4i, l3i, l2i, 0)))
                == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i).is_Some()
        &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger self.mapping_2m@[spec_index2va((l4i,l3i,l2i,0))]]
            self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512
                && self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i).is_Some()
                ==> self.mapping_2m@[spec_index2va((l4i, l3i, l2i, 0))].addr
                == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i).get_Some_0().addr
                && self.mapping_2m@[spec_index2va((l4i, l3i, l2i, 0))].write
                == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i).get_Some_0().perm.write
                && self.mapping_2m@[spec_index2va((l4i, l3i, l2i, 0))].execute_disable
                == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i).get_Some_0().perm.execute_disable
        &&& forall|va: VAddr|
            #![trigger self.mapping_2m@.dom().contains(va), page_ptr_2m_valid(self.mapping_2m@[va].addr)]
            self.mapping_2m@.dom().contains(va) ==> page_ptr_2m_valid(self.mapping_2m@[va].addr)
    }

    pub open   spec fn wf_mapping_1g(&self) -> bool {
        &&& forall|va: VAddr|
            #![trigger va_1g_valid(va), self.mapping_1g@.dom().contains(va)]
            self.mapping_1g@.dom().contains(va) ==> va_1g_valid(va)
        &&& forall|l4i: L4Index, l3i: L3Index|
            #![trigger self.mapping_1g@[spec_index2va((l4i,l3i,0,0))]]
            #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
            self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 ==> self.mapping_1g@.dom().contains(
                spec_index2va((l4i, l3i, 0, 0)),
            ) == self.spec_resolve_mapping_1g_l3(l4i, l3i).is_Some()
        &&& forall|l4i: L4Index, l3i: L3Index|
            #![trigger self.mapping_1g@[spec_index2va((l4i,l3i,0,0))]]
            #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
            self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && self.spec_resolve_mapping_1g_l3(
                l4i,
                l3i,
            ).is_Some() ==> self.mapping_1g@[spec_index2va((l4i, l3i, 0, 0))].addr
                == self.spec_resolve_mapping_1g_l3(l4i, l3i).get_Some_0().addr
                && self.mapping_1g@[spec_index2va((l4i, l3i, 0, 0))].write
                == self.spec_resolve_mapping_1g_l3(l4i, l3i).get_Some_0().perm.write
                && self.mapping_1g@[spec_index2va((l4i, l3i, 0, 0))].execute_disable
                == self.spec_resolve_mapping_1g_l3(l4i, l3i).get_Some_0().perm.execute_disable
        &&& forall|va: VAddr|
            #![trigger self.mapping_1g@.dom().contains(va), page_ptr_1g_valid(self.mapping_1g@[va].addr)]
            self.mapping_1g@.dom().contains(va) ==> page_ptr_1g_valid(self.mapping_1g@[va].addr)
    }

    pub open   spec fn kernel_entries_wf(&self) -> bool {
        &&& self.kernel_l4_end < 512
        &&& self.kernel_entries@.len() =~= self.kernel_l4_end as nat
        &&& forall|i: usize|
            #![trigger self.kernel_entries@[i as int]]
            0 <= i < self.kernel_l4_end ==> self.kernel_entries@[i as int]
                == self.l4_table@[self.cr3].value()[i]
    }

    pub open   spec fn wf(&self) -> bool {
        &&& self.wf_l4()
        &&& self.wf_l3()
        &&& self.wf_l2()
        &&& self.wf_l1()
        &&& self.wf_mapping_4k()
        &&& self.wf_mapping_2m()
        &&& self.wf_mapping_1g()
        &&& self.user_only()
        &&& self.rwx_upper_level_entries()
        &&& self.present_or_zero()
        // &&&
        // self.no_self_mapping()
        &&& self.table_pages_wf()
        &&& self.kernel_entries_wf()
        &&& self.pcid_ioid_wf()
        &&& self.tlb_wf()
        &&& self.tlb_submap_of_mapping()
    }

    // pub open   spec fn l4_kernel_entries_reserved(&self) -> bool
    //     recommends self.wf_l4(),
    // {
    //     forall|l4i: L4Index| #![auto] 0<=l4i<KERNEL_MEM_END_L4INDEX ==> self.l4_table@[self.cr3]@.value.get_Some_0()[l4i].is_None()
    // }
    pub open   spec fn l4_entry_exists(&self, l4i: L4Index) -> bool
        recommends
            self.wf(),
    {
        self.spec_resolve_mapping_l4(l4i).is_Some()
    }

    pub open   spec fn l3_2m_entry_exists(&self, l4i: L4Index, l3i: L3Index) -> bool
        recommends
            self.wf(),
            self.l4_entry_exists(l4i),
    {
        self.spec_resolve_mapping_l3(l4i, l3i).is_Some()
    }

    pub open   spec fn l3_4k_entry_exists(&self, l4i: L4Index, l3i: L3Index) -> bool
        recommends
            self.wf(),
            self.l4_entry_exists(l4i),
    {
        self.spec_resolve_mapping_l3(l4i, l3i).is_Some()
    }

    pub open   spec fn l2_4k_entry_exists(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> bool
        recommends
            self.wf(),
            self.l3_4k_entry_exists(l4i, l3i),
    {
        self.spec_resolve_mapping_l2(l4i, l3i, l2i).is_Some()
    }
}

// proof
impl PageTable {
    pub proof fn no_mapping_infer_not_mapped(&self, page_map_ptr: PageMapPtr)
        requires
            self.wf(),
            forall|va: VAddr|
                #![trigger self.mapping_4k().dom().contains(va)]
                #![trigger self.mapping_4k()[va]]
                self.mapping_4k().dom().contains(va) ==> self.mapping_4k()[va].addr != page_map_ptr,
            forall|va: VAddr|
                #![auto]
                self.mapping_2m().dom().contains(va) ==> self.mapping_2m()[va].addr != page_map_ptr,
            forall|va: VAddr|
                #![auto]
                self.mapping_1g().dom().contains(va) ==> self.mapping_1g()[va].addr != page_map_ptr,
        ensures
            self.page_not_mapped(page_map_ptr),
    {
    }

    pub proof fn no_mapping_infer_no_reslove(&self)
        requires
            self.wf(),
        ensures
            self.mapping_2m().dom() =~= Set::empty() ==> forall|
                l4i: L4Index,
                l3i: L3Index,
                l2i: L2Index,
            |
                #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512
                    ==> self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i).is_Some() == false,
            self.mapping_1g().dom() =~= Set::empty() ==> forall|l4i: L4Index, l3i: L3Index|
                #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512
                    ==> self.spec_resolve_mapping_1g_l3(l4i, l3i).is_Some() == false,
    {
    }

    pub proof fn ps_entries_exist_in_mapped_pages(&self)
        requires
            self.wf(),
        ensures
            forall|p: PageMapPtr, i: L3Index|
                #![trigger self.mapped_1g_pages().contains(self.l3_tables@[p].value()[i].addr)]
                self.l3_tables@.dom().contains(p) && 0 <= i < 512
                    && self.l3_tables@[p].value()[i].perm.present
                    && self.l3_tables@[p].value()[i].perm.ps ==> self.mapped_1g_pages().contains(
                    self.l3_tables@[p].value()[i].addr,
                ),
            forall|p: PageMapPtr, i: L2Index|
                #![trigger self.mapped_2m_pages().contains(self.l2_tables@[p].value()[i].addr)]
                self.l2_tables@.dom().contains(p) && 0 <= i < 512
                    && self.l2_tables@[p].value()[i].perm.present
                    && self.l2_tables@[p].value()[i].perm.ps ==> self.mapped_2m_pages().contains(
                    self.l2_tables@[p].value()[i].addr,
                ),
            forall|p: PageMapPtr, i: L2Index|
                #![trigger self.mapped_4k_pages().contains(self.l1_tables@[p].value()[i].addr)]
                self.l1_tables@.dom().contains(p) && 0 <= i < 512
                    && self.l1_tables@[p].value()[i].perm.present
                    ==> self.mapped_4k_pages().contains(self.l1_tables@[p].value()[i].addr),
    {
        assert(forall|p: PageMapPtr, i: L3Index|
        // #![auto]

            #![trigger self.l3_tables@[p].value()[i]]
            self.l3_tables@.dom().contains(p) && 0 <= i < 512
                && self.l3_tables@[p].value()[i].perm.present
                && self.l3_tables@[p].value()[i].perm.ps ==> self.mapped_1g_pages().contains(
                self.l3_tables@[p].value()[i].addr,
            )) by {
            assert(forall|p: PageMapPtr, i: L3Index|
            // #![auto]

                #![trigger self.l3_tables@[p].value()[i]]
                self.l3_tables@.dom().contains(p) && 0 <= i < 512
                    && self.l3_tables@[p].value()[i].perm.present
                    && self.l3_tables@[p].value()[i].perm.ps ==> self.kernel_l4_end
                    <= self.l3_rev_map@[p] < 512 && self.l3_rev_map@.dom().contains(p)
                    && self.spec_resolve_mapping_l4(self.l3_rev_map@[p]).is_Some()
                    && self.spec_resolve_mapping_l4(self.l3_rev_map@[p]).get_Some_0().addr == p
                    && self.spec_resolve_mapping_1g_l3(self.l3_rev_map@[p], i).is_Some()
                    && self.spec_resolve_mapping_1g_l3(self.l3_rev_map@[p], i).get_Some_0().addr
                    == self.l3_tables@[p].value()[i].addr && self.mapping_1g@.dom().contains(
                    spec_index2va((self.l3_rev_map@[p], i, 0, 0)),
                ) && self.mapping_1g@[spec_index2va((self.l3_rev_map@[p], i, 0, 0))].addr
                    == self.l3_tables@[p].value()[i].addr && self.mapping_1g().dom().contains(
                    spec_index2va((self.l3_rev_map@[p], i, 0, 0)),
                ) && self.mapping_1g()[spec_index2va((self.l3_rev_map@[p], i, 0, 0))].addr
                    == self.l3_tables@[p].value()[i].addr && self.mapped_1g_pages().contains(
                    self.l3_tables@[p].value()[i].addr,
                ));
        };

        assert(forall|p: PageMapPtr, i: L2Index|
            #![trigger self.l2_tables@[p].value()[i]]
            self.l2_tables@.dom().contains(p) && 0 <= i < 512
                && self.l2_tables@[p].value()[i].perm.present
                && self.l2_tables@[p].value()[i].perm.ps ==> self.mapped_2m_pages().contains(
                self.l2_tables@[p].value()[i].addr,
            )) by {
            assert(forall|p: PageMapPtr, i: L2Index|
                #![trigger self.l2_tables@[p].value()[i]]
                self.l2_tables@.dom().contains(p) && 0 <= i < 512
                    && self.l2_tables@[p].value()[i].perm.present
                    && self.l2_tables@[p].value()[i].perm.ps ==> self.l2_rev_map@.dom().contains(p)
                    && self.kernel_l4_end <= self.l2_rev_map@[p].0 < 512 && 0
                    <= self.l2_rev_map@[p].1 < 512 && self.spec_resolve_mapping_l3(
                    self.l2_rev_map@[p].0,
                    self.l2_rev_map@[p].1,
                ).is_Some() && self.spec_resolve_mapping_l3(
                    self.l2_rev_map@[p].0,
                    self.l2_rev_map@[p].1,
                ).get_Some_0().addr == p && self.spec_resolve_mapping_l3(
                    self.l2_rev_map@[p].0,
                    self.l2_rev_map@[p].1,
                ).is_Some() && self.spec_resolve_mapping_l3(
                    self.l2_rev_map@[p].0,
                    self.l2_rev_map@[p].1,
                ).get_Some_0().addr == p && self.spec_resolve_mapping_2m_l2(
                    self.l2_rev_map@[p].0,
                    self.l2_rev_map@[p].1,
                    i,
                ).is_Some() && self.spec_resolve_mapping_2m_l2(
                    self.l2_rev_map@[p].0,
                    self.l2_rev_map@[p].1,
                    i,
                ).get_Some_0().addr == self.l2_tables@[p].value()[i].addr
                    && self.mapping_2m@.dom().contains(
                    spec_index2va((self.l2_rev_map@[p].0, self.l2_rev_map@[p].1, i, 0)),
                ) && self.mapping_2m@[spec_index2va(
                    (self.l2_rev_map@[p].0, self.l2_rev_map@[p].1, i, 0),
                )].addr == self.l2_tables@[p].value()[i].addr && self.mapping_2m().dom().contains(
                    spec_index2va((self.l2_rev_map@[p].0, self.l2_rev_map@[p].1, i, 0)),
                ));
        };
        assert(forall|p: PageMapPtr, i: L1Index|
            #![trigger self.l1_tables@[p].value()[i]]
            self.l1_tables@.dom().contains(p) && 0 <= i < 512
                && self.l1_tables@[p].value()[i].perm.present ==> self.mapped_4k_pages().contains(
                self.l1_tables@[p].value()[i].addr,
            )) by {
            assert(forall|p: PageMapPtr, i: L1Index|
                #![trigger self.l1_tables@[p].value()[i]]
                self.l1_tables@.dom().contains(p) && 0 <= i < 512
                    && self.l1_tables@[p].value()[i].perm.present
                    ==> self.l1_rev_map@.dom().contains(p) && self.kernel_l4_end
                    <= self.l1_rev_map@[p].0 < 512 && 0 <= self.l1_rev_map@[p].1 < 512 && 0
                    <= self.l1_rev_map@[p].2 < 512 && self.spec_resolve_mapping_l2(
                    self.l1_rev_map@[p].0,
                    self.l1_rev_map@[p].1,
                    self.l1_rev_map@[p].2,
                ).is_Some() && self.spec_resolve_mapping_l2(
                    self.l1_rev_map@[p].0,
                    self.l1_rev_map@[p].1,
                    self.l1_rev_map@[p].2,
                ).get_Some_0().addr == p && self.spec_resolve_mapping_l2(
                    self.l1_rev_map@[p].0,
                    self.l1_rev_map@[p].1,
                    self.l1_rev_map@[p].2,
                ).is_Some() && self.spec_resolve_mapping_l2(
                    self.l1_rev_map@[p].0,
                    self.l1_rev_map@[p].1,
                    self.l1_rev_map@[p].2,
                ).get_Some_0().addr == p && self.spec_resolve_mapping_4k_l1(
                    self.l1_rev_map@[p].0,
                    self.l1_rev_map@[p].1,
                    self.l1_rev_map@[p].2,
                    i,
                ).is_Some() && self.spec_resolve_mapping_4k_l1(
                    self.l1_rev_map@[p].0,
                    self.l1_rev_map@[p].1,
                    self.l1_rev_map@[p].2,
                    i,
                ).get_Some_0().addr == self.l1_tables@[p].value()[i].addr
                    && self.mapping_4k@.dom().contains(
                    spec_index2va(
                        (self.l1_rev_map@[p].0, self.l1_rev_map@[p].1, self.l1_rev_map@[p].2, i),
                    ),
                ) && self.mapping_4k@[spec_index2va(
                    (self.l1_rev_map@[p].0, self.l1_rev_map@[p].1, self.l1_rev_map@[p].2, i),
                )].addr == self.l1_tables@[p].value()[i].addr && self.mapping_4k().dom().contains(
                    spec_index2va(
                        (self.l1_rev_map@[p].0, self.l1_rev_map@[p].1, self.l1_rev_map@[p].2, i),
                    ),
                )
            // &&
            // self.mapping_2m()[spec_index2va((l4i,l3i,l2i,i))].addr == self.l2_tables@[p].value()[i].addr
            // &&
            // self.mapped_2m_pages().contains(self.l2_tables@[p].value()[i].addr)
            );
        };
    }

    pub proof fn internal_resolve_disjoint(&self)
        requires
            self.wf(),
        ensures
            forall|l4i: L4Index, l4j: L4Index|
                #![trigger self.spec_resolve_mapping_l4(l4i), self.spec_resolve_mapping_l4(l4j)]
                self.kernel_l4_end <= l4i < 512 && self.kernel_l4_end <= l4j < 512 && l4i != l4j
                    && self.spec_resolve_mapping_l4(l4i).is_Some() && self.spec_resolve_mapping_l4(
                    l4j,
                ).is_Some() ==> self.spec_resolve_mapping_l4(l4i).get_Some_0().addr
                    != self.spec_resolve_mapping_l4(l4j).get_Some_0().addr,
            forall|l4i: L4Index, l3i: L3Index, l4j: L4Index, l3j: L3Index|
                #![trigger self.spec_resolve_mapping_l3(l4i,l3i), self.spec_resolve_mapping_l3(l4j,l3j)]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && self.kernel_l4_end <= l4j < 512
                    && 0 <= l3j < 512 && (l4i, l3i) != (l4j, l3j) && self.spec_resolve_mapping_l3(
                    l4i,
                    l3i,
                ).is_Some() && self.spec_resolve_mapping_l3(l4j, l3j).is_Some()
                    ==> self.spec_resolve_mapping_l3(l4i, l3i).get_Some_0().addr
                    != self.spec_resolve_mapping_l3(l4j, l3j).get_Some_0().addr,
            forall|
                l4i: L4Index,
                l3i: L3Index,
                l2i: L3Index,
                l4j: L4Index,
                l3j: L3Index,
                l2j: L2Index,
            |
                #![trigger self.spec_resolve_mapping_l2(l4i,l3i,l2i), self.spec_resolve_mapping_l2(l4j,l3j,l2j)]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512
                    && self.kernel_l4_end <= l4j < 512 && 0 <= l3j < 512 && 0 <= l2j < 512 && (
                    l4i,
                    l3i,
                    l2i,
                ) != (l4j, l3j, l2j) && self.spec_resolve_mapping_l2(l4i, l3i, l2i).is_Some()
                    && self.spec_resolve_mapping_l2(l4j, l3j, l2j).is_Some()
                    ==> self.spec_resolve_mapping_l2(l4i, l3i, l2i).get_Some_0().addr
                    != self.spec_resolve_mapping_l2(l4j, l3j, l2j).get_Some_0().addr,
    {
        assert(forall|l4i: L4Index, l4j: L4Index|
            #![trigger self.spec_resolve_mapping_l4(l4i), self.spec_resolve_mapping_l4(l4j)]
            self.kernel_l4_end <= l4i < 512 && self.kernel_l4_end <= l4j < 512 && l4i != l4j
                && self.spec_resolve_mapping_l4(l4i).is_Some() && self.spec_resolve_mapping_l4(
                l4j,
            ).is_Some() ==> self.spec_resolve_mapping_l4(l4i).get_Some_0().addr
                != self.spec_resolve_mapping_l4(l4j).get_Some_0().addr);

        assert(forall|l3pi: PageMapPtr, l3i: L3Index, l3pj: PageMapPtr, l3j: L3Index|
            #![auto]
            self.l3_tables@.dom().contains(l3pi) && 0 <= l3i < 512
                && self.l3_tables@.dom().contains(l3pj) && 0 <= l3j < 512 && (l3pi, l3i) != (
                l3pj,
                l3j,
            ) && self.l3_tables@[l3pi].value()[l3i].perm.present
                && !self.l3_tables@[l3pi].value()[l3i].perm.ps
                && self.l3_tables@[l3pj].value()[l3j].perm.present
                && !self.l3_tables@[l3pj].value()[l3j].perm.ps
                ==> self.l3_tables@[l3pi].value()[l3i].addr
                != self.l3_tables@[l3pj].value()[l3j].addr);

        assert(forall|l4i: L4Index, l3i: L3Index, l4j: L4Index, l3j: L3Index|
            #![auto]
            self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && self.kernel_l4_end <= l4j < 512
                && 0 <= l3j < 512 && (l4i, l3i) != (l4j, l3j) && self.spec_resolve_mapping_l3(
                l4i,
                l3i,
            ).is_Some() && self.spec_resolve_mapping_l3(l4j, l3j).is_Some()
                ==> self.spec_resolve_mapping_l3(l4i, l3i).get_Some_0().addr
                != self.spec_resolve_mapping_l3(l4j, l3j).get_Some_0().addr);
        assert(forall|l2pi: PageMapPtr, l2i: L2Index, l2pj: PageMapPtr, l2j: L2Index|
            #![auto]
            self.l2_tables@.dom().contains(l2pi) && 0 <= l2i < 512
                && self.l2_tables@.dom().contains(l2pj) && 0 <= l2j < 512 && (l2pi, l2i) != (
                l2pj,
                l2j,
            ) && self.l2_tables@[l2pi].value()[l2i].perm.present
                && !self.l2_tables@[l2pi].value()[l2i].perm.ps
                && self.l2_tables@[l2pj].value()[l2j].perm.present
                && !self.l2_tables@[l2pj].value()[l2j].perm.ps
                ==> self.l2_tables@[l2pi].value()[l2i].addr
                != self.l2_tables@[l2pj].value()[l2j].addr);

        assert(forall|
            l4i: L4Index,
            l3i: L3Index,
            l2i: L3Index,
            l4j: L4Index,
            l3j: L3Index,
            l2j: L2Index,
        |
            #![auto]
            self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512
                && self.kernel_l4_end <= l4j < 512 && 0 <= l3j < 512 && 0 <= l2j < 512 && (
                l4i,
                l3i,
                l2i,
            ) != (l4j, l3j, l2j) && self.spec_resolve_mapping_l2(l4i, l3i, l2i).is_Some()
                && self.spec_resolve_mapping_l2(l4j, l3j, l2j).is_Some()
                ==> self.spec_resolve_mapping_l2(l4i, l3i, l2i).get_Some_0().addr
                != self.spec_resolve_mapping_l2(l4j, l3j, l2j).get_Some_0().addr);

    }
}

} // verus!
