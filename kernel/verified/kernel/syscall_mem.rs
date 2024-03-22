use vstd::prelude::*;
verus! {

// use crate::array_vec::*;
// use crate::proc::*;
// use crate::page_alloc::*;
// use crate::cpu::*;
// use crate::mars_array::MarsArray;
use crate::pagetable::*;
use crate::cpu::*;
use crate::define::*;
use crate::trap::*;
use crate::page_alloc::*;

use crate::kernel::*;

pub closed spec fn syscall_malloc_spec(old:Kernel, new:Kernel, cpu_id:CPUID, va: usize, perm_bits:usize, range: usize) -> bool
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        let valid_thread = (cpu_id < NUM_CPUS && 
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let perm_bits_valid = spec_va_perm_bits_valid(perm_bits);
        let system_has_memory = old.page_alloc.free_pages.len() >= 4 * range;
        let range_valid = range != 0 && range < (usize::MAX/4);
        let pcid = old.proc_man.get_proc(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).pcid;
        let va_valid =  (forall|j:usize| #![auto] 0<=j<range ==> spec_va_valid(spec_va_add_range(va,j)));
        let va_mapping_valid = (forall|j:usize| #![auto] 0<=j<range ==> old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_None());

        if valid_thread && perm_bits_valid && system_has_memory && range_valid && va_valid && va_mapping_valid
        {
            (new.proc_man =~= old.proc_man
            &&
            new.cpu_list =~= old.cpu_list
            &&
            new.mmu_man.free_pcids =~= old.mmu_man.free_pcids
            &&
            new.mmu_man.free_ioids =~= old.mmu_man.free_ioids
            &&
            (forall|_pcid:Pcid| #![auto] 0<=_pcid<PCID_MAX && new.mmu_man.get_free_pcids_as_set().contains(_pcid) == false && _pcid != pcid ==> 
                new.mmu_man.get_pagetable_mapping_by_pcid(_pcid) =~= old.mmu_man.get_pagetable_mapping_by_pcid(_pcid))
            &&
            (forall|ioid:IOid| #![auto] 0<=ioid<IOID_MAX && new.mmu_man.get_free_ioids_as_set().contains(ioid) == false ==> 
                new.mmu_man.get_iommutable_mapping_by_ioid(ioid) =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid))
            &&
            (forall|j:usize| #![auto] 0<=j<range ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_Some())
            &&
            (forall|_va:VAddr| #![auto] spec_va_valid(_va) && 
            (
                forall|j:usize| #![auto] 0<=j<range ==> spec_va_add_range(va,j) != _va
            )
            ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[_va] == old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[_va])
            )
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

impl Kernel {

    
    pub fn syscall_malloc(&mut self, cpu_id:CPUID, va: usize, perm_bits:usize, range: usize) -> (ret:(SyscallReturnStruct,Option<ProcPtr>,Option<ThreadPtr>))
        requires
            old(self).wf(),
        ensures
            self.wf(),
            syscall_malloc_spec(*old(self), *self, cpu_id, va, perm_bits, range),
    {
        if cpu_id >= NUM_CPUS{
            return (SyscallReturnStruct::new(CPU_ID_INVALID,0,0),None,None);
        }else if self.cpu_list.get(cpu_id).get_is_idle() {
            return (SyscallReturnStruct::new(NO_RUNNING_THREAD,0,0),None,None);
        }else{
            assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
            let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
            assert(current_thread_ptr_op.is_Some());
            let current_thread_ptr = current_thread_ptr_op.unwrap();
            let current_proc_ptr = self.proc_man.get_parent_proc_ptr_by_thread_ptr(current_thread_ptr);
    
            let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
            let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);
    
            assert(self.mmu_man.get_free_pcids_as_set().contains(pcid) == false);
    
            if va_perm_bits_valid(perm_bits) == false{
                return (SyscallReturnStruct::new(VMEM_PERMBITS_INVALID,0,0),None,None);
            }else if range == 0 || range >= (usize::MAX/4) {
                return (SyscallReturnStruct::new(MMAP_VADDR_INVALID,0,0),None,None);
            }else if  self.page_alloc.free_pages.len() < 4 * range {
                return (SyscallReturnStruct::new(SYSTEM_OUT_OF_MEM,0,0),None,None);
            }else{
                let mut i = 0;
                while i != range
                    invariant
                        0<=i<=range,
                        self == old(self),
                        self.wf(),
                        cpu_id < NUM_CPUS,
                        self.cpu_list@[cpu_id as int].get_is_idle() == false,
                        self.mmu_man.get_free_pcids_as_set().contains(pcid) == false,
                        self.page_alloc.free_pages.len() >= 4*range,
                        spec_va_perm_bits_valid(perm_bits),
                        0<=pcid<PCID_MAX,
                        pcid == old(self).proc_man.get_proc(old(self).proc_man.get_thread(old(self).cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).pcid,
                        (forall|j:usize| #![auto] 0<=j<i ==> spec_va_valid(spec_va_add_range(va,j))),
                        (forall|j:usize| #![auto] 0<=j<i  ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_None()),
                    ensures
                        self == old(self),
                        self.wf(),
                        i==range,
                        self == old(self),
                        self.wf(),
                        cpu_id < NUM_CPUS,
                        self.cpu_list@[cpu_id as int].get_is_idle() == false,
                        self.mmu_man.get_free_pcids_as_set().contains(pcid) == false,
                        self.page_alloc.free_pages.len() >= 4*range,
                        spec_va_perm_bits_valid(perm_bits),
                        0<=pcid<PCID_MAX,
                        pcid == old(self).proc_man.get_proc(old(self).proc_man.get_thread(old(self).cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).pcid,
                        (forall|j:usize| #![auto] 0<=j<i ==> spec_va_valid(spec_va_add_range(va,j))),
                        (forall|j:usize| #![auto] 0<=j<i  ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_None()),
                {
                    if va_valid(va_add_range(va,i)) == false {
                        proof{
                            let valid_thread = (cpu_id < NUM_CPUS && 
                                old(self).cpu_list@[cpu_id as int].get_is_idle() == false);
                            let perm_bits_valid = spec_va_perm_bits_valid(perm_bits);
                            let system_has_memory = old(self).page_alloc.free_pages.len() >= 4 * range;
                            let range_valid = range != 0 || range >= (usize::MAX/4);
                            let pcid = old(self).proc_man.get_proc(old(self).proc_man.get_thread(old(self).cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).pcid;
                            let va_valid =  (forall|j:usize| #![auto] 0<=j<range ==> spec_va_valid(spec_va_add_range(va,j)));

                            assert(va_valid == false);
                            assert(self == old(self));
                        }
                        assert(syscall_malloc_spec(*old(self), *self, cpu_id, va, perm_bits, range));
                        return (SyscallReturnStruct::new(MMAP_VADDR_INVALID,0,0),None,None);
                    }
                    if self.mmu_man.mmu_get_va_entry_by_pcid(pcid,va_add_range(va,i)).is_some(){
                        assert(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,i)].is_Some());
                        proof{
                            let valid_thread = (cpu_id < NUM_CPUS && 
                                old(self).cpu_list@[cpu_id as int].get_is_idle() == false);
                            let perm_bits_valid = spec_va_perm_bits_valid(perm_bits);
                            let system_has_memory = old(self).page_alloc.free_pages.len() >= 4 * range;
                            let range_valid = range != 0 || range >= (usize::MAX/4);
                            let pcid = old(self).proc_man.get_proc(old(self).proc_man.get_thread(old(self).cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).pcid;
                            let va_valid =  (forall|j:usize| #![auto] 0<=j<range ==> spec_va_valid(spec_va_add_range(va,j)));
                            let va_mapping_valid = (forall|j:usize| #![auto] 0<=j<range ==> old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_None());

                            assert(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,i)].is_Some());
                            assert(old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,i)].is_Some());

                            assert(va_mapping_valid == false);
                            assert(self == old(self));
                        }
                        return (SyscallReturnStruct::new(MMAP_VADDR_NOT_FREE,0,0),None,None);
                    }
                    i = i + 1;
                }
        
                self.kernel_create_and_map_range_new_pages(pcid,va,perm_bits,range);
                assert(forall|j:usize| #![auto] 0<=j<range ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_Some());
                assert(self.wf());
                return (SyscallReturnStruct::new(SUCCESS,0,0),None,None);
            }
        }
       
    }

    pub fn syscall_map_pagetable_pages_to_iommutable(&mut self, cpu_id:CPUID, va:VAddr, perm_bits:usize, range:usize) -> (ret:(SyscallReturnStruct,Option<ProcPtr>,Option<ThreadPtr>))

        requires
            old(self).wf(),
        ensures
            self.wf(),
    {
        if cpu_id >= NUM_CPUS{
            return (SyscallReturnStruct::new(CPU_ID_INVALID,0,0),None,None);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return (SyscallReturnStruct::new(NO_RUNNING_THREAD,0,0),None,None);
        }
        assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
        let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
        assert(current_thread_ptr_op.is_Some());
        let current_thread_ptr = current_thread_ptr_op.unwrap();
        let current_proc_ptr = self.proc_man.get_parent_proc_ptr_by_thread_ptr(current_thread_ptr);

        let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
        let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);
        let ioid_op = self.proc_man.get_ioid_by_thread_ptr(current_thread_ptr);

        assert(self.mmu_man.get_free_pcids_as_set().contains(pcid) == false);

        if va_perm_bits_valid(perm_bits) == false{
            return (SyscallReturnStruct::new(VMEM_PERMBITS_INVALID,0,0),None,None);
        }

        if ioid_op.is_none() {
            return (SyscallReturnStruct::new(PROC_NO_IOMMUTABLE,0,0),None,None);
        }

        let ioid = ioid_op.unwrap();

        if range == 0 || range >= (usize::MAX/3) {
            return (SyscallReturnStruct::new(MMAP_VADDR_INVALID,0,0),None,None);
        }

        if  self.page_alloc.free_pages.len() < 3 * range {
            return (SyscallReturnStruct::new(SYSTEM_OUT_OF_MEM,0,0),None,None);
        }

        let mut i = 0;
        while i != range
            invariant
                0<=i<=range,
                self == old(self),
                self.wf(),
                0<=pcid<PCID_MAX,
                0<=ioid<IOID_MAX,
                spec_va_perm_bits_valid(perm_bits),
                self.page_alloc.free_pages.len() >= 3 * range,
                self.mmu_man.get_free_pcids_as_set().contains(pcid) == false,
                self.mmu_man.get_free_ioids_as_set().contains(ioid) == false,
                forall|j:usize| #![auto] 0<=j<i ==> spec_va_valid(spec_va_add_range(va,j)),
                forall|j:usize| #![auto] 0<=j<i ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_Some(),
                forall|j:usize| #![auto] 0<=j<i ==>  self.page_alloc.page_array@[
                    page_ptr2page_index(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].get_Some_0().addr) as int].rf_count < usize::MAX - range,
                forall|j:usize| #![auto] 0<=j<i ==> old(self).mmu_man.get_iommutable_mapping_by_ioid(ioid)[spec_va_add_range(va,j)].is_None(),
            ensures
                i==range,
                self == old(self),
                self.wf(),
                0<=pcid<PCID_MAX,
                0<=ioid<IOID_MAX,
                spec_va_perm_bits_valid(perm_bits),
                self.page_alloc.free_pages.len() >= 3 * range,
                self.mmu_man.get_free_pcids_as_set().contains(pcid) == false,
                self.mmu_man.get_free_ioids_as_set().contains(ioid) == false,
                forall|j:usize| #![auto] 0<=j<i ==> spec_va_valid(spec_va_add_range(va,j)),
                forall|j:usize| #![auto] 0<=j<i ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_Some(),
                forall|j:usize| #![auto] 0<=j<i ==>  self.page_alloc.page_array@[
                    page_ptr2page_index(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].get_Some_0().addr) as int].rf_count < usize::MAX - range,
                forall|j:usize| #![auto] 0<=j<i ==> old(self).mmu_man.get_iommutable_mapping_by_ioid(ioid)[spec_va_add_range(va,j)].is_None(),
        {
            if va_valid(va_add_range(va,i)) == false {
                return (SyscallReturnStruct::new(MMAP_VADDR_INVALID,0,0),None,None);
            }

            if self.mmu_man.mmu_get_va_entry_by_ioid(ioid,va_add_range(va,i)).is_some()
            {
                return (SyscallReturnStruct::new(MMAP_VADDR_NOT_FREE,0,0),None,None);
            }

            let page_entry = self.mmu_man.mmu_get_va_entry_by_pcid(pcid,va_add_range(va,i));

            if page_entry.is_none(){
                return (SyscallReturnStruct::new(MMAP_VADDR_NOT_FREE,0,0),None,None);
            }

            if self.page_alloc.get_page_rf_counter_by_page_ptr(page_entry.unwrap().addr) >= usize::MAX - range {
                return (SyscallReturnStruct::new(PAGE_RF_COUNTER_OVERFLOW,0,0),None,None);
            }
            i = i + 1;
        }

        self.kernel_map_pagetable_range_page_to_iommutable(pcid,ioid,va,perm_bits,range);
        assert(self.wf());

        return (SyscallReturnStruct::new(SUCCESS,0,0),None,None);
    }
    pub fn syscall_resolve_va(&self, cpu_id:CPUID, pt_regs: Registers, va: usize) -> (ret:(SyscallReturnStruct,PAddr))
        requires
            self.wf(),
    {
        if cpu_id >= NUM_CPUS{
            return (SyscallReturnStruct::new(CPU_ID_INVALID,0,0),0);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return (SyscallReturnStruct::new(NO_RUNNING_THREAD,0,0),0);
        }


        assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
        let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
        assert(current_thread_ptr_op.is_Some());
        let current_thread_ptr = current_thread_ptr_op.unwrap();
        let current_proc_ptr = self.proc_man.get_parent_proc_ptr_by_thread_ptr(current_thread_ptr);

        let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
        let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);

        if va_valid(va) == false{
            return (SyscallReturnStruct::new(VADDR_INVALID,pcid, cr3),0);
        }

        let page_entry = self.mmu_man.mmu_get_va_entry_by_pcid(pcid, va);

        if page_entry.is_none() {
            return (SyscallReturnStruct::new(VADDR_NOMAPPING,pcid, cr3),0);
        }else{
            return (SyscallReturnStruct::new(SUCCESS,pcid, cr3),page_entry.unwrap().addr | page_entry.unwrap().perm);
        }
    }
}
}
