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
// use crate::page_alloc::*;

use crate::kernel::*;


impl Kernel {

pub closed spec fn syscall_register_pci_dev_spec(old:Kernel,new:Kernel,cpu_id:CPUID, bus:u8, dev:u8, fun:u8) -> bool
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        //checking arguments
        let valid_thread = (cpu_id < NUM_CPUS &&
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let pci_dev_valid = dev < 32 && fun < 8;
        let proc_has_iommu = old.proc_man.get_proc(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).ioid.is_Some();
        let proc_owns_pci_dev = old.mmu_man.pci_bitmap@[(old.proc_man.get_proc(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).ioid.get_Some_0(), bus,dev,fun)] == true;
        let pci_dev_free = old.mmu_man.root_table.resolve(bus,dev,fun).is_None();

        if valid_thread && pci_dev_valid && proc_has_iommu && proc_owns_pci_dev && pci_dev_free
        {
            (
                new.cpu_list =~= old.cpu_list
                &&
                new.proc_man =~= old.proc_man
                &&
                new.page_alloc =~= old.page_alloc
                &&
                new.mmu_man =~= old.mmu_man
                &&
                forall|_bus:u8,_dev:u8,_fun:u8|#![auto] 0<=_bus<256 && 0<=_dev<32 && 0<=_fun<8 &&
                (_bus != bus || _dev != dev || _fun != fun)
                    ==> new.mmu_man.root_table.resolve(_bus,_dev,_fun) =~= old.mmu_man.root_table.resolve(_bus,_dev,_fun)
                &&
                forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                &&
                forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                &&
                new.mmu_man.root_table.resolve(bus,dev,fun).is_Some() && new.mmu_man.root_table.resolve(bus,dev,fun).get_Some_0().0 ==
                    old.proc_man.get_proc(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).ioid.get_Some_0()
            )
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old =~= new
        }
    }
}

    pub fn syscall_register_pci_dev(&mut self, cpu_id:CPUID, pt_regs: PtRegs, bus:u8, dev:u8, fun:u8) -> (ret:SyscallReturnStruct)
        requires
            old(self).wf(),
        ensures
            self.wf(),
    {
        let (default_pcid, default_cr3) = self.mmu_man.get_reserved_pcid_and_cr3();
        if cpu_id >= NUM_CPUS{
            return SyscallReturnStruct::new(CPU_ID_INVALID,default_pcid,default_cr3,pt_regs);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return SyscallReturnStruct::new(NO_RUNNING_THREAD,default_pcid,default_cr3,pt_regs);
        }

        assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
        let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
        assert(current_thread_ptr_op.is_Some());
        let current_thread_ptr = current_thread_ptr_op.unwrap();
        let current_proc_ptr = self.proc_man.get_parent_proc_ptr_by_thread_ptr(current_thread_ptr);

        let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
        let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);

        if dev >= 32 || fun >= 8 {
            return SyscallReturnStruct::new(PCI_DEV_NUM_INVALID,pcid,cr3,pt_regs);
        }
        let ioid_op = self.proc_man.get_ioid_by_thread_ptr(current_thread_ptr);
        if ioid_op.is_none(){
            return SyscallReturnStruct::new(PROC_NO_IOMMUTABLE,pcid,cr3,pt_regs);
        }

        let ioid = ioid_op.unwrap();
        if self.mmu_man.mmu_get_pci_dev_by_ioid(ioid,bus,dev,fun) == false
        {
            return SyscallReturnStruct::new(PCI_DEV_NO_OWNERSHIP,pcid,cr3,pt_regs);
        }

        if self.mmu_man.get_pci_binding(bus,dev,fun).is_some()
        {
            return SyscallReturnStruct::new(PCI_DEV_TAKEN,pcid,cr3,pt_regs);
        }

        self.mmu_man.mmu_register_pci_dev(ioid,bus,dev,fun);
        return SyscallReturnStruct::new(SUCCESS,pcid,cr3,pt_regs);
    }

}
}
