use vstd::prelude::*;
verus! {

// use crate::array_vec::*;
// use crate::proc::*;
// use crate::page_alloc::*;
// use crate::cpu::*;
// use crate::mars_array::MarsArray;
use crate::proc::*;
use crate::pagetable::*;
use crate::cpu::*;
use crate::define::*;
use crate::trap::*;
// use crate::page_alloc::*;

use crate::kernel::*;

pub closed spec fn syscall_reply_message_spec(old:Kernel, new:Kernel, cpu_id:CPUID, message_va: VAddr, length:usize) -> bool
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        let valid_thread = (cpu_id < NUM_CPUS && 
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let has_caller = old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).caller.is_Some();
        let system_scheduler_has_space = old.proc_man.scheduler.len() != MAX_NUM_THREADS;

        if valid_thread && has_caller && system_scheduler_has_space
        {
            let callee_ptr = old.cpu_list@[cpu_id as int].get_current_thread().unwrap();
            let caller_ptr = old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).caller.get_Some_0();
            let caller_ipc_payload = old.proc_man.get_thread(caller_ptr).ipc_payload;

            let callee_pcid = old.proc_man.get_proc(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).pcid;
            let caller_pcid = old.proc_man.get_proc(old.proc_man.get_thread(caller_ptr).parent).pcid;
            if caller_ipc_payload.message.is_none() ||
            caller_ipc_payload.page_payload.is_some() ||
            caller_ipc_payload.endpoint_payload.is_some() ||
            caller_ipc_payload.pci_payload.is_some()
            {
                forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                &&
                new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).caller.get_Some_0())
                &&
                new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                &&
                new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
            }else if (spec_va_valid(message_va) == false) || (spec_va_valid(caller_ipc_payload.message.unwrap().0) == false) || (length != caller_ipc_payload.message.unwrap().1)
                || (length>4096) || (length<=0)
            {
                forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                &&
                new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).caller.get_Some_0())
                &&
                new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                &&
                new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
            }else{
                let callee_pa_op = old.mmu_man.get_pagetable_mapping_by_pcid(callee_pcid)[message_va];
                let caller_pa_op = old.mmu_man.get_pagetable_mapping_by_pcid(caller_pcid)[caller_ipc_payload.message.unwrap().0];

                if callee_pa_op.is_None() || caller_pa_op.is_None() {
                    new.cpu_list@[cpu_id as int].get_current_thread() == Some(caller_ptr)
                    &&
                    forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                    &&
                    new.mmu_man =~= old.mmu_man
                    &&
                    forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    &&
                    forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                }else if  callee_pa_op.unwrap().addr == caller_pa_op.unwrap().addr
                {
                    new.cpu_list@[cpu_id as int].get_current_thread() == Some(caller_ptr)
                    &&
                    forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                    &&
                    new.mmu_man =~= old.mmu_man
                    &&
                    forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    &&
                    forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                }else{
                    new.cpu_list@[cpu_id as int].get_current_thread() == Some(caller_ptr)
                    &&
                    forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                    &&
                    new.mmu_man =~= old.mmu_man
                    &&
                    forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    &&
                    forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                }
            }
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

impl Kernel {
    pub fn syscall_reply_message(&mut self, cpu_id:CPUID, pt_regs: &mut Registers, message_va: VAddr, length:usize) -> (ret: SyscallReturnStruct)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            syscall_reply_message_spec(*old(self),*self, cpu_id,message_va, length),
    {
        let (default_pcid, default_cr3) = self.mmu_man.get_reserved_pcid_and_cr3();
        if cpu_id >= NUM_CPUS{
            return SyscallReturnStruct::new(CPU_ID_INVALID,default_pcid,default_cr3);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return SyscallReturnStruct::new(CPU_NO_IDLE,default_pcid,default_cr3);
        }

        assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
        let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
        assert(current_thread_ptr_op.is_Some());
        let current_thread_ptr = current_thread_ptr_op.unwrap();

        let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
        let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);

        let caller_ptr_op = self.proc_man.get_thread_caller(current_thread_ptr);

        if caller_ptr_op.is_none() {
            return SyscallReturnStruct::new(NO_CALLER,pcid,cr3);
        }

        if self.proc_man.scheduler.len() == MAX_NUM_THREADS {

            return SyscallReturnStruct::new(SCHEDULER_NO_SPACE,pcid,cr3);
        }
        let caller_ptr = caller_ptr_op.unwrap();

        let new_pcid = self.proc_man.get_pcid_by_thread_ptr(caller_ptr);
        let new_cr3 = self.mmu_man.get_cr3_by_pcid(new_pcid);

        let caller_ipc_payload = self.proc_man.get_ipc_payload_by_thread_ptr(caller_ptr);

        if caller_ipc_payload.message.is_none() ||
            caller_ipc_payload.page_payload.is_some() ||
            caller_ipc_payload.endpoint_payload.is_some() ||
            caller_ipc_payload.pci_payload.is_some()
        {
            self.proc_man.weak_up_caller_and_schedule(caller_ptr, current_thread_ptr, pt_regs, Some(IPC_TYPE_NOT_MATCH));
            self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
            return SyscallReturnStruct::new(IPC_TYPE_NOT_MATCH,new_pcid,new_cr3);
        }else if  (va_valid(message_va) == false) || (va_valid(caller_ipc_payload.message.unwrap().0) == false) || (length != caller_ipc_payload.message.unwrap().1)
                || (length>4096) || (length<=0)
        {
            self.proc_man.weak_up_caller_and_schedule(caller_ptr, current_thread_ptr, pt_regs, Some(MESSAGE_INVALID));
            self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
            return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3);
        }else{
            let callee_pa_op = self.mmu_man.mmu_get_va_entry_by_pcid(pcid,message_va);
            let caller_pa_op = self.mmu_man.mmu_get_va_entry_by_pcid(new_pcid,caller_ipc_payload.message.unwrap().0);

            if callee_pa_op.is_none() || caller_pa_op.is_none() {
                self.proc_man.weak_up_caller_and_schedule(caller_ptr, current_thread_ptr, pt_regs, Some(MESSAGE_INVALID));
                self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
                return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3);
            }else{
                let callee_pa = callee_pa_op.unwrap().addr;
                let caller_pa = caller_pa_op.unwrap().addr;

                if callee_pa == caller_pa{
                    self.proc_man.weak_up_caller_and_schedule(caller_ptr, current_thread_ptr, pt_regs, Some(MESSAGE_INVALID));
                    self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
                    return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3);
                }else{
                    self.kernel_pass_message(callee_pa, caller_pa, length);

                    self.proc_man.weak_up_caller_and_schedule(caller_ptr, current_thread_ptr, pt_regs, Some(SUCCESS));
                    self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
                    return SyscallReturnStruct::new(SUCCESS,new_pcid,new_cr3);
                }
            }
        }
        
    }
}
}
