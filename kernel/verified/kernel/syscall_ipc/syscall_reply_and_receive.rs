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

pub closed spec fn syscall_reply_and_receive_spec(old:Kernel, new:Kernel, cpu_id:CPUID,endpoint_index:EndpointIdx, message_va: VAddr, length:usize, return_message: Option<(VAddr, usize)>) -> bool
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
        let valid_endpoint = endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS && 
            old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int] != 0;
        let endpoint_has_space = old.proc_man.get_endpoint(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int]).len() != MAX_NUM_THREADS_PER_ENDPOINT;
        let endpoint_ok_to_send = old.proc_man.get_endpoint(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int]).len() == 0 ||
            old.proc_man.get_endpoint(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int]).queue_state != SEND;

        if valid_thread && has_caller && system_scheduler_has_space && valid_endpoint && endpoint_has_space && endpoint_ok_to_send
        {
            let callee_ptr = old.cpu_list@[cpu_id as int].get_current_thread().unwrap();
            let caller_ptr = old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).caller.get_Some_0();
            let caller_ipc_payload = old.proc_man.get_thread(caller_ptr).ipc_payload;

            let callee_pcid = old.proc_man.get_proc(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).pcid;
            let caller_pcid = old.proc_man.get_proc(old.proc_man.get_thread(caller_ptr).parent).pcid;
            if return_message.is_some() || caller_ipc_payload.message.is_some()
            {
                //sharing message
                if return_message.is_none() || caller_ipc_payload.message.is_none() {
                    forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                    &&
                    new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).caller.get_Some_0())
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                    &&
                    new.mmu_man =~= old.mmu_man
                }else if caller_ipc_payload.page_payload.is_some() || caller_ipc_payload.endpoint_payload.is_some() || caller_ipc_payload.pci_payload.is_some()
                {
                    forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                    &&
                    new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).caller.get_Some_0())
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                    &&
                    new.mmu_man =~= old.mmu_man
                }else{
                    let sender_va = return_message.unwrap().0;
                    let receiver_va = caller_ipc_payload.message.unwrap().0;
    
                    let sender_len = return_message.unwrap().1;
                    let receiver_len = caller_ipc_payload.message.unwrap().1;
                    if (spec_va_valid(sender_va) == false) || (spec_va_valid(receiver_va) == false) || (sender_len != receiver_len)
                    || (receiver_len>4096) || (receiver_len<=0)
                    {
                        forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                        &&
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).caller.get_Some_0())
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                        &&
                        new.mmu_man =~= old.mmu_man
                    }else{
                        let sender_pa_op = old.mmu_man.get_pagetable_mapping_by_pcid(callee_pcid)[sender_va];
                        let receiver_pa_op = old.mmu_man.get_pagetable_mapping_by_pcid(caller_pcid)[receiver_va];
                        
                        if sender_pa_op.is_none() || receiver_pa_op.is_none() {
                            forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                            &&
                            new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).caller.get_Some_0())
                            &&
                            new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                            &&
                            new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                            &&
                            new.mmu_man =~= old.mmu_man
                        }else{
                            let sender_pa = sender_pa_op.unwrap().addr;
                            let receiver_pa = receiver_pa_op.unwrap().addr;
    
                            if sender_pa == receiver_pa {
                                forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                                &&
                                new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).caller.get_Some_0())
                                &&
                                new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                                &&
                                new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                                &&
                                new.mmu_man =~= old.mmu_man
                            }else if old.proc_man.get_endpoint(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int]).queue_state == SEND {
                                forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                                &&
                                new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).caller.get_Some_0())
                                &&
                                new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                                &&
                                new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                                &&
                                new.mmu_man =~= old.mmu_man
                            }else{
                                forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                                &&
                                new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).caller.get_Some_0())
                                &&
                                new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                                &&
                                new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                                &&
                                new.mmu_man =~= old.mmu_man
                            }
                        }
                    }
                }
            }else{
                //no return value
                forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                &&
                new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).caller.get_Some_0())
                &&
                new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                &&
                new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                &&
                new.mmu_man =~= old.mmu_man
            }
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

impl Kernel {
    pub fn syscall_reply_and_receive(&mut self, cpu_id:CPUID, pt_regs: &mut Registers, endpoint_index:EndpointIdx, message_va: VAddr, length:usize, return_message: Option<(VAddr, usize)>) -> (ret: SyscallReturnStruct)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            syscall_reply_and_receive_spec(*old(self),*self, cpu_id,endpoint_index, message_va, length, return_message),
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


        if endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS{
            return SyscallReturnStruct::new(ENDPOINT_INDEX_INVALID,pcid,cr3);
        }
        let target_endpoint_ptr = self.proc_man.get_thread_endpoint_ptr_by_endpoint_idx(current_thread_ptr, endpoint_index);
        if target_endpoint_ptr == 0 {
            return SyscallReturnStruct::new(SHARED_ENDPOINT_NOT_EXIST,pcid,cr3);
        }

        if self.proc_man.get_endpoint_len_by_endpoint_ptr(target_endpoint_ptr) == MAX_NUM_THREADS_PER_ENDPOINT{
            return SyscallReturnStruct::new(ENDPOINT_FULL,pcid,cr3);
        }

        if self.proc_man.get_endpoint_len_by_endpoint_ptr(target_endpoint_ptr) != 0 && self.proc_man.get_endpoint_state_by_endpoint_ptr(target_endpoint_ptr) == SEND {
            return SyscallReturnStruct::new(ENDPOINT_SENDER_QUEUE,pcid,cr3);
        }

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

        let mut callee_ipc_payload = IPCPayLoad::new_to_none();
        callee_ipc_payload.calling == true;
        callee_ipc_payload.message = Some((message_va,length));
        let caller_ipc_payload = self.proc_man.get_ipc_payload_by_thread_ptr(caller_ptr);

        if return_message.is_some() || caller_ipc_payload.message.is_some()
        {
            //sharing message
            if return_message.is_none() || caller_ipc_payload.message.is_none() {
                self.proc_man.weak_up_caller_and_schedule(caller_ptr, current_thread_ptr, pt_regs, Some(MESSAGE_INVALID));
                self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
                return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3);
            }
            else if caller_ipc_payload.page_payload.is_some() || caller_ipc_payload.endpoint_payload.is_some() || caller_ipc_payload.pci_payload.is_some()
            {
                self.proc_man.weak_up_caller_and_schedule(caller_ptr, current_thread_ptr, pt_regs, Some(MESSAGE_INVALID));
                self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
                return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3);
            }
            else{
                let sender_va = return_message.unwrap().0;
                let receiver_va = caller_ipc_payload.message.unwrap().0;

                let sender_len = return_message.unwrap().1;
                let receiver_len = caller_ipc_payload.message.unwrap().1;

                if (va_valid(sender_va) == false) || (va_valid(receiver_va) == false) || (sender_len != receiver_len)
                    || (receiver_len>4096) || (receiver_len<=0)
                {
                    self.proc_man.weak_up_caller_and_schedule(caller_ptr, current_thread_ptr, pt_regs, Some(MESSAGE_INVALID));
                    self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
                    return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3);
                }else{
                    let sender_pa_op = self.mmu_man.mmu_get_va_entry_by_pcid(pcid,sender_va);
                    let receiver_pa_op = self.mmu_man.mmu_get_va_entry_by_pcid(new_pcid,receiver_va);

                    if sender_pa_op.is_none() || receiver_pa_op.is_none() {
                        self.proc_man.weak_up_caller_and_schedule(caller_ptr, current_thread_ptr, pt_regs, Some(MESSAGE_INVALID));
                        self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
                        return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3);
                    }else{
                        let sender_pa = sender_pa_op.unwrap().addr;
                        let receiver_pa = receiver_pa_op.unwrap().addr;

                        if sender_pa == receiver_pa {
                            self.proc_man.weak_up_caller_and_schedule(caller_ptr, current_thread_ptr, pt_regs, Some(MESSAGE_INVALID));
                            self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
                            return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3);
                        }else if self.proc_man.get_endpoint_state_by_endpoint_ptr(target_endpoint_ptr) == SEND {
                            assert(self.proc_man.get_endpoint(target_endpoint_ptr).len() == 0);
                            self.kernel_pass_message(sender_pa, receiver_pa, receiver_len);
                            self.proc_man.weak_up_caller_change_queue_state_and_receive(caller_ptr, current_thread_ptr, pt_regs, callee_ipc_payload, endpoint_index);
                            self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
                            return SyscallReturnStruct::new(SUCCESS,new_pcid,new_cr3);
                        }else{
                            self.kernel_pass_message(sender_pa, receiver_pa, receiver_len);
                            self.proc_man.weak_up_caller_and_receive(caller_ptr, current_thread_ptr, pt_regs, callee_ipc_payload, endpoint_index);
                            self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
                            return SyscallReturnStruct::new(SUCCESS,new_pcid,new_cr3);
                        }
                        
                    }
                }
            }
        }else{
            if self.proc_man.get_endpoint_state_by_endpoint_ptr(target_endpoint_ptr) == SEND {
                assert(self.proc_man.get_endpoint(target_endpoint_ptr).len() == 0);
                self.proc_man.weak_up_caller_change_queue_state_and_receive(caller_ptr, current_thread_ptr, pt_regs, callee_ipc_payload, endpoint_index);
                self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
                return SyscallReturnStruct::new(SUCCESS,new_pcid,new_cr3);
            }else{
                self.proc_man.weak_up_caller_and_receive(caller_ptr, current_thread_ptr, pt_regs, callee_ipc_payload, endpoint_index);
                self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
                return SyscallReturnStruct::new(SUCCESS,new_pcid,new_cr3);
            }
        }
    }
}
}
