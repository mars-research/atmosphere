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
use crate::page_alloc::*;

use crate::kernel::*;

pub closed spec fn syscall_call_with_message_wait_spec(old:Kernel, new:Kernel, cpu_id:CPUID, endpoint_index: EndpointIdx, message_va: VAddr, length:usize) -> bool
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        let valid_thread = (cpu_id < NUM_CPUS &&
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let valid_endpoint = endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS &&
            old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int] != 0;


        if valid_thread && valid_endpoint
        {
            let endpoint_ptr = old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int];
            let endpoint_state = old.proc_man.get_endpoint(endpoint_ptr).queue_state;
            let scheduler_len = old.proc_man.scheduler.len();
            let endpoint_len = old.proc_man.get_endpoint(endpoint_ptr).len();
            if endpoint_state == SEND {
                if endpoint_len == MAX_NUM_THREADS_PER_ENDPOINT{
                    old == new
                }else if scheduler_len == 0{
                    new.cpu_list@[cpu_id as int].get_is_idle() == true
                    &&
                    forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                    &&
                    new.mmu_man =~= old.mmu_man
                    // &&
                    // forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    // &&
                    // forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                }
                else{
                    new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.scheduler@[0])
                    &&
                    forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                    &&
                    new.mmu_man =~= old.mmu_man
                    // &&
                    // forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    // &&
                    // forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                }
            }else{

                if endpoint_len == 0 {
                    if scheduler_len == 0{
                        new.cpu_list@[cpu_id as int].get_is_idle() == true
                        &&
                        forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                        &&
                        new.mmu_man =~= old.mmu_man
                        // &&
                        // forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        // &&
                        // forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                    }
                    else{
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.scheduler@[0])
                        &&
                        forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                        &&
                        new.mmu_man =~= old.mmu_man
                        // &&
                        // forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        // &&
                        // forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                    }
                }else{
                    let receiver_ptr = old.proc_man.get_endpoint(endpoint_ptr).queue@[0];
                    let receiver_ipc_payload = old.proc_man.get_thread(receiver_ptr).ipc_payload;

                    let sender_pcid = old.proc_man.get_proc(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).pcid;
                    let receiver_pcid = old.proc_man.get_proc(old.proc_man.get_thread(receiver_ptr).parent).pcid;
                    if scheduler_len == MAX_NUM_THREADS{
                        old == new
                    }
                    else
                    {
                        if receiver_ipc_payload.calling == false ||
                        receiver_ipc_payload.message.is_None() ||
                        receiver_ipc_payload.page_payload.is_some() ||
                        receiver_ipc_payload.endpoint_payload.is_some() ||
                        receiver_ipc_payload.pci_payload.is_some()
                        {

                            new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                            &&
                            forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                            &&
                            new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                            &&
                            new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                            &&
                            new.mmu_man =~= old.mmu_man
                            // &&
                            // forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                            // &&
                            // forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                        }else if (spec_va_valid(message_va) == false) || (spec_va_valid(receiver_ipc_payload.message.unwrap().0) == false) || (length != receiver_ipc_payload.message.unwrap().1)
                                || (length>4096) || (length<=0)
                        {
                            new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                            &&
                            forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                            &&
                            new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                            &&
                            new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                            &&
                            new.mmu_man =~= old.mmu_man
                            // &&
                            // forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                            // &&
                            // forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                        }else{
                            let sender_pa_op = old.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[message_va];
                            let receiver_pa_op = old.mmu_man.get_pagetable_mapping_by_pcid(receiver_pcid)[receiver_ipc_payload.message.unwrap().0];

                            if sender_pa_op.is_None() || receiver_pa_op.is_None() {
                                new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                                &&
                                forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                                &&
                                new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                                &&
                                new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                                &&
                                new.mmu_man =~= old.mmu_man
                                // &&
                                // forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                                // &&
                                // forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                            }else if  sender_pa_op.unwrap().addr == receiver_pa_op.unwrap().addr
                            {
                                new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                                &&
                                forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                                &&
                                new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                                &&
                                new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                                &&
                                new.mmu_man =~= old.mmu_man
                                // &&
                                // forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                                // &&
                                // forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                            }else if old.proc_man.get_thread(receiver_ptr).caller.is_Some()
                            {
                                // true
                                new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                                &&
                                forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                                &&
                                new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                                &&
                                new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                                &&
                                new.mmu_man =~= old.mmu_man
                                // &&
                                // forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                                // &&
                                // forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                            }else {
                                // true
                                new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                                &&
                                forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                                &&
                                new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                                &&
                                new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == CALLING
                                &&
                                new.mmu_man =~= old.mmu_man
                                // &&
                                // forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                                // &&
                                // forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                            }

                        }
                    }
                }
            }
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old == new
        }

    }
}


impl Kernel {
    pub fn syscall_call_with_message_wait(&mut self, cpu_id:CPUID, pt_regs: &mut Registers, endpoint_index: EndpointIdx, message_va: VAddr, length:usize) -> (ret: SyscallReturnStruct)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            syscall_call_with_message_wait_spec(*old(self), *self, cpu_id, endpoint_index,message_va,length),
    {
        let (default_pcid, default_cr3) = self.mmu_man.get_reserved_pcid_and_cr3();
        if cpu_id >= NUM_CPUS{
            return SyscallReturnStruct::new(CPU_ID_INVALID,default_pcid,default_cr3,0);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return SyscallReturnStruct::new(CPU_NO_IDLE,default_pcid,default_cr3,0);
        }

        assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
        let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
        assert(current_thread_ptr_op.is_Some());
        let current_thread_ptr = current_thread_ptr_op.unwrap();

        let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
        let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);

        let mut ipc_payload = IPCPayLoad::new_to_none();
        ipc_payload.message = Some((message_va,length));
        ipc_payload.calling = true;
        if endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS{
            return SyscallReturnStruct::new(ENDPOINT_INDEX_INVALID,pcid,cr3,current_thread_ptr);
        }

        let target_endpoint_ptr = self.proc_man.get_thread_endpoint_ptr_by_endpoint_idx(current_thread_ptr, endpoint_index);
        if target_endpoint_ptr == 0 {
            return SyscallReturnStruct::new(SHARED_ENDPOINT_NOT_EXIST,pcid,cr3,current_thread_ptr);
        }

        if self.proc_man.get_endpoint_state_by_endpoint_ptr(target_endpoint_ptr) == SEND {
            //sender queue
            if self.proc_man.get_endpoint_len_by_endpoint_ptr(target_endpoint_ptr) == MAX_NUM_THREADS_PER_ENDPOINT{
                assert(self == old(self));
                return SyscallReturnStruct::new(ENDPOINT_FULL,pcid,cr3,current_thread_ptr);
            }

            // self.kernel_push_current_thread_to_endpoint()
            if self.proc_man.scheduler.len() == 0{
                //block current thread on endpoint and spin current cpu
                assert(self.proc_man.get_thread(current_thread_ptr).endpoint_descriptors@[endpoint_index as int] != 0);
                self.proc_man.push_endpoint(current_thread_ptr, endpoint_index, ipc_payload, pt_regs);
                self.cpu_list.set_current_thread(cpu_id, None);
                assert(self.wf());
                return SyscallReturnStruct::new(NO_NEXT_THREAD,0,0,0);
            }else{
                //block current thread on endpoint and pop scheduler
                self.proc_man.push_endpoint(current_thread_ptr, endpoint_index, ipc_payload, pt_regs);
                let (new_thread_ptr,error_code)  = self.proc_man.pop_scheduler(pt_regs);
                self.cpu_list.set_current_thread(cpu_id, Some(new_thread_ptr));
                assert(self.wf());
                let new_pcid = self.proc_man.get_pcid_by_thread_ptr(new_thread_ptr);
                let new_cr3 = self.mmu_man.get_cr3_by_pcid(new_pcid);
                if error_code.is_none(){
                    return SyscallReturnStruct::new(NO_ERROR_CODE,new_pcid,new_cr3,new_thread_ptr);
                }else{
                    return SyscallReturnStruct::new(error_code.unwrap(),new_pcid,new_cr3,new_thread_ptr);
                }
            }
        }
        else{
            //receiver queue
            if self.proc_man.get_endpoint_len_by_endpoint_ptr(target_endpoint_ptr) == 0{
                //change the endpoint to a sender queue.

                // self.proc_man.proc_man_set_endpoint_queue_state_by_endpoint_ptr(target_endpoint_ptr, SEND);
                // assert(self.wf());
                if self.proc_man.scheduler.len() == 0{
                    //block current thread on endpoint and spin current cpu
                    assert(self.proc_man.get_thread(current_thread_ptr).endpoint_descriptors@[endpoint_index as int] != 0);
                    self.proc_man.push_endpoint_and_set_state(current_thread_ptr, endpoint_index, ipc_payload, pt_regs, SEND);
                    self.cpu_list.set_current_thread(cpu_id, None);
                    assert(self.wf());
                    return SyscallReturnStruct::new(NO_NEXT_THREAD,0,0,0);
                }else{
                    //block current thread on endpoint and pop scheduler
                    self.proc_man.push_endpoint_and_set_state(current_thread_ptr, endpoint_index, ipc_payload, pt_regs, SEND);
                    let (new_thread_ptr,error_code)  = self.proc_man.pop_scheduler(pt_regs);
                    self.cpu_list.set_current_thread(cpu_id, Some(new_thread_ptr));
                    assert(self.wf());
                    let new_pcid = self.proc_man.get_pcid_by_thread_ptr(new_thread_ptr);
                    let new_cr3 = self.mmu_man.get_cr3_by_pcid(new_pcid);
                    let error_code = self.proc_man.get_error_code_by_thread_ptr(new_thread_ptr);
                    if error_code.is_none(){
                        return SyscallReturnStruct::new(NO_ERROR_CODE,new_pcid,new_cr3,new_thread_ptr);
                    }else{
                        return SyscallReturnStruct::new(error_code.unwrap(),new_pcid,new_cr3,new_thread_ptr);
                    }
                }

            }
                // pop the receiver.
                if self.proc_man.scheduler.len() == MAX_NUM_THREADS {
                    return SyscallReturnStruct::new(SCHEDULER_NO_SPACE,pcid,cr3,current_thread_ptr);
                }
                let new_thread_ptr = self.proc_man.get_head_of_endpoint_by_endpoint_ptr(target_endpoint_ptr);

                let sender_ipc_payload = ipc_payload;
                let receiver_ipc_payload = self.proc_man.get_ipc_payload_by_thread_ptr(new_thread_ptr);

                let sender_pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
                let receiver_pcid = self.proc_man.get_pcid_by_thread_ptr(new_thread_ptr);
                assert(0<=sender_pcid<PCID_MAX);
                assert(self.mmu_man.get_free_pcids_as_set().contains(sender_pcid) == false);
                assert(0<=receiver_pcid<PCID_MAX);
                assert(self.mmu_man.get_free_pcids_as_set().contains(receiver_pcid) == false);

                let new_pcid = self.proc_man.get_pcid_by_thread_ptr(new_thread_ptr);
                let new_cr3 = self.mmu_man.get_cr3_by_pcid(new_pcid);

                if receiver_ipc_payload.calling == false ||
                    receiver_ipc_payload.message.is_none() ||
                    receiver_ipc_payload.page_payload.is_some() ||
                    receiver_ipc_payload.endpoint_payload.is_some() ||
                    receiver_ipc_payload.pci_payload.is_some()
                {
                    self.proc_man.push_scheduler(current_thread_ptr, Some(IPC_TYPE_NOT_MATCH), pt_regs);
                    let new_thread_ptr = self.proc_man.pop_endpoint_to_running(current_thread_ptr, endpoint_index,pt_regs);
                    self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));

                    return SyscallReturnStruct::new(IPC_TYPE_NOT_MATCH,new_pcid,new_cr3,new_thread_ptr);
                }else if (va_valid(message_va) == false) || (va_valid(receiver_ipc_payload.message.unwrap().0) == false) || (length != receiver_ipc_payload.message.unwrap().1)
                            || (length>4096) || (length<=0)
                {
                    self.proc_man.push_scheduler(current_thread_ptr, Some(MESSAGE_INVALID), pt_regs);
                    let new_thread_ptr = self.proc_man.pop_endpoint_to_running(current_thread_ptr, endpoint_index,pt_regs);
                    self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));

                    return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3,new_thread_ptr);
                }else{
                    let sender_pa_op = self.mmu_man.mmu_get_va_entry_by_pcid(pcid,message_va);
                    let receiver_pa_op = self.mmu_man.mmu_get_va_entry_by_pcid(new_pcid,receiver_ipc_payload.message.unwrap().0);

                    if sender_pa_op.is_none() || receiver_pa_op.is_none() {
                        self.proc_man.push_scheduler(current_thread_ptr, Some(MESSAGE_INVALID), pt_regs);
                        let new_thread_ptr = self.proc_man.pop_endpoint_to_running(current_thread_ptr, endpoint_index,pt_regs);
                        self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                        return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3,new_thread_ptr);
                    }else{
                        let sender_pa = sender_pa_op.unwrap().addr;
                        let receiver_pa = receiver_pa_op.unwrap().addr;

                        if sender_pa == receiver_pa {
                            self.proc_man.push_scheduler(current_thread_ptr, Some(MESSAGE_INVALID), pt_regs);
                            let new_thread_ptr = self.proc_man.pop_endpoint_to_running(current_thread_ptr, endpoint_index,pt_regs);
                            self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                            return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3,new_thread_ptr);
                        }else if self.proc_man.get_thread_caller(new_thread_ptr).is_some()  {
                            self.proc_man.push_scheduler(current_thread_ptr, Some(MESSAGE_INVALID), pt_regs);
                            let new_thread_ptr = self.proc_man.pop_endpoint_to_running(current_thread_ptr, endpoint_index,pt_regs);
                            self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));
                            return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3,new_thread_ptr);
                        }else{
                            let caller_pt_regs = *pt_regs;
                            let new_thread_ptr = self.proc_man.pop_endpoint_to_running(current_thread_ptr, endpoint_index,pt_regs);
                            self.kernel_pass_message(sender_pa, receiver_pa, length);

                            self.proc_man.set_thread_caller(current_thread_ptr, new_thread_ptr, &caller_pt_regs);
                            self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));

                            return SyscallReturnStruct::new(SUCCESS,new_pcid,new_cr3,new_thread_ptr);
                        }
                    }
                }



        }
    }
}
}
