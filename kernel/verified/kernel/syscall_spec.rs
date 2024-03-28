use vstd::prelude::*;
verus! {

use crate::pagetable::*;
use crate::cpu::*;
use crate::define::*;
use crate::trap::*;
use crate::page_alloc::*;

use crate::kernel::*;

pub closed spec fn _syscall_call_with_message_wait_spec(old:Kernel, new:Kernel, cpu_id:CPUID, endpoint_index: EndpointIdx, message_va: VAddr, length:usize) -> bool
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
            //if the _syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

pub closed spec fn _syscall_receive_empty_wait_spec(old:Kernel, new:Kernel, cpu_id:CPUID, endpoint_index: EndpointIdx) -> bool
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
            if endpoint_state == RECEIVE {
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
                    forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    &&
                    forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                }
                else{
                    new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.scheduler@[0])
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)                    
                    &&
                    forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    &&
                    forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                    }
                }else{
                    let sender_ptr = old.proc_man.get_endpoint(endpoint_ptr).queue@[0];
                    let sender_ipc_payload = old.proc_man.get_thread(sender_ptr).ipc_payload;
                    
                    if scheduler_len == MAX_NUM_THREADS{
                        old == new
                    }else if sender_ipc_payload.calling != false ||
                    sender_ipc_payload.message.is_some() ||
                    sender_ipc_payload.page_payload.is_some() ||
                    sender_ipc_payload.endpoint_payload.is_some() ||
                    sender_ipc_payload.pci_payload.is_some()
                    {
                        forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                        &&
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(sender_ptr)
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                    }else{

                        forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                        &&
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(sender_ptr)
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                    }

                }
            }
        }else{
            //if the _syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

pub closed spec fn _syscall_receive_endpoint_wait_spec(old:Kernel, new:Kernel, cpu_id:CPUID, endpoint_index: EndpointIdx, share_endpoint_index: EndpointIdx) -> bool
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
            if endpoint_state == RECEIVE {
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
                    &&
                    forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    &&
                    forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                }
                else{
                    new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.scheduler@[0])
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                    &&
                    new.mmu_man =~= old.mmu_man
                    &&
                    forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    &&
                    forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                    }
                }else{
                    let sender_ptr = old.proc_man.get_endpoint(endpoint_ptr).queue@[0];
                    let sender_ipc_payload = old.proc_man.get_thread(sender_ptr).ipc_payload;

                    let receiver_pcid = old.proc_man.get_proc(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).pcid;
                    let sender_pcid = old.proc_man.get_proc(old.proc_man.get_thread(sender_ptr).parent).pcid;
                    if scheduler_len == MAX_NUM_THREADS{
                        old == new
                    }else if sender_ipc_payload.calling != false ||
                    sender_ipc_payload.message.is_some() ||
                    sender_ipc_payload.page_payload.is_some() ||
                    sender_ipc_payload.endpoint_payload.is_none() ||
                    sender_ipc_payload.pci_payload.is_some()
                    {
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(sender_ptr)
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
                    }else
                    {
                        let receiver_endpoint_index = share_endpoint_index;
                        let sender_endpoint_index = sender_ipc_payload.endpoint_payload.unwrap();
                        if sender_endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS || receiver_endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS {
                            new.cpu_list@[cpu_id as int].get_current_thread() == Some(sender_ptr)
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
                            let receiver_endpoint_ptr = old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[receiver_endpoint_index as int];
                            let sender_endpoint_ptr =  old.proc_man.get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int];

                            if sender_endpoint_ptr == 0 || receiver_endpoint_ptr != 0
                                ||old.proc_man.get_endpoint(sender_endpoint_ptr).rf_counter == usize::MAX
                                || (
                                    forall|i:int| #![auto] 0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS ==> old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[i as int] != sender_endpoint_ptr
                                ) == false
                            {
                                new.cpu_list@[cpu_id as int].get_current_thread() == Some(sender_ptr)
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
                                new.cpu_list@[cpu_id as int].get_current_thread() == Some(sender_ptr)
                                &&
                                new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                                &&
                                new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                                &&
                                new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@ =~= old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@.update(
                                    receiver_endpoint_index as int, sender_endpoint_ptr)
                                &&
                                new.mmu_man =~= old.mmu_man
                                &&
                                forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                                &&
                                forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                            }
                        }
                    }
                }
            }
        }else{
            //if the _syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

pub closed spec fn _syscall_receive_message_wait_spec(old:Kernel, new:Kernel, cpu_id:CPUID, endpoint_index: EndpointIdx, message_va: VAddr, length:usize) -> bool
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
            if endpoint_state == RECEIVE {
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
                    &&
                    forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    &&
                    forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                    &&
                    forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    &&
                    forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                    }
                }else{
                    let sender_ptr = old.proc_man.get_endpoint(endpoint_ptr).queue@[0];
                    let sender_ipc_payload = old.proc_man.get_thread(sender_ptr).ipc_payload;

                    let receiver_pcid = old.proc_man.get_proc(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).pcid;
                    let sender_pcid = old.proc_man.get_proc(old.proc_man.get_thread(sender_ptr).parent).pcid;
                    if scheduler_len == MAX_NUM_THREADS{
                        old == new
                    }else if sender_ipc_payload.calling != false ||
                    sender_ipc_payload.message.is_None() ||
                    sender_ipc_payload.page_payload.is_some() ||
                    sender_ipc_payload.endpoint_payload.is_some() ||
                    sender_ipc_payload.pci_payload.is_some()
                    {
                        
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(sender_ptr)
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
                    }else if (spec_va_valid(message_va) == false) || (spec_va_valid(sender_ipc_payload.message.unwrap().0) == false) || (length != sender_ipc_payload.message.unwrap().1)
                            || (length>4096) || (length<=0)
                    {
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(sender_ptr)
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
                        let sender_pa_op = old.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[sender_ipc_payload.message.unwrap().0];
                        let receiver_pa_op = old.mmu_man.get_pagetable_mapping_by_pcid(receiver_pcid)[message_va];

                        if sender_pa_op.is_None() || receiver_pa_op.is_None() {
                            new.cpu_list@[cpu_id as int].get_current_thread() == Some(sender_ptr)
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
                        }else if  sender_pa_op.unwrap().addr == receiver_pa_op.unwrap().addr
                        {
                            new.cpu_list@[cpu_id as int].get_current_thread() == Some(sender_ptr)
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
                            new.cpu_list@[cpu_id as int].get_current_thread() == Some(sender_ptr)
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
                }
            }
        }else{
            //if the _syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

pub closed spec fn _syscall_receive_pages_wait_spec(old:Kernel, new:Kernel, cpu_id:CPUID, endpoint_index: EndpointIdx, va: VAddr, range: usize) -> bool
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
            if endpoint_state == RECEIVE {
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
                    &&
                    forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    &&
                    forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                }
                else{
                    new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.scheduler@[0])
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                    &&
                    new.mmu_man =~= old.mmu_man
                    &&
                    forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    &&
                    forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                    }
                }else{
                    let sender_ptr = old.proc_man.get_endpoint(endpoint_ptr).queue@[0];
                    let sender_ipc_payload = old.proc_man.get_thread(sender_ptr).ipc_payload;
                    
                    let receiver_pcid = old.proc_man.get_proc(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).pcid;
                    let sender_pcid = old.proc_man.get_proc(old.proc_man.get_thread(sender_ptr).parent).pcid;

                    if scheduler_len == MAX_NUM_THREADS{
                        old == new
                    }else if sender_ipc_payload.calling != false ||
                        sender_ipc_payload.message.is_some() ||
                        sender_ipc_payload.page_payload.is_None() ||
                        sender_ipc_payload.endpoint_payload.is_some() ||
                        sender_ipc_payload.pci_payload.is_some()
                    {
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(sender_ptr)
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

                    }else if sender_ipc_payload.page_payload.unwrap().1 != range ||
                                range >= usize::MAX/3 || 
                                old.page_alloc.free_pages.len() < 3 * range
                    {
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(sender_ptr)
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
                    }
                    else if kernel_page_sharing_spec_helper(old,sender_pcid,receiver_pcid, sender_ipc_payload.page_payload.unwrap().0,va, range)
                    {
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(sender_ptr)
                        &&
                        forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                        &&
                        forall|j:usize| #![auto] 0<=j<range ==> new.mmu_man.get_pagetable_mapping_by_pcid(receiver_pcid)[spec_va_add_range(va,j)].is_Some()
                        &&
                        forall|j:usize| #![auto] 0<=j<range ==> new.mmu_man.get_pagetable_mapping_by_pcid(receiver_pcid)[spec_va_add_range(va,j)].get_Some_0().addr =~= new.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_ipc_payload.page_payload.unwrap().0,j)].get_Some_0().addr
                        &&
                        forall|i:IOid| #![auto] 0<=i<PCID_MAX ==> new.mmu_man.get_iommutable_mapping_by_ioid(i) =~= old.mmu_man.get_iommutable_mapping_by_ioid(i)
                        &&
                        forall|i:Pcid| #![auto] 0<=i<PCID_MAX && i != receiver_pcid ==> new.mmu_man.get_pagetable_mapping_by_pcid(i) =~= old.mmu_man.get_pagetable_mapping_by_pcid(i)
                    }else
                    {
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(sender_ptr)
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
                    }


                }
            }
        }else{
            //if the _syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

pub closed spec fn _syscall_reply_and_receive_spec(old:Kernel, new:Kernel, cpu_id:CPUID,endpoint_index:EndpointIdx, message_va: VAddr, length:usize, return_message: Option<(VAddr, usize)>) -> bool
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
            //if the _syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

pub closed spec fn _syscall_reply_empty_spec(old:Kernel, new:Kernel, cpu_id:CPUID) -> bool
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
            forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
            &&
            new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).caller.get_Some_0())
            &&
            new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
            &&
            new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
        }else{
            //if the _syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

pub closed spec fn _syscall_reply_message_spec(old:Kernel, new:Kernel, cpu_id:CPUID, message_va: VAddr, length:usize) -> bool
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
            //if the _syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

pub closed spec fn _syscall_send_empty_no_wait_spec(old:Kernel, new:Kernel, cpu_id:CPUID, endpoint_index: EndpointIdx) -> bool
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
                old == new
            }else{
                if endpoint_len == 0 {
                    old == new
                }else{
                    let receiver_ptr = old.proc_man.get_endpoint(endpoint_ptr).queue@[0];
                    let receiver_ipc_payload = old.proc_man.get_thread(receiver_ptr).ipc_payload;
                    
                    if scheduler_len == MAX_NUM_THREADS{
                        old == new
                    }else if receiver_ipc_payload.calling != false ||
                    receiver_ipc_payload.message.is_some() ||
                    receiver_ipc_payload.page_payload.is_some() ||
                    receiver_ipc_payload.endpoint_payload.is_some() ||
                    receiver_ipc_payload.pci_payload.is_some()
                    {
                        
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                    }else{
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                    }

                }
            }
        }else{
            //if the _syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

pub closed spec fn _syscall_send_empty_wait_spec(old:Kernel, new:Kernel, cpu_id:CPUID, endpoint_index: EndpointIdx) -> bool
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
                    forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    &&
                    forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                }
                else{
                    new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.scheduler@[0])
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)                    
                    &&
                    forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    &&
                    forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                    }
                }else{
                    let receiver_ptr = old.proc_man.get_endpoint(endpoint_ptr).queue@[0];
                    let receiver_ipc_payload = old.proc_man.get_thread(receiver_ptr).ipc_payload;
                    
                    if scheduler_len == MAX_NUM_THREADS{
                        old == new
                    }else if receiver_ipc_payload.calling != false ||
                    receiver_ipc_payload.message.is_some() ||
                    receiver_ipc_payload.page_payload.is_some() ||
                    receiver_ipc_payload.endpoint_payload.is_some() ||
                    receiver_ipc_payload.pci_payload.is_some()
                    {
                        forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                        &&
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                    }else{

                        forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                        &&
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                    }

                }
            }
        }else{
            //if the _syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

pub closed spec fn _syscall_send_endpoint_wait_spec(old:Kernel, new:Kernel, cpu_id:CPUID, endpoint_index: EndpointIdx, share_endpoint_index: EndpointIdx) -> bool
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
                    &&
                    forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    &&
                    forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                }
                else{
                    new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.scheduler@[0])
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                    &&
                    new.mmu_man =~= old.mmu_man
                    &&
                    forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    &&
                    forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                    }
                }else{
                    let receiver_ptr = old.proc_man.get_endpoint(endpoint_ptr).queue@[0];
                    let receiver_ipc_payload = old.proc_man.get_thread(receiver_ptr).ipc_payload;

                    let sender_pcid = old.proc_man.get_proc(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).pcid;
                    let receiver_pcid = old.proc_man.get_proc(old.proc_man.get_thread(receiver_ptr).parent).pcid;
                    if scheduler_len == MAX_NUM_THREADS{
                        old == new
                    }else if receiver_ipc_payload.calling != false ||
                    receiver_ipc_payload.message.is_some() ||
                    receiver_ipc_payload.page_payload.is_some() ||
                    receiver_ipc_payload.endpoint_payload.is_none() ||
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
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                    }else
                    {
                        let sender_endpoint_index = share_endpoint_index;
                        let receiver_endpoint_index = receiver_ipc_payload.endpoint_payload.unwrap();
                        if sender_endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS || receiver_endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS {
                            new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
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
                            let sender_endpoint_ptr = old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[sender_endpoint_index as int];
                            let receiver_endpoint_ptr =  old.proc_man.get_thread(receiver_ptr).endpoint_descriptors@[receiver_endpoint_index as int];

                        
                            if sender_endpoint_ptr == 0 || receiver_endpoint_ptr != 0
                                ||old.proc_man.get_endpoint(sender_endpoint_ptr).rf_counter == usize::MAX
                                || (
                                    forall|i:int| #![auto] 0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS ==> old.proc_man.get_thread(receiver_ptr).endpoint_descriptors@[i as int] != sender_endpoint_ptr
                                ) == false
                            {
                                new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
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

                                new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                                &&
                                new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                                &&
                                new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                                &&
                                new.proc_man.get_thread(receiver_ptr).endpoint_descriptors@ =~= old.proc_man.get_thread(receiver_ptr).endpoint_descriptors@.update(
                                                        receiver_endpoint_index as int, old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[sender_endpoint_index as int])
                                &&
                                new.mmu_man =~= old.mmu_man
                                &&
                                forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                                &&
                                forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                            }
                        }
                    }
                }
            }
        }else{
            //if the _syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

pub closed spec fn _syscall_send_message_wait_spec(old:Kernel, new:Kernel, cpu_id:CPUID, endpoint_index: EndpointIdx, message_va: VAddr, length:usize) -> bool
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
                    &&
                    forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    &&
                    forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                    &&
                    forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    &&
                    forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                    }
                }else{
                    let receiver_ptr = old.proc_man.get_endpoint(endpoint_ptr).queue@[0];
                    let receiver_ipc_payload = old.proc_man.get_thread(receiver_ptr).ipc_payload;

                    let sender_pcid = old.proc_man.get_proc(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).pcid;
                    let receiver_pcid = old.proc_man.get_proc(old.proc_man.get_thread(receiver_ptr).parent).pcid;
                    if scheduler_len == MAX_NUM_THREADS{
                        old == new
                    }else if receiver_ipc_payload.calling != false ||
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
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                            &&
                            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                            &&
                            forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                            &&
                            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                            &&
                            forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                        }else{
                            new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
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
                }
            }
        }else{
            //if the _syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

pub closed spec fn _syscall_send_pages_wait_spec(old:Kernel, new:Kernel, cpu_id:CPUID, endpoint_index: EndpointIdx, va: VAddr, range: usize) -> bool
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
                    &&
                    forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    &&
                    forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                }
                else{
                    new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.scheduler@[0])
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                    &&
                    new.mmu_man =~= old.mmu_man
                    &&
                    forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                    &&
                    forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
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
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                    }
                }else{
                    let receiver_ptr = old.proc_man.get_endpoint(endpoint_ptr).queue@[0];
                    let receiver_ipc_payload = old.proc_man.get_thread(receiver_ptr).ipc_payload;
                    
                    let sender_pcid = old.proc_man.get_proc(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).pcid;
                    let receiver_pcid = old.proc_man.get_proc(old.proc_man.get_thread(receiver_ptr).parent).pcid;

                    if scheduler_len == MAX_NUM_THREADS{
                        old == new
                    }else if receiver_ipc_payload.calling != false ||
                                receiver_ipc_payload.message.is_some() ||
                                receiver_ipc_payload.page_payload.is_None() ||
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
                        &&
                        forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                        &&
                        forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]

                    }else if receiver_ipc_payload.page_payload.unwrap().1 != range ||
                                range >= usize::MAX/3 || 
                                old.page_alloc.free_pages.len() < 3 * range
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
                    }
                    else if kernel_page_sharing_spec_helper(old,sender_pcid,receiver_pcid, va, receiver_ipc_payload.page_payload.unwrap().0, range)
                    {
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                        &&
                        forall|_cpu_id:CPUID| #![auto] 0 <= _cpu_id < NUM_CPUS && _cpu_id != cpu_id ==> new.cpu_list@[_cpu_id as int] =~= old.cpu_list@[_cpu_id as int]
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                        &&
                        forall|j:usize| #![auto] 0<=j<range ==> new.mmu_man.get_pagetable_mapping_by_pcid(receiver_pcid)[spec_va_add_range(receiver_ipc_payload.page_payload.unwrap().0,j)].is_Some()
                        &&
                        forall|j:usize| #![auto] 0<=j<range ==> new.mmu_man.get_pagetable_mapping_by_pcid(receiver_pcid)[spec_va_add_range(receiver_ipc_payload.page_payload.unwrap().0,j)].get_Some_0().addr =~= new.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(va,j)].get_Some_0().addr
                        &&
                        forall|i:IOid| #![auto] 0<=i<PCID_MAX ==> new.mmu_man.get_iommutable_mapping_by_ioid(i) =~= old.mmu_man.get_iommutable_mapping_by_ioid(i)
                        &&
                        forall|i:Pcid| #![auto] 0<=i<PCID_MAX && i != receiver_pcid ==> new.mmu_man.get_pagetable_mapping_by_pcid(i) =~= old.mmu_man.get_pagetable_mapping_by_pcid(i)
                    }else
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
                    }


                }
            }
        }else{
            //if the _syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

pub closed spec fn _syscall_new_proc_with_iommu_spec(old:Kernel,new:Kernel,cpu_id:CPUID, endpoint_index: EndpointIdx, new_proc:Option<ProcPtr>, new_thread:Option<ThreadPtr>) -> bool 
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        //checking arguments
        let valid_thread = (cpu_id < NUM_CPUS && 
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let valid_endpoint = (endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS && 
            old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int] != 0 &&
            old.proc_man.get_endpoint(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int]).rf_counter != usize::MAX);
        let proc_list_has_space = old.proc_man.proc_ptrs.len() != MAX_NUM_PROCS;
        let system_has_memory = old.page_alloc.free_pages.len() >= 5;
        let system_has_free_pcid_ioid = old.mmu_man.free_pcids.len() != 0 && old.mmu_man.free_ioids.len() != 0;
        let system_scheduler_has_space = old.proc_man.scheduler.len() != MAX_NUM_THREADS;

        if valid_thread && valid_endpoint && proc_list_has_space && system_has_memory && system_has_free_pcid_ioid && system_scheduler_has_space
        {
            (
                //if the _syscall is success, a new process and a new thread of the new process will be created
                new_proc.is_Some()
                &&
                new_thread.is_Some()
                &&
                //each cpu still runs the same thread, no context switch
                new.cpu_list =~= old.cpu_list
                &&
                // kernel correctly created a new process
                new.proc_man.get_proc_ptrs() =~= old.proc_man.get_proc_ptrs().push(new_proc.unwrap())
                &&
                // kernel correctly created a new thread for that process
                new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs().insert(new_thread.unwrap())
                &&
                // the new thread is scheduled
                new.proc_man.get_thread(new_thread.unwrap()).state == SCHEDULED
                &&
                // the new thread stores the endpoint from the parent process at 1st slot
                new.proc_man.get_thread(new_thread.unwrap()).endpoint_descriptors@[0] =~= new.proc_man.get_thread(new.cpu_list[cpu_id as int].current_t.unwrap()).endpoint_descriptors@[endpoint_index as int]
                &&
                // the new proccess's pagetable is empty. There are kernel and loader mapped in this new pagetable, but they are transparent to user level
                forall|va:VAddr| #![auto] spec_va_valid(va) ==> new.mmu_man.get_pagetable_by_pcid(new.proc_man.get_proc(new.proc_man.get_thread(new_thread.unwrap()).parent).pcid).get_pagetable_mapping()[va].is_None()                
                &&
                forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                &&
                forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
            )
        }else{
            //if the _syscall is not success, nothing will change, goes back to user level
            old =~= new
        }
    }
}

pub closed spec fn _syscall_new_proc_spec(old:Kernel,new:Kernel,cpu_id:CPUID, endpoint_index: EndpointIdx, new_proc:Option<ProcPtr>, new_thread:Option<ThreadPtr>) -> bool 
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        //checking arguments
        let valid_thread = (cpu_id < NUM_CPUS && 
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let valid_endpoint = (endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS && 
            old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int] != 0 &&
            old.proc_man.get_endpoint(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int]).rf_counter != usize::MAX);
        let proc_list_has_space = old.proc_man.proc_ptrs.len() != MAX_NUM_PROCS;
        let system_has_memory = old.page_alloc.free_pages.len() >= 4;
        let system_has_free_pcid = old.mmu_man.free_pcids.len() != 0;
        let system_scheduler_has_space = old.proc_man.scheduler.len() != MAX_NUM_THREADS;

        if valid_thread && valid_endpoint && proc_list_has_space && system_has_memory && system_has_free_pcid && system_scheduler_has_space
        {
            (
                //if the _syscall is success, a new process and a new thread of the new process will be created
                new_proc.is_Some()
                &&
                new_thread.is_Some()
                &&
                //each cpu still runs the same thread, no context switch
                new.cpu_list =~= old.cpu_list
                &&
                // kernel correctly created a new process
                new.proc_man.get_proc_ptrs() =~= old.proc_man.get_proc_ptrs().push(new_proc.unwrap())
                &&
                // kernel correctly created a new thread for that process
                new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs().insert(new_thread.unwrap())
                &&
                // the new thread is scheduled
                new.proc_man.get_thread(new_thread.unwrap()).state == SCHEDULED
                &&
                // the new thread stores the endpoint from the parent process at 1st slot
                new.proc_man.get_thread(new_thread.unwrap()).endpoint_descriptors@[0] =~= new.proc_man.get_thread(new.cpu_list[cpu_id as int].current_t.unwrap()).endpoint_descriptors@[endpoint_index as int]
                &&
                // the new proccess's pagetable is empty. There are kernel and loader mapped in this new pagetable, but they are transparent to user level
                forall|va:VAddr| #![auto] spec_va_valid(va) ==> new.mmu_man.get_pagetable_by_pcid(new.proc_man.get_proc(new.proc_man.get_thread(new_thread.unwrap()).parent).pcid).get_pagetable_mapping()[va].is_None()
                &&
                forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                &&
                forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
            )
        }else{
            //if the _syscall is not success, nothing will change, goes back to user level
            old =~= new
        }
    }
    
}

pub closed spec fn _syscall_new_endpoint_spec(old:Kernel,new:Kernel,cpu_id:CPUID, endpoint_index: EndpointIdx) -> bool 
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        //checking arguments
        let valid_thread = (cpu_id < NUM_CPUS && 
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let valid_endpoint = endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS && 
            old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int] == 0;
        let system_has_memory = old.page_alloc.free_pages.len() >= 1;

        if valid_thread && valid_endpoint && system_has_memory
        {
            new.cpu_list =~= old.cpu_list
            &&
            // kernel correctly created a new process
            new.proc_man.get_proc_ptrs() =~= old.proc_man.get_proc_ptrs()
            &&
            // kernel correctly created a new thread for that process
            new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
            &&
            new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int] != 0
            &&
            new.proc_man.get_endpoint_ptrs().len() == old.proc_man.get_endpoint_ptrs().len() + 1
            &&
            forall|_thread_ptr:ThreadPtr| #![auto] new.proc_man.get_thread_ptrs().contains(_thread_ptr) && _thread_ptr != old.cpu_list@[cpu_id as int].get_current_thread().unwrap() ==> new.proc_man.get_thread(_thread_ptr) =~= old.proc_man.get_thread(_thread_ptr)
            &&
            forall|_proc_ptr:ProcPtr| #![auto] new.proc_man.get_proc_ptrs().contains(_proc_ptr) ==> new.proc_man.get_proc(_proc_ptr) =~= old.proc_man.get_proc(_proc_ptr)
            &&
            forall|_endpoint_ptr:EndpointPtr| #![auto] old.proc_man.endpoint_ptrs@.contains(_endpoint_ptr) ==> new.proc_man.get_endpoint(_endpoint_ptr) =~= old.proc_man.get_endpoint(_endpoint_ptr)
        }else{
            //if the _syscall is not success, nothing will change, goes back to user level
            old =~= new
        }
    }
    
}

pub closed spec fn _syscall_malloc_spec(old:Kernel, new:Kernel, cpu_id:CPUID, va: usize, perm_bits:usize, range: usize) -> bool
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
            //if the _syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

pub closed spec fn _syscall_register_pci_dev_spec(old:Kernel,new:Kernel,cpu_id:CPUID, bus:u8, dev:u8, fun:u8) -> bool 
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
            //if the _syscall is not success, nothing will change, goes back to user level
            old =~= new
        }
    }
}

pub closed spec fn _syscall_new_thread_spec(old:Kernel,new:Kernel,cpu_id:CPUID, endpoint_index: EndpointIdx, proc:Option<ProcPtr>, new_thread:Option<ThreadPtr>) -> bool 
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        //checking arguments
        let valid_thread = (cpu_id < NUM_CPUS && 
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let valid_endpoint = (endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS && 
            old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int] != 0 &&
            old.proc_man.get_endpoint(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int]).rf_counter != usize::MAX);
        let system_has_memory = old.page_alloc.free_pages.len() >= 1;
        let system_scheduler_has_space = old.proc_man.scheduler.len() != MAX_NUM_THREADS;
        let proc_thread_list_has_space = old.proc_man.proc_perms@[old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent]@.value.get_Some_0().owned_threads.len() < MAX_NUM_THREADS_PER_PROC;

        if valid_thread && valid_endpoint && system_has_memory && system_scheduler_has_space && proc_thread_list_has_space
        {
            (
                //if the _syscall is success, a new process and a new thread of the new process will be created
                proc.is_Some()
                &&
                proc.unwrap() == old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent
                &&
                new_thread.is_Some()
                &&
                //each cpu still runs the same thread, no context switch
                new.cpu_list =~= old.cpu_list
                &&
                // kernel correctly created a new process
                new.proc_man.get_proc_ptrs() =~= old.proc_man.get_proc_ptrs()
                &&
                // kernel correctly created a new thread for that process
                new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs().insert(new_thread.unwrap())
                &&
                // the new thread is scheduled
                new.proc_man.get_thread(new_thread.unwrap()).state == SCHEDULED
                &&
                // the new thread stores the endpoint from the parent process at 1st slot
                new.proc_man.get_thread(new_thread.unwrap()).endpoint_descriptors@[0] =~= new.proc_man.get_thread(new.cpu_list[cpu_id as int].current_t.unwrap()).endpoint_descriptors@[endpoint_index as int]
                &&
                // the new proccess's pagetable is empty. There are kernel and loader mapped in this new pagetable, but they are transparent to user level
                forall|va:VAddr| #![auto] spec_va_valid(va) ==> new.mmu_man.get_pagetable_by_pcid(new.proc_man.get_proc(new.proc_man.get_thread(new_thread.unwrap()).parent).pcid).get_pagetable_mapping()[va].is_None()
                &&
                forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] =~= old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]
                &&
                forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> new.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]
                &&
                forall|proc_ptr:ProcPtr|#![auto] old.proc_man.get_proc_ptrs().contains(proc_ptr) ==> new.proc_man.get_proc(proc_ptr) =~= old.proc_man.get_proc(proc_ptr)
                &&
                forall|thread_ptr:ThreadPtr|#![auto] old.proc_man.get_thread_ptrs().contains(thread_ptr) ==> new.proc_man.get_thread(thread_ptr) =~= old.proc_man.get_thread(thread_ptr)
                &&
                forall|endpoint_ptr:EndpointPtr|#![auto] old.proc_man.get_endpoint_ptrs().contains(endpoint_ptr) ==> new.proc_man.get_endpoint(endpoint_ptr) =~= old.proc_man.get_endpoint(endpoint_ptr)
            )
        }else{
            //if the _syscall is not success, nothing will change, goes back to user level
            old =~= new
        }
    }
    
}


pub closed spec fn _kernel_timer_int_spec(old:Kernel,new:Kernel,cpu_id:CPUID) -> bool 
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        //checking arguments
        let valid_thread = (cpu_id < NUM_CPUS && 
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let scheduler_has_thread = old.proc_man.scheduler.len() != 0;

        if valid_thread && scheduler_has_thread 
        {
            forall|i:CPUID|#![auto] 0 <= i < NUM_CPUS && i != cpu_id ==> new.cpu_list@[i as int] =~= old.cpu_list@[i as int]
            &&
            new.cpu_list@[cpu_id as int].get_current_thread().unwrap() =~= old.proc_man.scheduler@[0]
            &&
            new.proc_man.scheduler@ =~= old.proc_man.scheduler@.subrange(1, old.proc_man.scheduler.len() as int).push(old.cpu_list@[cpu_id as int].get_current_thread().unwrap())
            &&
            new.mmu_man =~= old.mmu_man
            &&
            new.page_alloc =~= old.page_alloc
        }else{
            //if the _syscall is not success, nothing will change, goes back to user level
            old =~= new
        }
    }
}

pub closed spec fn _kernel_idle_pop_sched_spec(old:Kernel,new:Kernel,cpu_id:CPUID) -> bool 
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        //checking arguments
        let cpu_idle = (cpu_id < NUM_CPUS && 
            old.cpu_list@[cpu_id as int].get_is_idle());
        let scheduler_has_thread = old.proc_man.scheduler.len() != 0;

        if cpu_idle && scheduler_has_thread 
        {
            forall|i:CPUID|#![auto] 0 <= i < NUM_CPUS && i != cpu_id ==> new.cpu_list@[i as int] =~= old.cpu_list@[i as int]
            &&
            new.cpu_list@[cpu_id as int].get_current_thread().unwrap() =~= old.proc_man.scheduler@[0]
            &&
            new.proc_man.scheduler@ =~= old.proc_man.scheduler@.subrange(1, old.proc_man.scheduler.len() as int)
            &&
            new.mmu_man =~= old.mmu_man
            &&
            new.page_alloc =~= old.page_alloc
        }else{
            //if the _syscall is not success, nothing will change, goes back to user level
            old =~= new
        }
    }
    
}

}