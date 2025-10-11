use vstd::prelude::*;
verus! {

use crate::define::*;
use vstd::simple_pptr::PointsTo;
use crate::trap::*;
use crate::array::Array;
use crate::process_manager::endpoint::*;
use crate::process_manager::process::*;
use crate::process_manager::container::*;
use crate::process_manager::thread::*;
use crate::process_manager::cpu::*;
use vstd::simple_pptr::PPtr;
use crate::process_manager::spec_proof::*;
use crate::process_manager::thread_util_t::*;
use crate::process_manager::proc_util_t::*;
use crate::process_manager::container_util_t::*;
use crate::process_manager::endpoint_util_t::*;
use crate::lemma::lemma_u::*;
use crate::lemma::lemma_t::*;
use crate::array_set::ArraySet;
use core::mem::MaybeUninit;
use crate::trap::Registers;
use crate::process_manager::container_tree::*;
use crate::process_manager::process_tree::*;
use crate::quota::*;


        pub open spec fn containers_unchanged(old: ProcessManager, new: ProcessManager) -> bool 
        {
            &&&
            old.container_dom() =~= new.container_dom()
            &&&
            forall|container_ptr: ContainerPtr|
                #![trigger old.get_container(container_ptr)]
                old.container_dom().contains(container_ptr)
                    ==> new.get_container(container_ptr) =~= old.get_container(container_ptr)
        }
        pub open spec fn containers_unchanged_except(old: ProcessManager, new: ProcessManager, changed: Set<ContainerPtr>) -> bool 
        {
            forall|container_ptr: ContainerPtr|
                #![trigger old.get_container(container_ptr)]
                new.container_dom().contains(container_ptr) && !changed.contains(container_ptr)
                    ==> new.get_container(container_ptr) =~= old.get_container(
                    container_ptr,
                )
        }
        pub open spec fn containers_tree_unchanged(old: ProcessManager, new: ProcessManager) -> bool 
        {
            forall|container_ptr: ContainerPtr|
                #![trigger old.get_container(container_ptr)]
                new.container_dom().contains(container_ptr) 
                    ==> 
                    {
                        &&& new.get_container(container_ptr).parent =~= old.get_container(container_ptr).parent
                        &&& new.get_container(container_ptr).children =~= old.get_container(container_ptr).children
                        &&& new.get_container(container_ptr).uppertree_seq =~= old.get_container(container_ptr).uppertree_seq
                        &&& new.get_container(container_ptr).subtree_set =~= old.get_container(container_ptr).subtree_set
                        &&& new.get_container(container_ptr).depth =~= old.get_container(container_ptr).depth
                    }
        }

        pub open spec fn containers_owned_proc_unchanged(old: ProcessManager, new: ProcessManager) -> bool 
        {
            forall|container_ptr: ContainerPtr|
                #![trigger old.get_container(container_ptr)]
                new.container_dom().contains(container_ptr) 
                    ==> 
                    {
                        &&& new.get_container(container_ptr).root_process =~= old.get_container(container_ptr).root_process
                        &&& new.get_container(container_ptr).owned_procs =~= old.get_container(container_ptr).owned_procs
                    }
        }

        pub open spec fn processes_unchanged(old:ProcessManager, new: ProcessManager) -> bool {
            &&&
            old.proc_dom() =~= new.proc_dom()
            &&&
            forall|proc_ptr: ProcPtr|
                #![trigger old.get_proc(proc_ptr)]
                old.proc_dom().contains(proc_ptr)
                    ==> new.get_proc(proc_ptr) =~= old.get_proc(
                    proc_ptr,
                )
        }

        pub open spec fn processes_fields_unchanged(old:ProcessManager, new: ProcessManager) -> bool {
            &&&
            forall|proc_ptr: ProcPtr|
                #![trigger old.get_proc(proc_ptr)]
                new.proc_dom().contains(proc_ptr)
                    ==> 
                    new.get_proc(proc_ptr).pcid =~= old.get_proc(proc_ptr).pcid
                    &&
                    new.get_proc(proc_ptr).ioid =~= old.get_proc(proc_ptr).ioid
                    &&
                    new.get_proc(proc_ptr).owned_threads =~= old.get_proc(proc_ptr).owned_threads
                    &&
                    new.get_proc(proc_ptr).dmd_paging_mode =~= old.get_proc(proc_ptr).dmd_paging_mode
                    &&
                    new.get_proc(proc_ptr).depth =~= old.get_proc(proc_ptr).depth
                    &&
                    new.get_proc(proc_ptr).parent =~= old.get_proc(proc_ptr).parent
        }

        pub open spec fn processes_unchanged_expect(old:ProcessManager, new: ProcessManager, changed: Set<ProcPtr>) -> bool {
            &&&
            forall|proc_ptr: ProcPtr|
                #![trigger old.get_proc(proc_ptr)]
                new.proc_dom().contains(proc_ptr) && changed.contains(proc_ptr) == false
                    ==> new.get_proc(proc_ptr) =~= old.get_proc(
                    proc_ptr,
                )
        }

        pub open spec fn process_tree_unchanged(old: ProcessManager, new: ProcessManager) -> bool 
        {
            forall|p_ptr: ProcPtr|
                #![trigger old.get_proc(p_ptr)]
                new.proc_dom().contains(p_ptr) 
                    ==> 
                    {
                        &&& new.get_proc(p_ptr).parent =~= old.get_proc(p_ptr).parent
                        &&& new.get_proc(p_ptr).children =~= old.get_proc(p_ptr).children
                        &&& new.get_proc(p_ptr).uppertree_seq =~= old.get_proc(p_ptr).uppertree_seq
                        &&& new.get_proc(p_ptr).subtree_set =~= old.get_proc(p_ptr).subtree_set
                        &&& new.get_proc(p_ptr).depth =~= old.get_proc(p_ptr).depth
                    }
        }

        pub open spec fn process_mem_unchanged(old: ProcessManager, new: ProcessManager) -> bool 
        {
            forall|p_ptr: ProcPtr|
                #![trigger old.get_proc(p_ptr)]
                new.proc_dom().contains(p_ptr) 
                    ==> 
                    {
                        &&& new.get_proc(p_ptr).pcid =~= old.get_proc(p_ptr).pcid
                        &&& new.get_proc(p_ptr).ioid =~= old.get_proc(p_ptr).ioid
                    }
        }

        pub open spec fn threads_unchanged(old: ProcessManager, new: ProcessManager) -> bool 
        {
            forall|t_ptr: ThreadPtr|
                #![trigger old.get_thread(t_ptr)]
                new.thread_dom().contains(t_ptr) 
                    ==> new.get_thread(t_ptr) =~= old.get_thread(
                    t_ptr,
                )
        }

        pub open spec fn threads_unchanged_except(old: ProcessManager, new: ProcessManager, changed: Set<ThreadPtr>) -> bool 
        {
            forall|t_ptr: ThreadPtr|
                #![trigger old.get_thread(t_ptr)]
                new.thread_dom().contains(t_ptr) && !changed.contains(t_ptr)
                    ==> new.get_thread(t_ptr) =~= old.get_thread(
                    t_ptr,
                )
        }
        pub open spec fn cpus_unchanged(old:ProcessManager, new: ProcessManager) -> bool {
            &&&
            forall|cpu_id: CpuId|
                #![trigger old.get_cpu(cpu_id)]
                0 <= cpu_id < NUM_CPUS
                    ==> new.get_cpu(cpu_id) =~= old.get_cpu(
                    cpu_id,
                )
        }
    

}