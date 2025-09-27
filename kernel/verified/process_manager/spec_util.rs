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
use crate::process_manager::spec_impl::*;
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
                old.container_dom().contains(container_ptr) && !changed.contains(container_ptr)
                    ==> new.get_container(container_ptr) =~= old.get_container(
                    container_ptr,
                )
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