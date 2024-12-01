use vstd::prelude::*;
verus! {
use crate::kernel::Kernel;
use crate::define::*;
    pub struct IsolationStateMachine{
        pub kernel_state: Ghost<Kernel>,

        pub v_c_ptr: ContainerPtr,
        pub v_p_ptr: ProcPtr,
        pub v_t_ptr: ThreadPtr,
        pub v_a_shared_va: Ghost<Seq<VAddr>>,
        pub v_v_shared_va: Ghost<Seq<VAddr>>,
        pub v_a_shared_pa: Ghost<Seq<PAddr>>,
        pub v_v_shared_pa: Ghost<Seq<PAddr>>,
        
        pub a_c_ptr: ContainerPtr,
        pub b_c_ptr: ContainerPtr,
    }

    impl IsolationStateMachine{
        pub open spec fn v_container_inv(&self) -> bool{
            &&&
            self.kernel_state@.container_dom().contains(self.v_c_ptr)
            &&&
            self.kernel_state@.get_container(self.v_c_ptr).owned_procs@ =~= seq![self.v_p_ptr]
            &&&
            self.kernel_state@.get_container(self.v_c_ptr).owned_threads@ =~= set![self.v_t_ptr]
        }

        pub open spec fn v_address_space_inv(&self) -> bool {
            &&&
            forall|v_va_i:Vaddr, v_va_j:VAddr|
                self.kernel_state@.get_address_space(v_p_ptr).dom().contains(v_va_i)
                &&
                self.kernel_state@.get_address_space(v_p_ptr).dom().contains(v_va_j)
                &&
                v_va_i != v_va_j
                ==>
                self.kernel_state@.get_address_space(v_p_ptr)[v_va_i].addr != self.kernel_state@.get_address_space(v_p_ptr)[v_va_j].addr
        }

        pub open spec fn shared_memory_inv(&self) -> bool{
            &&&
            self.v_a_shared_va@.len() == self.v_a_shared_pa@.len()
            &&&
            self.v_b_shared_va@.len() == self.v_b_shared_pa@.len()
            &&&
            forall|i:int|
                0 <= i < self.v_a_shared_va@.len()
                ==>
                self.get_address_space(v_p_ptr).dom().contains(self.v_a_shared_va@[i])
                &&
                self.get_address_space(v_p_ptr)[i].addr == self.v_a_shared_pa@[i]
            &&&
            forall|i:int|
                0 <= i < self.v_b_shared_va@.len()
                ==>
                self.get_address_space(v_p_ptr).dom().contains(self.v_b_shared_va@[i])
                &&
                self.get_address_space(v_p_ptr)[i].addr == self.v_b_shared_pa@[i]
        }

        pub open spec fn a_b_container_inv(&self) -> bool{
            &&&
            self.kernel_state@.container_dom().contains(self.a_c_ptr)
            &&&
            self.kernel_state@.container_dom().contains(self.b_c_ptr)
        }

        //major isolation invariant
        pub open spec fn memory_inv(&self) -> bool{
            &&&
            forall|a_p_ptr: ProcPtr, b_p_ptr: ProcPtr, a_va:Vaddr, b_va:VAddr|
                self.kernel_state@.get_container(self.a_c_ptr).owned_procs@.contains(a_p_ptr)
                &&
                self.kernel_state@.get_container(self.b_c_ptr).owned_procs@.contains(b_p_ptr)
                &&
                self.kernel_state@.get_address_space(a_p_ptr).dom().contains(a_va)
                &&
                self.kernel_state@.get_address_space(b_p_ptr).dom().contains(b_va)
                ==>
                self.kernel_state@.get_address_space(a_p_ptr)[a_va].addr != self.kernel_state@.get_address_space(b_p_ptr)[b_va].addr
        }

        pub open spec fn endpoint_inv(&self) -> bool{
            &&&
            forall|a_t_ptr: ThreadPtr, a_index:int, t_ptr:ThreadPtr|
                self.kernel_state@.get_container(self.a_c_ptr).owned_threads@.contains(a_t_ptr)
                &&
                0 <= a_index < MAX_NUM_ENDPOINT_DESCRIPTORS
                &&
                self.kernel_state@.get_thread(a_t_ptr).endpoint_descriptors@[a_index].is_Some()
                &&
                self.kernel_state@.get_endpoint(self.kernel_state@.get_thread(a_t_ptr).endpoint_descriptors@[a_index].unwrap()).owned_threads.contains(t_ptr)
                ==>
                (
                    t_ptr == self.v_t_ptr
                    ||
                    self.kernel_state@.get_container(self.a_c_ptr).owned_threads@.contains(t_ptr)
                )
            &&&
            forall|b_t_ptr: ThreadPtr, b_index:int, t_ptr:ThreadPtr|
                self.kernel_state@.get_container(self.b_c_ptr).owned_threads@.contains(b_t_ptr)
                &&
                0 <= a_index < MAX_NUM_ENDPOINT_DESCRIPTORS
                &&
                self.kernel_state@.get_thread(b_t_ptr).endpoint_descriptors@[b_index].is_Some()
                &&
                self.kernel_state@.get_endpoint(self.kernel_state@.get_thread(b_t_ptr).endpoint_descriptors@[b_index].unwrap()).owned_threads.contains(t_ptr)
                ==>
                (
                    t_ptr == self.v_t_ptr
                    ||
                    self.kernel_state@.get_container(self.b_c_ptr).owned_threads@.contains(t_ptr)
                )
        }
    }
}