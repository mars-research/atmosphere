use vstd::prelude::*;
verus! {
use crate::kernel::*;
use crate::define::*;
use crate::va_range::VaRange4K;
use crate::lemma::lemma_u::*;
use crate::lemma::lemma_t::*;

    pub struct ContainerGroup{
        pub v_c_ptr: ContainerPtr,
        pub v_p_ptr: ProcPtr,
        pub v_t_ptr: ThreadPtr,

        pub a_c_ptr: ContainerPtr,
        pub b_c_ptr: ContainerPtr,
    }
    pub struct IsolationStateMachine{
        pub kernel_state: Ghost<Kernel>,

        pub containers: ContainerGroup
        // pub v_private_va: Ghost<Seq<VAddr>>,
        // pub v_private_pa: Ghost<Seq<VAddr>>,
        // pub v_a_shared_va: Ghost<Seq<VAddr>>,
        // pub v_b_shared_va: Ghost<Seq<VAddr>>,
        // pub v_a_shared_pa: Ghost<Seq<PAddr>>,
        // pub v_b_shared_pa: Ghost<Seq<PAddr>>,
        
    }

    impl IsolationStateMachine{
        pub open spec fn v_container_inv(&self) -> bool{
            &&&
            self.kernel_state@.container_dom().contains(self.containers.v_c_ptr)
            &&&
            self.kernel_state@.get_container(self.containers.v_c_ptr).owned_procs@ =~= Seq::<ProcPtr>::empty().push(self.containers.v_p_ptr)
            &&&
            self.kernel_state@.get_container(self.containers.v_c_ptr).owned_threads@ =~= Set::<ThreadPtr>::empty().insert(self.containers.v_t_ptr)
            &&&
            self.kernel_state@.get_proc(self.containers.v_p_ptr).owned_threads@ =~= Seq::<ThreadPtr>::empty().push(self.containers.v_t_ptr)
            &&&
            self.kernel_state@.get_thread(self.containers.v_t_ptr).owning_container == self.containers.v_c_ptr
            &&&
            self.kernel_state@.get_thread(self.containers.v_t_ptr).owning_proc == self.containers.v_p_ptr
            &&&
            self.kernel_state@.get_proc(self.containers.v_p_ptr).owning_container == self.containers.v_c_ptr
        }

        pub open spec fn v_address_space_inv(&self) -> bool {
            &&&
            forall|v_va_i:VAddr, v_va_j:VAddr|
            #![auto]
                self.kernel_state@.get_address_space(self.containers.v_p_ptr).dom().contains(v_va_i)
                &&
                self.kernel_state@.get_address_space(self.containers.v_p_ptr).dom().contains(v_va_j)
                &&
                v_va_i != v_va_j
                ==>
                self.kernel_state@.get_address_space(self.containers.v_p_ptr)[v_va_i].addr != self.kernel_state@.get_address_space(self.containers.v_p_ptr)[v_va_j].addr
        }

        pub open spec fn a_b_container_inv(&self) -> bool{
            &&&
            self.containers.a_c_ptr != self.containers.b_c_ptr
            &&&
            self.kernel_state@.container_dom().contains(self.containers.a_c_ptr)
            &&&
            self.kernel_state@.container_dom().contains(self.containers.b_c_ptr)
        }

        //major isolation invariant
        pub open spec fn memory_inv(&self) -> bool{
            &&&
            forall|a_sub_c_ptr:ContainerPtr, a_p_ptr: ProcPtr, b_p_ptr: ProcPtr, b_sub_c_ptr:ContainerPtr, a_va:VAddr, b_va:VAddr|
            #![trigger 
                self.kernel_state@.get_container(a_sub_c_ptr), 
                self.kernel_state@.get_container(b_sub_c_ptr),
                self.kernel_state@.get_address_space(a_p_ptr),
                self.kernel_state@.get_address_space(b_p_ptr),
                self.kernel_state@.get_address_space(a_p_ptr)[a_va],
                self.kernel_state@.get_address_space(b_p_ptr)[b_va],
            ]
                (
                    self.kernel_state@.get_container(self.containers.a_c_ptr).subtree_set@.contains(a_sub_c_ptr)
                    || 
                    a_sub_c_ptr == self.containers.a_c_ptr
                )
                &&
                (
                    self.kernel_state@.get_container(self.containers.b_c_ptr).subtree_set@.contains(b_sub_c_ptr)
                    ||
                    b_sub_c_ptr == self.containers.b_c_ptr
                )
                &&
                self.kernel_state@.get_container(a_sub_c_ptr).owned_procs@.contains(a_p_ptr)
                &&
                self.kernel_state@.get_container(b_sub_c_ptr).owned_procs@.contains(b_p_ptr)
                &&
                self.kernel_state@.get_address_space(a_p_ptr).dom().contains(a_va)
                &&
                self.kernel_state@.get_address_space(b_p_ptr).dom().contains(b_va)
                ==>
                self.kernel_state@.get_address_space(a_p_ptr)[a_va].addr != self.kernel_state@.get_address_space(b_p_ptr)[b_va].addr
        }

        pub open spec fn endpoint_inv(&self) -> bool{
            &&&
            forall|a_sub_c_ptr:ContainerPtr, a_t_ptr: ThreadPtr, a_index:int,  b_sub_c_ptr:ContainerPtr, b_t_ptr: ThreadPtr, b_index:int|
            #![trigger 
                self.kernel_state@.get_container(a_sub_c_ptr).owned_threads, 
                self.kernel_state@.get_container(b_sub_c_ptr).owned_threads,
                self.kernel_state@.get_thread(a_t_ptr),
                self.kernel_state@.get_thread(b_t_ptr),
                self.kernel_state@.get_thread(a_t_ptr).endpoint_descriptors@[a_index],
                self.kernel_state@.get_thread(b_t_ptr).endpoint_descriptors@[b_index],
            ]
                (
                    self.kernel_state@.get_container(self.containers.a_c_ptr).subtree_set@.contains(a_sub_c_ptr)
                    || 
                    a_sub_c_ptr == self.containers.a_c_ptr
                )
                &&
                (
                    self.kernel_state@.get_container(self.containers.b_c_ptr).subtree_set@.contains(b_sub_c_ptr)
                    ||
                    b_sub_c_ptr == self.containers.b_c_ptr
                )
                &&
                self.kernel_state@.get_container(a_sub_c_ptr).owned_threads@.contains(a_t_ptr)
                &&
                self.kernel_state@.get_container(b_sub_c_ptr).owned_threads@.contains(b_t_ptr)
                &&
                0 <= a_index < MAX_NUM_ENDPOINT_DESCRIPTORS
                &&
                0 <= b_index < MAX_NUM_ENDPOINT_DESCRIPTORS
                &&
                self.kernel_state@.get_thread(a_t_ptr).endpoint_descriptors@[a_index].is_Some()
                &&
                self.kernel_state@.get_thread(b_t_ptr).endpoint_descriptors@[b_index].is_Some()
                ==>
                self.kernel_state@.get_thread(a_t_ptr).endpoint_descriptors@[a_index].unwrap() != self.kernel_state@.get_thread(b_t_ptr).endpoint_descriptors@[b_index].unwrap()
            &&&
            forall|sub_c_ptr:ContainerPtr, t_ptr: ThreadPtr, index:int, outside_c_ptr:ContainerPtr, outside_t_ptr: ThreadPtr, outside_index:int|
            #![trigger 
                self.kernel_state@.get_container(sub_c_ptr),
                self.kernel_state@.get_container(outside_c_ptr),
                self.kernel_state@.get_thread(t_ptr),
                self.kernel_state@.get_thread(outside_t_ptr),
                self.kernel_state@.get_thread(t_ptr).endpoint_descriptors@[index],
                self.kernel_state@.get_thread(outside_t_ptr).endpoint_descriptors@[outside_index]
                ]
                (
                    self.kernel_state@.get_container(self.containers.a_c_ptr).subtree_set@.contains(sub_c_ptr)
                    || 
                    sub_c_ptr == self.containers.a_c_ptr
                    || 
                    self.kernel_state@.get_container(self.containers.b_c_ptr).subtree_set@.contains(sub_c_ptr)
                    ||
                    sub_c_ptr == self.containers.b_c_ptr
                )
                &&
                self.kernel_state@.get_container(sub_c_ptr).owned_threads@.contains(t_ptr)
                &&
                self.kernel_state@.container_dom().contains(outside_c_ptr)
                &&
                self.kernel_state@.get_container(self.containers.a_c_ptr).subtree_set@.contains(outside_c_ptr) == false
                &&
                outside_c_ptr != self.containers.a_c_ptr
                && 
                self.kernel_state@.get_container(self.containers.b_c_ptr).subtree_set@.contains(outside_c_ptr) == false
                &&
                outside_c_ptr != self.containers.b_c_ptr
                &&
                self.kernel_state@.get_container(outside_c_ptr).owned_threads@.contains(outside_t_ptr)
                &&
                0 <= index < MAX_NUM_ENDPOINT_DESCRIPTORS
                &&
                0 <= outside_index < MAX_NUM_ENDPOINT_DESCRIPTORS
                &&
                self.kernel_state@.get_thread(t_ptr).endpoint_descriptors@[index].is_Some()
                &&
                self.kernel_state@.get_thread(outside_t_ptr).endpoint_descriptors@[outside_index].is_Some()
                ==>
                self.kernel_state@.get_thread(t_ptr).endpoint_descriptors@[index].unwrap() != self.kernel_state@.get_thread(outside_t_ptr).endpoint_descriptors@[outside_index].unwrap()
        }

        pub open spec fn v_endpoint_inv(&self) -> bool{
            &&&
            self.kernel_state@.get_thread(self.containers.v_t_ptr).endpoint_descriptors@[0].is_Some()
            &&&
            self.kernel_state@.get_thread(self.containers.v_t_ptr).endpoint_descriptors@[1].is_Some()
            &&&
            self.kernel_state@.get_thread(self.containers.v_t_ptr).endpoint_descriptors@[0].unwrap() != self.kernel_state@.get_thread(self.containers.v_t_ptr).endpoint_descriptors@[1].unwrap()
            &&&
            (
                self.kernel_state@.get_thread(self.containers.v_t_ptr).state == ThreadState::BLOCKED 
                ==> 
                self.kernel_state@.get_endpoint(self.kernel_state@.get_thread(self.containers.v_t_ptr).blocking_endpoint_ptr.unwrap()).queue_state == EndpointState::RECEIVE
            )
            &&&
            forall|i:int|
                2 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS
                ==>
                self.kernel_state@.get_thread(self.containers.v_t_ptr).endpoint_descriptors@[i].is_None()
        }

        pub open spec fn inv(&self) -> bool{
            &&&
            self.v_container_inv()
            &&&
            self.v_address_space_inv()
            &&&
            self.a_b_container_inv()
            &&&
            self.memory_inv()
            &&&
            self.endpoint_inv()
            &&&
            self.v_endpoint_inv()

        }
    }



    impl IsolationStateMachine{
        pub open spec fn v_step_receive_page(&self, blocking_endpoint_index: EndpointIdx, va_range:VaRange4K) -> bool{
            &&&
            blocking_endpoint_index == 0 || blocking_endpoint_index == 1
            // &&&
            // forall|va:VAddr| 
            //     #![auto] 
            //     va_range@.contains(va) 
            //     ==>
            //     self.v_private_va@.contains(va) == false
            //     &&
            //     self.v_a_shared_va@.contains(va) == false
            //     &&
            //     self.v_b_shared_va@.contains(va) == false
        }

        pub open spec fn v_step_receive_endpoint(&self) -> bool{
            false
        }

        pub open spec fn v_step_send_endpoint(&self) -> bool{
            false
        }

        pub open spec fn v_step_send_pages(&self) -> bool{
            false
        }

        pub open spec fn v_step_mmap(&self) -> bool{
            false
        }

        pub open spec fn v_step_new_thread_with_endpoint(&self, thread_ptr:ThreadPtr, endpoint_index: EndpointIdx) -> bool{
            if self.containers.v_t_ptr == thread_ptr{
                false
            }else{
                true
            }
        }
    }

    impl IsolationStateMachine{
        pub proof fn new_thread_preserve_inv(old: IsolationStateMachine, new: IsolationStateMachine, thread_ptr:ThreadPtr, endpoint_index: EndpointIdx, ret: SyscallReturnStruct)
            requires
                old.kernel_state@.thread_dom().contains(thread_ptr),
                0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
                old.kernel_state@.wf(),
                new.kernel_state@.wf(),
                syscall_new_thread_with_endpoint_spec(old.kernel_state@, new.kernel_state@, thread_ptr, endpoint_index, ret),
                old.containers =~= new.containers,
                old.v_step_new_thread_with_endpoint(thread_ptr, endpoint_index),
                old.inv(),
            ensures
                new.inv(),
        {
            let target_proc_ptr = old.kernel_state@.get_thread(thread_ptr).owning_proc;
            let target_container_ptr = old.kernel_state@.get_thread(thread_ptr).owning_container;

            old.kernel_state@.container_thread_inv_1();
            old.kernel_state@.proc_thread_inv_1();
            old.kernel_state@.container_inv();
            old.kernel_state@.thread_inv();
            old.kernel_state@.container_subtree_inv();
            new.kernel_state@.container_thread_inv_1();
            new.kernel_state@.proc_thread_inv_1();
            new.kernel_state@.container_inv();
            new.kernel_state@.thread_inv();
            new.kernel_state@.container_subtree_inv();
            seq_push_lemma::<ProcPtr>();
            set_insert_lemma::<ThreadPtr>();
            assert(old.kernel_state@.get_container(old.containers.v_c_ptr).owned_procs@.contains(old.containers.v_p_ptr));
            assert(old.kernel_state@.get_container(old.containers.v_c_ptr).owned_threads@.contains(old.containers.v_t_ptr));
            assert(old.kernel_state@.get_container(old.containers.v_c_ptr).owned_threads@.contains(thread_ptr) == false);
            assert(old.kernel_state@.get_proc(old.containers.v_p_ptr).owned_threads@.contains(thread_ptr) == false);
            assert(thread_ptr != old.containers.v_t_ptr);
            assert(target_proc_ptr != old.containers.v_p_ptr);
            assert(target_container_ptr != old.containers.v_c_ptr);


            if syscall_new_thread_with_endpoint_requirement(old.kernel_state@, thread_ptr, endpoint_index) == false {
                assert(new.kernel_state@ =~= old.kernel_state@);
                assert(new.inv());
            }else{
                let target_endpoint_ptr = old.kernel_state@.get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap();
                let new_thread_ptr = ret.get_return_vaule_usize().unwrap();
                assert(new.kernel_state@.thread_dom().contains(new.containers.v_t_ptr));
                assert(ret.get_return_vaule_usize().is_Some());
                assert(new.v_container_inv());
                assert(new.v_address_space_inv());
                assert(new.a_b_container_inv());
                assert(new.memory_inv());
                assert(new.endpoint_inv());
                assert(new.v_endpoint_inv());
                assert(new.inv());
            }
        }

    }
}