use vstd::prelude::*;
verus! {

// use crate::array_vec::*;
// use crate::proc::*;
// use crate::page_alloc::*;
// use crate::cpu::*;
// use crate::mars_array::MarsArray;
use crate::pagetable::*;
// use crate::cpu::*;
use crate::define::*;
// use crate::trap::*;
use crate::page_alloc::*;

use crate::kernel::*;


pub closed spec fn kernel_page_sharing_spec_helper(kernel: Kernel, sender_pcid:Pcid, receiver_pcid:Pcid, sender_page_start:VAddr, receiver_page_start:VAddr, sender_page_len:usize) -> bool {
    (forall|j:usize| #![auto] 0<=j<sender_page_len ==> spec_va_valid(spec_va_add_range(sender_page_start,j)))
    &&
    (forall|j:usize| #![auto] 0<=j<sender_page_len ==> spec_va_valid(spec_va_add_range(receiver_page_start,j)))
    &&
    (forall|j:usize| #![auto] 0<=j<sender_page_len  ==> kernel.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].is_Some())
    &&
    (forall|j:usize| #![auto] 0<=j<sender_page_len ==>  kernel.page_alloc.page_array@[
        page_ptr2page_index(kernel.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].get_Some_0().addr) as int].rf_count < usize::MAX - sender_page_len)
    &&
    (forall|j:usize| #![auto] 0<=j<sender_page_len ==> kernel.mmu_man.get_pagetable_mapping_by_pcid(receiver_pcid)[spec_va_add_range(receiver_page_start,j)].is_None())

}


impl Kernel {

    pub fn kernel_page_sharing_helper(&self, sender_pcid:Pcid, receiver_pcid:Pcid, perm_bits:usize, sender_page_start:VAddr, receiver_page_start:VAddr, sender_page_len:usize) -> (ret: bool)
        requires
            self.wf(),
            self.page_alloc.free_pages.len() >= 3 * sender_page_len,
            sender_page_len < usize::MAX/3,
            0<=sender_pcid<PCID_MAX,
            0<=receiver_pcid<PCID_MAX,
            self.mmu_man.get_free_pcids_as_set().contains(sender_pcid) == false,
            self.mmu_man.get_free_pcids_as_set().contains(receiver_pcid) == false,
        ensures
            ret == true <==> (
                (forall|j:usize| #![auto] 0<=j<sender_page_len ==> spec_va_valid(spec_va_add_range(sender_page_start,j)))
                &&
                (forall|j:usize| #![auto] 0<=j<sender_page_len ==> spec_va_valid(spec_va_add_range(receiver_page_start,j)))
                &&
                (forall|j:usize| #![auto] 0<=j<sender_page_len  ==> self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].is_Some())
                &&
                (forall|j:usize| #![auto] 0<=j<sender_page_len ==>  self.page_alloc.page_array@[
                    page_ptr2page_index(self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].get_Some_0().addr) as int].rf_count < usize::MAX - sender_page_len)
                &&
                (forall|j:usize| #![auto] 0<=j<sender_page_len ==> self.mmu_man.get_pagetable_mapping_by_pcid(receiver_pcid)[spec_va_add_range(receiver_page_start,j)].is_None())
            ),
            ret == false ==> !(
                (forall|j:usize| #![auto] 0<=j<sender_page_len ==> spec_va_valid(spec_va_add_range(sender_page_start,j)))
                &&
                (forall|j:usize| #![auto] 0<=j<sender_page_len ==> spec_va_valid(spec_va_add_range(receiver_page_start,j)))
                &&
                (forall|j:usize| #![auto] 0<=j<sender_page_len  ==> self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].is_Some())
                &&
                (forall|j:usize| #![auto] 0<=j<sender_page_len ==>  self.page_alloc.page_array@[
                    page_ptr2page_index(self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].get_Some_0().addr) as int].rf_count < usize::MAX - sender_page_len)
                &&
                (forall|j:usize| #![auto] 0<=j<sender_page_len ==> self.mmu_man.get_pagetable_mapping_by_pcid(receiver_pcid)[spec_va_add_range(receiver_page_start,j)].is_None())
            ),

            ret == kernel_page_sharing_spec_helper(*self, sender_pcid, receiver_pcid, sender_page_start, receiver_page_start, sender_page_len),
    {
        let mut i = 0;
        while i != sender_page_len
            invariant
                0<=i<=sender_page_len,
                self.wf(),
                0<=sender_pcid<PCID_MAX,
                0<=receiver_pcid<IOID_MAX,
                self.page_alloc.free_pages.len() >= 3 * sender_page_len,
                forall|j:usize| #![auto] 0<=j<i ==> spec_va_valid(spec_va_add_range(sender_page_start,j)),
                forall|j:usize| #![auto] 0<=j<i ==> spec_va_valid(spec_va_add_range(receiver_page_start,j)),
                self.mmu_man.get_free_pcids_as_set().contains(sender_pcid) == false,
                self.mmu_man.get_free_pcids_as_set().contains(receiver_pcid) == false,
                forall|j:usize| #![auto] 0<=j<i  ==> self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].is_Some(),
                forall|j:usize| #![auto] 0<=j<i ==>  self.page_alloc.page_array@[
                    page_ptr2page_index(self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].get_Some_0().addr) as int].rf_count < usize::MAX - sender_page_len,
                forall|j:usize| #![auto] 0<=j<i ==> self.mmu_man.get_pagetable_mapping_by_pcid(receiver_pcid)[spec_va_add_range(receiver_page_start,j)].is_None(),
            ensures
                i == sender_page_len,
                self.wf(),
                0<=sender_pcid<PCID_MAX,
                0<=receiver_pcid<IOID_MAX,
                forall|j:usize| #![auto] 0<=j<sender_page_len ==> spec_va_valid(spec_va_add_range(sender_page_start,j)),
                forall|j:usize| #![auto] 0<=j<sender_page_len ==> spec_va_valid(spec_va_add_range(receiver_page_start,j)),
                self.page_alloc.free_pages.len() >= 3 * sender_page_len,
                self.mmu_man.get_free_pcids_as_set().contains(sender_pcid) == false,
                self.mmu_man.get_free_pcids_as_set().contains(receiver_pcid) == false,
                forall|j:usize| #![auto] 0<=j<i  ==> self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].is_Some(),
                forall|j:usize| #![auto] 0<=j<i ==>  self.page_alloc.page_array@[
                    page_ptr2page_index(self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].get_Some_0().addr) as int].rf_count < usize::MAX - sender_page_len,
                forall|j:usize| #![auto] 0<=j<i ==> self.mmu_man.get_pagetable_mapping_by_pcid(receiver_pcid)[spec_va_add_range(receiver_page_start,j)].is_None(),
        {
            if va_valid(va_add_range(sender_page_start,i)) == false {
                return false;
            }

            if va_valid(va_add_range(receiver_page_start,i)) == false {
                return false;
            }

            if self.mmu_man.mmu_get_va_entry_by_pcid(receiver_pcid,va_add_range(receiver_page_start,i)).is_some()
            {
                return false;
            }

            let page_entry = self.mmu_man.mmu_get_va_entry_by_pcid(sender_pcid,va_add_range(sender_page_start,i));

            if page_entry.is_none(){
                return false;
            }

            if self.page_alloc.get_page_rf_counter_by_page_ptr(page_entry.unwrap().addr) >= usize::MAX - sender_page_len {
                return false;
            }
            i = i + 1;
        }
        return true;
    }

        pub fn kernel_page_sharing_helper_2(&self, sender_pcid:Pcid, perm_bits:usize, sender_page_start:VAddr, sender_page_len:usize) -> (ret: bool)
        requires
            self.wf(),
            self.page_alloc.free_pages.len() >= 3 * sender_page_len,
            sender_page_len < usize::MAX/3,
            0<=sender_pcid<PCID_MAX,
            self.mmu_man.get_free_pcids_as_set().contains(sender_pcid) == false,
        ensures
            ret == true <==> (
                (forall|j:usize| #![auto] 0<=j<sender_page_len ==> spec_va_valid(spec_va_add_range(sender_page_start,j)))
                &&
                (forall|j:usize| #![auto] 0<=j<sender_page_len  ==> self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].is_Some())
                &&
                (forall|j:usize| #![auto] 0<=j<sender_page_len ==>  self.page_alloc.page_array@[
                    page_ptr2page_index(self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].get_Some_0().addr) as int].rf_count < usize::MAX - sender_page_len)
            ),
            ret == false ==> !(
                (forall|j:usize| #![auto] 0<=j<sender_page_len ==> spec_va_valid(spec_va_add_range(sender_page_start,j)))
                &&
                (forall|j:usize| #![auto] 0<=j<sender_page_len  ==> self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].is_Some())
                &&
                (forall|j:usize| #![auto] 0<=j<sender_page_len ==>  self.page_alloc.page_array@[
                    page_ptr2page_index(self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].get_Some_0().addr) as int].rf_count < usize::MAX - sender_page_len)
            ),
    {
        let mut i = 0;
        while i != sender_page_len
            invariant
                0<=i<=sender_page_len,
                self.wf(),
                0<=sender_pcid<PCID_MAX,
                self.page_alloc.free_pages.len() >= 3 * sender_page_len,
                forall|j:usize| #![auto] 0<=j<i ==> spec_va_valid(spec_va_add_range(sender_page_start,j)),
                self.mmu_man.get_free_pcids_as_set().contains(sender_pcid) == false,
                forall|j:usize| #![auto] 0<=j<i  ==> self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].is_Some(),
                forall|j:usize| #![auto] 0<=j<i ==>  self.page_alloc.page_array@[
                    page_ptr2page_index(self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].get_Some_0().addr) as int].rf_count < usize::MAX - sender_page_len,
            ensures
                i == sender_page_len,
                self.wf(),
                0<=sender_pcid<PCID_MAX,
                forall|j:usize| #![auto] 0<=j<sender_page_len ==> spec_va_valid(spec_va_add_range(sender_page_start,j)),
                self.page_alloc.free_pages.len() >= 3 * sender_page_len,
                self.mmu_man.get_free_pcids_as_set().contains(sender_pcid) == false,
                forall|j:usize| #![auto] 0<=j<i  ==> self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].is_Some(),
                forall|j:usize| #![auto] 0<=j<i ==>  self.page_alloc.page_array@[
                    page_ptr2page_index(self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].get_Some_0().addr) as int].rf_count < usize::MAX - sender_page_len,
        {
            if va_valid(va_add_range(sender_page_start,i)) == false {
                return false;
            }

            let page_entry = self.mmu_man.mmu_get_va_entry_by_pcid(sender_pcid,va_add_range(sender_page_start,i));

            if page_entry.is_none(){
                return false;
            }

            if self.page_alloc.get_page_rf_counter_by_page_ptr(page_entry.unwrap().addr) >= usize::MAX - sender_page_len {
                return false;
            }
            i = i + 1;
        }
        return true;
    }

    pub fn kernel_ipc_copy_pages(&mut self, sender_ptr: ThreadPtr, receiver_ptr: ThreadPtr) -> (ret:ErrorCodeType)
        requires
            old(self).wf(),
            old(self).proc_man.get_thread_ptrs().contains(sender_ptr),
            old(self).proc_man.get_thread_ptrs().contains(receiver_ptr),
        ensures
            self.wf(),
        {
            let sender_page_op = self.proc_man.get_thread_page_payload(sender_ptr);
            if sender_page_op.is_none(){
                return PAGE_PAYLOAD_INVALID;
            }
            let receiver_page_op = self.proc_man.get_thread_page_payload(sender_ptr);
            if receiver_page_op.is_none(){
                return PAGE_PAYLOAD_INVALID;
            }

            let (sender_page_start,sender_page_len) = sender_page_op.unwrap();
            let (receiver_page_start,receiver_page_len) = receiver_page_op.unwrap();

            if sender_page_len != receiver_page_len{
                return PAGE_PAYLOAD_INVALID;
            }

            let sender_pcid = self.proc_man.get_pcid_by_thread_ptr(sender_ptr);
            let receiver_pcid = self.proc_man.get_pcid_by_thread_ptr(receiver_ptr);

            let perm_bits = 0x3 as usize;

            if sender_page_len >= usize::MAX/3{
                return PAGE_PAYLOAD_INVALID;
            }

            if ! va_perm_bits_valid(perm_bits) {
                return PAGE_PAYLOAD_INVALID;
            }

            if  self.page_alloc.free_pages.len() < 3 * sender_page_len {
                return PAGE_PAYLOAD_INVALID;
            }

            let mut i = 0;
            while i != sender_page_len
                invariant
                    0<=i<=sender_page_len,
                    self == old(self),
                    self.wf(),
                    0<=sender_pcid<PCID_MAX,
                    0<=receiver_pcid<IOID_MAX,
                    spec_va_perm_bits_valid(perm_bits),
                    self.page_alloc.free_pages.len() >= 3 * sender_page_len,
                    forall|j:usize| #![auto] 0<=j<i ==> spec_va_valid(spec_va_add_range(sender_page_start,j)),
                    forall|j:usize| #![auto] 0<=j<i ==> spec_va_valid(spec_va_add_range(receiver_page_start,j)),
                    self.mmu_man.get_free_pcids_as_set().contains(sender_pcid) == false,
                    self.mmu_man.get_free_pcids_as_set().contains(receiver_pcid) == false,
                    forall|j:usize| #![auto] 0<=j<i  ==> self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].is_Some(),
                    forall|j:usize| #![auto] 0<=j<i ==>  self.page_alloc.page_array@[
                        page_ptr2page_index(self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].get_Some_0().addr) as int].rf_count < usize::MAX - sender_page_len,
                    forall|j:usize| #![auto] 0<=j<i ==> old(self).mmu_man.get_pagetable_mapping_by_pcid(receiver_pcid)[spec_va_add_range(receiver_page_start,j)].is_None(),
                ensures
                    i == sender_page_len,
                    self == old(self),
                    self.wf(),
                    0<=sender_pcid<PCID_MAX,
                    0<=receiver_pcid<IOID_MAX,
                    spec_va_perm_bits_valid(perm_bits),
                    forall|j:usize| #![auto] 0<=j<sender_page_len ==> spec_va_valid(spec_va_add_range(sender_page_start,j)),
                    forall|j:usize| #![auto] 0<=j<sender_page_len ==> spec_va_valid(spec_va_add_range(receiver_page_start,j)),
                    self.page_alloc.free_pages.len() >= 3 * sender_page_len,
                    self.mmu_man.get_free_pcids_as_set().contains(sender_pcid) == false,
                    self.mmu_man.get_free_pcids_as_set().contains(receiver_pcid) == false,
                    forall|j:usize| #![auto] 0<=j<i  ==> self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].is_Some(),
                    forall|j:usize| #![auto] 0<=j<i ==>  self.page_alloc.page_array@[
                        page_ptr2page_index(self.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[spec_va_add_range(sender_page_start,j)].get_Some_0().addr) as int].rf_count < usize::MAX - sender_page_len,
                    forall|j:usize| #![auto] 0<=j<i ==> old(self).mmu_man.get_pagetable_mapping_by_pcid(receiver_pcid)[spec_va_add_range(receiver_page_start,j)].is_None(),
            {
                if va_valid(va_add_range(sender_page_start,i)) == false {
                    return PAGE_PAYLOAD_INVALID;
                }

                if va_valid(va_add_range(receiver_page_start,i)) == false {
                    return PAGE_PAYLOAD_INVALID;
                }

                if self.mmu_man.mmu_get_va_entry_by_pcid(receiver_pcid,va_add_range(receiver_page_start,i)).is_some()
                {
                    return PAGE_PAYLOAD_INVALID;
                }

                let page_entry = self.mmu_man.mmu_get_va_entry_by_pcid(sender_pcid,va_add_range(sender_page_start,i));

                if page_entry.is_none(){
                    return PAGE_PAYLOAD_INVALID;
                }

                if self.page_alloc.get_page_rf_counter_by_page_ptr(page_entry.unwrap().addr) >= usize::MAX - sender_page_len {
                    return PAGE_PAYLOAD_INVALID;
                }
            }
            self.kernel_map_pagetable_range_page_to_pagetable(sender_pcid, receiver_pcid, sender_page_start, receiver_page_start, perm_bits,sender_page_len);

            assert(self.wf());
            return SUCCESS;

        }

    pub fn kernel_ipc_copy_messages(&self, sender_ptr: ThreadPtr, receiver_ptr: ThreadPtr) -> (ret:ErrorCodeType)
        requires
            self.wf(),
            self.proc_man.get_thread_ptrs().contains(sender_ptr),
            self.proc_man.get_thread_ptrs().contains(receiver_ptr),
    {
        let sender_message_op = self.proc_man.get_thread_message_payload(sender_ptr);
        if sender_message_op.is_none(){
            return MESSAGE_INVALID;
        }
        let receiver_message_op = self.proc_man.get_thread_message_payload(sender_ptr);
        if receiver_message_op.is_none(){
            return MESSAGE_INVALID;
        }
        let (sender_message_ptr,sender_message_len) = sender_message_op.unwrap();
        let (receiver_message_ptr,receiver_message_len) = receiver_message_op.unwrap();
        if sender_message_len == 0 || sender_message_len > 4096{
            return MESSAGE_INVALID;
        }
        if receiver_message_len == 0 || receiver_message_len > 4096{
            return MESSAGE_INVALID;
        }

        if receiver_message_len != sender_message_len {
            return MESSAGE_INVALID;
        }

        let sender_pcid = self.proc_man.get_pcid_by_thread_ptr(sender_ptr);
        let receiver_pcid = self.proc_man.get_pcid_by_thread_ptr(receiver_ptr);

        if !va_valid(sender_message_ptr) {
            return MESSAGE_INVALID;
        }
        if !va_valid(receiver_message_ptr) {
            return MESSAGE_INVALID;
        }

        let sender_message_pa_op = self.mmu_man.mmu_get_va_entry_by_pcid(sender_pcid, sender_message_ptr);
        let receiver_message_pa_op = self.mmu_man.mmu_get_va_entry_by_pcid(receiver_pcid, receiver_message_ptr);

        if sender_message_pa_op.is_none() {
            return MESSAGE_INVALID;
        }
        if receiver_message_pa_op.is_none() {
            return MESSAGE_INVALID;
        }

        let sender_message_pa = sender_message_pa_op.unwrap().addr;
        let receiver_message_pa = receiver_message_pa_op.unwrap().addr;

        if sender_message_pa == receiver_message_pa {
            return MESSAGE_INVALID;
        }
        self.kernel_pass_message(sender_message_pa,receiver_message_pa, sender_message_len);

        return SUCCESS;

    }

    #[verifier(external_body)]
    pub fn kernel_pass_message(&self, sender_message_pa:PAddr, receiver_message_pa:PAddr, len:usize)
        requires
            self.wf(),
            page_ptr_valid(sender_message_pa),
            page_ptr_valid(receiver_message_pa),
            sender_message_pa != receiver_message_pa,
            0<len<=4096,
    {
        unsafe{
            let dst_ptr = receiver_message_pa as *mut u8;
            let src_ptr = sender_message_pa as *const u8;
            core::ptr::copy_nonoverlapping(src_ptr, dst_ptr, len);
        }
    }

}
}
