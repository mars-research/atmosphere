extern crate nvme_driver;
extern crate ring_buffer;
use core::mem::MaybeUninit;
use libtime::rdtsc;
use libtime::sys_ns_loopsleep;
use nvme_driver::device::NvmeDevice;
use nvme_driver::nvme_test::{run_blocktest_blkreq, run_blocktest_raw_with_delay};
use pcid::utils::PciBarAddr;
use crate::ring_buffer::{RingBuffer, SIZE_OF_BUFFER, SIZE_OF_QUEUE};
use nvme_driver::*;
use core::arch::asm;
use crate::DATA_BUFFER_ADDR;
use ring_buffer::*;
use core::arch::x86_64::_rdtsc;
use constants::*;

pub fn test_nvme_driver() {
    unsafe {
        let pml4: u64 = asys::sys_rd_io_cr3() as u64;
        log::info!("IOMMUTable Root @ {:x?}", pml4);
        asys::sys_set_device_iommu(NVME_PCI_DEV.0, NVME_PCI_DEV.1, NVME_PCI_DEV.2, pml4);
    }

    let mut nvme_dev =
        unsafe { NvmeDevice::new(PciBarAddr::new(USERSPACE_BASE + NVME_BAR_BASE, NVME_BAR_SIZE)) };

    log::info!("Initializing Nvme driver...");

    nvme_dev.init();

    log::info!("Running Nvme Read/write tests!");

    run_blocktest_raw_with_delay(&mut nvme_dev, 30, 32, true, false, 0);
    run_blocktest_raw_with_delay(&mut nvme_dev, 30, 32, false, false, 0);

    //run_blocktest_blkreq(&mut nvme_dev);

}

/// | MSG_TYPE | PAYLOAD |
/// MSG_TYPE == STOP
///     quit polling

struct Rand {
    seed: u64,
    pow: u64,
}

impl Rand {
    fn new() -> Rand {
        Rand {
            seed: 123456789,
            pow: 2u64.pow(31),
        }
    }

    #[inline(always)]
    fn get_rand_u64(&mut self) -> u64 {
        self.seed = (1103515245 * self.seed + 12345) % self.pow;
        self.seed
    }
}


// #[no_mangle]
// pub fn test_nvme_with_ring_buffer_ap()-> ! {
//     log::info!("hello from test_nvme_with_ring_buffer_ap");

//     unsafe{
//         let size = core::mem::size_of::<GenericRingBuffer<BlockReq,BlockReq>>();
//         let error_code = asys::sys_receive_pages(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
//         if error_code != 0 {
//             log::info!("sys_receive_pages failed {:?}", error_code);
//         }else{
//             log::info!("data_buffer received by dom1");
//         }   

//         let buff_ref:&mut GenericRingBuffer<BlockReq,BlockReq> = &mut*(DATA_BUFFER_ADDR as *mut GenericRingBuffer<BlockReq,BlockReq>);
//         let mut rng = Rand::new();
//         let iter = 10000000;
//         let print_interval = 1000000;
//         let mut count = 0;
//         let mut print_count = 0;

//         let mut block_num: u64 = 0;
//         let max_block_num = 10 * 1000 * 1000 * 1000 / 512 - 8 ; //10GB

//         let batch_sz = 32;

//         for i in 0..batch_sz {
//             let mut breq = BlockReq::new(block_num, 8, buff_ref.try_pop_allocator().unwrap(), BlockOp::Read);
//             block_num = block_num.wrapping_add(8)%max_block_num;
//             buff_ref.request_queue.try_push(&breq);
//             // log::info!("request @ {:x}", breq.data);
//         }

//         let seq_read_start = _rdtsc();
//         loop{
//             if count >= iter{
//                 break;
//             }
//             if print_count >= print_interval{
//                 log::info!("progress {}%", count as f64 / iter as f64 * 100.0);
//                 print_count = 0;
//             }

//             let mut push_count = 0;
//             let mut pop_count = 0;

//             loop{
//                 if pop_count >= batch_sz{
//                     break;
//                 }
//                 let breq_op = buff_ref.reply_queue.try_pop();
//                 if breq_op.is_none(){
//                     break;
//                 }
//                 pop_count = pop_count + 1;
//                 count = count + 1;
//                 print_count = print_count + 1;
//                 buff_ref.try_push_allocator(breq_op.unwrap().data);
                
//                 // log::info!("reply @ {:x}", breq_op.unwrap().data);

//             }

//             loop{
//                 if push_count >= batch_sz{
//                     break;
//                 }
//                 if buff_ref.request_queue.is_full(){
//                     break;
//                 }

//                 let data_op = buff_ref.try_pop_allocator();

//                 if data_op.is_none(){
//                     break;
//                 }

//                 push_count = push_count + 1;
//                 let mut breq = BlockReq::new(block_num, 8, data_op.unwrap(), BlockOp::Read);
//                 block_num = block_num.wrapping_add(8)%max_block_num;
//                 buff_ref.request_queue.try_push(&breq);
                
//                 // log::info!("request @ {:x}", breq.data);
//             }
//         }
//         let seq_read_end = _rdtsc();


//         let mut count = 0;
//         let mut print_count = 0;

//         let mut block_num: u64 = 0;

//         let seq_write_start = _rdtsc();
//         loop{
//             if count >= iter{
//                 break;
//             }
//             if print_count >= print_interval{
//                 log::info!("progress {}%", count as f64 / iter as f64 * 100.0);
//                 print_count = 0;
//             }

//             let mut push_count = 0;
//             let mut pop_count = 0;

//             loop{
//                 if pop_count >= batch_sz{
//                     break;
//                 }
//                 let breq_op = buff_ref.reply_queue.try_pop();
//                 if breq_op.is_none(){
//                     break;
//                 }
//                 pop_count = pop_count + 1;
//                 count = count + 1;
//                 print_count = print_count + 1;
//                 buff_ref.try_push_allocator(breq_op.unwrap().data);
                
//                 // log::info!("reply @ {:x}", breq_op.unwrap().data);

//             }

//             loop{
//                 if push_count >= batch_sz{
//                     break;
//                 }
//                 if buff_ref.request_queue.is_full(){
//                     break;
//                 }

//                 let data_op = buff_ref.try_pop_allocator();

//                 if data_op.is_none(){
//                     break;
//                 }

//                 push_count = push_count + 1;
//                 let mut breq = BlockReq::new(block_num, 8, data_op.unwrap(), BlockOp::Write);
//                 block_num = block_num.wrapping_add(8)%max_block_num;
//                 buff_ref.request_queue.try_push(&breq);
                
//                 // log::info!("request @ {:x}", breq.data);
//             }
//         }
//         let seq_write_end = _rdtsc();

//         let mut count = 0;
//         let mut print_count = 0;

//         let mut block_num: u64 = 0;

//         let rand_read_start = _rdtsc();
//         loop{
//             if count >= iter{
//                 break;
//             }
//             if print_count >= print_interval{
//                 log::info!("progress {}%", count as f64 / iter as f64 * 100.0);
//                 print_count = 0;
//             }

//             let mut push_count = 0;
//             let mut pop_count = 0;

//             loop{
//                 if pop_count >= batch_sz{
//                     break;
//                 }
//                 let breq_op = buff_ref.reply_queue.try_pop();
//                 if breq_op.is_none(){
//                     break;
//                 }
//                 pop_count = pop_count + 1;
//                 count = count + 1;
//                 print_count = print_count + 1;
//                 buff_ref.try_push_allocator(breq_op.unwrap().data);
                
//                 // log::info!("reply @ {:x}", breq_op.unwrap().data);

//             }

//             loop{
//                 if push_count >= batch_sz{
//                     break;
//                 }
//                 if buff_ref.request_queue.is_full(){
//                     break;
//                 }

//                 let data_op = buff_ref.try_pop_allocator();

//                 if data_op.is_none(){
//                     break;
//                 }

//                 push_count = push_count + 1;
//                 let mut breq = BlockReq::new(block_num, 8, data_op.unwrap(), BlockOp::Read);
//                 block_num = rng.get_rand_u64() % max_block_num;
//                 buff_ref.request_queue.try_push(&breq);
                
//                 // log::info!("request @ {:x}", breq.data);
//             }
//         }
//         let rand_read_end = _rdtsc();

//         let mut count = 0;
//         let mut print_count = 0;

//         let mut block_num: u64 = 0;

//         let rand_write_start = _rdtsc();
//         loop{
//             if count >= iter{
//                 break;
//             }
//             if print_count >= print_interval{
//                 log::info!("progress {}%", count as f64 / iter as f64 * 100.0);
//                 print_count = 0;
//             }

//             let mut push_count = 0;
//             let mut pop_count = 0;

//             loop{
//                 if pop_count >= batch_sz{
//                     break;
//                 }
//                 let breq_op = buff_ref.reply_queue.try_pop();
//                 if breq_op.is_none(){
//                     break;
//                 }
//                 pop_count = pop_count + 1;
//                 count = count + 1;
//                 print_count = print_count + 1;
//                 buff_ref.try_push_allocator(breq_op.unwrap().data);
                
//                 // log::info!("reply @ {:x}", breq_op.unwrap().data);

//             }

//             loop{
//                 if push_count >= batch_sz{
//                     break;
//                 }
//                 if buff_ref.request_queue.is_full(){
//                     break;
//                 }

//                 let data_op = buff_ref.try_pop_allocator();

//                 if data_op.is_none(){
//                     break;
//                 }

//                 push_count = push_count + 1;
//                 let mut breq = BlockReq::new(block_num, 8, data_op.unwrap(), BlockOp::Write);
//                 block_num = rng.get_rand_u64() % max_block_num;
//                 buff_ref.request_queue.try_push(&breq);
                
//                 // log::info!("request @ {:x}", breq.data);
//             }
//         }
//         let rand_write_end = _rdtsc();


//         log::info!("nvme cycles per seq_read {:?} throughput {:}",(seq_read_end - seq_read_start) as usize /iter, iter as u64 /((seq_read_end - seq_read_start)/2_600_000_000_u64));
//         log::info!("nvme cycles per seq_write {:?} throughput {:}",(seq_write_end - seq_write_start) as usize /iter, iter as u64 /((seq_write_end - seq_write_start)/2_600_000_000_u64));
//         log::info!("nvme cycles per rand_read {:?} throughput {:}",(rand_read_end - rand_read_start) as usize /iter, iter as u64 /((rand_read_end - rand_read_start)/2_600_000_000_u64));
//         log::info!("nvme cycles per rand_write {:?} throughput {:}",(rand_write_end - rand_write_start) as usize /iter, iter as u64 /((rand_write_end - rand_write_start)/2_600_000_000_u64));
//     }

//     loop {
//         unsafe{asm!("nop");}
//     }
// }


// pub fn test_nvme_with_ring_buffer(){
//     unsafe {
//         let error_code = asys::sys_new_endpoint(0);
//             if error_code != 0 {
//                 log::info!("sys_new_endpoint failed {:?}", error_code);
//                 return;
//             }
//         let mut range = 0;
//         loop{
//             let (pa,perm) = asys::sys_mresolve(0x8000000000usize + range * 4096);
//             // log::info!("va:{:x?}, pa:{:x?}, perm:{:?}", 0x8000000000usize + range * 4096, pa, perm);
//             if perm == 34{
//                 break;
//             }
//             range = range + 1;
//         }
//         log::info!("find {:?} pages until {:x?}", range, 0x8000000000usize + range * 4096);

//         // log::info!("request_queue address: {:p}", &request_queue);   

//         let size = core::mem::size_of::<GenericRingBuffer<BlockReq,BlockReq>>();
//         let error_code = asys::sys_mmap(DATA_BUFFER_ADDR as usize, 0x0000_0000_0000_0002u64 as usize, size / 4096 + 1);
//         if error_code != 0 {
//             log::info!("sys_mmap for data_buffer failed {:?}", error_code);
//             return;
//         }

//         let error_code = asys::sys_io_mmap(DATA_BUFFER_ADDR as usize, 0x0000_0000_0000_0002u64 as usize, size / 4096 + 1);
//         if error_code != 0 {
//             log::error!("sys_io_mmap for data_buffer failed {:?}", error_code);
//             return;
//         }
        
//         let buff_ref:&mut GenericRingBuffer<BlockReq,BlockReq> = &mut*(DATA_BUFFER_ADDR as *mut GenericRingBuffer<BlockReq,BlockReq>);
//         buff_ref.init();
//         log::info!("data_buffer init done");

//         let new_stack = 0x8000000000usize + range * 4096;
//         log::info!("allocating dom1 stack from {:x?}", new_stack);
//         let stack_size = 16 * 1024 * 1024;
//         let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, stack_size / 4096);
//         if error_code != 0 {
//             log::info!("sys_mmap for dom1 stack failed {:?}", error_code);
//             return;
//         }
//         let error_code = asys::sys_io_mmap(new_stack as usize, 0x0000_0000_0000_0002u64 as usize, stack_size / 4096);
//         if error_code != 0 {
//             log::error!("sys_io_mmap for dom1 stack failed {:?}", error_code);
//             return;
//         }
//         let rsp: usize = new_stack + stack_size/2;
//         log::info!("request_queue address: {:x?}", rsp);  
//         let error_code = asys::sys_new_proc_with_iommu_pass_mem(0,test_nvme_with_ring_buffer_ap as *const () as usize, rsp, 0x8000000000usize, range + stack_size / 4096);
//             if error_code != 0 {
//                 log::info!("sys_new_proc_with_iommu_pass_mem failed {:?}", error_code);
//                 return;
//             }

//         loop{
//             let error_code = asys::sys_send_pages_no_wait(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
//             if error_code == 5  {
//             }else{
//                 if error_code == 0 {
//                     log::info!("data_buffer sent to dom1");
//                     break;
//                 }else{
//                     log::info!("sys_send_pages_no_wait failed {:?}", error_code);
//                     break;
//                 }
//             }
//         }

//         let mut nvme_dev =
//             NvmeDevice::new(PciBarAddr::new(USERSPACE_BASE + 0xfebf_0000, 0x4000));
        
//         log::info!("Initializing Nvme driver...");

//         nvme_dev.init();

//         log::info!("Running Nvme Read/write tests!");

//         loop{
//             nvme_dev.submit_and_poll_breq_with_ringbuffer(&mut buff_ref.request_queue, &mut buff_ref.reply_queue);
//         }

//     }
// }

