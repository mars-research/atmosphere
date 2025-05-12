use crate::USERSPACE_BASE;
use ixgbe_driver::device::IxgbeDevice;
use libtime::rdtsc;
use libtime::sys_ns_loopsleep;
use pcid::utils::PciBarAddr;

use ring_buffer::*;
use crate::*;
use core::ptr;

use crate::maglev::*;

pub fn test_ixgbe_driver() {
    let mut ixgbe_dev =
        unsafe { IxgbeDevice::new(PciBarAddr::new(USERSPACE_BASE + 0xFE000000, 0x4000)) };

    log::info!("Initializing Ixgbe driver...");

    ixgbe_dev.init();

    ixgbe_driver::ixgbe_test::run_fwd_udptest(&mut ixgbe_dev, 64, false);
}

#[no_mangle]
pub fn test_ixgbe_with_ring_buffer_ap()-> ! {
    log::info!("hello from test_ixgbe_with_ring_buffer_ap");

    let sender_mac = [
        0x90, 0xe2, 0xba, 0xb3, 0xbd, 0x99, // Dst mac
    ];
    let our_mac = [
        // 90:E2:BA:B5:15:75
        0x90, 0xe2, 0xba, 0xb5, 0x15, 0x75, // Src mac
    ];

    unsafe{
        let size = core::mem::size_of::<IxgbeRingBuffer>();
        let error_code = asys::sys_receive_pages(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_receive_pages failed {:?}", error_code);
        }else{
            log::info!("data_buffer received by dom1");
        }   

        let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);

        for i in 0..240 {
            let (addr,paddr) = buff_ref.try_pop_allocator().unwrap();
            buff_ref.request_queue.try_push(&IxgbePayLoad{addr:addr, paddr:paddr, len:4096});
            // log::info!("receiving package at {:x}", addr);
        }

        let iter = 500000000;
        let mut count = 0;
        let print_iter = iter/20;
        let mut print_count = 0;

        while count <= iter {

            if print_count >= print_iter{
                log::info!("progress {}%", count as f64 / iter as f64 * 100.0);
                print_count = 0;
            }
                let pkt_op = buff_ref.request_completion_queue.try_pop();
                if pkt_op.is_none(){
                }else{
                    // log::info!("received package at {:x}", pkt_op.unwrap().addr);
    
                    count = count + 1;
                    print_count = print_count + 1;
                    let addr = pkt_op.unwrap().addr;
        
                    unsafe {
                        ptr::copy(
                            our_mac.as_ptr(),
                            (addr + 6) as *mut u8,
                            our_mac.len(),
                        );
                        ptr::copy(
                            sender_mac.as_ptr(),
                            addr as *mut u8,
                            sender_mac.len(),
                        );
                    }
        
                    buff_ref.reply_queue.try_push(&pkt_op.unwrap());
                    // log::info!("sending package at {:x}", pkt_op.unwrap().addr);
                }

        }
        log::info!("warm up done");
        count = 0;

        let start = _rdtsc();

        while count <= iter {

            if print_count >= print_iter{
                log::info!("progress {}%", count as f64 / iter as f64 * 100.0);
                print_count = 0;
            }
                let pkt_op = buff_ref.request_completion_queue.try_pop();
                if pkt_op.is_none(){
                }else{
                    // log::info!("received package at {:x}", pkt_op.unwrap().addr);
    
                    count = count + 1;
                    print_count = print_count + 1;
                    let addr = pkt_op.unwrap().addr;
        
                    unsafe {
                        ptr::copy(
                            our_mac.as_ptr(),
                            (addr + 6) as *mut u8,
                            our_mac.len(),
                        );
                        ptr::copy(
                            sender_mac.as_ptr(),
                            addr as *mut u8,
                            sender_mac.len(),
                        );
                    }
        
                    buff_ref.reply_queue.try_push(&pkt_op.unwrap());
                    // log::info!("sending package at {:x}", pkt_op.unwrap().addr);
                }

        }

        let end = _rdtsc();

        log::info!("ixgbe cycles per packet forwarding {:?} throughput {:}",(end - start) as usize /iter, iter as u64 /((end - start)/2_600_000_000_u64));
    }
    loop{

    }
}

#[no_mangle]
pub fn test_ixgbe_with_ring_buffer_tx_ap()-> ! {
    log::info!("hello from test_ixgbe_with_ring_buffer_tx_ap");

    let sender_mac = [
        0x90, 0xe2, 0xba, 0xb3, 0xbd, 0x99, // Dst mac
    ];
    let our_mac = [
        // 90:E2:BA:B5:15:75
        0x90, 0xe2, 0xba, 0xb5, 0x15, 0x75, // Src mac
    ];

    unsafe{
        let size = core::mem::size_of::<IxgbeRingBuffer>();
        let error_code = asys::sys_receive_pages(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_receive_pages failed {:?}", error_code);
        }else{
            log::info!("data_buffer received by dom1");
        }   

        let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);

        for i in 0..255 {
            let (addr,paddr) = buff_ref.try_pop_allocator().unwrap();
            unsafe {
                ptr::copy(
                    our_mac.as_ptr(),
                    (addr + 6) as *mut u8, 
                    our_mac.len(),
                );
                ptr::copy(
                    sender_mac.as_ptr(),
                    addr as *mut u8,
                    sender_mac.len(),
                );
            }
            buff_ref.reply_queue.try_push(&IxgbePayLoad{addr:addr, paddr:paddr, len:0});
            // log::info!("receiving package at {:x}", addr);
        }

        let iter = 500000000;
        let mut count = 0;
        let print_iter = iter/20;
        let mut print_count = 0;

        while count <= iter {

            if print_count >= print_iter{
                log::info!("progress {}%", count as f64 / iter as f64 * 100.0);
                print_count = 0;
            }
                let pkt_op = buff_ref.reply_completion_queue.try_pop();
                if pkt_op.is_none(){
                    // for i in 0.. 100{
                    //     asm!("nop");
                    // }
                }else{
                    // log::info!("received package at {:x}", pkt_op.unwrap().addr);
    
                    count = count + 1;
                    print_count = print_count + 1;
                    let addr = pkt_op.unwrap().addr;
        
                    // unsafe {
                    //     ptr::copy(
                    //         our_mac.as_ptr(),
                    //         (addr + 6) as *mut u8,
                    //         our_mac.len(),
                    //     );
                    //     ptr::copy(
                    //         sender_mac.as_ptr(),
                    //         addr as *mut u8,
                    //         sender_mac.len(),
                    //     );
                    // }
        
                    buff_ref.reply_queue.try_push(&pkt_op.unwrap());
                    // log::info!("sending package at {:x}", pkt_op.unwrap().addr);
                }
        }
        log::info!("warm up done");

        count = 0;

        let start = _rdtsc();

        while count <= iter {

            // if print_count >= print_iter{
            //     log::info!("progress {}%", count as f64 / iter as f64 * 100.0);
            //     print_count = 0;
            // }
                let pkt_op = buff_ref.reply_completion_queue.try_pop();
                if pkt_op.is_none(){
                    // for i in 0.. 100{
                    //     asm!("nop");
                    // }
                }else{
                    // log::info!("received package at {:x}", pkt_op.unwrap().addr);
    
                    count = count + 1;
                    // print_count = print_count + 1;
                    let addr = pkt_op.unwrap().addr;
        
                    // unsafe {
                    //     ptr::copy(
                    //         our_mac.as_ptr(),
                    //         (addr + 6) as *mut u8,
                    //         our_mac.len(),
                    //     );
                    //     ptr::copy(
                    //         sender_mac.as_ptr(),
                    //         addr as *mut u8,
                    //         sender_mac.len(),
                    //     );
                    // }
        
                    buff_ref.reply_queue.try_push(&pkt_op.unwrap());
                    // log::info!("sending package at {:x}", pkt_op.unwrap().addr);
                }
        }

        let end = _rdtsc();

        log::info!("ixgbe cycles tx {:?} throughput {:}",(end - start) as usize /iter, iter as u64 /((end - start)/2_600_000_000_u64));
    }
    loop{

    }
}

pub fn test_ixgbe_with_ring_buffer_tx(){
    unsafe {
        let error_code = asys::sys_new_endpoint(0);
            if error_code != 0 {
                log::info!("sys_new_endpoint failed {:?}", error_code);
                return;
            }
        let mut range = 0;
        loop{
            let (pa,perm) = asys::sys_mresolve(0x8000000000usize + range * 4096);
            // log::info!("va:{:x?}, pa:{:x?}, perm:{:?}", 0x8000000000usize + range * 4096, pa, perm);
            if perm == 34{
                break;
            }
            range = range + 1;
        }
        log::info!("find {:?} pages until {:x?}", range, 0x8000000000usize + range * 4096);

        let size = core::mem::size_of::<IxgbeRingBuffer>();
        let error_code = asys::sys_mmap(DATA_BUFFER_ADDR as usize, 0x0000_0000_0000_0002u64 as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_mmap for data_buffer failed {:?}", error_code);
            return;
        }
        
        let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
        buff_ref.init();
        log::info!("data_buffer init done");

        let new_stack = 0x8000000000usize + range * 4096;
        log::info!("allocating dom1 stack from {:x?}", new_stack);
        let stack_size = 16 * 1024 * 1024;
        let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, stack_size / 4096);
        if error_code != 0 {
            log::info!("sys_mmap for dom1 stack failed {:?}", error_code);
            return;
        }

        let rsp: usize = new_stack + stack_size/2;
        log::info!("request_queue address: {:x?}", rsp);  
        let error_code = asys::sys_new_proc_with_iommu_pass_mem(0,test_ixgbe_with_ring_buffer_tx_ap as *const () as usize, rsp, 0x8000000000usize, range + stack_size / 4096);
            if error_code != 0 {
                log::info!("sys_new_proc_with_iommu_pass_mem failed {:?}", error_code);
                return;
            }
        

        loop{
            let error_code = asys::sys_send_pages_no_wait(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
            if error_code == 5  {
            }else{
                if error_code == 0{
                    log::info!("data_buffer sent to dom1");
                    break;
                }else{
                    log::info!("sys_send_pages_no_wait failed {:?}", error_code);
                    break;
                }
            }
        }
    let mut ixgbe_dev =
        unsafe { IxgbeDevice::new(PciBarAddr::new(USERSPACE_BASE + 0xFE000000, 0x4000)) };

    log::info!("Initializing Ixgbe driver...");

    ixgbe_dev.init();

    unsafe{
        let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
        log::info!("ixgbe_backend started");
        loop{
            ixgbe_dev.tx_submit_and_poll_with_ringbuffer_2(&mut buff_ref.reply_queue, &mut buff_ref.reply_completion_queue, false);
        }
    }
    }
}

pub fn test_ixgbe_with_ring_buffer(){
    unsafe {
        let error_code = asys::sys_new_endpoint(0);
            if error_code != 0 {
                log::info!("sys_new_endpoint failed {:?}", error_code);
                return;
            }
        let mut range = 0;
        loop{
            let (pa,perm) = asys::sys_mresolve(0x8000000000usize + range * 4096);
            // log::info!("va:{:x?}, pa:{:x?}, perm:{:?}", 0x8000000000usize + range * 4096, pa, perm);
            if perm == 34{
                break;
            }
            range = range + 1;
        }
        log::info!("find {:?} pages until {:x?}", range, 0x8000000000usize + range * 4096);

        let size = core::mem::size_of::<IxgbeRingBuffer>();
        let error_code = asys::sys_mmap(DATA_BUFFER_ADDR as usize, 0x0000_0000_0000_0002u64 as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_mmap for data_buffer failed {:?}", error_code);
            return;
        }
        
        let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
        buff_ref.init();
        log::info!("data_buffer init done");

        let new_stack = 0x8000000000usize + range * 4096;
        log::info!("allocating dom1 stack from {:x?}", new_stack);
        let stack_size = 16 * 1024 * 1024;
        let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, stack_size / 4096);
        if error_code != 0 {
            log::info!("sys_mmap for dom1 stack failed {:?}", error_code);
            return;
        }

        let rsp: usize = new_stack + stack_size/2;
        log::info!("request_queue address: {:x?}", rsp);  
        let error_code = asys::sys_new_proc_with_iommu_pass_mem(0,test_ixgbe_with_ring_buffer_ap as *const () as usize, rsp, 0x8000000000usize, range + stack_size / 4096);
            if error_code != 0 {
                log::info!("sys_new_proc_with_iommu_pass_mem failed {:?}", error_code);
                return;
            }
        

        loop{
            let error_code = asys::sys_send_pages_no_wait(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
            if error_code == 5  {
            }else{
                if error_code == 0{
                    log::info!("data_buffer sent to dom1");
                    break;
                }else{
                    log::info!("sys_send_pages_no_wait failed {:?}", error_code);
                    break;
                }
            }
        }
        ixgbe_driver_backend();
    }
}


pub fn ixgbe_driver_backend(){
    let mut ixgbe_dev =
        unsafe { IxgbeDevice::new(PciBarAddr::new(USERSPACE_BASE + 0xFE000000, 0x4000)) };

    log::info!("Initializing Ixgbe driver...");

    ixgbe_dev.init();

    unsafe{
        let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
        log::info!("ixgbe_backend started");
        loop{
            ixgbe_dev.rx_submit_and_poll_with_ringbuffer_2(&mut buff_ref.request_queue, &mut buff_ref.request_completion_queue, false);
            // log::info!("dashi");
            ixgbe_dev.tx_submit_and_poll_with_ringbuffer_2(&mut buff_ref.reply_queue, &mut buff_ref.request_queue, false);
        }
    }


}

pub fn test_ixgbe_with_ring_buffer_single_core(){

    let sender_mac = [
        0x90, 0xe2, 0xba, 0xb3, 0xbd, 0x99, // Dst mac
    ];
    let our_mac = [
        // 90:E2:BA:B5:15:75
        0x90, 0xe2, 0xba, 0xb5, 0x15, 0x75, // Src mac
    ];
    unsafe{

        let size = core::mem::size_of::<IxgbeRingBuffer>();
        let error_code = asys::sys_mmap(DATA_BUFFER_ADDR as usize, 0x0000_0000_0000_0002u64 as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_mmap for data_buffer failed {:?}", error_code);
            return;
        }
        
        let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
        buff_ref.init();
        log::info!("data_buffer init done");

        let mut ixgbe_dev =
            unsafe { IxgbeDevice::new(PciBarAddr::new(USERSPACE_BASE + 0xFE000000, 0x4000)) };

        log::info!("Initializing Ixgbe driver...");

        ixgbe_dev.init();
        
        let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
        log::info!("ixgbe_backend started");

        for i in 0..128 {
            let (addr,paddr) = buff_ref.try_pop_allocator().unwrap();
            buff_ref.request_queue.try_push(&IxgbePayLoad{addr:addr, paddr:paddr, len:4096});
            // log::info!("receiving package at {:x}", addr);
        }

        let iter = 500000000;
        let mut count = 0;
        let print_iter = iter/20;
        let mut print_count = 0;

        log::info!("warming up");
        while count <= iter {

            if print_count >= print_iter{
                log::info!("warm up progress {}%", count as f64 / iter as f64 * 100.0);
                print_count = 0;
            }

            for i in 0..64{
                let pkt_op = buff_ref.request_completion_queue.try_pop();
                if pkt_op.is_none(){
                    break;
                }else{
                    // log::info!("received package at {:x}", pkt_op.unwrap().addr);
    
                    count = count + 1;
                    print_count = print_count + 1;
                    let addr = pkt_op.unwrap().addr;
        
                    unsafe {
                        ptr::copy(
                            our_mac.as_ptr(),
                            (addr + 6) as *mut u8,
                            our_mac.len(),
                        );
                        ptr::copy(
                            sender_mac.as_ptr(),
                            addr as *mut u8,
                            sender_mac.len(),
                        );
                    }
        
                    buff_ref.reply_queue.try_push(&pkt_op.unwrap());
                    // log::info!("sending package at {:x}", pkt_op.unwrap().addr);
                }
            }
        

            // let pkt_op = buff_ref.reply_completion_queue.try_pop();
            // if pkt_op.is_none(){
            // }else{
            //     // log::info!("sent package at {:x}", pkt_op.unwrap().addr);
    
            //     let addr = pkt_op.unwrap().addr;
    
            //     buff_ref.try_push_allocator((pkt_op.unwrap().addr,pkt_op.unwrap().paddr));

            //     if let Some((addr,paddr)) = buff_ref.try_pop_allocator(){
            //         buff_ref.request_queue.try_push(&IxgbePayLoad{addr:addr, paddr:paddr, len:4096});
            //         // log::info!("receiving package at {:x}", addr);
            //     }
            // }

            ixgbe_dev.rx_submit_and_poll_with_ringbuffer_2(&mut buff_ref.request_queue, &mut buff_ref.request_completion_queue, false);
            // log::info!("dashi");
            ixgbe_dev.tx_submit_and_poll_with_ringbuffer_2(&mut buff_ref.reply_queue, &mut buff_ref.request_queue, false);

        }
        log::info!("warm up done");

        count = 0;
        let start = _rdtsc();

        while count <= iter {

            if print_count >= print_iter{
                log::info!("progress {}%", count as f64 / iter as f64 * 100.0);
                print_count = 0;
            }
            for i in 0 .. 64{
                let pkt_op = buff_ref.request_completion_queue.try_pop();
                if pkt_op.is_none(){
                    break;
                }else{
                    // log::info!("received package at {:x}", pkt_op.unwrap().addr);
    
                    count = count + 1;
                    print_count = print_count + 1;
                    let addr = pkt_op.unwrap().addr;
        
                    unsafe {
                        ptr::copy(
                            our_mac.as_ptr(),
                            (addr + 6) as *mut u8,
                            our_mac.len(),
                        );
                        ptr::copy(
                            sender_mac.as_ptr(),
                            addr as *mut u8,
                            sender_mac.len(),
                        );
                    }
        
                    buff_ref.reply_queue.try_push(&pkt_op.unwrap());
                    // log::info!("sending package at {:x}", pkt_op.unwrap().addr);
                }
            }

            ixgbe_dev.rx_submit_and_poll_with_ringbuffer_2(&mut buff_ref.request_queue, &mut buff_ref.request_completion_queue, false);
            // log::info!("dashi");
            ixgbe_dev.tx_submit_and_poll_with_ringbuffer_2(&mut buff_ref.reply_queue, &mut buff_ref.request_queue, false);

        }

        let end = _rdtsc();

        log::info!("ixgbe cycles per packet forwarding {:?} throughput {:}",(end - start) as usize /iter, iter as u64 /((end - start)/2_600_000_000_u64));

    }

}

    #[no_mangle]
    pub fn test_ixgbe_with_ring_buffer_single_core_two_processes_ap()-> ! {
        log::info!("hello from test_ixgbe_with_ring_buffer_single_core_two_processes_ap");
    
        let sender_mac = [
            0x90, 0xe2, 0xba, 0xb3, 0xbd, 0x99, // Dst mac
        ];
        let our_mac = [
            // 90:E2:BA:B5:15:75
            0x90, 0xe2, 0xba, 0xb5, 0x15, 0x75, // Src mac
        ];
    
        unsafe{
            let size = core::mem::size_of::<IxgbeRingBuffer>();
            let error_code = asys::sys_receive_pages(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
            if error_code != 0 {
                log::info!("sys_receive_pages failed {:?}", error_code);
            }else{
                log::info!("data_buffer received by dom1");
            }   
    
            let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
    
            for i in 0..32 {
                let (addr,paddr) = buff_ref.try_pop_allocator().unwrap();
                buff_ref.request_queue.try_push(&IxgbePayLoad{addr:addr, paddr:paddr, len:4096});
                // log::info!("receiving package at {:x}", addr);
            }
    
            let iter = 500000000;
            let mut count = 0;
            let print_iter = iter/20;
            let mut print_count = 0;

            let start = _rdtsc();
    
            while true {
    
                if print_count >= print_iter{
                    log::info!("progress {}%", count as f64 / iter as f64 * 100.0);
                    print_count = 0;
                }
                for i in 0 .. 1 {
                    let pkt_op = buff_ref.request_completion_queue.try_pop();
                    if pkt_op.is_none(){
                        break;
                    }else{
                        // log::info!("received package at {:x}", pkt_op.unwrap().addr);
        
                        count = count + 1;
                        print_count = print_count + 1;
                        let addr = pkt_op.unwrap().addr;
            
                        unsafe {
                            ptr::copy(
                                our_mac.as_ptr(),
                                (addr + 6) as *mut u8,
                                our_mac.len(),
                            );
                            ptr::copy(
                                sender_mac.as_ptr(),
                                addr as *mut u8,
                                sender_mac.len(),
                            );
                        }
            
                        buff_ref.reply_queue.try_push(&pkt_op.unwrap());
                        // log::info!("sending package at {:x}", pkt_op.unwrap().addr);
                    }
                }

                // log::info!("receiving from dom1");
                let error_code = asys::sys_receive_empty(0);
                // log::info!("pong");
                if error_code != 0 {
                    log::info!("sys_send_empty failed {:?}", error_code);
                    break;
                }
    
                // for i in 0 .. 64{
                //     let pkt_op = buff_ref.reply_completion_queue.try_pop();
                //     if pkt_op.is_none(){
                //         break;
                //     }else{
                //         // log::info!("sent package at {:x}", pkt_op.unwrap().addr);
            
                //         let addr = pkt_op.unwrap().addr;
            
                //         // buff_ref.try_push_allocator(pkt_op.unwrap().addr);
    
                //         // if let Some(addr) = buff_ref.try_pop_allocator(){
                //         buff_ref.request_queue.try_push(&IxgbePayLoad{addr:pkt_op.unwrap().addr,paddr:pkt_op.unwrap().paddr,len:4096});
                //             // log::info!("receiving package at {:x}", addr);
                //         // }
                //     }
                // }
    
            }
    
            let end = _rdtsc();
    
            log::info!("ixgbe cycles per packet forwarding {:?} throughput {:}",(end - start) as usize /iter, iter as u64 /((end - start)/2_600_000_000_u64));
        }
        loop{
    
        }
    }
    
pub fn test_ixgbe_with_ring_buffer_single_core_two_processes(){
    unsafe {
        let error_code = asys::sys_new_endpoint(0);
            if error_code != 0 {
                log::info!("sys_new_endpoint failed {:?}", error_code);
                return;
            }
        let mut range = 0;
        loop{
            let (pa,perm) = asys::sys_mresolve(0x8000000000usize + range * 4096);
            // log::info!("va:{:x?}, pa:{:x?}, perm:{:?}", 0x8000000000usize + range * 4096, pa, perm);
            if perm == 34{
                break;
            }
            range = range + 1;
        }
        log::info!("find {:?} pages until {:x?}", range, 0x8000000000usize + range * 4096);

        let size = core::mem::size_of::<IxgbeRingBuffer>();
        let error_code = asys::sys_mmap(DATA_BUFFER_ADDR as usize, 0x0000_0000_0000_0002u64 as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_mmap for data_buffer failed {:?}", error_code);
            return;
        }
        
        let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
        buff_ref.init();
        log::info!("data_buffer init done");

        let new_stack = 0x8000000000usize + range * 4096;
        log::info!("allocating dom1 stack from {:x?}", new_stack);
        let stack_size = 16 * 1024 * 1024;
        let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, stack_size / 4096);
        if error_code != 0 {
            log::info!("sys_mmap for dom1 stack failed {:?}", error_code);
            return;
        }

        let rsp: usize = new_stack + stack_size/2;
        log::info!("request_queue address: {:x?}", rsp);  
        let error_code = asys::sys_new_proc_with_iommu_pass_mem(0,test_ixgbe_with_ring_buffer_single_core_two_processes_ap as *const () as usize, rsp, 0x8000000000usize, range + stack_size / 4096);
            if error_code != 0 {
                log::info!("sys_new_proc_with_iommu_pass_mem failed {:?}", error_code);
                return;
            }
    
        let mut ixgbe_dev =
            unsafe { IxgbeDevice::new(PciBarAddr::new(USERSPACE_BASE + 0xFE000000, 0x4000)) };

        log::info!("Initializing Ixgbe driver...");

        ixgbe_dev.init();


        let error_code = asys::sys_send_pages(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
        if error_code == 5  {
        }else{
            if error_code == 0{
                log::info!("data_buffer sent to dom1");
            }else{
                log::info!("sys_send_pages_no_wait failed {:?}", error_code);
            }
        }
        
        let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
        log::info!("ixgbe_backend started");
        
        loop{
            ixgbe_dev.rx_submit_and_poll_with_ringbuffer_2(&mut buff_ref.request_queue, &mut buff_ref.request_completion_queue, false);
            // log::info!("dashi");
            ixgbe_dev.tx_submit_and_poll_with_ringbuffer_2(&mut buff_ref.reply_queue, &mut buff_ref.request_queue, false);

            // log::info!("sending from dom0");
            let error_code = asys::sys_send_empty(0);
            // log::info!("sent from dom0");
            if error_code != 0 {
                log::info!("sys_send_empty failed {:?}", error_code);
                return;
            }

        }
    }
}


#[no_mangle]
pub fn test_ixgbe_with_ring_buffer_tx_single_core_two_processes_ap()-> ! {
    log::info!("hello from test_ixgbe_with_ring_buffer_single_core_two_processes_ap");

    let sender_mac = [
        0x90, 0xe2, 0xba, 0xb3, 0xbd, 0x99, // Dst mac
    ];
    let our_mac = [
        // 90:E2:BA:B5:15:75
        0x90, 0xe2, 0xba, 0xb5, 0x15, 0x75, // Src mac
    ];

    unsafe{
        let size = core::mem::size_of::<IxgbeRingBuffer>();
        let error_code = asys::sys_receive_pages(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_receive_pages failed {:?}", error_code);
        }else{
            log::info!("data_buffer received by dom1");
        }   

        let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);

        for i in 0..32 {
            let (addr,paddr) = buff_ref.try_pop_allocator().unwrap();
            // log::info!("receiving package at {:x}", addr);
            unsafe {
                ptr::copy(
                    our_mac.as_ptr(),
                    (addr + 6) as *mut u8, 
                    our_mac.len(),
                );
                ptr::copy(
                    sender_mac.as_ptr(),
                    addr as *mut u8,
                    sender_mac.len(),
                );
            }
            buff_ref.reply_queue.try_push(&IxgbePayLoad{addr:addr, paddr:paddr, len:64});
        }

        let iter = 100000000;
        let mut count = 0;
        let print_iter = iter/20;
        let mut print_count = 0;

        while count <= iter {

            if print_count >= print_iter{
                log::info!("progress {}%", count as f64 / iter as f64 * 100.0);
                print_count = 0;
            }
            for i in 0 .. 32 {
                let pkt_op = buff_ref.reply_completion_queue.try_pop();
                if pkt_op.is_none(){
                    break;
                }else{
                    // log::info!("received package at {:x}", pkt_op.unwrap().addr);
    
                    count = count + 1;
                    print_count = print_count + 1;
        
                    buff_ref.reply_queue.try_push(&pkt_op.unwrap());
                    // log::info!("sending package at {:x}", pkt_op.unwrap().addr);
                }
            }

            // log::info!("receiving from dom1");
            let error_code = asys::sys_receive_empty(0);
            // log::info!("pong");
            if error_code != 0 {
                log::info!("sys_send_empty failed {:?}", error_code);
                break;
            }
        }

        count = 0;

        let start = _rdtsc();

        while count <= iter {

            if print_count >= print_iter{
                log::info!("progress {}%", count as f64 / iter as f64 * 100.0);
                print_count = 0;
            }
            for i in 0 .. 1 {
                let pkt_op = buff_ref.reply_completion_queue.try_pop();
                if pkt_op.is_none(){
                    break;
                }else{
                    // log::info!("received package at {:x}", pkt_op.unwrap().addr);
    
                    count = count + 1;
                    print_count = print_count + 1;
        
                    buff_ref.reply_queue.try_push(&pkt_op.unwrap());
                    // log::info!("sending package at {:x}", pkt_op.unwrap().addr);
                }
            }

            // log::info!("receiving from dom1");
            let error_code = asys::sys_receive_empty(0);
            // log::info!("pong");
            if error_code != 0 {
                log::info!("sys_send_empty failed {:?}", error_code);
                break;
            }
        }

        let end = _rdtsc();

        log::info!("ixgbe cycles per tx {:?} throughput {:}",(end - start) as usize /iter, iter as u64 /((end - start)/2_600_000_000_u64));
    }
    loop{

    }
}

pub fn test_ixgbe_with_ring_buffer_tx_single_core_two_processes(){
unsafe {
    let error_code = asys::sys_new_endpoint(0);
        if error_code != 0 {
            log::info!("sys_new_endpoint failed {:?}", error_code);
            return;
        }
    let mut range = 0;
    loop{
        let (pa,perm) = asys::sys_mresolve(0x8000000000usize + range * 4096);
        // log::info!("va:{:x?}, pa:{:x?}, perm:{:?}", 0x8000000000usize + range * 4096, pa, perm);
        if perm == 34{
            break;
        }
        range = range + 1;
    }
    log::info!("find {:?} pages until {:x?}", range, 0x8000000000usize + range * 4096);

    let size = core::mem::size_of::<IxgbeRingBuffer>();
    let error_code = asys::sys_mmap(DATA_BUFFER_ADDR as usize, 0x0000_0000_0000_0002u64 as usize, size / 4096 + 1);
    if error_code != 0 {
        log::info!("sys_mmap for data_buffer failed {:?}", error_code);
        return;
    }
    
    let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
    buff_ref.init();
    log::info!("data_buffer init done");

    let new_stack = 0x8000000000usize + range * 4096;
    log::info!("allocating dom1 stack from {:x?}", new_stack);
    let stack_size = 16 * 1024 * 1024;
    let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, stack_size / 4096);
    if error_code != 0 {
        log::info!("sys_mmap for dom1 stack failed {:?}", error_code);
        return;
    }

    let rsp: usize = new_stack + stack_size/2;
    log::info!("request_queue address: {:x?}", rsp);  
    let error_code = asys::sys_new_proc_with_iommu_pass_mem(0,test_ixgbe_with_ring_buffer_tx_single_core_two_processes_ap as *const () as usize, rsp, 0x8000000000usize, range + stack_size / 4096);
        if error_code != 0 {
            log::info!("sys_new_proc_with_iommu_pass_mem failed {:?}", error_code);
            return;
        }

    let mut ixgbe_dev =
        unsafe { IxgbeDevice::new(PciBarAddr::new(USERSPACE_BASE + 0xFE000000, 0x4000)) };

    log::info!("Initializing Ixgbe driver...");

    ixgbe_dev.init();


    let error_code = asys::sys_send_pages(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
    if error_code == 5  {
    }else{
        if error_code == 0{
            log::info!("data_buffer sent to dom1");
        }else{
            log::info!("sys_send_pages_no_wait failed {:?}", error_code);
        }
    }
    
    let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
    log::info!("ixgbe_backend started");
    
    loop{
        ixgbe_dev.tx_submit_and_poll_with_ringbuffer_2(&mut buff_ref.reply_queue, &mut buff_ref.reply_completion_queue, false);

        // log::info!("sending from dom0");
        let error_code = asys::sys_send_empty(0);
        // log::info!("sent from dom0");
        if error_code != 0 {
            log::info!("sys_send_empty failed {:?}", error_code);
            return;
        }

    }
}
}

#[no_mangle]
pub fn test_ixgbe_with_ring_buffer_rx_single_core_two_processes_ap()-> ! {
    log::info!("hello from test_ixgbe_with_ring_buffer_rx_single_core_two_processes_ap");

    let sender_mac = [
        0x90, 0xe2, 0xba, 0xb3, 0xbd, 0x99, // Dst mac
    ];
    let our_mac = [
        // 90:E2:BA:B5:15:75
        0x90, 0xe2, 0xba, 0xb5, 0x15, 0x75, // Src mac
    ];

    unsafe{
        let size = core::mem::size_of::<IxgbeRingBuffer>();
        let error_code = asys::sys_receive_pages(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_receive_pages failed {:?}", error_code);
        }else{
            log::info!("data_buffer received by dom1");
        }   

        let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);

        for i in 0..32 {
            let (addr,paddr) = buff_ref.try_pop_allocator().unwrap();
            // log::info!("receiving package at {:x}", addr);
            buff_ref.request_queue.try_push(&IxgbePayLoad{addr:addr, paddr:paddr, len:60});
        }

        let iter = 100000000;
        let mut count = 0;
        let print_iter = iter/20;
        let mut print_count = 0;

        while count <= iter {

            if print_count >= print_iter{
                log::info!("progress {}%", count as f64 / iter as f64 * 100.0);
                print_count = 0;
            }
            for i in 0 .. 32 {
                let pkt_op = buff_ref.request_completion_queue.try_pop();
                if pkt_op.is_none(){
                    break;
                }else{
                    // log::info!("received package at {:x}", pkt_op.unwrap().addr);
    
                    count = count + 1;
                    print_count = print_count + 1;
        
                    buff_ref.request_queue.try_push(&pkt_op.unwrap());
                    // log::info!("sending package at {:x}", pkt_op.unwrap().addr);
                }
            }

            // log::info!("receiving from dom1");
            let error_code = asys::sys_receive_empty(0);
            // log::info!("pong");
            if error_code != 0 {
                log::info!("sys_send_empty failed {:?}", error_code);
                break;
            }
        }

        count = 0;

        let start = _rdtsc();

        while count <= iter {

            if print_count >= print_iter{
                log::info!("progress {}%", count as f64 / iter as f64 * 100.0);
                print_count = 0;
            }
            for i in 0 .. 32 {
                let pkt_op = buff_ref.request_completion_queue.try_pop();
                if pkt_op.is_none(){
                    break;
                }else{
                    // log::info!("received package at {:x}", pkt_op.unwrap().addr);
    
                    count = count + 1;
                    print_count = print_count + 1;
        
                    buff_ref.request_queue.try_push(&pkt_op.unwrap());
                    // log::info!("sending package at {:x}", pkt_op.unwrap().addr);
                }
            }

            // log::info!("receiving from dom1");
            let error_code = asys::sys_receive_empty(0);
            // log::info!("pong");
            if error_code != 0 {
                log::info!("sys_send_empty failed {:?}", error_code);
                break;
            }
        }

        let end = _rdtsc();

        log::info!("ixgbe cycles per rx {:?} throughput {:}",(end - start) as usize /iter, iter as u64 /((end - start)/2_600_000_000_u64));
    }
    loop{

    }
}

pub fn test_ixgbe_with_ring_buffer_rx_single_core_two_processes(){
unsafe {
    let error_code = asys::sys_new_endpoint(0);
        if error_code != 0 {
            log::info!("sys_new_endpoint failed {:?}", error_code);
            return;
        }
    let mut range = 0;
    loop{
        let (pa,perm) = asys::sys_mresolve(0x8000000000usize + range * 4096);
        // log::info!("va:{:x?}, pa:{:x?}, perm:{:?}", 0x8000000000usize + range * 4096, pa, perm);
        if perm == 34{
            break;
        }
        range = range + 1;
    }
    log::info!("find {:?} pages until {:x?}", range, 0x8000000000usize + range * 4096);

    let size = core::mem::size_of::<IxgbeRingBuffer>();
    let error_code = asys::sys_mmap(DATA_BUFFER_ADDR as usize, 0x0000_0000_0000_0002u64 as usize, size / 4096 + 1);
    if error_code != 0 {
        log::info!("sys_mmap for data_buffer failed {:?}", error_code);
        return;
    }
    
    let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
    buff_ref.init();
    log::info!("data_buffer init done");

    let new_stack = 0x8000000000usize + range * 4096;
    log::info!("allocating dom1 stack from {:x?}", new_stack);
    let stack_size = 16 * 1024 * 1024;
    let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, stack_size / 4096);
    if error_code != 0 {
        log::info!("sys_mmap for dom1 stack failed {:?}", error_code);
        return;
    }

    let rsp: usize = new_stack + stack_size/2;
    log::info!("request_queue address: {:x?}", rsp);  
    let error_code = asys::sys_new_proc_with_iommu_pass_mem(0,test_ixgbe_with_ring_buffer_rx_single_core_two_processes_ap as *const () as usize, rsp, 0x8000000000usize, range + stack_size / 4096);
        if error_code != 0 {
            log::info!("sys_new_proc_with_iommu_pass_mem failed {:?}", error_code);
            return;
        }

    let mut ixgbe_dev =
        unsafe { IxgbeDevice::new(PciBarAddr::new(USERSPACE_BASE + 0xFE000000, 0x4000)) };

    log::info!("Initializing Ixgbe driver...");

    ixgbe_dev.init();


    let error_code = asys::sys_send_pages(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
    if error_code == 5  {
    }else{
        if error_code == 0{
            log::info!("data_buffer sent to dom1");
        }else{
            log::info!("sys_send_pages_no_wait failed {:?}", error_code);
        }
    }
    
    let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
    log::info!("ixgbe_backend started");
    
    loop{
        ixgbe_dev.rx_submit_and_poll_with_ringbuffer_2(&mut buff_ref.request_queue, &mut buff_ref.request_completion_queue, false);

        // log::info!("sending from dom0");
        let error_code = asys::sys_send_empty(0);
        // log::info!("sent from dom0");
        if error_code != 0 {
            log::info!("sys_send_empty failed {:?}", error_code);
            return;
        }
    }
}
}


pub fn start_ixgbe_driver_backend(){
    unsafe {

        let size = core::mem::size_of::<IxgbeRingBuffer>();
        let error_code = asys::sys_mmap(DATA_BUFFER_ADDR as usize, 0x0000_0000_0000_0002u64 as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_mmap for data_buffer failed {:?}", error_code);
            return;
        }
        
        let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
        buff_ref.init();
        log::info!("data_buffer init done");
        
        loop{
            let error_code = asys::sys_send_pages_no_wait(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
            if error_code == 5  {
            }else{
                if error_code == 0{
                    log::info!("data_buffer sent to dom1");
                    break;
                }else{
                    log::info!("sys_send_pages_no_wait failed {:?}", error_code);
                    break;
                }
            }
        }
        let mut ixgbe_dev =
            unsafe { IxgbeDevice::new(PciBarAddr::new(USERSPACE_BASE + 0xFE000000, 0x4000)) };

        log::info!("Initializing Ixgbe driver...");

        ixgbe_dev.init();

        unsafe{
            let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
            log::info!("ixgbe_backend started");
            loop{
                ixgbe_dev.rx_submit_and_poll_with_ringbuffer_2(&mut buff_ref.request_queue, &mut buff_ref.request_completion_queue, false);
                // log::info!("dashi");
                ixgbe_dev.tx_submit_and_poll_with_ringbuffer_2(&mut buff_ref.reply_queue, &mut buff_ref.request_queue, false);
            }
        }
    }
}

pub fn start_ixgbe_driver_backend_with_ipc(){
    unsafe {

        let size = core::mem::size_of::<IxgbeRingBuffer>();
        let error_code = asys::sys_mmap(DATA_BUFFER_ADDR as usize, 0x0000_0000_0000_0002u64 as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_mmap for data_buffer failed {:?}", error_code);
            return;
        }
        
        let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
        buff_ref.init();
        log::info!("data_buffer init done");
        
        loop{
            let error_code = asys::sys_send_pages(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
            if error_code == 5  {
            }else{
                if error_code == 0{
                    log::info!("data_buffer sent to dom1");
                    break;
                }else{
                    log::info!("sys_send_pages_no_wait failed {:?}", error_code);
                    break;
                }
            }
        }
        let mut ixgbe_dev =
            unsafe { IxgbeDevice::new(PciBarAddr::new(USERSPACE_BASE + 0xFE000000, 0x4000)) };

        log::info!("Initializing Ixgbe driver...");

        ixgbe_dev.init();

        unsafe{
            let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
            log::info!("ixgbe_backend started");
            loop{
                ixgbe_dev.rx_submit_and_poll_with_ringbuffer_2(&mut buff_ref.request_queue, &mut buff_ref.request_completion_queue, false);
                // log::info!("dashi");
                ixgbe_dev.tx_submit_and_poll_with_ringbuffer_2(&mut buff_ref.reply_queue, &mut buff_ref.request_queue, false);
                asys::sys_send_empty(0);
            }
        }
    }
}


pub fn start_ixgbe_driver_fwd_test(){
    let sender_mac = [
        0x90, 0xe2, 0xba, 0xb3, 0xbd, 0x99, // Dst mac
    ];
    let our_mac = [
        // 90:E2:BA:B5:15:75
        0x90, 0xe2, 0xba, 0xb5, 0x15, 0x75, // Src mac
    ];
    unsafe {

        let size = core::mem::size_of::<IxgbeRingBuffer>();
        let error_code = asys::sys_mmap(DATA_BUFFER_ADDR as usize, 0x0000_0000_0000_0002u64 as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_mmap for data_buffer failed {:?}", error_code);
            return;
        }
        
        let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
        buff_ref.init();
        log::info!("data_buffer init done");

        for i in 0..240 {
            let (addr,paddr) = buff_ref.try_pop_allocator().unwrap();
            buff_ref.request_queue.try_push(&IxgbePayLoad{addr:addr, paddr:paddr, len:4096});
            // log::info!("receiving package at {:x}", addr);
        }
        
        let mut ixgbe_dev =
            unsafe { IxgbeDevice::new(PciBarAddr::new(USERSPACE_BASE + 0xFE000000, 0x4000)) };

        log::info!("Initializing Ixgbe driver...");

        ixgbe_dev.init();

        unsafe{
            let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
            log::info!("ixgbe_backend started");
            loop{
                ixgbe_dev.rx_submit_and_poll_with_ringbuffer_2(&mut buff_ref.request_queue, &mut buff_ref.request_completion_queue, false);
                // log::info!("dashi");
                ixgbe_dev.tx_submit_and_poll_with_ringbuffer_2(&mut buff_ref.reply_queue, &mut buff_ref.request_queue, false);

                loop{
                    let pkt_op = buff_ref.request_completion_queue.try_pop();
                    if pkt_op.is_none(){
                        break;
                    }else{
                        // log::info!("received package at {:x}", pkt_op.unwrap().addr);
        
                        let addr = pkt_op.unwrap().addr;
            
                        unsafe {
                            ptr::copy(
                                our_mac.as_ptr(),
                                (addr + 6) as *mut u8,
                                our_mac.len(),
                            );
                            ptr::copy(
                                sender_mac.as_ptr(),
                                addr as *mut u8,
                                sender_mac.len(),
                            );
                        }
            
                        buff_ref.reply_queue.try_push(&pkt_op.unwrap());
                        // log::info!("sending package at {:x}", pkt_op.unwrap().addr);
                    }
                }
            }
        }
    }
}

pub fn start_ixgbe_driver_maglev_test(){
    let sender_mac = [
        0x90, 0xe2, 0xba, 0xb3, 0xbd, 0x99, // Dst mac
    ];
    let our_mac = [
        // 90:E2:BA:B5:15:75
        0x90, 0xe2, 0xba, 0xb5, 0x15, 0x75, // Src mac
    ];

    maglev_init();

    unsafe {

        let size = core::mem::size_of::<IxgbeRingBuffer>();
        let error_code = asys::sys_mmap(DATA_BUFFER_ADDR as usize, 0x0000_0000_0000_0002u64 as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_mmap for data_buffer failed {:?}", error_code);
            return;
        }
        
        let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
        buff_ref.init();
        log::info!("data_buffer init done");
        
        for i in 0..240 {
            let (addr,paddr) = buff_ref.try_pop_allocator().unwrap();
            buff_ref.request_queue.try_push(&IxgbePayLoad{addr:addr, paddr:paddr, len:4096});
            // log::info!("receiving package at {:x}", addr);
        }

        let mut ixgbe_dev =
            unsafe { IxgbeDevice::new(PciBarAddr::new(USERSPACE_BASE + 0xFE000000, 0x4000)) };

        log::info!("Initializing Ixgbe driver...");

        ixgbe_dev.init();

        unsafe{
            let buff_ref:&mut IxgbeRingBuffer = &mut*(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);
            log::info!("ixgbe_backend started");
            loop{
                ixgbe_dev.rx_submit_and_poll_with_ringbuffer_2(&mut buff_ref.request_queue, &mut buff_ref.request_completion_queue, false);
                // log::info!("dashi");
                ixgbe_dev.tx_submit_and_poll_with_ringbuffer_2(&mut buff_ref.reply_queue, &mut buff_ref.request_queue, false);

                loop{
                    let pkt_op = buff_ref.request_completion_queue.try_pop();
                    if pkt_op.is_none(){
                        break;
                    }else{
                        // log::info!("received package at {:x}", pkt_op.unwrap().addr);
        
                        let addr = pkt_op.unwrap().addr;

                        let backend = maglev_process_frame(addr as *mut rte_ether_hdr, pkt_op.unwrap().len);
                        if backend != 233{
                            unsafe {
                                ptr::copy(
                                    our_mac.as_ptr(),
                                    (addr + 6) as *mut u8,
                                    our_mac.len(),
                                );
                                ptr::copy(
                                    sender_mac.as_ptr(),
                                    addr as *mut u8,
                                    sender_mac.len(),
                                );
                            }
                        }
            
                        buff_ref.reply_queue.try_push(&pkt_op.unwrap());
                        // log::info!("sending package at {:x}", pkt_op.unwrap().addr);
                    }
                }
            }
        }
    }
}

pub fn start_ixgbe_driver_smoltcp_test() {
    use smoltcp::iface::{Config, Interface, SocketSet, SocketStorage};
    use smoltcp::wire::{EthernetAddress, IpAddress, IpCidr};
    use smoltcp::time::Instant;

    use crate::smoltcp_device::SmolIxgbe;

    let size = core::mem::size_of::<IxgbeRingBuffer>();
    let error_code = unsafe {
        asys::sys_mmap(DATA_BUFFER_ADDR as usize, 0x0000_0000_0000_0002u64 as usize, size / 4096 + 1)
    };

    if error_code != 0 {
        log::info!("sys_mmap for data_buffer failed {:?}", error_code);
        return;
    }
    
    let buff_ref: &mut IxgbeRingBuffer = unsafe {
        &mut *(DATA_BUFFER_ADDR as *mut IxgbeRingBuffer)
    };
    buff_ref.init();
    log::info!("data_buffer init done");

    for i in 0..240 {
        let (addr, paddr) = buff_ref.try_pop_allocator().unwrap();
        buff_ref.request_queue.try_push(&IxgbePayLoad{addr: addr, paddr: paddr, len: 4096 });
        log::info!("receiving packet at {:x}", addr);
    }

    let mut ixgbe_dev =
        unsafe { IxgbeDevice::new(PciBarAddr::new(USERSPACE_BASE + 0xFE000000, 0x4000)) };
    ixgbe_dev.init();

    let mut device = crate::smoltcp_device::SmolIxgbe::new(ixgbe_dev, DATA_BUFFER_ADDR as *mut IxgbeRingBuffer);

    let config = Config::new(EthernetAddress([0x90, 0xe2, 0xba, 0xac, 0x16, 0x59]).into());
    let mut iface = Interface::new(config, &mut device, Instant::from_secs(0));
    iface.update_ip_addrs(|ip_addrs| {
        ip_addrs
            .push(IpCidr::new(IpAddress::v4(10, 0, 0, 2), 24))
            .unwrap();
    });

    let mut sockets = [SocketStorage::EMPTY; 1024];
    let mut sockets = SocketSet::new(sockets.as_mut_slice());


    let mut timestamp = 0;

    loop {
        device.do_rx();

        iface.poll(Instant::from_millis(timestamp), &mut device, &mut sockets);
        // httpd.handle(&mut sockets);

        device.do_tx();

        timestamp += 1;
    }
}
