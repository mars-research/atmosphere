use core::arch::x86_64::_rdtsc;
use core::arch::asm;
use crate::*;

pub const BATCH_SIZE:usize = 1;
pub const EMPTY_QUEUE_SLEEP_CYCLE:usize = 100;

#[no_mangle]
pub fn test_null_driver_ap()-> ! {
    log::info!("hello from test_null_driver_ap");

    unsafe{
        let size = core::mem::size_of::<DataBufferAllocWrapper>();
        let error_code = asys::sys_receive_pages(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_receive_pages failed {:?}", error_code);
        }else{
            log::info!("data_buffer received by dom1");
        }   
    }

    let target = 10000000;
    let mut counter = 0;
        unsafe{
            let buff_ref:&mut DataBufferAllocWrapper = &mut*(DATA_BUFFER_ADDR as *mut DataBufferAllocWrapper);
            for i in 0..SIZE_OF_QUEUE{
                buff_ref.free_stack[buff_ref.len] = i;
                buff_ref.len = buff_ref.len + 1;
            }
            // log::info!("free_stack init done");
            let start = _rdtsc();
            while counter <= target{
                //push free stack into request queue
                // log::info!("counter: {:?}",counter);
                while buff_ref.len != 0 {
                    let result = buff_ref.request_queue.try_push(buff_ref.free_stack[buff_ref.len-1]);
                    // log::info!("result: {:?} i: {:?}",result,free_stack[len-1]);
                    if result{
                        buff_ref.len = buff_ref.len -1;
                    }
                    

                }
                //pop reply queue to free stack
                loop{
                    let result = buff_ref.reply_queue.try_pop();
                    if result.is_none(){
                        break;
                    }else{
                        counter = counter + 1;
                        buff_ref.free_stack[buff_ref.len] = result.unwrap();
                        buff_ref.len = buff_ref.len + 1;
                    }
                }
            }
            let end = _rdtsc();
            log::info!("null_driver cycles per request {:?}",(end-start) as usize /target);
        }

    loop {
        unsafe{asm!("nop");}
    }
}
pub fn test_null_driver(){
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

        let new_stack = 0x8000000000usize + range * 4096;
        log::info!("allocating dom1 stack from {:x?}", new_stack);
        let size = 16 * 1024 * 1024;
        let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, size / 4096);
        if error_code != 0 {
            log::info!("sys_mmap for dom1 stack failed {:?}", error_code);
            return;
        }
        let rsp: usize = new_stack + size/2;
        log::info!("request_queue address: {:x?}", rsp);  
        let error_code = asys::sys_new_proc_with_iommu_pass_mem(0,test_null_driver_ap as *const () as usize, rsp, 0x8000000000usize, range + size / 4096);
            if error_code != 0 {
                log::info!("sys_new_proc_with_iommu_pass_mem failed {:?}", error_code);
                return;
            }
        // log::info!("request_queue address: {:p}", &request_queue);   

        let size = core::mem::size_of::<DataBufferAllocWrapper>();
        let error_code = asys::sys_mmap(DATA_BUFFER_ADDR as usize, 0x0000_0000_0000_0002u64 as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_mmap for data_buffer failed {:?}", error_code);
            return;
        }
        
        let buff_ref:&mut DataBufferAllocWrapper = &mut*(DATA_BUFFER_ADDR as *mut DataBufferAllocWrapper);
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
        loop{
            let result = buff_ref.request_queue.try_pop();
            if result.is_none(){
                for i in 0.. EMPTY_QUEUE_SLEEP_CYCLE{
                    asm!("nop");
                }
            }else{
                // for i in 0..SIZE_OF_BUFFER{
                //     buff_ref.data_buffer[result.unwrap()][i] += 1;
                // }
                buff_ref.reply_queue.try_push(result.unwrap());
            }
        }
    }
}


#[no_mangle]
pub fn test_null_driver_with_batch_size_ap()-> ! {
    log::info!("hello from test_null_driver_with_batch_size_ap");

    unsafe{
        let size = core::mem::size_of::<DataBufferAllocWrapper>();
        let error_code = asys::sys_receive_pages(0,DATA_BUFFER_ADDR as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_receive_pages failed {:?}", error_code);
        }else{
            log::info!("data_buffer received by dom1");
        }   
    }

    let target = 10000000;
    let mut counter = 0;
        unsafe{
            let buff_ref:&mut DataBufferAllocWrapper = &mut*(DATA_BUFFER_ADDR as *mut DataBufferAllocWrapper);
            for i in 0..SIZE_OF_QUEUE{
                buff_ref.free_stack[buff_ref.len] = i;
                buff_ref.len = buff_ref.len + 1;
            }
            // log::info!("free_stack init done");
            let start = _rdtsc();
            while counter <= target{
                //push free stack into request queue
                // log::info!("counter: {:?}",counter);
                let mut current_batch = BATCH_SIZE;
                while current_batch != 0 {
                    let result = buff_ref.request_queue.try_push(buff_ref.free_stack[buff_ref.len-1]);
                    // log::info!("result: {:?} i: {:?}",result,free_stack[len-1]);
                    if result{
                        buff_ref.len = buff_ref.len -1;
                        current_batch -= 1;
                    }
                    

                }
                //pop reply queue to free stack
                while current_batch != BATCH_SIZE{
                    let result = buff_ref.reply_queue.try_pop();
                    if result.is_none(){
                        for i in 0.. EMPTY_QUEUE_SLEEP_CYCLE{
                            asm!("nop");
                        }
                    }else{
                        current_batch += 1;
                        counter = counter + 1;
                        buff_ref.free_stack[buff_ref.len] = result.unwrap();
                        buff_ref.len = buff_ref.len + 1;
                    }
                }
            }
            let end = _rdtsc();
            log::info!("null_driver cycles per request {:?}",(end-start) as usize /target);
        }

    loop {
        unsafe{asm!("nop");}
    }
}
pub fn test_null_driver_with_batch_size(){
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

        let new_stack = 0x8000000000usize + range * 4096;
        log::info!("allocating dom1 stack from {:x?}", new_stack);
        let size = 16 * 1024 * 1024;
        let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, size / 4096);
        if error_code != 0 {
            log::info!("sys_mmap for dom1 stack failed {:?}", error_code);
            return;
        }
        let rsp: usize = new_stack + size/2;
        let error_code = asys::sys_new_proc_with_iommu_pass_mem(0,test_null_driver_with_batch_size_ap as *const () as usize, rsp, 0x8000000000usize, range + size / 4096);
            if error_code != 0 {
                log::info!("sys_new_proc_with_iommu_pass_mem failed {:?}", error_code);
                return;
            }
        // log::info!("request_queue address: {:p}", &request_queue);   

        let size = core::mem::size_of::<DataBufferAllocWrapper>();
        let error_code = asys::sys_mmap(DATA_BUFFER_ADDR as usize, 0x0000_0000_0000_0002u64 as usize, size / 4096 + 1);
        if error_code != 0 {
            log::info!("sys_mmap for data_buffer failed {:?}", error_code);
            return;
        }
        
        let buff_ref:&mut DataBufferAllocWrapper = &mut*(DATA_BUFFER_ADDR as *mut DataBufferAllocWrapper);
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
        loop{
            let result = buff_ref.request_queue.try_pop();
            if result.is_none(){
                for i in 0.. EMPTY_QUEUE_SLEEP_CYCLE{
                    asm!("nop");
                }
            }else{
                // for i in 0..SIZE_OF_BUFFER{
                //     buff_ref.data_buffer[result.unwrap()][i] += 1;
                // }
                buff_ref.reply_queue.try_push(result.unwrap());
            }
        }
    }
}
