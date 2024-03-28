use core::arch::x86_64::_rdtsc;
use core::arch::asm;
use crate::*;


pub fn try_new_thread_ap(){
    log::info!("thread_1_hello_ap at {:p}", thread_1_hello_ap as *const ());
    unsafe {
        let error_code = asys::sys_new_endpoint(0);
            if error_code != 0 {
                log::info!("sys_new_endpoint failed {:?}", error_code);
                return;
            }
        let new_stack = 0xA000000000;
        let size = 16 * 1024 * 1024;
        let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, size / 4096);
        if error_code != 0 {
            log::info!("sys_mmap failed {:?}", error_code);
            return;
        }

        let rsp: usize = (new_stack + size) & !(4096 - 1);

        let error_code = asys::sys_new_thread(0,thread_1_hello_ap as *const () as usize, rsp);
        if error_code != 0 {
            log::info!("sys_new_thread failed {:?}", error_code);
            return;
        }
    }
}

pub fn test_proc_pingpong(){
    unsafe {
        let error_code = asys::sys_new_endpoint(0);
            if error_code != 0 {
                log::info!("sys_new_endpoint failed {:?}", error_code);
                return;
            }
        let mut range = 0;
        loop{
            let (pa,perm) = asys::sys_mresolve(0x8000000000usize + range * 4096);
            log::info!("va:{:x?}, pa:{:x?}, perm:{:?}", 0x8000000000usize + range * 4096, pa, perm);
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
            log::info!("sys_mmap failed {:?}", error_code);
            return;
        }
        let rsp: usize = (new_stack + size) & !(4096 - 1);
        let error_code = asys::sys_new_proc_with_iommu_pass_mem(0,dom_1_main as *const () as usize, rsp, 0x8000000000usize, range + size / 4096);
            if error_code != 0 {
                log::info!("sys_new_proc_with_iommu_pass_mem failed {:?}", error_code);
                return;
            }

        let iter = 100000;
        unsafe{
            let start = _rdtsc();
            for i in 0..iter{
                let error_code = asys::sys_send_empty(0);
                // log::info!("pong");
                if error_code != 0 {
                    log::info!("sys_send_empty failed {:?}", error_code);
                    return;
                }
            }
            let end = _rdtsc();
            log::info!("pingpong between process using send/receive syscall {:?}",(end-start) as usize /iter);
        }
    }
}

pub fn test_null_syscall(){
    unsafe {
        let error_code = asys::sys_new_endpoint(0);
            if error_code != 0 {
                log::info!("sys_new_endpoint failed {:?}", error_code);
                return;
            }
        let iter = 50000;
            let start = _rdtsc();
            for i in 0..iter{
                let error_code = asys::sys_send_empty_no_wait(0);
                if error_code != 5 {
                    log::info!("sys_send_empty_no_wait failed {:?}", error_code);
                    return;
                }
            }
            let end = _rdtsc();
            log::info!("send no wait cycle per syscall {:?}",(end-start) as usize /iter);
        }
}

pub fn test_new_thread(){
    unsafe {
    let error_code = asys::sys_new_endpoint(0);
        if error_code != 0 {
            log::info!("sys_new_endpoint failed {:?}", error_code);
            return;
        }
    let iter = 249;
        let start = _rdtsc();
        for i in 0..iter{
            let error_code = asys::sys_new_thread(0,0,0);
            if error_code != 0 {
                log::info!("sys_new_thread failed {:?}", error_code);
                return;
            }
        }
        let end = _rdtsc();
        log::info!("new thread cycle per syscall {:?}",(end-start) as usize /iter);
    }
}

pub fn test_new_proc(){
    unsafe {
    let error_code = asys::sys_new_endpoint(0);
        if error_code != 0 {
            log::info!("sys_new_endpoint failed {:?}", error_code);
            return;
        }
    let iter = 4095;
        let start = _rdtsc();
        for i in 0..iter{
            let error_code = asys::sys_new_proc(0,0);
            if error_code != 0 {
                log::info!("sys_new_proc failed {:?}", error_code);
                return;
            }
        }
        let end = _rdtsc();
        log::info!("new proc cycle per syscall {:?}",(end-start) as usize /iter);
    }
}

pub fn test_new_endpoint(){
    let iter = 128;
    unsafe {
        let start = _rdtsc();
        for i in 0..iter{
            let error_code = asys::sys_new_endpoint(i);
            if error_code != 0 {
                log::info!("sys_new_endpoint failed {:?}", error_code);
                return;
            }
        }
        let end = _rdtsc();
        log::info!("new endpoint cycle per syscall {:?}",(end-start) as usize /iter);
    }
}

pub fn test_mmap(){
    let iter = 50000;
    unsafe {
        let start = _rdtsc();
        for i in 0..iter{
            let error_code = asys::sys_mmap(0xA000000000 + 4096 * i, 0x0000_0000_0000_0002u64 as usize, 1);
            if error_code != 0 {
                log::info!("sys_mmap failed {:?}", error_code);
                return;
            }
        }
        let end = _rdtsc();
        log::info!("mmap cycle per syscall {:?}",(end-start) as usize /iter);
    }
}

pub fn test_pingpong(){
    log::info!("thread_1_main at {:p}", thread_1_main as *const ());
    unsafe {
        let error_code = asys::sys_new_endpoint(0);
            if error_code != 0 {
                log::info!("sys_new_endpoint failed {:?}", error_code);
                return;
            }
        let new_stack = 0xA000000000;
        let size = 16 * 1024 * 1024;
        let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, size / 4096);
        if error_code != 0 {
            log::info!("sys_mmap failed {:?}", error_code);
            return;
        }

        let rsp: usize = (new_stack + size) & !(4096 - 1);

        let error_code = asys::sys_new_thread(0,thread_1_main as *const () as usize, rsp);
        if error_code != 0 {
            log::info!("sys_new_thread failed {:?}", error_code);
            return;
        }
        let iter = 100000;
        unsafe{
            let start = _rdtsc();
            for i in 0..iter{
                let error_code = asys::sys_send_empty(0);
                // log::info!("pong");
                if error_code != 0 {
                    log::info!("sys_new_thread failed {:?}", error_code);
                    return;
                }
            }
            let end = _rdtsc();
            log::info!("pingpong between threads using send/receive syscall {:?}",(end-start) as usize /iter);
        }

    }
}


