use astd::boot::PhysicalMemoryType;
use astd::heapless::Vec as ArrayVec;
use astd::sync::Mutex;
use verified::define::NUM_CPUS;
use core::arch::asm;
use core::arch::x86_64::_rdtsc;
use core::mem::size_of;
use verified::kernel::Kernel;
use verified::define as vdefine;
use verified::trap::Registers as vRegisters;
use crate::bridge::Bridge;
use verified::bridge::SwitchDecision;
use verified::bridge::TrustedBridge;
use crate::cpu;
static KERNEL: Mutex<Option<Kernel>> = Mutex::new(None);

use vstd::prelude::*;

use verified::process_manager::spec_proof::ProcessManager;
use verified::memory_manager::MemoryManager;
use verified::allocator::page_allocator_spec_impl::PageAllocator;
use verified::process_manager::container::Container;
use verified::process_manager::process::Process;
use verified::process_manager::thread::Thread;
use verified::process_manager::endpoint::Endpoint;
use verified::array_vec::ArrayVec as vArrayVec;
use verified::pagetable::pagemap::PageMap;
use verified::define::PagePerm4k;
use verified::va_range::VaRange4K as vVaRange4K;

use vstd::simple_pptr::PointsTo;

trait PhysicalMemoryTypeExt {
    fn to_verified_page_state(&self) -> vdefine::PageState;
}

impl PhysicalMemoryTypeExt for PhysicalMemoryType {
    fn to_verified_page_state(&self) -> vdefine::PageState {
        match self {
            Self::Available => vdefine::PageState::Free4k,
            Self::Domain => vdefine::PageState::Mapped4k,
            Self::PageTable => vdefine::PageState::Allocated4k,
            Self::Kernel | Self::Reserved => vdefine::PageState::Unavailable4k,
        }
    }
}

pub fn kernel_test() {
    log::info!("hello from kernel");
}

pub fn kernel_new() {
    // log::info!("kernel size={:?}", size_of::<Kernel>());
    // log::info!("proc_man size={:?}", size_of::<ProcessManager>());
    // log::info!("mmu_man size={:?}", size_of::<MemoryManager>());
    // log::info!("page_alloc size={:?}", size_of::<PageAllocator>());

    log::trace!("testing kernel obj size");
    log::info!("container size={:?}", size_of::<Container>());
    if size_of::<Container>() > 4096 {
        panic!("Container size is over the page limit!")
    }
    log::info!("process size={:?}", size_of::<Process>());
    if size_of::<Process>() > 4096 {
        panic!("Process size is over the page limit!")
    }
    log::info!("thread size={:?}", size_of::<Thread>());
    if size_of::<Thread>() > 4096 {
        panic!("Thread size is over the page limit!")
    }
    log::info!("endpoint size={:?}", size_of::<Endpoint>());
    if size_of::<Endpoint>() > 4096 {
        panic!("Thread size is over the page limit!")
    }
    log::trace!("Kernel objects are within page limit");
    let mut my_int = KERNEL.lock();
    *my_int = Some(Kernel::new());
}

pub fn kernel_init(
    boot_page_ptrs: &ArrayVec<(u64, PhysicalMemoryType), { 4 * 1024 * 1024 }>,
    dom0_pagetable_ptr: usize,
    kernel_pml4_entry_ptr: usize,
) {

    let mut boot_pages = vArrayVec::<(vdefine::PageState, usize), { vdefine::NUM_PAGES }>::new();
    let mut i = 0;

    let mut dom_0_container_ptr = 0;
    let mut dom_0_proc_ptr = 0;
    let mut dom_0_thread_ptr = 0;

    //convert memeory info from the bootloader to something verified kernel can understand
    while i !=  vdefine::NUM_PAGES {
        boot_pages.push((
            boot_page_ptrs[i].1.to_verified_page_state(),
            boot_page_ptrs[i].0 as usize,
        ));
        i = i + 1;
    }

    //get a free page and convert it to the first container.
    for i in 0.. vdefine::NUM_PAGES{
        if boot_pages.get(i).0 == vdefine::PageState::Free4k{
            boot_pages.set(i, (vdefine::PageState::Allocated4k, boot_pages.get(i).1));
            dom_0_container_ptr = boot_pages.get(i).1;
            break;
        }
    }

    //get a free page and convert it to the first process.
    for i in 0.. vdefine::NUM_PAGES{
        if boot_pages.get(i).0 == vdefine::PageState::Free4k{
            boot_pages.set(i, (vdefine::PageState::Allocated4k, boot_pages.get(i).1));
            dom_0_proc_ptr = boot_pages.get(i).1;
            break;
        }
    }

    //get a free page and convert it to the first thread.
    for i in 0.. vdefine::NUM_PAGES{
        if boot_pages.get(i).0 == vdefine::PageState::Free4k{
            boot_pages.set(i, (vdefine::PageState::Allocated4k, boot_pages.get(i).1));
            dom_0_thread_ptr = boot_pages.get(i).1;
            break;
        }
    }

    // log::info!("dom_0_container_ptr {:x?}",dom_0_container_ptr);
    // log::info!("dom_0_proc_ptr {:x?}",dom_0_proc_ptr);
    // log::info!("dom_0_thread_ptr {:x?}",dom_0_thread_ptr);

    let mut dom0_pt_regs = vRegisters::new_empty();
    dom0_pt_regs.r15 = 233;

    let page_perm_0: Tracked<PagePerm4k> = Tracked::assume_new();
    let page_perm_1: Tracked<PagePerm4k> = Tracked::assume_new();
    let page_perm_2: Tracked<PagePerm4k> = Tracked::assume_new();
    let dom0_page_map_perm: Tracked<PointsTo<PageMap>> = Tracked::assume_new();

    KERNEL.lock().as_mut().unwrap().kernel_init(
        dom_0_container_ptr,
        dom_0_proc_ptr,
        dom_0_thread_ptr,
        &mut boot_pages,
        dom0_pagetable_ptr,
        kernel_pml4_entry_ptr,
        page_perm_0,
        page_perm_1,
        page_perm_2,
        dom0_page_map_perm
    );

    let dom0_retstruc = KERNEL
    .lock()
    .as_mut()
    .unwrap()
    .schedule_idle_cpu(0, &mut dom0_pt_regs);

    log::info!("dom0 is running on CPU 0");
    let pcid_dom0 = 0;
    let cr3 = dom0_pagetable_ptr | vdefine::PCID_ENABLE_MASK | pcid_dom0;
    Bridge::set_cr3(cr3 as u64);

    log::trace!("Kernel init success!! XD");
}

pub extern "C" fn sys_mmap(va:usize, perm_bits:usize, range:usize, regs: &mut vRegisters) {
    let cpu_id = cpu::get_cpu_id();
    let mut kernel = KERNEL.lock();
    let thread_info = kernel.as_mut().unwrap().get_current_cpu_info(cpu_id);

    let ret_struc =  kernel.as_mut().unwrap().syscall_mmap(
        thread_info.0.unwrap(),
        vVaRange4K::new(va, range)
    );
    regs.rax = 
        if ret_struc.is_error(){
            log::info!{"sys_mmap failed"};
            1
        }else{
            0
        };
    Bridge::set_switch_decision(SwitchDecision::NoSwitching);
}

/// This syscall does a send and runs the blocked thread if it belongs to the same container. 
pub extern "C" fn sys_send_empty_try_schedule(endpoint_index:usize, _:usize, _:usize, regs: &mut vRegisters) {
    // log::info!("sys_send_empty_try_schedule regs at entrace: {:x?}", regs);
    let cpu_id = cpu::get_cpu_id();
    let mut kernel = KERNEL.lock();
    let thread_info = kernel.as_mut().unwrap().get_current_cpu_info(cpu_id);
    let sender_thread_ptr = thread_info.0.unwrap();
    let sender_proc_ptr = thread_info.0.unwrap();
    let sender_cr3: usize = thread_info.3.unwrap();
    let sender_pcid = thread_info.4.unwrap();
    let syscall_ret = kernel.as_mut().unwrap().syscall_send_empty_try_schedule(cpu_id, sender_thread_ptr, endpoint_index, regs);
    if syscall_ret.pcid.unwrap() != sender_pcid{
        Bridge::set_cr3((syscall_ret.cr3.unwrap() | syscall_ret.pcid.unwrap() | vdefine::PCID_ENABLE_MASK) as u64);
    }

    Bridge::set_switch_decision(SwitchDecision::SwitchToClean);
}

/// Resolve VA to PA.
pub extern "C" fn sys_resolve(va:usize,_:usize, _:usize, regs: &mut vRegisters){
    let cpu_id = cpu::get_cpu_id();    
    let mut kernel = KERNEL.lock();
    let thread_info = kernel.as_ref().unwrap().get_current_cpu_info(cpu_id);
    let thread_ptr = thread_info.0.unwrap();
    let ret_struc = kernel.as_ref().unwrap().syscall_resolve_va(
        thread_ptr,
        vVaRange4K::new(va, 1),
    );
    match ret_struc.error_code{
        vdefine::RetValueType::SuccessPairUsize { value1, value2 } => {
            regs.rax = value1 as u64;
        },
        _ => {
            regs.rax = 1;
        },
    }
    Bridge::set_switch_decision(SwitchDecision::NoSwitching);
}

pub extern "C" fn sys_resolve_io(va:usize,_:usize, _:usize, regs: &mut vRegisters){
    let cpu_id = cpu::get_cpu_id();    
    let mut kernel = KERNEL.lock();
    let thread_info = kernel.as_ref().unwrap().get_current_cpu_info(cpu_id);
    let thread_ptr = thread_info.0.unwrap();
    let ret_struc = kernel.as_ref().unwrap().syscall_io_resolve_va(
        thread_ptr,
        vVaRange4K::new(va, 1),
    );
    match ret_struc.error_code{
        vdefine::RetValueType::SuccessPairUsize { value1, value2 } => {
            regs.rax = value1 as u64;
        },
        _ => {
            regs.rax = 1;
        },
    }
    Bridge::set_switch_decision(SwitchDecision::NoSwitching);
}


pub extern "C" fn sys_new_endpoint(endpoint_index:usize, _:usize, _:usize, regs: &mut vRegisters) {
    let cpu_id = cpu::get_cpu_id();
    let mut kernel = KERNEL.lock();
    let thread_info = kernel.as_mut().unwrap().get_current_cpu_info(cpu_id);
    let ret_struc =  kernel.as_mut().unwrap().syscall_new_endpoint(
        thread_info.0.unwrap(),
        endpoint_index,
    );
    regs.rax = 
        if ret_struc.is_error(){
            log::info!{"sys_new_endpoint failed"};
            1
        }else{
            0
        };
    Bridge::set_switch_decision(SwitchDecision::NoSwitching);
}

/// create a new process, pass an endpoint, and pass some physical pages
pub fn sys_new_proc(endpoint_index:usize, ip:usize, sp:usize, regs: &mut vRegisters, va:usize, range:usize) {
    let cpu_id = cpu::get_cpu_id();
    let mut kernel = KERNEL.lock();
    let thread_info = kernel.as_mut().unwrap().get_current_cpu_info(cpu_id);
    let mut new_proc_pt_regs = *regs;
    new_proc_pt_regs.rip = ip as u64;
    new_proc_pt_regs.rsp = sp as u64;
    log::info!{"range {:#?}", range};
    let ret_struc = kernel.as_mut().unwrap().syscall_new_proc_with_endpoint(
        thread_info.0.unwrap(),
        endpoint_index,
        &new_proc_pt_regs,
        vVaRange4K::new(va, range)
    );
    regs.rax = 
        if ret_struc.is_error(){
            log::info!{"sys_new_proc failed"};
            1
        }else{
            0
        };
    Bridge::set_switch_decision(SwitchDecision::NoSwitching);
}

// pub fn sys_new_proc_with_iommu(endpoint_index:usize, ip:usize, sp:usize,regs: &mut vRegisters) -> usize{
//     let cpu_id = cpu::get_cpu_id();
//     let new_proc_pt_regs = vRegisters::new_empty();
//     let ret_struc =  KERNEL.lock().as_mut().unwrap().syscall_new_proc_with_iommu(
//         cpu_id,
//         endpoint_index,
//         new_proc_pt_regs,
//     );
//     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
//     ret_struc.0.error_code
// }

/// create a new thread and pass an endpoint
pub extern "C" fn sys_new_thread(endpoint_index:usize, ip:usize, sp:usize, regs: &mut vRegisters){
    let cpu_id = cpu::get_cpu_id();
    let mut new_thread_pt_regs = regs.clone();
    new_thread_pt_regs.rip = ip as u64;
    new_thread_pt_regs.rsp = sp as u64;
    let mut kernel = KERNEL.lock();
    let thread_info = kernel.as_ref().unwrap().get_current_cpu_info(cpu_id);
    let ret_struc =  kernel.as_mut().unwrap().syscall_new_thread_with_endpoint(
        thread_info.0.unwrap(),
        endpoint_index,
        &new_thread_pt_regs,
    );
    Bridge::set_switch_decision(SwitchDecision::NoSwitching);
        regs.rax = 
        if ret_struc.is_error(){
            log::info!{"sys_new_thread failed"};
            1
        }else{
            0
        };
}

// pub fn sys_send_empty_no_wait(endpoint_index:usize,_:usize, _:usize, regs: &mut vRegisters){
//     let cpu_id = cpu::get_cpu_id();
//     let mut kernel = KERNEL.lock();
//     let ret_struc =  kernel.as_mut().unwrap().syscall_send_empty_no_wait(
//         cpu_id,
//         endpoint_index,
//     );
//     drop(kernel);
//     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
//     regs.rax = ret_struc.error_code as u64;
// }

// pub extern "C" fn sys_send_empty(endpoint_index:usize, _:usize, _:usize, regs: &mut vRegisters){
//     // log::info!("regs {:x?}", regs);
//     let cpu_id = cpu::get_cpu_id();
//     let mut kernel = KERNEL.lock();
//     let ret_struc =  kernel.as_mut().unwrap().syscall_send_empty_wait(
//         cpu_id,
//         regs,
//         endpoint_index,
//     );
//     drop(kernel);
//     if ret_struc.0.error_code == vdefine::NO_NEXT_THREAD {
//         loop{
//             log::info!("no next thread, spin the CPU. TODO: enter the scheduling routine");
//         }
//     }else{
//         if ret_struc.1.is_none(){
//             log::info!("fatal: syscall coming from null cpu");
//         }else{
//             if ret_struc.1.unwrap().1 != ret_struc.0.cr3 {
//                 Bridge::set_cr3((ret_struc.0.cr3 | ret_struc.0.pcid | vdefine::PCID_ENABLE_MASK) as u64);
//             }

//             if ret_struc.0.error_code == vdefine::NO_ERROR_CODE{
//                 Bridge::set_switch_decision(SwitchDecision::SwitchToPreempted);
//             }else{
                
//                 regs.rax = ret_struc.0.error_code as u64;
                
//                 if ret_struc.1.unwrap().2 != ret_struc.0.thread_ptr{
//                     Bridge::set_switch_decision(SwitchDecision::SwitchToClean);
//                 }else{
//                     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
//                 }
//             }
//         }
//     }
// }

/// This syscall does a receive and block caller thread is possible.
/// Once the cpu becomes idel, try to schedule a new thread.
/// This syscall currently assumes there's always threads to run. 
/// @Xiangdong fix this ^
pub extern "C" fn sys_receive_empty(endpoint_index:usize, _:usize, _:usize, regs: &mut vRegisters){
    // log::info!{
    //     "hello from sys_receive_empty"
    // };
    // log::info!("sys_receive_empty regs at entrance: \n{:x?}", regs);
    let cpu_id = cpu::get_cpu_id();
    let mut kernel = KERNEL.lock();
    let thread_info_op = kernel.as_mut().unwrap().get_current_cpu_info(cpu_id);
    let pcid = thread_info_op.4.unwrap();
    //     log::info!{
    //     "thread_info_op {:#?}",
    //     thread_info_op
    // };
    let thread_ptr = thread_info_op.0.unwrap();
    let ret_struc =  kernel.as_mut().unwrap().syscall_receive_empty_block(
        thread_ptr,
        endpoint_index,
        &regs,
    );
    // log::info!{"ret_struc:
    // is_error: {:#?},
    // pcid: {:#?}
    // cr3: {:#?}
    // switchdecision: {:#?}", ret_struc.is_error(), ret_struc.pcid, ret_struc.cr3, ret_struc.switch_decision};
    if matches!(ret_struc.switch_decision, verified::define::SwitchDecision::NoThread){
        let sche_ret = kernel.as_mut().unwrap().schedule_idle_cpu(cpu_id, regs);
    //     log::info!{"sche_ret:
    // is_error: {:#?},
    // pcid: {:#?}
    // cr3: {:#?}
    // switchdecision: {:x?}", sche_ret.is_error(), sche_ret.pcid, sche_ret.cr3, sche_ret.switch_decision};
        if pcid != sche_ret.pcid.unwrap(){
            Bridge::set_cr3((sche_ret.cr3.unwrap() | sche_ret.pcid.unwrap() | vdefine::PCID_ENABLE_MASK) as u64);
        }
    }
    
    // log::info!("sys_receive_empty regs before return: {:x?}", regs);
    
    Bridge::set_switch_decision(SwitchDecision::SwitchToClean);
}

// pub extern "C" fn sys_new_proc_with_iommu_pass_mem(endpoint_index:usize, ip:usize, sp:usize, regs: &mut vRegisters, va:usize, range:usize){
//     let cpu_id = cpu::get_cpu_id();
//     let mut new_proc_pt_regs = *regs;
//     new_proc_pt_regs.rip = ip as u64;
//     new_proc_pt_regs.rsp = sp as u64;
//     let ret_struc =  KERNEL.lock().as_mut().unwrap().syscall_new_proc_with_iommu_pass_mem(
//         cpu_id,
//         endpoint_index,
//         new_proc_pt_regs,
//         va,
//         range
//     );
//     regs.rax = ret_struc.0.error_code as u64;
// }

// pub extern "C" fn sched_get_next_thread(regs: &mut vRegisters) -> bool{
//     let cpu_id = cpu::get_cpu_id();
//     let mut kernel = KERNEL.lock();
//     let thread_info_op = kernel.as_mut().unwrap().until_get_current_thread_info(cpu_id);
//     let ret_struc =  kernel.as_mut().unwrap().kernel_idle_pop_sched(
//         cpu_id,
//         regs,

//     );
//     drop(kernel);
//     if ret_struc.error_code == vdefine::CPU_ID_INVALID{
//         false
//     }else if ret_struc.error_code == vdefine::CPU_NO_IDLE{
//         false
//     }else if ret_struc.error_code == vdefine::SCHEDULER_EMPTY{
//         false
//     }else{
//         if thread_info_op.is_none(){
//             log::info!("cpu {:?} switching to a new thread/process {:x?} trap frame {:x?} cr3 {:x?}", cpu::get_cpu_id(),ret_struc,regs,ret_struc.cr3 | ret_struc.pcid | vdefine::PCID_ENABLE_MASK);

//             // Bridge::set_cr3((ret_struc.cr3 | ret_struc.pcid | vdefine::PCID_ENABLE_MASK) as u64);

//             // let cr3: u64;
//             // unsafe { asm!("mov {cr3}, cr3", cr3 = out(reg) cr3); }
//             Bridge::set_cr3((ret_struc.cr3 | ret_struc.pcid | vdefine::PCID_ENABLE_MASK) as u64 as u64);
//             // log::info!("cr3 {:x?}", cr3);

//             if ret_struc.error_code == vdefine::NO_ERROR_CODE{
//                 Bridge::set_switch_decision(SwitchDecision::SwitchToPreempted);
//             }else{

//                 regs.rax = ret_struc.error_code as u64;

//                 Bridge::set_switch_decision(SwitchDecision::SwitchToClean);

//             }

//         }else{
//             if thread_info_op.unwrap().1 != ret_struc.cr3 {

//                 Bridge::set_cr3((ret_struc.cr3 | ret_struc.pcid | vdefine::PCID_ENABLE_MASK) as u64);
//             }

//             if ret_struc.error_code == vdefine::NO_ERROR_CODE{
//                 Bridge::set_switch_decision(SwitchDecision::SwitchToPreempted);
//             }else{

//                 regs.rax = ret_struc.error_code as u64;
                
//                 if thread_info_op.unwrap().2 != ret_struc.thread_ptr{
//                     Bridge::set_switch_decision(SwitchDecision::SwitchToClean);
//                 }else{
//                     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
//                 }
//             }
//         }
//         true
//     }
// }

// pub extern "C" fn sys_receive_pages(endpoint_index:usize, va:usize, range:usize, regs: &mut vRegisters){
//     let cpu_id = cpu::get_cpu_id();
//     let mut kernel = KERNEL.lock();
//     let thread_info_op = kernel.as_mut().unwrap().until_get_current_thread_info(cpu_id);
//     // log::info!("cpu_list addr {:p}",&(kernel.as_ref().unwrap().cpu_list.ar));
//     // log::info!("sys_receive_pagestrap frame {:x?} thead_info {:x?} thread{:x?}",regs,thread_info_op,kernel.as_mut().unwrap().cpu_list.ar[cpu_id].current_t, );
//     let ret_struc =  kernel.as_mut().unwrap().syscall_receive_pages_wait(
//         cpu_id,
//         regs,
//         endpoint_index,
//         va,
//         range
//     );
//     drop(kernel);
//     if ret_struc.error_code == vdefine::NO_NEXT_THREAD {
//         loop{
//             unsafe{
//                 let has_next_thread = sched_get_next_thread(regs);
//                 if has_next_thread == false{
//                     for i in 0..1000{
//                         asm!("nop");
//                     }
//                 }else{
//                     break;
//                 }
//             }
//         }
//     }else{
//         if thread_info_op.is_none(){
//             log::info!("fatal: syscall coming from null cpu");
//         }else{
//             if thread_info_op.unwrap().1 != ret_struc.cr3 {
//                 Bridge::set_cr3((ret_struc.cr3 | ret_struc.pcid | vdefine::PCID_ENABLE_MASK) as u64);
//             }

//             if ret_struc.error_code == vdefine::NO_ERROR_CODE{
//                 Bridge::set_switch_decision(SwitchDecision::SwitchToPreempted);
//             }else{
                
//                 regs.rax = ret_struc.error_code as u64;

//                 if thread_info_op.unwrap().2 != ret_struc.thread_ptr{
//                     Bridge::set_switch_decision(SwitchDecision::SwitchToClean);
//                 }else{
//                     // log::info!("sys_receive_pages NoSwitching trap frame {:x?}",regs);
//                     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
//                 }
//             }
//         }
//     }
// }

// pub extern "C" fn sys_send_pages_no_wait(endpoint_index:usize, va:usize, range:usize, regs: &mut vRegisters){
//     // log::info!("regs {:x?}", regs);
//     let cpu_id = cpu::get_cpu_id();
//     let mut kernel = KERNEL.lock();
//     // log::info!("sys_send_pages_no_wait frame {:x?} thead_info {:x?}",regs,kernel.as_mut().unwrap().cpu_list.ar[0].current_t, );
//     let thread_info_op = kernel.as_mut().unwrap().until_get_current_thread_info(0);
//     // log::info!("sys_send_pages_no_wait frame {:x?} thead_info {:x?} thread{:x?}",regs,thread_info_op,kernel.as_mut().unwrap().cpu_list.ar[0].current_t, );
//     let ret_struc =  kernel.as_mut().unwrap().syscall_send_pages_no_wait(
//         cpu_id,
//         endpoint_index,
//         va,
//         range,
//     );
//     drop(kernel);
//     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
//     regs.rax = ret_struc.error_code as u64;
// }

// pub extern "C" fn sys_send_pages(endpoint_index:usize, va:usize, range:usize, regs: &mut vRegisters){
//     let cpu_id = cpu::get_cpu_id();
//     let mut kernel = KERNEL.lock();
//     let thread_info_op = kernel.as_mut().unwrap().until_get_current_thread_info(cpu_id);
//     let ret_struc =  kernel.as_mut().unwrap().syscall_send_pages_wait(
//         cpu_id,
//         regs,
//         endpoint_index,
//         va,
//         range
//     );
//     drop(kernel);
//     if ret_struc.error_code == vdefine::NO_NEXT_THREAD {
//         loop{
//             unsafe{
//                 let has_next_thread = sched_get_next_thread(regs);
//                 if has_next_thread == false{
//                     for i in 0..1000{
//                         asm!("nop");
//                     }
//                 }else{
//                     break;
//                 }
//             }
//         }
//     }else{
//         if thread_info_op.is_none(){
//             log::info!("fatal: syscall coming from null cpu");
//         }else{
//             if thread_info_op.unwrap().1 != ret_struc.cr3 {
//                 Bridge::set_cr3((ret_struc.cr3 | ret_struc.pcid | vdefine::PCID_ENABLE_MASK) as u64);
//             }

//             if ret_struc.error_code == vdefine::NO_ERROR_CODE{
//                 Bridge::set_switch_decision(SwitchDecision::SwitchToPreempted);
//             }else{
                
//                 regs.rax = ret_struc.error_code as u64;

//                 if thread_info_op.unwrap().2 != ret_struc.thread_ptr{
//                     Bridge::set_switch_decision(SwitchDecision::SwitchToClean);
//                 }else{
//                     Bridge::set_switch_decision(SwitchDecision::NoSwitching);
//                 }
//             }
//         }
//     }
// }

pub extern "C" fn sys_get_iommu_cr3(endpoint_index:usize, _:usize, _:usize, regs: &mut vRegisters){
    // log::info!("regs {:x?}", regs);
    
    Bridge::set_switch_decision(SwitchDecision::NoSwitching);
    let cpu_id = cpu::get_cpu_id();
    let mut kernel = KERNEL.lock();
    let thread_info = kernel.as_mut().unwrap().get_current_cpu_info(cpu_id);
    let proc_ptr = thread_info.1.unwrap();
    let ioid_op = kernel.as_ref().unwrap().proc_man.get_proc(proc_ptr).ioid;
    if let Some(ioid) = ioid_op{
        let io_cr3 =  kernel.as_ref().unwrap().mem_man.get_cr3_by_ioid(ioid);
        regs.rax = io_cr3 as u64;
    }else{
        log::debug!("sys_get_iommu_cr3 has no IOMMU");
        regs.rax = 233 as u64;
    }
}

pub extern "C" fn sys_iommu_mmap(va:usize, perm_bits:usize, range:usize, regs: &mut vRegisters) {
    let cpu_id = cpu::get_cpu_id();
    let mut kernel = KERNEL.lock();
    let thread_info = kernel.as_mut().unwrap().get_current_cpu_info(cpu_id);

    log::trace!{"iommaping from {:x?} with {:#?} pages", va, range};

    let address_shareable = kernel.as_ref().unwrap().check_address_space_va_range_shareable(        thread_info.1.unwrap(),
        &vVaRange4K::new(va, range));
     log::trace!{"address_shareable {:#?}", address_shareable};
    let io_address_shareable = kernel.as_ref().unwrap().check_io_space_va_range_free(
    thread_info.1.unwrap(),
        &vVaRange4K::new(va, range));
     log::trace!{"io_address_shareable {:#?}", io_address_shareable};
    let ret_struc =  kernel.as_mut().unwrap().syscall_mmap_to_iommu_table(
        thread_info.0.unwrap(),
        vVaRange4K::new(va, range)
    );
    regs.rax = 
        if ret_struc.is_error(){
            log::trace!{"sys_iommu_mmap failed"};
            1
        }else{
            0
        };
    Bridge::set_switch_decision(SwitchDecision::NoSwitching);
}