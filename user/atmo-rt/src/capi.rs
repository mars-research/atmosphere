//! The C interface of the task calls. See `include/atmo_rt.h`.

use core::ffi::c_void;

use crate::sync::{ERROR, NO_MEMORY, OK};
use crate::task::{self, Entry, Error};
use crate::time;

fn code(result: Result<(), Error>) -> i32 {
    match result {
        Ok(()) => OK,
        Err(Error::NoMemory) => NO_MEMORY,
        Err(_) => ERROR,
    }
}

/// Creates a task. With a null `stack` the runtime maps the stack.
#[no_mangle]
pub unsafe extern "C" fn art_task_create(
    handle: *mut u32,
    entry: Option<Entry>,
    arg: *mut c_void,
    stack: *mut u8,
    stack_size: usize,
    priority: u8,
) -> i32 {
    let entry = match entry {
        Some(entry) if !handle.is_null() => entry,
        _ => return ERROR,
    };
    code(task::spawn(entry, arg, stack, stack_size, priority, handle))
}

#[no_mangle]
pub extern "C" fn art_task_exit() -> ! {
    task::exit_current()
}

#[no_mangle]
pub extern "C" fn art_task_delete(handle: u32) -> i32 {
    code(task::delete(handle))
}

#[no_mangle]
pub extern "C" fn art_task_self() -> u32 {
    task::current_handle()
}

#[no_mangle]
pub extern "C" fn art_task_yield() {
    task::yield_now()
}

/// Blocks the running task until the clock reaches `deadline`.
#[no_mangle]
pub extern "C" fn art_task_sleep_until(deadline: u64) {
    task::sleep_until(deadline)
}

/// Blocks the running task for `ns` nanoseconds.
#[no_mangle]
pub extern "C" fn art_task_sleep(ns: u64) {
    task::sleep_until(time::now().saturating_add(ns))
}

#[no_mangle]
pub extern "C" fn art_task_set_priority(handle: u32, priority: u8) -> i32 {
    code(task::set_priority(handle, priority))
}

#[no_mangle]
pub unsafe extern "C" fn art_task_get_priority(handle: u32, priority: *mut u8) -> i32 {
    match task::get_priority(handle) {
        Ok(p) => {
            priority.write(p);
            OK
        }
        Err(e) => code(Err(e)),
    }
}

#[no_mangle]
pub extern "C" fn art_task_set_tag(handle: u32, tag: usize) -> i32 {
    code(task::set_tag(handle, tag))
}

/// The tag of a task, or zero if the handle is not valid.
#[no_mangle]
pub extern "C" fn art_task_get_tag(handle: u32) -> usize {
    task::get_tag(handle).unwrap_or(0)
}

/// Whether a handle names a live task.
#[no_mangle]
pub extern "C" fn art_task_valid(handle: u32) -> bool {
    task::get_priority(handle).is_ok()
}

/// Lets the runtime notice deadlines that have passed. A task that runs for a
/// long time without another runtime call should call this.
#[no_mangle]
pub extern "C" fn art_poll() {
    task::poll()
}
