//! Mutexes, semaphores, and message queues.
//!
//! The objects live in memory that the C program provides, like POSIX
//! synchronization objects. Their layout is mirrored by opaque types in
//! `atmo_rt.h`. All blocking goes through [`crate::task`].
//!
//! The runtime runs its tasks in one kernel thread and switches between them
//! only inside its own calls, so an object needs no lock of its own.

use core::ptr;

use crate::mem;
use crate::sys::PAGE_SIZE;
use crate::task::{self, Slot, WaitQueue, Wake, PRIORITY_MIN};
use crate::time::FOREVER;

/// Results of the object calls, as the C interface returns them.
pub const OK: i32 = 0;
pub const TIMEOUT: i32 = 1;
pub const FULL: i32 = 2;
pub const EMPTY: i32 = 3;
pub const ERROR: i32 = -1;
pub const NOT_OWNER: i32 = -2;
pub const TOO_LARGE: i32 = -3;
pub const DESTROYED: i32 = -4;
pub const NO_MEMORY: i32 = -5;

// ---------------------------------------------------------------------------
// Mutex

/// A recursive mutex with priority inheritance.
///
/// While a task waits for a mutex, the owner runs at the priority of the most
/// urgent waiter if that is more urgent than its own. Unlocking passes the
/// mutex to the most urgent waiter.
#[repr(C)]
pub struct Mutex {
    /// The owner, or zero.
    owner: Slot,
    waiters: WaitQueue,
    /// How many times the owner has locked the mutex.
    depth: u32,
    /// The next mutex that the same task owns.
    next_owned: *mut Mutex,
}

/// The priority that a task must run at: its own, or that of the most urgent
/// task that waits for a mutex that it owns.
fn inherited_priority(slot: Slot) -> u8 {
    let mut priority = task::base_priority_of(slot);
    let mut m = task::owned(slot);
    while !m.is_null() {
        let mutex = unsafe { &*m };
        if let Some(waiter) = task::top_waiter_priority(&mutex.waiters) {
            priority = priority.min(waiter);
        }
        m = mutex.next_owned;
    }
    priority
}

/// Recomputes the running priority of a task, and of the owners of the
/// mutexes that it transitively waits for.
pub(crate) fn refresh_priority(slot: Slot) {
    let mut slot = slot;
    // A chain is no longer than the number of tasks unless there is a deadlock.
    for _ in 0..task::MAX_TASKS {
        task::set_running_priority(slot, inherited_priority(slot));
        let m = task::blocked_on(slot);
        if m.is_null() {
            return;
        }
        let owner = unsafe { (*m).owner };
        if owner == 0 {
            return;
        }
        slot = owner;
    }
}

fn own(m: *mut Mutex, slot: Slot) {
    let mutex = unsafe { &mut *m };
    mutex.owner = slot;
    mutex.depth = 1;
    mutex.next_owned = task::owned(slot);
    task::set_owned(slot, m);
    task::set_blocked_on(slot, ptr::null_mut());
}

fn disown(m: *mut Mutex, slot: Slot) {
    let mut at = task::owned(slot);
    if at == m {
        task::set_owned(slot, unsafe { (*m).next_owned });
    } else {
        while !at.is_null() {
            let next = unsafe { (*at).next_owned };
            if next == m {
                unsafe { (*at).next_owned = (*m).next_owned };
                break;
            }
            at = next;
        }
    }
    let mutex = unsafe { &mut *m };
    mutex.owner = 0;
    mutex.depth = 0;
    mutex.next_owned = ptr::null_mut();
}

#[no_mangle]
pub unsafe extern "C" fn art_mutex_init(m: *mut Mutex) {
    m.write(Mutex { owner: 0, waiters: WaitQueue::new(), depth: 0, next_owned: ptr::null_mut() });
}

#[no_mangle]
pub unsafe extern "C" fn art_mutex_lock(m: *mut Mutex) -> i32 {
    let me = task::current();
    let owner = (*m).owner;
    if owner == 0 {
        own(m, me);
        return OK;
    }
    if owner == me {
        (*m).depth += 1;
        return OK;
    }
    task::set_blocked_on(me, m);
    // Joining the queue first lets the owner inherit this task's priority.
    // `block_on` inserts by priority, so the order of the two steps does not
    // matter to the queue; the owner must be raised before this task stops.
    if task::priority_of(me) < task::priority_of(owner) {
        raise_owner_chain(owner, task::priority_of(me));
    }
    let wake = task::block_on(&raw mut (*m).waiters, FOREVER);
    task::set_blocked_on(me, ptr::null_mut());
    match wake {
        // The task that unlocked made this task the owner.
        Wake::Signal => OK,
        _ => DESTROYED,
    }
}

/// Raises an owner, and the owners that it waits for, to `priority`.
fn raise_owner_chain(owner: Slot, priority: u8) {
    let mut slot = owner;
    for _ in 0..task::MAX_TASKS {
        if task::priority_of(slot) <= priority {
            return;
        }
        task::set_running_priority(slot, priority);
        let m = task::blocked_on(slot);
        if m.is_null() {
            return;
        }
        slot = unsafe { (*m).owner };
        if slot == 0 {
            return;
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn art_mutex_unlock(m: *mut Mutex) -> i32 {
    let me = task::current();
    if (*m).owner != me {
        return NOT_OWNER;
    }
    if (*m).depth > 1 {
        (*m).depth -= 1;
        return OK;
    }
    disown(m, me);
    if let Some(next) = task::wake_first(&raw mut (*m).waiters, Wake::Signal) {
        own(m, next);
    }
    // This task no longer inherits from the waiters of the mutex.
    task::set_running_priority(me, inherited_priority(me));
    task::preempt();
    OK
}

/// Destroys a mutex. Tasks that wait for it stop waiting with an error.
#[no_mangle]
pub unsafe extern "C" fn art_mutex_destroy(m: *mut Mutex) {
    let owner = (*m).owner;
    if owner != 0 {
        disown(m, owner);
    }
    task::wake_all(&raw mut (*m).waiters, Wake::Destroyed);
    if owner != 0 {
        task::set_running_priority(owner, inherited_priority(owner));
    }
    task::preempt();
}

/// Whether the running task owns the mutex.
#[no_mangle]
pub unsafe extern "C" fn art_mutex_held(m: *const Mutex) -> bool {
    (*m).owner == task::current()
}

// ---------------------------------------------------------------------------
// Semaphore

/// A counting semaphore with a maximum count. A maximum of one makes a binary
/// semaphore.
#[repr(C)]
pub struct Sem {
    count: u32,
    max: u32,
    waiters: WaitQueue,
}

#[no_mangle]
pub unsafe extern "C" fn art_sem_init(s: *mut Sem, initial: u32, max: u32) {
    let max = max.max(1);
    s.write(Sem { count: initial.min(max), max, waiters: WaitQueue::new() });
}

/// Takes the semaphore. Waits until `deadline` if the count is zero; a
/// deadline of zero does not wait.
#[no_mangle]
pub unsafe extern "C" fn art_sem_take(s: *mut Sem, deadline: u64) -> i32 {
    if (*s).count > 0 {
        (*s).count -= 1;
        return OK;
    }
    if deadline == 0 {
        return TIMEOUT;
    }
    match task::block_on(&raw mut (*s).waiters, deadline) {
        // The task that gave passed its unit to this task, or flushed.
        Wake::Signal => OK,
        Wake::Timeout => TIMEOUT,
        Wake::Destroyed => DESTROYED,
    }
}

/// Gives the semaphore. The most urgent waiter gets the unit. At the maximum
/// count and without waiters, the call returns `FULL` and changes nothing.
#[no_mangle]
pub unsafe extern "C" fn art_sem_give(s: *mut Sem) -> i32 {
    if task::wake_first(&raw mut (*s).waiters, Wake::Signal).is_some() {
        task::preempt();
        return OK;
    }
    if (*s).count >= (*s).max {
        return FULL;
    }
    (*s).count += 1;
    OK
}

/// Releases every task that waits for the semaphore. The count does not
/// change.
#[no_mangle]
pub unsafe extern "C" fn art_sem_flush(s: *mut Sem) -> i32 {
    if task::wake_all(&raw mut (*s).waiters, Wake::Signal) != 0 {
        task::preempt();
    }
    OK
}

#[no_mangle]
pub unsafe extern "C" fn art_sem_count(s: *const Sem) -> u32 {
    (*s).count
}

/// Destroys a semaphore. Tasks that wait for it stop waiting with an error.
#[no_mangle]
pub unsafe extern "C" fn art_sem_destroy(s: *mut Sem) {
    if task::wake_all(&raw mut (*s).waiters, Wake::Destroyed) != 0 {
        task::preempt();
    }
}

// ---------------------------------------------------------------------------
// Message queue

/// A queue of messages of bounded size. Putting never waits.
#[repr(C)]
pub struct Queue {
    /// `depth` slots of `slot_size` bytes. A slot is a 4-byte length and the
    /// message.
    storage: *mut u8,
    slot_size: u32,
    /// The largest message in bytes.
    max_size: u32,
    depth: u32,
    head: u32,
    count: u32,
    readers: WaitQueue,
    /// Pages that the runtime mapped for `storage`.
    pages: u32,
}

const LENGTH_SIZE: usize = 4;

/// Makes a queue of `depth` messages of at most `max_size` bytes.
#[no_mangle]
pub unsafe extern "C" fn art_queue_init(q: *mut Queue, depth: u32, max_size: u32) -> i32 {
    if depth == 0 {
        return ERROR;
    }
    let slot_size = (max_size as usize + LENGTH_SIZE + 7) & !7;
    let bytes = match slot_size.checked_mul(depth as usize) {
        Some(bytes) => bytes,
        None => return NO_MEMORY,
    };
    let pages = bytes.div_ceil(PAGE_SIZE);
    let storage = match mem::alloc_pages(pages) {
        Some(addr) => addr as *mut u8,
        None => return NO_MEMORY,
    };
    q.write(Queue {
        storage,
        slot_size: slot_size as u32,
        max_size,
        depth,
        head: 0,
        count: 0,
        readers: WaitQueue::new(),
        pages: pages as u32,
    });
    OK
}

#[no_mangle]
pub unsafe extern "C" fn art_queue_put(q: *mut Queue, data: *const u8, size: usize) -> i32 {
    let queue = &mut *q;
    if size > queue.max_size as usize {
        return TOO_LARGE;
    }
    if queue.count == queue.depth {
        return FULL;
    }
    let index = (queue.head + queue.count) % queue.depth;
    let slot = queue.storage.add(index as usize * queue.slot_size as usize);
    (slot as *mut u32).write(size as u32);
    ptr::copy_nonoverlapping(data, slot.add(LENGTH_SIZE), size);
    queue.count += 1;
    if task::wake_first(&raw mut queue.readers, Wake::Signal).is_some() {
        task::preempt();
    }
    OK
}

/// Takes the oldest message. Waits until `deadline` if the queue is empty; a
/// deadline of zero does not wait. A message that does not fit in `capacity`
/// bytes stays in the queue and the call returns `TOO_LARGE`.
#[no_mangle]
pub unsafe extern "C" fn art_queue_get(
    q: *mut Queue,
    data: *mut u8,
    capacity: usize,
    size: *mut usize,
    deadline: u64,
) -> i32 {
    loop {
        if (*q).count > 0 {
            let queue = &mut *q;
            let slot = queue.storage.add(queue.head as usize * queue.slot_size as usize);
            let length = (slot as *const u32).read() as usize;
            if length > capacity {
                return TOO_LARGE;
            }
            ptr::copy_nonoverlapping(slot.add(LENGTH_SIZE), data, length);
            if !size.is_null() {
                size.write(length);
            }
            queue.head = (queue.head + 1) % queue.depth;
            queue.count -= 1;
            return OK;
        }
        if deadline == 0 {
            return EMPTY;
        }
        // Another task can take the message before this one runs, so the
        // queue is checked again after a wake.
        match task::block_on(&raw mut (*q).readers, deadline) {
            Wake::Signal => {}
            Wake::Timeout => return TIMEOUT,
            Wake::Destroyed => return DESTROYED,
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn art_queue_count(q: *const Queue) -> u32 {
    (*q).count
}

/// Destroys a queue. Tasks that wait for a message stop waiting with an error.
#[no_mangle]
pub unsafe extern "C" fn art_queue_destroy(q: *mut Queue) {
    let woke = task::wake_all(&raw mut (*q).readers, Wake::Destroyed);
    let queue = &mut *q;
    if queue.pages != 0 {
        mem::free_pages(queue.storage as usize, queue.pages as usize);
    }
    queue.storage = ptr::null_mut();
    queue.depth = 0;
    queue.count = 0;
    queue.pages = 0;
    if woke != 0 {
        task::preempt();
    }
}

// The C header declares the objects as arrays of 64-bit words.
const _: () = assert!(core::mem::size_of::<Mutex>() <= 24);
const _: () = assert!(core::mem::size_of::<Sem>() <= 16);
const _: () = assert!(core::mem::size_of::<Queue>() <= 40);
const _: () = assert!(PRIORITY_MIN == 255);
