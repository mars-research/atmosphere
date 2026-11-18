//! Tasks and the scheduler.
//!
//! The runtime schedules its tasks itself, inside one kernel thread. The
//! public Atmosphere kernel runs one processor, does not deliver a timer
//! interrupt to the scheduler, and cannot wake a thread after a timeout, so
//! it cannot schedule the tasks of a real-time program by priority.
//!
//! Scheduling is by strict priority, 0 is the most urgent, and tasks of equal
//! priority run first come, first served. A task runs until it blocks, yields,
//! or makes a more urgent task ready. There is no time slicing: a timeout of
//! a more urgent task is noticed when the running task next enters the
//! runtime.
//!
//! The synchronization objects in [`crate::sync`] use only [`block_on`],
//! [`wake_first`], [`wake_all`], [`preempt`], and the priority calls. A
//! scheduler on kernel threads can replace this module behind those calls.

use core::cell::UnsafeCell;
use core::ffi::c_void;
use core::ptr;

use crate::mem;
use crate::sync::Mutex;
use crate::sys::PAGE_SIZE;
use crate::time::{self, FOREVER};

/// The most tasks that can exist at once, the first task included.
pub const MAX_TASKS: usize = 128;

/// The least urgent priority.
pub const PRIORITY_MIN: u8 = 255;

/// The smallest stack that the runtime gives a task.
const STACK_MIN: usize = 32 * 1024;

/// A task slot number plus one. Zero means no task.
pub type Slot = u16;
const NONE: Slot = 0;

/// Why a blocked task runs again.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Wake {
    /// Another task woke it.
    Signal,
    /// Its deadline passed.
    Timeout,
    /// The object that it waited on was destroyed.
    Destroyed,
}

/// Errors of the task calls.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Error {
    /// All task slots are in use.
    NoSlot,
    /// The stack could not be mapped.
    NoMemory,
    /// The handle does not name a live task.
    BadHandle,
    /// The argument is not valid.
    BadArgument,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum State {
    Free,
    Ready,
    Running,
    Blocked,
    /// The task has exited and still runs on its stack.
    Zombie,
}

/// A list of tasks, linked through `Task::next` and `Task::prev`.
///
/// The type is part of the C layout of the synchronization objects. All zero
/// is an empty list.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct WaitQueue {
    head: Slot,
    tail: Slot,
}

impl WaitQueue {
    pub const fn new() -> Self {
        Self { head: NONE, tail: NONE }
    }

    pub fn is_empty(&self) -> bool {
        self.head == NONE
    }
}

pub type Entry = unsafe extern "C" fn(*mut c_void);

struct Task {
    state: State,
    /// Incremented when the slot is freed, so that old handles stop working.
    generation: u16,
    /// The saved stack pointer while the task does not run.
    sp: usize,
    /// The priority that the program gave the task.
    base_priority: u8,
    /// The priority that the task runs at. It is more urgent than
    /// `base_priority` while a more urgent task waits for a mutex that this
    /// task owns.
    priority: u8,
    /// When a blocked task wakes by itself.
    deadline: u64,
    wake: Wake,
    next: Slot,
    prev: Slot,
    /// The wait queue that a blocked task is on, or null.
    queue: *mut WaitQueue,
    /// The mutex that the task waits for, or null.
    blocked_on: *mut Mutex,
    /// The mutexes that the task owns, linked through `Mutex::next_owned`.
    owned: *mut Mutex,
    stack_base: usize,
    stack_pages: usize,
    entry: Option<Entry>,
    arg: *mut c_void,
    /// A value that the program attaches to the task.
    tag: usize,
}

const EMPTY_TASK: Task = Task {
    state: State::Free,
    generation: 0,
    sp: 0,
    base_priority: PRIORITY_MIN,
    priority: PRIORITY_MIN,
    deadline: FOREVER,
    wake: Wake::Signal,
    next: NONE,
    prev: NONE,
    queue: ptr::null_mut(),
    blocked_on: ptr::null_mut(),
    owned: ptr::null_mut(),
    stack_base: 0,
    stack_pages: 0,
    entry: None,
    arg: ptr::null_mut(),
    tag: 0,
};

struct Sched {
    tasks: [Task; MAX_TASKS],
    /// One list of ready tasks per priority.
    ready: [WaitQueue; 256],
    /// Bit `p` is set when `ready[p]` is not empty.
    ready_bits: [u64; 4],
    current: Slot,
    /// The earliest deadline of a blocked task, or earlier.
    next_deadline: u64,
    /// A task that has exited and whose stack is still to be freed.
    zombie: Slot,
    started: bool,
}

struct Shared(UnsafeCell<Sched>);
// The runtime runs in one kernel thread.
unsafe impl Sync for Shared {}

static SCHED: Shared = Shared(UnsafeCell::new(Sched {
    tasks: [EMPTY_TASK; MAX_TASKS],
    ready: [WaitQueue::new(); 256],
    ready_bits: [0; 4],
    current: NONE,
    next_deadline: FOREVER,
    zombie: NONE,
    started: false,
}));

/// The scheduler state. No reference to it is held across a context switch.
fn sched() -> &'static mut Sched {
    unsafe { &mut *SCHED.0.get() }
}

fn task(s: &mut Sched, slot: Slot) -> &mut Task {
    &mut s.tasks[slot as usize - 1]
}

// ---------------------------------------------------------------------------
// Lists

fn list_push_back(s: &mut Sched, q: *mut WaitQueue, slot: Slot) {
    let q = unsafe { &mut *q };
    let tail = q.tail;
    {
        let t = task(s, slot);
        t.next = NONE;
        t.prev = tail;
    }
    if tail == NONE {
        q.head = slot;
    } else {
        task(s, tail).next = slot;
    }
    q.tail = slot;
}

fn list_push_front(s: &mut Sched, q: *mut WaitQueue, slot: Slot) {
    let q = unsafe { &mut *q };
    let head = q.head;
    {
        let t = task(s, slot);
        t.prev = NONE;
        t.next = head;
    }
    if head == NONE {
        q.tail = slot;
    } else {
        task(s, head).prev = slot;
    }
    q.head = slot;
}

/// Inserts a task before the first task that is less urgent, so that the list
/// stays ordered by priority and by arrival within a priority.
fn list_insert_by_priority(s: &mut Sched, q: *mut WaitQueue, slot: Slot) {
    let priority = task(s, slot).priority;
    let mut at = unsafe { (*q).head };
    while at != NONE && task(s, at).priority <= priority {
        at = task(s, at).next;
    }
    if at == NONE {
        list_push_back(s, q, slot);
        return;
    }
    let before = task(s, at).prev;
    {
        let t = task(s, slot);
        t.next = at;
        t.prev = before;
    }
    task(s, at).prev = slot;
    if before == NONE {
        unsafe { (*q).head = slot };
    } else {
        task(s, before).next = slot;
    }
}

fn list_remove(s: &mut Sched, q: *mut WaitQueue, slot: Slot) {
    let (prev, next) = {
        let t = task(s, slot);
        let links = (t.prev, t.next);
        t.prev = NONE;
        t.next = NONE;
        links
    };
    let q = unsafe { &mut *q };
    if prev == NONE {
        q.head = next;
    } else {
        task(s, prev).next = next;
    }
    if next == NONE {
        q.tail = prev;
    } else {
        task(s, next).prev = prev;
    }
}

// ---------------------------------------------------------------------------
// The ready lists

fn ready_queue(s: &mut Sched, priority: u8) -> *mut WaitQueue {
    &raw mut s.ready[priority as usize]
}

fn make_ready(s: &mut Sched, slot: Slot, front: bool) {
    let priority = {
        let t = task(s, slot);
        t.state = State::Ready;
        t.queue = ptr::null_mut();
        t.deadline = FOREVER;
        t.priority
    };
    let q = ready_queue(s, priority);
    if front {
        list_push_front(s, q, slot);
    } else {
        list_push_back(s, q, slot);
    }
    s.ready_bits[priority as usize / 64] |= 1 << (priority % 64);
}

fn unready(s: &mut Sched, slot: Slot) {
    let priority = task(s, slot).priority;
    let q = ready_queue(s, priority);
    list_remove(s, q, slot);
    if unsafe { (*q).is_empty() } {
        s.ready_bits[priority as usize / 64] &= !(1 << (priority % 64));
    }
}

/// The priority of the most urgent ready task.
fn top_ready(s: &Sched) -> Option<u8> {
    for (i, bits) in s.ready_bits.iter().enumerate() {
        if *bits != 0 {
            return Some((i * 64) as u8 + bits.trailing_zeros() as u8);
        }
    }
    None
}

fn pop_ready(s: &mut Sched) -> Option<Slot> {
    let priority = top_ready(s)?;
    let slot = s.ready[priority as usize].head;
    unready(s, slot);
    Some(slot)
}

// ---------------------------------------------------------------------------
// Timeouts

/// Makes ready every blocked task whose deadline has passed.
fn expire(s: &mut Sched, now: u64) {
    if now < s.next_deadline {
        return;
    }
    let mut next = FOREVER;
    for i in 0..MAX_TASKS {
        let slot = i as Slot + 1;
        let (blocked, deadline, queue) = {
            let t = &s.tasks[i];
            (t.state == State::Blocked, t.deadline, t.queue)
        };
        if !blocked || deadline == FOREVER {
            continue;
        }
        if deadline <= now {
            if !queue.is_null() {
                list_remove(s, queue, slot);
            }
            task(s, slot).wake = Wake::Timeout;
            make_ready(s, slot, false);
        } else if deadline < next {
            next = deadline;
        }
    }
    s.next_deadline = next;
}

// ---------------------------------------------------------------------------
// Switching

/// Saves the callee-saved registers of the running task on its stack, stores
/// its stack pointer at `save`, and continues the task whose stack pointer is
/// `load`. Tasks use general-purpose registers only, so there is no other
/// state to save.
#[unsafe(naked)]
unsafe extern "C" fn switch_stacks(save: *mut usize, load: usize) {
    core::arch::naked_asm!(
        "push rbp",
        "push rbx",
        "push r12",
        "push r13",
        "push r14",
        "push r15",
        "mov [rdi], rsp",
        "mov rsp, rsi",
        "pop r15",
        "pop r14",
        "pop r13",
        "pop r12",
        "pop rbx",
        "pop rbp",
        "ret",
    )
}

/// The first code of a new task. `switch_stacks` returns into it.
#[unsafe(naked)]
unsafe extern "C" fn task_boot() -> ! {
    core::arch::naked_asm!(
        "and rsp, -16",
        "xor ebp, ebp",
        "call {main}",
        "ud2",
        main = sym task_main,
    )
}

extern "C" fn task_main() -> ! {
    after_switch();
    let (entry, arg) = {
        let s = sched();
        let current = s.current;
        let t = task(s, current);
        (t.entry, t.arg)
    };
    if let Some(entry) = entry {
        unsafe { entry(arg) };
    }
    exit_current()
}

/// Frees the stack of a task that exited before the last switch.
fn after_switch() {
    let s = sched();
    let zombie = s.zombie;
    if zombie != NONE && zombie != s.current {
        s.zombie = NONE;
        release_slot(s, zombie);
    }
}

fn release_slot(s: &mut Sched, slot: Slot) {
    let t = task(s, slot);
    if t.stack_pages != 0 {
        mem::free_pages(t.stack_base, t.stack_pages);
    }
    let generation = t.generation.wrapping_add(1);
    *t = EMPTY_TASK;
    t.generation = generation;
}

/// Runs the most urgent ready task. The caller has already taken the current
/// task out of the running state: it is ready and queued, blocked, or a
/// zombie. Waits here while no task is ready.
fn reschedule() {
    let (prev, next) = {
        let s = sched();
        let prev = s.current;
        let next = loop {
            expire(s, time::now());
            if let Some(next) = pop_ready(s) {
                break next;
            }
            // Nothing to run until a deadline passes. Nothing else can make
            // a task ready: there are no interrupts.
            core::hint::spin_loop();
        };
        task(s, next).state = State::Running;
        s.current = next;
        (prev, next)
    };
    if next != prev {
        let (save, load) = {
            let s = sched();
            (&raw mut task(s, prev).sp, task(s, next).sp)
        };
        unsafe { switch_stacks(save, load) };
        after_switch();
    }
}

// ---------------------------------------------------------------------------
// Calls for the synchronization objects

/// The running task.
pub fn current() -> Slot {
    sched().current
}

/// The priority that a task runs at.
pub(crate) fn priority_of(slot: Slot) -> u8 {
    task(sched(), slot).priority
}

/// The mutex that a task waits for, or null.
pub(crate) fn blocked_on(slot: Slot) -> *mut Mutex {
    task(sched(), slot).blocked_on
}

pub(crate) fn set_blocked_on(slot: Slot, mutex: *mut Mutex) {
    task(sched(), slot).blocked_on = mutex;
}

/// The head of the list of mutexes that a task owns.
pub(crate) fn owned(slot: Slot) -> *mut Mutex {
    task(sched(), slot).owned
}

pub(crate) fn set_owned(slot: Slot, mutex: *mut Mutex) {
    task(sched(), slot).owned = mutex;
}

/// The priority of the most urgent task on a wait queue.
pub(crate) fn top_waiter_priority(q: &WaitQueue) -> Option<u8> {
    if q.head == NONE {
        None
    } else {
        Some(task(sched(), q.head).priority)
    }
}

/// Blocks the running task until another task wakes it or `deadline` passes.
/// With a queue, the task waits on the queue in priority order. A deadline of
/// zero is treated like any deadline in the past.
pub(crate) fn block_on(queue: *mut WaitQueue, deadline: u64) -> Wake {
    {
        let s = sched();
        let current = s.current;
        {
            let t = task(s, current);
            t.state = State::Blocked;
            t.queue = queue;
            t.deadline = deadline;
            t.wake = Wake::Signal;
        }
        if !queue.is_null() {
            list_insert_by_priority(s, queue, current);
        }
        if deadline < s.next_deadline {
            s.next_deadline = deadline;
        }
    }
    reschedule();
    let s = sched();
    let current = s.current;
    task(s, current).wake
}

/// Makes the most urgent task on a queue ready. Does not switch to it; the
/// caller calls [`preempt`] when its own state is consistent.
pub(crate) fn wake_first(queue: *mut WaitQueue, why: Wake) -> Option<Slot> {
    let s = sched();
    let slot = unsafe { (*queue).head };
    if slot == NONE {
        return None;
    }
    list_remove(s, queue, slot);
    task(s, slot).wake = why;
    make_ready(s, slot, false);
    Some(slot)
}

/// Makes all tasks on a queue ready. Returns how many there were.
pub(crate) fn wake_all(queue: *mut WaitQueue, why: Wake) -> usize {
    let mut count = 0;
    while wake_first(queue, why).is_some() {
        count += 1;
    }
    count
}

/// Switches to a ready task if it is more urgent than the running one. The
/// running task keeps its place at the head of its priority.
pub(crate) fn preempt() {
    let s = sched();
    let current = s.current;
    if current == NONE {
        return;
    }
    let mine = task(s, current).priority;
    match top_ready(s) {
        Some(top) if top < mine => {
            make_ready(s, current, true);
            reschedule();
        }
        _ => {}
    }
}

/// Changes the priority that a task runs at and keeps the task in the right
/// place on the list that it is on.
pub(crate) fn set_running_priority(slot: Slot, priority: u8) {
    let s = sched();
    let (state, old, queue) = {
        let t = task(s, slot);
        (t.state, t.priority, t.queue)
    };
    if old == priority {
        return;
    }
    match state {
        State::Ready => {
            unready(s, slot);
            task(s, slot).priority = priority;
            make_ready(s, slot, false);
        }
        State::Blocked if !queue.is_null() => {
            list_remove(s, queue, slot);
            task(s, slot).priority = priority;
            list_insert_by_priority(s, queue, slot);
        }
        _ => task(s, slot).priority = priority,
    }
}

pub(crate) fn base_priority_of(slot: Slot) -> u8 {
    task(sched(), slot).base_priority
}

// ---------------------------------------------------------------------------
// Public calls

/// Makes the thread that the kernel started the first task. It runs at the
/// most urgent priority until the program changes it.
pub fn init() {
    let s = sched();
    if s.started {
        return;
    }
    s.started = true;
    let t = &mut s.tasks[0];
    t.state = State::Running;
    t.base_priority = 0;
    t.priority = 0;
    s.current = 1;
}

fn handle_of(s: &mut Sched, slot: Slot) -> u32 {
    ((task(s, slot).generation as u32) << 16) | slot as u32
}

fn slot_of(s: &mut Sched, handle: u32) -> Result<Slot, Error> {
    let slot = (handle & 0xffff) as Slot;
    if slot == NONE || slot as usize > MAX_TASKS {
        return Err(Error::BadHandle);
    }
    let t = task(s, slot);
    if t.generation as u32 != handle >> 16 || t.state == State::Free || t.state == State::Zombie {
        return Err(Error::BadHandle);
    }
    Ok(slot)
}

/// Creates a task and makes it ready. With a null `stack`, the runtime maps a
/// stack of at least `stack_size` bytes with an unmapped page below it.
///
/// The handle is stored at `handle` before the new task can run, because a
/// more urgent new task runs before this call returns.
pub fn spawn(
    entry: Entry,
    arg: *mut c_void,
    stack: *mut u8,
    stack_size: usize,
    priority: u8,
    handle: *mut u32,
) -> Result<(), Error> {
    let s = sched();
    let slot = match s.tasks.iter().position(|t| t.state == State::Free) {
        Some(i) => i as Slot + 1,
        None => return Err(Error::NoSlot),
    };
    let (base, pages, top) = if stack.is_null() {
        let pages = stack_size.max(STACK_MIN).div_ceil(PAGE_SIZE);
        mem::reserve_gap(1);
        let base = mem::alloc_pages(pages).ok_or(Error::NoMemory)?;
        (base, pages, base + pages * PAGE_SIZE)
    } else {
        if stack_size < 4096 {
            return Err(Error::BadArgument);
        }
        (stack as usize, 0, (stack as usize + stack_size) & !15)
    };
    // The frame that `switch_stacks` pops: six registers and a return address.
    let sp = top - 7 * 8;
    unsafe {
        let frame = sp as *mut usize;
        for i in 0..6 {
            frame.add(i).write(0);
        }
        frame.add(6).write(task_boot as *const () as usize);
    }
    let generation = task(s, slot).generation;
    *task(s, slot) = Task {
        generation,
        sp,
        base_priority: priority,
        priority,
        stack_base: base,
        stack_pages: pages,
        entry: Some(entry),
        arg,
        ..EMPTY_TASK
    };
    make_ready(s, slot, false);
    let new_handle = handle_of(s, slot);
    unsafe { handle.write(new_handle) };
    preempt();
    Ok(())
}

/// Ends the running task.
pub fn exit_current() -> ! {
    {
        let s = sched();
        let current = s.current;
        task(s, current).state = State::Zombie;
        s.zombie = current;
    }
    reschedule();
    unreachable!("an exited task ran again");
}

/// Ends another task, or the running task. Mutexes that the task owns stay
/// locked.
pub fn delete(handle: u32) -> Result<(), Error> {
    let s = sched();
    let slot = slot_of(s, handle)?;
    if slot == s.current {
        exit_current();
    }
    let (state, queue) = {
        let t = task(s, slot);
        (t.state, t.queue)
    };
    match state {
        State::Ready => unready(s, slot),
        State::Blocked if !queue.is_null() => list_remove(s, queue, slot),
        _ => {}
    }
    release_slot(s, slot);
    Ok(())
}

/// The handle of the running task.
pub fn current_handle() -> u32 {
    let s = sched();
    let current = s.current;
    handle_of(s, current)
}

/// Lets other ready tasks of the same or a more urgent priority run.
pub fn yield_now() {
    {
        let s = sched();
        let current = s.current;
        make_ready(s, current, false);
    }
    reschedule();
}

/// Blocks the running task until `deadline`.
pub fn sleep_until(deadline: u64) {
    if deadline <= time::now() {
        yield_now();
        return;
    }
    block_on(ptr::null_mut(), deadline);
}

/// Notices deadlines that have passed and switches to a more urgent task if
/// one became ready.
pub fn poll() {
    expire(sched(), time::now());
    preempt();
}

/// Sets the priority that the program gives a task.
pub fn set_priority(handle: u32, priority: u8) -> Result<(), Error> {
    let slot = {
        let s = sched();
        let slot = slot_of(s, handle)?;
        task(s, slot).base_priority = priority;
        slot
    };
    crate::sync::refresh_priority(slot);
    preempt();
    Ok(())
}

pub fn get_priority(handle: u32) -> Result<u8, Error> {
    let s = sched();
    let slot = slot_of(s, handle)?;
    Ok(task(s, slot).base_priority)
}

pub fn set_tag(handle: u32, tag: usize) -> Result<(), Error> {
    let s = sched();
    let slot = slot_of(s, handle)?;
    task(s, slot).tag = tag;
    Ok(())
}

pub fn get_tag(handle: u32) -> Result<usize, Error> {
    let s = sched();
    let slot = slot_of(s, handle)?;
    Ok(task(s, slot).tag)
}

/// The lowest address of the stack of a task that the runtime mapped, and its
/// size in bytes.
pub fn stack_of(handle: u32) -> Result<(usize, usize), Error> {
    let s = sched();
    let slot = slot_of(s, handle)?;
    let t = task(s, slot);
    Ok((t.stack_base, t.stack_pages * PAGE_SIZE))
}
