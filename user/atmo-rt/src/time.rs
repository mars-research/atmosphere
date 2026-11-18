//! The monotonic clock.
//!
//! Time is the timestamp counter scaled to nanoseconds. The scale is measured
//! once at start against the programmable interval timer.

use core::arch::asm;
use core::cell::UnsafeCell;

use crate::sys;

/// A deadline that never arrives.
pub const FOREVER: u64 = u64::MAX;

/// The frequency of the programmable interval timer in Hz.
const PIT_HZ: u64 = 1_193_182;

struct Clock {
    /// The counter value at start.
    base: u64,
    /// Nanoseconds per counter tick as a 32.32 fixed-point number.
    scale: u64,
    /// The measured counter frequency in Hz.
    hz: u64,
}

struct Shared(UnsafeCell<Clock>);
unsafe impl Sync for Shared {}

// Until `init` runs the clock assumes 1 GHz, so that an early reading is sane.
static CLOCK: Shared = Shared(UnsafeCell::new(Clock { base: 0, scale: 1 << 32, hz: 1_000_000_000 }));

unsafe fn outb(port: u16, value: u8) {
    asm!("out dx, al", in("dx") port, in("al") value, options(nomem, nostack));
}

unsafe fn inb(port: u16) -> u8 {
    let value: u8;
    asm!("in al, dx", in("dx") port, out("al") value, options(nomem, nostack));
    value
}

/// Counts timestamp ticks over `pit_ticks` ticks of timer channel 2.
///
/// The first process runs with I/O privilege, so it can program the timer.
/// Returns `None` if the timer does not answer.
unsafe fn measure(pit_ticks: u16) -> Option<u64> {
    // Gate on, speaker off.
    let control = inb(0x61);
    outb(0x61, (control & !0x02) | 0x01);
    // Channel 2, low byte then high byte, mode 0: the output rises at zero.
    outb(0x43, 0xb0);
    outb(0x42, pit_ticks as u8);
    outb(0x42, (pit_ticks >> 8) as u8);
    let start = sys::rdtsc();
    let mut end = start;
    let mut polls: u64 = 0;
    while inb(0x61) & 0x20 == 0 {
        end = sys::rdtsc();
        polls += 1;
        if polls > 50_000_000 {
            outb(0x61, control);
            return None;
        }
    }
    outb(0x61, control);
    if polls < 4 {
        // The output was already high: the timer is not counting.
        return None;
    }
    Some(end - start)
}

/// Measures the counter frequency and starts the clock at zero.
pub fn init() {
    // 10 ms per round. Interference only makes a round longer, so the least
    // of several rounds is the best estimate.
    let pit_ticks: u16 = 11_932;
    let mut best: Option<u64> = None;
    for _ in 0..5 {
        if let Some(ticks) = unsafe { measure(pit_ticks) } {
            best = Some(best.map_or(ticks, |b| b.min(ticks)));
        }
    }
    let clock = unsafe { &mut *CLOCK.0.get() };
    if let Some(ticks) = best {
        let hz = (ticks as u128 * PIT_HZ as u128 / pit_ticks as u128) as u64;
        if hz >= 1_000_000 {
            clock.hz = hz;
            clock.scale = ((1_000_000_000u128 << 32) / hz as u128) as u64;
        }
    }
    clock.base = sys::rdtsc();
}

/// Nanoseconds since `init`.
pub fn now() -> u64 {
    let clock = unsafe { &*CLOCK.0.get() };
    let ticks = sys::rdtsc().wrapping_sub(clock.base);
    ((ticks as u128 * clock.scale as u128) >> 32) as u64
}

/// The measured frequency of the timestamp counter in Hz.
pub fn counter_hz() -> u64 {
    unsafe { (*CLOCK.0.get()).hz }
}

/// Nanoseconds since the runtime started. Never goes backward.
#[no_mangle]
pub extern "C" fn art_clock_ns() -> u64 {
    now()
}

/// The measured frequency of the timestamp counter in Hz.
#[no_mangle]
pub extern "C" fn art_clock_counter_hz() -> u64 {
    counter_hz()
}
