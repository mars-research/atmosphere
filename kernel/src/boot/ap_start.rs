//! AP boot trampoline.
//!
//! ## AP Boot ABI
//!
//! -32 @ 0x6fe0: Argument
//! -24 @ 0x6fe8: Code Pointer
//! -16 @ 0x6ff8: Stack Pointer
//!  -8 @ 0x6ff0: CR3
//!   0 @ 0x7000: Trampoline Code

use core::ptr;

static TRAMPOLINE_CODE: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/ap_start.bin"));

pub struct StartTrampoline {
    base: u16,
}

impl StartTrampoline {
    const CR3_OFFSET: isize = -8;
    const STACK_PTR_OFFSET: isize = -16;
    const CODE_POINTER_OFFSET: isize = -24;
    const ARG_OFFSET: isize = -32;

    pub unsafe fn new(base: u16) -> Result<Self, &'static str> {
        if base & (4096 - 1) != 0 {
            return Err("Destination not page aligned");
        }

        let mut handle = Self { base };

        handle.copy_binary();

        Ok(handle)
    }

    pub fn with_stack(&mut self, stack: u64) -> &mut Self {
        unsafe {
            let stack_dst = self.base_ptr().offset(Self::STACK_PTR_OFFSET) as *mut u64;
            ptr::write_volatile(stack_dst, stack);
        }

        self
    }

    pub fn with_cr3(&mut self, cr3: u64) -> &mut Self {
        unsafe {
            let cr3_dst = self.base_ptr().offset(Self::CR3_OFFSET) as *mut u64;
            ptr::write_volatile(cr3_dst, cr3);
        }

        self
    }

    pub fn with_code(&mut self, code: u64) -> &mut Self {
        unsafe {
            let code_dst = self.base_ptr().offset(Self::CODE_POINTER_OFFSET) as *mut u64;
            ptr::write_volatile(code_dst, code);
        }

        self
    }

    pub fn with_arg(&mut self, arg: u64) -> &mut Self {
        unsafe {
            let arg_dst = self.base_ptr().offset(Self::ARG_OFFSET) as *mut u64;
            ptr::write_volatile(arg_dst, arg);
        }

        self
    }

    pub fn start_page(&self) -> u8 {
        (self.base >> 12) as u8
    }

    fn base_ptr(&self) -> *mut u8 {
        self.base as *mut u8
    }

    fn copy_binary(&mut self) {
        unsafe {
            ptr::copy(
                TRAMPOLINE_CODE as *const _ as *const u8,
                self.base_ptr(),
                TRAMPOLINE_CODE.len(),
            );
        }
    }
}
