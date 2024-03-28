use vstd::prelude::*;
use core::mem::MaybeUninit;
verus! {

pub struct RegistersOption{
    pub reg: Registers,
    pub exists: bool,
}
impl RegistersOption {
    pub open spec fn is_Some(&self) -> bool{
        self.exists
    }
    pub open spec fn is_None(&self) -> bool{
        self.exists == false
    }
    pub open spec fn get_Some_0(&self) -> &Registers
        recommends self.is_Some()
    {
        &self.reg
    }
    pub fn is_some(&self) -> (ret:bool)
        ensures 
            ret == self.is_Some()
    {
        self.exists
    }
    pub fn is_none(&self) -> (ret:bool)
        ensures 
            ret == self.is_None()
    {
        self.exists == false
    }
    pub fn unwrap(&self) -> (ret: &Registers)
        ensures
            self.get_Some_0() =~= ret,
    {
        &self.reg
    }

    #[verifier(external_body)]
    pub fn set_self_fast(&mut self, src: &Registers)
        ensures
            self.is_Some(),
            self.get_Some_0() =~= src
    {
        self.exists = true;
        self.reg.rbx = src.rbx;
        self.reg.rbp = src.rbp;
        self.reg.r12 = src.r12;
        self.reg.r13 = src.r13;
        self.reg.r14 = src.r14;
        self.reg.r15 = src.r15;
        self.reg.rsp = src.rsp;
        self.reg.rip = src.rip;
        self.reg.flags = src.flags;
    }

    pub fn set_self(&mut self, src: &Registers)
        ensures
            self.is_Some(),
            self.get_Some_0() =~= src
    {
        self.exists = true;
        self.reg = *src;
    }

    #[verifier(external_body)]
    pub fn set_dst_fast(&self, dst: &mut Registers)
        requires
            self.is_Some(),
        ensures
            *dst =~= *self.get_Some_0(),
    {
        dst.rbx = self.reg.rbx;
        dst.rbp = self.reg.rbp;
        dst.r12 = self.reg.r12;
        dst.r13 = self.reg.r13;
        dst.r14 = self.reg.r14;
        dst.r15 = self.reg.r15;
        dst.rsp = self.reg.rsp;
        dst.rip = self.reg.rip;
        dst.flags = self.reg.flags;
    }

    pub fn set_dst(&self, dst: &mut Registers)
        requires
            self.is_Some(),
        ensures
            *dst =~= *self.get_Some_0(),
    {
        *dst = self.reg;
    }
    
    pub fn set_to_none(&mut self)
        ensures
            self.is_None(),
    {
        self.exists = false;
    }

    pub fn zeroed_none() -> (ret: Self)
        ensures
            ret.is_None(),
    {
        Self{
            reg: Registers::zeroed(),
            exists: false,
        }
    }
}

/// Registers passed to the ISR.
#[repr(C, align(8))]
#[derive(Clone, Copy, Debug)]
pub struct Registers {
    pub r15: u64,
    pub r14: u64,
    pub r13: u64,
    pub r12: u64,
    pub rbp: u64,
    pub rbx: u64,
    pub r11: u64,
    pub r10: u64,
    pub r9: u64,
    pub r8: u64,
    pub rcx: u64,
    pub rdx: u64,
    pub rsi: u64,
    pub rdi: u64,
    pub rax: u64,

    // Original interrupt stack frame

    pub error_code: u64,
    pub rip: u64,
    pub cs: u64,
    pub flags: u64,
    pub rsp: u64,
    pub ss: u64,
}

impl Registers {
    #[verifier(external_body)]
    pub const fn zeroed() -> Self {
        unsafe {
            MaybeUninit::zeroed().assume_init()
        }
    }

    #[verifier(external_body)]
    pub fn random() -> (ret: Self)
    {
        unsafe{
            return MaybeUninit::uninit().assume_init();
        }
    }

    pub fn new_empty()-> (ret : Self)
    {
        let ret = Self {
            r15 : 0,
            r14 : 0,
            r13 : 0,
            r12 : 0,
            rbp : 0,
            rbx : 0,
            r11 : 0,
            r10 : 0,
            r9 : 0,
            r8 : 0,
            rcx : 0,
            rdx : 0,
            rsi : 0,
            rdi : 0,
            rax : 0,

            error_code: 0,
            rip : 0,
            cs : 0,
            flags : 0,
            rsp : 0,
            ss : 0,
        };
        ret
    }

    pub fn new(input: &Registers) -> (ret : Self)
        ensures
        ret =~= *input,
    {
        let ret = Self {
            r15 : input.r15,
            r14 : input.r14,
            r13 : input.r13,
            r12 : input.r12,
            rbp : input.rbp,
            rbx : input.rbx,

            r11 : input.r11,
            r10 : input.r10,
            r9 : input.r9,
            r8 : input.r8,
            rcx : input.rcx,
            rdx : input.rdx,
            rsi : input.rsi,
            rdi : input.rdi,
            rax : input.rax,

            error_code: input.error_code,
            rip : input.rip,
            cs : input.cs,
            flags : input.flags,
            rsp : input.rsp,
            ss : input.ss,
        };
        ret
    }

}

}
