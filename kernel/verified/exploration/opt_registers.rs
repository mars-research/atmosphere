use vstd::prelude::*;
use core::mem::MaybeUninit;
use core::borrow::BorrowMut;

verus! {

pub struct Registers {
    pub rax: u64,
    pub rbx: u64,
}

pub struct OptRegisters {
    present: bool,
    registers: Registers,
}

impl OptRegisters {
    #[verifier(external_body)]
    pub fn new() -> (res: Self)
        ensures
            res@ == None::<Registers>,
            res.wf(),
    {
        Self {
            present: false,
            registers: MaybeUninit::zeroed().assume_init(),
        }
    }

    #[inline(always)]
    pub const fn is_some(&self) -> (res: bool)
        requires self.wf(),
        ensures res == self.is_Some(),
    {
        self.present
    }

    #[inline(always)]
    pub const fn is_none(&self) -> (res: bool)
        requires self.wf(),
        ensures res == self.is_None(),
    {
        !self.present
    }

    #[verifier(external_body)]
    pub fn set(&mut self, registers: Registers)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self@ == Some(registers),
    {
        self.present = true;
        self.registers = registers;
    }

    #[verifier(external_body)]
    pub fn set_callee_saved(&mut self, registers: Registers)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self.spec_set_callee_saved(registers),
    {
        self.present = true;
        self.registers.rbx = registers.rbx;
    }

    pub open spec fn spec_set_callee_saved(&self, registers: Registers) -> bool {
        // don't prove anything about other registers being unchanged
        // (they are simply clobbered)
        self@ == Some(Registers {
            rax: arbitrary(),
            rbx: registers.rbx,
        })
    }

    pub spec fn view(&self) -> Option<Registers>;

    #[verifier(inline)]
    pub open spec fn is_Some(&self) -> bool {
        builtin::is_variant(self@, "Some")
    }

    #[verifier(inline)]
    pub open spec fn get_Some_0(&self) -> Registers {
        builtin::get_variant_field(self@, "Some", "0")
    }

    #[verifier(inline)]
    pub open spec fn is_None(&self) -> bool {
        builtin::is_variant(self@, "None")
    }

    pub closed spec fn wf(&self) -> bool {
        self.present == self.is_Some()
    }
}

fn test() {
    let mut reg = OptRegisters::new();

    assert(reg.wf());
    assert(reg.is_None());

    reg.set(Registers {
        rax: 1,
        rbx: 2,
    });

    assert(reg.is_Some());
    assert(reg.get_Some_0().rax == 1);
    assert(reg.get_Some_0().rbx == 2);

    reg.set_callee_saved(Registers {
        rax: 3,
        rbx: 4,
    });

    assert(reg.is_Some());
    assert(reg.get_Some_0().rbx == 4);
}

}
