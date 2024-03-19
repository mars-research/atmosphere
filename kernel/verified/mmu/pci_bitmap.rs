use vstd::prelude::*;
verus! {
use crate::define::*;
use core::mem::MaybeUninit;
pub struct PCIBitMap
{
    pub bit_map:[[[u8;32];256];IOID_MAX], //32MB
    pub ghost_map:Ghost<Map<(IOid,u8,u8,u8),bool>>,
}
impl PCIBitMap{
    #[verifier(external_body)]
    pub fn new() -> (ret: Self)
        ensures
            ret.wf(),
    {
        unsafe{
            Self{
                bit_map:MaybeUninit::uninit().assume_init(),
                ghost_map:Ghost(Map::empty()),
            }
        }
    }
    #[verifier(external_body)]
    pub fn init(&mut self)
        requires
            // old(self).wf(),
        ensures
            self.wf(),
            forall|ioid:IOid, bus:u8,dev:u8,fun:u8|#![auto] 0<=ioid<IOID_MAX && 0<=bus<256 && 0<=dev<32 && 0<=fun<8 ==> self@[(ioid,bus,dev,fun)] == false,
    {
        let mut ioid = 0;
        while ioid != IOID_MAX{
            let mut bus = 0;
            while bus != 256 {
                let mut dev = 0;
                while dev != 32{
                    let mut fun = 0;
                    while fun != 8{

                        self.bit_map[ioid][bus as usize][dev as usize] = 0;

                        fun = fun + 1;
                    }
                    dev = dev + 1;
                }
                bus = bus + 1;
            }
            ioid = ioid + 1;
        }
    }
    pub open spec fn wf(&self) -> bool{
        &&&
        (
            forall|ioid:IOid, bus:u8,dev:u8,fun:u8|#![auto] 0<=ioid<IOID_MAX && 0<=bus<256 && 0<=dev<32 && 0<=fun<8 <==> self.ghost_map@.dom().contains((ioid,bus,dev,fun))
        )
    }

    pub open spec fn view(&self) -> Map<(IOid,u8,u8,u8),bool>
    {
        self.ghost_map@
    }

    pub open spec fn resolve(&self,ioid:IOid,bus:u8,dev:u8,fun:u8) -> bool
        recommends
            self.wf(),
            0<=ioid<IOID_MAX,
            0<=bus<256 && 0<=dev<32 && 0<=fun<8,
    {
        self.ghost_map@[(ioid,bus,dev,fun)]
    }

    #[verifier(external_body)]
    pub fn get(&self, ioid:IOid,bus:u8,dev:u8,fun:u8) -> (ret:bool)
        requires
            self.wf(),
            0<=ioid<IOID_MAX,
            0<=bus<256 && 0<=dev<32 && 0<=fun<8,
        ensures
            ret == self.resolve(ioid,bus,dev,fun)
    {
        (self.bit_map[ioid][bus as usize][dev as usize] & (0x1u8 << (fun as usize))) == 0
    }

    #[verifier(external_body)]
    pub fn set(&mut self, ioid:IOid,bus:u8,dev:u8,fun:u8, target:bool)
        requires
            old(self).wf(),
            0<=ioid<IOID_MAX,
            0<=bus<256 && 0<=dev<32 && 0<=fun<8,
        ensures
            self.wf(),
            self.ghost_map@ =~= old(self).ghost_map@.insert((ioid,bus,dev,fun),target),
            self@ =~= old(self)@.insert((ioid,bus,dev,fun),target),
    {
        let bit_mask = !(0x1u8 << fun);
        let old = self.bit_map[ioid][bus as usize][dev as usize] & bit_mask;
        if target{
            self.bit_map[ioid][bus as usize][dev as usize] = old;
        }
        else{
            self.bit_map[ioid][bus as usize][dev as usize] = old | (0x1u8 << fun);
        }
    }

}
}
