use byteorder::{ByteOrder, LittleEndian};

use super::PciDev;
use heapless::Vec as AVec;

pub trait ConfigReader {
    unsafe fn read_range(&self, offset: u8, len: u8) -> AVec<u8, 32> {
        assert!(len > 3 && len % 4 == 0);
        let mut ret = AVec::<u8, 32>::new();
        let results =
            (offset..offset + len)
                .step_by(4)
                .fold(AVec::<u32, 8>::new(), |mut acc, offset| {
                    let val = self.read_u32(offset);
                    acc.push(val);
                    acc
                });
        unsafe {
            ret.set_len(len as usize);
        }
        LittleEndian::write_u32_into(&*results, &mut ret);
        ret
    }

    unsafe fn read_u32(&self, offset: u8) -> u32;
}

pub struct PciFunc<'pci> {
    pub dev: &'pci PciDev<'pci>,
    pub num: u8,
}

impl<'pci> ConfigReader for PciFunc<'pci> {
    unsafe fn read_u32(&self, offset: u8) -> u32 {
        self.dev.read(self.num, offset)
    }
}
