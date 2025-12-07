// e810_driver/src/aq.rs
#![allow(non_camel_case_types)]

#[repr(C)]
#[derive(Copy, Clone, Default)]
pub struct IceAqDesc {
    pub flags: u16,
    pub opcode: u16,
    pub datalen: u16,
    pub retval: u16,
    pub cookie_high: u32,
    pub cookie_low: u32,
    pub param0: u32,
    pub param1: u32,
    pub addr_high: u32,
    pub addr_low: u32,
}

// opcode from ice_adminq_cmd.h: 0x0107
pub const ICE_AQC_OPC_MANAGE_MAC_READ: u16 = 0x0107;

// Common AQ flag bits (from Linux driver)
pub const ICE_AQ_FLAG_BUF: u16 = 1 << 2;
pub const ICE_AQ_FLAG_RD:  u16 = 1 << 3;
pub const ICE_AQ_FLAG_DD:  u16 = 1 << 9;
pub const ICE_AQ_FLAG_ERR: u16 = 1 << 10;

#[repr(C)]
#[derive(Copy, Clone, Default)]
pub struct IceAqcManageMacRead {
    pub flags: u16,
    pub num_addr: u16,
    pub reserved: [u16; 2],
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct IceAqcManageMacReadResp {
    pub flags: u16,
    pub lport_num: u8,
    pub addr_type: u8,
    pub mac_addr: [u8; 6],
    pub pf_num: u8,
    pub vf_num: u8,
    pub vf_type: u8,
    pub reserved: [u8; 2],
}

// Keep descriptor size honest; ICE descriptors are 32 bytes
const _: [(); 32] = [(); core::mem::size_of::<IceAqDesc>()];
