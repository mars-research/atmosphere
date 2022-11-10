use alloc::sync::Arc;

use crate::util::{MacAddress, Ipv4Address};

use super::eth::{EthernetLayer, EtherType};

const ETHERNET_HRD_TYPE: u16 = 1;
const IPV4_PROTO_TYPE: u16 = 0x800;
const ETHERNET_HRD_ADDR_LEN: u8 = 6;
const IPV4_PROTO_ADDR_LEN: u8 = 4;
const ARP_REQUEST: u16 = 1;
const ARP_RESPONSE: u16 = 2;

pub struct ArpLayer {
    lower: Arc<EthernetLayer>,
    mac_addr: MacAddress,
    ipv4_addr: Ipv4Address,
}

impl ArpLayer {
    pub fn new(mac_addr: MacAddress, ipv4_addr: Ipv4Address, lower: Arc<EthernetLayer>) -> Self {
        Self { lower, mac_addr, ipv4_addr }
    }

    pub fn send_request(&self, dest: Ipv4Address) {
        self.lower.send_packet(MacAddress::broadcast(), EtherType::Arp, |buf: &mut [u8]| {
            buf[0..2].copy_from_slice(&ETHERNET_HRD_TYPE.to_be_bytes());
            buf[2..4].copy_from_slice(&IPV4_PROTO_TYPE.to_be_bytes());
            buf[4] = ETHERNET_HRD_ADDR_LEN;
            buf[5] = IPV4_PROTO_ADDR_LEN;
            buf[6..8].copy_from_slice(&ARP_REQUEST.to_be_bytes());
            buf[8..14].copy_from_slice(&self.mac_addr.0);
            buf[14..18].copy_from_slice(&self.ipv4_addr.0);
            buf[18..28].copy_from_slice(&[0; 10]);

            28
        }).expect("failed to send arp packet");
    }

    pub fn recv(&self) {

    }
}
