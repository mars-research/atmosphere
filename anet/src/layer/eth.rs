use alloc::sync::Arc;
use thingbuf::mpsc::Receiver;

use crate::{
    netmanager::NetManager,
    nic::{DummyNic, Net},
    util::{MacAddress, RawPacket, VacantBufs, read_proto_and_port},
};


pub const ETHER_HDR_LEN: usize = 14;

pub enum EtherType {
    Ipv4 = 0x800,
    Arp = 0x806,
}

pub struct EthernetLayer {
    endpoint: MacAddress,
}

impl EthernetLayer {
    pub fn new(
        endpoint: MacAddress,
    ) -> Self {
        Self {
            endpoint,
        }
    }

    pub fn send_packet<F>(&self, buf: &mut[u8], dmac: MacAddress, ether_type: EtherType, f: F) -> Result<usize, ()>
    where
        F: FnOnce(&mut [u8]) -> usize,
    {
        buf[0..6].copy_from_slice(&self.endpoint.0);
        buf[6..12].copy_from_slice(&dmac.0);

        buf[12..14].copy_from_slice(&(ether_type as u16).to_be_bytes());

        let payload_len = f(&mut buf[14..1504]);

        Ok(payload_len + ETHER_HDR_LEN)
    }

    pub fn recv_packet<F>(&self, buf: &[u8], f: F) -> Result<MacAddress, ()>
    where
        F: FnOnce(MacAddress, &[u8]) -> (),
    {
        let mut mac_addr = MacAddress::default();

        mac_addr = MacAddress::from_slice(&buf[0..6]);
        f(mac_addr, &buf[14..]);
        
        Ok(mac_addr)
    }
}

// let data = [0; 1024];
// socket.recv_with(|packet: &[u8], remote_addr: SocketAddress| {
//      data.copy_from_slice(packet);
// })
//
