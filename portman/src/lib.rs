#![no_std]
// #![deny(
//     dead_code,
//     deprecated,
//     missing_abi,
//     rustdoc::bare_urls,
//     unused_imports,
//     unused_must_use,
//     unused_mut,
//     unused_unsafe,
//     unused_variables,
// )]

use atcp::TCPStack;
use hashbrown::HashMap;
use pnet::packet::{ethernet::EthernetPacket, Packet, ipv4::Ipv4Packet, tcp::TcpPacket};
use ringbuf::Consumer;

type Port = u16;
type PortManResult<T> = core::result::Result<T, ()>;

/// The PortManager maintains mapping from a Port to a TCPStack.
/// It forwards the packets it receives from the NIC to a corresponding TCPStack
pub struct PortManager<'a> {
    mappings: HashMap<Port, &'a TCPStack>,
}

impl<'a> PortManager<'a> {
    pub fn new() -> Self {
        Self {
            mappings: HashMap::new(),
        }
    }

    pub fn create_mapping(&mut self, port: Port, stack: &'a TCPStack) {
        self.mappings.insert(port, stack);
    }

    pub fn delete_mapping(&mut self, port: Port) {
        self.mappings.remove(&port);
    }

    // parse packet with libpnet for now, later we can write a faster parser since we only need one
    // field from the packet here
    pub fn recv_pkt(&self, _pkt_data: &[u8]) {
    }
}

// Given an ethernet frame containing a TCP packet, extracts the TCP port of that packet.
fn get_port(packet: &[u8]) -> PortManResult<Port> {
    let ether_pkt = EthernetPacket::new(packet).ok_or(())?;

    let ipv4_pkt = Ipv4Packet::new(ether_pkt.payload()).ok_or(())?;

    let tcp_pkt = TcpPacket::new(ipv4_pkt.payload()).ok_or(())?;

    Ok(tcp_pkt.get_destination())
}

#[cfg(test)]
mod test {
    // pub use std::prelude::v1::*;
    use crate::get_port;

    // type Result<T> = std::result::Result<T, ()>;

    #[test]
    fn test_get_port() -> Result<(), ()> {
        let pkt = [
        0xb0, 0x6a, 0x41, 0xea, 0xe7, 0x2b, 0xf4, 0xd4, 0x88, 0x7c, 0x04, 0xa5, 0x08, 0x00, 0x45, 0x00,
        0x00, 0x34, 0x00, 0x00, 0x00, 0x00, 0x40, 0x06, 0x79, 0xe7, 0xc0, 0xa8, 0x54, 0x1f, 0x22, 0xe5,
        0xc9, 0x30, 0xc5, 0xcd, 0x01, 0xbb, 0xcd, 0xf2, 0xc2, 0x9d, 0x4d, 0x13, 0xca, 0x59, 0x80, 0x10,
        0x08, 0x00, 0x9c, 0xa8, 0x00, 0x00, 0x01, 0x01, 0x08, 0x0a, 0xbd, 0x35, 0x2c, 0x59, 0x7b, 0x99,
        0xfc, 0x88,
        ];

        let port = get_port(&pkt)?;

        assert_eq!(port, 443);

        Ok(())
    }
}
