use alloc::collections::VecDeque;
use pnet::packet::ip::IpNextHeaderProtocols;
use pnet::packet::{ipv4::checksum, Packet};
use pnet::util::core_net::Ipv4Addr;

use crate::packet::UdpPacketRepr;

pub mod routing;

pub const IPV4_HEADER_LEN: usize = 20;

const IP_DEFAULT_TTL: u8 = 64;
const IPV4_VERSION: u8 = 4;
const IPV4_HDR_LEN: u8 = 5;

#[repr(u8)]
#[derive(Debug, PartialEq, Eq)]
pub enum Ipv4NextHeader {
    Udp = 17,
    Tcp = 06,
    Icmp = 01,
}

pub struct Ipv4Layer {
    endpoint: Ipv4Addr,
}

impl Ipv4Layer {
    pub fn new(endpoint: Ipv4Addr) -> Self {
        Self { endpoint }
    }

    pub fn prepare_udp_batch(&self, dest: Ipv4Addr, packets: &mut VecDeque<UdpPacketRepr>) {
        for packet in packets.iter_mut() {
            let total_len = packet.udp_packet().get_length() + IPV4_HEADER_LEN as u16;
            packet.set_ip_packet(|mut ip| {
                ip.set_destination(dest);
                ip.set_source(self.endpoint);
                ip.set_ttl(64);
                ip.set_ttl(IP_DEFAULT_TTL);
                ip.set_version(IPV4_VERSION);
                ip.set_header_length(IPV4_HDR_LEN);
                ip.set_total_length(total_len);
                ip.set_next_level_protocol(IpNextHeaderProtocols::Udp);

                let ck = checksum(&ip.to_immutable());
                ip.set_checksum(ck);
            });
        }
    }
}
