use crossbeam::queue::ArrayQueue;

use crate::layer::{
    eth::ETHER_HDR_LEN,
    ip::{Ipv4NextHeader, IPV4_HEADER_LEN},
};

pub type Port = u16;

#[derive(Default, Clone, Copy)]
pub struct MacAddress(pub [u8; 6]);

impl MacAddress {
    pub fn new(octets: [u8; 6]) -> Self {
        Self(octets)
    }

    pub fn broadcast() -> Self {
        Self([0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])
    }

    pub fn from_slice(slice: &[u8]) -> Self {
        let mut octets = [0; 6];

        octets.copy_from_slice(slice);

        Self(octets)
    }
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ipv4Address(pub [u8; 4]);

impl Ipv4Address {
    pub fn new(octets: [u8; 4]) -> Self {
        Self(octets)
    }

    pub fn from_slice(slice: &[u8]) -> Self {
        let mut octets = [0; 4];
        octets.copy_from_slice(slice);
        Self(octets)
    }
}

impl From<Ipv4Address> for u32 {
    fn from(value: Ipv4Address) -> Self {
        u32::from_be_bytes(value.0)
    }
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct SocketAddress {
    pub ip: Ipv4Address,
    pub port: Port,
}

impl SocketAddress {
    pub fn new(ip: Ipv4Address, port: u16) -> Self {
        Self { ip, port }
    }
}

#[derive(Clone, Debug)]
pub struct RawPacket(pub [u8; 1514]);

impl Default for RawPacket {
    fn default() -> Self {
        RawPacket([0; 1514])
    }
}

pub type VacantBufs = ArrayQueue<RawPacket>;

pub fn flip_ip_hdr(ip_hdr: &mut [u8]) {
    let mut src_ip: [u8; 4] = [0; 4];
    src_ip.copy_from_slice(&ip_hdr[12..16]);

    let mut dst_ip: [u8; 4] = [0; 4];
    dst_ip.copy_from_slice(&ip_hdr[16..20]);

    let ttl = ip_hdr[8] - 1;

    ip_hdr[12..16].copy_from_slice(&dst_ip);
    ip_hdr[16..20].copy_from_slice(&src_ip);
    ip_hdr[8] = ttl;
}

pub fn flip_udp_hdr(udp_hdr: &mut [u8]) {
    let mut src_port = [0; 2];
    src_port.copy_from_slice(&udp_hdr[0..2]);

    let mut dst_port = [0; 2];
    dst_port.copy_from_slice(&udp_hdr[2..4]);

    udp_hdr[0..2].copy_from_slice(&dst_port);
    udp_hdr[2..4].copy_from_slice(&src_port);
}

pub fn flip_eth_hdr(eth_hdr: &mut [u8]) {
    let mut dst_mac: [u8; 6] = [0; 6];
    dst_mac.copy_from_slice(&eth_hdr[0..6]);
    let mut src_mac: [u8; 6] = [0; 6];
    src_mac.copy_from_slice(&eth_hdr[6..12]);

    eth_hdr[0..6].copy_from_slice(&src_mac);
    eth_hdr[6..12].copy_from_slice(&dst_mac);
}

pub fn echo_pkt(buf: &mut [u8]) {
    flip_eth_hdr(&mut buf[0..14]);
    flip_ip_hdr(&mut buf[14..34]);
    flip_udp_hdr(&mut buf[34..42]);
}

#[inline(always)]
pub fn read_proto_and_port(buf: &[u8]) -> (Ipv4NextHeader, Port) {
    let ipv4_packet = &buf[ETHER_HDR_LEN..];
    let next_header = *&ipv4_packet[9];

    if next_header == (Ipv4NextHeader::Udp as u8) {
        (Ipv4NextHeader::Udp, read_udp_port(ipv4_packet))
    } else if next_header == (Ipv4NextHeader::Tcp as u8) {
        (Ipv4NextHeader::Tcp, read_tcp_port(ipv4_packet))
    } else {
        panic!("unsupported ipv4 next header");
    }
}

fn read_tcp_port(ipv4_packet: &[u8]) -> Port {
    let tcp_packet = &ipv4_packet[IPV4_HEADER_LEN..];
    let tcp_port = u16::from_be_bytes([tcp_packet[2], tcp_packet[3]]);

    tcp_port
}

fn read_udp_port(ipv4_packet: &[u8]) -> Port {
    let udp_packet = &ipv4_packet[IPV4_HEADER_LEN..];
    let udp_port = u16::from_be_bytes([udp_packet[2], udp_packet[3]]);

    udp_port
}
