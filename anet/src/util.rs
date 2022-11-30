use pnet::packet::{
    ip::{
        IpNextHeaderProtocol,
        IpNextHeaderProtocols::{self, Udp},
    },
    ipv4::Ipv4Packet,
    tcp::TcpPacket,
    udp::UdpPacket,
    Packet,
};

use crate::layer::{eth::ETHER_HDR_LEN, ip::IPV4_HEADER_LEN};

pub type Port = u16;
pub type MacAddress = pnet::util::MacAddr;
pub type Ipv4Address = pnet::util::core_net::Ipv4Addr;
pub type SocketAddress = pnet::util::core_net::SocketAddrV4;

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
pub fn read_proto_and_port(buf: &[u8]) -> Result<(IpNextHeaderProtocol, Port), ()> {
    if let Some(ipv4_packet) = Ipv4Packet::new(&buf[ETHER_HDR_LEN..]) {
        let next_header = ipv4_packet.get_next_level_protocol();

        if next_header == IpNextHeaderProtocols::Udp {
            if let Some(udp_packet) = UdpPacket::new(ipv4_packet.payload()) {
                let port = udp_packet.get_destination();
                Ok((IpNextHeaderProtocols::Udp, port))
            } else {
                Err(())
            }
        } else if next_header == IpNextHeaderProtocols::Tcp {
            if let Some(tcp_packet) = TcpPacket::new(ipv4_packet.payload()) {
                let port = tcp_packet.get_destination();
                Ok((IpNextHeaderProtocols::Tcp, port))
            } else {
                Err(())
            }
        } else {
            Err(())
        }
    } else {
        Err(())
    }
}
