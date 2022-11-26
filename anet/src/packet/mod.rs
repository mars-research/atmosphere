use core::cmp::min;

use pnet::{
    packet::{
        ethernet::{EthernetPacket, MutableEthernetPacket},
        ipv4::{Ipv4Packet, MutableIpv4Packet},
        udp::{MutableUdpPacket, UdpPacket},
        MutablePacket, Packet,
    },
    util::MacAddr,
};

// 14 byte ethernet + 20 byte ipv4 + 8 byte udp
const UDP_PAYLOAD_OFFSET: usize = 42;
const UDP_HEADER_OFFSET: usize = 34;
const UDP_HEADER_LEN: usize = 8;
const IP_HEADER_OFFSET: usize = 14;
const ETH_HEADER_OFFSET: usize = 0;

#[derive(Clone, Copy, Debug)]
pub struct RawPacket(pub [u8; 1514]);

impl Default for RawPacket {
    fn default() -> Self {
        Self([0; 1514])
    }
}

#[derive(Clone, Copy, Debug)]
pub struct UdpPacketRepr {
    packet: RawPacket,
    udp_payload_len: usize,
}

impl UdpPacketRepr {
    pub fn new() -> Self {
        let packet = RawPacket::default();
        Self {
            packet,
            udp_payload_len: 0,
        }
    }

    pub fn set_udp_packet<F: FnOnce(MutableUdpPacket)>(&mut self, f: F) {
        let udp_packet = MutableUdpPacket::new(&mut self.packet.0[UDP_HEADER_OFFSET..])
            .expect("buffer has insufficient length");
        f(udp_packet);
    }

    pub fn set_ip_packet<F: FnOnce(MutableIpv4Packet)>(&mut self, f: F) {
        let ip_packet = MutableIpv4Packet::new(&mut self.packet.0[IP_HEADER_OFFSET..])
            .expect("buffer has insufficient length");
        f(ip_packet);
    }

    pub fn set_eth_packet<F: FnOnce(MutableEthernetPacket)>(&mut self, f: F) {
        let eth_packet = MutableEthernetPacket::new(&mut self.packet.0[ETH_HEADER_OFFSET..])
            .expect("buffer has insufficient length");
        f(eth_packet);
    }

    pub fn udp_packet(&self) -> UdpPacket {
        UdpPacket::new(&self.packet.0[UDP_HEADER_OFFSET..]).expect("buffer has insufficient length")
    }

    pub fn ip_packet(&self) -> Ipv4Packet {
        Ipv4Packet::new(&self.packet.0[IP_HEADER_OFFSET..]).expect("buffer has insufficient length")
    }

    pub fn eth_packet(&self) -> EthernetPacket {
        EthernetPacket::new(&self.packet.0[ETH_HEADER_OFFSET..])
            .expect("buffer has insufficient length")
    }

    pub fn set_udp_payload<F: FnOnce(&mut [u8]) -> usize>(&mut self, f: F) {
        let mut payload_len = 0;
        self.set_udp_packet(|mut udp| {
            payload_len = f(udp.payload_mut());
        });

        self.udp_payload_len = payload_len;
    }

    pub fn udp_payload(&self) -> &[u8] {
        &self.packet.0[UDP_PAYLOAD_OFFSET..UDP_PAYLOAD_OFFSET + self.udp_payload_len]
    }

    pub fn consume(self) -> RawPacket {
        self.packet
    }

    pub fn udp_payload_len(&self) -> usize {
        self.udp_payload_len
    }
}

impl From<RawPacket> for UdpPacketRepr {
    fn from(packet: RawPacket) -> Self {
        let udp_packet =
            UdpPacket::new(&packet.0[UDP_HEADER_OFFSET..]).expect("buffer has insufficient length");
        let udp_payload_len = if udp_packet.get_length() as usize > UDP_HEADER_LEN {
            udp_packet.get_length() as usize - UDP_HEADER_LEN
        } else {
            0
        };

        Self {
            packet,
            udp_payload_len,
        }
    }
}
