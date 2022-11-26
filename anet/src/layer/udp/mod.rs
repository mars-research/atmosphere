use alloc::{collections::VecDeque, sync::Arc};
use pnet::packet::udp::ipv4_checksum;

use crate::{
    packet::UdpPacketRepr,
    util::{Port, SocketAddress},
};

pub struct UdpLayer {
    endpoint: Port,
}

impl UdpLayer {
    pub fn new(endpoint: Port) -> Self {
        Self { endpoint }
    }

    pub fn send_packet<F>(&self, buf: &mut [u8], addr: SocketAddress, f: F) -> Result<usize, ()>
    where
        F: FnOnce(&mut [u8]) -> usize,
    {
        todo!()
        // self.lower.send_packet(
        //     buf,
        //     addr.ip,
        //     super::ip::Ipv4NextHeader::Udp,
        //     |buf: &mut [u8]| {
        //         buf[0..2].copy_from_slice(&self.endpoint.to_be_bytes());
        //         buf[2..4].copy_from_slice(&addr.port.to_be_bytes());

        //         let mut udp_payload_len: u16 = f(&mut buf[8..])
        //             .try_into()
        //             .expect("udp payload len overflowed");

        //         udp_payload_len += 8;

        //         buf[4..6].copy_from_slice(&udp_payload_len.to_be_bytes());

        //         buf[6..8].copy_from_slice(&[0, 0]); // checksum here

        //         (udp_payload_len).into()
        //     },
        // )
    }

    pub fn recv_packet<F>(&self, buf: &[u8], f: F) -> Result<SocketAddress, ()>
    where
        F: FnOnce(SocketAddress, &[u8]) -> (),
    {
        // let mut socket_addr = SocketAddress::default();

        // self.lower
        //     .recv_packet(buf, |remote_ip: Ipv4Address, payload: &[u8]| {
        //         let port = u16::from_be_bytes([payload[0], payload[1]]);

        //         let len = u16::from_be_bytes([payload[4], payload[5]]) as usize;

        //         if len < 8 {
        //             panic!("invalid packet received");
        //         }

        //         socket_addr = SocketAddress::new(remote_ip, port);

        //         f(socket_addr, &payload[8..len]);
        //     })?;

        // Ok(socket_addr)
        todo!()
    }

    pub fn prepare_udp_batch(&self, dest: Port, packets: &mut VecDeque<UdpPacketRepr>) {
        for packet in packets.iter_mut() {
            let udp_len: u16 = (packet.udp_payload_len() + 8)
                .try_into()
                .expect("udp length overflowed");
            dbg!(udp_len);

            packet.set_udp_packet(|mut udp| {
                udp.set_source(self.endpoint);
                udp.set_destination(dest);
                udp.set_length(udp_len);
                udp.set_checksum(0);
            });
        }
    }
}
