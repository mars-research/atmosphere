use alloc::collections::VecDeque;
use spin::Mutex;

use crate::{
    util::{flip_eth_hdr, flip_ip_hdr, flip_udp_hdr, RawPacket},
    RpcResult,
};

use super::Net;

pub struct DummyNic {
    echo_queue: Mutex<VecDeque<[u8; 1514]>>,
}

impl DummyNic {
    pub fn new() -> Self {
        Self {
            echo_queue: Mutex::new(VecDeque::new()),
        }
    }
}

impl Net for DummyNic {
    fn submit(&self, send_buf: RawPacket) -> crate::RpcResult<(bool, RawPacket)> {
        let mut copy = [0; 1514];
        copy.copy_from_slice(&send_buf.0);

        flip_eth_hdr(&mut copy[0..14]);
        flip_ip_hdr(&mut copy[14..34]);
        flip_udp_hdr(&mut copy[34..42]);

        let mut g = self.echo_queue.lock();
        g.push_back(copy);

        Ok((true, send_buf))
    }

    fn submit_batch(
        &self,
        send_bufs: &mut VecDeque<RawPacket>,
        return_bufs: &mut VecDeque<RawPacket>,
    ) -> RpcResult<usize> {
        let num_sent = send_bufs.len();
        let mut g = self.echo_queue.lock();

        while let Some(send_buf) = send_bufs.pop_front() {
            let mut copy = [0; 1514];
            copy.copy_from_slice(&send_buf.0);

            flip_eth_hdr(&mut copy[0..14]);
            flip_ip_hdr(&mut copy[14..34]);
            flip_udp_hdr(&mut copy[34..42]);

            g.push_back(copy);
            return_bufs.push_back(send_buf);
        }
        Ok(num_sent)
    }

    fn poll(&self, mut buf: RawPacket) -> RpcResult<(bool, RawPacket)> {
        let mut g = self.echo_queue.lock();

        let sent = {
            if let Some(echo_packet) = g.pop_back() {
                buf.0.copy_from_slice(&echo_packet);
                true
            } else {
                false
            }
        };

        Ok((sent, buf))
    }

    fn poll_batch(
        &self,
        bufs: &mut VecDeque<RawPacket>,
        recvd_bufs: &mut VecDeque<RawPacket>,
    ) -> crate::RpcResult<usize> {
        let mut g = self.echo_queue.lock();

        let num_pkts = core::cmp::min(g.len(), bufs.len());

        g.drain(0..num_pkts)
            .zip(bufs.drain(0..num_pkts))
            .for_each(|(pkt, mut recv_buf)| {
                recv_buf.0.copy_from_slice(&pkt);
                recvd_bufs.push_back(recv_buf);
            });

        Ok(num_pkts)
    }
}

#[cfg(test)]
mod test {
    use core::iter::repeat;

    use alloc::collections::VecDeque;
    use pnet::packet::{
        ethernet::EthernetPacket, ipv4::Ipv4Packet, udp::UdpPacket, FromPacket, Packet,
    };

    use crate::{nic::Net, util::RawPacket};

    use super::DummyNic;

    fn assert_echo(sent: &[u8], recvd: &[u8]) {
        let sent_frame = EthernetPacket::new(sent).unwrap();
        let recvd_frame = EthernetPacket::new(recvd).unwrap();

        assert_eq!(sent_frame.get_source(), recvd_frame.get_destination());
        assert_eq!(sent_frame.get_destination(), recvd_frame.get_source());
        assert_eq!(sent_frame.get_ethertype(), recvd_frame.get_ethertype());

        let sent_ip = Ipv4Packet::new(sent_frame.payload()).unwrap();
        let recvd_ip = Ipv4Packet::new(recvd_frame.payload()).unwrap();

        assert_eq!(sent_ip.get_source(), recvd_ip.get_destination());
        assert_eq!(sent_ip.get_destination(), recvd_ip.get_source());
        assert_eq!(sent_ip.get_ttl(), recvd_ip.get_ttl() + 1);
        assert_eq!(
            sent_ip.get_next_level_protocol(),
            recvd_ip.get_next_level_protocol()
        );

        let sent_udp = UdpPacket::new(sent_ip.payload()).unwrap();
        let recvd_udp = UdpPacket::new(recvd_ip.payload()).unwrap();

        assert_eq!(sent_udp.get_source(), recvd_udp.get_destination());
        assert_eq!(sent_udp.get_destination(), recvd_udp.get_source());
        assert_eq!(sent_udp.payload(), recvd_udp.payload());
    }

    #[test]
    pub fn test_dummy_nic_send() {
        let nic = DummyNic::new();

        let mut packet_buf = RawPacket::default();
        let data = [
            74, 228, 110, 95, 212, 240, 246, 212, 136, 199, 229, 100, 8, 0, 69, 0, 0, 41, 0, 0, 0,
            0, 64, 17, 0, 0, 192, 168, 64, 9, 192, 168, 64, 1, 31, 64, 31, 64, 0, 21, 0, 0, 104,
            101, 108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 33,
        ];

        packet_buf.0[..data.len()].copy_from_slice(&data);

        let (sent, packet_buf) = nic.submit(packet_buf).unwrap();

        assert!(sent);

        let mut free_bufs: VecDeque<RawPacket> = repeat(RawPacket::default()).take(8).collect();

        let mut recvd_bufs = VecDeque::new();

        let num_recvd = nic.poll_batch(&mut free_bufs, &mut recvd_bufs).unwrap();

        assert_eq!(num_recvd, 1);

        let recvd_packet = recvd_bufs.pop_front().unwrap();

        assert_echo(&packet_buf.0, &recvd_packet.0);
    }

    #[test]
    pub fn test_dummy_nic_send_batch() {
        let nic = DummyNic::new();

        let mut packet_buf = RawPacket::default();
        let data = [
            74, 228, 110, 95, 212, 240, 246, 212, 136, 199, 229, 100, 8, 0, 69, 0, 0, 41, 0, 0, 0,
            0, 64, 17, 0, 0, 192, 168, 64, 9, 192, 168, 64, 1, 31, 64, 31, 64, 0, 21, 0, 0, 104,
            101, 108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 33,
        ];

        packet_buf.0[..data.len()].copy_from_slice(&data);

        let mut batch = repeat(packet_buf).take(32).collect();
        let mut returned_bufs = VecDeque::new();

        let num_sent = nic.submit_batch(&mut batch, &mut returned_bufs).unwrap();

        assert_eq!(num_sent, 32);
        assert_eq!(returned_bufs.len(), 32);

        let mut recv_bufs = repeat(RawPacket::default()).take(16).collect();
        let mut recvd_batch = VecDeque::new();

        let num_recvd = nic.poll_batch(&mut recv_bufs, &mut recvd_batch).unwrap();

        assert_eq!(num_recvd, 16);
        assert_eq!(recvd_batch.len(), 16);

        recvd_batch
            .iter()
            .for_each(|pkt| assert_echo(&data, &pkt.0));
    }
}
