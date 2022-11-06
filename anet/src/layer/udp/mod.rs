use alloc::sync::Arc;

use crate::util::{Port, SocketAddress};

use super::ip::Ipv4Layer;

pub struct UdpLayer {
    endpoint: Port,
    lower: Arc<Ipv4Layer>,
}

impl UdpLayer {
    pub fn new(endpoint: Port, lower: Arc<Ipv4Layer>) -> Self {
        Self { endpoint, lower }
    }

    pub fn send_packet<F>(&self, addr: SocketAddress, f: F) -> Result<usize, ()>
    where
        F: FnOnce(&mut [u8]) -> usize,
    {
        self.lower.send_packet(addr.ip, |buf: &mut [u8]| {
            buf[0..2].copy_from_slice(&self.endpoint.to_be_bytes());
            buf[2..4].copy_from_slice(&addr.port.to_be_bytes());

            let udp_payload_len: u16 = f(&mut buf[8..])
                .try_into()
                .expect("udp payload len overflowed");

            buf[4..6].copy_from_slice(&udp_payload_len.to_be_bytes());

            buf[6..8].copy_from_slice(&[0, 0]);

            (udp_payload_len + 8).into()
        })
    }
}
