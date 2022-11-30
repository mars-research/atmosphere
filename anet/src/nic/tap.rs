use pnet::packet;

use crate::packet::RawPacket;

use super::Net;

pub struct TapDevice {
    tap: tun_tap::Iface,
}

impl TapDevice {
    pub fn new(name: &str) -> Self {
        let tap = tun_tap::Iface::without_packet_info(name, tun_tap::Mode::Tap)
            .expect("failed to open tap interface");
        Self { tap }
    }
}

impl Net for TapDevice {
    fn submit(
        &self,
        buf: crate::packet::RawPacket,
    ) -> crate::RpcResult<(bool, crate::packet::RawPacket)> {
        let bytes = self.tap.send(&buf.0).expect("failed to send on tap device");
        if bytes < buf.0.len() {
            panic!("failed to send");
        } else {
            Ok((true, buf))
        }
    }

    fn submit_batch(
        &self,
        bufs: &mut std::collections::VecDeque<crate::packet::RawPacket>,
        return_bufs: &mut std::collections::VecDeque<crate::packet::RawPacket>,
    ) -> crate::RpcResult<usize> {
        let mut n_submitted = 0;
        while let Some(buf) = bufs.pop_front() {
            let (sent, buf) = self.submit(buf).expect("failed to submit packet");
            return_bufs.push_back(buf);
            if sent {
                n_submitted += 1;
            } else {
                break;
            }
        }
        Ok(n_submitted)
    }

    fn poll(
        &self,
        mut buf: crate::packet::RawPacket,
    ) -> crate::RpcResult<(bool, crate::packet::RawPacket)> {
        Ok(self
            .tap
            .recv(&mut buf.0)
            .map_or((true, buf), |_| (false, buf)))
    }

    fn poll_batch(
        &self,
        bufs: &mut std::collections::VecDeque<crate::packet::RawPacket>,
        recvd_bufs: &mut std::collections::VecDeque<crate::packet::RawPacket>,
    ) -> crate::RpcResult<usize> {
        let mut n_recvd = 0;
        while let Some(buf) = bufs.pop_front() {
            let (recvd, buf) = self.poll(buf).expect("failed to recv packet");
            recvd_bufs.push_back(buf);
            if recvd {
                n_recvd += 1;
            } else {
                break;
            }
        }
        Ok(n_recvd)
    }
}
