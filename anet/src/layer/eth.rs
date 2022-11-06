use thingbuf::mpsc::{Sender, Receiver};

use crate::util::{MacAddress, RawPacket};

pub enum EtherType {
    Ipv4 = 0x800,
    Arp = 0x806,
}

pub struct EthernetLayer {
    endpoint: MacAddress,
    tx_queue: Sender<RawPacket>,
    rx_dequeue: Receiver<RawPacket>,
}

impl EthernetLayer {
    pub fn new(endpoint: MacAddress, tx_queue: Sender<RawPacket>, rx_dequeue: Receiver<RawPacket>) -> Self {
        Self { endpoint, tx_queue, rx_dequeue }
    }

    pub fn enqueue_packet<F>(&self, f: F) -> Result<usize, ()>
    where
        F: FnOnce(&mut [u8]) -> usize,
    {
        let mut raw_packet = RawPacket::default();

        let packet_size = f(&mut raw_packet.0);

        self.tx_queue.try_send(raw_packet).map_err(|_| ())?;

        Ok(packet_size)
    }

    pub fn send_packet<F>(&self, dmac: MacAddress, ether_type: EtherType, f: F) -> Result<usize, ()>
    where
        F: FnOnce(&mut [u8]) -> usize,
    {
        self.enqueue_packet(|buf: &mut [u8]| {
            buf[0..6].copy_from_slice(&self.endpoint.0);
            buf[6..12].copy_from_slice(&dmac.0);

            buf[12..14].copy_from_slice(&(ether_type as u16).to_be_bytes());

            let payload_len = f(&mut buf[14..1504]);

            payload_len + 14
        })
    }
}
