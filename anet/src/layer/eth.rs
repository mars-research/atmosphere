use core::cell::RefCell;

use alloc::{
    sync::Arc,
    vec::Vec, collections::VecDeque,
};

// use pnet::packet::ethernet::EthernetPacket;

use crate::address::MacAddress;

// Replace with actual NIC
pub struct Nic;

impl Nic {
    pub fn recv(&self) -> (&[u8], Vec<u8>) {
        todo!()
    }

    pub fn send(&self, buffer: Vec<u8>, payload: &[u8]) {
        todo!()
    }
}

pub enum EtherType {
    Ipv4 = 0x800,
    Arp = 0x806,
}

pub struct EthernetLayer {
    endpoint: MacAddress,
    rx_queue: RefCell<VecDeque<[u8; 1514]>>,
    tx_queue: RefCell<VecDeque<[u8; 1514]>>,
}

impl EthernetLayer {
    pub fn new(endpoint: MacAddress) -> Self {
        let tx_queue = RefCell::new(VecDeque::new());
        let rx_queue = RefCell::new(VecDeque::new());

        Self { endpoint, tx_queue, rx_queue }
    }

    pub fn enqueue_packet<F>(&self, f: F) -> Result<usize, ()>
    where
        F: FnOnce(&mut [u8]) -> usize,
    {
        let mut packet_buf: [u8; 1514] = [0; 1514];

        let packet_size = f(&mut packet_buf);

        self.tx_queue.borrow_mut().push_back(packet_buf);

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
