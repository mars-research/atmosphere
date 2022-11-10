use core::borrow::{BorrowMut, Borrow};

use alloc::sync::Arc;
use thingbuf::mpsc::{Receiver, Sender};

use crate::{util::{MacAddress, RawPacket}, netmanager::NetManager};

pub enum EtherType {
    Ipv4 = 0x800,
    Arp = 0x806,
}

pub struct EthernetLayer {
    endpoint: MacAddress,
    tx_queue: Sender<RawPacket>,
    rx_dequeue: Receiver<RawPacket>,
    manager: Arc<NetManager>,
}

impl EthernetLayer {
    pub fn new(
        endpoint: MacAddress,
        tx_queue: Sender<RawPacket>,
        rx_dequeue: Receiver<RawPacket>,
        manager: Arc<NetManager>,
    ) -> Self {
        Self {
            endpoint,
            tx_queue,
            rx_dequeue,
            manager,
        }
    }

    fn enqueue_packet<F>(&self, f: F) -> Result<usize, ()>
    where
        F: FnOnce(&mut [u8]) -> usize,
    {
        let mut raw_packet = self.manager.get_packet_buf().expect("failed to receive a packet buffer");

        let packet_size = f(&mut raw_packet.0);

        self.tx_queue.try_send(raw_packet).map_err(|_| ())?;

        Ok(packet_size)
    }

    fn dequeue_packet<F>(&self, f: F) -> Result<(), ()>
    where
        F: FnOnce(&[u8]) -> ()
    {
        let packet = self.rx_dequeue.try_recv().map_err(|_| ())?;

        f(&packet.0);

        // self.manager.give_back(packet);
        Ok(())
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

    pub fn recv_packet<F>(&self, f: F) -> Result<MacAddress, ()> 
    where
        F: FnOnce(MacAddress, &[u8]) -> ()
    {
        let mut mac_addr = MacAddress::default();

        self.dequeue_packet(|packet: &[u8]| {
            mac_addr = MacAddress::from_slice(&packet[0..6]);
            f(mac_addr, &packet[14..]);
        })?;

        Ok(mac_addr)
    }
}


// let data = [0; 1024];
// socket.recv_with(|packet: &[u8], remote_addr: SocketAddress| {
//      data.copy_from_slice(packet);
// })
//
