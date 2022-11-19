use core::cell::RefCell;

use alloc::sync::Arc;
use alloc::vec::Vec;
use alloc::vec;
use thingbuf::mpsc::{Receiver, Sender};

use crate::nic::DummyNic;
use crate::arp::ArpTable;
use crate::layer::ip::routing::RoutingTable;
use crate::layer::{eth::EthernetLayer, ip::Ipv4Layer, udp::UdpLayer};
use crate::netmanager::NetManager;
use crate::util::{Ipv4Address, MacAddress, Port, RawPacket, SocketAddress};

pub struct UdpStack {
    udp: Arc<UdpLayer>,
    pub tx_dequeue: Receiver<RawPacket>,
    pub rx_queue: Sender<RawPacket>,
    pub manager: Arc<NetManager>,
    pub vacant_bufs: RefCell<Vec<RawPacket>>,
}

impl UdpStack {
    pub fn new(
        udp_port: Port,
        manager: Arc<NetManager>,
        nic_handle: Arc<DummyNic>,
        ipv4_addr: Ipv4Address,
        mac_addr: MacAddress,
        routing_table: RoutingTable,
        arp_table: Arc<ArpTable>,
    ) -> Self {
        let (tx_queue, tx_dequeue) = thingbuf::mpsc::channel(32);
        let (rx_queue, rx_dequeue) = thingbuf::mpsc::channel(32);

        let eth = Arc::new(EthernetLayer::new(mac_addr, tx_queue, rx_dequeue, manager.clone()));
        let ipv4 = Arc::new(Ipv4Layer::new(
            ipv4_addr,
            routing_table,
            arp_table,
            eth.clone(),
        ));

        let udp = Arc::new(UdpLayer::new(udp_port, ipv4.clone()));

        let vacant_bufs = RefCell::new(vec![RawPacket::default(); 32]);

        Self {
            manager,
            udp,
            tx_dequeue,
            rx_queue,
            vacant_bufs,
        }
    }

    pub fn send<F>(&self, dst: SocketAddress, payload: F) -> Result<usize, ()>
    where
        F: FnOnce(&mut [u8]) -> usize,
    {
        // TODO: ideally, do fragmentation here
        self.udp.send_packet(dst, payload)
    }

    pub fn recv<F>(&self, f: F) -> Result<SocketAddress, ()> 
    where
        F: FnOnce(SocketAddress, &[u8]) -> ()
    {
        self.udp.recv_packet(f)
    }

    pub fn run() {
        // TODO:
        // Run the UDP Stack
        // 2 threads: one for rx one for tx.
        // on receiving a packet from the dispatcher, rx thread will queue it in the rx_queue.
        // packet gets dequeued when application calls socket.recv()
        // for sending a packet, a packet_buffer is allocated application calls socket.send()
        // socket.send() will call the subsequent layers and construct a packet in the buffer.
        // the packet then gets queued in the tx_queue.
    }
}
