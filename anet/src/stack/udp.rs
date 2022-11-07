use alloc::sync::Arc;
use thingbuf::mpsc::{Receiver, Sender};

use crate::arp::ArpTable;
use crate::layer::ip::routing::RoutingTable;
use crate::layer::{eth::EthernetLayer, ip::Ipv4Layer, udp::UdpLayer};
use crate::util::{Ipv4Address, MacAddress, Port, RawPacket, SocketAddress};

pub struct UdpStack {
    udp: Arc<UdpLayer>,
    pub(crate) tx_dequeue: Receiver<RawPacket>,
    pub(crate) rx_queue: Sender<RawPacket>,
}

impl UdpStack {
    pub fn new(
        udp_port: Port,
        ipv4_addr: Ipv4Address,
        mac_addr: MacAddress,
        routing_table: RoutingTable,
        arp_table: Arc<ArpTable>,
    ) -> Self {
        let (tx_queue, tx_dequeue) = thingbuf::mpsc::channel(32);
        let (rx_queue, rx_dequeue) = thingbuf::mpsc::channel(32);

        let eth_layer = Arc::new(EthernetLayer::new(mac_addr, tx_queue, rx_dequeue));
        let ipv4_layer = Arc::new(Ipv4Layer::new(ipv4_addr, routing_table, arp_table, eth_layer.clone()));
        let udp_layer = Arc::new(UdpLayer::new(udp_port, ipv4_layer.clone()));

        Self {
            udp: udp_layer,
            tx_dequeue,
            rx_queue,
        }
    }

    pub fn send<F>(&self, dst: SocketAddress, payload: F) -> Result<usize, ()>
    where
        F: FnOnce(&mut [u8]) -> usize,
    {
        // TODO: ideally, do fragmentation here
        self.udp.send_packet(dst, payload)
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
