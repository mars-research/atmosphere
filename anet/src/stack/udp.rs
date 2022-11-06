use alloc::{collections::VecDeque, sync::Arc, vec::Vec};

use crate::address::{MacAddress, Ipv4Address, Port};
use crate::arp::ArpTable;
use crate::layer::{eth::EthernetLayer, eth::Nic, ip::Ipv4Layer, udp::UdpLayer};

pub struct UdpStack {
    udp: Arc<UdpLayer>,
}

impl UdpStack {
    pub fn new(udp_port: Port, ipv4_addr: Ipv4Address, mac_addr: MacAddress, nic: Arc<Nic>, arp_table: Arc<ArpTable>) -> Self {
        let eth_layer = Arc::new(EthernetLayer::new(mac_addr));
        let ipv4_layer = Arc::new(Ipv4Layer::new(ipv4_addr, arp_table, eth_layer.clone()));
        let udp_layer = Arc::new(UdpLayer::new(udp_port, ipv4_layer.clone()));

        Self {
            udp: udp_layer,
        }
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
