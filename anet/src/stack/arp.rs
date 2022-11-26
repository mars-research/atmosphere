// use alloc::sync::Arc;
// use thingbuf::mpsc::{Receiver, Sender};

// use crate::{
//     layer::arp::ArpLayer,
//     util::{Ipv4Address, MacAddress},
//     packet::RawPacket,
// };

// pub struct ArpStack {
//     arp: Arc<ArpLayer>,
//     pub(crate) tx_dequeue: Receiver<RawPacket>,
//     pub(crate) rx_queue: Sender<RawPacket>,
// }

// impl ArpStack {
//     pub fn new(mac_addr: MacAddress, ipv4_addr: Ipv4Address) -> Self {
//         // let (tx_queue, tx_dequeue) = thingbuf::mpsc::channel(32);
//         // let (rx_queue, rx_dequeue) = thingbuf::mpsc::channel(32);

//         // let eth_layer = Arc::new(EthernetLayer::new(mac_addr, tx_queue, rx_dequeue));

//         // let arp_layer = Arc::new(ArpLayer::new(mac_addr, ipv4_addr, eth_layer));

//         // Self {
//         //     arp: arp_layer,
//         //     tx_dequeue,
//         //     rx_queue,
//         // }
//         todo!()
//     }
// }
