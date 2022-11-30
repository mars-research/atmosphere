#![cfg(test)]

use std::{str::FromStr, net::SocketAddr};
use std::net::UdpSocket;

const TAP_MAC: &'static str = "02:aa:aa:aa:aa:aa";
const ANET_MAC: &'static str = "02:bb:bb:bb:bb:bb";

use crate::{
    arp::ArpTable,
    layer::ip::routing::{RoutingTable, RoutingEntry},
    netmanager::NetManager,
    nic::TapDevice,
    packet::RawPacket,
    stack::udp::UdpStack,
    util::{Ipv4Address, MacAddress, SocketAddress},
};

use alloc::{collections::VecDeque, sync::Arc};

lazy_static::lazy_static! {
    static ref TAP: Arc<TapDevice> = Arc::new(TapDevice::new("tap1"));
    static ref SOCKET: UdpSocket = UdpSocket::bind("10.0.0.1:3000").unwrap();
}

fn create_udp_stack() -> UdpStack<TapDevice> {
    let nic = TAP.clone();
    let arp_table = Arc::new(ArpTable::new());
    arp_table.add_static_entry(Ipv4Address::from_str("10.0.0.1").unwrap(), MacAddress::from_str(TAP_MAC).unwrap());

    let mut routing_table = RoutingTable::new();
    routing_table.set_default_gateway(Ipv4Address::new(10, 0, 0, 1));
    routing_table.insert_rule(Ipv4Address::new(10, 0, 0, 1), 24, RoutingEntry::DirectlyConnected);

    let netman = Arc::new(NetManager {});

    let endpoint = SocketAddress::new(Ipv4Address::new(10, 0, 0, 2), 8000);

    UdpStack::new(
        endpoint,
        netman,
        nic,
        MacAddress::from_str(ANET_MAC).unwrap(),
        routing_table,
        arp_table,
    )
}

#[test]
pub fn test_udp_send() -> Result<(), ()> {
    let stack = create_udp_stack();

    let mut free_bufs = VecDeque::from(vec![RawPacket::default(); 32]);
    let mut send_batch = VecDeque::new();
    let mut recv_buf = [0; 1024];

    let src = stack.endpoint();
    let dst = match SOCKET.local_addr().unwrap() {
        std::net::SocketAddr::V4(a) => a,
        std::net::SocketAddr::V6(_) => todo!()
    };

    let data = b"hello, world!";

    stack.prepare_batch(&mut free_bufs, &mut send_batch, dst, data)?;
    let num_sent = stack.send_batch(&mut send_batch, &mut free_bufs)?;

    let (n_bytes, remote) = SOCKET.recv_from(&mut recv_buf).expect("failed to recv on socket");

    assert_eq!(num_sent, 1);
    assert_eq!(&recv_buf[..n_bytes], data);
    assert_eq!(remote, SocketAddr::V4(src));


    Ok(())
}

#[test]
pub fn test_udp_recv() -> Result<(), ()> {
    let stack = create_udp_stack();

    let mut free_bufs = VecDeque::from(vec![RawPacket::default(); 32]);
    let mut recv_batch = VecDeque::new();

    let src = match SOCKET.local_addr().unwrap() {
        std::net::SocketAddr::V4(a) => a,
        std::net::SocketAddr::V6(_) => todo!()
    };
    let dst = SocketAddr::V4(stack.endpoint());

    let data = b"hello, world!";

    let bytes_sent = (*SOCKET).send_to(data, dst).unwrap();

    stack.recv_batch(&mut free_bufs, &mut recv_batch)?;

    let packet = recv_batch.pop_front().unwrap();

    assert_eq!(packet.udp_payload(), data);

    Ok(())
}
