#![cfg(test)]

use crate::{
    arp::ArpTable,
    layer::ip::routing::RoutingTable,
    netmanager::NetManager,
    nic::{DummyNic, Net},
    packet::RawPacket,
    stack::udp::UdpStack,
    util::{Ipv4Address, MacAddress, SocketAddress},
};

use alloc::{collections::VecDeque, sync::Arc};

use pnet::packet::{ethernet::EthernetPacket, ipv4::Ipv4Packet, udp::UdpPacket, Packet};

fn create_udp_stack() -> UdpStack {
    let arp_table = Arc::new(ArpTable::new());

    let mut routing_table = RoutingTable::new();
    routing_table.set_default_gateway(Ipv4Address::new(192, 168, 64, 1));

    let netman = Arc::new(NetManager {});

    let nic = Arc::new(DummyNic::new());

    UdpStack::new(
        8000,
        netman,
        nic,
        Ipv4Address::new(192, 168, 64, 9),
        MacAddress::new(0x4a, 0xe4, 0x6e, 0x5f, 0xd4, 0xf0),
        routing_table,
        arp_table,
    )
}

#[test]
pub fn test_udp_send() -> Result<(), ()> {
    let stack = create_udp_stack();

    let mut free_bufs = VecDeque::from(vec![RawPacket::default(); 32]);
    let mut send_batch = VecDeque::new();

    let dst = SocketAddress::new(Ipv4Address::new(8, 8, 8, 8), 8000);

    let data = b"hello, world!";

    stack.prepare_batch(&mut free_bufs, &mut send_batch, dst, data)?;

    stack.send_batch(&mut send_batch, &mut free_bufs)?;

    let packet = RawPacket::default();
    let (did_recv, packet) = stack.nic.poll(packet).unwrap();

    assert!(did_recv);

    println!("{:?}", packet);

    let eth = dbg!(EthernetPacket::new(&packet.0).expect("invalid ethernet header"));

    let ipv4 = dbg!(Ipv4Packet::new(eth.payload()).expect("invalid ipv4 header"));

    println!("{:?}", ipv4.payload());

    let udp = dbg!(UdpPacket::new(ipv4.payload()).expect("invalid udp header"));

    assert_eq!(udp.payload(), data);

    assert_eq!(packet.0, *eth.packet());

    println!("{}", eth.packet().len());

    Ok(())
}

#[test]
pub fn test_udp_recv() -> Result<(), ()> {
    let stack = create_udp_stack();
    let mut free_bufs = VecDeque::from(vec![RawPacket::default(); 32]);
    let mut recv_batch = VecDeque::new();

    let mut raw_packet = RawPacket::default();
    let data = [
        74, 228, 110, 95, 212, 240, 246, 212, 136, 199, 229, 100, 8, 0, 69, 0, 0, 41, 0, 0, 0, 0,
        64, 17, 0, 0, 192, 168, 64, 1, 192, 168, 64, 9, 31, 64, 31, 64, 0, 21, 0, 0, 104, 101, 108,
        108, 111, 44, 32, 119, 111, 114, 108, 100, 33,
    ];

    raw_packet.0[..data.len()].copy_from_slice(&data);

    // queue packet in the nic
    let (sent, raw_packet) = stack.nic.submit(raw_packet).map_err(|_| ())?;

    assert!(sent);

    stack.recv_batch(&mut free_bufs, &mut recv_batch)?;

    let repr = recv_batch.pop_back().unwrap();

    let recvd_packet = repr.udp_packet();

    Ok(())
}

#[test]
pub fn test_udp_echo() -> Result<(), ()> {
    let stack = create_udp_stack();
    let mut free_bufs = VecDeque::from(vec![RawPacket::default(); 32]);
    let mut recv_batch = VecDeque::new();
    let mut send_batch = VecDeque::new();

    let dst = SocketAddress::new(Ipv4Address::new(8, 8, 8, 8), 5454);

    let data = b"hello, world!";

    stack.prepare_batch(&mut free_bufs, &mut send_batch, dst, data)?;

    stack.send_batch(&mut send_batch, &mut free_bufs)?;

    stack.recv_batch(&mut free_bufs, &mut recv_batch)?;

    let repr = recv_batch.pop_back().unwrap();

    let payload = repr.udp_payload();

    assert_eq!(data, payload);

    Ok(())
}
