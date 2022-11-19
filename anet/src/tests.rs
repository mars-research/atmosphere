#![cfg(test)]
use crate::{
    arp::ArpTable,
    layer::ip::routing::RoutingTable,
    stack::udp::UdpStack,
    util::{Ipv4Address, MacAddress, SocketAddress, RawPacket}, netmanager::NetManager, nic::DummyNic};

use alloc::sync::Arc;

use pnet::packet::{ethernet::EthernetPacket, ipv4::Ipv4Packet, udp::UdpPacket, Packet};

fn create_udp_stack() -> UdpStack {
    let arp_table = Arc::new(ArpTable::new());

    let mut routing_table = RoutingTable::new();
    routing_table.set_default_gateway(Ipv4Address::new([192, 168, 64, 1]));

    let netman = Arc::new(NetManager {});

    let nic_handle = Arc::new(DummyNic::new());

    UdpStack::new(
        8000,
        netman,
        nic_handle,
        Ipv4Address::new([192, 168, 64, 9]),
        MacAddress::new([0x4a, 0xe4, 0x6e, 0x5f, 0xd4, 0xf0]),
        routing_table,
        arp_table,
    )
}

#[test]
pub fn test_udp_send() -> Result<(), ()> {
    
    let stack = create_udp_stack();

    let dst = SocketAddress::new(Ipv4Address::new([8, 8, 8, 8]), 8000);

    let data = b"hello, world!";

    stack.send(dst, |buf: &mut [u8]| {
        buf[0..data.len()].copy_from_slice(data);

        data.len()
    })?;

    let packet = stack.tx_dequeue.try_recv().expect("packet wasn't queued");

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

    let mut raw_packet = RawPacket::default();
    let payload = [74, 228, 110, 95, 212, 240, 246, 212, 136, 199, 229, 100, 8, 0, 69, 0, 0, 41, 0, 0, 0, 0, 64, 17, 0, 0, 192, 168, 64, 9, 192, 168, 64, 1, 31, 64, 31, 64, 0, 21, 0, 0, 104, 101, 108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 33];

    raw_packet.0[..payload.len()].copy_from_slice(&payload);

    // queue packet in the receive ring
    stack.rx_queue.try_send(raw_packet).map_err(|_|())?;
    
    stack.recv(|remote: SocketAddress, payload: &[u8]| {
        assert_eq!(remote, SocketAddress { ip: Ipv4Address([192, 168, 64, 9]), port: 8000});
        assert_eq!(payload, b"hello, world!");
    })?;


    Ok(())
}


