#![cfg(test)]

use alloc::sync::Arc;

use crate::{
    arp::ArpTable,
    stack::udp::UdpStack,
    util::{Ipv4Address, MacAddress, SocketAddress}, layer::ip::routing::RoutingTable,
};

use pnet::packet::{ethernet::EthernetPacket, ipv4::Ipv4Packet, udp::UdpPacket, Packet};

#[test]
pub fn test_udp_stack() -> Result<(), ()> {
    let arp_table = Arc::new(ArpTable::new());

    let mut routing_table = RoutingTable::new();
    routing_table.set_default_gateway(Ipv4Address::new([192, 168, 64, 1]));

    let stack = UdpStack::new(
        8000,
        Ipv4Address::new([192, 168, 64, 9]),
        MacAddress::new([0x4a, 0xe4, 0x6e, 0x5f, 0xd4, 0xf0]),
        routing_table,
        arp_table,
    );

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

    Ok(())
}
