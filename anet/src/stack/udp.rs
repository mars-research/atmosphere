use alloc::collections::VecDeque;
use alloc::sync::Arc;
use pnet::packet::ip::IpNextHeaderProtocols;
use pnet::util::MacAddr;
use thingbuf::mpsc::Sender;

use crate::arp::ArpTable;
use crate::layer::ip::routing::{RoutingEntry, RoutingResult, RoutingTable};
use crate::layer::{eth::EthernetLayer, ip::Ipv4Layer, udp::UdpLayer};
use crate::netmanager::NetManager;
use crate::nic::Net;
use crate::packet::{RawPacket, UdpPacketRepr};
use crate::util::{read_proto_and_port, SocketAddress};

pub struct UdpStack<Dev: Net> {
    endpoint: SocketAddress,
    udp_layer: UdpLayer,
    ipv4_layer: Ipv4Layer,
    routing_table: RoutingTable,
    eth_layer: EthernetLayer,
    rx_queue: Sender<RawPacket>,
    arp_table: Arc<ArpTable>,
    manager: Arc<NetManager>,
    pub(crate) nic: Arc<Dev>,
}

impl<Dev: Net> UdpStack<Dev> {
    pub fn new(
        endpoint: SocketAddress,
        manager: Arc<NetManager>,
        nic: Arc<Dev>,
        mac_addr: MacAddr,
        routing_table: RoutingTable,
        arp_table: Arc<ArpTable>,
    ) -> Self {
        let (rx_queue, rx_dequeue) = thingbuf::mpsc::channel(32);

        let eth_layer = EthernetLayer::new(mac_addr);
        let ipv4_layer = Ipv4Layer::new(*endpoint.ip());

        let udp_layer = UdpLayer::new(endpoint.port());

        Self {
            endpoint,
            manager,
            udp_layer,
            ipv4_layer,
            routing_table,
            eth_layer,
            rx_queue,
            nic,
            arp_table,
        }
    }

    pub fn prepare_batch(
        &self,
        buffers: &mut VecDeque<RawPacket>,
        packets: &mut VecDeque<UdpPacketRepr>,
        dest: SocketAddress,
        payload: &[u8],
    ) -> Result<usize, ()> {
        let mut bytes = 0;

        while let Some(buf) = buffers.pop_front() {
            if bytes >= payload.len() {
                buffers.push_back(buf);
                break;
            }
            let mut packet = UdpPacketRepr::from(buf);
            packet.set_udp_payload(|buf: &mut [u8]| {
                let len = core::cmp::min(buf.len(), payload[bytes..].len());
                buf[..len].copy_from_slice(&payload[bytes..len]);

                bytes += len;

                len
            });
            packets.push_back(packet);
        }

        self.udp_layer.prepare_udp_batch(dest.port(), packets);
        self.ipv4_layer.prepare_udp_batch(*dest.ip(), packets);

        let next_ip = match self.routing_table.resolve(*dest.ip()) {
            RoutingResult::Reachable(entry) => match entry {
                RoutingEntry::Gateway(ip) => ip,
                RoutingEntry::DirectlyConnected => *dest.ip(),
            },
            RoutingResult::Unreachable => panic!("unreachable ipv4 address"),
        };

        let dmac = self.arp_table.resolve(&next_ip);

        self.eth_layer.prepare_udp_batch(dmac, packets);

        Ok(packets.len())
    }

    pub fn send_batch(
        &self,
        packets: &mut VecDeque<UdpPacketRepr>,
        returned: &mut VecDeque<RawPacket>,
    ) -> Result<usize, ()> {
        self.nic
            .submit_batch(
                &mut packets
                    .drain(..packets.len())
                    .map(|p| p.consume())
                    .rev()
                    .collect(),
                returned,
            )
            .map_err(|_| ())
    }

    pub fn recv_batch(
        &self,
        bufs: &mut VecDeque<RawPacket>,
        returned: &mut VecDeque<UdpPacketRepr>,
    ) -> Result<usize, ()> {
        let mut returned_bufs = VecDeque::new();
        self.nic
            .poll_batch(bufs, &mut returned_bufs)
            .map_err(|_| ())?;
        let mut num_pkts = 0;

        for buf in returned_bufs {
            if let Ok((proto, port)) = read_proto_and_port(&buf.0) {
                if proto == IpNextHeaderProtocols::Udp && port == self.endpoint.port() {
                    returned.push_back(UdpPacketRepr::from(buf));
                    num_pkts += 1;
                } else {
                    // TODO: flip with demuxer
                    bufs.push_back(buf);
                }
            } else {
                // drop
                bufs.push_back(buf);
            }
        }

        Ok(num_pkts)
    }

    pub fn endpoint(&self) -> SocketAddress {
        self.endpoint
    }
}
// first you request from demuxer
// then request from nic?
