use core::iter;

use alloc::sync::Arc;
use thingbuf::mpsc::Sender;

use crate::arp::ArpTable;
use crate::layer::ip::routing::RoutingTable;
use crate::layer::{eth::EthernetLayer, ip::Ipv4Layer, udp::UdpLayer};
use crate::netmanager::NetManager;
use crate::nic::{DummyNic, Net};
use crate::util::{Ipv4Address, MacAddress, Port, RawPacket, SocketAddress, VacantBufs, read_proto_and_port};

pub struct UdpStack {
    port: Port,
    udp: Arc<UdpLayer>,
    rx_queue: Sender<RawPacket>,
    manager: Arc<NetManager>,
    vacant_bufs: Arc<VacantBufs>,
    pub(crate) nic: Arc<DummyNic>,
}

impl UdpStack {
    pub fn new(
        port: Port,
        manager: Arc<NetManager>,
        nic: Arc<DummyNic>,
        ipv4_addr: Ipv4Address,
        mac_addr: MacAddress,
        routing_table: RoutingTable,
        arp_table: Arc<ArpTable>,
    ) -> Self {
        let (rx_queue, rx_dequeue) = thingbuf::mpsc::channel(32);
        let mut vacant_bufs = Arc::new(VacantBufs::new(32));
        iter::repeat(RawPacket::default()).take(32).for_each(|buf| vacant_bufs.push(buf).expect("32 != 32"));
        //
        let nic = Arc::new(DummyNic::new());

        let eth = Arc::new(EthernetLayer::new(
            mac_addr,
        ));
        let ipv4 = Arc::new(Ipv4Layer::new(
            ipv4_addr,
            routing_table,
            arp_table,
            eth.clone(),
        ));

        let udp = Arc::new(UdpLayer::new(port, ipv4.clone()));

        Self {
            port,
            manager,
            udp,
            rx_queue,
            vacant_bufs,
            nic,
        }
    }

    pub fn send<F>(&self, dst: SocketAddress, payload: F) -> Result<usize, ()>
    where
        F: FnOnce(&mut [u8]) -> usize,
    {
        // get packet buffer
        let mut packet_buf = self.vacant_bufs.pop().expect("no vacant_buf available");

        let len = self.udp.send_packet(&mut packet_buf.0, dst, payload)?;

        let (sent, free_buf) = self.nic.submit(packet_buf).expect("nic submit call failed");
        // return packet buffer
        self.vacant_bufs.push(free_buf).expect("more buffers returned than taken");

        if sent {
            Ok(len)
        } else {
            Err(())
        }
    }

    pub fn recv<F>(&self, f: F) -> Result<SocketAddress, ()>
    where
        F: FnOnce(SocketAddress, &[u8]) -> (),
    {
        // take buffer
        let buf = self.vacant_bufs.pop().expect("no vacant buffer available");

        let (recvd, buf) = self.nic.poll(buf).expect("failed to poll nic");

        if recvd {
            let (proto, port) = read_proto_and_port(&buf.0);

            if port == self.port {
                self.udp.recv_packet(&buf.0, f)
            } else {
                // flip packet with demuxer
                Err(())
            }
        } else {
            self.vacant_bufs.push(buf).expect("more bufs returned than taken");
            Err(())
        }
    }
}
