use alloc::{sync::Arc, borrow::ToOwned};

use crate::{arp::ArpTable, util::Ipv4Address};

use self::routing::RoutingTable;

use super::eth::EthernetLayer;

mod routing;

const IPV4_VERSION: u8 = 4;
const IPV4_HDR_LEN: u8 = 5;

pub struct Ipv4Layer {
    endpoint: Ipv4Address,
    arp_table: Arc<ArpTable>,
    routing_table: RoutingTable,
    pub(crate) lower: Arc<EthernetLayer>,
}

impl Ipv4Layer {
    pub fn new(endpoint: Ipv4Address, arp_table: Arc<ArpTable>, lower: Arc<EthernetLayer>) -> Self {
        let routing_table = RoutingTable::new();
        Self {
            endpoint,
            arp_table,
            routing_table,
            lower,
        }
    }

    pub fn send_packet<F>(&self, dst_addr: Ipv4Address, f: F) -> Result<usize, ()> 
    where
        F: FnOnce(&mut [u8]) -> usize,
    {
        let next_hop_ip = self.routing_table.resolve(dst_addr);
        let dmac = self.arp_table.resolve(&next_hop_ip);

        self.lower.send_packet(dmac, super::eth::EtherType::Ipv4, |buf: &mut [u8]| {
            // write ipv4 header here
            // buf[0..20].copy_from_slice(&[0; 20]);
            buf[0] = (IPV4_VERSION << 4) | IPV4_HDR_LEN;
            buf[1] = 0;

            let ipv4_payload_len: u16 = f(&mut buf[20..]).try_into().expect("ipv4_payload_len overflowed");

            let total_len = ipv4_payload_len + 20;

            buf[2..4].copy_from_slice(&total_len.to_be_bytes());

            buf[4..8].copy_from_slice(&[0; 4]);

            buf[8] = 64;

            buf[9] = 17;

            buf[12..16].copy_from_slice(&self.endpoint.0);
            buf[16..20].copy_from_slice(&next_hop_ip.0);

            
            total_len.into()
        })
    }
}
