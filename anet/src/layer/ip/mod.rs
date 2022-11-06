use alloc::sync::Arc;

use crate::{arp::ArpTable, address::Ipv4Address};

use self::routing::RoutingTable;

use super::eth::EthernetLayer;

mod routing;

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
        let dmac = self.arp_table.resolve(next_hop_ip);

        self.lower.send_packet(dmac, super::eth::EtherType::Ipv4, |buf: &mut [u8]| {
            // write ipv4 header here
            buf[0..20].copy_from_slice(&[0; 20]);

            let ipv4_payload_len = f(&mut buf[20..]);
            
            20 + ipv4_payload_len
        });
        
        Ok(0)
    }
}
