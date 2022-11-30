use std::str::FromStr;

use hashbrown::{HashMap, HashSet};

use pnet::util::core_net::Ipv4Addr;
use pnet::util::MacAddr;
use spin::RwLock;

const ETHERNET_HRD_LEN: u8 = 6;
const IPV4_PROTO_LEN: u8 = 4;

pub enum HardwareType {
    Ethernet = 1,
}

pub enum ProtocolType {
    Ipv4 = 0x800,
}

struct ArpRequest {
    hardware_type: HardwareType,
    protocol_type: ProtocolType,
}

pub struct ArpTable {
    cache: RwLock<HashMap<Ipv4Addr, MacAddr>>,
    inflight: RwLock<HashSet<Ipv4Addr>>,
}

impl ArpTable {
    pub fn new() -> Self {
        Self {
            cache: RwLock::new(HashMap::new()),
            inflight: RwLock::new(HashSet::new()),
        }
    }

    pub fn resolve(&self, ip_addr: &Ipv4Addr) -> MacAddr {
        if let Some(mac_addr) = self.cache.read().get(ip_addr) {
            *mac_addr
        } else {
            todo!()
        }
    }

    pub fn add_static_entry(&self, ip_addr: Ipv4Addr, mac_addr: MacAddr) {
        let mut cache = self.cache.write();
        cache.insert(ip_addr, mac_addr);
    }
}
