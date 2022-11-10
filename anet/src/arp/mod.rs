use hashbrown::{HashMap, HashSet};

use crate::util::{Ipv4Address, MacAddress};

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
    cache: HashMap<Ipv4Address, MacAddress>,
    inflight: HashSet<Ipv4Address>,
}

impl ArpTable {
    pub fn new() -> Self {
        Self {
            cache: HashMap::new(),
            inflight: HashSet::new(),
        }
    }

    pub fn resolve(&self, ip_addr: &Ipv4Address) -> MacAddress {
        // TODO: Actual resolving
        MacAddress([0xf6, 0xd4, 0x88, 0xc7, 0xe5, 0x64])
    }
}
