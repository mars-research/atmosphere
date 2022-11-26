use hashbrown::{HashMap, HashSet};

use pnet::util::core_net::Ipv4Addr;
use pnet::util::MacAddr;

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
    cache: HashMap<Ipv4Addr, MacAddr>,
    inflight: HashSet<Ipv4Addr>,
}

impl ArpTable {
    pub fn new() -> Self {
        Self {
            cache: HashMap::new(),
            inflight: HashSet::new(),
        }
    }

    pub fn resolve(&self, ip_addr: &Ipv4Addr) -> MacAddr {
        // TODO: Actual resolving
        MacAddr(0xf6, 0xd4, 0x88, 0xc7, 0xe5, 0x64)
    }
}
