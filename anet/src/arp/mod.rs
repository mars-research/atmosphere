use hashbrown::{HashMap, HashSet};

use crate::address::{Ipv4Address, MacAddress};

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

    pub fn resolve(&self, ip_addr: Ipv4Address) -> MacAddress {
        todo!()
    }
}
