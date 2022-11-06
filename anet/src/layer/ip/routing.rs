use crate::address::Ipv4Address;

pub struct RoutingTable {}

impl RoutingTable {
    pub fn new() -> Self {
        Self {}
    }

    pub fn resolve(&self, dest: Ipv4Address) -> Ipv4Address {
        todo!()
    }
}
