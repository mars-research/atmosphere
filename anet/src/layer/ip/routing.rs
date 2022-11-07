use alloc::boxed::Box;

use crate::util::Ipv4Address;

pub struct RoutingTable {
    trie: Trie,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum RoutingEntry {
    DirectlyConnected,
    Gateway(Ipv4Address),
}

#[derive(Debug, PartialEq, Eq)]
pub enum RoutingResult {
    Reachable(RoutingEntry),
    Unreachable,
}

impl RoutingTable {
    pub fn new() -> Self {
        Self { trie: Trie::new() }
    }

    pub fn resolve(&self, dest: Ipv4Address) -> RoutingResult {
        if let Some(entry) = self.trie.get(dest.into()) {
            RoutingResult::Reachable(entry)
        } else {
            RoutingResult::Unreachable
        }
    }

    pub fn insert_rule(&mut self, cidr: Ipv4Address, mask: u8, value: RoutingEntry) {
        if mask > 32 {
            panic!("invalid subnet mask");
        }
        
        let key = cidr.into();

        self.trie.insert(key, value, mask);
    }

    pub fn set_default_gateway(&mut self, gateway: Ipv4Address) {
        let key = 0; // match 0.0.0.0/0

        self.trie.insert(key, RoutingEntry::Gateway(gateway), 0);
    }
}

struct Trie {
    root: Box<TrieNode>,
}

impl Trie {
    pub fn new() -> Self {
        Self {
            root: TrieNode::new(),
        }
    }

    pub fn insert(&mut self, key: u32, value: RoutingEntry, bits: u8) {
        self.root.insert(key, value, bits, 0)
    }

    pub fn get(&self, key: u32) -> Option<RoutingEntry> {
        self.root.get(key, 0)
    }
}

struct TrieNode {
    value: Option<RoutingEntry>,
    left: Option<Box<TrieNode>>,
    right: Option<Box<TrieNode>>,
}

impl TrieNode {
    pub fn new() -> Box<Self> {
        Box::new(Self {
            left: None,
            right: None,
            value: None,
        })
    }
    pub fn insert(&mut self, key: u32, value: RoutingEntry, bits: u8, pos: u8) {
        if pos == bits {
            self.value = Some(value);
            return;
        }
        let bit = (key >> (31 - pos)) & 1;

        if bit == 1 {
            if self.right.is_none() {
                self.right = Some(TrieNode::new());
            }
            self.right.as_mut().unwrap().insert(key, value, bits, pos + 1);
        } else {
            if self.left.is_none() {
                self.left = Some(TrieNode::new());
            }
            self.left.as_mut().unwrap().insert(key, value, bits, pos + 1);
        }
    }

    pub fn get(&self, key: u32, pos: u8) -> Option<RoutingEntry> {
        if pos > 31 {
            panic!("pos can't be greater than 32");
        }

        let bit = (key >> (31 - pos)) & 1;

        let mut value = None;

        if bit == 1 {
            if self.right.is_some() {
                value = self.right.as_ref().unwrap().get(key, pos + 1);
            }
        } else {
            if self.left.is_some() {
                value = self.left.as_ref().unwrap().get(key, pos + 1);
            }
        }

        if value.is_some() {
            value
        } else {
            self.value
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{util::Ipv4Address, layer::ip::routing::RoutingEntry}; 

    use super::{RoutingTable, RoutingResult};

    #[test]
    pub fn test_routing_table() {
        let mut table = RoutingTable::new();
        
        // default gateway
        table.set_default_gateway(Ipv4Address([192, 168, 64, 1]));
        // directly connected hosts in a LAN
        table.insert_rule(Ipv4Address::new([192, 168, 64, 1]), 24, RoutingEntry::DirectlyConnected); 

        // another router for another LAN (test overlapping prefixes)
        table.insert_rule(Ipv4Address::new([192, 168, 65, 1]), 24, RoutingEntry::Gateway(Ipv4Address::new([192, 168, 65, 1])));
        // a VM running on the host
        table.insert_rule(Ipv4Address::new([10, 0, 0, 1]), 24, RoutingEntry::Gateway(Ipv4Address::new([192, 168, 64, 10])));

        // via default gateway
        assert_eq!(
            table.resolve(Ipv4Address::new([8, 8, 8, 8])),
            RoutingResult::Reachable(RoutingEntry::Gateway(Ipv4Address::new([192, 168, 64, 1])))
        );

        // directly connected to host
        assert_eq!(
            table.resolve(Ipv4Address::new([192, 168, 64, 9])),
            RoutingResult::Reachable(RoutingEntry::DirectlyConnected)
        );

        // via another gateway
        assert_eq!(
            table.resolve(Ipv4Address::new([10, 0, 0, 8])),
            RoutingResult::Reachable(RoutingEntry::Gateway(Ipv4Address::new([192, 168, 64, 10])))
        );

        assert_eq!(
            table.resolve(Ipv4Address::new([192, 168, 65, 30])),
            RoutingResult::Reachable(RoutingEntry::Gateway(Ipv4Address::new([192, 168, 65, 1])))
        );
    }
}
