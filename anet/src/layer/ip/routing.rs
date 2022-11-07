use alloc::boxed::Box;

use crate::util::Ipv4Address;

pub struct RoutingTable {
    trie: Trie,
}

#[derive(Debug, PartialEq, Eq)]
pub enum RoutingResult {
    Reachable(Ipv4Address),
    Unreachable,
}

impl RoutingTable {
    pub fn new() -> Self {
        Self { trie: Trie::new() }
    }

    pub fn resolve(&self, dest: Ipv4Address) -> RoutingResult {
        if let Some(next_ip) = self.trie.get(u32::from_be_bytes(dest.0)) {
            RoutingResult::Reachable(next_ip)
        } else {
            RoutingResult::Unreachable
        }
    }

    pub fn insert_rule(&mut self, cidr: Ipv4Address, mask: u8, next: Ipv4Address) {
        if mask > 32 {
            panic!("invalid subnet mask");
        }
        
        let key = u32::from_be_bytes(cidr.0);

        self.trie.insert(key, next, mask);
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

    pub fn insert(&mut self, key: u32, value: Ipv4Address, bits: u8) {
        self.root.insert(key, value, bits, 0)
    }

    pub fn get(&self, key: u32) -> Option<Ipv4Address> {
        self.root.get(key, 0)
    }
}

struct TrieNode {
    value: Option<Ipv4Address>,
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
    pub fn insert(&mut self, key: u32, value: Ipv4Address, bits: u8, pos: u8) {
        if pos + 1 >= bits {
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

    pub fn get(&self, key: u32, pos: u8) -> Option<Ipv4Address> {
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
    use crate::util::Ipv4Address; 

    use super::{RoutingTable, RoutingResult};

    #[test]
    pub fn test_routing_table() {
    let mut table = RoutingTable::new();

    let a = u32::from_be_bytes([192, 168, 64, 1]);
    
    table.insert_rule(Ipv4Address::new([192, 168, 65, 1]), 24, Ipv4Address::new([192, 168, 65, 1])); // some other router 
    table.insert_rule(Ipv4Address::new([0, 0, 0, 0]), 0, Ipv4Address::new([192, 168, 64, 1])); // gateway from router
    table.insert_rule(Ipv4Address::new([172, 17, 24, 1]), 24, Ipv4Address::new([172, 17, 24, 1])); // another interface probably

    assert_eq!(
        table.resolve(Ipv4Address::new([8, 8, 8, 8])),
        RoutingResult::Reachable(Ipv4Address::new([192, 168, 64, 1]))
    );

    assert_eq!(
        table.resolve(Ipv4Address::new([192, 168, 65, 1])),
        RoutingResult::Reachable(Ipv4Address::new([192, 168, 65, 1]))
    );

    assert_eq!(
        table.resolve(Ipv4Address::new([172, 17, 24, 31])),
        RoutingResult::Reachable(Ipv4Address::new([172, 17, 24, 1]))
    );

    assert_eq!(
        table.resolve(Ipv4Address::new([172, 17, 45, 31])), // 25 instead of 24
        RoutingResult::Reachable(Ipv4Address::new([192, 168, 64, 1])) // should use the gateway
    );
    }
}
