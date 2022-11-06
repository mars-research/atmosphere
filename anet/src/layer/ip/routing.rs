use bitfield::Bit;

use crate::util::Ipv4Address;

pub struct RoutingTable {
    trie: Trie,
}

impl RoutingTable {
    pub fn new() -> Self {
        Self { trie: Trie::new() }
    }

    pub fn resolve(&self, dest: Ipv4Address) -> Ipv4Address {
        Ipv4Address::new([192, 168, 64, 1])
    }
}

struct Trie {
    root: TrieNode,
}

impl Trie {
    fn new() -> Self {
        Self { root: TrieNode {} }
    }
}

struct TrieNode {}
