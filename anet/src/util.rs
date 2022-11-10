pub type Port = u16;

#[derive(Default, Clone, Copy)]
pub struct MacAddress(pub [u8; 6]);

impl MacAddress {
    pub fn new(octets: [u8; 6]) -> Self {
        Self(octets)
    }
    
    pub fn broadcast() -> Self {
        Self([0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])
    }

    pub fn from_slice(slice: &[u8]) -> Self {
        let mut octets = [0; 6];

        octets.copy_from_slice(slice);

        Self(octets)
    }
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ipv4Address(pub [u8; 4]);

impl Ipv4Address {
    pub fn new(octets: [u8; 4]) -> Self {
        Self(octets)
    }

    pub fn from_slice(slice: &[u8]) -> Self {
        let mut octets = [0; 4];
        octets.copy_from_slice(slice);
        Self(octets)
    }
}

impl From<Ipv4Address> for u32 {
    fn from(value: Ipv4Address) -> Self {
        u32::from_be_bytes(value.0)
    }
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct SocketAddress {
    pub ip: Ipv4Address,
    pub port: Port,
}

impl SocketAddress {
    pub fn new(ip: Ipv4Address, port: u16) -> Self {
        Self { ip, port }
    }
}

#[cfg(not(test))]
#[derive(Clone)]
pub struct RawPacket(pub [u8; 1518]);

impl Default for RawPacket {
    fn default() -> Self {
        RawPacket([0; 1518])
    }
}

#[cfg(test)]
#[derive(Clone, Debug)]
pub struct RawPacket(pub [u8; 1518]);
