pub type Port = u16;

pub struct MacAddress(pub [u8; 6]);

impl MacAddress {
    pub fn new(octets: [u8; 6]) -> Self {
        Self(octets)
    }
}

pub struct Ipv4Address(pub [u8; 4]);

impl Ipv4Address {
    pub fn new(octets: [u8; 4]) -> Self {
        Self(octets)
    }
}

pub struct SocketAddress {
    pub ip: Ipv4Address,
    pub port: Port,
}

impl SocketAddress {
    pub fn new(ip: Ipv4Address, port: Port) -> Self { Self { ip, port } }
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
