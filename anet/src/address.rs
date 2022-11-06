pub type Port = u16;

pub struct MacAddress(pub [u8; 6]);

impl MacAddress {
    pub fn new(octets: [u8; 6]) -> Self {
        Self(octets)
    }
}

pub struct Ipv4Address([u8; 4]);

impl Ipv4Address {
    pub fn new(octets: [u8; 4]) -> Self {
        Self(octets)
    }
}

pub struct SocketAddress {
    pub ip: Ipv4Address,
    pub port: Port,
}
