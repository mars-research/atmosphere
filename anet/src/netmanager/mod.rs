use crate::util::RawPacket;

pub struct NetManager {}
// TCP hashmap and udp dispatch
impl NetManager {
    pub fn get_packet_buf(&self) -> Option<RawPacket> {
        // TODO: pop available packet from vacant bufs.
        return Some(RawPacket::default());
    }
}
