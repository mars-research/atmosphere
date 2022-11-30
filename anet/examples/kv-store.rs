/// Example UDP Server running on an Anet UDP stack
/// To test: Run `sudo ./setup-tap.sh` and then run the example server using `cargo r
/// --example=echo-server-stack`
/// In another terminal, send requests to the server using `nc 10.0.0.2 3000`
/// Syntax:
///  - ins:key:value
///  - get:key
///  - del:key
///
use std::{collections::VecDeque, str::FromStr, sync::Arc};

use anet::{
    arp::ArpTable,
    layer::ip::routing::{RoutingEntry, RoutingTable},
    netmanager::NetManager,
    nic::TapDevice,
    packet::{RawPacket, UdpPacketRepr},
    stack::udp::UdpStack,
    util::{Ipv4Address, MacAddress, SocketAddress},
};
use hashbrown::HashMap;
use pnet::packet::ipv4::checksum;

const TAP_MAC: &'static str = "02:aa:aa:aa:aa:aa";
const ANET_MAC: &'static str = "02:bb:bb:bb:bb:bb";

pub type Store = HashMap<String, String>;

// pretend that the NIC is globally initialized by the OS
lazy_static::lazy_static! {
    static ref TAP: Arc<TapDevice> = Arc::new(TapDevice::new("tap1"));
}

fn create_udp_stack() -> UdpStack<TapDevice> {
    let nic = TAP.clone();
    let arp_table = Arc::new(ArpTable::new());
    arp_table.add_static_entry(
        Ipv4Address::from_str("10.0.0.1").unwrap(),
        MacAddress::from_str(TAP_MAC).unwrap(),
    );

    let mut routing_table = RoutingTable::new();
    routing_table.set_default_gateway(Ipv4Address::new(10, 0, 0, 1));
    routing_table.insert_rule(
        Ipv4Address::new(10, 0, 0, 1),
        24,
        RoutingEntry::DirectlyConnected,
    );

    let netman = Arc::new(NetManager {});

    let endpoint = SocketAddress::new(Ipv4Address::new(10, 0, 0, 2), 3000);

    UdpStack::new(
        endpoint,
        netman,
        nic,
        MacAddress::from_str(ANET_MAC).unwrap(),
        routing_table,
        arp_table,
    )
}
pub fn main() {
    let stack = create_udp_stack();
    let mut store = Store::new();

    let mut free_bufs = VecDeque::from(vec![RawPacket::default(); 32]);
    let mut recvd_packets = VecDeque::new();
    let mut send_batch = VecDeque::new();

    loop {
        let n_packets = stack
            .recv_batch(&mut free_bufs, &mut recvd_packets)
            .expect("failed to receive packets");

        println!("received {n_packets} packets");
        if n_packets > 0 {
            recvd_packets.drain(..n_packets).for_each(|mut pkt| {
                println!("payload: {}", String::from_utf8_lossy(pkt.udp_payload()));
                process_pkt(&mut pkt, &mut store);
                send_batch.push_back(pkt);
            });
            stack
                .send_batch(&mut send_batch, &mut free_bufs)
                .expect("failed to send packets");
        }
    }
}

pub fn process_pkt(pkt: &mut UdpPacketRepr, store: &mut Store) {
    let resp = if let Ok(req_str) = std::str::from_utf8(pkt.udp_payload()) {
        if let Ok(req) = Request::from_str(req_str) {
            req.process(store)
        } else {
            Response::InvalidCommand
        }
    } else {
        Response::InvalidCommand
    };
    let resp = resp.to_string();
    println!("resp: {resp}");
    let resp_bytes = resp.as_bytes();
    println!("resp_bytes: {}", resp_bytes.len());
    pkt.set_udp_payload(|payload| {
        payload[..resp_bytes.len()].copy_from_slice(resp_bytes);
        resp_bytes.len()
    });

    pkt.set_udp_packet(|mut udp| {
        let src = udp.get_source();
        let dst = udp.get_destination();
        udp.set_destination(src);
        udp.set_source(dst);
        udp.set_checksum(0);
    });

    let ip_total_len = pkt.udp_packet().get_length() + 20;

    pkt.set_ip_packet(|mut ip| {
        let src = ip.get_source();
        let dst = ip.get_destination();
        ip.set_destination(src);
        ip.set_source(dst);
        ip.set_total_length(ip_total_len);
        ip.set_checksum(0);
        let ck = checksum(&ip.to_immutable());
        ip.set_checksum(ck);
    });

    pkt.set_eth_packet(|mut eth| {
        let src = eth.get_source();
        let dst = eth.get_destination();
        eth.set_destination(src);
        eth.set_source(dst);
    })
}

enum Request {
    Ins(String, String),
    Get(String),
    Del(String),
}

impl Request {
    pub fn process(&self, store: &mut Store) -> Response {
        match self {
            Request::Ins(k, v) => {
                store.insert(k.to_string(), v.to_string());

                Response::Inserted
            }
            Request::Get(k) => match store.get(k) {
                Some(v) => Response::Found(v.to_string()),
                None => Response::NotFound,
            },
            Request::Del(k) => match store.remove(k) {
                Some(_) => Response::Deleted,
                None => Response::NotFound,
            },
        }
    }
}

impl FromStr for Request {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut req = s.trim().split(":");
        if let Some(cmd) = req.next() {
            match cmd {
                "ins" => {
                    if let (Some(key), Some(value)) = (req.next(), req.next()) {
                        Ok(Request::Ins(key.to_owned(), value.to_owned()))
                    } else {
                        Err("invalid command")
                    }
                }
                "get" => {
                    if let Some(key) = req.next() {
                        Ok(Request::Get(key.to_owned()))
                    } else {
                        Err("invalid command")
                    }
                }
                "del" => {
                    if let Some(key) = req.next() {
                        Ok(Request::Del(key.to_owned()))
                    } else {
                        Err("invalid command")
                    }
                }
                _ => Err("invalid command"),
            }
        } else {
            Err("invalid command")
        }
    }
}

enum Response {
    Inserted,
    Deleted,
    Found(String),
    NotFound,
    InvalidCommand,
}

impl ToString for Response {
    fn to_string(&self) -> String {
        match self {
            Response::Inserted => "inserted\n".to_string(),
            Response::Found(value) => format!("found: {}\n", value),
            Response::NotFound => "not found\n".to_string(),
            Response::InvalidCommand => "invalid command\n".to_string(),
            Response::Deleted => "deleted\n".to_string(),
        }
    }
}
