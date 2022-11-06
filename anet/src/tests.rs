#![cfg(test)]

use crate::{socket::SocketAddr, stack::UdpStack};

#[test]
pub fn test_socket() {
    let mut stack = UdpStack::new();

    let mut socket = stack.socket();

    let addr = SocketAddr::new([0, 0, 0, 0], 8000);

    socket.bind(addr);
}
