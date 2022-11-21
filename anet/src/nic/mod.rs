use alloc::collections::VecDeque;

use crate::{util::RawPacket, RpcResult};

mod dummy;

pub use dummy::DummyNic;

// TODO: Add RRef versions of submit and poll.
pub trait Net {
    fn submit(&self, buf: RawPacket) -> RpcResult<(bool, RawPacket)>;

    fn submit_batch(
        &self,
        bufs: &mut VecDeque<RawPacket>,
        return_bufs: &mut VecDeque<RawPacket>,
    ) -> RpcResult<usize>;

    fn poll(&self, buf: RawPacket) -> RpcResult<(bool, RawPacket)>;

    fn poll_batch(
        &self,
        bufs: &mut VecDeque<RawPacket>,
        recvd_bufs: &mut VecDeque<RawPacket>,
    ) -> RpcResult<usize>;
}
