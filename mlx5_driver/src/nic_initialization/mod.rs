use crate::device::RX_BUFFER_POOL;

pub fn init_rx_buf_pool(_num_descs: usize, _mtu: u16, _pool: &RX_BUFFER_POOL) -> Result<(), &'static str> {
    Ok(())
}
