// src/nic_buffers.rs

use core::ops::Deref;
use alloc::vec::Vec;

pub struct TransmitBuffer {
        data: Vec<u8>
}

impl TransmitBuffer {
        pub fn new(self, data: Vec<u8>) -> Self {
                TransmitBuffer { data }
        }
        pub fn phys_addr(&self) -> usize { 0 }
}

impl Deref for TransmitBuffer {
        type Target = [u8];

        fn deref(&self) -> &Self::Target {
                &self.data
        }
}

pub struct ReceiveBuffer;
