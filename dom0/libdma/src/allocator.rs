use super::Dma;
use core::marker::Sized;
use core::result::Result;

pub trait DmaAllocator
where
    Self: Sized,
{
    fn allocate() -> Result<Dma<Self>, i32>;
}

#[macro_export]
macro_rules! zeroed_allocator {
    ($t: ty) => {
        impl DmaAllocator for $t {
            fn allocate() -> Result<Dma<Self>, i32> {
                unsafe { Dma::zeroed() }
            }
        }
    };
}
