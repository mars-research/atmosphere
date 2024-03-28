pub mod syscall_new_proc;
pub mod syscall_new_proc_with_iommu;
// pub mod syscall_new_proc_pass_mem;
pub mod syscall_new_proc_with_iommu_pass_mem;

pub use syscall_new_proc::*;
pub use syscall_new_proc_with_iommu::*;
// pub use syscall_new_proc_pass_mem::*;
pub use syscall_new_proc_with_iommu_pass_mem::*;