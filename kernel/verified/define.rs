use vstd::prelude::*;
verus! {
use vstd::ptr::*;
use crate::trap::Registers;

#[derive(Debug)]
pub struct SyscallReturnStruct{
    pub error_code: ErrorCodeType,
    pub pcid: Pcid,
    pub cr3: usize,
    pub thread_ptr:ThreadPtr ,
}

impl SyscallReturnStruct{

    pub fn new(error_code:ErrorCodeType,pcid:Pcid,cr3:usize,thread_ptr:ThreadPtr )->(ret:Self)
        ensures
            ret.error_code == error_code,
            ret.pcid == pcid,
            ret.cr3 == cr3,
            ret.thread_ptr == thread_ptr,
    {
        return Self{
            error_code:error_code,
            pcid:pcid,
            cr3:cr3,
            thread_ptr:thread_ptr,
        };
    }
}

pub type ErrorCodeType = usize;

// NO_ERROR_CODE is used for timer interrupt or an ipc syscall when the current thread gives up the cpu and
// scheduler picks a next thread to run. We do not need to return a syscall error code for a thread coming
// from the scheduler.
// However, if the thread was sent to the scheduler due to its previous syscall, most likely from endpoint related ones,
// we do need to return an error code that is stored in the thread struct.
pub const NO_ERROR_CODE:ErrorCodeType = 233;
// The TCB needs to spin at the kernel entry until the next thread is available.
pub const NO_NEXT_THREAD:ErrorCodeType = 234;

pub const SUCCESS: ErrorCodeType = 0;
pub const SENDER_ENDPOINT_NOT_EXIST: ErrorCodeType = 1;
pub const RECEIVER_ENDPOINT_EXIST: ErrorCodeType = 2;
pub const RECEIVER_ENDPOINT_USED: ErrorCodeType = 3;
pub const SENDER_ENDPOINT_OUT_OF_BOUND: ErrorCodeType = 4;
pub const NO_RECEIVER:ErrorCodeType = 5;
pub const SCHEDULER_NO_SPACE:ErrorCodeType = 6;
pub const SHARED_ENDPOINT_NOT_EXIST:ErrorCodeType = 7;
pub const SHARED_ENDPOINT_REF_COUNT_OVERFLOW:ErrorCodeType = 8;
pub const SHARED_ENDPOINT_SLOT_TAKEN:ErrorCodeType = 9;
pub const NO_RUNNING_THREAD:ErrorCodeType = 10;
pub const CPU_ID_INVALID:ErrorCodeType = 11;
pub const ENDPOINT_INDEX_INVALID:ErrorCodeType = 12;
pub const SYSTEM_OUT_OF_MEM:ErrorCodeType = 13;
pub const PROCESS_LIST_NO_SPEC:ErrorCodeType = 14;
pub const NO_FREE_PCID:ErrorCodeType = 15;
pub const PROC_THREAD_LIST_FULL:ErrorCodeType = 16;
pub const NO_FREE_IOID:ErrorCodeType = 17;
pub const VMEM_PERMBITS_INVALID:ErrorCodeType = 18;
pub const MMAP_VADDR_INVALID:ErrorCodeType = 19;
pub const MMAP_VADDR_NOT_FREE:ErrorCodeType = 20;
pub const PROC_NO_IOMMUTABLE:ErrorCodeType = 21;
pub const PAGE_RF_COUNTER_OVERFLOW:ErrorCodeType = 22;
pub const SCHEDULER_EMPTY:ErrorCodeType = 23;
pub const CPU_NO_IDLE:ErrorCodeType = 24;
pub const ENDPOINT_SLOT_TAKEN:ErrorCodeType = 25;
pub const ENDPOINT_FULL:ErrorCodeType = 26;
pub const MESSAGE_INVALID:ErrorCodeType = 27;
pub const PAGE_PAYLOAD_INVALID:ErrorCodeType = 28;
pub const CALL_FAILED:ErrorCodeType = 29;
pub const NO_CALLER:ErrorCodeType = 30;
pub const ENDPOINT_PAYLOAD_INVALID:ErrorCodeType = 31;
pub const PCI_DEV_PAYLOAD_INVALID:ErrorCodeType = 32;
pub const VADDR_INVALID:ErrorCodeType = 33;
pub const VADDR_NOMAPPING:ErrorCodeType = 34;
pub const ENDPOINT_SENDER_QUEUE:ErrorCodeType = 35;
pub const IPC_TYPE_NOT_MATCH:ErrorCodeType = 36;
pub const PCI_DEV_NUM_INVALID:ErrorCodeType = 37;
pub const PCI_DEV_NO_OWNERSHIP:ErrorCodeType = 38;
pub const PCI_DEV_TAKEN:ErrorCodeType = 39;
pub const NEW_THREAD:ErrorCodeType = 40;

pub type ThreadState = usize;
pub const SCHEDULED:ThreadState = 1;
pub const BLOCKED:ThreadState = 2;
pub const RUNNING:ThreadState = 3;
pub const CALLING:ThreadState = 4;
pub const TRANSIT:ThreadState = 5;

pub type EndpointState = bool;
pub const RECEIVE:EndpointState = true;
pub const SEND:EndpointState = false;

pub type ThreadPtr = usize;
pub type ProcPtr = usize;
pub type EndpointIdx = usize;
pub type EndpointPtr = usize;

pub const MAX_NUM_ENDPOINT_DESCRIPTORS:usize = 128;
pub const MAX_NUM_THREADS_PER_PROC:usize = 250;
pub const MAX_NUM_THREADS_PER_ENDPOINT:usize = 250;
pub const MAX_NUM_PROCS:usize = PCID_MAX;
pub const MAX_NUM_THREADS:usize = 500 * 4096;
pub const IPC_MESSAGE_LEN:usize = 1024;
pub const IPC_PAGEPAYLOAD_LEN:usize = 128;

pub const KERNEL_MEM_END_L4INDEX:usize = 1; //1 for now
// pub const NUM_PAGES:usize = 2*1024*1024; //8GB
pub const NUM_PAGES:usize = 64*1024; //256MiB
pub const PAGE_SZ:usize = 4096;
pub const MAX_USIZE:u64 = 31*1024*1024*1024;


pub type PageType = u8;
pub const R:PageType = 1;
pub const RW:PageType = 2;
pub const RX:PageType = 3;
pub const RWX:PageType = 4;

pub type PageState = u8;

pub const UNAVAILABLE:PageState = 0;
pub const FREE:PageState = 1;
pub const PAGETABLE:PageState = 2;
pub const ALLOCATED:PageState = 3;
pub const MAPPED:PageState = 4;
pub const IO:PageState = 5;

pub type PageTablePtr = usize;
pub const PCID_MAX:usize = 4096;
pub const IOID_MAX:usize = 4096;

pub type PagePPtr = PPtr<[u8; PAGE_SZ]>;
pub type PagePtr = usize;
pub type PagePerm = PointsTo<[u8; PAGE_SZ]>;

pub type VAddr = usize;
pub type PAddr = usize;

pub type Pcid = usize;
pub type IOid = usize;

pub type L4Index = usize;
pub type L3Index = usize;
pub type L2Index = usize;
pub type L1Index = usize;

pub const VA_MASK:u64 = 0x0000_ffff_ffff_f000;
pub const VA_PERM_MASK:u64 = 0x8000_0000_0000_0002;
pub const READ:usize = 0x8000_0000_0000_0000u64 as usize;
pub const READ_WRITE:usize = 0x8000_0000_0000_0002u64 as usize;
pub const READ_EXECUTE:usize = 0x0000_0000_0000_0000u64 as usize;
pub const READ_WRITE_EXECUTE:usize = 0x0000_0000_0000_0002u64 as usize;
pub const PCID_ENABLE_MASK:usize = 0x8000_0000_0000_0000u64 as usize;

pub const NUM_CPUS:usize = 32;
pub const PAGE_ENTRY_PRESENT_MASK:u64 = 0x5; //Hack, force the verified pagetable to map everything as user.
}
