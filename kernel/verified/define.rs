use vstd::prelude::*;

verus! {

use vstd::simple_pptr::*;

// use crate::trap::Registers;
// -------------------- Begin of Types --------------------
pub type ThreadPtr = usize;

pub type ProcPtr = usize;

pub type EndpointIdx = usize;

pub type EndpointPtr = usize;

pub type ContainerPtr = usize;

pub type CpuId = usize;

pub type PagePtr = usize;

pub type PagePerm4k = PointsTo<[u8; PAGE_SZ_4k]>;

pub type PagePerm2m = PointsTo<[u8; PAGE_SZ_2m]>;

pub type PagePerm1g = PointsTo<[u8; PAGE_SZ_1g]>;

pub type VAddr = usize;

pub type PAddr = usize;

pub type PageMapPtr = usize;

// pub type PageEntryPerm = usize;
pub type Pcid = usize;

pub type IOid = usize;

pub type L4Index = usize;

pub type L3Index = usize;

pub type L2Index = usize;

pub type L1Index = usize;

pub type SLLIndex = i32;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ThreadState {
    SCHEDULED,
    BLOCKED,
    RUNNING,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum EndpointState {
    RECEIVE,
    SEND,
}

impl EndpointState {
    pub fn is_send(&self) -> (ret: bool)
        ensures
            ret == (self == EndpointState::SEND),
    {
        match self {
            EndpointState::SEND => true,
            _ => false,
        }
    }

    pub fn is_receive(&self) -> (ret: bool)
        ensures
            ret == (self == EndpointState::RECEIVE),
    {
        match self {
            EndpointState::RECEIVE => true,
            _ => false,
        }
    }
    // pub open spec fn is_receive_spec(&self) -> bool {
    //     self matches EndpointState { foo } &&  foo == EndpointState::SEND
    // }

}

#[derive(Clone, Copy, Debug)]
pub enum PageType {
    R,
    RW,
    RX,
    RWX,
}

#[allow(inconsistent_fields)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum PageState {
    Unavailable4k,
    Unavailable2m,
    Unavailable1g,
    Pagetable,
    Allocated4k,
    Allocated2m,
    Allocated1g,
    Free4k,
    Free2m,
    Free1g,
    Mapped4k,
    Mapped2m,
    Mapped1g,
    Merged2m,
    Merged1g,
    Io,
}

#[derive(Clone, Copy, Debug)]
pub enum PageSize {
    SZ4k,
    SZ2m,
    SZ1g,
}

#[derive(Clone, Copy, Debug)]
pub enum PageTableErrorCode {
    NoError,
    L4EntryNotExist,
    L3EntryNotExist,
    L2EntryNotExist,
    L1EntryNotExist,
    EntryTakenBy4k,
    EntryTakenBy2m,
    EntryTakenBy1g,
}

#[derive(Clone, Copy)]
#[allow(inconsistent_fields)]
pub enum UserRetValueType {
    Success,
    ErrorNoQuota,
    ErrorVaInUse,
    Else,
}

impl UserRetValueType {
    pub open spec fn spec_is_error(&self) -> bool {
        match self {
            Self::Success => { false },
            Self::ErrorNoQuota => { true },
            Self::ErrorVaInUse => { true },
            Self::Else => { true },
        }
    }

    #[verifier(when_used_as_spec(spec_is_error))]
    pub fn is_error(&self) -> bool {
        match self {
            Self::Success => { false },
            Self::ErrorNoQuota => { true },
            Self::ErrorVaInUse => { true },
            Self::Else => { true },
        }
    }
}

#[derive(Clone, Copy)]
#[allow(inconsistent_fields)]
pub enum RetValueType {
    SuccessUsize { value: usize },
    SuccessSeqUsize { value: Ghost<Seq<usize>> },
    SuccessPairUsize { value1: usize, value2: usize },
    SuccessThreeUsize { value1: usize, value2: usize, value3: usize },
    ErrorNoQuota,
    ErrorVaInUse,
    CpuIdle,
    Error,
    Else,
    NoQuota,
    VaInUse,
}

// -------------------- End of Types --------------------
// -------------------- Begin of Const --------------------
pub const MAX_NUM_ENDPOINT_DESCRIPTORS: usize = 128;

pub const MAX_NUM_THREADS_PER_PROC: usize = 128;

pub const MAX_NUM_THREADS_PER_ENDPOINT: usize = 128;

pub const MAX_NUM_PROCS: usize = PCID_MAX;

pub const MAX_NUM_THREADS: usize = 500 * 4096;

pub const IPC_MESSAGE_LEN: usize = 1024;

pub const IPC_PAGEPAYLOAD_LEN: usize = 128;

//1 for now
pub const KERNEL_MEM_END_L4INDEX: usize = 1;

//8GiB
pub const NUM_PAGES: usize = 2 * 1024 * 1024;

pub const PAGE_SZ_4k: usize = 1usize << 12;

pub const PAGE_SZ_2m: usize = 1usize << 21;

pub const PAGE_SZ_1g: usize = 1usize << 30;

pub const MAX_USIZE: u64 = 31 * 1024 * 1024 * 1024;

pub const PCID_MAX: usize = 4096;

pub const IOID_MAX: usize = 4096;

pub const MEM_MASK: u64 = 0x0000_ffff_ffff_f000;

pub const MEM_4k_MASK: u64 = 0x0000_ffff_ffff_f000;

pub const MEM_2m_MASK: u64 = 0x0000_ffff_ffe0_0000;

pub const MEM_1g_MASK: u64 = 0x0000_fffc_0000_0000;

pub const VA_PERM_MASK: u64 = 0x8000_0000_0000_0002;

pub const READ: usize = 0x8000_0000_0000_0000u64 as usize;

pub const READ_WRITE: usize = 0x8000_0000_0000_0002u64 as usize;

pub const READ_EXECUTE: usize = 0x0000_0000_0000_0000u64 as usize;

pub const READ_WRITE_EXECUTE: usize = 0x0000_0000_0000_0002u64 as usize;

pub const PCID_ENABLE_MASK: usize = 0x8000_0000_0000_0000u64 as usize;

pub const NUM_CPUS: usize = 32;

pub const PAGE_ENTRY_PRESENT_SHIFT: u64 = 0;

pub const PAGE_ENTRY_WRITE_SHIFT: u64 = 1;

pub const PAGE_ENTRY_USER_SHIFT: u64 = 2;

pub const PAGE_ENTRY_PS_SHIFT: u64 = 7;

pub const PAGE_ENTRY_EXECUTE_SHIFT: u64 = 63;

pub const PAGE_ENTRY_PRESENT_MASK: u64 = 0x1;

pub const PAGE_ENTRY_WRITE_MASK: u64 = 0x1u64 << PAGE_ENTRY_WRITE_SHIFT;

pub const PAGE_ENTRY_USER_MASK: u64 = 0x1u64 << PAGE_ENTRY_USER_SHIFT;

pub const PAGE_ENTRY_PS_MASK: u64 = 0x1u64 << PAGE_ENTRY_PS_SHIFT;

pub const PAGE_ENTRY_EXECUTE_MASK: u64 = 0x1u64 << PAGE_ENTRY_EXECUTE_SHIFT;

pub const CONTAINER_PROC_LIST_LEN: usize = 10;

pub const CONTAINER_CHILD_LIST_LEN: usize = 10;

pub const PROC_CHILD_LIST_LEN: usize = 10;

pub const CONTAINER_ENDPOINT_LIST_LEN: usize = 10;

pub const MAX_CONTAINER_SCHEDULER_LEN: usize = 10;

// -------------------- End of Const --------------------
// -------------------- Begin of Structs --------------------
#[derive(Clone, Copy, Debug)]
pub enum DemandPagingMode {
    NoDMDPG,
    DirectParentPrc,
    AllParentProc,
    AllParentContainer,
}

#[derive(Clone, Copy, Debug)]
pub enum SwitchDecision {
    NoSwitch,
    NoThread,
    Switch,
}

#[derive(Clone, Copy)]
pub struct SyscallReturnStruct {
    pub error_code: RetValueType,
    pub pcid: Option<Pcid>,
    pub cr3: Option<usize>,
    pub switch_decision: SwitchDecision,
}

impl SyscallReturnStruct {
    pub open spec fn to_user_return_value(&self) -> UserRetValueType {
        match self.error_code {
            RetValueType::SuccessUsize { .. } => UserRetValueType::Success,
            RetValueType::SuccessSeqUsize { .. } => UserRetValueType::Success,
            RetValueType::SuccessPairUsize { .. } => UserRetValueType::Success,
            RetValueType::SuccessThreeUsize { .. } => UserRetValueType::Success,
            RetValueType::ErrorNoQuota => UserRetValueType::ErrorNoQuota,
            RetValueType::ErrorVaInUse => UserRetValueType::ErrorVaInUse,
            _ => UserRetValueType::Else,
        }
    }

    pub open spec fn get_return_vaule_usize(&self) -> Option<usize> {
        match self.error_code {
            RetValueType::SuccessUsize { value: value } => Some(value),
            _ => None,
        }
    }

    pub open spec fn get_return_vaule_seq_usize(&self) -> Option<Seq<usize>> {
        match self.error_code {
            RetValueType::SuccessSeqUsize { value: value } => Some(value@),
            _ => None,
        }
    }

    pub open spec fn get_return_vaule_pair_usize(&self) -> Option<(usize, usize)> {
        match self.error_code {
            RetValueType::SuccessPairUsize { value1: value1, value2: value2 } => Some(
                (value1, value2),
            ),
            _ => None,
        }
    }

    pub open spec fn get_return_vaule_three_usize(&self) -> Option<(usize, usize, usize)> {
        match self.error_code {
            RetValueType::SuccessThreeUsize {
                value1: value1,
                value2: value2,
                value3: value3,
            } => Some((value1, value2, value3)),
            _ => None,
        }
    }

    pub open spec fn spec_is_error(&self) -> bool {
        match self.error_code {
            RetValueType::Error => true,
            _ => false,
        }
    }

    #[verifier(when_used_as_spec(spec_is_error))]
    pub fn is_error(&self) -> (ret: bool)
        ensures
            ret == self.is_error(),
    {
        match self.error_code {
            RetValueType::Error => true,
            _ => false,
        }
    }

    pub fn NoSwitchNew(error_code: RetValueType) -> (ret: Self)
        ensures
            ret.error_code == error_code,
            ret.pcid.is_None(),
            ret.cr3.is_None(),
            ret.switch_decision == SwitchDecision::NoSwitch,
    {
        return Self {
            error_code: error_code,
            pcid: None,
            cr3: None,
            switch_decision: SwitchDecision::NoSwitch,
        };
    }

    pub fn NoNextThreadNew(error_code: RetValueType) -> (ret: Self)
        ensures
            ret.error_code == error_code,
            ret.pcid.is_None(),
            ret.cr3.is_None(),
            ret.switch_decision == SwitchDecision::NoThread,
    {
        return Self {
            error_code: error_code,
            pcid: None,
            cr3: None,
            switch_decision: SwitchDecision::NoThread,
        };
    }

    pub fn SwitchNew(error_code: RetValueType, cr3: usize, pcid: Pcid) -> (ret: Self)
        ensures
            ret.error_code == error_code,
            ret.pcid =~= Some(pcid),
            ret.cr3 =~= Some(cr3),
            ret.switch_decision == SwitchDecision::Switch,
    {
        return Self {
            error_code: error_code,
            pcid: Some(pcid),
            cr3: Some(cr3),
            switch_decision: SwitchDecision::Switch,
        };
    }
}

// -------------------- End of Structs -------------------
} // verus!
