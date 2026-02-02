use core::hint::spin_loop;
use core::mem;
use core::ptr;
use core::sync::atomic::{compiler_fence, Ordering};
use core::time::Duration;

use asys;
use libdma::ixgbe::allocate_dma;
use libdma::{Dma, DmaAllocator};

#[cfg(feature = "std")]
use libc;
#[cfg(feature = "std")]
use std::io;
#[cfg(feature = "std")]
use std::thread;
#[cfg(feature = "std")]
use std::time::Instant;

// Interrupt control (mirrors ice_hw_autogen.h)
const GLINT_DYN_CTL_0: usize = 0x0016_0000;
const GLINT_DYN_CTL_WB_ON_ITR_M: u32 = 1 << 30;

// Power-on/reset status
const GLGEN_RSTAT: usize = 0x000B_8188;
const GLGEN_RSTAT_DEVSTATE_M: u32 = 0x3; // ICE_M(0x3,0)
const GL_MNG_FWSM: usize = 0x000B_6134;
const GL_MNG_FWSM_FW_LOADING_M: u32 = 1 << 30;
const PFGEN_CTRL: usize = 0x0009_1000;
const PFGEN_CTRL_PFSWR_M: u32 = 1 << 0;

// AdminQ registers (PF space)
const PF_FW_ATQBAL: usize = 0x0008_0000;
const PF_FW_ATQBAH: usize = 0x0008_0100;
const PF_FW_ATQLEN: usize = 0x0008_0200;
const PF_FW_ATQLEN_ATQLEN_M: u32 = 0x3FF;
const PF_FW_ATQLEN_ATQENABLE_M: u32 = 1 << 31;
const PF_FW_ATQH: usize = 0x0008_0300;
const PF_FW_ATQH_ATQH_M: u32 = 0x3FF;
const PF_FW_ATQT: usize = 0x0008_0400;

const PF_FW_ARQBAL: usize = 0x0008_0080;
const PF_FW_ARQBAH: usize = 0x0008_0180;
const PF_FW_ARQLEN: usize = 0x0008_0280;
const PF_FW_ARQLEN_ARQLEN_M: u32 = 0x3FF;
const PF_FW_ARQLEN_ARQENABLE_M: u32 = 1 << 31;
const PF_FW_ARQH: usize = 0x0008_0380;
const PF_FW_ARQT: usize = 0x0008_0480;

// AdminQ flags/opcodes (subset)
const ICE_AQC_OPC_MANAGE_MAC_READ: u16 = 0x0107;
const ICE_AQC_MAN_MAC_LAN_ADDR_VALID: u16 = 1 << 4;
const ICE_AQC_MAN_MAC_ADDR_TYPE_LAN: u8 = 0;

const LIBIE_AQ_FLAG_LB: u16 = 0x200;
const LIBIE_AQ_FLAG_BUF: u16 = 0x1000;
const LIBIE_AQ_FLAG_SI: u16 = 0x2000;
const LIBIE_AQ_LG_BUF: usize = 512;

const ADMIN_SQ_LEN: u16 = 8;
const ADMIN_RQ_LEN: u16 = 8;
const ADMIN_SQ_COUNT: usize = ADMIN_SQ_LEN as usize;
const ADMIN_RQ_COUNT: usize = ADMIN_RQ_LEN as usize;
const ADMIN_SQ_BUF: usize = 1024;
const ADMIN_RQ_BUF: usize = 1024;
#[cfg_attr(not(feature = "std"), allow(dead_code))]
const ADMIN_TIMEOUT: Duration = Duration::from_secs(1);
#[cfg_attr(feature = "std", allow(dead_code))]
const ADMIN_POLL_ITERS: u32 = 5_000_000;

// DMA layout for admin queues: 4 KiB pages with simple page alignment.
const ADMIN_PAGE_SIZE: usize = 4096;
const ADMIN_DMA_PAGES: usize = 2 + ADMIN_SQ_COUNT + ADMIN_RQ_COUNT;
const ADMIN_DMA_BYTES: usize = ADMIN_PAGE_SIZE * ADMIN_DMA_PAGES;

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct LibieAqGeneric {
    pub param0: u32,
    pub param1: u32,
    pub addr_high: u32,
    pub addr_low: u32,
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct LibieAqDesc {
    pub flags: u16,
    pub opcode: u16,
    pub datalen: u16,
    pub retval: u16,
    pub cookie_high: u32,
    pub cookie_low: u32,
    pub params: LibieAqParams,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub union LibieAqParams {
    pub raw: [u8; 16],
    pub generic: LibieAqGeneric,
}

impl Default for LibieAqParams {
    fn default() -> Self {
        LibieAqParams { raw: [0; 16] }
    }
}

#[repr(C, packed)]
#[derive(Clone, Copy, Default)]
struct ManageMacRead {
    flags: u16,
    _rsvd0: [u8; 2],
    num_addr: u8,
    _rsvd1: [u8; 3],
    addr_high: u32,
    addr_low: u32,
}

#[repr(C, packed)]
#[derive(Clone, Copy, Default)]
struct ManageMacReadResp {
    lport_num: u8,
    addr_type: u8,
    mac_addr: [u8; 6],
}

#[derive(Debug)]
pub enum Error {
    #[cfg(feature = "std")]
    Io(io::Error),
    Timeout,
    Firmware(u16),
    InvalidResponse(&'static str),
    Config(&'static str),
}

#[cfg(feature = "std")]
impl From<io::Error> for Error {
    fn from(err: io::Error) -> Self {
        Error::Io(err)
    }
}

pub type Result<T> = core::result::Result<T, Error>;

/// Raw BAR region passed in from the caller.
#[derive(Clone, Copy)]
pub struct PciBarAddr {
    ptr: *mut u8,
    len: usize,
}

impl PciBarAddr {
    /// # Safety
    /// Caller must ensure the BAR is already mapped and that `base` points to a
    /// region of `len` bytes with read/write access to device registers.
    pub unsafe fn new(base: usize, len: usize) -> Self {
        Self {
            ptr: base as *mut u8,
            len,
        }
    }

    pub fn as_ptr(&self) -> *mut u8 {
        self.ptr
    }

    pub fn len(&self) -> usize {
        self.len
    }

    fn read32(&self, offset: usize) -> Result<u32> {
        if offset.checked_add(4).map_or(true, |end| end > self.len) {
            return Err(Error::Config("mmio read offset outside BAR"));
        }
        unsafe {
            compiler_fence(Ordering::SeqCst);
            let v = ptr::read_volatile(self.ptr.add(offset) as *const u32);
            compiler_fence(Ordering::SeqCst);
            Ok(u32::from_le(v))
        }
    }

    fn write32(&self, offset: usize, val: u32) -> Result<()> {
        if offset.checked_add(4).map_or(true, |end| end > self.len) {
            return Err(Error::Config("mmio write offset outside BAR"));
        }
        unsafe {
            compiler_fence(Ordering::SeqCst);
            ptr::write_volatile(self.ptr.add(offset) as *mut u32, val.to_le());
            let _ = ptr::read_volatile(self.ptr.add(offset) as *const u32);
            compiler_fence(Ordering::SeqCst);
            Ok(())
        }
    }
}

/// Simple DMA buffer that assumes the IOVA matches the provided `iova`.
/// `allocate` uses the shared libdma allocator to carve out a 4 KiB–aligned
/// region sized for the admin queues, relying on an identity-mapped IOVA.
pub struct DmaMemory {
    ptr: *mut u8,
    iova: u64,
    len: usize,
    _allocation: Option<Dma<AdminDmaChunk>>,
}

impl DmaMemory {
    pub fn allocate(len: usize) -> Result<Self> {
        if len > ADMIN_DMA_BYTES {
            return Err(Error::Config("adminq DMA request exceeds reserved chunk"));
        }

        let mut allocation = allocate_dma::<AdminDmaChunk>()
            .map_err(|_| Error::Config("failed to allocate adminq DMA"))?;

        let base_ptr = {
            let chunk: &mut AdminDmaChunk = &mut *allocation;
            chunk.0.as_mut_ptr()
        };

        Ok(Self {
            ptr: base_ptr,
            iova: allocation.physical() as u64,
            len: ADMIN_DMA_BYTES,
            _allocation: Some(allocation),
        })
    }

    /// # Safety
    /// The caller must guarantee `ptr`/`iova` are valid DMA-able memory the NIC
    /// can access for the lifetime of the device.
    pub unsafe fn from_raw_parts(ptr: *mut u8, iova: u64, len: usize) -> Self {
        Self {
            ptr,
            iova,
            len,
            _allocation: None,
        }
    }
}

#[repr(align(4096))]
struct AdminDmaChunk([u8; ADMIN_DMA_BYTES]);

impl DmaAllocator for AdminDmaChunk {
    fn allocate() -> core::result::Result<Dma<Self>, i32> {
        unsafe { Dma::zeroed() }
    }
}

#[derive(Clone, Copy)]
struct DmaSlice {
    ptr: *mut u8,
    iova: u64,
    len: usize,
}

impl Default for DmaSlice {
    fn default() -> Self {
        Self {
            ptr: core::ptr::null_mut(),
            iova: 0,
            len: 0,
        }
    }
}

struct AdminDmaAllocator<'a> {
    base: &'a DmaMemory,
    page: usize,
    offset: usize,
}

impl<'a> AdminDmaAllocator<'a> {
    fn new(base: &'a DmaMemory, page: usize) -> Self {
        Self {
            base,
            page,
            offset: 0,
        }
    }

    fn take(&mut self, len: usize, align: usize) -> Result<DmaSlice> {
        if align == 0 {
            return Err(Error::Config("alignment cannot be zero"));
        }
        let align_to = align.max(self.page);
        let start = align_up(self.offset, align_to);
        let end = start
            .checked_add(len)
            .ok_or_else(|| Error::InvalidResponse("DMA layout overflowed available space"))?;
        if end > self.base.len {
            return Err(Error::InvalidResponse("not enough DMA space reserved"));
        }
        self.offset = end;
        Ok(DmaSlice {
            ptr: unsafe { self.base.ptr.add(start) },
            iova: self.base.iova + start as u64,
            len,
        })
    }
}

#[derive(Clone, Copy, Debug)]
pub struct StartupRegs {
    pub glgen_rstat: u32,
    pub gl_mng_fwsm: u32,
    pub pfgen_ctrl: u32,
}

pub struct E810Device {
    bar0: PciBarAddr,
    adminq: AdminQueue,
    _dma: DmaMemory,
    dma_mapped: bool,
}

impl E810Device {
    /// # Safety
    /// `bar0` must be a valid, writable mapping of the device's BAR0 registers.
    /// The default allocator assumes an identity IOVA; pass your own DMA mapping
    /// via `with_dma` when that is not the case.
    pub unsafe fn new(bar0: PciBarAddr) -> Result<Self> {
        let page_size = page_size()?;
        let dma_bytes = AdminQueue::dma_bytes(page_size);
        let dma = DmaMemory::allocate(dma_bytes)?;
        log::info!(
        "Admin DMA allocated: ptr={:#p}, iova={:#x}, len={} bytes (page_size={})",
            dma.ptr,
            dma.iova,
            dma.len,
            page_size
        );
        Self::with_dma(bar0, dma)
    }

    /// # Safety
    /// The caller must ensure that `bar0` and the provided DMA memory are valid
    /// and accessible by the NIC for the lifetime of the device.
    pub unsafe fn with_dma(bar0: PciBarAddr, dma: DmaMemory) -> Result<Self> {
        if bar0.as_ptr().is_null() || bar0.len() == 0 {
            return Err(Error::Config("BAR0 pointer/length invalid"));
        }
        let page_size = page_size()?;
        let mut alloc = AdminDmaAllocator::new(&dma, page_size);
        let adminq = AdminQueue::new(bar0, &mut alloc, page_size)?;
        Ok(Self {
            bar0,
            adminq,
            _dma: dma,
            dma_mapped: false,
        })
    }

    pub fn bar0(&self) -> PciBarAddr {
        self.bar0
    }

    /// Polls for the device to leave reset and for firmware loader to finish.
    pub fn wait_for_device_active(&self, mut loops: usize) -> Result<()> {
        while loops > 0 {
            let rstat = self.bar0.read32(GLGEN_RSTAT)?;
            let fwm = self.bar0.read32(GL_MNG_FWSM)?;
            let pfc = self.bar0.read32(PFGEN_CTRL)?;
            let devstate_ok = (rstat & GLGEN_RSTAT_DEVSTATE_M) == 0;
            let fw_not_loading = (fwm & GL_MNG_FWSM_FW_LOADING_M) == 0;
            let pf_not_in_swreset = (pfc & PFGEN_CTRL_PFSWR_M) == 0;

            if devstate_ok && fw_not_loading && pf_not_in_swreset {
                log::info!("Device seems fine!!!!!");
                return Ok(());
            }
            loops -= 1;
            spin_loop();
        }

        Err(Error::Timeout)
    }

    pub fn dump_startup_regs(&self) -> Result<StartupRegs> {
        let regs = StartupRegs {
            glgen_rstat: self.bar0.read32(GLGEN_RSTAT)?,
            gl_mng_fwsm: self.bar0.read32(GL_MNG_FWSM)?,
            pfgen_ctrl: self.bar0.read32(PFGEN_CTRL)?,
        };

        log::info!("GLGEN_RSTAT = 0x{:08x}", regs.glgen_rstat);
        log::info!("GL_MNG_FWSM = 0x{:08x}", regs.gl_mng_fwsm);
        log::info!("PFGEN_CTRL  = 0x{:08x}", regs.pfgen_ctrl);
        Ok(regs)
    }

    /// Disable IRQ0 by writing GLINT_DYN_CTL(0) with WB_ON_ITR (mirrors Linux reset path).
    pub fn disable_irq0(&self) -> Result<()> {
        self.bar0.write32(GLINT_DYN_CTL_0, GLINT_DYN_CTL_WB_ON_ITR_M)?;
        let _ = self.bar0.read32(GLINT_DYN_CTL_0)?;
        Ok(())
    }

    /// Map the admin queue DMA region into the IOMMU and invalidate the device's IOTLB.
    pub fn map_admin_dma(&mut self, bdf: (usize, usize, usize)) -> Result<()> {
        if self.dma_mapped {
            return Ok(());
        }

        if self._dma.ptr.is_null() || self._dma.len == 0 {
            return Err(Error::Config("admin DMA region is empty"));
        }

        let base = self._dma.ptr as usize;
        let pages = (self._dma.len + ADMIN_PAGE_SIZE - 1) / ADMIN_PAGE_SIZE;
        let io_flags = 0x2usize; // read/write

        let map_res = unsafe { asys::sys_mmap(base, io_flags, pages) };
        if map_res != 0 {
            log::error!(
                "sys_mmap failed for admin DMA (base={:#x}, pages={}): {}",
                base,
                pages,
                map_res
            );
            return Err(Error::Config("failed to mmap admin DMA"));
        }

        // let res = unsafe { asys::sys_io_mmap(base, io_flags, pages) };
        // if res != 0 {
        //     log::error!(
        //         "sys_io_mmap failed for admin DMA (base={:#x}, pages={}): {}",
        //         base,
        //         pages,
        //         res
        //     );
        //     return Err(Error::Config("failed to map admin DMA into IOMMU"));
        // }

        for page in 0..pages {
            let addr = base + page * ADMIN_PAGE_SIZE;
            unsafe { asys::sys_invalidate_iotlb(bdf.0, bdf.1, bdf.2, addr as u64) };
        }

        self.dma_mapped = true;
        Ok(())
    }

    /// Program admin queue registers after DMA is mapped.
    pub fn init_adminq(&mut self, bdf: (usize, usize, usize)) -> Result<()> {
        self.map_admin_dma(bdf)?;
        self.adminq.program_hw()?;
        Ok(())
    }

    pub fn submit_adminq(
        &mut self,
        desc: &mut LibieAqDesc,
        buf: Option<&mut [u8]>,
    ) -> Result<()> {
        if !self.adminq.ready() {
            return Err(Error::Config("admin queue not initialized"));
        }
        self.adminq.send(desc, buf)
    }

    pub fn read_mac(&mut self) -> Result<[u8; 6]> {
        if !self.adminq.ready() {
            return Err(Error::Config("admin queue not initialized"));
        }

        let mut desc = LibieAqDesc::default();
        desc.opcode = ICE_AQC_OPC_MANAGE_MAC_READ.to_le();
        desc.flags = LIBIE_AQ_FLAG_SI.to_le();
        // desc.flags = 0;

        // Two entries is what the driver uses (LAN + WoL).
        let mut buf = [0u8; 2 * mem::size_of::<ManageMacReadResp>()];
        self.adminq.send(&mut desc, Some(&mut buf))?;

        let cmd: ManageMacRead =
            unsafe { ptr::read_unaligned(desc.params.raw.as_ptr() as *const ManageMacRead) };
        let flags = u16::from_le(cmd.flags);
        if flags & ICE_AQC_MAN_MAC_LAN_ADDR_VALID == 0 {
            return Err(Error::InvalidResponse("firmware reported MAC as invalid"));
        }

        let resp_count = cmd.num_addr as usize;
        let max_entries = buf.len() / mem::size_of::<ManageMacReadResp>();
        let mut found = None;

        for idx in 0..resp_count.min(max_entries) {
            let start = idx * mem::size_of::<ManageMacReadResp>();
            let entry: ManageMacReadResp = unsafe {
                ptr::read_unaligned(buf[start..].as_ptr() as *const ManageMacReadResp)
            };
            if entry.addr_type == ICE_AQC_MAN_MAC_ADDR_TYPE_LAN {
                found = Some(entry.mac_addr);
                break;
            }
        }

        found.ok_or_else(|| Error::InvalidResponse("no LAN MAC returned"))
    }
}

struct AdminQueue {
    bar0: PciBarAddr,
    sq_ring: DmaSlice,
    rq_ring: DmaSlice,
    sq_bufs: [DmaSlice; ADMIN_SQ_COUNT],
    _rq_bufs: [DmaSlice; ADMIN_RQ_COUNT],
    sq_tail: u16,
    sq_count: u16,
    programmed: bool,
}

impl AdminQueue {
    fn dma_bytes(_page_size: usize) -> usize {
        ADMIN_DMA_BYTES
    }

    fn new(bar0: PciBarAddr, alloc: &mut AdminDmaAllocator, page_size: usize) -> Result<Self> {
        if bar0.as_ptr().is_null() {
            return Err(Error::Config("BAR0 pointer was null"));
        }

        let sq_ring = alloc.take(
            (ADMIN_SQ_LEN as usize) * mem::size_of::<LibieAqDesc>(),
            page_size,
        )?;
        let rq_ring = alloc.take(
            (ADMIN_RQ_LEN as usize) * mem::size_of::<LibieAqDesc>(),
            page_size,
        )?;

        let mut sq_bufs = [DmaSlice::default(); ADMIN_SQ_COUNT];
        for buf in sq_bufs.iter_mut() {
            *buf = alloc.take(ADMIN_SQ_BUF, page_size)?;
        }

        let mut rq_bufs = [DmaSlice::default(); ADMIN_RQ_COUNT];
        for buf in rq_bufs.iter_mut() {
            *buf = alloc.take(ADMIN_RQ_BUF, page_size)?;
        }

        unsafe {
            ptr::write_bytes(sq_ring.ptr, 0, sq_ring.len);
            ptr::write_bytes(rq_ring.ptr, 0, rq_ring.len);
            for b in &sq_bufs {
                ptr::write_bytes(b.ptr, 0, b.len);
            }
            for b in &rq_bufs {
                ptr::write_bytes(b.ptr, 0, b.len);
            }
        }

        // Pre-post RQ buffers so the hardware can DMA completions immediately after enabling.
        for (idx, buf) in rq_bufs.iter().enumerate() {
            let desc = unsafe {
                (rq_ring.ptr as *mut LibieAqDesc)
                    .add(idx)
                    .as_mut()
                    .unwrap()
            };
            let mut flags = LIBIE_AQ_FLAG_BUF;
            if buf.len > LIBIE_AQ_LG_BUF {
                flags |= LIBIE_AQ_FLAG_LB;
            }
            *desc = LibieAqDesc {
                flags: flags.to_le(),
                datalen: (buf.len as u16).to_le(),
                params: LibieAqParams {
                    generic: LibieAqGeneric {
                        addr_high: high(buf.iova),
                        addr_low: low(buf.iova),
                        ..Default::default()
                    },
                },
                ..Default::default()
            };
        }
        Ok(Self {
            bar0,
            sq_ring,
            rq_ring,
            sq_bufs,
            _rq_bufs: rq_bufs,
            sq_tail: 0,
            sq_count: ADMIN_SQ_LEN,
            programmed: false,
        })
    }

    fn program_hw(&mut self) -> Result<()> {
        compiler_fence(Ordering::SeqCst);

        self.bar0.write32(PF_FW_ATQH, 0)?;
        self.bar0.write32(PF_FW_ATQT, 0)?;
        self.bar0.write32(
            PF_FW_ATQLEN,
            (ADMIN_SQ_LEN as u32 & PF_FW_ATQLEN_ATQLEN_M) | PF_FW_ATQLEN_ATQENABLE_M,
        )?;
        log::info!(
            "Programming Admin SQ: iova={:#x}, len={}",
            self.sq_ring.iova,
            self.sq_ring.len
        );
        self.bar0.write32(PF_FW_ATQBAL, low(self.sq_ring.iova))?;
        self.bar0.write32(PF_FW_ATQBAH, high(self.sq_ring.iova))?;

        self.bar0.write32(PF_FW_ARQH, 0)?;
        self.bar0.write32(PF_FW_ARQT, 0)?;
        self.bar0.write32(
            PF_FW_ARQLEN,
            (ADMIN_RQ_LEN as u32 & PF_FW_ARQLEN_ARQLEN_M) | PF_FW_ARQLEN_ARQENABLE_M,
        )?;
                log::info!(
            "Programming Admin RQ: iova={:#x}, len={}",
            self.rq_ring.iova,
            self.rq_ring.len
        );
        self.bar0.write32(PF_FW_ARQBAL, low(self.rq_ring.iova))?;
        self.bar0.write32(PF_FW_ARQBAH, high(self.rq_ring.iova))?;
        self.bar0
            .write32(PF_FW_ARQT, (ADMIN_RQ_LEN as u32).wrapping_sub(1))?;

        self.programmed = true;
        Ok(())
    }

    fn ready(&self) -> bool {
        self.programmed
    }

    fn send(&mut self, desc: &mut LibieAqDesc, buf: Option<&mut [u8]>) -> Result<()> {
        if !self.programmed {
            return Err(Error::Config("admin queue not initialized"));
        }

        let mut buf = buf;
        let idx = self.sq_tail as usize;
        let ring_desc = unsafe {
            (self.sq_ring.ptr as *mut LibieAqDesc)
                .add(idx)
                .as_mut()
                .unwrap()
        };
        let dma_buf = &self.sq_bufs[idx];

        if let Some(data_ref) = buf.as_mut() {
            let data = &mut **data_ref;
            if data.len() > dma_buf.len {
                return Err(Error::InvalidResponse("adminq buffer too small"));
            }
            unsafe {
                ptr::copy_nonoverlapping(data.as_ptr(), dma_buf.ptr, data.len());
            }
            let mut flags = u16::from_le(desc.flags) | LIBIE_AQ_FLAG_BUF;
            if data.len() > LIBIE_AQ_LG_BUF {
                flags |= LIBIE_AQ_FLAG_LB;
            }
            desc.flags = flags.to_le();
            desc.datalen = (data.len() as u16).to_le();
            desc.params.generic.addr_high = high(dma_buf.iova);
            desc.params.generic.addr_low = low(dma_buf.iova);
        }

        unsafe {
            ptr::write_volatile(ring_desc, *desc);
        }
        compiler_fence(Ordering::SeqCst);

        self.sq_tail = (self.sq_tail + 1) % self.sq_count;
        self.bar0.write32(PF_FW_ATQT, self.sq_tail as u32)?;

        #[cfg(feature = "std")]
        {
            let deadline = Instant::now() + ADMIN_TIMEOUT;
            loop {
                let head = self.bar0.read32(PF_FW_ATQH)? & PF_FW_ATQH_ATQH_M;
                if head == self.sq_tail as u32 {
                    break;
                }
                if Instant::now() > deadline {
                    return Err(Error::Timeout);
                }
                thread::sleep(Duration::from_micros(20));
            }
        }

        #[cfg(not(feature = "std"))]
        {
            let mut iters = ADMIN_POLL_ITERS;
            loop {
                let head = self.bar0.read32(PF_FW_ATQH)? & PF_FW_ATQH_ATQH_M;
                if head == self.sq_tail as u32 {
                    break;
                }
                if iters == 0 {
                    let wb = unsafe { ptr::read_volatile(ring_desc) };
                    log::error!(
                        "adminq timeout: head=0x{:x} tail=0x{:x} flags=0x{:04x} retval=0x{:04x}",
                        head,
                        self.sq_tail,
                        u16::from_le(wb.flags),
                        u16::from_le(wb.retval)
                    );
                    return Err(Error::Timeout);
                }
                iters -= 1;
                spin_loop();
            }
        }

        let completed = unsafe { ptr::read_volatile(ring_desc) };
        *desc = completed;

        if let Some(data_ref) = buf.as_mut() {
            let data = &mut **data_ref;
            let copy_len = u16::from_le(desc.datalen) as usize;
            if copy_len > data.len() {
                return Err(Error::InvalidResponse(
                    "firmware returned longer buffer than provided",
                ));
            }
            unsafe {
                ptr::copy_nonoverlapping(dma_buf.ptr, data.as_mut_ptr(), copy_len);
            }
        }

        let retval = u16::from_le(desc.retval);
        if retval != 0 {
            return Err(Error::Firmware(retval));
        }

        Ok(())
    }
}

fn high(val: u64) -> u32 {
    (val >> 32) as u32
}

fn low(val: u64) -> u32 {
    (val & 0xFFFF_FFFF) as u32
}

fn align_up(val: usize, align: usize) -> usize {
    (val + align - 1) & !(align - 1)
}

#[cfg(feature = "std")]
fn page_size() -> Result<usize> {
    let sz = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    if sz <= 0 {
        return Err(Error::Config("failed to query page size"));
    }
    Ok(sz as usize)
}

#[cfg(not(feature = "std"))]
fn page_size() -> Result<usize> {
    Ok(ADMIN_PAGE_SIZE)
}
