use core::sync::atomic::{compiler_fence, Ordering};
use core::hint::spin_loop;
use core::ptr;
use asys;
use libdma::ixgbe::allocate_dma;
use libdma::Dma;
use pcid::utils::PciBarAddr;

/// Tiny error type
#[derive(Debug, Clone, Copy)]
pub enum E810Error {
    InvalidBar,
    Timeout,
    Mmio,
    Other,
}
pub type Result<T> = core::result::Result<T, E810Error>;

pub struct E810Device {
    pub bar: PciBarAddr,
    mmio_base: usize,
    mmio_size: usize,
}
use crate::aq::{
    IceAqDesc,
    IceAqcManageMacRead,
    IceAqcManageMacReadResp,
    ICE_AQC_OPC_MANAGE_MAC_READ,
    ICE_AQ_FLAG_BUF,
    ICE_AQ_FLAG_RD,
    ICE_AQ_FLAG_DD,
    ICE_AQ_FLAG_ERR
};


/* --- Constants taken from your ice_hw_autogen.h snippet --- */
/* GLINT dynamic control base for interrupt index 0 */
const GLINT_DYN_CTL_0: usize = 0x0016_0000;
/* Mask used in header: GLINT_DYN_CTL_WB_ON_ITR_M */
const GLINT_DYN_CTL_WB_ON_ITR_M: u32 = 1 << 30;
/* GLINT dynamic control INTENA mask (not used, but available) */
#[allow(dead_code)]
const GLINT_DYN_CTL_INTENA_M: u32 = 1 << 0;

const PF_FW_ATQH: usize = 0x0008_0300;
const PF_FW_ATQT: usize = 0x0008_0400;
const PF_FW_ATQH_ATQH_M: u32 = 0x3ff; // PF_FW_ATQH_ATQH_M

/* ------- End constants ------- */

const PAGE_SIZE: usize = 4096;

pub struct AdminQueue {
    atq_page: Dma<[u8; PAGE_SIZE]>,
    arq_page: Dma<[u8; PAGE_SIZE]>,
    entries: u16,
    ring_bytes: usize,
}

impl AdminQueue {
    pub fn new(entries: u16) -> Result<Self> {
        let ring_bytes = (entries as usize) * core::mem::size_of::<IceAqDesc>();

        if ring_bytes >= PAGE_SIZE {
            log::error!(
                "adminq ring too large for page: entries={} ({} bytes)",
                entries,
                ring_bytes
            );
            return Err(E810Error::Other);
        }

        let atq_page: Dma<[u8; PAGE_SIZE]> =
            allocate_dma().map_err(|e| {
                log::error!("failed to allocate ATQ DMA page: {}", e);
                E810Error::Other
            })?;
        let arq_page: Dma<[u8; PAGE_SIZE]> =
            allocate_dma().map_err(|e| {
                log::error!("failed to allocate ARQ DMA page: {}", e);
                E810Error::Other
            })?;

        Ok(Self {
            atq_page,
            arq_page,
            entries,
            ring_bytes,
        })
    }

    #[inline(always)]
    pub fn atq_dma(&self) -> u64 {
        self.atq_page.physical() as u64
    }

    #[inline(always)]
    pub fn arq_dma(&self) -> u64 {
        self.arq_page.physical() as u64
    }

    #[inline(always)]
    pub fn atq_virt(&self) -> *mut u8 {
        self.atq_page.as_ptr() as *mut u8
    }

    #[inline(always)]
    pub fn arq_virt(&self) -> *mut u8 {
        self.arq_page.as_ptr() as *mut u8
    }

    #[inline(always)]
    pub fn entries(&self) -> u16 {
        self.entries
    }

    #[inline(always)]
    pub fn ring_bytes(&self) -> usize {
        self.ring_bytes
    }

    pub fn clear(&mut self) {
        unsafe {
            ptr::write_bytes(self.atq_virt(), 0, PAGE_SIZE);
            ptr::write_bytes(self.arq_virt(), 0, PAGE_SIZE);
        }
    }

    pub fn invalidate_iotlb(&self, bus: usize, device: usize, function: usize) {
        let mask = !(PAGE_SIZE as u64 - 1);
        let atq_page = self.atq_dma() & mask;
        let arq_page = self.arq_dma() & mask;

        unsafe {
            let atq_res = asys::sys_invalidate_iotlb(bus, device, function, atq_page);
            if atq_res != 0 {
                log::warn!(
                    "IOTLB invalidate failed for ATQ page {:x} (res={})",
                    atq_page,
                    atq_res
                );
            }

            let arq_res = asys::sys_invalidate_iotlb(bus, device, function, arq_page);
            if arq_res != 0 {
                log::warn!(
                    "IOTLB invalidate failed for ARQ page {:x} (res={})",
                    arq_page,
                    arq_res
                );
            }
        }
    }
}

impl E810Device {
    pub fn submit_manage_mac_read_once(
        &mut self,
        adminq: &mut AdminQueue,
    ) -> Result<[u8; 6]> {
        if adminq.ring_bytes() >= PAGE_SIZE {
            log::error!(
                "submit_manage_mac_read_once: ring_bytes {} exceed page",
                adminq.ring_bytes()
            );
            return Err(E810Error::Other);
        }

        adminq.clear();

        // Descriptor 0 at start of ATQ page
        let desc = unsafe { &mut *(adminq.atq_virt() as *mut IceAqDesc) };

        // Response buffer placed after the ring
        let resp_buf_virt = unsafe { adminq.atq_virt().add(adminq.ring_bytes()) };
        let resp_buf_dma = adminq.atq_dma() + adminq.ring_bytes() as u64;
        let resp_size = (2 * core::mem::size_of::<IceAqcManageMacReadResp>()) as u16;

        *desc = IceAqDesc::default();
        desc.opcode = ICE_AQC_OPC_MANAGE_MAC_READ.to_le();
        desc.flags = (ICE_AQ_FLAG_RD | ICE_AQ_FLAG_BUF).to_le();
        desc.datalen = resp_size.to_le();
        desc.addr_high = ((resp_buf_dma >> 32) as u32).to_le();
        desc.addr_low = (resp_buf_dma as u32).to_le();

        // Fill the command payload (params.mac_read)
        let cmd = unsafe { &mut *(&mut desc.param0 as *mut u32 as *mut IceAqcManageMacRead) };
        *cmd = IceAqcManageMacRead::default();
        cmd.num_addr = 2; // ask for two entries (LAN + WoL) like Linux

        log::info!(
            "submit_manage_mac_read_once: ATQ virt=0x{:x} dma=0x{:x}, resp dma=0x{:x} ({} bytes)",
            adminq.atq_virt() as u64,
            adminq.atq_dma(),
            resp_buf_dma,
            resp_size
        );

        // Ensure descriptor writes are visible before doorbell
        compiler_fence(Ordering::SeqCst);

        // Ring tail to index 1
        let tail_idx: u16 = 1;
        self.writel(PF_FW_ATQT, tail_idx as u32)?;

        // Poll ATQH until it reaches 1
        let expected_head = (tail_idx as u32) & PF_FW_ATQH_ATQH_M;
        let mut loops = 1_000_000;
        while loops > 0 {
            let h = self.readl(PF_FW_ATQH)?;
            if (h & PF_FW_ATQH_ATQH_M) == expected_head {
                break;
            }
            loops -= 1;
            spin_loop();
        }
        if loops == 0 {
            log::error!("submit_manage_mac_read_once: timeout waiting for ATQH");
            return Err(E810Error::Timeout);
        }

        // Now descriptor 0 should contain writeback (flags, retval, etc).
        let f = u16::from_le(desc.flags);
        let retval = u16::from_le(desc.retval);

        log::info!(
            "submit_manage_mac_read_once: flags=0x{:04x} retval=0x{:04x}",
            f,
            retval
        );

        if (f & ICE_AQ_FLAG_DD) == 0 {
            log::warn!("submit_manage_mac_read_once: DD not set on completion");
        }

        if (f & ICE_AQ_FLAG_ERR) != 0 || retval != 0 {
            log::error!(
                "submit_manage_mac_read_once: AQ error (flags=0x{:04x}, retval=0x{:04x})",
                f,
                retval
            );
            return Err(E810Error::Other);
        }

        // Parse MAC from response buffer. For now, just read the first entry
        // and return its MAC.
        let resp = unsafe { &*(resp_buf_virt as *const IceAqcManageMacReadResp) };
        let mac = resp.mac_addr;

        log::info!(
            "submit_manage_mac_read_once: got MAC {:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}",
            mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]
        );

        Ok(mac)
    }

    pub fn init_adminq(
        &mut self,
        bdf: (usize, usize, usize),
        entries: u16,
    ) -> Result<AdminQueue> {
        let adminq = AdminQueue::new(entries)?;

        adminq.invalidate_iotlb(bdf.0, bdf.1, bdf.2);

        log::info!(
            "Allocated adminq rings: ATQ virt=0x{:x}, dma=0x{:x}; ARQ virt=0x{:x}, dma=0x{:x}",
            adminq.atq_virt() as u64,
            adminq.atq_dma(),
            adminq.arq_virt() as u64,
            adminq.arq_dma()
        );

        self.setup_adminq_minimal(&adminq)?;

        Ok(adminq)
    }

    pub fn setup_adminq_minimal(&mut self, adminq: &AdminQueue) -> Result<()> {
        const PF_FW_ATQBAL: usize = 0x0008_0000;
        const PF_FW_ATQBAH: usize = 0x0008_0100;
        const PF_FW_ATQLEN: usize = 0x0008_0200;
        const PF_FW_ATQH:   usize = 0x0008_0300;
        const PF_FW_ATQT:   usize = 0x0008_0400;

        const PF_FW_ARQBAL: usize = 0x0008_0080;
        const PF_FW_ARQBAH: usize = 0x0008_0180;
        const PF_FW_ARQLEN: usize = 0x0008_0280;
        const PF_FW_ARQH:   usize = 0x0008_0380;
        const PF_FW_ARQT:   usize = 0x0008_0480;

        const ATQENABLE_M: u32 = 1u32 << 31; // PF_FW_ATQLEN_ATQENABLE_M
        const ARQENABLE_M: u32 = 1u32 << 31; // PF_FW_ARQLEN_ARQENABLE_M
        const LEN_MASK:   u32 = 0x3ff;       // PF_FW_ATQLEN_ATQLEN_M / ARQLEN_M
        let ring_len = adminq.entries() as u32;

        if ring_len == 0 {
            log::error!("setup_adminq_minimal: ring_len must be non-zero");
            return Err(E810Error::Other);
        }

        let atq_iova = adminq.atq_dma();
        let arq_iova = adminq.arq_dma();

        let atqbal = (atq_iova & 0xFFFF_FFFF) as u32;
        let atqbah = ((atq_iova >> 32) & 0xFFFF_FFFF) as u32;
        let arqbal = (arq_iova & 0xFFFF_FFFF) as u32;
        let arqbah = ((arq_iova >> 32) & 0xFFFF_FFFF) as u32;

        // 1) program base addrs
        self.writel(PF_FW_ATQBAL, atqbal)?;
        self.writel(PF_FW_ATQBAH, atqbah)?;
        self.writel(PF_FW_ARQBAL, arqbal)?;
        self.writel(PF_FW_ARQBAH, arqbah)?;

        // 2) clear head/tail
        self.writel(PF_FW_ATQH, 0)?;
        self.writel(PF_FW_ATQT, 0)?;
        self.writel(PF_FW_ARQH, 0)?;
        self.writel(PF_FW_ARQT, 0)?;

        // 3) enable rings
        let len_field = (ring_len & LEN_MASK) as u32;
        let atq_len_val = ATQENABLE_M | len_field;
        let arq_len_val = ARQENABLE_M | len_field;

        self.writel(PF_FW_ATQLEN, atq_len_val)?;
        self.writel(PF_FW_ARQLEN, arq_len_val)?;

        // For ARQ, Linux pre-posts all entries and then sets tail=num_rq_entries-1.
        // We don't actually _use_ ARQ yet, but this mirrors the real init.
        let arq_tail = ((ring_len - 1) & LEN_MASK) as u32;
        self.writel(PF_FW_ARQT, arq_tail)?;

        // Readback for debug:
        let r_atqbal = self.readl(PF_FW_ATQBAL)?;
        let r_atqbah = self.readl(PF_FW_ATQBAH)?;
        let r_atqlen = self.readl(PF_FW_ATQLEN)?;
        let r_arqbal = self.readl(PF_FW_ARQBAL)?;
        let r_arqbah = self.readl(PF_FW_ARQBAH)?;
        let r_arqlen = self.readl(PF_FW_ARQLEN)?;
        let r_atqh   = self.readl(PF_FW_ATQH)?;
        let r_atqt   = self.readl(PF_FW_ATQT)?;
        let r_arqh   = self.readl(PF_FW_ARQH)?;
        let r_arqt   = self.readl(PF_FW_ARQT)?;

        log::info!("ATQ BAL/BAH = 0x{:08x}/0x{:08x}, LEN=0x{:08x}, H/T=0x{:08x}/0x{:08x}",
                r_atqbal, r_atqbah, r_atqlen, r_atqh, r_atqt);
        log::info!("ARQ BAL/BAH = 0x{:08x}/0x{:08x}, LEN=0x{:08x}, H/T=0x{:08x}/0x{:08x}",
                r_arqbal, r_arqbah, r_arqlen, r_arqh, r_arqt);

        if (r_atqlen & ATQENABLE_M) == 0 || (r_arqlen & ARQENABLE_M) == 0 {
            log::warn!("ATQ/ARQ enable bits not set after programming");
            return Err(E810Error::Other);
        }

        Ok(())
    }

    pub fn dump_and_check_adminq_ready(&self) -> Result<bool> {
        // Autogen offsets:
        const PF_FW_ATQBAL: usize = 0x0008_0000;
        const PF_FW_ATQBAH: usize = 0x0008_0100;
        const PF_FW_ATQLEN: usize = 0x0008_0200;

        const PF_FW_ARQBAL: usize = 0x0008_0080;
        const PF_FW_ARQBAH: usize = 0x0008_0180;
        const PF_FW_ARQLEN: usize = 0x0008_0280;

        const GLNVM_ULD: usize = 0x000B_6008;
        const GL_MNG_FWSM: usize = 0x000B_6134;

        // Masks:
        const ATQENABLE: u32 = 1u32 << 31;
        const ARQENABLE: u32 = 1u32 << 31;

        let atqbal = self.readl(PF_FW_ATQBAL)?;
        let atqbah = self.readl(PF_FW_ATQBAH)?;
        let atqlen = self.readl(PF_FW_ATQLEN)?;

        let arqbal = self.readl(PF_FW_ARQBAL)?;
        let arqbah = self.readl(PF_FW_ARQBAH)?;
        let arqlen = self.readl(PF_FW_ARQLEN)?;

        let glnvm = self.readl(GLNVM_ULD)?;
        let fws = self.readl(GL_MNG_FWSM)?;

        log::info!("PF_FW_ATQBAL = 0x{:08x}", atqbal);
        log::info!("PF_FW_ATQBAH = 0x{:08x}", atqbah);
        log::info!("PF_FW_ATQLEN = 0x{:08x}", atqlen);
        log::info!("PF_FW_ARQBAL = 0x{:08x}", arqbal);
        log::info!("PF_FW_ARQBAH = 0x{:08x}", arqbah);
        log::info!("PF_FW_ARQLEN = 0x{:08x}", arqlen);

        log::info!("GLNVM_ULD = 0x{:08x}", glnvm);
        log::info!("GL_MNG_FWSM = 0x{:08x}", fws);

        // Interpret
        let atq_base_nonzero = (atqbal != 0) || (atqbah != 0);
        let arq_base_nonzero = (arqbal != 0) || (arqbah != 0);
        let atq_enabled = (atqlen & ATQENABLE) != 0;
        let arq_enabled = (arqlen & ARQENABLE) != 0;

        if atq_enabled || arq_enabled {
            log::info!("Admin queues show ENABLED: ATQ_enabled={}, ARQ_enabled={}", atq_enabled, arq_enabled);
        } else {
            log::info!("Admin queues not enabled yet by firmware/host.");
        }

        if atq_base_nonzero || arq_base_nonzero {
            log::info!("Some admin queue base addresses are non-zero (likely programmed): ATQ_base_nonzero={}, ARQ_base_nonzero={}", atq_base_nonzero, arq_base_nonzero);
        } else {
            log::info!("Admin queue base addresses appear zero.");
        }

        // Check NVM: if any of the glnvm bits indicate not-done, warn
        // (we don't know all bits you care about — but if GLNVM_ULD != 0 it's worth inspecting)
        if glnvm != 0 {
            log::info!("GLNVM_ULD non-zero: 0x{:08x}. Inspect NVM DONE bits.", glnvm);
        }

        // Quick heuristic: admin queues "ready" if both bases are non-zero and enable bits set.
        // Relax this if you want to manually program them from userspace.
        let adminq_ready = atq_base_nonzero && arq_base_nonzero && atq_enabled && arq_enabled;

        Ok(adminq_ready)
    }
    pub fn dump_startup_regs(&self) -> Result<()> {
        const GLGEN_RSTAT: usize = 0x000B_8188;
        const GL_MNG_FWSM: usize = 0x000B_6134;
        const PFGEN_CTRL: usize = 0x0009_1000;

        let rstat = self.readl(GLGEN_RSTAT)?;
        let fws  = self.readl(GL_MNG_FWSM)?;
        let pfc  = self.readl(PFGEN_CTRL)?;

        // Use your logging facility in caller; return the raw values here.
        // If you don't have `std`, call into the caller to print; here we return them:
        log::info!("GLGEN_RSTAT = 0x{:08x}", rstat);
        log::info!("GL_MNG_FWSM = 0x{:08x}", fws);
        log::info!("PFGEN_CTRL  = 0x{:08x}", pfc);

        Ok(())
    }
    pub fn wait_for_device_active(&self, timeout_loops: usize) -> Result<()> {
        // Constants taken from ice_hw_autogen.h provided earlier:
        const GLGEN_RSTAT: usize = 0x000B_8188;
        const GLGEN_RSTAT_DEVSTATE_M: u32 = 0x3; // ICE_M(0x3,0)

        const GL_MNG_FWSM: usize = 0x000B_6134;
        const GL_MNG_FWSM_FW_LOADING_M: u32 = 1 << 30;

        const PFGEN_CTRL: usize = 0x0009_1000;
        const PFGEN_CTRL_PFSWR_M: u32 = 1 << 0;

        // Closure that returns Ok(true) when all conditions are met.
        let check_ready = || -> Result<bool> {
            // 1) out of reset: DEVSTATE == 0?
            let rstat = self.readl(GLGEN_RSTAT)?;
            let devstate_ok = (rstat & GLGEN_RSTAT_DEVSTATE_M) == 0;

            // 2) firmware loader not busy
            let fwm = self.readl(GL_MNG_FWSM)?;
            let fw_not_loading = (fwm & GL_MNG_FWSM_FW_LOADING_M) == 0;

            // 3) PF soft reset bit cleared
            let pfc = self.readl(PFGEN_CTRL)?;
            let pf_not_in_swreset = (pfc & PFGEN_CTRL_PFSWR_M) == 0;

            Ok(devstate_ok && fw_not_loading && pf_not_in_swreset)
        };

        // Poll loop using your poll helper (adapting signature)
        // Reuse your existing poll() pattern that accepts a read function and predicate;
        // here we implement a small loop so we can check all three conditions together.
        let mut loops = timeout_loops;
        while loops > 0 {
            match check_ready() {
                Ok(true) => return Ok(()),
                Ok(false) => { /* not ready yet */ }
                Err(e) => {
                    // If MMIO read failed, bubble up as Mmio error
                    return Err(e);
                }
            }
            loops -= 1;
            core::hint::spin_loop();
        }

        Err(E810Error::Timeout)
    }

    /// Safety: caller must ensure `bar` is a valid mapping for this process.
    pub unsafe fn new(bar: PciBarAddr) -> Self {
        // use provided accessors on PciBarAddr
        let mmio_base = bar.base() as usize;
        let mmio_size = bar.size();
        E810Device { bar, mmio_base, mmio_size }
    }

    #[inline(always)]
    fn base_ptr(&self) -> *mut u8 {
        self.mmio_base as *mut u8
    }

    pub fn readl(&self, offset: usize) -> Result<u32> {
        if offset >= self.mmio_size {
            return Err(E810Error::InvalidBar);
        }
        unsafe {
            let addr = self.base_ptr().add(offset) as *const u32;
            compiler_fence(Ordering::SeqCst);
            let v = core::ptr::read_volatile(addr);
            compiler_fence(Ordering::SeqCst);
            Ok(u32::from_le(v))
        }
    }

    pub fn writel(&mut self, offset: usize, val: u32) -> Result<()> {
        if offset >= self.mmio_size {
            return Err(E810Error::InvalidBar);
        }
        unsafe {
            let addr = self.base_ptr().add(offset) as *mut u32;
            compiler_fence(Ordering::SeqCst);
            core::ptr::write_volatile(addr, val.to_le());
            // readback to ensure posted write
            let _ = core::ptr::read_volatile(addr);
            compiler_fence(Ordering::SeqCst);
            Ok(())
        }
    }

    pub fn poll<F, P>(&self, mut read_fn: F, mut predicate: P, mut loops: usize) -> Result<u32>
    where
        F: FnMut() -> Result<u32>,
        P: FnMut(u32) -> bool,
    {
        while loops > 0 {
            let v = read_fn()?;
            if predicate(v) {
                return Ok(v);
            }
            loops -= 1;
            spin_loop();
        }
        Err(E810Error::Timeout)
    }

    /// Disable IRQ0 by writing GLINT_DYN_CTL(0) with WB_ON_ITR (mirrors ICE code).
    pub fn disable_irq0(&mut self) -> Result<()> {
        // Write the "WB on ITR" mask to dynamic control 0 which effectively
        // disables interrupt enabling for that vector in many upstream sequences.
        self.writel(GLINT_DYN_CTL_0, GLINT_DYN_CTL_WB_ON_ITR_M)?;
        // readback to flush
        let _ = self.readl(GLINT_DYN_CTL_0)?;
        Ok(())
    }
}
