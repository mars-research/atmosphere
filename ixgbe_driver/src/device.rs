use crate::constants::*;
use crate::println;
use crate::regs::IxgbeDmaArrayRegs;
use crate::regs::{IxgbeDmaRegs, IxgbeNonDmaRegs};
use crate::regs::{IxgbeNoDmaArrayRegs, IxgbeRegs};
use alloc::boxed::Box;
use alloc::collections::VecDeque;
use alloc::format;
use alloc::vec::Vec;
use core::cell::UnsafeCell;
use core::{fmt, mem, ptr};
use libdma::ixgbe::{allocate_dma, ixgbe_adv_rx_desc, ixgbe_adv_tx_desc, ixgbe_adv_tx_desc_read};
use libdma::Dma;
use libtime::sys_ns_loopsleep;
use pcid::utils::PciBarAddr;

use ring_buffer::*;

const PACKET_SIZE: usize = 60;
const TX_CLEAN_BATCH: usize = 32;

const IXGBE_SRRCTL_DESCTYPE_MASK: u64 = 0x0E000000;
const IXGBE_SRRCTL_DESCTYPE_ADV_ONEBUF: u64 = 0x02000000;
const IXGBE_SRRCTL_DROP_EN: u64 = 0x10000000;

const IXGBE_RXD_STAT_DD: u32 = 0x01; /* Descriptor Done */
const IXGBE_RXD_STAT_EOP: u32 = 0x02; /* End of Packet */
const IXGBE_RXDADV_STAT_DD: u32 = IXGBE_RXD_STAT_DD; /* Done */
const IXGBE_RXDADV_STAT_EOP: u32 = IXGBE_RXD_STAT_EOP; /* End of Packet */

const IXGBE_ADVTXD_PAYLEN_SHIFT: u32 = 14; /* Adv desc PAYLEN shift */
const IXGBE_TXD_CMD_EOP: u32 = 0x01000000; /* End of Packet */
const IXGBE_ADVTXD_DCMD_EOP: u32 = IXGBE_TXD_CMD_EOP; /* End of Packet */
const IXGBE_TXD_CMD_RS: u32 = 0x08000000; /* Report Status */
const IXGBE_ADVTXD_DCMD_RS: u32 = IXGBE_TXD_CMD_RS; /* Report Status */
const IXGBE_TXD_CMD_IFCS: u32 = 0x02000000; /* Insert FCS (Ethernet CRC) */
const IXGBE_ADVTXD_DCMD_IFCS: u32 = IXGBE_TXD_CMD_IFCS; /* Insert FCS */
const IXGBE_TXD_CMD_DEXT: u32 = 0x20000000; /* Desc extension (0 = legacy) */
const IXGBE_ADVTXD_DTYP_DATA: u32 = 0x00300000; /* Adv Data Descriptor */
const IXGBE_ADVTXD_DCMD_DEXT: u32 = IXGBE_TXD_CMD_DEXT; /* Desc ext 1=Adv */
const IXGBE_TXD_STAT_DD: u32 = 0x00000001; /* Descriptor Done */
const IXGBE_ADVTXD_STAT_DD: u32 = IXGBE_TXD_STAT_DD; /* Descriptor Done */

const IXGBE_TXPBSIZE_40KB: u64 = 0x0000A000; /* 40KB Packet Buffer */
const IXGBE_RXPBSIZE_128KB: u64 = 0x00020000; /* 128KB Packet Buffer */
const IXGBE_RXDCTL_ENABLE: u64 = 0x02000000; /* Ena specific Rx Queue */
const IXGBE_TXDCTL_ENABLE: u64 = 0x02000000; /* Ena specific Tx Queue */

const ONE_MS_IN_NS: u64 = 1_000_000 * 1;

const NUM_TX_DESCS: usize = 256;
const NUM_RX_DESCS: usize = 256;

pub struct NetworkStats {
    pub tx_count: u64,
    pub rx_count: u64,
    pub tx_dma_ok: u64,
    pub rx_dma_ok: u64,
    pub rx_missed: u64,
    pub rx_crc_err: u64,
}

impl NetworkStats {
    pub fn new() -> Self {
        Self {
            tx_count: 0,
            rx_count: 0,
            tx_dma_ok: 0,
            rx_dma_ok: 0,
            rx_missed: 0,
            rx_crc_err: 0,
        }
    }

    pub fn stats_diff(&mut self, start: NetworkStats) {
        self.tx_count.saturating_sub(start.tx_count);
        self.rx_count.saturating_sub(start.rx_count);
        self.tx_dma_ok.saturating_sub(start.tx_dma_ok);
        self.rx_dma_ok.saturating_sub(start.rx_dma_ok);
        self.rx_missed.saturating_sub(start.rx_missed);
        self.rx_crc_err.saturating_sub(start.rx_crc_err);
    }
}

impl fmt::Display for NetworkStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "=> Tx stats: Count: {} dma_OK: {}\n",
            self.tx_count, self.tx_dma_ok
        );
        write!(
            f,
            "=> Rx stats: Count: {} dma_OK: {} missed: {} crc_err: {}",
            self.rx_count, self.rx_dma_ok, self.rx_missed, self.rx_crc_err
        )
    }
}

pub struct IxgbeDevice {
    //pub bar: Box<dyn IxgbeBarRegion>,
    bar: PciBarAddr,
    transmit_buffers: [Option<Vec<u8>>; NUM_TX_DESCS],
    transmit_addrs: [Option<IxgbePayLoad>; NUM_TX_DESCS],
    //transmit_rrefs: [Option<RRef<[u8; 1514]>>; NUM_TX_DESCS],
    transmit_buffers_tup: [Option<(Vec<u8>, u64)>; NUM_TX_DESCS],
    transmit_ring: Dma<[ixgbe_adv_tx_desc; NUM_TX_DESCS]>,
    receive_buffers: [Option<Vec<u8>>; NUM_RX_DESCS],
    receive_addrs: [Option<IxgbePayLoad>; NUM_RX_DESCS],
    receive_buffers_tup: [Option<(Vec<u8>, u64)>; NUM_RX_DESCS],
    //receive_rrefs: [Option<RRef<[u8; 1514]>>; NUM_TX_DESCS],
    receive_ring: Dma<[ixgbe_adv_rx_desc; NUM_RX_DESCS]>,
    tx_slot: [bool; NUM_TX_DESCS],
    rx_slot: [bool; NUM_RX_DESCS],
    transmit_index: usize,
    transmit_clean_index: usize,
    rx_clean_index: usize,
    tx_clean_index: usize,
    receive_index: usize,
    regs: IxgbeDmaRegs,
    pub nd_regs: IxgbeNonDmaRegs,
    dump: bool,
    rx_dump: bool,
}

fn wrap_ring(index: usize, ring_size: usize) -> usize {
    (index + 1) & (ring_size - 1)
}

impl IxgbeDevice {
    pub fn new(bar: PciBarAddr) -> IxgbeDevice {
        IxgbeDevice {
            bar,
            transmit_buffers: array_init::array_init(|_| None),
            transmit_addrs: array_init::array_init(|_| None),
            //transmit_rrefs: array_init::array_init(|_| None),
            transmit_buffers_tup: array_init::array_init(|_| None),
            //receive_rrefs: array_init::array_init(|_| None),
            receive_buffers: array_init::array_init(|_| None),
            receive_addrs: array_init::array_init(|_| None),
            //receive_rrefs: array_init::array_init(|_| None),
            receive_buffers_tup: array_init::array_init(|_| None),
            transmit_index: 0,
            transmit_clean_index: 0,
            rx_clean_index: 0,
            tx_clean_index: 0,
            receive_index: 0,
            tx_slot: [false; NUM_TX_DESCS],
            rx_slot: [false; NUM_RX_DESCS],
            receive_ring: allocate_dma().unwrap(),
            transmit_ring: allocate_dma().unwrap(),
            regs: unsafe { IxgbeDmaRegs::new(bar) },
            nd_regs: unsafe { IxgbeNonDmaRegs::new(bar) },
            dump: false,
            rx_dump: false,
        }
    }

    /// Clear all interrupt masks for all queues.
    fn clear_interrupts(&self) {
        // Clear interrupt mask
        self.write_reg(IxgbeRegs::EIMC, IXGBE_IRQ_CLEAR_MASK);
        self.read_reg(IxgbeRegs::EICR);
    }

    /// Disable all interrupts for all queues.
    fn disable_interrupts(&self) {
        // Clear interrupt mask to stop from interrupts being generated
        self.write_reg(IxgbeRegs::EIMS, 0x0000_0000);
        self.clear_interrupts();
    }

    /// Resets and initializes an ixgbe device.
    pub fn init(&mut self) {
        println!("Disable irqs");
        self.disable_interrupts();

        println!("Writing regs");
        self.write_reg(IxgbeRegs::CTRL, IXGBE_CTRL_PCIE_MASTER_DISABLE);
        println!("CTRL <- {:#010x}", IXGBE_CTRL_PCIE_MASTER_DISABLE);

        self.wait_clear_reg(IxgbeRegs::STATUS, IXGBE_STATUS_PCIE_MASTER_STATUS);

        // section 4.6.3.2
        self.write_reg(IxgbeRegs::CTRL, IXGBE_CTRL_RST_MASK);

        self.wait_clear_reg(IxgbeRegs::CTRL, IXGBE_CTRL_RST_MASK);
        println!("Sleep");
        sys_ns_loopsleep(ONE_MS_IN_NS * 100);

        println!("resume after Sleep");
        // section 4.6.3.1 - disable interrupts again after reset
        self.disable_interrupts();

        println!("No snoop disable bit");
        // check for no snoop disable bit
        let ctrl_ext = self.read_reg(IxgbeRegs::CTRL_EXT);
        if (ctrl_ext & IXGBE_CTRL_EXT_NS_DIS) == 0 {
            self.write_reg(IxgbeRegs::CTRL_EXT, ctrl_ext | IXGBE_CTRL_EXT_NS_DIS);
        }
        self.write_reg(IxgbeRegs::CTRL_EXT, IXGBE_CTRL_EXT_DRV_LOAD);

        self.write_reg(IxgbeRegs::CTRL_EXT, IXGBE_CTRL_EXT_DRV_LOAD);

        let mac = self.get_mac_addr();

        println!("initializing device");
        println!(
            "   - MAC: {:>02X}:{:>02X}:{:>02X}:{:>02X}:{:>02X}:{:>02X}",
            mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]
        );

        /*
        let _ = setcfg(
            "mac",
            &format!(
                "{:>02X}-{:>02X}-{:>02X}-{:>02X}-{:>02X}-{:>02X}\n",
                mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]
            ),
        );*/

        // section 4.6.3 - wait for EEPROM auto read completion
        self.wait_write_reg(IxgbeRegs::EEC, IXGBE_EEC_ARD);

        // section 4.6.3 - wait for dma initialization done
        self.wait_write_reg(IxgbeRegs::RDRXCTL, IXGBE_RDRXCTL_DMAIDONE);

        // section 4.6.4 - initialize link (auto negotiation)
        self.init_link();

        // section 4.6.5 - statistical counters
        // reset-on-read registers, just read them once
        self.reset_stats();

        // section 4.6.7 - init rx
        self.init_rx();

        // section 4.6.8 - init tx
        self.init_tx();

        // start a single receive queue/ring
        self.start_rx_queue(0);

        // start a single transmit queue/ring
        self.start_tx_queue(0);

        // section 4.6.3.9 - enable interrupts
        //self.enable_msix_interrupt(0);

        // enable promisc mode by default to make testing easier
        self.set_promisc(true);

        // wait some time for the link to come up
        self.wait_for_link();

        self.dump_all_regs();

        // sleep for 10 seconds. Just stabilize the hardware
        // Well. this ugliness costed us two days of debugging.
        println!("Sleep for 15 seconds");
        sys_ns_loopsleep(ONE_MS_IN_NS * 1000 * 3);
        println!("Resuming sleep");
    }

    /// Returns the mac address of this device.
    pub fn get_mac_addr(&self) -> [u8; 6] {
        let low = self.read_reg_idx(IxgbeNoDmaArrayRegs::Ral, 0);
        let high = self.read_reg_idx(IxgbeNoDmaArrayRegs::Rah, 0);

        [
            (low & 0xff) as u8,
            (low >> 8 & 0xff) as u8,
            (low >> 16 & 0xff) as u8,
            (low >> 24) as u8,
            (high & 0xff) as u8,
            (high >> 8 & 0xff) as u8,
        ]
    }

    /// Sets the mac address of this device.
    #[allow(dead_code)]
    pub fn set_mac_addr(&self, mac: [u8; 6]) {
        let low: u32 = u32::from(mac[0])
            + (u32::from(mac[1]) << 8)
            + (u32::from(mac[2]) << 16)
            + (u32::from(mac[3]) << 24);
        let high: u32 = u32::from(mac[4]) + (u32::from(mac[5]) << 8);

        self.write_reg_idx(IxgbeNoDmaArrayRegs::Ral, 0, low as u64);
        self.write_reg_idx(IxgbeNoDmaArrayRegs::Rah, 0, high as u64);
    }

    // see section 4.6.4
    /// Initializes the link of this device.
    fn init_link(&self) {
        // link auto-configuration register should already be set correctly, we're resetting it anyway
        self.write_reg(
            IxgbeRegs::AUTOC,
            (self.read_reg(IxgbeRegs::AUTOC) & !IXGBE_AUTOC_LMS_MASK) | IXGBE_AUTOC_LMS_10G_SERIAL,
        );
        self.write_reg(
            IxgbeRegs::AUTOC,
            (self.read_reg(IxgbeRegs::AUTOC) & !IXGBE_AUTOC_10G_PMA_PMD_MASK)
                | IXGBE_AUTOC_10G_XAUI,
        );
        // negotiate link
        self.write_flag(IxgbeRegs::AUTOC, IXGBE_AUTOC_AN_RESTART);
        // datasheet wants us to wait for the link here, but we can continue and wait afterwards
    }

    /// Resets the stats of this device.
    fn reset_stats(&self) {
        self.read_reg(IxgbeRegs::GPRC);
        self.read_reg(IxgbeRegs::GPTC);
        self.read_reg(IxgbeRegs::GORCL);
        self.read_reg(IxgbeRegs::GORCH);
        self.read_reg(IxgbeRegs::GOTCL);
        self.read_reg(IxgbeRegs::GOTCH);
    }

    // sections 4.6.7
    /// Initializes the rx queues of this device.
    fn init_rx(&mut self) {
        // disable rx while re-configuring it
        self.clear_flag(IxgbeRegs::RXCTRL, IXGBE_RXCTRL_RXEN);

        // enable CRC offloading
        self.write_flag(IxgbeRegs::HLREG0, IXGBE_HLREG0_RXCRCSTRP);
        self.write_flag(IxgbeRegs::RDRXCTL, IXGBE_RDRXCTL_CRCSTRIP);

        // accept broadcast packets
        self.write_flag(IxgbeRegs::FCTRL, IXGBE_FCTRL_BAM);

        // configure a single receive queue/ring
        let _i: u64 = 0;

        // TODO: Manipulation of rx queue. Move this to trusted part
        self.init_rx_inner();

        // last sentence of section 4.6.7 - set some magic bits
        self.write_flag(IxgbeRegs::CTRL_EXT, IXGBE_CTRL_EXT_NS_DIS);

        // start rx
        self.write_flag(IxgbeRegs::RXCTRL, IXGBE_RXCTRL_RXEN);
    }

    fn enable_loopback(&self) {
        self.write_flag(IxgbeRegs::HLREG0, IXGBE_HLREG0_LPBK);
    }

    // section 4.6.8
    /// Initializes the tx queues of this device.
    fn init_tx(&mut self) {
        // crc offload and small packet padding
        self.write_flag(
            IxgbeRegs::HLREG0,
            IXGBE_HLREG0_TXCRCEN | IXGBE_HLREG0_TXPADEN,
        );

        // required when not using DCB/VTd
        self.write_reg(IxgbeRegs::DTXMXSZRQ, 0xffff);
        self.clear_flag(IxgbeRegs::RTTDCS, IXGBE_RTTDCS_ARBDIS);

        // configure a single transmit queue/ring
        let _i: u64 = 0;

        // section 7.1.9 - setup descriptor ring

        self.init_tx_inner();

        // final step: enable DMA
        self.write_reg(IxgbeRegs::DMATXCTL, IXGBE_DMATXCTL_TE);
    }

    /// Returns the link speed of this device.
    fn get_link_speed(&self) -> u16 {
        let speed = self.read_reg(IxgbeRegs::LINKS);
        if (speed & IXGBE_LINKS_UP) == 0 {
            return 0;
        }
        match speed & IXGBE_LINKS_SPEED_82599 {
            IXGBE_LINKS_SPEED_100_82599 => 100,
            IXGBE_LINKS_SPEED_1G_82599 => 1000,
            IXGBE_LINKS_SPEED_10G_82599 => 10000,
            _ => 0,
        }
    }

    /// Enables or disables promisc mode of this device.
    fn set_promisc(&self, enabled: bool) {
        if enabled {
            self.write_flag(IxgbeRegs::FCTRL, IXGBE_FCTRL_MPE | IXGBE_FCTRL_UPE);
        } else {
            self.clear_flag(IxgbeRegs::FCTRL, IXGBE_FCTRL_MPE | IXGBE_FCTRL_UPE);
        }
    }

    /// Waits for the link to come up.
    fn wait_for_link(&self) {
        println!("   - waiting for link");
        let mut speed = self.get_link_speed();
        let mut count = 0;
        while speed == 0 && count < 100 {
            count += 1;
            sys_ns_loopsleep(ONE_MS_IN_NS * 100);
            speed = self.get_link_speed();
        }
        println!("   - link speed is {} Mbit/s", self.get_link_speed());
    }

    pub fn dump_stats(&self) {
        println!("Ixgbe statistics:");
        let mut string = format!(
            "Stats regs:\n\tGPRC {:08X} GPTC {:08X}\n \
                                 \tGORCL {:08X} GORCH {:08X}\n \
                                 \tGOTCL {:08X} GOTCH {:08X}\n \
                                 \tTXDGPC {:08X} TXDGBCH {:08X} TXDGBCL {:08X} QPTC(0) {:08X}\n \
                                 \t MPTC {:08X} BPTC {:08X}\n",
            self.read_reg(IxgbeRegs::GPRC) as u32,
            self.read_reg(IxgbeRegs::GPTC) as u32,
            self.read_reg(IxgbeRegs::GORCL) as u32,
            self.read_reg(IxgbeRegs::GORCH) as u32,
            self.read_reg(IxgbeRegs::GOTCL) as u32,
            self.read_reg(IxgbeRegs::GOTCH) as u32,
            self.read_reg(IxgbeRegs::TXDGPC) as u32,
            self.read_reg(IxgbeRegs::TXDGBCH) as u32,
            self.read_reg(IxgbeRegs::TXDGBCL) as u32,
            self.read_reg_idx(IxgbeNoDmaArrayRegs::Qptc, 0) as u32,
            self.read_reg(IxgbeRegs::MPTC) as u32,
            self.read_reg(IxgbeRegs::BPTC) as u32,
        );

        string.push_str(&format!(
            "CRCERRS {:08X} ILLERRC {:08X} ERRBC {:08X}\n \
                                    \tMLFC {:08X} MRFC {:08X} RXMPC[0] {:08X}\n \
                                    \tRLEC {:08X} LXONRXCNT {:08X} LXONRXCNT {:08X}\n \
                                    \tRXDGPC {:08X} RXDGBCL {:08X} RXDGBCH {:08X}\n \
                                    \tRUC {:08X} RFC {:08X} ROC {:08X}\n \
                                    \tRJC {:08X} BPRC {:08X} MPRC {:08X}\n",
            self.read_reg(IxgbeRegs::CRCERRS) as u32,
            self.read_reg(IxgbeRegs::ILLERRC) as u32,
            self.read_reg(IxgbeRegs::ERRBC) as u32,
            self.read_reg(IxgbeRegs::MLFC) as u32,
            self.read_reg(IxgbeRegs::MRFC) as u32,
            self.read_reg_idx(IxgbeNoDmaArrayRegs::Rxmpc, 0) as u32,
            self.read_reg(IxgbeRegs::RLEC) as u32,
            self.read_reg(IxgbeRegs::LXONRXCNT) as u32,
            self.read_reg(IxgbeRegs::LXOFFRXCNT) as u32,
            self.read_reg(IxgbeRegs::RXDGPC) as u32,
            self.read_reg(IxgbeRegs::RXDGBCH) as u32,
            self.read_reg(IxgbeRegs::RXDGBCL) as u32,
            self.read_reg(IxgbeRegs::RUC) as u32,
            self.read_reg(IxgbeRegs::RFC) as u32,
            self.read_reg(IxgbeRegs::ROC) as u32,
            self.read_reg(IxgbeRegs::RJC) as u32,
            self.read_reg(IxgbeRegs::BPRC) as u32,
            self.read_reg(IxgbeRegs::MPRC) as u32,
        ));
        println!("{}", string);
    }

    pub fn dump_all_regs(&self) {
        let mut string = format!(
            "Interrupt regs:\n\tEICR: {:08X} EIMS: {:08X} EIMC: {:08X}\n\tGPIE {:08X}\n",
            self.read_reg(IxgbeRegs::EICR) as u32,
            self.read_reg(IxgbeRegs::EIMS) as u32,
            self.read_reg(IxgbeRegs::EIMC) as u32,
            self.read_reg(IxgbeRegs::GPIE) as u32,
        );

        string.push_str(&format!(
            "Control regs:\n\tCTRL {:08X} CTRL_EXT {:08X}\n",
            self.read_reg(IxgbeRegs::CTRL) as u32,
            self.read_reg(IxgbeRegs::CTRL_EXT) as u32,
        ));

        string.push_str(&format!(
            "EEPROM regs:\n\tEEC_ARD {:08X}\n",
            self.read_reg(IxgbeRegs::EEC) as u32
        ));

        string.push_str(&format!(
            "AUTOC {:08X}\n",
            self.read_reg(IxgbeRegs::AUTOC) as u32
        ));

        string.push_str(&format!(
            "Receive regs:\n\tRDRXCTRL {:08X} RXCTRL {:08X}\n\tHLREG0 {:08X} FCTRL {:08X}\n",
            self.read_reg(IxgbeRegs::RDRXCTL) as u32,
            self.read_reg(IxgbeRegs::RXCTRL) as u32,
            self.read_reg(IxgbeRegs::HLREG0) as u32,
            self.read_reg(IxgbeRegs::FCTRL) as u32,
        ));

        string.push_str(&format!(
            "Transmit regs:\n\tDTXMSSZRQ {:08X} RTTDCS {:08X} DMATXCTL: {:08X}\n",
            self.read_reg(IxgbeRegs::DTXMXSZRQ) as u32,
            self.read_reg(IxgbeRegs::RTTDCS) as u32,
            self.read_reg(IxgbeRegs::DMATXCTL) as u32,
        ));
        string.push_str(&format!("Stats regs:\n\tGPRC {:08X} GPTC {:08X}\n\tGORCL {:08X} GORCH {:08X}\n\tGOTCL {:08X} GOTCH {:08X}\n\tTXDGPC {:08X} TXDGBCH {:08X} TXDGBCL {:08X} QPTC(0) {:08X}\n",
                                self.read_reg(IxgbeRegs::GPRC) as u32,
                                self.read_reg(IxgbeRegs::GPTC) as u32,
                                self.read_reg(IxgbeRegs::GORCL) as u32,
                                self.read_reg(IxgbeRegs::GORCH) as u32,
                                self.read_reg(IxgbeRegs::GOTCL) as u32,
                                self.read_reg(IxgbeRegs::GOTCH) as u32,
                                self.read_reg(IxgbeRegs::TXDGPC) as u32,
                                self.read_reg(IxgbeRegs::TXDGBCH) as u32,
                                self.read_reg(IxgbeRegs::TXDGBCL) as u32,
                                self.read_reg_idx(IxgbeNoDmaArrayRegs::Qptc, 0) as u32,
                                ));
        println!("{}", string);

        self.dump_dma_regs();

        self.dump_stats();
    }

    pub fn get_stats(&self) -> NetworkStats {
        NetworkStats {
            tx_count: self.read_reg(IxgbeRegs::GPTC),
            rx_count: self.read_reg(IxgbeRegs::GPRC),
            tx_dma_ok: self.read_reg(IxgbeRegs::TXDGPC),
            rx_dma_ok: self.read_reg(IxgbeRegs::RXDGPC),
            rx_missed: self.read_reg_idx(IxgbeNoDmaArrayRegs::Rxmpc, 0),
            rx_crc_err: self.read_reg(IxgbeRegs::CRCERRS),
        }
    }
    pub fn read_reg(&self, reg: IxgbeRegs) -> u64 {
        unsafe {
            ptr::read_volatile((self.bar.get_base() as u64 + reg as u64) as *const u32) as u64
                & 0xFFFF_FFFFu64
        }
    }

    pub fn write_reg(&self, reg: IxgbeRegs, val: u64) {
        unsafe {
            log::trace!("writing to {:x}", (self.bar.get_base() as u64 + reg as u64));
            ptr::write_volatile(
                (self.bar.get_base() as u64 + reg as u64) as *mut u32,
                val as u32,
            );
        }
    }

    fn read_reg_idx(&self, register: IxgbeNoDmaArrayRegs, idx: u64) -> u64 {
        self.nd_regs.read_reg_idx(register, idx)
    }

    fn write_reg_idx(&self, register: IxgbeNoDmaArrayRegs, idx: u64, value: u64) {
        self.nd_regs.write_reg_idx(register, idx, value);
    }

    fn wait_clear_reg(&self, register: IxgbeRegs, value: u64) {
        loop {
            println!("Waiting for {:?} bit {:x} to clear/set", register, value);
            let current = self.read_reg(register);
            if (current & value) == 0 {
                break;
            }
            sys_ns_loopsleep(ONE_MS_IN_NS * 100);
        }
    }

    fn wait_write_reg(&self, register: IxgbeRegs, value: u64) {
        loop {
            let current = self.read_reg(register);
            if (current & value) == value {
                break;
            }
            sys_ns_loopsleep(ONE_MS_IN_NS * 100);
        }
    }

    fn write_flag(&self, register: IxgbeRegs, flags: u64) {
        self.write_reg(register, self.read_reg(register) | flags);
    }

    fn clear_flag(&self, register: IxgbeRegs, flags: u64) {
        self.write_reg(register, self.read_reg(register) & !flags);
    }

    fn read_qreg_idx(&self, reg: IxgbeDmaArrayRegs, idx: u64) -> u64 {
        self.regs.read_reg_idx(reg, idx)
    }

    fn write_qreg_idx(&self, reg: IxgbeDmaArrayRegs, idx: u64, val: u64) {
        self.regs.write_reg_idx(reg, idx, val);
    }

    fn write_qflag_idx(&self, register: IxgbeDmaArrayRegs, idx: u64, flags: u64) {
        self.write_qreg_idx(register, idx, self.read_qreg_idx(register, idx) | flags);
    }

    fn wait_write_qreg_idx(&self, register: IxgbeDmaArrayRegs, idx: u64, value: u64) {
        loop {
            let current = self.read_qreg_idx(register, idx);
            if (current & value) == value {
                break;
            }
            sys_ns_loopsleep(ONE_MS_IN_NS * 100);
        }
    }

    fn clear_qflag_idx(&self, register: IxgbeDmaArrayRegs, idx: u64, flags: u64) {
        self.write_qreg_idx(register, idx, self.read_qreg_idx(register, idx) & !flags);
    }

    pub fn start_rx_queue(&self, queue_id: u16) {
        // enable queue and wait if necessary
        self.write_qflag_idx(
            IxgbeDmaArrayRegs::Rxdctl,
            u64::from(queue_id),
            IXGBE_RXDCTL_ENABLE,
        );
        self.wait_write_qreg_idx(
            IxgbeDmaArrayRegs::Rxdctl,
            u64::from(queue_id),
            IXGBE_RXDCTL_ENABLE,
        );

        // rx queue starts out full
        self.write_qreg_idx(IxgbeDmaArrayRegs::Rdh, u64::from(queue_id), 0);
        self.write_qreg_idx(IxgbeDmaArrayRegs::Rdt, u64::from(queue_id), 0);
    }

    pub fn start_tx_queue(&self, queue_id: u16) {
        self.write_qreg_idx(IxgbeDmaArrayRegs::Tdh, u64::from(queue_id), 0);
        self.write_qreg_idx(IxgbeDmaArrayRegs::Tdt, u64::from(queue_id), 0);

        // enable queue and wait if necessary
        self.write_qflag_idx(
            IxgbeDmaArrayRegs::Txdctl,
            u64::from(queue_id),
            IXGBE_TXDCTL_ENABLE,
        );
        self.wait_write_qreg_idx(
            IxgbeDmaArrayRegs::Txdctl,
            u64::from(queue_id),
            IXGBE_TXDCTL_ENABLE,
        );
    }

    pub fn init_rx_inner(&self) {
        let i: u64 = 0;

        // probably a broken feature, this flag is initialized with 1 but has to be set to 0
        self.clear_qflag_idx(IxgbeDmaArrayRegs::DcaRxctrl, i, 1 << 12);

        // section 4.6.11.3.4 - allocate all queues and traffic to PB0
        self.write_qreg_idx(IxgbeDmaArrayRegs::Rxpbsize, 0, IXGBE_RXPBSIZE_128KB);

        for i in 1..8 {
            self.write_qreg_idx(IxgbeDmaArrayRegs::Rxpbsize, i, 0);
        }

        self.write_qreg_idx(
            IxgbeDmaArrayRegs::Srrctl,
            i,
            (self.read_qreg_idx(IxgbeDmaArrayRegs::Srrctl, i) & !IXGBE_SRRCTL_DESCTYPE_MASK)
                | IXGBE_SRRCTL_DESCTYPE_ADV_ONEBUF,
        );

        // let nic drop packets if no rx descriptor is available instead of buffering them
        self.write_qreg_idx(
            IxgbeDmaArrayRegs::Srrctl,
            i,
            self.read_qreg_idx(IxgbeDmaArrayRegs::Srrctl, i) | IXGBE_SRRCTL_DROP_EN,
        );

        self.write_qreg_idx(
            IxgbeDmaArrayRegs::Rdbal,
            i,
            (self.receive_ring.physical() & 0xffff_ffff) as u64,
        );

        self.write_qreg_idx(
            IxgbeDmaArrayRegs::Rdbah,
            i,
            (self.receive_ring.physical() >> 32) as u64,
        );

        println!(
            "rx ring {} phys addr: {:#x}",
            i,
            self.receive_ring.physical()
        );

        self.write_qreg_idx(
            IxgbeDmaArrayRegs::Rdlen,
            i,
            (self.receive_ring.len() * mem::size_of::<ixgbe_adv_rx_desc>()) as u64,
        );
    }

    pub fn init_tx_inner(&self) {
        let i: u64 = 0;

        // section 4.6.11.3.4 - set default buffer size allocations
        self.write_qreg_idx(IxgbeDmaArrayRegs::Txpbsize, 0, IXGBE_TXPBSIZE_40KB);
        for i in 1..8 {
            self.write_qreg_idx(IxgbeDmaArrayRegs::Txpbsize, i, 0);
        }

        self.write_qreg_idx(IxgbeDmaArrayRegs::TxpbThresh, 0, 0xA0);

        for i in 1..8 {
            self.write_qreg_idx(IxgbeDmaArrayRegs::TxpbThresh, i, 0);
        }

        self.write_qreg_idx(
            IxgbeDmaArrayRegs::Tdbal,
            i,
            self.transmit_ring.physical() as u64,
        );
        self.write_qreg_idx(
            IxgbeDmaArrayRegs::Tdbah,
            i,
            (self.transmit_ring.physical() >> 32) as u64,
        );

        println!(
            "tx ring {} phys addr: {:#x}",
            i,
            self.transmit_ring.physical()
        );
        self.write_qreg_idx(
            IxgbeDmaArrayRegs::Tdlen,
            i,
            (self.transmit_ring.len() * mem::size_of::<ixgbe_adv_tx_desc>()) as u64,
        );

        // descriptor writeback magic values, important to get good performance and low PCIe overhead
        // see 7.2.3.4.1 and 7.2.3.5 for an explanation of these values and how to find good ones
        // we just use the defaults from DPDK here, but this is a potentially interesting point for optimizations
        //let mut txdctl = self.read_reg_idx(IxgbeArrayRegs::Txdctl, i);
        // there are no defines for this in ixgbe.rs for some reason
        // pthresh: 6:0, hthresh: 14:8, wthresh: 22:16
        //txdctl &= !(0x3F | (0x3F << 8) | (0x3F << 16));
        //txdctl |= 36 | (8 << 8) | (4 << 16);

        let mut txdctl = 0;
        txdctl |= 8 << 16;

        txdctl |= (1 << 8) | 32;

        self.write_qreg_idx(IxgbeDmaArrayRegs::Txdctl, i, txdctl);
    }

    fn clean_tx_queue(&mut self) -> usize {
        let mut clean_index = self.transmit_clean_index;
        let cur_index = self.transmit_index;

        loop {
            let mut cleanable = cur_index as i32 - clean_index as i32;
            let num_descriptors = self.transmit_ring.len();

            if cleanable < 0 {
                cleanable += num_descriptors as i32;
            }

            if cleanable < TX_CLEAN_BATCH as i32 {
                break;
            }

            let mut cleanup_to = clean_index + TX_CLEAN_BATCH - 1;

            if cleanup_to >= num_descriptors {
                cleanup_to -= num_descriptors;
            }

            let status = unsafe {
                core::ptr::read_volatile(
                    &(*self.transmit_ring.as_ptr().add(clean_index)).wb.status as *const u32,
                )
            };

            if (status & IXGBE_ADVTXD_STAT_DD) != 0 {
                clean_index = wrap_ring(clean_index, num_descriptors);
            } else {
                break;
            }
        }

        self.transmit_clean_index = clean_index;

        clean_index
    }

    pub fn submit(&mut self, packets: &mut VecDeque<Vec<u8>>) -> usize {
        let mut sent = 0;
        let mut cur_index = self.transmit_index;
        let clean_index = self.clean_tx_queue();
        let num_descriptors = self.transmit_ring.len();

        while let Some(packet) = packets.pop_front() {
            let next_index = wrap_ring(cur_index, num_descriptors);

            if clean_index == next_index {
                // tx queue of device is full, push packet back onto the
                // queue of to-be-sent packets
                packets.push_front(packet);
                break;
            }

            self.transmit_index = wrap_ring(self.transmit_index, num_descriptors);

            let pkt_len = packet.len();

            unsafe {
                self.transmit_ring[cur_index].read.buffer_addr = packet.as_ptr() as u64;
                let mut buf_addr: UnsafeCell<*mut u64> = UnsafeCell::new(
                    &(*self.transmit_ring.as_ptr().add(cur_index))
                        .read
                        .buffer_addr as *const u64 as *mut u64,
                );

                core::ptr::write_volatile(*buf_addr.get_mut(), packet.as_ptr() as u64);

                self.transmit_buffers[cur_index] = Some(packet);
                self.tx_slot[cur_index] = true;

                let mut cmd_type: UnsafeCell<*mut u32> = UnsafeCell::new(
                    &(*self.transmit_ring.as_ptr().add(cur_index))
                        .read
                        .cmd_type_len as *const u32 as *mut u32,
                );

                core::ptr::write_volatile(
                    *cmd_type.get_mut(),
                    IXGBE_ADVTXD_DCMD_EOP
                        | IXGBE_ADVTXD_DCMD_RS
                        | IXGBE_ADVTXD_DCMD_IFCS
                        | IXGBE_ADVTXD_DCMD_DEXT
                        | IXGBE_ADVTXD_DTYP_DATA
                        | pkt_len as u32,
                );

                let mut olinfo_status: UnsafeCell<*mut u32> = UnsafeCell::new(
                    &(*self.transmit_ring.as_ptr().add(cur_index))
                        .read
                        .olinfo_status as *const u32 as *mut u32,
                );

                core::ptr::write_volatile(
                    *olinfo_status.get_mut(),
                    (pkt_len as u32) << IXGBE_ADVTXD_PAYLEN_SHIFT,
                );
            }

            cur_index = next_index;
            sent += 1;
        }

        if sent > 0 {
            //self.bar.write_reg_tdt(0, self.transmit_index as u64);
            self.write_qreg_idx(IxgbeDmaArrayRegs::Tdt, 0, self.transmit_index as u64);
        }

        sent
    }

    /*pub fn submit_and_poll_rref(
        &mut self,
        mut packets: RRefDeque<[u8; 1514], 32>,
        mut collect: RRefDeque<[u8; 1514], 32>,
        tx: bool,
        pkt_len: usize,
        debug: bool,
    ) -> (usize, RRefDeque<[u8; 1514], 32>, RRefDeque<[u8; 1514], 32>) {
        if tx {
            self.tx_submit_and_poll_rref(packets, collect, pkt_len, debug)
        } else {
            self.rx_submit_and_poll_rref(packets, collect, pkt_len, debug)
        }
    }*/

    pub fn submit_and_poll2(
        &mut self,
        packets: &mut VecDeque<(Vec<u8>, u64)>,
        reap_queue: &mut VecDeque<(Vec<u8>, u64)>,
        tx: bool,
        debug: bool,
    ) -> usize {
        if tx {
            self.tx_submit_and_poll2(packets, reap_queue, debug)
        } else {
            self.rx_submit_and_poll2(packets, reap_queue, debug)
        }
    }

    pub fn submit_and_poll(
        &mut self,
        packets: &mut VecDeque<Vec<u8>>,
        reap_queue: &mut VecDeque<Vec<u8>>,
        tx: bool,
        debug: bool,
    ) -> usize {
        if tx {
            self.tx_submit_and_poll(packets, reap_queue, debug)
        } else {
            self.rx_submit_and_poll(packets, reap_queue, debug)
        }
    }

    pub fn poll(&mut self, reap_queue: &mut VecDeque<Vec<u8>>, tx: bool) -> usize {
        if tx {
            self.tx_poll(reap_queue)
        } else {
            self.rx_poll(reap_queue)
        }
    }

    /*
    pub fn poll_rref(
        &mut self,
        mut reap_queue: RRefDeque<[u8; 1514], 512>,
        tx: bool,
    ) -> (usize, RRefDeque<[u8; 1514], 512>) {
        if tx {
            self.tx_poll_rref(reap_queue)
        } else {
            self.rx_poll_rref(reap_queue)
        }
    }

    fn tx_poll_rref(
        &mut self,
        mut reap_queue: RRefDeque<[u8; 1514], 512>,
    ) -> (usize, RRefDeque<[u8; 1514], 512>) {
        let num_descriptors = self.transmit_ring.len();
        let mut reaped: usize = 0;
        let mut count: usize = 0;
        let mut tx_clean_index: usize = self.tx_clean_index;

        for tx_index in 0..num_descriptors {
            let status = unsafe {
                core::ptr::read_volatile(
                    &(*self.transmit_ring.as_ptr().add(tx_index)).wb.status as *const u32,
                )
            };

            if (status & IXGBE_ADVTXD_STAT_DD) != 0 {
                if self.tx_slot[tx_index] {
                    count += 1;
                    if let Some(mut pkt) = self.transmit_rrefs[tx_index].take() {
                        if reap_queue.push_back(pkt).is_some() {
                            println!("tx_poll_rref: Pushing to full reap queue");
                        }
                    }
                    self.tx_slot[tx_index] = false;
                    self.transmit_rrefs[tx_index] = None;
                    reaped += 1;
                    tx_clean_index = tx_index;
                }
            }
        }
        println!("Found {} sent DDs", count);
        let head = self.read_qreg_idx(IxgbeDmaArrayRegs::Tdh, 0);
        let tail = self.read_qreg_idx(IxgbeDmaArrayRegs::Tdt, 0);

        println!(
            "Tx ring {:16x} len {} HEAD {} TAIL {}\n",
            self.transmit_ring.physical(),
            self.transmit_ring.len(),
            head,
            tail
        );

        if reaped > 0 {
            self.tx_clean_index = self.transmit_index;
        }
        (reaped, reap_queue)
    }

    fn rx_poll_rref(
        &mut self,
        mut reap_queue: RRefDeque<[u8; 1514], 512>,
    ) -> (usize, RRefDeque<[u8; 1514], 512>) {
        let num_descriptors = self.receive_ring.len();
        let mut reaped: usize = 0;
        let mut count: usize = 0;
        let mut rx_clean_index: usize = self.rx_clean_index;

        for rx_index in 0..num_descriptors {
            let mut desc = unsafe {
                &mut *(self.receive_ring.as_ptr().add(rx_index) as *mut ixgbe_adv_rx_desc)
            };

            let status =
                unsafe { core::ptr::read_volatile(&mut (*desc).wb.upper.status_error as *mut u32) };

            if ((status & IXGBE_RXDADV_STAT_DD) != 0) && ((status & IXGBE_RXDADV_STAT_EOP) == 0) {
                panic!("increase buffer size or decrease MTU")
            }

            if (status & IXGBE_RXDADV_STAT_DD) != 0 {
                if self.rx_slot[rx_index] {
                    count += 1;
                    if let Some(mut pkt) = self.receive_rrefs[rx_index].take() {
                        //println!("{}, buffer {:16x}", rx_index, pkt.as_ptr() as u64);

                        let length = unsafe {
                            core::ptr::read_volatile(&(*desc).wb.upper.length as *const u16)
                                as usize
                        };

                        if reap_queue.push_back(pkt).is_some() {
                            println!("rx_poll_rref: Pushing to full reap queue");
                        }
                    }
                    self.rx_slot[rx_index] = false;
                    self.receive_rrefs[rx_index] = None;
                    reaped += 1;
                    rx_clean_index = rx_index;
                }
            }
        }
        println!("Found {} sent DDs", count);

        let head = self.read_qreg_idx(IxgbeDmaArrayRegs::Rdh, 0);
        let tail = self.read_qreg_idx(IxgbeDmaArrayRegs::Rdt, 0);

        println!(
            "rx_index {} rx_clean_index {}\n",
            self.receive_index, self.rx_clean_index
        );
        println!(
            "Rx ring {:16x} len {} HEAD {} TAIL {}\n",
            self.receive_ring.physical(),
            self.receive_ring.len(),
            head,
            tail
        );

        if reaped > 0 {
            println!("update clean index to {}", rx_clean_index);
            self.rx_clean_index = self.receive_index;
        }
        (reaped, reap_queue)
    }*/

    fn tx_poll(&mut self, reap_queue: &mut VecDeque<Vec<u8>>) -> usize {
        let num_descriptors = self.transmit_ring.len();
        let mut reaped: usize = 0;
        let mut count: usize = 0;
        let mut tx_clean_index: usize = self.tx_clean_index;

        for tx_index in 0..num_descriptors {
            let status = unsafe {
                core::ptr::read_volatile(
                    &(*self.transmit_ring.as_ptr().add(tx_index)).wb.status as *const u32,
                )
            };

            if (status & IXGBE_ADVTXD_STAT_DD) != 0 {
                if self.tx_slot[tx_index] {
                    count += 1;
                    if let Some(pkt) = self.transmit_buffers[tx_index].take() {
                        reap_queue.push_front(pkt);
                    }
                    self.tx_slot[tx_index] = false;
                    self.transmit_buffers[tx_index] = None;
                    reaped += 1;
                    tx_clean_index = tx_index;
                }
            }
        }
        println!("Found {} sent DDs", count);
        let head = self.read_qreg_idx(IxgbeDmaArrayRegs::Tdh, 0);
        let tail = self.read_qreg_idx(IxgbeDmaArrayRegs::Tdt, 0);

        println!(
            "Tx ring {:16x} len {} HEAD {} TAIL {}\n",
            self.transmit_ring.physical(),
            self.transmit_ring.len(),
            head,
            tail
        );

        if reaped > 0 {
            self.tx_clean_index = self.transmit_index;
        }
        reaped
    }

    fn rx_poll(&mut self, reap_queue: &mut VecDeque<Vec<u8>>) -> usize {
        let num_descriptors = self.receive_ring.len();
        let mut reaped: usize = 0;
        let mut count: usize = 0;
        let mut rx_clean_index: usize = self.rx_clean_index;

        for rx_index in 0..num_descriptors {
            let mut desc = unsafe {
                &mut *(self.receive_ring.as_ptr().add(rx_index) as *mut ixgbe_adv_rx_desc)
            };

            let status =
                unsafe { core::ptr::read_volatile(&mut (*desc).wb.upper.status_error as *mut u32) };

            if ((status & IXGBE_RXDADV_STAT_DD) != 0) && ((status & IXGBE_RXDADV_STAT_EOP) == 0) {
                panic!("increase buffer size or decrease MTU")
            }

            if (status & IXGBE_RXDADV_STAT_DD) != 0 {
                if self.rx_slot[rx_index] {
                    count += 1;
                    if let Some(mut pkt) = self.receive_buffers[rx_index].take() {
                        //println!("{}, buffer {:16x}", rx_index, pkt.as_ptr() as u64);

                        let length = unsafe {
                            core::ptr::read_volatile(&(*desc).wb.upper.length as *const u16)
                                as usize
                        };

                        //let mut buf = pkt.as_mut_ptr();
                        //let vec = unsafe { Vec::from_raw_parts(buf, length, pkt.capacity()) };
                        unsafe {
                            pkt.set_len(length);
                        }
                        reap_queue.push_front(pkt);
                    }
                    self.rx_slot[rx_index] = false;
                    self.receive_buffers[rx_index] = None;
                    reaped += 1;
                    rx_clean_index = rx_index;
                }
            }
        }
        println!("Found {} rx DDs", count);

        let head = self.read_qreg_idx(IxgbeDmaArrayRegs::Rdh, 0);
        let tail = self.read_qreg_idx(IxgbeDmaArrayRegs::Rdt, 0);

        println!(
            "rx_index {} rx_clean_index {}\n",
            self.receive_index, self.rx_clean_index
        );
        println!(
            "Rx ring {:16x} len {} HEAD {} TAIL {}\n",
            self.receive_ring.physical(),
            self.receive_ring.len(),
            head,
            tail
        );

        if reaped > 0 {
            println!("update clean index to {}", rx_clean_index);
            self.rx_clean_index = self.receive_index;
        }
        reaped
    }

    fn dump_rx_desc(&mut self) {
        println!("=====================\n");
        println!("Rx descriptors\n");
        println!("=====================\n");

        let head = self.read_qreg_idx(IxgbeDmaArrayRegs::Rdh, 0);
        let tail = self.read_qreg_idx(IxgbeDmaArrayRegs::Rdt, 0);

        println!(
            "Rx ring {:16x} len {} HEAD {} TAIL {}\n",
            self.receive_ring.physical(),
            self.receive_ring.len(),
            head,
            tail
        );
        println!(
            "rx_index: {} rx_clean_index {}\n",
            self.receive_index, self.rx_clean_index
        );

        let mut str = format!("[Idx]  [buffer]   [slot]   [status]\n");
        for i in 0..self.receive_ring.len() {
            let mut desc =
                unsafe { &mut *(self.receive_ring.as_ptr().add(i) as *mut ixgbe_adv_rx_desc) };

            let status =
                unsafe { core::ptr::read_volatile(&mut (*desc).wb.upper.status_error as *mut u32) };

            if i == head as usize {
                str.push_str(&format!("H=>"));
            }

            if i == tail as usize {
                str.push_str(&format!("T=>"));
            }

            let mut buffer: u64 = 0;
            if let Some(pkt) = &self.receive_buffers[i] {
                buffer = pkt.as_ptr() as u64;
            }
            str.push_str(&format!(
                "[{}] buffer: {:16x} rx_slot {} status {:x}\n",
                i, buffer, self.rx_slot[i], status
            ));
        }
        println!("{}", str);
        self.rx_dump = true;
    }

    fn dump_tx_desc(&mut self) {
        println!("=====================\n");
        println!("Tx descriptors\n");
        println!("=====================\n");

        let head = self.read_qreg_idx(IxgbeDmaArrayRegs::Tdh, 0);
        let tail = self.read_qreg_idx(IxgbeDmaArrayRegs::Tdt, 0);

        println!(
            "Tx ring {:16x} len {} HEAD {} TAIL {}\n",
            self.transmit_ring.physical(),
            self.transmit_ring.len(),
            head,
            tail
        );

        let mut str = format!("[Idx]  [buffer]   [slot]   [status]\n");
        for i in 0..self.transmit_ring.len() {
            let mut desc =
                unsafe { &mut *(self.transmit_ring.as_ptr().add(i) as *mut ixgbe_adv_tx_desc) };

            let status = unsafe { core::ptr::read_volatile(&mut (*desc).wb.status as *mut u32) };

            if i == head as usize {
                str.push_str(&format!("H=>"));
            }

            if i == tail as usize {
                str.push_str(&format!("T=>"));
            }

            let mut buffer: u64 = 0;
            if let Some(pkt) = &self.transmit_buffers[i] {
                buffer = pkt.as_ptr() as u64;
            }
            str.push_str(&format!(
                "[{}] buffer: {:16x} tx_slot {} status {:x}\n",
                i, buffer, self.tx_slot[i], status
            ));
        }
        println!("{}", str);
        self.dump = true;
    }

    pub fn dump_rx_descs(&mut self) {
        self.dump_rx_desc();
        self.rx_dump = false;
    }

    pub fn dump_tx_descs(&mut self) {
        self.dump_tx_desc();
        self.dump = false;
    }

    #[inline(always)]
    fn tx_submit_and_poll(
        &mut self,
        packets: &mut VecDeque<Vec<u8>>,
        reap_queue: &mut VecDeque<Vec<u8>>,
        debug: bool,
    ) -> usize {
        let mut sent = 0;
        let mut tx_index = self.transmit_index;
        let mut tx_clean_index = self.tx_clean_index;
        let mut last_tx_index = self.transmit_index;
        let num_descriptors = self.transmit_ring.len();
        let BATCH_SIZE = 32;

        if packets.len() > 0 {
            if debug {
                println!("tx index {} packets {}", tx_index, packets.len());
            }
            while let Some(packet) = packets.pop_front() {
                //println!("Found packet!");
                let desc = unsafe {
                    &mut *(self.transmit_ring.as_ptr().add(tx_index) as *mut ixgbe_adv_tx_desc)
                };

                let status =
                    unsafe { core::ptr::read_volatile(&mut (*desc).wb.status as *mut u32) };

                // DD == 0 on a TX desc leaves us with 2 possibilities
                // 1) The desc is populated (tx_slot[i] = true), the device did not sent it out yet
                // 2) The desc is not populated. In that case, tx_slot[i] = false
                if ((status & IXGBE_RXDADV_STAT_DD) == 0) && self.tx_slot[tx_index] {
                    if debug {
                        println!("No free slot. Fucked");
                        if !self.dump {
                            self.dump_tx_desc();
                        }
                    }
                    packets.push_front(packet);
                    break;
                }

                let pkt_len = packet.len();
                if debug {
                    println!("packet len {}", pkt_len);
                }
                unsafe {
                    if self.tx_slot[tx_index] {
                        if let Some(pkt) = self.transmit_buffers[tx_index].take() {
                            reap_queue.push_front(pkt);
                        }

                        tx_clean_index = wrap_ring(tx_clean_index, self.transmit_ring.len());
                    }

                    let mut buf_addr: UnsafeCell<*mut u64> = UnsafeCell::new(
                        &(*self.transmit_ring.as_ptr().add(tx_index))
                            .read
                            .buffer_addr as *const u64 as *mut u64,
                    );

                    use asys::sys_mresolve;
                    let pkt_paddr = sys_mresolve(packet.as_ptr() as usize).0 as u64;

                    log::trace!(
                        "pkt vaddr {:>08x} paddr {:>08x}",
                        packet.as_ptr() as usize,
                        pkt_paddr
                    );

                    // switch to a new buffer
                    core::ptr::write_volatile(*buf_addr.get_mut(), pkt_paddr);

                    self.transmit_buffers[tx_index] = Some(packet);
                    self.tx_slot[tx_index] = true;

                    let mut cmd_type: UnsafeCell<*mut u32> = UnsafeCell::new(
                        &(*self.transmit_ring.as_ptr().add(tx_index))
                            .read
                            .cmd_type_len as *const u32 as *mut u32,
                    );

                    core::ptr::write_volatile(
                        *cmd_type.get_mut(),
                        IXGBE_ADVTXD_DCMD_EOP
                            | IXGBE_ADVTXD_DCMD_RS
                            | IXGBE_ADVTXD_DCMD_IFCS
                            | IXGBE_ADVTXD_DCMD_DEXT
                            | IXGBE_ADVTXD_DTYP_DATA
                            | pkt_len as u32,
                    );

                    let mut olinfo_status: UnsafeCell<*mut u32> = UnsafeCell::new(
                        &(*self.transmit_ring.as_ptr().add(tx_index))
                            .read
                            .olinfo_status as *const u32 as *mut u32,
                    );

                    core::ptr::write_volatile(
                        *olinfo_status.get_mut(),
                        (pkt_len as u32) << IXGBE_ADVTXD_PAYLEN_SHIFT,
                    );
                }

                last_tx_index = tx_index;
                tx_index = wrap_ring(tx_index, self.transmit_ring.len());
                sent += 1;
            }
            if reap_queue.len() < BATCH_SIZE {
                let mut reaped = 0;
                let mut count = 0;
                let batch = BATCH_SIZE - reap_queue.len();

                loop {
                    let status = unsafe {
                        core::ptr::read_volatile(
                            &(*self.transmit_ring.as_ptr().add(tx_clean_index)).wb.status
                                as *const u32,
                        )
                    };

                    if (status & IXGBE_ADVTXD_STAT_DD) != 0 {
                        if self.tx_slot[tx_clean_index] {
                            if let Some(pkt) = self.transmit_buffers[tx_clean_index].take() {
                                reap_queue.push_front(pkt);
                            }
                            self.tx_slot[tx_clean_index] = false;
                            self.transmit_buffers[tx_clean_index] = None;
                            reaped += 1;
                        }
                        tx_clean_index = wrap_ring(tx_clean_index, self.transmit_ring.len());
                    }

                    count += 1;

                    if tx_clean_index == self.transmit_index || count == batch {
                        break;
                    }
                }
                self.tx_clean_index = wrap_ring(tx_clean_index, self.transmit_ring.len());
            }
        }

        if sent > 0 && tx_index == last_tx_index {
            println!("Queued packets, but failed to update idx");
            println!(
                "last_tx_index {} tx_index {} tx_clean_index {}",
                last_tx_index, tx_index, tx_clean_index
            );
        }

        if tx_index != last_tx_index {
            if debug {
                println!(
                    "Update tdt from {} to {}",
                    self.read_qreg_idx(IxgbeDmaArrayRegs::Tdt, 0),
                    tx_index
                );
            }
            //self.bar.write_reg_tdt(0, tx_index as u64);
            self.write_qreg_idx(IxgbeDmaArrayRegs::Tdt, 0, tx_index as u64);
            self.transmit_index = tx_index;
            self.tx_clean_index = tx_clean_index;
        }

        if sent == 0 {
            //println!("Sent {} packets", sent);
        }

        sent
    }

    #[inline(always)]
    fn tx_submit_and_poll2(
        &mut self,
        packets: &mut VecDeque<(Vec<u8>, u64)>,
        reap_queue: &mut VecDeque<(Vec<u8>, u64)>,
        debug: bool,
    ) -> usize {
        let mut sent = 0;
        let mut tx_index = self.transmit_index;
        let mut tx_clean_index = self.tx_clean_index;
        let mut last_tx_index = self.transmit_index;
        let num_descriptors = self.transmit_ring.len();
        let BATCH_SIZE = 32;

        if packets.len() > 0 {
            if debug {
                println!("tx index {} packets {}", tx_index, packets.len());
            }
            while let Some((packet, pkt_paddr)) = packets.pop_front() {
                //println!("Found packet!");
                let mut desc = unsafe {
                    &mut *(self.transmit_ring.as_ptr().add(tx_index) as *mut ixgbe_adv_tx_desc)
                };

                let status =
                    unsafe { core::ptr::read_volatile(&mut (*desc).wb.status as *mut u32) };

                //unsafe {
                //println!("pkt_addr {:08X} tx_Buffer {:08X}",
                //            (*desc).read.pkt_addr as *const u64 as u64,
                //            self.transmit_buffer[tx_index].physical());
                //}

                // DD == 0 on a TX desc leaves us with 2 possibilities
                // 1) The desc is populated (tx_slot[i] = true), the device did not sent it out yet
                // 2) The desc is not populated. In that case, tx_slot[i] = false
                if ((status & IXGBE_RXDADV_STAT_DD) == 0) && self.tx_slot[tx_index] {
                    if debug {
                        println!("No free slot. Fucked");
                        if !self.dump {
                            self.dump_tx_desc();
                        }
                    }
                    packets.push_front((packet, pkt_paddr));
                    break;
                }

                let pkt_len = packet.len();
                if debug {
                    println!("packet len {}", pkt_len);
                }
                unsafe {
                    if self.tx_slot[tx_index] {
                        if let Some(pkt) = self.transmit_buffers[tx_index].take() {
                            //let mut buf = pkt.as_mut_ptr();
                            //let vec = Vec::from_raw_parts(buf, pkt_len, pkt.capacity());
                            /*if debug {
                                println!(
                                    "buf {:x} vec_raw_parts {:x}",
                                    buf as u64,
                                    vec.as_ptr() as u64
                                );
                            }*/
                            reap_queue.push_front((pkt, pkt_paddr));
                        }

                        tx_clean_index = wrap_ring(tx_clean_index, self.transmit_ring.len());
                    }

                    if debug {
                        println!(
                            "programming new buffer! {:x} packet[0] {:x}",
                            packet.as_ptr() as u64,
                            packet[0]
                        );
                    }
                    let mut buf_addr: UnsafeCell<*mut u64> = UnsafeCell::new(
                        &(*self.transmit_ring.as_ptr().add(tx_index))
                            .read
                            .buffer_addr as *const u64 as *mut u64,
                    );

                    //use asys::sys_mresolve;
                    //let pkt_paddr = sys_mresolve(packet.as_ptr() as usize).0 as u64;

                    log::trace!(
                        "pkt vaddr {:>08x} paddr {:>08x}",
                        packet.as_ptr() as usize,
                        pkt_paddr
                    );

                    // switch to a new buffer
                    core::ptr::write_volatile(*buf_addr.get_mut(), pkt_paddr);

                    self.transmit_buffers_tup[tx_index] = Some((packet, pkt_paddr));
                    self.tx_slot[tx_index] = true;

                    //core::mem::forget(packet);

                    let mut cmd_type: UnsafeCell<*mut u32> = UnsafeCell::new(
                        &(*self.transmit_ring.as_ptr().add(tx_index))
                            .read
                            .cmd_type_len as *const u32 as *mut u32,
                    );

                    core::ptr::write_volatile(
                        *cmd_type.get_mut(),
                        IXGBE_ADVTXD_DCMD_EOP
                            | IXGBE_ADVTXD_DCMD_RS
                            | IXGBE_ADVTXD_DCMD_IFCS
                            | IXGBE_ADVTXD_DCMD_DEXT
                            | IXGBE_ADVTXD_DTYP_DATA
                            | pkt_len as u32,
                    );

                    let mut olinfo_status: UnsafeCell<*mut u32> = UnsafeCell::new(
                        &(*self.transmit_ring.as_ptr().add(tx_index))
                            .read
                            .olinfo_status as *const u32 as *mut u32,
                    );

                    core::ptr::write_volatile(
                        *olinfo_status.get_mut(),
                        (pkt_len as u32) << IXGBE_ADVTXD_PAYLEN_SHIFT,
                    );
                }

                last_tx_index = tx_index;
                tx_index = wrap_ring(tx_index, self.transmit_ring.len());
                sent += 1;
            }
            if reap_queue.len() < BATCH_SIZE {
                let mut reaped = 0;
                let mut count = 0;
                let batch = BATCH_SIZE - reap_queue.len();

                loop {
                    let status = unsafe {
                        core::ptr::read_volatile(
                            &(*self.transmit_ring.as_ptr().add(tx_clean_index)).wb.status
                                as *const u32,
                        )
                    };

                    if (status & IXGBE_ADVTXD_STAT_DD) != 0 {
                        if self.tx_slot[tx_clean_index] {
                            if let Some((pkt, paddr)) =
                                self.transmit_buffers_tup[tx_clean_index].take()
                            {
                                reap_queue.push_front((pkt, paddr));
                            }
                            self.tx_slot[tx_clean_index] = false;
                            self.transmit_buffers[tx_clean_index] = None;
                            reaped += 1;
                        }
                        tx_clean_index = wrap_ring(tx_clean_index, self.transmit_ring.len());
                    }

                    count += 1;

                    if tx_clean_index == self.transmit_index || count == batch {
                        break;
                    }
                }
                self.tx_clean_index = wrap_ring(tx_clean_index, self.transmit_ring.len());
            }
        }

        if sent > 0 && tx_index == last_tx_index {
            println!("Queued packets, but failed to update idx");
            println!(
                "last_tx_index {} tx_index {} tx_clean_index {}",
                last_tx_index, tx_index, tx_clean_index
            );
        }

        if tx_index != last_tx_index {
            if debug {
                println!(
                    "Update tdt from {} to {}",
                    self.read_qreg_idx(IxgbeDmaArrayRegs::Tdt, 0),
                    tx_index
                );
            }
            //self.bar.write_reg_tdt(0, tx_index as u64);
            self.write_qreg_idx(IxgbeDmaArrayRegs::Tdt, 0, tx_index as u64);
            self.transmit_index = tx_index;
            self.tx_clean_index = tx_clean_index;
        }

        if sent == 0 {
            //println!("Sent {} packets", sent);
        }

        sent
    }

    #[inline(always)]
    fn rx_submit_and_poll2(
        &mut self,
        packets: &mut VecDeque<(Vec<u8>, u64)>,
        reap_queue: &mut VecDeque<(Vec<u8>, u64)>,
        debug: bool,
    ) -> usize {
        let mut rx_index = self.receive_index;
        let mut last_rx_index = self.receive_index;
        let mut received_packets = 0;
        let mut rx_clean_index = self.rx_clean_index;
        let BATCH_SIZE = 32;

        while let Some((packet, pkt_paddr)) = packets.pop_front() {
            let mut desc = unsafe {
                &mut *(self.receive_ring.as_ptr().add(rx_index) as *mut ixgbe_adv_rx_desc)
            };

            let status =
                unsafe { core::ptr::read_volatile(&mut (*desc).wb.upper.status_error as *mut u32) };

            if ((status & IXGBE_RXDADV_STAT_DD) == 0) && self.rx_slot[rx_index] {
                packets.push_front((packet, pkt_paddr));
                break;
            }

            if ((status & IXGBE_RXDADV_STAT_DD) != 0) && ((status & IXGBE_RXDADV_STAT_EOP) == 0) {
                panic!("increase buffer size or decrease MTU")
            }

            let length = unsafe {
                core::ptr::read_volatile(&(*desc).wb.upper.length as *const u16) as usize
            };

            unsafe {
                if self.rx_slot[rx_index] {
                    if let Some((mut pkt, paddr)) = self.receive_buffers_tup[rx_index].take() {
                        //let mut buf = pkt.as_mut_ptr();
                        //println!("{:x} len {} cap {}", buf as u64, pkt.len(), pkt.capacity());
                        if length <= pkt.capacity() {
                            unsafe {
                                pkt.set_len(length);
                            }
                            reap_queue.push_back((pkt, paddr));
                            //received_packets += 1;
                        } else {
                            println!("Not pushed");
                        }
                        self.receive_buffers_tup[rx_index] = None;
                    }
                    self.rx_slot[rx_index] = false;
                    rx_clean_index = wrap_ring(rx_clean_index, self.receive_ring.len());
                }

                let mut pkt_addr: UnsafeCell<*mut u64> = UnsafeCell::new(
                    &(*self.receive_ring.as_ptr().add(rx_index)).read.pkt_addr as *const u64
                        as *mut u64,
                );

                //use asys::sys_mresolve;
                //let pkt_paddr = sys_mresolve(packet.as_ptr() as usize).0 as u64;

                core::ptr::write_volatile(*pkt_addr.get_mut(), pkt_paddr);

                log::trace!(
                    "pkt vaddr {:>08x} paddr {:>08x}",
                    packet.as_ptr() as usize,
                    pkt_paddr
                );

                let mut hdr_addr: UnsafeCell<*mut u64> = UnsafeCell::new(
                    &(*self.receive_ring.as_ptr().add(rx_index)).read.hdr_addr as *const u64
                        as *mut u64,
                );

                core::ptr::write_volatile(*hdr_addr.get_mut(), 0 as u64);

                self.receive_buffers_tup[rx_index] = Some((packet, pkt_paddr));
                self.rx_slot[rx_index] = true;
            }

            last_rx_index = rx_index;
            rx_index = wrap_ring(rx_index, self.receive_ring.len());

            received_packets += 1;
        }

        //rx_clean_index = wrap_ring(rx_clean_index, self.receive_ring.len());

        /*if reap_queue.len() < BATCH_SIZE {
            let rx_index = self.receive_index;
            let mut reaped = 0;
            let batch = BATCH_SIZE - reap_queue.len();
            let mut count = 0;
            let last_rx_clean = rx_clean_index;
            //println!("reap_queue {} ", reap_queue.len());

            loop {
                let mut desc = unsafe {
                    &mut *(self.receive_ring.as_ptr().add(rx_clean_index) as *mut ixgbe_adv_rx_desc)
                };

                let status = unsafe {
                    core::ptr::read_volatile(&mut (*desc).wb.upper.status_error as *mut u32)
                };

                if debug {
                    println!("checking status[{}] {:x}", rx_clean_index, status);
                }

                if ((status & IXGBE_RXDADV_STAT_DD) == 0) {
                    break;
                }

                if ((status & IXGBE_RXDADV_STAT_DD) != 0) && ((status & IXGBE_RXDADV_STAT_EOP) == 0)
                {
                    panic!("increase buffer size or decrease MTU")
                }

                if self.rx_slot[rx_clean_index] {
                    if let Some(mut pkt) = self.receive_buffers[rx_clean_index].take() {
                        let length = unsafe {
                            core::ptr::read_volatile(&(*desc).wb.upper.length as *const u16)
                                as usize
                        };
                        //log::info!("length {}", length);

                        //let mut buf = pkt.as_mut_ptr();
                        //let vec = unsafe { Vec::from_raw_parts(buf, length, pkt.capacity()) };
                        if length <= pkt.capacity() {
                            unsafe {
                                pkt.set_len(length);
                            }
                            reap_queue.push_back(pkt);
                        } else {
                            println!("Not pushed");
                        }
                    }
                    self.rx_slot[rx_clean_index] = false;
                    self.receive_buffers[rx_clean_index] = None;
                    reaped += 1;
                    rx_clean_index = wrap_ring(rx_clean_index, self.receive_ring.len());
                }

                count += 1;

                if rx_clean_index == rx_index || count == batch {
                    break;
                }
            }

            if debug {
                println!("clean_index {}", rx_clean_index);
            }

            //println!("reap_queue_after {}\n", reap_queue.len());

            if last_rx_clean != rx_clean_index {
                rx_clean_index = wrap_ring(rx_clean_index, self.receive_ring.len());
            }
        }*/

        if rx_index != last_rx_index {
            if debug {
                println!(
                    "Update rdt from {} to {}",
                    self.read_qreg_idx(IxgbeDmaArrayRegs::Rdt, 0),
                    last_rx_index
                );
                println!("rx_index {} clean_index {}", rx_index, self.rx_clean_index);
            }
            self.write_qreg_idx(IxgbeDmaArrayRegs::Rdt, 0, last_rx_index as u64);
            self.receive_index = rx_index;
            self.rx_clean_index = rx_clean_index;
        }

        received_packets
    }

    #[inline(always)]
    fn rx_submit_and_poll(
        &mut self,
        packets: &mut VecDeque<Vec<u8>>,
        reap_queue: &mut VecDeque<Vec<u8>>,
        debug: bool,
    ) -> usize {
        let mut rx_index = self.receive_index;
        let mut last_rx_index = self.receive_index;
        let mut received_packets = 0;
        let mut rx_clean_index = self.rx_clean_index;
        let BATCH_SIZE = 32;

        while let Some(packet) = packets.pop_front() {
            let mut desc = unsafe {
                &mut *(self.receive_ring.as_ptr().add(rx_index) as *mut ixgbe_adv_rx_desc)
            };

            let status =
                unsafe { core::ptr::read_volatile(&mut (*desc).wb.upper.status_error as *mut u32) };

            if ((status & IXGBE_RXDADV_STAT_DD) == 0) && self.rx_slot[rx_index] {
                packets.push_front(packet);
                break;
            }

            if ((status & IXGBE_RXDADV_STAT_DD) != 0) && ((status & IXGBE_RXDADV_STAT_EOP) == 0) {
                panic!("increase buffer size or decrease MTU")
            }

            let length = unsafe {
                core::ptr::read_volatile(&(*desc).wb.upper.length as *const u16) as usize
            };

            unsafe {
                if self.rx_slot[rx_index] {
                    if let Some(mut pkt) = self.receive_buffers[rx_index].take() {
                        //let mut buf = pkt.as_mut_ptr();
                        //println!("{:x} len {} cap {}", buf as u64, pkt.len(), pkt.capacity());
                        if length <= pkt.capacity() {
                            pkt.set_len(length);
                            reap_queue.push_back(pkt);
                            //received_packets += 1;
                        } else {
                            println!("Not pushed");
                        }
                        self.receive_buffers[rx_index] = None;
                    }
                    self.rx_slot[rx_index] = false;
                    rx_clean_index = wrap_ring(rx_clean_index, self.receive_ring.len());
                }

                let mut pkt_addr: UnsafeCell<*mut u64> = UnsafeCell::new(
                    &(*self.receive_ring.as_ptr().add(rx_index)).read.pkt_addr as *const u64
                        as *mut u64,
                );

                use asys::sys_mresolve;
                let pkt_paddr = sys_mresolve(packet.as_ptr() as usize).0 as u64;

                core::ptr::write_volatile(*pkt_addr.get_mut(), pkt_paddr);

                log::trace!(
                    "pkt vaddr {:>08x} paddr {:>08x}",
                    packet.as_ptr() as usize,
                    pkt_paddr
                );

                let mut hdr_addr: UnsafeCell<*mut u64> = UnsafeCell::new(
                    &(*self.receive_ring.as_ptr().add(rx_index)).read.hdr_addr as *const u64
                        as *mut u64,
                );

                core::ptr::write_volatile(*hdr_addr.get_mut(), 0 as u64);

                self.receive_buffers[rx_index] = Some(packet);
                self.rx_slot[rx_index] = true;
            }

            last_rx_index = rx_index;
            rx_index = wrap_ring(rx_index, self.receive_ring.len());

            received_packets += 1;
        }

        if rx_index != last_rx_index {
            if debug {
                println!(
                    "Update rdt from {} to {}",
                    self.read_qreg_idx(IxgbeDmaArrayRegs::Rdt, 0),
                    last_rx_index
                );
                println!("rx_index {} clean_index {}", rx_index, self.rx_clean_index);
            }
            self.write_qreg_idx(IxgbeDmaArrayRegs::Rdt, 0, last_rx_index as u64);
            self.receive_index = rx_index;
            self.rx_clean_index = rx_clean_index;
        }

        received_packets
    }

    /*
    fn tx_submit_and_poll_rref(
        &mut self,
        mut packets: RRefDeque<[u8; 1514], 32>,
        mut reap_queue: RRefDeque<[u8; 1514], 32>,
        pkt_len: usize,
        debug: bool,
    ) -> (usize, RRefDeque<[u8; 1514], 32>, RRefDeque<[u8; 1514], 32>) {
        let mut sent = 0;
        let mut tx_index = self.transmit_index;
        let mut tx_clean_index = self.tx_clean_index;
        let mut last_tx_index = self.transmit_index;
        let num_descriptors = self.transmit_ring.len();
        let BATCH_SIZE = 32;

        if debug {
            //println!("tx index {} packets {}", tx_index, packets.len());
        }

        while let Some(packet) = packets.pop_front() {
            //println!("Found packet!");
            let mut desc = unsafe {
                &mut *(self.transmit_ring.as_ptr().add(tx_index) as *mut ixgbe_adv_tx_desc)
            };

            let status = unsafe { core::ptr::read_volatile(&mut (*desc).wb.status as *mut u32) };

            unsafe {
                //println!("pkt_addr {:08X} tx_Buffer {:08X}",
                //            (*desc).read.pkt_addr as *const u64 as u64,
                //            self.transmit_buffer[tx_index].physical());
            }

            // DD == 0 on a TX desc leaves us with 2 possibilities
            // 1) The desc is populated (tx_slot[i] = true), the device did not sent it out yet
            // 2) The desc is not populated. In that case, tx_slot[i] = false
            if ((status & IXGBE_RXDADV_STAT_DD) == 0) && self.tx_slot[tx_index] {
                if debug {
                    //println!("No free slot. Fucked");
                    if !self.dump {
                        self.dump_tx_desc();
                    }
                }
                packets.push_back(packet);
                break;
            }

            if debug {
                //println!("packet len {}", pkt_len);
            }

            // HACK: Fix pkt_len here
            // Assuming all we send is IPv4
            // 14 + 2, 14 + 2
            //let pkt_len_hi = packet[14 + 2];
            //let pkt_len_lo = packet[14 + 3];
            let real_pkt_len =
                { ((packet[14 + 2] as usize) << 8) + (packet[14 + 3] as usize) + 14 };
            // println!("tx/ixgbe: packet len {}", real_pkt_len);
            // println!("tx/ixgbe: packet: {:02x?}", &packet[..real_pkt_len]);

            unsafe {
                if self.tx_slot[tx_index] {
                    if let Some(mut buf) = self.transmit_rrefs[tx_index].take() {
                        if debug {
                            //println!("buf {:x}", buf as u64);
                        }

                        //if reap_queue.push_back(RRef::new(buf.take().unwrap())).is_some() {
                        if let Some(buf) = reap_queue.push_back(buf) {
                            println!("tx_sub_and_poll1: Pushing to a full reap queue");
                            self.transmit_rrefs[tx_index] = Some(buf);
                            break;
                        }

                        tx_clean_index = wrap_ring(tx_clean_index, self.transmit_ring.len());
                    }
                }

                let pkt_addr = &*packet as *const [u8; 1514] as *const u64 as u64;
                if debug {
                    //println!("programming new buffer! {:x} packet[0] {:x}", packet.as_ptr() as u64, packet[0]);
                }
                // switch to a new buffer
                core::ptr::write_volatile(
                    &(*self.transmit_ring.as_ptr().add(tx_index))
                        .read
                        .buffer_addr as *const u64 as *mut u64,
                    pkt_addr,
                );

                self.transmit_rrefs[tx_index] = Some(packet);
                self.tx_slot[tx_index] = true;

                core::ptr::write_volatile(
                    &(*self.transmit_ring.as_ptr().add(tx_index))
                        .read
                        .cmd_type_len as *const u32 as *mut u32,
                    IXGBE_ADVTXD_DCMD_EOP
                        | IXGBE_ADVTXD_DCMD_RS
                        | IXGBE_ADVTXD_DCMD_IFCS
                        | IXGBE_ADVTXD_DCMD_DEXT
                        | IXGBE_ADVTXD_DTYP_DATA
                        | real_pkt_len as u32,
                );

                core::ptr::write_volatile(
                    &(*self.transmit_ring.as_ptr().add(tx_index))
                        .read
                        .olinfo_status as *const u32 as *mut u32,
                    (real_pkt_len as u32) << IXGBE_ADVTXD_PAYLEN_SHIFT,
                );
            }

            last_tx_index = tx_index;
            tx_index = wrap_ring(tx_index, self.transmit_ring.len());
            sent += 1;
        }
        if reap_queue.len() < BATCH_SIZE {
            let mut reaped = 0;
            let mut count = 0;
            let batch = BATCH_SIZE - reap_queue.len();

            loop {
                let status = unsafe {
                    core::ptr::read_volatile(
                        &(*self.transmit_ring.as_ptr().add(tx_clean_index)).wb.status as *const u32,
                    )
                };

                if (status & IXGBE_ADVTXD_STAT_DD) != 0 {
                    if self.tx_slot[tx_clean_index] {
                        if let Some(mut buf) = self.transmit_rrefs[tx_clean_index].take() {
                            if reap_queue.push_back(buf).is_some() {
                                println!("tx_sub_and_poll2: Pushing to a full reap queue");
                            }
                        }

                        self.tx_slot[tx_clean_index] = false;
                        self.transmit_buffers[tx_clean_index] = None;
                        reaped += 1;
                    }
                    tx_clean_index = wrap_ring(tx_clean_index, self.transmit_ring.len());
                }

                count += 1;

                if tx_clean_index == self.transmit_index || count == batch {
                    break;
                }
            }
            self.tx_clean_index = wrap_ring(tx_clean_index, self.transmit_ring.len());
        }

        if sent > 0 && tx_index == last_tx_index {
            //println!("Queued packets, but failed to update idx");
            //println!("last_tx_index {} tx_index {} tx_clean_index {}", last_tx_index, tx_index, tx_clean_index);
        }

        if tx_index != last_tx_index {
            if debug {
                // println!("Update tdt from {} to {}", self.read_qreg_idx(IxgbeDmaArrayRegs::Tdt, 0), tx_index);
            }
            //self.bar.write_reg_tdt(0, tx_index as u64);
            self.write_qreg_idx(IxgbeDmaArrayRegs::Tdt, 0, tx_index as u64);
            self.transmit_index = tx_index;
            self.tx_clean_index = tx_clean_index;
        }

        if sent == 0 {
            //println!("Sent {} packets", sent);
        }
        (sent, packets, reap_queue)
    }

    #[inline(always)]
    fn rx_submit_and_poll_rref(
        &mut self,
        mut packets: RRefDeque<[u8; 1514], 32>,
        mut reap_queue: RRefDeque<[u8; 1514], 32>,
        pkt_len: usize,
        debug: bool,
    ) -> (usize, RRefDeque<[u8; 1514], 32>, RRefDeque<[u8; 1514], 32>) {
        let mut rx_index = self.receive_index;
        let mut last_rx_index = self.receive_index;
        let mut received_packets = 0;
        let mut rx_clean_index = self.rx_clean_index;
        let BATCH_SIZE = 32;

        while let Some(packet) = packets.pop_front() {
            let mut desc = unsafe {
                &mut *(self.receive_ring.as_ptr().add(rx_index) as *mut ixgbe_adv_rx_desc)
            };

            let status =
                unsafe { core::ptr::read_volatile(&mut (*desc).wb.upper.status_error as *mut u32) };

            unsafe {
                //println!("pkt_addr {:08X} status {:x}",
                //            (*desc).read.pkt_addr as *const u64 as u64, status);
                //self.receive_buffers[rx_index].physical());
            }

            if debug {
                println!("rx_index {} clean_index {}", rx_index, rx_clean_index);
            }
            if ((status & IXGBE_RXDADV_STAT_DD) == 0) && self.rx_slot[rx_index] {
                //println!("no packets to rx");
                packets.push_back(packet);
                break;
            }

            if ((status & IXGBE_RXDADV_STAT_DD) != 0) && ((status & IXGBE_RXDADV_STAT_EOP) == 0) {
                panic!("increase buffer size or decrease MTU")
            }

            // Reset the status DD bit
            /*unsafe {
                if (status & IXGBE_RXDADV_STAT_DD) != 0 {
                    core::ptr::write_volatile(&mut (*desc).wb.upper.status_error as *mut u32,
                                status & !IXGBE_RXDADV_STAT_DD);
                }
            }*/

            //println!("Found packet {}", rx_index);
            let length = unsafe {
                core::ptr::read_volatile(&(*desc).wb.upper.length as *const u16) as usize
            };

            //if length > 0 {
            //println!("Got a packet with len {}", length);
            //}

            unsafe {
                if self.rx_slot[rx_index] {
                    if let Some(mut buf) = self.receive_rrefs[rx_index].take() {
                        if length <= 1514 {
                            if reap_queue.push_back(buf).is_some() {
                                println!("rx_sub_and_poll1: Pushing to a full reap queue");
                            }
                        } else {
                            println!("Not pushed");
                        }
                    }
                    self.rx_slot[rx_index] = false;
                    rx_clean_index = wrap_ring(rx_clean_index, self.receive_ring.len());
                }

                let pkt_addr = &*packet as *const [u8; 1514] as *const u64 as u64;

                core::ptr::write_volatile(
                    &(*self.receive_ring.as_ptr().add(rx_index)).read.pkt_addr as *const u64
                        as *mut u64,
                    pkt_addr,
                );

                core::ptr::write_volatile(
                    &(*self.receive_ring.as_ptr().add(rx_index)).read.hdr_addr as *const u64
                        as *mut u64,
                    0 as u64,
                );

                self.receive_rrefs[rx_index] = Some(packet);
                self.rx_slot[rx_index] = true;
            }

            last_rx_index = rx_index;
            rx_index = wrap_ring(rx_index, self.receive_ring.len());

            received_packets += 1;
        }

        rx_clean_index = wrap_ring(rx_clean_index, self.receive_ring.len());

        if reap_queue.len() < BATCH_SIZE {
            let rx_index = self.receive_index;
            let mut reaped = 0;
            let batch = BATCH_SIZE - reap_queue.len();
            let mut count = 0;
            let last_rx_clean = rx_clean_index;
            //println!("reap_queue {} ", reap_queue.len());

            loop {
                let mut desc = unsafe {
                    &mut *(self.receive_ring.as_ptr().add(rx_clean_index) as *mut ixgbe_adv_rx_desc)
                };

                let status = unsafe {
                    core::ptr::read_volatile(&mut (*desc).wb.upper.status_error as *mut u32)
                };

                if debug {
                    println!("checking status[{}] {:x}", rx_clean_index, status);
                }

                if ((status & IXGBE_RXDADV_STAT_DD) == 0) {
                    break;
                }

                if ((status & IXGBE_RXDADV_STAT_DD) != 0) && ((status & IXGBE_RXDADV_STAT_EOP) == 0)
                {
                    panic!("increase buffer size or decrease MTU")
                }

                if self.rx_slot[rx_clean_index] {
                    if let Some(mut pkt) = self.receive_rrefs[rx_clean_index].take() {
                        let length = unsafe {
                            core::ptr::read_volatile(&(*desc).wb.upper.length as *const u16)
                                as usize
                        };

                        if reap_queue.push_back(pkt).is_some() {
                            println!("rx_sub_and_poll2: Pushing to a full reap queue");
                        }
                    }
                    self.rx_slot[rx_clean_index] = false;
                    self.receive_rrefs[rx_clean_index] = None;
                    reaped += 1;
                    rx_clean_index = wrap_ring(rx_clean_index, self.receive_ring.len());
                }

                count += 1;

                if rx_clean_index == rx_index || count == batch {
                    break;
                }
            }

            if debug {
                println!("clean_index {}", rx_clean_index);
            }

            //println!("reap_queue_after {}\n", reap_queue.len());

            if last_rx_clean != rx_clean_index {
                rx_clean_index = wrap_ring(rx_clean_index, self.receive_ring.len());
            }
        }

        if rx_index != last_rx_index {
            if debug {
                println!(
                    "Update rdt from {} to {}",
                    self.read_qreg_idx(IxgbeDmaArrayRegs::Rdt, 0),
                    last_rx_index
                );
                println!("rx_index {} clean_index {}", rx_index, self.rx_clean_index);
            }
            self.write_qreg_idx(IxgbeDmaArrayRegs::Rdt, 0, last_rx_index as u64);
            self.receive_index = rx_index;
            self.rx_clean_index = rx_clean_index;
        }

        (received_packets, packets, reap_queue)
    }
    */

    pub fn dump_dma_regs(&self) {
        let mut string = format!(
            "Interrupt regs:\n\tEITR {:08X} IVAR(0) {:08X}\n",
            self.read_qreg_idx(IxgbeDmaArrayRegs::Eitr, 0) as u32,
            self.read_qreg_idx(IxgbeDmaArrayRegs::Ivar, 0) as u32
        );

        string.push_str(&format!("Receive regs:\n\tRXPBSIZE(0): {:08X} SRRCTL(0) {:08X}\n\tRDBAL(0) {:08X} RDBAH(0) {:08X} \
                                 \n\tRDLEN(0) {:08X} RDH(0) {:08X} RDT(0) {:08X}\n",
                                 self.read_qreg_idx(IxgbeDmaArrayRegs::Rxpbsize, 0) as u32,
                                 self.read_qreg_idx(IxgbeDmaArrayRegs::Srrctl, 0) as u32,
                                 self.read_qreg_idx(IxgbeDmaArrayRegs::Rdbal, 0) as u32,
                                 self.read_qreg_idx(IxgbeDmaArrayRegs::Rdbah, 0) as u32,
                                 self.read_qreg_idx(IxgbeDmaArrayRegs::Rdlen, 0) as u32,
                                 self.read_qreg_idx(IxgbeDmaArrayRegs::Rdh, 0) as u32,
                                 self.read_qreg_idx(IxgbeDmaArrayRegs::Rdt, 0) as u32));

        string.push_str(&format!(
            "Transmit regs:\n\tTXDCTL(0) {:08X} TXPBSIZE(0): {:08X}\n\t \
                                 TDBAL(0) {:08X} TDBAH(0) {:08X}\n\t \
                                 TDLEN(0) {:08X} TDH(0) {:08X} TDT(0) {:08X}\n",
            self.read_qreg_idx(IxgbeDmaArrayRegs::Txdctl, 0) as u32,
            self.read_qreg_idx(IxgbeDmaArrayRegs::Txpbsize, 0) as u32,
            self.read_qreg_idx(IxgbeDmaArrayRegs::Tdbal, 0) as u32,
            self.read_qreg_idx(IxgbeDmaArrayRegs::Tdbah, 0) as u32,
            self.read_qreg_idx(IxgbeDmaArrayRegs::Tdlen, 0) as u32,
            self.read_qreg_idx(IxgbeDmaArrayRegs::Tdh, 0) as u32,
            self.read_qreg_idx(IxgbeDmaArrayRegs::Tdt, 0) as u32
        ));

        println!("{}", string);
    }

    #[inline(always)]
    pub fn tx_submit_and_poll_with_ringbuffer(
        &mut self,
        packets: &mut RingBuffer<GenericRingBufferNode<IxgbePayLoad>, SIZE_OF_QUEUE>,
        reap_queue: &mut RingBuffer<GenericRingBufferNode<IxgbePayLoad>, SIZE_OF_QUEUE>,
        debug: bool,
    ) -> usize {
        let mut sent = 0;
        let mut tx_index = self.transmit_index;
        let mut tx_clean_index = self.tx_clean_index;
        let mut last_tx_index = self.transmit_index;
        let num_descriptors = self.transmit_ring.len();
        let BATCH_SIZE = 32;

        if packets.is_empty() == false {
            while let Some(packet) = packets.try_read() {
                //println!("Found packet!");
                let mut desc = unsafe {
                    &mut *(self.transmit_ring.as_ptr().add(tx_index) as *mut ixgbe_adv_tx_desc)
                };

                let status =
                    unsafe { core::ptr::read_volatile(&mut (*desc).wb.status as *mut u32) };

                //unsafe {
                //println!("pkt_addr {:08X} tx_Buffer {:08X}",
                //            (*desc).read.pkt_addr as *const u64 as u64,
                //            self.transmit_buffer[tx_index].physical());
                //}

                // DD == 0 on a TX desc leaves us with 2 possibilities
                // 1) The desc is populated (tx_slot[i] = true), the device did not sent it out yet
                // 2) The desc is not populated. In that case, tx_slot[i] = false
                if ((status & IXGBE_RXDADV_STAT_DD) == 0) && self.tx_slot[tx_index] {
                    if debug {
                        println!("No free slot. Fucked");
                        if !self.dump {
                            self.dump_tx_desc();
                        }
                    }
                    // packets.push_front(packet);
                    break;
                }

                packets.try_free();

                let pkt_len = packet.len;
                if debug {
                    println!("packet len {}", pkt_len);
                }
                unsafe {
                    if self.tx_slot[tx_index] {
                        if let Some(pkt) = self.transmit_addrs[tx_index].take() {
                            //let mut buf = pkt.as_mut_ptr();
                            //let vec = Vec::from_raw_parts(buf, pkt_len, pkt.capacity());
                            /*if debug {
                                println!(
                                    "buf {:x} vec_raw_parts {:x}",
                                    buf as u64,
                                    vec.as_ptr() as u64
                                );
                            }*/
                            while reap_queue.try_push(&pkt) == false {}
                        }

                        tx_clean_index = wrap_ring(tx_clean_index, self.transmit_ring.len());
                    }

                    let mut buf_addr: UnsafeCell<*mut u64> = UnsafeCell::new(
                        &(*self.transmit_ring.as_ptr().add(tx_index))
                            .read
                            .buffer_addr as *const u64 as *mut u64,
                    );

                    use asys::sys_mresolve;
                    let pkt_paddr = sys_mresolve(packet.addr).0 as u64;

                    log::trace!("pkt vaddr {:>08x} paddr {:>08x}", packet.addr, pkt_paddr);

                    // switch to a new buffer
                    core::ptr::write_volatile(*buf_addr.get_mut(), pkt_paddr);

                    self.transmit_addrs[tx_index] = Some(packet);
                    self.tx_slot[tx_index] = true;

                    //core::mem::forget(packet);

                    let mut cmd_type: UnsafeCell<*mut u32> = UnsafeCell::new(
                        &(*self.transmit_ring.as_ptr().add(tx_index))
                            .read
                            .cmd_type_len as *const u32 as *mut u32,
                    );

                    core::ptr::write_volatile(
                        *cmd_type.get_mut(),
                        IXGBE_ADVTXD_DCMD_EOP
                            | IXGBE_ADVTXD_DCMD_RS
                            | IXGBE_ADVTXD_DCMD_IFCS
                            | IXGBE_ADVTXD_DCMD_DEXT
                            | IXGBE_ADVTXD_DTYP_DATA
                            | pkt_len as u32,
                    );

                    let mut olinfo_status: UnsafeCell<*mut u32> = UnsafeCell::new(
                        &(*self.transmit_ring.as_ptr().add(tx_index))
                            .read
                            .olinfo_status as *const u32 as *mut u32,
                    );

                    core::ptr::write_volatile(
                        *olinfo_status.get_mut(),
                        (pkt_len as u32) << IXGBE_ADVTXD_PAYLEN_SHIFT,
                    );
                }

                last_tx_index = tx_index;
                tx_index = wrap_ring(tx_index, self.transmit_ring.len());
                sent += 1;

                if sent == BATCH_SIZE {
                    break;
                }
            }
            if reap_queue.is_full() == false {
                let mut reaped = 0;
                let mut count = 0;

                loop {
                    let status = unsafe {
                        core::ptr::read_volatile(
                            &(*self.transmit_ring.as_ptr().add(tx_clean_index)).wb.status
                                as *const u32,
                        )
                    };

                    if (status & IXGBE_ADVTXD_STAT_DD) != 0 {
                        if self.tx_slot[tx_clean_index] {
                            if let Some(pkt) = self.transmit_addrs[tx_clean_index].take() {
                                while reap_queue.try_push(&pkt) == false {}
                            }
                            self.tx_slot[tx_clean_index] = false;
                            self.transmit_addrs[tx_clean_index] = None;
                            reaped += 1;
                        }
                        tx_clean_index = wrap_ring(tx_clean_index, self.transmit_ring.len());
                    }

                    count += 1;

                    if tx_clean_index == self.transmit_index
                        || count == BATCH_SIZE
                        || reap_queue.is_full()
                    {
                        break;
                    }
                }
                self.tx_clean_index = wrap_ring(tx_clean_index, self.transmit_ring.len());
            }
        }

        if sent > 0 && tx_index == last_tx_index {
            println!("Queued packets, but failed to update idx");
            println!(
                "last_tx_index {} tx_index {} tx_clean_index {}",
                last_tx_index, tx_index, tx_clean_index
            );
        }

        if tx_index != last_tx_index {
            if debug {
                println!(
                    "Update tdt from {} to {}",
                    self.read_qreg_idx(IxgbeDmaArrayRegs::Tdt, 0),
                    tx_index
                );
            }
            //self.bar.write_reg_tdt(0, tx_index as u64);
            self.write_qreg_idx(IxgbeDmaArrayRegs::Tdt, 0, tx_index as u64);
            self.transmit_index = tx_index;
            self.tx_clean_index = tx_clean_index;
        }

        if sent == 0 {
            //println!("Sent {} packets", sent);
        }

        sent
    }
    #[inline(always)]
    pub fn rx_submit_and_poll_with_ringbuffer(
        &mut self,
        packets: &mut RingBuffer<GenericRingBufferNode<IxgbePayLoad>, SIZE_OF_QUEUE>,
        reap_queue: &mut RingBuffer<GenericRingBufferNode<IxgbePayLoad>, SIZE_OF_QUEUE>,
        debug: bool,
    ) -> usize {
        let mut rx_index = self.receive_index;
        let mut last_rx_index = self.receive_index;
        let mut received_packets = 0;
        let mut rx_clean_index = self.rx_clean_index;
        let BATCH_SIZE = 32;

        while let Some(packet) = packets.try_read() {
            let mut desc = unsafe {
                &mut *(self.receive_ring.as_ptr().add(rx_index) as *mut ixgbe_adv_rx_desc)
            };

            let status =
                unsafe { core::ptr::read_volatile(&mut (*desc).wb.upper.status_error as *mut u32) };

            //unsafe {
            //println!("pkt_addr {:08X} status {:x}",
            //            (*desc).read.pkt_addr as *const u64 as u64, status);
            //self.receive_buffers[rx_index].physical());
            //}

            if debug {
                println!("rx_index {} clean_index {}", rx_index, rx_clean_index);
            }
            if ((status & IXGBE_RXDADV_STAT_DD) == 0) && self.rx_slot[rx_index] {
                //println!("no packets to rx");
                // packets.push_front(packet);
                break;
            }
            println!(
                "driver submitting packets at {:x} index {} clean index {}",
                packet.addr, rx_index, rx_clean_index
            );
            packets.try_free();

            if ((status & IXGBE_RXDADV_STAT_DD) != 0) && ((status & IXGBE_RXDADV_STAT_EOP) == 0) {
                panic!("increase buffer size or decrease MTU")
            }

            // Reset the status DD bit
            /*unsafe {
                if (status & IXGBE_RXDADV_STAT_DD) != 0 {
                    core::ptr::write_volatile(&mut (*desc).wb.upper.status_error as *mut u32,
                                status & !IXGBE_RXDADV_STAT_DD);
                }
            }*/

            //println!("Found packet {}", rx_index);
            let length = unsafe {
                core::ptr::read_volatile(&(*desc).wb.upper.length as *const u16) as usize
            };

            //if length > 0 {
            //println!("Got a packet with len {}", length);
            //}

            unsafe {
                if self.rx_slot[rx_index] {
                    println!(" self.rx_slot[rx_index] = true");

                    if let Some(mut pkt) = self.receive_addrs[rx_index].take() {
                        //let mut buf = pkt.as_mut_ptr();
                        //println!("{:x} len {} cap {}", buf as u64, pkt.len(), pkt.capacity());
                        if length <= pkt.len {
                            unsafe {
                                pkt.len = length;
                            }
                            while reap_queue.try_push(&pkt) == false {
                                println!(" while reap_queue.try_push(&pkt) == false");
                            }
                            println!(
                                "driver submitted packets at {:x} index {} clean index  {}",
                                pkt.addr, rx_index, rx_clean_index
                            );
                            //received_packets += 1;
                        } else {
                            println!("Not pushed");
                        }
                        self.receive_addrs[rx_index] = None;
                    }
                    self.rx_slot[rx_index] = false;

                    println!("increamenting clean_index {}", rx_clean_index);
                    rx_clean_index = wrap_ring(rx_clean_index, self.receive_ring.len());
                    println!("increamented clean_index {}", rx_clean_index);
                }

                let mut pkt_addr: UnsafeCell<*mut u64> = UnsafeCell::new(
                    &(*self.receive_ring.as_ptr().add(rx_index)).read.pkt_addr as *const u64
                        as *mut u64,
                );

                use asys::sys_mresolve;
                let pkt_paddr = sys_mresolve(packet.addr).0 as u64;

                core::ptr::write_volatile(*pkt_addr.get_mut(), pkt_paddr);

                log::trace!("pkt vaddr {:>08x} paddr {:>08x}", packet.addr, pkt_paddr);

                let mut hdr_addr: UnsafeCell<*mut u64> = UnsafeCell::new(
                    &(*self.receive_ring.as_ptr().add(rx_index)).read.hdr_addr as *const u64
                        as *mut u64,
                );

                core::ptr::write_volatile(*hdr_addr.get_mut(), 0 as u64);

                self.receive_addrs[rx_index] = Some(packet);
                self.rx_slot[rx_index] = true;
            }

            last_rx_index = rx_index;
            rx_index = wrap_ring(rx_index, self.receive_ring.len());

            received_packets += 1;

            if received_packets == BATCH_SIZE {
                break;
            }
        }

        // println!("increamenting clean_index {}", rx_clean_index);
        // rx_clean_index = wrap_ring(rx_clean_index, self.receive_ring.len());
        // println!("increamented clean_index {}", rx_clean_index);

        println!("self.rx_slot {:?}", self.rx_slot);

        if reap_queue.is_full() == false {
            let rx_index = self.receive_index;
            let mut reaped = 0;
            let last_rx_clean = rx_clean_index;
            //println!("reap_queue {} ", reap_queue.len());

            loop {
                // println!("clean_index {} index {}", rx_clean_index, rx_index);

                let mut desc = unsafe {
                    &mut *(self.receive_ring.as_ptr().add(rx_clean_index) as *mut ixgbe_adv_rx_desc)
                };

                let status = unsafe {
                    core::ptr::read_volatile(&mut (*desc).wb.upper.status_error as *mut u32)
                };

                if debug {
                    println!("checking status[{}] {:x}", rx_clean_index, status);
                }

                if ((status & IXGBE_RXDADV_STAT_DD) == 0) {
                    break;
                }

                if ((status & IXGBE_RXDADV_STAT_DD) != 0) && ((status & IXGBE_RXDADV_STAT_EOP) == 0)
                {
                    panic!("increase buffer size or decrease MTU")
                }

                if self.rx_slot[rx_clean_index] {
                    println!(" self.rx_slot[rx_clean_index] = true");
                    if let Some(mut pkt) = self.receive_addrs[rx_clean_index].take() {
                        let length = unsafe {
                            core::ptr::read_volatile(&(*desc).wb.upper.length as *const u16)
                                as usize
                        };
                        //log::info!("length {}", length);

                        //let mut buf = pkt.as_mut_ptr();
                        //let vec = unsafe { Vec::from_raw_parts(buf, length, pkt.capacity()) };
                        if length <= pkt.len {
                            unsafe {
                                pkt.len = length;
                            }
                            while reap_queue.try_push(&pkt) == false {
                                println!(" while reap_queue.try_push(&pkt) == false");
                            }

                            println!(
                                "driver submitted packets at {:x} index {} clean index  {}",
                                pkt.addr, rx_index, rx_clean_index
                            );
                        } else {
                            println!("Not pushed");
                        }
                    }
                    self.rx_slot[rx_clean_index] = false;
                    self.receive_addrs[rx_clean_index] = None;
                    reaped += 1;

                    println!("increamenting clean_index {}", rx_clean_index);
                    rx_clean_index = wrap_ring(rx_clean_index, self.receive_ring.len());
                    println!("increamented clean_index {}", rx_clean_index);
                } else {
                    break;
                }

                if rx_clean_index == rx_index || reaped == BATCH_SIZE || reap_queue.is_full() {
                    println!("clean_index {} index {}", rx_clean_index, rx_index);
                    break;
                }
            }

            if debug {
                println!("clean_index {}", rx_clean_index);
            }

            //println!("reap_queue_after {}\n", reap_queue.len());

            if last_rx_clean != rx_clean_index {
                println!("increamenting clean_index {}", rx_clean_index);
                rx_clean_index = wrap_ring(rx_clean_index, self.receive_ring.len());
                println!("increamented clean_index {}", rx_clean_index);
            }
        }

        if rx_index != last_rx_index {
            if debug {
                println!(
                    "Update rdt from {} to {}",
                    self.read_qreg_idx(IxgbeDmaArrayRegs::Rdt, 0),
                    last_rx_index
                );
                println!("rx_index {} clean_index {}", rx_index, self.rx_clean_index);
            }
            self.write_qreg_idx(IxgbeDmaArrayRegs::Rdt, 0, last_rx_index as u64);
            self.receive_index = rx_index;
            self.rx_clean_index = rx_clean_index;
        }

        received_packets
    }

    #[inline(always)]
    pub fn tx_submit_and_poll_with_ringbuffer_2(
        &mut self,
        packets: &mut RingBuffer<GenericRingBufferNode<IxgbePayLoad>, SIZE_OF_QUEUE>,
        reap_queue: &mut RingBuffer<GenericRingBufferNode<IxgbePayLoad>, SIZE_OF_QUEUE>,
        debug: bool,
    ) {
        let mut tx_index = self.transmit_index;
        let mut tx_clean_index = self.tx_clean_index;
        let num_descriptors = self.transmit_ring.len();
        let BATCH_SIZE = 128;

        while let Some(packet) = packets.try_read() {
            //println!("Found packet!");
            if tx_clean_index == wrap_ring(tx_index, self.transmit_ring.len()) {
                //println!("skip tx");
                break;
            }

            let mut desc = unsafe {
                &mut *(self.transmit_ring.as_ptr().add(tx_index) as *mut ixgbe_adv_tx_desc)
            };

            let status = unsafe { core::ptr::read_volatile(&mut (*desc).wb.status as *mut u32) };

            //unsafe {
            //println!("pkt_addr {:08X} tx_Buffer {:08X}",
            //            (*desc).read.pkt_addr as *const u64 as u64,
            //            self.transmit_buffer[tx_index].physical());
            //}

            // DD == 0 on a TX desc leaves us with 2 possibilities
            // 1) The desc is populated (tx_slot[i] = true), the device did not sent it out yet
            // 2) The desc is not populated. In that case, tx_slot[i] = false
            if ((status & IXGBE_RXDADV_STAT_DD) == 0) && self.tx_slot[tx_index] {
                if debug {
                    println!("No free slot. Fucked");
                    if !self.dump {
                        self.dump_tx_desc();
                    }
                }
                // packets.push_front((packet, pkt_paddr));
                break;
            }
            packets.try_free();

            let pkt_len = packet.len;
            if debug {
                println!("packet len {}", pkt_len);
            }
            unsafe {
                let mut buf_addr: UnsafeCell<*mut u64> = UnsafeCell::new(
                    &(*self.transmit_ring.as_ptr().add(tx_index))
                        .read
                        .buffer_addr as *const u64 as *mut u64,
                );

                use asys::sys_mresolve;
                // let pkt_paddr = sys_mresolve(packet.addr).0 as u64;
                let pkt_paddr = packet.paddr as u64;

                // log::trace!(
                //     "pkt vaddr {:>08x} paddr {:>08x}",
                //     packet.as_ptr() as usize,
                //     pkt_paddr
                // );

                // switch to a new buffer
                core::ptr::write_volatile(*buf_addr.get_mut(), pkt_paddr);

                self.transmit_addrs[tx_index] = Some(packet);
                self.tx_slot[tx_index] = true;

                // println!("driver sending tx_index {}", tx_index);

                // println!("driver sending packet@ {:x} self.transmit_index {} self.tx_clean_index {} tx_clean_index {}
                // self.tx_slot {:?}
                // ", packet.addr, self.transmit_index, self.tx_clean_index,tx_clean_index,self.tx_slot);
                //core::mem::forget(packet);

                let mut cmd_type: UnsafeCell<*mut u32> = UnsafeCell::new(
                    &(*self.transmit_ring.as_ptr().add(tx_index))
                        .read
                        .cmd_type_len as *const u32 as *mut u32,
                );

                core::ptr::write_volatile(
                    *cmd_type.get_mut(),
                    IXGBE_ADVTXD_DCMD_EOP
                        | IXGBE_ADVTXD_DCMD_RS
                        | IXGBE_ADVTXD_DCMD_IFCS
                        | IXGBE_ADVTXD_DCMD_DEXT
                        | IXGBE_ADVTXD_DTYP_DATA
                        | pkt_len as u32,
                );

                let mut olinfo_status: UnsafeCell<*mut u32> = UnsafeCell::new(
                    &(*self.transmit_ring.as_ptr().add(tx_index))
                        .read
                        .olinfo_status as *const u32 as *mut u32,
                );

                core::ptr::write_volatile(
                    *olinfo_status.get_mut(),
                    (pkt_len as u32) << IXGBE_ADVTXD_PAYLEN_SHIFT,
                );
            }

            tx_index = wrap_ring(tx_index, self.transmit_ring.len());
        }

        if self.transmit_index != tx_index {
            if debug {
                println!(
                    "Update tdt from {} to {}",
                    self.read_qreg_idx(IxgbeDmaArrayRegs::Tdt, 0),
                    tx_index
                );
            }
            //self.bar.write_reg_tdt(0, tx_index as u64);
            self.write_qreg_idx(IxgbeDmaArrayRegs::Tdt, 0, tx_index as u64);
            self.transmit_index = tx_index;
        }

        let mut reaped = 0;
        let mut count = 0;
        let batch = BATCH_SIZE;

        loop {
            if reap_queue.is_full() {
                break;
            }

            if tx_clean_index == self.transmit_index || count == batch {
                break;
            }

            let status = unsafe {
                core::ptr::read_volatile(
                    &(*self.transmit_ring.as_ptr().add(tx_clean_index)).wb.status as *const u32,
                )
            };

            if (status & IXGBE_ADVTXD_STAT_DD) != 0 {
                // log::info!("tx_clean_index {}
                // self.transmit_index {}
                // self.tx_clean_index {}
                // self.transmit_ring.len() {}
                // self.tx_slot {:?}", tx_clean_index,  self.transmit_index,self.tx_clean_index,self.transmit_ring.len(), self.tx_slot);

                if self.tx_slot[tx_clean_index] {
                    if let Some(pkt) = self.transmit_addrs[tx_clean_index].take() {
                        while reap_queue.try_push(&pkt) == false {}
                        // println!("driver sent tx_clean_index {}", tx_clean_index);
                        // println!("driver sent packet@ {:x} self.transmit_index {} self.tx_clean_index {} tx_clean_index {}
                        // self.tx_slot {:?}
                        // ", pkt.addr, self.transmit_index, self.tx_clean_index,tx_clean_index,self.tx_slot);
                    }
                    self.tx_slot[tx_clean_index] = false;
                    self.transmit_addrs[tx_clean_index] = None;
                }
                tx_clean_index = wrap_ring(tx_clean_index, self.transmit_ring.len());
            } else {
                break;
            }

            count += 1;
        }
        self.tx_clean_index = tx_clean_index;
    }

    #[inline(always)]
    pub fn rx_submit_and_poll_with_ringbuffer_2(
        &mut self,
        packets: &mut RingBuffer<GenericRingBufferNode<IxgbePayLoad>, SIZE_OF_QUEUE>,
        reap_queue: &mut RingBuffer<GenericRingBufferNode<IxgbePayLoad>, SIZE_OF_QUEUE>,
        debug: bool,
    ) {
        let mut rx_index = self.receive_index;
        let mut last_rx_index = self.receive_index;
        let mut rx_clean_index = self.rx_clean_index;
        let BATCH_SIZE = 128;

        while let Some(packet) = packets.try_read() {
            if rx_clean_index == wrap_ring(rx_index, self.receive_ring.len()) {
                //println!("skip rx");
                break;
            }

            let mut desc = unsafe {
                &mut *(self.receive_ring.as_ptr().add(rx_index) as *mut ixgbe_adv_rx_desc)
            };

            let status =
                unsafe { core::ptr::read_volatile(&mut (*desc).wb.upper.status_error as *mut u32) };

            if ((status & IXGBE_RXDADV_STAT_DD) == 0) && self.rx_slot[rx_index] {
                // packets.push_front((packet, pkt_paddr));
                break;
            }

            packets.try_free();

            // log::info!("driver receiving @ {:x}", packet.addr);

            if ((status & IXGBE_RXDADV_STAT_DD) != 0) && ((status & IXGBE_RXDADV_STAT_EOP) == 0) {
                panic!("increase buffer size or decrease MTU")
            }

            unsafe {
                // if self.rx_slot[rx_index] {
                //     if let Some(mut pkt) = self.receive_addrs[rx_index].take() {
                //         //let mut buf = pkt.as_mut_ptr();
                //         //println!("{:x} len {} cap {}", buf as u64, pkt.len(), pkt.capacity());
                //         if length <= pkt.len {
                //             unsafe {
                //                 pkt.len = length;
                //             }
                //             while reap_queue.try_push(&pkt) == false{

                //             }

                //             // log::info!("driver received @ {:x}", pkt.addr);
                //             //received_packets += 1;
                //         } else {
                //             println!("Not pushed");
                //         }
                //         self.receive_addrs[rx_index] = None;
                //     }
                //     self.rx_slot[rx_index] = false;
                //     rx_clean_index = wrap_ring(rx_clean_index, self.receive_ring.len());
                // }

                let mut pkt_addr: UnsafeCell<*mut u64> = UnsafeCell::new(
                    &(*self.receive_ring.as_ptr().add(rx_index)).read.pkt_addr as *const u64
                        as *mut u64,
                );

                use asys::sys_mresolve;
                // let pkt_paddr = sys_mresolve(packet.addr).0 as u64;
                let pkt_paddr = packet.paddr as u64;

                core::ptr::write_volatile(*pkt_addr.get_mut(), pkt_paddr);

                // log::trace!(
                //     "pkt vaddr {:>08x} paddr {:>08x}",
                //     packet.as_ptr() as usize,
                //     pkt_paddr
                // );

                let mut hdr_addr: UnsafeCell<*mut u64> = UnsafeCell::new(
                    &(*self.receive_ring.as_ptr().add(rx_index)).read.hdr_addr as *const u64
                        as *mut u64,
                );

                core::ptr::write_volatile(*hdr_addr.get_mut(), 0 as u64);

                self.receive_addrs[rx_index] = Some(packet);
                self.rx_slot[rx_index] = true;
            }
            last_rx_index = rx_index;
            rx_index = wrap_ring(rx_index, self.receive_ring.len());
        }

        if rx_index != self.receive_index {
            // println!(
            //     "Update rdt from {} to {}",
            //     self.read_qreg_idx(IxgbeDmaArrayRegs::Rdt, 0),
            //     rx_index
            // );
            // println!("rx_index {} clean_index {}", rx_index, self.rx_clean_index);
            self.write_qreg_idx(IxgbeDmaArrayRegs::Rdt, 0, rx_index as u64);
            self.receive_index = rx_index;
        }

        let mut reaped = 0;
        let batch = BATCH_SIZE;
        let mut count = 0;
        //println!("reap_queue {} ", reap_queue.len());

        loop {
            // println!("rx_clean_index: {}
            // rx_index: {}
            // self.rx_slot: {:#?}", rx_clean_index, rx_index,self.rx_slot);
            if reap_queue.is_full() {
                break;
            }

            if rx_clean_index == rx_index || count == batch {
                // println!("break; rx_clean_index{} rx_index {}",rx_clean_index, rx_index );
                break;
            }

            let mut desc = unsafe {
                &mut *(self.receive_ring.as_ptr().add(rx_clean_index) as *mut ixgbe_adv_rx_desc)
            };

            let status =
                unsafe { core::ptr::read_volatile(&mut (*desc).wb.upper.status_error as *mut u32) };

            if debug {
                println!("checking status[{}] {:x}", rx_clean_index, status);
            }

            if (status & IXGBE_RXDADV_STAT_DD) == 0 {
                break;
            }
            // log::info!("driver sent rx_clean_index {}", rx_clean_index);
            if ((status & IXGBE_RXDADV_STAT_DD) != 0) && ((status & IXGBE_RXDADV_STAT_EOP) == 0) {
                panic!("increase buffer size or decrease MTU")
            }

            if self.rx_slot[rx_clean_index] {
                if let Some(mut pkt) = self.receive_addrs[rx_clean_index].take() {
                    let length = unsafe {
                        core::ptr::read_volatile(&(*desc).wb.upper.length as *const u16) as usize
                    };
                    //log::info!("length {}", length);

                    //let mut buf = pkt.as_mut_ptr();
                    //let vec = unsafe { Vec::from_raw_parts(buf, length, pkt.capacity()) };
                    //if length <= pkt.len {
                    pkt.len = length;
                    while reap_queue.try_push(&pkt) == false {}
                }
                self.rx_slot[rx_clean_index] = false;
                self.receive_addrs[rx_clean_index] = None;
                reaped += 1;
            } else {
                // log::info!("driver received rx_clean_index @ {:?} on empty slot", rx_clean_index);
            }
            rx_clean_index = wrap_ring(rx_clean_index, self.receive_ring.len());

            count += 1;
        }

        if debug {
            println!("clean_index {}", rx_clean_index);
        }

        //println!("reap_queue_after {}\n", reap_queue.len());

        self.rx_clean_index = rx_clean_index;
    }
}
