//mod maglev;

use crate::device::IxgbeDevice;
use crate::packettool::{ETH_HEADER_LEN, IPV4_PROTO_OFFSET};
use crate::println;
use alloc::boxed::Box;
use alloc::collections::VecDeque;
use alloc::vec::Vec;
use asys::sys_mresolve;
use b2histogram::Base2Histogram;
use byteorder::{BigEndian, ByteOrder};
use core::alloc::Layout;
use core::ptr;
use libtime::{rdtsc, sys_ns_loopsleep};
//use sashstore_redleaf::SashStore;

macro_rules! print_hist {
    ($hist: ident) => {
        println!("{}", core::stringify!($hist));

        for bucket in $hist.iter().filter(|b| b.count > 0) {
            println!("({:5}, {:5}): {}", bucket.start, bucket.end, bucket.count);
        }
    };
}

const BATCH_SIZE: usize = 32;
const CPU_MHZ: u64 = 2_600_000_000;

pub fn run_tx_udptest(net: &mut IxgbeDevice, pkt_len: usize, mut debug: bool) -> Result<(), ()> {
    #[cfg(feature = "noop")]
    return Ok(());

    let batch_sz: usize = BATCH_SIZE;
    // let mut packets: VecDeque<(Vec<u8>, u64)> = VecDeque::with_capacity(batch_sz);
    // let mut collect: VecDeque<(Vec<u8>, u64)> = VecDeque::new();
    let mut packets: VecDeque<Vec<u8>> = VecDeque::with_capacity(batch_sz);
    let mut collect: VecDeque<Vec<u8>> = VecDeque::new();

    let mac_data = alloc::vec![
        0x90, 0xe2, 0xba, 0xb3, 0xbd, 0x99, // Dst mac
        // 90:E2:BA:B5:15:75
        0x90, 0xe2, 0xba, 0xb5, 0x15, 0x75, // Src mac
        0x08, 0x00, // Protocol
    ];
    let mut ip_data = alloc::vec![
        0x45, 0x00, 0x00, 0x2e, 0x00, 0x0, 0x0, 0x00, 0x40, 0x11, 0x00, 0x00, 0x0a, 0x0a, 0x03,
        0x01, 0x0a, 0x0a, 0x03, 0x02,
    ];

    let udp_hdr = alloc::vec![0xb2, 0x6f, 0x14, 0x51, 0x00, 0x1a, 0x9c, 0xaf,];

    // pkt_len - header_size
    let mut payload = alloc::vec![0u8; pkt_len - 42];

    payload[0] = b'R';
    payload[1] = b'e';
    payload[2] = b'd';
    payload[3] = b'l';
    payload[4] = b'e';
    payload[5] = b'a';
    payload[6] = b'f';

    let checksum = calc_ipv4_checksum(&ip_data);
    // Calculated checksum is little-endian; checksum field is big-endian
    ip_data[10] = (checksum >> 8) as u8;
    ip_data[11] = (checksum & 0xff) as u8;

    let mut pkt: Vec<u8> = Vec::new();
    pkt.extend(mac_data.iter());
    pkt.extend(ip_data.iter());
    pkt.extend(udp_hdr.iter());
    pkt.extend(payload.iter());

    // for i in 0..batch_sz {
    //     let packet: Vec<u8> = Vec::with_capacity(pkt_len);
    //     let pkt_paddr = unsafe { sys_mresolve(packet.as_ptr() as usize).0 as u64 };
    //     log::info!("pkt {:>08x} paddr {:x}", packet.as_ptr() as u64, pkt_paddr);
    //     packets.push_front((packet, pkt_paddr));
    // }
    for i in 0..batch_sz {
        packets.push_front(pkt.clone());
    }

    let mut append_rdtsc: u64 = 0;
    let mut alloc_count = 0;
    let mut alloc_elapsed = 0;

    let mut sum: usize = 0;
    let mut collect_tx_hist = Base2Histogram::new();

    println!(
        "======== Starting udp transmit test {}B ==========",
        pkt_len
    );

    let runtime = 30;

    let stats_start = net.get_stats();
    let mut loop_count = 0u32;

    let start = rdtsc();
    let end = rdtsc() + runtime * CPU_MHZ;

    loop {
        let ret = net.submit_and_poll(&mut packets, &mut collect, true, false);

        sum += ret;

        collect_tx_hist.record(collect.len() as u64);

        log::trace!("{}: Appending {}", loop_count, collect.len());
        log::trace!("{}: round", loop_count);

        packets.append(&mut collect);

        if packets.len() == 0 {
            alloc_count += 1;

            log::trace!("{}: Allocating new batch", loop_count);
            let alloc_rdstc_start = rdtsc();
            for i in 0..batch_sz {
                packets.push_front(pkt.clone());
            }
            alloc_elapsed += rdtsc() - alloc_rdstc_start;
        }

        // packets.append(&mut collect);

        // if (batch_sz == 1 && packets.len() == 0) || (batch_sz > 1 && packets.len() < batch_sz / 4) {
        //     //println!("allocating new batch");
        //     alloc_count += 1;

        //     let alloc_rdstc_start = rdtsc();
        //     for i in 0..batch_sz {
        //         let packet: Vec<u8> = Vec::with_capacity(pkt_len);
        //         let pkt_paddr = unsafe { sys_mresolve(packet.as_ptr() as usize).0 as u64 };
        //         packets.push_front((packet, pkt_paddr));
        //     }
        //     alloc_elapsed += rdtsc() - alloc_rdstc_start;
        // }

        if rdtsc() > end {
            break;
        }
        loop_count += 1;
    }

    let elapsed = rdtsc() - start;

    let mut stats_end = net.get_stats();

    stats_end.stats_diff(stats_start);

    let adj_runtime = elapsed as f64 / CPU_MHZ as f64;

    if sum > 0 {
        println!("runtime: {:.2} seconds", adj_runtime);
        println!(
            "tx_udptest ({}): Transmitted {} packets took {} cycles (avg = {})",
            pkt_len,
            sum,
            elapsed,
            elapsed as f64 / sum as f64
        );

        println!("Observed Pkts/s: {}", sum as f64 / adj_runtime as f64);

        //println!("packet.len {} collect.len {}", packets.unwrap().len(), collect.unwrap().len());
        let mut collect: VecDeque<Vec<u8>> = VecDeque::new();
        let done = net.poll(&mut collect, false);

        println!("Reaped {} packets", done);

        println!("Device Stats\n{}", stats_end);

        println!(
            "Tx Pkts/s {:.2}",
            stats_end.tx_dma_ok as f64 / adj_runtime as f64
        );

        println!(
            "Number of new allocations {}, took {} cycles (avg = {})",
            alloc_count * batch_sz,
            alloc_elapsed,
            alloc_elapsed as f64 / (alloc_count * batch_sz) as f64
        );
    } else {
        println!("Test failed! No packets transmitted");
    }

    print_hist!(collect_tx_hist);

    println!("+++++++++++++++++++++++++++++++++++++++++++++++++");
    Ok(())
}

pub fn run_rx_udptest(net: &mut IxgbeDevice, pkt_len: usize, debug: bool) -> Result<(), ()> {
    #[cfg(feature = "noop")]
    return Ok(());

    run_rx_udptest_with_delay(net, pkt_len, debug, 0)
}

pub fn run_rx_udptest_with_delay(
    net: &mut IxgbeDevice,
    pkt_len: usize,
    debug: bool,
    delay: usize,
) -> Result<(), ()> {
    #[cfg(feature = "noop")]
    return Ok(());

    let req_pkt_len = pkt_len;
    let pkt_len = 2048;
    let batch_sz: usize = BATCH_SIZE;
    let mut packets: VecDeque<(Vec<u8>, u64)> = VecDeque::with_capacity(batch_sz);
    let mut collect: VecDeque<(Vec<u8>, u64)> = VecDeque::new();

    for i in 0..batch_sz {
        let packet: Vec<u8> = Vec::with_capacity(pkt_len);
        let pkt_paddr = unsafe { sys_mresolve(packet.as_ptr() as usize).0 as u64 };
        log::info!("pkt {:>08x} paddr {:x}", packet.as_ptr() as u64, pkt_paddr);
        packets.push_front((packet, pkt_paddr));
    }

    let mut sum: usize = 0;
    let mut alloc_count = 0;
    let mut alloc_elapsed = 0;

    let mut submit_rx_hist = Base2Histogram::new();
    let mut collect_rx_hist = Base2Histogram::new();

    let mut collect_start = true;
    let mut collect_end = false;
    let mut seq_start: u64 = 0;
    let mut seq_end: u64 = 0;
    let runtime = 30;

    println!(
        "======== Starting udp rx test {}B loop_delay: {} ==========",
        pkt_len, delay
    );

    let stats_start = net.get_stats();
    let start = rdtsc();
    let end = start + runtime * CPU_MHZ;

    loop {
        // We observed that rx performance would slightly improve if we introduce this delay in
        // every loop. The hypothesis is that, some sort of pointer thrashing is happening between
        // the cpu and hardware. This delay was empirically found.
        sys_ns_loopsleep(delay as u64);

        submit_rx_hist.record(packets.len() as u64);

        let ret = net.submit_and_poll2(&mut packets, &mut collect, false, false);

        if debug {
            println!(
                "rx packets.len {} collect.len {} ret {}",
                packets.len(),
                collect.len(),
                ret
            );
        }

        sum += collect.len();
        collect_rx_hist.record(collect.len() as u64);

        /*if collect_start && !collect.is_empty() {
            let pkt = &collect[0];
            dump_packet(pkt);
            seq_start = BigEndian::read_u64(&pkt[42..42+8]);
            collect_start = false;
            collect_end = true;
        }*/

        packets.append(&mut collect);

        if (batch_sz == 1 && packets.len() == 0) || (batch_sz > 1 && packets.len() < batch_sz / 4) {
            //println!("allocating new batch");
            alloc_count += 1;

            let alloc_rdstc_start = rdtsc();
            for i in 0..batch_sz {
                let packet: Vec<u8> = Vec::with_capacity(pkt_len);
                let pkt_paddr = unsafe { sys_mresolve(packet.as_ptr() as usize).0 as u64 };
                packets.push_front((packet, pkt_paddr));
            }
            alloc_elapsed += rdtsc() - alloc_rdstc_start;
        }

        if rdtsc() > end {
            break;
        }
    }

    let elapsed = rdtsc() - start;

    let mut stats_end = net.get_stats();

    stats_end.stats_diff(stats_start);

    let adj_runtime = elapsed as f64 / CPU_MHZ as f64;

    if sum > 0 {
        println!("runtime: {:.2} seconds", adj_runtime);
        println!(
            "rx_udptest (delay: {}ns) : Received {} packets took {} cycles (avg = {})",
            delay,
            sum,
            elapsed,
            elapsed as f64 / sum as f64
        );

        let mut collect: VecDeque<Vec<u8>> = VecDeque::new();
        let done = net.poll(&mut collect, false);

        println!("Reaped {} packets", done);

        println!("Device Stats\n{}", stats_end);

        println!(
            "Rx Pkts/s {:.2}",
            stats_end.rx_dma_ok as f64 / adj_runtime as f64
        );

        println!(
            "Number of new allocations {}, took {} cycles (avg = {})",
            alloc_count,
            alloc_elapsed,
            alloc_elapsed as f64 / alloc_count as f64
        );
    } else {
        println!("Test failed! No packets Received");
    }

    print_hist!(submit_rx_hist);
    print_hist!(collect_rx_hist);

    println!("+++++++++++++++++++++++++++++++++++++++++++++++++");

    Ok(())
}

pub fn dump_packet(pkt: &Vec<u8>) {
    for (i, b) in pkt.iter().enumerate() {
        println!("{:02X} ", b);

        if i > 0 && (i + 1) % 25 == 0 {
            println!("\n");
        }
    }
    println!("\n");
}

/*
static mut SASHSTORE: Option<SashStore> = None;

pub const CAPACITY: usize = (1 << 20) * 1;

pub fn run_sashstoretest(net: &mut IxgbeDevice, pkt_size: u16, capacity: usize) -> Result<()> {
    let batch_sz = BATCH_SIZE;
    let mut rx_packets: VecDeque<Vec<u8>> = VecDeque::with_capacity(batch_sz);
    let mut tx_packets: VecDeque<Vec<u8>> = VecDeque::with_capacity(batch_sz);
    let mut submit_rx_hist = Base2Histogram::new();
    let mut submit_tx_hist = Base2Histogram::new();

    unsafe {
        // SASHSTORE = Some(SashStore::with_capacity((1 << 20)));
        SASHSTORE = Some(SashStore::with_capacity(capacity));
    }

    for i in 0..batch_sz {
        rx_packets.push_front(Vec::with_capacity(2048));
    }

    for (i, v) in rx_packets.iter().enumerate() {
        println!("{} : {:x?}", i, v.as_ptr());
    }

    let mut sum: usize = 0;
    let mut fwd_sum: usize = 0;

    println!("======== Starting sashstore test ==========");
    let stats_start = net.get_stats().unwrap()?;

    let start = rdtsc();
    let end = start + 120 * CPU_MHZ;

    let mut alloc_count = 0;
    let mut alloc_elapsed = 0;

    let mut tx_elapsed = 0;
    let mut rx_elapsed = 0;
    let mut lookup_elapsed = 0;

    let mut submit_rx: usize = 0;
    let mut submit_tx: usize = 0;
    let mut loop_count: usize = 0;

    loop {
        loop_count = loop_count.wrapping_add(1);

        submit_rx += rx_packets.len();
        submit_rx_hist.record(rx_packets.len() as u64);
        //println!("call rx_submit_poll packet {}", packets.len());
        let rx_start = rdtsc();
        let ret = net
            .submit_and_poll(&mut rx_packets, &mut tx_packets, false)
            .unwrap()?;
        rx_elapsed += rdtsc() - rx_start;
        sum += ret;

        let lookup_start = rdtsc();

        for i in 0..tx_packets.len() {
            // Prefetch ahead
            {
                if (i + 1) < tx_packets.len() {
                    let pkt_next = &tx_packets[i + 1];
                    unsafe {
                        let pkt_addr = pkt_next.as_ptr();
                        core::intrinsics::prefetch_read_data(pkt_addr, 3);
                        core::intrinsics::prefetch_read_data(pkt_addr.offset(64), 3);
                        //core::intrinsics::prefetch_read_data(pkt_addr.offset(128), 3);
                    }
                }
            }

            let mut pkt = &mut tx_packets[i];

            //println!(" cur pkt {:x?}\n", pkt.as_ptr());
            if let Some((padding, payload)) = packettool::get_mut_udp_payload(pkt) {
                if let Some(mut sashstore) = unsafe { SASHSTORE.as_mut() } {
                    let payloadptr = payload as *mut _ as *mut u8;
                    let mut payloadvec = unsafe {
                        Vec::from_raw_parts(
                            payloadptr,
                            payload.len(),
                            2048 - padding, // FIXME: Awful
                        )
                    };

                    // println!("Before handle: payloadvec.capacity() = {}, len() = {}", payloadvec.capacity(), payloadvec.len());
                    //let responsevec = unsafe { sashstore.handle_network_request(payloadvec) };
                    sashstore.handle_network_request_simple(&mut payloadvec);

                    // assert!(responsevec.as_ptr() == payloadptr);
                    // println!("Handled: {:x?} -> {:x?}", responsevec.as_ptr(), payloadptr);
                    // println!("After handle: responsevec.capacity() = {}, len() = {}", responsevec.capacity(), responsevec.len());
                    /*if responsevec.as_ptr() != payloadptr {
                        unsafe {
                            ptr::copy(responsevec.as_ptr(), payloadptr, responsevec.len());
                        }
                        println!("copied");
                    }*/

                    // println!("Before set_len: {}", pkt.len());
                    unsafe {
                        //pkt.set_len(padding + responsevec.len());
                        pkt.set_len(padding + payloadvec.len());
                    }
                    // println!("After set_len: padding={}, resposevec.len() = {}, set to {}", padding, responsevec.len(), pkt.len());

                    //packettool::swap_udp_ips(pkt);
                    //packettool::swap_mac(pkt);
                    //packettool::fix_ip_length(pkt);
                    //packettool::fix_ip_checksum(pkt);
                    //packettool::fix_udp_length(pkt);
                    //packettool::fix_udp_checksum(pkt);

                    // println!("To send: {:x?}", pkt);
                } else {
                    println!("No sashstore???");
                }
            } else {
                // println!("Not a UDP packet: {:x?}", &pkt);
            }
        }

        lookup_elapsed += rdtsc() - lookup_start;

        submit_tx += tx_packets.len();
        submit_tx_hist.record(tx_packets.len() as u64);
        let tx_start = rdtsc();
        let ret = net
            .submit_and_poll(&mut tx_packets, &mut rx_packets, true)
            .unwrap()?;
        tx_elapsed += rdtsc() - tx_start;
        fwd_sum += ret;

        //println!("tx: submitted {} collect {}\n", ret, rx_packets.len());

        if rx_packets.len() == 0 && tx_packets.len() < batch_sz * 4 {
            //println!("-> Allocating new rx_ptx batch");
            let alloc_rdstc_start = rdtsc();
            for i in 0..batch_sz {
                rx_packets.push_front(Vec::with_capacity(2048));
            }
            alloc_elapsed += rdtsc() - alloc_rdstc_start;
        }

        if rdtsc() > end {
            break;
        }
    }

    let elapsed = rdtsc() - start;

    let mut stats_end = net.get_stats().unwrap()?;

    stats_end.stats_diff(stats_start);

    let adj_runtime = elapsed as f64 / CPU_MHZ as f64;

    if sum > 0 && fwd_sum > 0 {
        println!("runtime: {:.2} seconds", adj_runtime);

        println!("Received packets: {} forwarded packets: {}", sum, fwd_sum);

        println!(
            "Rx: {} packets took {} cycles (avg = {})",
            sum,
            rx_elapsed,
            rx_elapsed as f64 / sum as f64
        );

        println!(
            "KV lookup: {} packets took {} cycles (avg = {})",
            sum,
            lookup_elapsed,
            lookup_elapsed as f64 / sum as f64
        );

        println!(
            "Tx: {} packets took {} cycles (avg = {})",
            fwd_sum,
            tx_elapsed,
            tx_elapsed as f64 / fwd_sum as f64
        );

        println!(
            "Sashstore: {} packets took {} cycles (avg = {})",
            fwd_sum,
            elapsed,
            elapsed as f64 / fwd_sum as f64
        );

        let done_rx = net.poll(&mut rx_packets, false).unwrap()?;
        let done_tx = net.poll(&mut tx_packets, true).unwrap()?;

        println!("Reaped rx {} packets tx {} packets", done_rx, done_tx);

        println!("Device Stats\n{}", stats_end);

        println!(
            "Tx Pkts/s {:.2}",
            stats_end.tx_dma_ok as f64 / adj_runtime as f64
        );
        println!(
            "Rx Pkts/s {:.2}",
            stats_end.rx_dma_ok as f64 / adj_runtime as f64
        );

        println!(
            "Number of new allocations {}, took {} cycles (avg = {})",
            alloc_count * batch_sz,
            alloc_elapsed,
            alloc_elapsed as f64 / (alloc_count * batch_sz) as f64
        );
    } else {
        println!(
            "Test failed! No packets Forwarded! Rxed {}, Txed {}",
            sum, fwd_sum
        );
    }

    print_hist!(submit_rx_hist);

    print_hist!(submit_tx_hist);

    if let Some(mut sashstore) = unsafe { SASHSTORE.as_mut() } {
        sashstore.print_stats();
        sashstore.print_stats_simple();
    }
    Ok(())
}
*/
/*
pub fn run_fwd_maglevtest(net: &mut IxgbeDevice, pkt_size: u16) -> Result<()> {
    #[cfg(feature = "noop")]
    return Ok(());

    let batch_sz = BATCH_SIZE;
    let mut maglev = maglev::Maglev::new(0..3);
    let mut rx_packets: VecDeque<Vec<u8>> = VecDeque::with_capacity(batch_sz);
    let mut tx_packets: VecDeque<Vec<u8>> = VecDeque::with_capacity(batch_sz);
    let mut submit_rx_hist = Base2Histogram::new();
    let mut submit_tx_hist = Base2Histogram::new();

    let mut sender_mac = alloc::vec![0x90, 0xe2, 0xba, 0xb3, 0x74, 0x81];
    let mut our_mac = alloc::vec![0x90, 0xe2, 0xba, 0xb5, 0x14, 0xcd];

    for i in 0..batch_sz {
        // Attempt to make the buffers align at different offsets - to avoid eviction from L1
        /*let mut vec = unsafe {
            let layout = Layout::from_size_align(4096, 4096)
                    .map_err(|e| panic!("Layout error: {}", e)).unwrap();

            let buf = unsafe {alloc::alloc::alloc(layout) as *mut u8 };
            let mut v: Vec<u8> = unsafe { Vec::from_raw_parts(buf.offset(64 * i as isize), 64, 64) };
            v
        };
        rx_packets.push_front(vec);
        */
        rx_packets.push_front(Vec::with_capacity(2048));
    }

    /*for i in 0..batch_sz {
        println!("buf_addr[{}] = {:x}", i, rx_packets[i].as_ptr() as *const _ as *const u64 as u64);
    }*/

    let mut sum: usize = 0;
    let mut fwd_sum: usize = 0;

    println!("======== Starting maglev test ==========");
    let stats_start = net.get_stats().unwrap()?;

    let start = rdtsc();
    let end = start + 30 * CPU_MHZ;

    let mut alloc_count = 0;
    let mut alloc_elapsed = 0;

    let mut mswap_elapsed = 0;

    let mut tx_elapsed = 0;
    let mut rx_elapsed = 0;

    let mut submit_rx: usize = 0;
    let mut submit_tx: usize = 0;
    let mut loop_count: usize = 0;
    let mut hash_sum: usize = 0;

    let delay = 350;
    loop {
        // sys_ns_loopsleep(delay as u64);

        loop_count = loop_count.wrapping_add(1);

        submit_rx += rx_packets.len();
        submit_rx_hist.record(rx_packets.len() as u64);
        //println!("call rx_submit_poll packet {}", packets.len());
        let rx_start = rdtsc();
        let ret = net
            .submit_and_poll(&mut rx_packets, &mut tx_packets, false)
            .unwrap()?;
        rx_elapsed += rdtsc() - rx_start;
        sum += ret;

        //println!("rx: submitted {} collect {}", ret, tx_packets.len());

        let ms_start = rdtsc();

        for i in 0..tx_packets.len() {
            // Prefetch ahead
            {
                if (i + 2) < tx_packets.len() {
                    let pkt_next = &tx_packets[i + 2];
                    unsafe {
                        let pkt_addr = pkt_next.as_ptr();
                        core::intrinsics::prefetch_read_data(pkt_addr, 3);
                        //core::intrinsics::prefetch_read_data(pkt_addr.offset(64), 3);
                        //core::intrinsics::prefetch_read_data(pkt_addr.offset(128), 3);
                    }
                }
            }

            let mut pkt = &mut tx_packets[i];
            let backend = {
                if let Some(hash) = packettool::get_flowhash(&pkt) {
                    Some(maglev.get_index_from_hash(hash))
                } else {
                    println!("flowhash failed");
                    None
                }
            };

            if let Some(_) = backend {
                unsafe {
                    ptr::copy(
                        our_mac.as_ptr(),
                        pkt.as_mut_ptr().offset(6),
                        our_mac.capacity(),
                    );
                    ptr::copy(
                        sender_mac.as_ptr(),
                        pkt.as_mut_ptr().offset(0),
                        sender_mac.capacity(),
                    );
                }
            };

            //hash_sum = hash_sum.wrapping_add(backend.unwrap());
        }

        mswap_elapsed += rdtsc() - ms_start;

        submit_tx += tx_packets.len();
        submit_tx_hist.record(tx_packets.len() as u64);
        let tx_start = rdtsc();
        let ret = net
            .submit_and_poll(&mut tx_packets, &mut rx_packets, true)
            .unwrap()?;
        tx_elapsed += rdtsc() - tx_start;
        fwd_sum += ret;

        //println!("tx: submitted {} collect {}\n", ret, rx_packets.len());

        if rx_packets.len() == 0 && tx_packets.len() < batch_sz * 4 {
            //println!("-> Allocating new rx_ptx batch");
            let alloc_rdstc_start = rdtsc();
            for i in 0..batch_sz {
                rx_packets.push_front(Vec::with_capacity(2048));
            }
            alloc_elapsed += rdtsc() - alloc_rdstc_start;
        }

        if rdtsc() > end {
            break;
        }
    }

    let elapsed = rdtsc() - start;

    let mut stats_end = net.get_stats().unwrap()?;

    stats_end.stats_diff(stats_start);

    let adj_runtime = elapsed as f64 / CPU_MHZ as f64;

    if sum > 0 && fwd_sum > 0 {
        println!("runtime: {:.2} seconds", adj_runtime);

        println!("Received packets: {} forwarded packets: {}", sum, fwd_sum);

        println!(
            "Rx: {} packets took {} cycles (avg = {})",
            sum,
            rx_elapsed,
            rx_elapsed as f64 / sum as f64
        );

        println!(
            "mac_swap: {} packets took {} cycles (avg = {})",
            sum,
            mswap_elapsed,
            mswap_elapsed as f64 / sum as f64
        );

        println!(
            "Tx: {} packets took {} cycles (avg = {})",
            fwd_sum,
            tx_elapsed,
            tx_elapsed as f64 / fwd_sum as f64
        );

        println!(
            "maglev_fwd : Forwarding {} packets took {} cycles (avg = {})",
            fwd_sum,
            elapsed,
            elapsed as f64 / fwd_sum as f64
        );

        let done_rx = net.poll(&mut rx_packets, false).unwrap()?;
        let done_tx = net.poll(&mut tx_packets, true).unwrap()?;

        println!("Reaped rx {} packets tx {} packets", done_rx, done_tx);

        println!("Device Stats\n{}", stats_end);

        println!(
            "Tx Pkts/s {:.2}",
            stats_end.tx_dma_ok as f64 / adj_runtime as f64
        );
        println!(
            "Rx Pkts/s {:.2}",
            stats_end.rx_dma_ok as f64 / adj_runtime as f64
        );

        println!(
            "Number of new allocations {}, took {} cycles (avg = {})",
            alloc_count * batch_sz,
            alloc_elapsed,
            alloc_elapsed as f64 / (alloc_count * batch_sz) as f64
        );
    } else {
        println!(
            "Test failed! No packets Forwarded! Rxed {}, Txed {}",
            sum, fwd_sum
        );
    }

    print_hist!(submit_rx_hist);

    print_hist!(submit_tx_hist);

    maglev.dump_stats();

    println!("+++++++++++++++++++++++++++++++++++++++++++++++++");

    Ok(())
}
*/
pub fn run_fwd_udptest(net: &mut IxgbeDevice, pkt_len: u16, debug: bool) -> Result<(), ()> {
    run_fwd_udptest_with_delay(net, pkt_len, 0)
}

pub fn run_fwd_udptest_with_delay(
    net: &mut IxgbeDevice,
    pkt_len: u16,
    delay: u64,
) -> Result<(), ()> {
    #[cfg(feature = "noop")]
    return Ok(());

    let batch_sz = BATCH_SIZE;
    let mut rx_packets: VecDeque<Vec<u8>> = VecDeque::with_capacity(batch_sz);
    let mut tx_packets: VecDeque<Vec<u8>> = VecDeque::with_capacity(batch_sz);
    let mut submit_rx_hist = Base2Histogram::new();
    let mut submit_tx_hist = Base2Histogram::new();

    let sender_mac = alloc::vec![
        0x90, 0xe2, 0xba, 0xb2, 0xa6, 0xb1, // Dst mac
    ];
    let our_mac = alloc::vec![
        // 90:E2:BA:B5:15:75
        0x90, 0xe2, 0xba, 0xb2, 0xa6, 0xb1, // Src mac
    ];

    for i in 0..batch_sz {
        rx_packets.push_front(Vec::with_capacity(1024));
    }

    let mut sum: usize = 0;
    let mut fwd_sum: usize = 0;

    let mut append_rdtsc: u64 = 0;
    let mut alloc_count = 0;
    let mut alloc_elapsed = 0;

    let mut tx_elapsed = 0;
    let mut rx_elapsed = 0;

    let mut mswap_elapsed = 0;
    let mut bswap_elapsed = 0;

    let mut submit_rx: usize = 0;
    let mut submit_tx: usize = 0;
    let runtime = 30;

    println!(
        "======== Starting udp fwd test (delay {} ns)==========",
        delay
    );

    let stats_start = net.get_stats();

    let start = rdtsc();
    let end = start + runtime * CPU_MHZ;

    // 1. Rx a bunch of packets
    // 2. Swap the MAC headers, IP headers
    // 3. Tx the received packets
    loop {
        sys_ns_loopsleep(delay);
        submit_rx += rx_packets.len();
        submit_rx_hist.record(rx_packets.len() as u64);
        //println!("call rx_submit_poll packet {}", packets.len());
        let rx_start = rdtsc();
        let ret = net.submit_and_poll(&mut rx_packets, &mut tx_packets, false, false);
        rx_elapsed += rdtsc() - rx_start;
        sum += ret;

        println!("rx: submitted {} collect {}", ret, tx_packets.len());
        if tx_packets.len() > 0 {
            log::info!(
                "tx_packets {} packet {:#?}",
                tx_packets.len(),
                tx_packets[0].as_ptr(),
            );
        }

        let ms_start = rdtsc();
        for pkt in tx_packets.iter_mut() {
            /*for i in 0..6 {
                (pkt).swap(i, 6 + i);
            }*/
            unsafe {
                ptr::copy(
                    our_mac.as_ptr(),
                    pkt.as_mut_ptr().offset(6),
                    our_mac.capacity(),
                );
                ptr::copy(
                    sender_mac.as_ptr(),
                    pkt.as_mut_ptr().offset(0),
                    sender_mac.capacity(),
                );
            }
        }
        mswap_elapsed += rdtsc() - ms_start;

        submit_tx += tx_packets.len();
        submit_tx_hist.record(tx_packets.len() as u64);

        let tx_start = rdtsc();
        let ret = net.submit_and_poll(&mut tx_packets, &mut rx_packets, true, false);

        tx_elapsed += rdtsc() - tx_start;
        fwd_sum += ret;

        //println!("tx: submitted {} collect {}\n", ret, rx_packets.len());

        if rx_packets.len() == 0 && tx_packets.len() < batch_sz * 4 {
            //println!("-> Allocating new rx_ptx batch");
            alloc_count += 1;

            let alloc_rdstc_start = rdtsc();

            for i in 0..batch_sz {
                rx_packets.push_front(Vec::with_capacity(2048));
            }
            alloc_elapsed += rdtsc() - alloc_rdstc_start;
        }

        if rdtsc() > end {
            break;
        }
    }

    let elapsed = rdtsc() - start;

    let mut stats_end = net.get_stats();

    stats_end.stats_diff(stats_start);

    let adj_runtime = elapsed as f64 / CPU_MHZ as f64;

    if sum > 0 && fwd_sum > 0 {
        println!("runtime: {:.2} seconds", adj_runtime);

        println!("Received packets: {} forwarded packets: {}", sum, fwd_sum);

        println!(
            "Rx: {} packets took {} cycles (avg = {})",
            sum,
            rx_elapsed,
            rx_elapsed as f64 / sum as f64
        );

        println!(
            "mac_swap: {} packets took {} cycles (avg = {})",
            sum,
            mswap_elapsed,
            mswap_elapsed as f64 / sum as f64
        );

        println!(
            "Tx: {} packets took {} cycles (avg = {})",
            fwd_sum,
            tx_elapsed,
            tx_elapsed as f64 / fwd_sum as f64
        );

        println!(
            "fwd_udptest: Forwarding {} packets took {} cycles (avg = {})",
            fwd_sum,
            elapsed,
            elapsed as f64 / fwd_sum as f64
        );

        //println!("packet.len {} collect.len {}", packets.unwrap().len(), collect.unwrap().len());
        let done_rx = net.poll(&mut rx_packets, false);
        let done_tx = net.poll(&mut tx_packets, true);

        println!("Reaped rx {} packets tx {} packets", done_rx, done_tx);

        println!(
            "Number of new allocations {}, took {} cycles (avg = {})",
            alloc_count * batch_sz,
            alloc_elapsed,
            alloc_elapsed as f64 / (alloc_count * batch_sz) as f64
        );
    } else {
        println!(
            "Test failed! No packets Forwarded! Rxed {}, Txed {}",
            sum, fwd_sum
        );
    }

    println!("Device Stats\n{}", stats_end);

    println!(
        "Tx Pkts/s {:.2}",
        stats_end.tx_dma_ok as f64 / adj_runtime as f64
    );
    println!(
        "Rx Pkts/s {:.2}",
        stats_end.rx_dma_ok as f64 / adj_runtime as f64
    );

    print_hist!(submit_rx_hist);
    print_hist!(submit_tx_hist);

    println!("+++++++++++++++++++++++++++++++++++++++++++++++++");

    //dev.dump_tx_descs();
    Ok(())
}

fn calc_ipv4_checksum(ipv4_header: &[u8]) -> u16 {
    assert!(ipv4_header.len() % 2 == 0);
    let mut checksum = 0;
    for i in 0..ipv4_header.len() / 2 {
        if i == 5 {
            // Assume checksum field is set to 0
            continue;
        }
        checksum += (u32::from(ipv4_header[i * 2]) << 8) + u32::from(ipv4_header[i * 2 + 1]);
        if checksum > 0xffff {
            checksum = (checksum & 0xffff) + 1;
        }
    }
    !(checksum as u16)
}
