use crate::println;
use crate::rdtsc;
use crate::NvmeDevice;
use alloc::collections::VecDeque;
use alloc::vec::Vec;
use b2histogram::Base2Histogram;
use libtime::sys_ns_loopsleep;

fn run_blocktest_raw(
    dev: &mut NvmeDevice,
    runtime: u64,
    batch_sz: u64,
    is_write: bool,
    is_random: bool,
) {
    run_blocktest_raw_with_delay(dev, runtime, batch_sz, is_write, is_random, 0);
}

pub fn run_blocktest_raw_with_delay(
    dev: &mut NvmeDevice,
    runtime: u64,
    batch_sz: u64,
    is_write: bool,
    is_random: bool,
    delay: u64,
) {
    let req: Vec<u8>;
    if is_write {
        req = alloc::vec![0xdeu8; 4096];
    } else {
        req = alloc::vec![0u8; 4096];
    }

    let mut submit: VecDeque<Vec<u8>> = VecDeque::with_capacity(batch_sz as usize);
    let mut collect: VecDeque<Vec<u8>> = VecDeque::new();

    let _block_num: u64 = 0;

    for _i in 0..batch_sz {
        let req1 = req.clone();
        //println!("req 0x{:08x}", req1.as_ptr() as u64);
        submit.push_back(req1);
    }

    /*println!(
        "submit ptr {:08x} collect ptr 0x{:08x}",
        &submit as *mut _ as *mut u64 as u64, &collect as *mut _ as *mut u64 as u64
    );*/
    //if let Some(device) = dev.as_mut() {
    //let dev: &mut NvmeDevice = device;

    let mut submit_start = 0;
    let mut submit_elapsed = 0;
    let _poll_start = 0;
    let _poll_elapsed = 0;
    let mut count = 0;
    let mut alloc_count = 0;

    let mut submit_hist = Base2Histogram::new();
    let mut poll_hist = Base2Histogram::new();
    let mut ret = 0;

    println!(
        "======== Starting {}{} test (delay {})  ==========",
        if is_random { "rand" } else { "" },
        if is_write { "write" } else { "read" },
        delay
    );

    let tsc_start = rdtsc();
    let tsc_end = tsc_start + runtime * 2_400_000_000;

    loop {
        count += 1;
        submit_start = rdtsc();
        //println!("submit and poll raw count {}", count);
        ret = dev.submit_and_poll_raw(&mut submit, &mut collect, is_write, is_random);
        submit_elapsed += rdtsc() - submit_start;

        submit_hist.record(ret as u64);

        poll_hist.record(collect.len() as u64);

        //println!("Append # {} finished blocks {}", count, collect.len());
        submit.append(&mut collect);

        if submit.is_empty() {
            alloc_count += 1;
            //println!("allocating new batch at count {}", count);
            for _i in 0..batch_sz {
                submit.push_back(req.clone());
            }
        }

        if rdtsc() > tsc_end {
            break;
        }
        sys_ns_loopsleep(delay);
    }

    let elapsed = rdtsc() - tsc_start;

    let adj_runtime = elapsed as f64 / 2_400_000_000_f64;

    let (sub, comp) = dev.stats.get_stats();

    println!("Polling ....");

    let done = dev.poll_raw(&mut collect);

    println!("Poll: Reaped {} requests", done);
    println!("submit {} requests", submit.len());
    println!("collect {} requests", collect.len());

    println!("runtime: {:.2} seconds", adj_runtime);
    println!("total sub {} comp {}", sub, comp);

    println!(
        "submitted {:.2} K IOPS completed {:.2} K IOPS",
        sub as f64 / adj_runtime as f64 / 1_000_f64,
        comp as f64 / adj_runtime as f64 / 1_000_f64
    );
    println!(
        "submit_and_poll_rref took {} cycles (avg {} cycles)",
        submit_elapsed,
        submit_elapsed / count
    );

    println!("Number of new allocations {}", alloc_count * batch_sz);

    for hist in alloc::vec![submit_hist, poll_hist] {
        println!("hist:");
        // Iterate buckets that have observations
        for bucket in hist.iter().filter(|b| b.count > 0) {
            println!("({:5}, {:5}): {}", bucket.start, bucket.end, bucket.count);
            println!("\n");
        }
    }
    println!("++++++++++++++++++++++++++++++++++++++++++++++++++++");
    //}
}

/*
fn run_blocktest(dev: &Nvme, runtime: u64, batch_sz: u64, is_write: bool) {
    let buffer: Vec<u8>;
    if is_write {
        buffer = alloc::vec![0xbau8; 4096];
    } else {
        buffer = alloc::vec![0u8; 4096];
    }

    let _block_size = buffer.len();
    let breq: BlockReq = BlockReq::new(0, 8, buffer);
    let mut submit: VecDeque<BlockReq> = VecDeque::with_capacity(batch_sz as usize);
    let mut collect: VecDeque<BlockReq> = VecDeque::new();

    let mut block_num: u64 = 0;

    for _i in 0..batch_sz {
        let mut breq = breq.clone();
        breq.block = block_num;
        block_num = block_num.wrapping_add(1);
        submit.push_back(breq.clone());
    }

    if let Some(device) = dev.device.borrow_mut().as_mut() {
        let dev: &mut NvmeDev = device;

        let mut submit_start = 0;
        let mut submit_elapsed = 0;
        let _poll_start = 0;
        let _poll_elapsed = 0;
        let mut count = 0;

        let mut submit_hist = Base2Histogram::new();
        let mut poll_hist = Base2Histogram::new();
        let mut ret = 0;

        let tsc_start = rdtsc();
        let tsc_end = tsc_start + runtime * 2_400_000_000;

        loop {
            count += 1;
            submit_start = rdtsc();
            ret = dev.submit_and_poll(&mut submit, &mut collect, is_write);
            submit_elapsed += rdtsc() - submit_start;

            submit_hist.record(ret as u64);

            poll_hist.record(collect.len() as u64);

            submit.append(&mut collect);

            if submit.is_empty() {
                //println!("allocating new batch");
                for _i in 0..batch_sz {
                    let mut breq = breq.clone();
                    breq.block = block_num;
                    block_num = block_num.wrapping_add(1);
                    submit.push_back(breq.clone());
                }
            }

            for b in submit.iter_mut() {
                b.block = block_num;
                block_num = block_num.wrapping_add(1);
            }

            if rdtsc() > tsc_end {
                break;
            }
            sys_ns_loopsleep(2000);
        }

        let (sub, comp) = dev.get_stats();
        println!(
            "runtime {} submitted {:.2} K IOPS completed {:.2} K IOPS",
            runtime,
            sub as f64 / runtime as f64 / 1_000_f64,
            comp as f64 / runtime as f64 / 1_000_f64
        );
        println!(
            "run_blocktest loop {} submit_and_poll took {} cycles (avg {} cycles)",
            count,
            submit_elapsed,
            submit_elapsed / count
        );

        for hist in alloc::vec![poll_hist] {
            println!("hist:");
            // Iterate buckets that have observations
            for bucket in hist.iter().filter(|b| b.count > 0) {
                print!("({:5}, {:5}): {}", bucket.start, bucket.end, bucket.count);
                print!("\n");
            }
        }
    }
}
*/
