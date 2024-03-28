use std::time::{Duration, Instant};
use cap::Cap;

use smt_log_parser::{LogParser, Z3Parser};

#[global_allocator]
static ALLOCATOR: Cap<std::alloc::System> = Cap::new(std::alloc::System, usize::max_value());

#[test]
fn parse_all_logs() {
    let mem = std::env::var("SLP_MEMORY_LIMIT_GB").ok().and_then(|mem| mem.parse().ok());
    // Default to limit of 16GiB.
    let mem = mem.unwrap_or(16) * 1024 * 1024 * 1024;
    ALLOCATOR.set_limit(mem).unwrap();
    std::env::set_var("SLP_TEST_MODE", "true");

    let mut all_logs: Vec<_> = std::fs::read_dir("../logs").unwrap().map(|r| r.unwrap()).collect();
    all_logs.sort_by_key(|dir| dir.path());
    for log in all_logs {
        // Put things in a thread to isolate memory usage more than the default.
        let t = std::thread::spawn(move || {
            let filename = log.path();
            let (metadata, mut parser) = Z3Parser::from_file(&filename).unwrap();
            let file_size = metadata.len();
            let file_size_kb = file_size / 1024;

            // Gives 100 millis per MB (or 100 secs per GB)
            let timeout = Duration::from_millis(500 + (file_size_kb / 10));
            println!(
                "Parsing {} ({} MB) with timeout of {timeout:?}",
                filename.display(),
                file_size_kb / 1024
            );
            // Some memory usage is still left over from previous loop iterations, so we'll need to subtract that.
            let start_mem = memory_stats::memory_stats().unwrap().physical_mem as u64;
            // TODO: optimize memory usage and reduce `max_mem`.
            let max_mem = start_mem + 2 * file_size + 1024 * 1024 * 1024;
            let now = Instant::now();

            parser.process_check_every(Duration::from_millis(100), |_, _| {
                assert!(now.elapsed() < timeout, "Parsing took longer than timeout");
                let physical_mem = memory_stats::memory_stats().unwrap().physical_mem as u64;
                assert!(
                    physical_mem < max_mem,
                    "Memory usage was {} MB, but file size was {} MB (max mem {} MB)",
                    physical_mem / 1024 / 1024,
                    file_size / 1024 / 1024,
                    max_mem / 1024 / 1024
                );
                true
            });
            let elapsed = now.elapsed();
            println!("Finished parsing in {elapsed:?} ({} kB/ms)", file_size_kb as u128 / elapsed.as_millis());
            println!();
            drop(parser);
        });
        t.join().unwrap();
    }
}
