use criterion::{black_box, criterion_group, criterion_main, Criterion};
use wasm_parser::{parse, read_wasm};

macro_rules! test_file {
    ($fs_name:expr) => {{
        let file = read_wasm!(&format!("test_files/{}", $fs_name));
        file
    }};
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("arithmetic", |b| {
        let arithmetic_fs = test_file!("arithmetic.wasm");
        b.iter(|| parse(arithmetic_fs.clone()).unwrap())
    });
    c.bench_function("gcd", |b| {
        let gcd_fs = test_file!("gcd.wasm");
        b.iter(|| parse(gcd_fs.clone()).unwrap())
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
