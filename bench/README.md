# Benchmark data

Raw output of the benchmarks reported in the paper (§10 and §11.3). All files were produced in one session on one machine:
one core of an Intel Xeon at 2.80 GHz (cloud VM, 2 vCPUs, 7 GB RAM), Rust 1.95.0, release profile with fat LTO and one codegen unit.
Times are medians (11 runs for n ≤ 18, 5 for n = 20, 3 for n = 22; 21 runs for verification).

| File | Command | Paper |
|---|---|---|
| `scaling.csv` | `cargo run --release --example bench -- scaling` | Tables 3 and 6 |
| `breakdown.csv` | `... -- breakdown` | Table 4 |
| `fields.csv` | `... -- fields` | Table 5 |
| `stop.csv` | `... -- stop` | Table 7 |
| `params.csv` | `... -- params` | Table 8 |
| `kbfold_scaling.csv` | `cargo run --release --example bench -- scaling` in [qoosmo/kbfold](https://github.com/qoosmo/kbfold) `rust/` | Table 3 (KBFold and baseline columns) |

Timings of identical work vary by about 10–20% between runs on this shared machine; proof sizes are exact.
