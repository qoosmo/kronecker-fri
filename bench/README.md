# Benchmark data

Raw output of the benchmarks reported in the paper (§10 and §11.3). All files were produced in one session on one machine:
one core of an Intel Xeon at 2.10 GHz (cloud VM, 2 vCPUs, 7 GB RAM), Rust 1.95.0, release profile with fat LTO and one codegen unit.
Times are medians (11 runs for n ≤ 18, 5 for n = 20, 3 for n = 22 and for `arity`, `stop` and `params`; 21 runs for verification).

Configurations: **KF-2** = arity 2, no caps, ℓ = n − 4 (`config = v1`); **KF-8** = arity 8, caps of 128 nodes, ℓ = n − 8 (`config = v2`). In `arity.csv`, `fold_log` = k (arity 2^k) and `cap_log` = c (caps of 2^c nodes).

| File | Command | Paper |
|---|---|---|
| `scaling.csv` | `cargo run --release --example bench -- scaling` | Tables 3 (KF-2) and 5 (KF-8) |
| `arity.csv` | `... -- arity` | Table 4 |
| `breakdown.csv` | `... -- breakdown` | Table 6 |
| `stop.csv` | `... -- stop` | Table 7 |
| `params.csv` | `... -- params` | Table 8 |
| `ip.csv` | `cargo run --release --example ip_bench` (KF-8, 148 queries, 32-byte salts, F_{p^2}; a later session on the same machine type) | research note `notes/inner-product`, §4 |
| `kbfold_scaling.csv` | `cargo run --release --example bench -- scaling` in [qoosmo/kbfold](https://github.com/qoosmo/kbfold) `rust/` | Table 3 (KBFold and baseline columns) |

Timings of identical work vary by about 10–20% between runs on this shared machine; proof sizes are exact.
