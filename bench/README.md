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
| `ip.csv` | `cargo run --release --example ip_bench` (KF-8, 148 queries, 32-byte salts, F_{p^2}; a later session on the same machine type) | research note `notes/inner-product`, §4 (evaluation, inner product and Hadamard check) |
| `batch.csv` | `cargo run --release --example batch_bench` (KF-8, 148 queries, 32-byte salts, F_{p^2}) | research note `notes/inner-product`, §4 (one batched proof against four separate proofs) |
| `r1cs.csv` | `cargo run --release --example r1cs_bench` (KF-8, 148 queries, 32-byte salts, F_{p^2}; same session as `spartan.csv`) | research note `notes/inner-product`, §5 (R1CS prototype) |
| `spartan.csv` | `cargo run --release --example spartan_bench` (Spartan core: two sumchecks and one Π_KF opening; same configuration) | research note `notes/inner-product`, §5 (comparison with a sumcheck-based argument) |
| `primitives.csv` | `cargo run --release --example primitives_bench` (one inner product and one Hadamard check, sumcheck-free (`sf`) and sumcheck + batched opening (`sc`), same commitments and engine; same configuration) | research note `notes/inner-product`, §6 (the two routes) |
| `merkle_format.csv` | `ip_bench` (KF columns) built at three versions and run interleaved: one-byte prefixes with one keyed call per salt, prefixes with a salt stream, BLAKE3 keys with a salt stream; means of two medians | Table `tab:exp-hash` (§10, Merkle hashing) |
| `parallel.csv` | `ip_bench` (KF columns) built without and with `--features parallel`, run interleaved on the 2-vCPU machine of `merkle_format.csv`; means of two medians | not in the papers (engineering) |
| `kbfold_scaling.csv` | `cargo run --release --example bench -- scaling` in [qoosmo/kbfold](https://github.com/qoosmo/kbfold) `rust/` | Table 3 (KBFold and baseline columns) |

The Merkle trees were made faster after these recordings (one salt stream per tree, and domain separation by BLAKE3 keys instead of one-byte prefixes; see CHANGELOG and paper §10.7). All files except `merkle_format.csv` were recorded with the earlier format; `merkle_format.csv` compares the three formats in one session on another machine (Intel Xeon at 2.80 GHz).

Timings of identical work vary by about 10–20% between runs on this shared machine; proof sizes are exact.
