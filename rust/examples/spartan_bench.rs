//! Baseline for the research note (Section 5.3): the core of a Spartan-style R1CS argument
//! (`spartan`: two sumchecks and one Pi_KF opening of the witness, verifier linear in the number
//! of nonzero entries) on the instances of `r1cs::sample_instance`, with the configuration of
//! `r1cs_bench`: KF-8 (rate 1/4, arity 8, caps of 128 nodes, l = n - 8, at least 1), 148
//! queries, 32-byte salts, F_{p^2}. Single-threaded.
//!   cargo run --release --example spartan_bench -- [n ...]      (default: 10 12 14 16 18 20)
use kronecker_fri::field::Fp2;
use kronecker_fri::pcs::Params;
use kronecker_fri::r1cs::sample_instance;
use kronecker_fri::spartan::{prove_spartan, verify_spartan};
use std::time::Instant;

fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    v[v.len() / 2]
}

fn main() {
    let args: Vec<usize> = std::env::args()
        .skip(1)
        .filter_map(|a| a.parse().ok())
        .collect();
    let ns = if args.is_empty() {
        vec![10, 12, 14, 16, 18, 20]
    } else {
        args
    };
    println!("n,constraints,commit_ms,sumcheck_ms,open_ms,prove_ms,verify_ms,proof_kib");
    for n in ns {
        let p = Params::recommended(n, 148, 32);
        let reps = if n >= 18 { 3 } else { 5 };
        let (r, x, wit) = sample_instance(n, 2, 2, 99 + n as u64);
        let (mut cv, mut sv, mut ov, mut pv, mut vv, mut size) =
            (vec![], vec![], vec![], vec![], vec![], 0);
        for _ in 0..reps {
            let t = Instant::now();
            let (pf, tm) = prove_spartan::<Fp2>(&p, &r, &x, &wit).unwrap();
            pv.push(t.elapsed().as_secs_f64() * 1e3);
            cv.push(tm.commit * 1e3);
            sv.push(tm.sumchecks * 1e3);
            ov.push(tm.open * 1e3);
            let t = Instant::now();
            assert_eq!(verify_spartan(&p, &r, &x, &pf), Ok(()));
            vv.push(t.elapsed().as_secs_f64() * 1e3);
            size = pf.size_bytes();
        }
        println!(
            "{n},{},{:.1},{:.1},{:.1},{:.1},{:.2},{:.1}",
            1usize << (n - 1),
            median(cv),
            median(sv),
            median(ov),
            median(pv),
            median(vv),
            size as f64 / 1024.0
        );
    }
}
