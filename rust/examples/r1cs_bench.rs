//! The sumcheck-free R1CS argument (`r1cs`) on the test instances of `r1cs::sample_instance`:
//! N/2 constraints of the form (A z)_i (B z)_i = z_{N/2+i}, two nonzero entries per row of A and
//! B, two public inputs.  Configuration KF-8 (rate 1/4, arity 8, caps of 128 nodes,
//! l = n - 8, at least 1), 148 queries, 32-byte salts, F_{p^2}.  Single-threaded.
//!   cargo run --release --example r1cs_bench -- [n ...]      (default: 10 12 14 16)
use kronecker_fri::affine::affine_words;
use kronecker_fri::field::Fp2;
use kronecker_fri::pcs::Params;
use kronecker_fri::r1cs::{index, prove_r1cs, sample_instance, verify_r1cs};
use std::time::Instant;

fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    v[v.len() / 2]
}

fn ms(t: Instant) -> f64 {
    t.elapsed().as_secs_f64() * 1e3
}

fn main() {
    let args: Vec<usize> = std::env::args()
        .skip(1)
        .filter_map(|a| a.parse().ok())
        .collect();
    let ns = if args.is_empty() {
        vec![10, 12, 14, 16]
    } else {
        args
    };
    println!("n,constraints,words,index_ms,prove_ms,verify_ms,proof_kib");
    for n in ns {
        let p = Params::recommended(n, 148, 32);
        let reps = if n >= 16 { 3 } else { 5 };
        let (r, x, wit) = sample_instance(n, 2, 2, 99 + n as u64);
        let t = Instant::now();
        let idx = index(&p, &r, &[1u8; 32]);
        let tidx = ms(t);
        let (mut pv, mut vv, mut size) = (vec![], vec![], 0);
        for _ in 0..reps {
            let t = Instant::now();
            let pr = prove_r1cs::<Fp2>(&p, &r, &idx, &x, &wit, &[2u8; 32]);
            pv.push(ms(t));
            let t = Instant::now();
            assert_eq!(verify_r1cs(&p, &r, &idx.roots, &x, &pr), Ok(()));
            vv.push(ms(t));
            size = pr.size_bytes();
        }
        let words = affine_words(&kronecker_fri::r1cs::statements_for_count::<Fp2>(&r, &x));
        println!(
            "{n},{},{words},{tidx:.1},{:.1},{:.2},{:.1}",
            1usize << (n - 1),
            median(pv),
            median(vv),
            size as f64 / 1024.0
        );
    }
}
