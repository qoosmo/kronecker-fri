//! One inner product and one Hadamard check on committed tables by two routes that share the
//! commitments (one group per table) and the proof engine (`affine`): the sumcheck-free
//! statement itself (`sf`), and a sumcheck followed by one evaluation of a random combination of
//! the tables at the sumcheck point (`sc`, a batched opening). Commitments excluded.
//! Configuration KF-8 (rate 1/4, arity 8, caps of 128 nodes, l = n - 8), 148 queries, 32-byte
//! salts, F_{p^2}. Single-threaded.
//!   cargo run --release --example primitives_bench -- [n ...]      (default: 12 14 16 18 20)
use kronecker_fri::field::{Fp, Fp2};
use kronecker_fri::pcs::Params;
use kronecker_fri::sumcheck::{
    commit_one, prove_had_sc, prove_had_sf, prove_ip_sc, prove_ip_sf, verify_had_sc, verify_had_sf,
    verify_ip_sc, verify_ip_sf,
};
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
        vec![12, 14, 16, 18, 20]
    } else {
        args
    };
    println!(
        "n,ip_sf_prove_ms,ip_sf_verify_ms,ip_sf_kib,ip_sc_prove_ms,ip_sc_verify_ms,ip_sc_kib,had_sf_prove_ms,had_sf_verify_ms,had_sf_kib,had_sc_prove_ms,had_sc_verify_ms,had_sc_kib"
    );
    for n in ns {
        let p = Params::recommended(n, 148, 32);
        let reps = if n >= 20 { 3 } else { 7 };
        let mut s = 0x5EED_u64 + n as u64;
        let mut next = || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            Fp::new(s)
        };
        let a: Vec<Fp> = (0..p.big_n()).map(|_| next()).collect();
        let b: Vec<Fp> = (0..p.big_n()).map(|_| next()).collect();
        let c: Vec<Fp> = a.iter().zip(&b).map(|(&x, &y)| x * y).collect();
        let ga = commit_one(&p, &a).unwrap();
        let gb = commit_one(&p, &b).unwrap();
        let gc = commit_one(&p, &c).unwrap();
        let (ra, rb, rc) = (ga.tree.root(), gb.tree.root(), gc.tree.root());
        let mut t = vec![vec![]; 8];
        let mut sz = [0usize; 4];
        for _ in 0..reps {
            let t0 = Instant::now();
            let (sv, pr) = prove_ip_sf::<Fp2>(&p, [&ga, &gb]).unwrap();
            t[0].push(ms(t0));
            let t0 = Instant::now();
            assert_eq!(verify_ip_sf(&p, [ra, rb], sv, &pr), Ok(()));
            t[1].push(ms(t0));
            sz[0] = pr.size_bytes();

            let t0 = Instant::now();
            let (sv, pr) = prove_ip_sc::<Fp2>(&p, [&ga, &gb]).unwrap();
            t[2].push(ms(t0));
            let t0 = Instant::now();
            assert_eq!(verify_ip_sc(&p, [ra, rb], sv, &pr), Ok(()));
            t[3].push(ms(t0));
            sz[1] = pr.size_bytes();

            let t0 = Instant::now();
            let pr = prove_had_sf::<Fp2>(&p, [&ga, &gb, &gc]).unwrap();
            t[4].push(ms(t0));
            let t0 = Instant::now();
            assert_eq!(verify_had_sf(&p, [ra, rb, rc], &pr), Ok(()));
            t[5].push(ms(t0));
            sz[2] = pr.size_bytes();

            let t0 = Instant::now();
            let pr = prove_had_sc::<Fp2>(&p, [&ga, &gb, &gc]).unwrap();
            t[6].push(ms(t0));
            let t0 = Instant::now();
            assert_eq!(verify_had_sc(&p, [ra, rb, rc], &pr), Ok(()));
            t[7].push(ms(t0));
            sz[3] = pr.size_bytes();
        }
        let m: Vec<f64> = t.into_iter().map(median).collect();
        let k = |b: usize| b as f64 / 1024.0;
        println!(
            "{n},{:.2},{:.3},{:.1},{:.2},{:.3},{:.1},{:.2},{:.3},{:.1},{:.2},{:.3},{:.1}",
            m[0],
            m[1],
            k(sz[0]),
            m[2],
            m[3],
            k(sz[1]),
            m[4],
            m[5],
            k(sz[2]),
            m[6],
            m[7],
            k(sz[3])
        );
    }
}
