//! Cost of the inner-product protocol Pi_IP and of the Hadamard check Pi_Had against one
//! evaluation opening Pi_KF, with the
//! recommended configuration KF-8 (rate 1/4, arity 8, caps of 128 nodes, l = n - 8), 148 queries,
//! 32-byte salts, over F_{p^2}.  Single-threaded.
//!   cargo run --release --example ip_bench -- [n ...]      (default: 12 14 16 18 20)
use kronecker_fri::field::{ExtField, Fp, Fp2};
use kronecker_fri::had::{prove_had, verify_had};
use kronecker_fri::ip::{commit_table_form, prove_ip, verify_ip};
use kronecker_fri::pcs::{Params, open, verify};
use std::time::Instant;

struct Rng(u64);
impl Rng {
    fn fp(&mut self) -> Fp {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        Fp::new(self.0)
    }
    fn e<E: ExtField>(&mut self) -> E {
        let d: Vec<Fp> = (0..E::DEGREE).map(|_| self.fp()).collect();
        E::from_digits(&d)
    }
}

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
        "n,commit_ms,kf_open_ms,kf_verify_ms,kf_proof_kib,ip_prove_ms,ip_verify_ms,ip_proof_kib,had_prove_ms,had_verify_ms,had_proof_kib"
    );
    for n in ns {
        let p = Params::recommended(n, 148, 32);
        let reps = if n >= 20 { 5 } else { 11 };
        let mut rng = Rng(0x1234 + n as u64);
        let a: Vec<Fp> = (0..p.big_n()).map(|_| rng.fp()).collect();
        let b: Vec<Fp> = (0..p.big_n()).map(|_| rng.fp()).collect();
        let z: Vec<Fp2> = (0..n).map(|_| rng.e()).collect();
        let (mut cm, mut ko, mut kv, mut ipp, mut ipv) = (vec![], vec![], vec![], vec![], vec![]);
        let (mut hp, mut hv, mut had_size) = (vec![], vec![], 0);
        let c: Vec<Fp> = a.iter().zip(&b).map(|(&x, &y)| x * y).collect();
        let (mut kf_size, mut ip_size) = (0, 0);
        for _ in 0..reps {
            let t = Instant::now();
            let (ra, pda) = commit_table_form(&p, &a, &[1u8; 32]);
            cm.push(ms(t));
            let (rb, pdb) = commit_table_form(&p, &b, &[2u8; 32]);

            let t = Instant::now();
            let (v, proof) = open::<Fp2>(&p, &pda, &z, &[3u8; 32]);
            ko.push(ms(t));
            let t = Instant::now();
            assert!(verify(&p, &ra, &z, v, &proof));
            kv.push(ms(t));
            kf_size = proof.size_bytes();

            let t = Instant::now();
            let (s, ipr) = prove_ip::<Fp2>(&p, &pda, &pdb, &[4u8; 32]);
            ipp.push(ms(t));
            let t = Instant::now();
            assert!(verify_ip(&p, &ra, &rb, s, &ipr));
            ipv.push(ms(t));
            ip_size = ipr.size_bytes();

            let (rc, pdc) = commit_table_form(&p, &c, &[5u8; 32]);
            let t = Instant::now();
            let hpr = prove_had::<Fp2>(&p, &pda, &pdb, &pdc, &[6u8; 32]);
            hp.push(ms(t));
            let t = Instant::now();
            assert!(verify_had(&p, [&ra, &rb, &rc], &hpr));
            hv.push(ms(t));
            had_size = hpr.size_bytes();
        }
        println!(
            "{n},{:.2},{:.2},{:.3},{:.1},{:.2},{:.3},{:.1},{:.2},{:.3},{:.1}",
            median(cm),
            median(ko),
            median(kv),
            kf_size as f64 / 1024.0,
            median(ipp),
            median(ipv),
            ip_size as f64 / 1024.0,
            median(hp),
            median(hv),
            had_size as f64 / 1024.0
        );
    }
}
