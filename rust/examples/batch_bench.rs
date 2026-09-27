//! One batched proof (Pi_Batch) against separate proofs of the same statements: a Hadamard check
//! a o b = c, an inner product <a, d>, and evaluations of a and c at random points.
//! Configuration KF-8 (rate 1/4, arity 8, caps of 128 nodes, l = n - 8), 148 queries, 32-byte
//! salts, F_{p^2}.  Single-threaded.
//!   cargo run --release --example batch_bench -- [n ...]      (default: 12 14 16 18 20)
use kronecker_fri::batch::{Stmt, batch_words, prove_batch, verify_batch};
use kronecker_fri::field::{ExtField, Field, Fp, Fp2};
use kronecker_fri::ip::commit_table_form;
use kronecker_fri::merkle::Digest;
use kronecker_fri::pcs::{Params, ProverData};
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

fn mle(t: &[Fp], z: &[Fp2]) -> Fp2 {
    // sum_w t(w) eq(w, z), by folding the table one variable at a time
    let mut v: Vec<Fp2> = t.iter().map(|&x| Fp2::from(x)).collect();
    for &zk in z {
        v = v
            .chunks(2)
            .map(|c| c[0] * (Fp2::ONE - zk) + c[1] * zk)
            .collect();
    }
    v[0]
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
        "n,words,batch_prove_ms,batch_verify_ms,batch_proof_kib,sep_prove_ms,sep_verify_ms,sep_proof_kib"
    );
    for n in ns {
        let p = Params::recommended(n, 148, 32);
        let reps = if n >= 20 { 3 } else { 7 };
        let mut rng = Rng(0xBA7C + n as u64);
        let nn = p.big_n();
        let a: Vec<Fp> = (0..nn).map(|_| rng.fp()).collect();
        let b: Vec<Fp> = (0..nn).map(|_| rng.fp()).collect();
        let c: Vec<Fp> = a.iter().zip(&b).map(|(&x, &y)| x * y).collect();
        let d: Vec<Fp> = (0..nn).map(|_| rng.fp()).collect();
        let com: Vec<(Digest, ProverData)> = [&a, &b, &c, &d]
            .iter()
            .enumerate()
            .map(|(i, t)| commit_table_form(&p, t, &[i as u8 + 1; 32]))
            .collect();
        let roots: Vec<Digest> = com.iter().map(|x| x.0).collect();
        let pds: Vec<&ProverData> = com.iter().map(|x| &x.1).collect();
        let z1: Vec<Fp2> = (0..n).map(|_| rng.e()).collect();
        let z2: Vec<Fp2> = (0..n).map(|_| rng.e()).collect();
        let s = Fp2::from(a.iter().zip(&d).fold(Fp::ZERO, |s, (&x, &y)| s + x * y));
        let stmts = vec![
            Stmt::Had { a: 0, b: 1, c: 2 },
            Stmt::Ip { a: 0, b: 3, s },
            Stmt::Eval {
                f: 0,
                z: z1.clone(),
                v: mle(&a, &z1),
            },
            Stmt::Eval {
                f: 2,
                z: z2.clone(),
                v: mle(&c, &z2),
            },
        ];
        let (mut bp, mut bv, mut sp, mut sv) = (vec![], vec![], vec![], vec![]);
        let (mut bsize, mut ssize) = (0, 0);
        for _ in 0..reps {
            let t = Instant::now();
            let pr = prove_batch(&p, &pds, &stmts, &[9u8; 32]);
            bp.push(ms(t));
            let t = Instant::now();
            assert!(verify_batch(&p, &roots, &stmts, &pr));
            bv.push(ms(t));
            bsize = pr.size_bytes();
            let (mut tp, mut tv, mut sz) = (0.0, 0.0, 0);
            for st in &stmts {
                let one = std::slice::from_ref(st);
                let t = Instant::now();
                let pr = prove_batch(&p, &pds, one, &[9u8; 32]);
                tp += ms(t);
                let t = Instant::now();
                assert!(verify_batch(&p, &roots, one, &pr));
                tv += ms(t);
                sz += pr.size_bytes();
            }
            sp.push(tp);
            sv.push(tv);
            ssize = sz;
        }
        println!(
            "{n},{},{:.1},{:.2},{:.1},{:.1},{:.2},{:.1}",
            batch_words(&stmts),
            median(bp),
            median(bv),
            bsize as f64 / 1024.0,
            median(sp),
            median(sv),
            ssize as f64 / 1024.0
        );
    }
}
