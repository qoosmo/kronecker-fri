//! Benchmarks for Section 10.  Single-threaded.  Usage:
//!   cargo run --release --example bench -- scaling | breakdown | stop | fields
use kronecker_fri::field::{ExtField, Field, Fp, Fp2, Fp4};
use kronecker_fri::merkle::MerkleTree;
use kronecker_fri::pcs::virtual_value;
use kronecker_fri::pcs::{Params, commit_coeffs, open, verify};
use kronecker_fri::poly::{fold_word, kernel_on_domain, ntt, opening_polys};
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

fn reps_for(n: usize) -> usize {
    if n >= 22 {
        3
    } else if n >= 20 {
        5
    } else {
        11
    }
}

struct Row {
    commit: f64,
    open: f64,
    verify: f64,
    proof_kib: f64,
}

fn run<E: ExtField>(p: &Params, reps: usize, seed: u64) -> Row {
    let mut rng = Rng(seed);
    let alpha: Vec<Fp> = (0..p.big_n()).map(|_| rng.fp()).collect();
    let z: Vec<E> = (0..p.n).map(|_| rng.e()).collect();
    let mut cm = vec![];
    for _ in 0..reps {
        let t = Instant::now();
        let r = commit_coeffs(p, &alpha, &[1u8; 32]);
        cm.push(ms(t));
        std::hint::black_box(r.0);
    }
    let (root, pd) = commit_coeffs(p, &alpha, &[1u8; 32]);
    let mut op = vec![];
    let mut last = None;
    for _ in 0..reps {
        let t = Instant::now();
        let r = open(p, &pd, &z, &[2u8; 32]);
        op.push(ms(t));
        last = Some(r);
    }
    let (v, proof) = last.unwrap();
    let mut ve = vec![];
    for _ in 0..21 {
        let t = Instant::now();
        let ok = verify(p, &root, &z, v, &proof);
        ve.push(ms(t));
        assert!(ok);
    }
    Row {
        commit: median(cm),
        open: median(op),
        verify: median(ve),
        proof_kib: proof.size_bytes() as f64 / 1024.0,
    }
}

/// Components of the opening, with the same code as `pcs::open` (unsalted trees).
fn breakdown(n: usize) {
    let p = Params {
        n,
        log_inv_rate: 2,
        ell: n - 4,
        queries: 148,
        salt_len: 0,
    };
    let (nn, m) = (p.big_n(), p.m());
    let mut rng = Rng(5 + n as u64);
    let alpha: Vec<Fp> = (0..nn).map(|_| rng.fp()).collect();
    let z: Vec<Fp2> = (0..n).map(|_| rng.e()).collect();
    let (_, pd) = commit_coeffs(&p, &alpha, &[1u8; 32]);
    let omega = p.omega();
    let inv2 = Fp::new(2).inv();
    let oi = omega.inv();
    let inv_x0: Vec<Fp> = (0..m / 2)
        .scan(Fp::ONE, |s, _| {
            let c = *s;
            *s = *s * oi;
            Some(c)
        })
        .collect();
    let (mut kp, mut nt, mut mk, mut bt, mut fd) = (vec![], vec![], vec![], vec![], vec![]);
    for _ in 0..reps_for(n) {
        let t = Instant::now();
        let u: Vec<Fp2> = alpha.iter().map(|&x| Fp2::from(x)).collect();
        let (a, _v, h) = opening_polys(&u, &z);
        kp.push(ms(t));
        let t = Instant::now();
        let mut wa = a.clone();
        wa.resize(m, Fp2::ZERO);
        ntt(&mut wa, omega);
        nt.push(ms(t));
        let t = Instant::now();
        let tree = MerkleTree::from_fn(
            m / 2,
            |k, b| {
                wa[k].to_bytes(b);
                wa[k + m / 2].to_bytes(b)
            },
            &[3u8; 32],
            b"round1",
            0,
        );
        mk.push(ms(t));
        std::hint::black_box(tree.root());
        drop(tree);
        let t = Instant::now();
        let beta: Fp2 = rng.e();
        let b2 = beta * beta;
        let kz = kernel_on_domain(&z, omega, m);
        let v = _v;
        let (sn, si) = (omega.pow(nn as u64), omega.pow((m - nn - 1) as u64));
        let (mut x, mut xn, mut xi) = (Fp::ONE, Fp::ONE, Fp::ONE);
        let mut w0 = Vec::with_capacity(m);
        for i in 0..m {
            let yi = Fp2::from(pd.y[i]);
            let hi = virtual_value(x, yi, wa[i], kz[i], v, xn, xi);
            w0.push(yi + beta * wa[i] + b2 * hi);
            x = x * omega;
            xn = xn * sn;
            xi = xi * si;
        }
        let _ = &h;
        bt.push(ms(t));
        let t = Instant::now();
        let mut w = w0;
        for j in 1..p.ell {
            let r: Fp2 = rng.e();
            w = fold_word(&w, r, &inv_x0, j - 1, inv2);
            let h2 = w.len() / 2;
            let tr = MerkleTree::from_fn(
                h2,
                |k, b| {
                    w[k].to_bytes(b);
                    w[k + h2].to_bytes(b)
                },
                &[4u8; 32],
                b"w",
                0,
            );
            std::hint::black_box(tr.root());
        }
        fd.push(ms(t));
    }
    println!(
        "{},{:.2},{:.2},{:.2},{:.2},{:.2}",
        n,
        median(kp),
        median(nt),
        median(mk),
        median(bt),
        median(fd)
    );
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "scaling".into());
    match mode.as_str() {
        "scaling" => {
            println!("salt,n,ell,queries,commit_ms,open_ms,verify_ms,proof_kib");
            for n in (12..=22).step_by(2) {
                for salt_len in [0, 32] {
                    let p = Params {
                        n,
                        log_inv_rate: 2,
                        ell: n - 4,
                        queries: 148,
                        salt_len,
                    };
                    let r = run::<Fp2>(&p, reps_for(n), 1 + n as u64);
                    println!(
                        "{},{},{},{},{:.2},{:.2},{:.3},{:.1}",
                        salt_len, n, p.ell, p.queries, r.commit, r.open, r.verify, r.proof_kib
                    );
                }
            }
        }
        "breakdown" => {
            println!(
                "n,kernel_product_ms,ntt_A_ms,merkle_A_ms,virtual_and_batch_ms,folds_and_trees_ms"
            );
            for n in (16..=22).step_by(2) {
                breakdown(n);
            }
        }
        "stop" => {
            println!("n,ell,final_len,open_ms,verify_ms,proof_kib");
            let n = 20;
            for ell in [8, 10, 12, 14, 16, 18, 20] {
                let p = Params {
                    n,
                    log_inv_rate: 2,
                    ell,
                    queries: 148,
                    salt_len: 0,
                };
                let r = run::<Fp2>(&p, 3, 77);
                println!(
                    "{},{},{},{:.2},{:.3},{:.1}",
                    n,
                    ell,
                    1 << (n - ell),
                    r.open,
                    r.verify,
                    r.proof_kib
                );
            }
        }
        "fields" => {
            println!("setting,field,queries,salt,commit_ms,open_ms,verify_ms,proof_kib");
            let n = 20;
            let cases: [(&str, usize, usize, usize); 3] = [
                ("classical", 2, 148, 0),
                ("classical-salted", 2, 148, 32),
                ("post-quantum", 4, 248, 32),
            ];
            for (name, e, q, salt) in cases {
                let p = Params {
                    n,
                    log_inv_rate: 2,
                    ell: n - 4,
                    queries: q,
                    salt_len: salt,
                };
                let r = if e == 2 {
                    run::<Fp2>(&p, 5, 9)
                } else {
                    run::<Fp4>(&p, 5, 9)
                };
                println!(
                    "{},{},{},{},{:.2},{:.2},{:.3},{:.1}",
                    name, e, q, salt, r.commit, r.open, r.verify, r.proof_kib
                );
            }
        }
        "params" => {
            println!("setting,field,R,queries,ell,salt,commit_ms,open_ms,verify_ms,proof_kib");
            let n = 20;
            let cases: [(&str, usize, usize, usize); 4] = [
                ("100-bit rho=1/4", 2, 2, 148),
                ("100-bit rho=1/8", 2, 3, 121),
                ("128-bit rho=1/4", 4, 2, 189),
                ("post-quantum rho=1/4", 4, 2, 248),
            ];
            for (name, e, r, q) in cases {
                let p = Params {
                    n,
                    log_inv_rate: r,
                    ell: n - 8,
                    queries: q,
                    salt_len: 32,
                };
                let row = if e == 2 {
                    run::<Fp2>(&p, 3, 11)
                } else {
                    run::<Fp4>(&p, 3, 11)
                };
                println!(
                    "{},{},{},{},{},32,{:.2},{:.2},{:.3},{:.1}",
                    name, e, r, q, p.ell, row.commit, row.open, row.verify, row.proof_kib
                );
            }
        }
        _ => eprintln!("unknown mode"),
    }
}
