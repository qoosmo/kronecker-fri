//! Malformed proofs: every verifier must return an error, never panic, and never accept.
//!
//! Each test builds a valid proof, applies structural mutations (emptied, shortened and lengthened
//! vectors at every level, corrupted salts, paths and values) and checks that `verify` returns
//! `Err` without panicking.

use kronecker_fri::error::Error;
use kronecker_fri::field::{Field, Fp, Fp2};
use kronecker_fri::merkle::GroupOpening;
use kronecker_fri::pcs::{Params, Proof, commit_table, open, verify};
use kronecker_fri::r1cs::{R1csProof, index, prove_r1cs, sample_instance, verify_r1cs};
use std::panic::{AssertUnwindSafe, catch_unwind};

type Mut<P> = Box<dyn Fn(&mut P)>;

/// Mutations of a vector: emptied, last element removed, first element duplicated.
fn vec_muts<P: 'static, T: Clone + 'static>(get: fn(&mut P) -> &mut Vec<T>) -> Vec<Mut<P>> {
    vec![
        Box::new(move |p: &mut P| get(p).clear()),
        Box::new(move |p: &mut P| {
            get(p).pop();
        }),
        Box::new(move |p: &mut P| {
            let v = get(p);
            if let Some(x) = v.first().cloned() {
                v.push(x);
            }
        }),
    ]
}

fn opening_muts<P: 'static>(get: fn(&mut P) -> Option<&mut GroupOpening>) -> Vec<Mut<P>> {
    let f: Vec<fn(&mut GroupOpening)> = vec![
        |o| o.path.clear(),
        |o| {
            o.path.pop();
        },
        |o| {
            if let Some(x) = o.path.first().cloned() {
                o.path.push(x)
            }
        },
        |o| {
            if let Some(x) = o.path.first_mut() {
                x[0] ^= 1
            }
        },
        |o| o.salts.clear(),
        |o| {
            o.salts.pop();
        },
        |o| {
            if let Some(s) = o.salts.first_mut() {
                s.pop();
            }
        },
        |o| {
            if let Some(s) = o.salts.first_mut() {
                s.push(0);
            }
        },
        |o| {
            if let Some(s) = o.salts.first_mut().and_then(|s| s.first_mut()) {
                *s ^= 1
            }
        },
    ];
    f.into_iter()
        .map(|m| {
            Box::new(move |p: &mut P| {
                if let Some(o) = get(p) {
                    m(o)
                }
            }) as Mut<P>
        })
        .collect()
}

fn run<P: Clone + core::fmt::Debug>(
    name: &str,
    base: &P,
    muts: Vec<Mut<P>>,
    verify: impl Fn(&P) -> Result<(), Error>,
) {
    assert_eq!(
        verify(base),
        Ok(()),
        "{name}: the unmutated proof must verify"
    );
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let mut failures = Vec::new();
    let mut applied = 0;
    for (k, m) in muts.iter().enumerate() {
        let mut p = base.clone();
        m(&mut p);
        if format!("{p:?}") == format!("{base:?}") {
            continue; // the mutation does not apply to this proof (e.g. empty salts)
        }
        applied += 1;
        match catch_unwind(AssertUnwindSafe(|| verify(&p))) {
            Err(_) => failures.push(format!("mutation {k}: panic")),
            Ok(Ok(())) => failures.push(format!("mutation {k}: accepted")),
            Ok(Err(_)) => {}
        }
    }
    std::panic::set_hook(hook);
    assert!(failures.is_empty(), "{name}: {failures:?}");
    assert!(
        applied * 4 >= muts.len() * 3,
        "{name}: only {applied} of {} mutations applied",
        muts.len()
    );
}

fn pcs_muts() -> Vec<Mut<Proof<Fp2>>> {
    let mut m: Vec<Mut<Proof<Fp2>>> = Vec::new();
    m.extend(vec_muts(|p: &mut Proof<Fp2>| &mut p.cap_y));
    m.extend(vec_muts(|p: &mut Proof<Fp2>| &mut p.cap_a));
    m.extend(vec_muts(|p: &mut Proof<Fp2>| &mut p.caps));
    m.extend(vec_muts(|p: &mut Proof<Fp2>| &mut p.round_salts));
    m.extend(vec_muts(|p: &mut Proof<Fp2>| &mut p.p));
    m.extend(vec_muts(|p: &mut Proof<Fp2>| &mut p.level0));
    m.extend(vec_muts(|p: &mut Proof<Fp2>| &mut p.levels));
    m.extend(vec_muts(|p: &mut Proof<Fp2>| p.caps.first_mut().unwrap()));
    m.extend(vec_muts(|p: &mut Proof<Fp2>| &mut p.level0[0].y));
    m.extend(vec_muts(|p: &mut Proof<Fp2>| &mut p.level0[0].a));
    m.extend(vec_muts(|p: &mut Proof<Fp2>| p.levels.first_mut().unwrap()));
    m.extend(vec_muts(|p: &mut Proof<Fp2>| &mut p.levels[0][0].vals));
    m.extend(vec_muts(|p: &mut Proof<Fp2>| &mut p.round_salts[0]));
    m.extend(opening_muts(|p: &mut Proof<Fp2>| {
        Some(&mut p.level0[0].y_open)
    }));
    m.extend(opening_muts(|p: &mut Proof<Fp2>| {
        Some(&mut p.level0[0].a_open)
    }));
    m.extend(opening_muts(|p: &mut Proof<Fp2>| {
        p.levels
            .first_mut()
            .and_then(|l| l.first_mut())
            .map(|o| &mut o.open)
    }));
    m.push(Box::new(|p| p.level0[0].pos ^= 1));
    m.push(Box::new(|p| p.level0[0].pos = usize::MAX));
    m.push(Box::new(|p| p.levels[0][0].pos = usize::MAX));
    m.push(Box::new(|p| p.p[0] = p.p[0] + Fp2::ONE));
    m.push(Box::new(|p| {
        p.level0[0].y[0][0] = p.level0[0].y[0][0] + Fp::ONE
    }));
    m.push(Box::new(|p| {
        p.level0[0].a[0][1] = p.level0[0].a[0][1] + Fp2::ONE
    }));
    m.push(Box::new(|p| p.cap_y[0][0] ^= 1));
    m.push(Box::new(|p| p.cap_a[0][0] ^= 1));
    m
}

#[test]
fn pcs_malformed_proofs() {
    for (n, fold_log, cap_log, salt) in [(6, 1, 0, 0), (9, 3, 2, 16), (11, 3, 7, 32)] {
        let p = Params {
            n,
            log_inv_rate: 2,
            ell: n - 3,
            queries: 12,
            salt_len: salt,
            fold_log,
            cap_log,
        };
        let table: Vec<Fp> = (0..1u64 << n).map(|i| Fp::new(i * i + 1)).collect();
        let z: Vec<Fp2> = (0..n as u64)
            .map(|i| Fp2(Fp::new(5 + i), Fp::new(3 * i + 1)))
            .collect();
        let (root, pd) = commit_table(&p, &table, &[1u8; 32]);
        let (v, proof) = open(&p, &pd, &z, &[2u8; 32]);
        run(&format!("pcs n={n}"), &proof, pcs_muts(), |pr| {
            verify(&p, &root, &z, v, pr)
        });
        // wrong statement shapes
        assert!(verify(&p, &root, &z[1..], v, &proof).is_err());
        let mut bad = p;
        bad.ell = 0;
        assert!(matches!(
            verify(&bad, &root, &z, v, &proof),
            Err(Error::Params(_))
        ));
    }
}

fn r1cs_muts() -> Vec<Mut<R1csProof<Fp2>>> {
    let mut m: Vec<Mut<R1csProof<Fp2>>> = Vec::new();
    m.extend(vec_muts(|p: &mut R1csProof<Fp2>| &mut p.salts));
    m.extend(vec_muts(|p: &mut R1csProof<Fp2>| &mut p.salts[0]));
    m.extend(vec_muts(|p: &mut R1csProof<Fp2>| &mut p.engine.gcaps));
    m.extend(vec_muts(|p: &mut R1csProof<Fp2>| &mut p.engine.gcaps[0]));
    m.extend(vec_muts(|p: &mut R1csProof<Fp2>| &mut p.engine.gopen));
    m.extend(vec_muts(|p: &mut R1csProof<Fp2>| &mut p.engine.cap_q));
    m.extend(vec_muts(|p: &mut R1csProof<Fp2>| &mut p.engine.cap_w));
    m.extend(vec_muts(|p: &mut R1csProof<Fp2>| &mut p.engine.salts));
    m.extend(vec_muts(|p: &mut R1csProof<Fp2>| &mut p.engine.ys));
    m.extend(vec_muts(|p: &mut R1csProof<Fp2>| &mut p.engine.oq));
    m.extend(vec_muts(|p: &mut R1csProof<Fp2>| &mut p.engine.ow));
    m.extend(vec_muts(|p: &mut R1csProof<Fp2>| &mut p.engine.ft.caps));
    m.extend(vec_muts(|p: &mut R1csProof<Fp2>| {
        &mut p.engine.ft.round_salts
    }));
    m.extend(vec_muts(|p: &mut R1csProof<Fp2>| &mut p.engine.ft.p));
    m.extend(vec_muts(|p: &mut R1csProof<Fp2>| &mut p.engine.ft.levels));
    m.extend(vec_muts(|p: &mut R1csProof<Fp2>| &mut p.engine.ow[0].vals));
    m.extend(vec_muts(|p: &mut R1csProof<Fp2>| {
        &mut p.engine.ow[0].vals[0]
    }));
    m.extend(opening_muts(|p: &mut R1csProof<Fp2>| {
        p.engine.ow.first_mut().map(|o| &mut o.open)
    }));
    m.extend(opening_muts(|p: &mut R1csProof<Fp2>| {
        p.engine.oq.first_mut().map(|o| &mut o.open)
    }));
    m.extend(opening_muts(|p: &mut R1csProof<Fp2>| {
        p.engine
            .ft
            .levels
            .first_mut()
            .and_then(|l| l.first_mut())
            .map(|o| &mut o.open)
    }));
    m.push(Box::new(|p| p.sums[0] = p.sums[0] + Fp2::ONE));
    m.push(Box::new(|p| p.root_wit[0] ^= 1));
    m.push(Box::new(|p| p.engine.ow[0].pos = usize::MAX));
    m.push(Box::new(|p| p.engine.ft.p[0] = p.engine.ft.p[0] + Fp2::ONE));
    m
}

#[test]
fn r1cs_malformed_proofs() {
    let n = 5;
    let p = Params {
        n,
        log_inv_rate: 2,
        ell: 3,
        queries: 10,
        salt_len: 16,
        fold_log: 2,
        cap_log: 1,
    };
    let (r, x, wit) = sample_instance(n, 2, 2, 11);
    let idx = index(&p, &r, &[1u8; 32]);
    let pr = prove_r1cs::<Fp2>(&p, &r, &idx, &x, &wit, &[2u8; 32]);
    run("r1cs", &pr, r1cs_muts(), |q| {
        verify_r1cs(&p, &r, &idx.root, &x, q)
    });
    assert!(verify_r1cs(&p, &r, &idx.root, &x[1..], &pr).is_err());
}
