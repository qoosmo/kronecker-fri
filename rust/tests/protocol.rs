//! End-to-end tests of Pi_KF (Section 9.5): completeness over all parameter shapes, and rejection
//! of tampered proofs.
use kronecker_fri::field::{ExtField, Field, Fp, Fp2, Fp4};
use kronecker_fri::pcs::{Params, commit_coeffs, commit_table, open, verify, verify_detail};

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

/// f(z) from the table form: sum_b f(b) prod_k (b_k z_k + (1 - b_k)(1 - z_k)), independent of the
/// Moebius transform and of the kernel product.
fn eval_table<E: ExtField>(t: &[Fp], z: &[E]) -> E {
    let mut acc = E::ZERO;
    for (b, &fb) in t.iter().enumerate() {
        let mut w = E::ONE;
        for (k, &zk) in z.iter().enumerate() {
            w = w * if b >> k & 1 == 1 { zk } else { E::ONE - zk };
        }
        acc = acc + w * fb;
    }
    acc
}

fn completeness<E: ExtField>(max_n: usize) {
    let mut rng = Rng(0xC0FFEE);
    for n in 1..=max_n {
        for r in [2, 3, 4] {
            for ell in 1..=n {
                for salt_len in [0, 32] {
                    let p = Params {
                        n,
                        log_inv_rate: r,
                        ell,
                        queries: 8,
                        salt_len,
                    };
                    let table: Vec<Fp> = (0..1 << n).map(|_| rng.fp()).collect();
                    let z: Vec<E> = (0..n).map(|_| rng.e()).collect();
                    let (root, pd) = commit_table(&p, &table, &[7u8; 32]);
                    let (v, proof) = open(&p, &pd, &z, &[8u8; 32]);
                    assert_eq!(v, eval_table(&table, &z), "value n={n} R={r} l={ell}");
                    assert_eq!(
                        verify_detail(&p, &root, &z, v, &proof),
                        Ok(()),
                        "n={n} R={r} l={ell} salt={salt_len}"
                    );
                }
            }
        }
    }
}

#[test]
fn completeness_fp2() {
    completeness::<Fp2>(9);
}

#[test]
fn completeness_fp4() {
    completeness::<Fp4>(7);
}

type Mutation = Box<dyn Fn(&mut kronecker_fri::pcs::Proof<Fp2>)>;

#[test]
fn tampering_is_rejected() {
    let mut rng = Rng(12345);
    for (n, ell) in [(6, 3), (8, 4), (8, 8)] {
        let p = Params {
            n,
            log_inv_rate: 2,
            ell,
            queries: 20,
            salt_len: 32,
        };
        let alpha: Vec<Fp> = (0..1 << n).map(|_| rng.fp()).collect();
        let z: Vec<Fp2> = (0..n).map(|_| rng.e()).collect();
        let (root, pd) = commit_coeffs(&p, &alpha, &[1u8; 32]);
        let (v, proof) = open(&p, &pd, &z, &[2u8; 32]);
        assert!(verify(&p, &root, &z, v, &proof));

        // wrong value, wrong point
        assert!(!verify(&p, &root, &z, v + Fp2::ONE, &proof));
        let mut z2 = z.clone();
        z2[0] = z2[0] + Fp2::ONE;
        assert!(!verify(&p, &root, &z2, v, &proof));
        // other commitment
        let alpha2: Vec<Fp> = (0..1 << n).map(|_| rng.fp()).collect();
        let (root2, _) = commit_coeffs(&p, &alpha2, &[1u8; 32]);
        assert!(!verify(&p, &root2, &z, v, &proof));
        // a proof for another polynomial, checked against the original commitment
        let (_, pd2) = commit_coeffs(&p, &alpha2, &[1u8; 32]);
        let (v2, proof2) = open(&p, &pd2, &z, &[2u8; 32]);
        assert!(!verify(&p, &root, &z, v2, &proof2));

        let mutations: Vec<Mutation> = vec![
            Box::new(|pr| pr.queries[0].y[0] = pr.queries[0].y[0] + Fp::ONE),
            Box::new(|pr| pr.queries[3].a[0] = pr.queries[3].a[0] + Fp2::ONE),
            Box::new(|pr| pr.queries[5].a[1] = pr.queries[5].a[1] + Fp2::ONE),
            Box::new(|pr| pr.p[0] = pr.p[0] + Fp2::ONE),
            Box::new(|pr| pr.root_a[0] ^= 1),
            Box::new(|pr| pr.round_salts[1][0] ^= 1),
            Box::new(|pr| pr.queries[2].y_open.salts[0][0] ^= 1),
            Box::new(|pr| pr.queries[1].a_open.path[0][0] ^= 1),
        ];
        for (i, mt) in mutations.iter().enumerate() {
            let mut pr = proof.clone();
            mt(&mut pr);
            assert!(
                !verify(&p, &root, &z, v, &pr),
                "mutation {i} accepted (n={n}, l={ell})"
            );
        }
        if ell >= 2 {
            let mut pr = proof.clone();
            pr.queries[4].levels[0].0[1] = pr.queries[4].levels[0].0[1] + Fp2::ONE;
            assert!(!verify(&p, &root, &z, v, &pr));
            let mut pr = proof.clone();
            pr.roots[0][5] ^= 1;
            assert!(!verify(&p, &root, &z, v, &pr));
        }
    }
}
