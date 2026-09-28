//! Zero-knowledge mode of the engine `affine` (`Params::mask > 0`): masked commitments, degree
//! adjustment and masking codeword (Kronobol `docs/zk/01-commitment.md`), and the public table
//! `Pub::Eq`.

use kronecker_fri::affine::{
    AStmt, Form, GData, OId, Pub, Shape, commit_group, commit_group_masked, prove_affine,
    verify_affine,
};
use kronecker_fri::error::Error;
use kronecker_fri::field::{Field, Fp, Fp2};
use kronecker_fri::merkle::Transcript;
use kronecker_fri::pcs::{Params, commit_table};

fn eq_table(r: &[Fp2]) -> Vec<Fp2> {
    (0..1usize << r.len())
        .map(|w| {
            r.iter().enumerate().fold(Fp2::ONE, |acc, (k, &rk)| {
                acc * if (w >> k) & 1 == 1 { rk } else { Fp2::ONE - rk }
            })
        })
        .collect()
}

fn params(n: usize, mask: usize) -> Params {
    Params {
        n,
        log_inv_rate: 2,
        ell: 3,
        queries: 24,
        salt_len: 32,
        fold_log: 1,
        cap_log: 2,
        mask,
    }
}

/// The statement of Kronobol's final claim: <W, mu·eq(., r) + alpha·p> = c, plus an evaluation.
fn statements(
    table: &[Fp],
    r: &[Fp2],
    sparse: &[(usize, Fp2)],
    mu: Fp2,
    alpha: Fp2,
    z: &[Fp2],
) -> Vec<AStmt<Fp2>> {
    let w = OId { group: 0, word: 0 };
    let eqt = eq_table(r);
    let mut c = Fp2::ZERO;
    for (j, &x) in table.iter().enumerate() {
        c = c + mu * eqt[j] * Fp2::from(x);
    }
    for &(j, v) in sparse {
        c = c + alpha * v * Fp2::from(table[j]);
    }
    let g = Form {
        com: vec![],
        pubs: vec![
            (Pub::Eq(r.to_vec()), mu),
            (Pub::Sparse(sparse.to_vec()), alpha),
        ],
    };
    let v = eq_table(z)
        .iter()
        .zip(table)
        .fold(Fp2::ZERO, |acc, (&e, &x)| acc + e * Fp2::from(x));
    vec![
        AStmt::Ip(Form::word(w), g, c),
        AStmt::Eval(Form::word(w), z.to_vec(), v),
    ]
}

fn run(n: usize, mask: usize) -> Result<(), Error> {
    let p = params(n, mask);
    let nn = 1usize << n;
    let table: Vec<Fp> = (0..nn as u64).map(|i| Fp::new(i * i + 7)).collect();
    let r: Vec<Fp2> = (0..n as u64)
        .map(|i| Fp2(Fp::new(i + 3), Fp::new(2 * i + 1)))
        .collect();
    let z: Vec<Fp2> = (0..n as u64)
        .map(|i| Fp2(Fp::new(5 * i + 2), Fp::new(i)))
        .collect();
    let sparse = vec![(nn - 1, Fp2::ONE), (nn - 2, Fp2(Fp::new(4), Fp::new(1)))];
    let (mu, alpha) = (Fp2(Fp::new(11), Fp::new(3)), Fp2(Fp::new(2), Fp::new(9)));
    let g = if mask > 0 {
        commit_group_masked(&p, vec![table.clone()], b"W")?
    } else {
        commit_group(&p, vec![table.clone()], b"W")?
    };
    let stmts = statements(&table, &r, &sparse, mu, alpha, &z);
    let groups = [GData::Base(&g)];
    let mut tp = Transcript::new(b"test/zk");
    let proof = prove_affine(&p, &mut tp, 0, &groups, &stmts)?;
    let shapes = [Shape {
        base: true,
        words: 1,
    }];
    let roots = [g.tree.root()];
    verify_affine(
        &p,
        &mut Transcript::new(b"test/zk"),
        &roots,
        &shapes,
        &stmts,
        &proof,
    )?;
    // a wrong claim is rejected
    let mut bad = stmts.clone();
    if let AStmt::Ip(f, gg, c) = &bad[0] {
        bad[0] = AStmt::Ip(f.clone(), gg.clone(), *c + Fp2::ONE);
    }
    assert!(
        verify_affine(
            &p,
            &mut Transcript::new(b"test/zk"),
            &roots,
            &shapes,
            &bad,
            &proof
        )
        .is_err()
    );
    // another transcript is rejected
    assert!(
        verify_affine(
            &p,
            &mut Transcript::new(b"other"),
            &roots,
            &shapes,
            &stmts,
            &proof
        )
        .is_err()
    );
    Ok(())
}

#[test]
fn masked_ip_and_eval() {
    for n in [6, 8, 10] {
        run(n, 0).unwrap();
        run(n, 8).unwrap();
        run(n, 16).unwrap();
    }
}

#[test]
fn masked_commitments_differ() {
    let p = params(8, 16);
    let table: Vec<Fp> = (0..256u64).map(Fp::new).collect();
    let a = commit_group_masked(&p, vec![table.clone()], b"W").unwrap();
    let b = commit_group_masked(&p, vec![table.clone()], b"W").unwrap();
    assert_eq!(a.coeffs[0][..256], b.coeffs[0][..256]);
    assert_eq!(a.coeffs[0].len(), 256 + 16);
    assert_ne!(a.coeffs[0][256..], b.coeffs[0][256..], "fresh masks");
    assert_ne!(a.evals[0], b.evals[0]);
}

#[test]
fn zk_mode_restrictions() {
    let n = 8;
    // mask must be a multiple of 2^ell and below N/2
    assert!(matches!(params(n, 12).validate(), Err(Error::Params(_))));
    assert!(matches!(params(n, 128).validate(), Err(Error::Params(_))));
    assert!(params(n, 64).validate().is_ok());
    // pcs does not support masking
    let table: Vec<Fp> = (0..256u64).map(Fp::new).collect();
    assert!(matches!(
        commit_table(&params(n, 16), &table),
        Err(Error::Params(_))
    ));
    // no Hadamard checks in zero-knowledge mode
    let p = params(n, 16);
    let g =
        commit_group_masked(&p, vec![table.clone(), table.clone(), table.clone()], b"W").unwrap();
    let w = |k| Form::word(OId { group: 0, word: k });
    let st = vec![AStmt::<Fp2>::Had(w(0), w(1), w(2))];
    let r = prove_affine(&p, &mut Transcript::new(b"t"), 0, &[GData::Base(&g)], &st);
    assert!(matches!(r, Err(Error::Input(_))));
}

#[test]
fn eq_table_polynomial() {
    // the table-form polynomial of Pub::Eq is prod_k ((1 - r_k) + r_k X^{2^k})
    let r: Vec<Fp2> = (0..5u64).map(|i| Fp2(Fp::new(i + 2), Fp::new(7))).collect();
    let x = Fp2(Fp::new(123), Fp::new(45));
    let direct = eq_table(&r)
        .iter()
        .enumerate()
        .fold(Fp2::ZERO, |acc, (w, &c)| acc + c * x.pow(w as u64));
    assert_eq!(Pub::Eq(r).eval(5, x), direct);
}
