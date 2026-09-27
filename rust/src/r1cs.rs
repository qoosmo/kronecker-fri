//! Prototype of the sumcheck-free R1CS argument of the research note (`notes/inner-product`,
//! Section 5.3, Theorem 5.8): (Az) o (Bz) = Cz with z = x_hat + w, for public sparse A, B, C
//! (committed once by an honest indexer), a public input x at fixed positions, and a committed
//! witness w (zero on the input positions).
//!
//! Rounds:
//! 1. the prover commits the group (w, a, b, c), a = Az, b = Bz, c = Cz;
//! 2. eta; the prover commits, for each matrix, e = eta^row, zeta = z(col), p = e zeta (one group);
//! 3. x_R, y_R, x_C, y_C (shared by the three matrices); the prover commits, for each matrix,
//!    phi^R, psi^R, phi^C, psi^C (one group) and sends s, s_R, s_C;
//! 4. the engine `affine` proves the 11 statements of each lincheck (Definition 5.3),
//!    Had(a, b, c) and Had(w, chi, 0), with one folding test.

use crate::affine::{
    AStmt, AffineProof, Form, GData, GroupData, OId, Pub, Shape, commit_group, prove_affine,
    verify_affine,
};
use crate::field::{ExtField, Field, Fp, batch_inv};
use crate::ft::round_salt;
use crate::lincheck::Sparse;
use crate::merkle::{Digest, Transcript};
use crate::pcs::{Params, e_bytes};

/// An R1CS instance: N x N sparse matrices (N = 2^n) and the input positions.
#[derive(Clone, Debug)]
pub struct R1cs {
    pub n: usize,
    pub mats: [Sparse; 3],
    pub inputs: Vec<usize>,
}

/// The index: one group (row, col, val, mR, mC) per matrix.
pub struct Index {
    pub groups: Vec<GroupData<Fp>>,
    pub roots: Vec<Digest>,
}

pub fn index(p: &Params, r: &R1cs, seed: &Digest) -> Index {
    let groups: Vec<GroupData<Fp>> = r
        .mats
        .iter()
        .enumerate()
        .map(|(i, mt)| {
            let (mr, mc) = mt.multiplicities();
            let words = vec![
                mt.row.iter().map(|&x| Fp::new(x as u64)).collect(),
                mt.col.iter().map(|&x| Fp::new(x as u64)).collect(),
                mt.val.clone(),
                mr,
                mc,
            ];
            commit_group(p, words, seed, format!("index-{i}").as_bytes())
        })
        .collect();
    let roots = groups.iter().map(|g| g.tree.root()).collect();
    Index { groups, roots }
}

#[derive(Clone, Debug)]
pub struct R1csProof<E> {
    pub root_wit: Digest,
    pub root_l1: Digest,
    pub root_l2: Digest,
    pub salts: Vec<Vec<u8>>,
    /// (s, s_R, s_C) for A, B, C
    pub sums: Vec<[E; 3]>,
    pub engine: AffineProof<E>,
}

impl<E: ExtField> R1csProof<E> {
    /// Size in bytes (the index roots are known to the verifier).
    pub fn size_bytes(&self) -> usize {
        let e = 8 * E::DEGREE;
        let caps_wit_l: usize =
            self.engine.gcaps[0].len() + self.engine.gcaps[4].len() + self.engine.gcaps[5].len();
        32 * caps_wit_l
            + self.salts.iter().map(|s| s.len()).sum::<usize>()
            + 3 * e * self.sums.len()
            + self.engine.size_bytes(false)
    }
}

const G_WIT: usize = 0;
const G_L1: usize = 4;
const G_L2: usize = 5;

fn o(group: usize, word: usize) -> OId {
    OId { group, word }
}

fn x_hat<E: ExtField>(r: &R1cs, x: &[Fp]) -> Pub<E> {
    Pub::Sparse(
        r.inputs
            .iter()
            .zip(x)
            .map(|(&i, &v)| (i, E::from(v)))
            .collect(),
    )
}

/// The statements of step 4.
fn statements<E: ExtField>(
    r: &R1cs,
    x: &[Fp],
    eta: E,
    ch: [E; 4],
    sums: &[[E; 3]],
) -> Vec<AStmt<E>> {
    let [xr, yr, xc, yc] = ch;
    let one = E::ONE;
    let w = |k: usize| Form::word(o(G_WIT, k));
    let pubf = |pb: Pub<E>| Form::public(pb);
    let mut st = Vec::new();
    for mi in 0..3 {
        let gi = 1 + mi;
        let (row, col, val, mr, mc) = (o(gi, 0), o(gi, 1), o(gi, 2), o(gi, 3), o(gi, 4));
        let (e, zeta, pp) = (o(G_L1, 3 * mi), o(G_L1, 3 * mi + 1), o(G_L1, 3 * mi + 2));
        let (phr, psr, phc, psc) = (
            o(G_L2, 4 * mi),
            o(G_L2, 4 * mi + 1),
            o(G_L2, 4 * mi + 2),
            o(G_L2, 4 * mi + 3),
        );
        let [s, sr, sc] = sums[mi];
        st.push(AStmt::Ip(w(1 + mi), pubf(Pub::Geo(eta)), s));
        st.push(AStmt::Ip(Form::word(val), Form::word(pp), s));
        st.push(AStmt::Had(Form::word(e), Form::word(zeta), Form::word(pp)));
        // row lookup
        st.push(AStmt::Had(
            Form::word(phr),
            Form {
                com: vec![(row, -one), (e, -yr)],
                pubs: vec![(Pub::One, xr)],
            },
            pubf(Pub::One),
        ));
        st.push(AStmt::Had(
            Form::word(psr),
            Form {
                com: vec![],
                pubs: vec![(Pub::One, xr), (Pub::Id, -one), (Pub::Geo(eta), -yr)],
            },
            Form::word(mr),
        ));
        st.push(AStmt::Ip(Form::word(phr), pubf(Pub::One), sr));
        st.push(AStmt::Ip(Form::word(psr), pubf(Pub::One), sr));
        // column lookup (z = x_hat + w)
        st.push(AStmt::Had(
            Form::word(phc),
            Form {
                com: vec![(col, -one), (zeta, -yc)],
                pubs: vec![(Pub::One, xc)],
            },
            pubf(Pub::One),
        ));
        st.push(AStmt::Had(
            Form::word(psc),
            Form {
                com: vec![(o(G_WIT, 0), -yc)],
                pubs: vec![(Pub::One, xc), (Pub::Id, -one), (x_hat(r, x), -yc)],
            },
            Form::word(mc),
        ));
        st.push(AStmt::Ip(Form::word(phc), pubf(Pub::One), sc));
        st.push(AStmt::Ip(Form::word(psc), pubf(Pub::One), sc));
    }
    st.push(AStmt::Had(w(1), w(2), w(3)));
    let chi = Pub::Sparse(r.inputs.iter().map(|&i| (i, E::ONE)).collect());
    st.push(AStmt::Had(w(0), pubf(chi), pubf(Pub::Zero)));
    st
}

/// The statements of step 4 with arbitrary challenges and sums, for counting the words.
pub fn statements_for_count<E: ExtField>(r: &R1cs, x: &[Fp]) -> Vec<AStmt<E>> {
    let one = E::ONE;
    statements(r, x, one + one, [one; 4], &[[one; 3]; 3])
}

fn init_transcript<E: ExtField>(
    p: &Params,
    idx_roots: &[Digest],
    r: &R1cs,
    x: &[Fp],
) -> Transcript {
    let mut tr = Transcript::new(b"kronecker-fri-r1cs-v1");
    let params = [
        p.n,
        p.log_inv_rate,
        p.ell,
        p.queries,
        p.salt_len,
        p.fold_log,
        p.cap_log,
        E::DEGREE,
    ];
    let pb: Vec<u8> = params
        .iter()
        .flat_map(|&v| (v as u64).to_le_bytes())
        .collect();
    tr.absorb(b"params", &pb);
    for rt in idx_roots {
        tr.absorb(b"index", rt);
    }
    let mut ib = Vec::new();
    for (&i, v) in r.inputs.iter().zip(x) {
        ib.extend((i as u64).to_le_bytes());
        v.to_bytes(&mut ib);
    }
    tr.absorb(b"input", &ib);
    tr
}

/// Deviations from the honest prover, for the tests.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum R1csCheat {
    None,
    /// commit a with a(N-1) = Az(N-1) + 1 (a row where A, B, C vanish, so that a o b = c still
    /// holds): only the lincheck of A is false
    WrongA,
    /// WrongA, and zeta of A forged at one nonzero entry so that the weighted sums agree: only the
    /// column lookup of A fails
    WrongAForgeZeta,
    /// WrongA, and e of A forged instead: only the row lookup of A fails
    WrongAForgeE,
}

/// The prover. `x` is the public input (one value per input position), `wit` the witness table
/// (zero on the input positions); z = x_hat + wit must satisfy the instance.
pub fn prove_r1cs<E: ExtField>(
    p: &Params,
    r: &R1cs,
    idx: &Index,
    x: &[Fp],
    wit: &[Fp],
    seed: &Digest,
) -> R1csProof<E> {
    prove_r1cs_with(p, r, idx, x, wit, seed, R1csCheat::None)
}

pub fn prove_r1cs_with<E: ExtField>(
    p: &Params,
    r: &R1cs,
    idx: &Index,
    x: &[Fp],
    wit: &[Fp],
    seed: &Digest,
    cheat: R1csCheat,
) -> R1csProof<E> {
    let nn = p.big_n();
    assert_eq!(p.n, r.n);
    let mut z = wit.to_vec();
    for (&i, &v) in r.inputs.iter().zip(x) {
        z[i] = z[i] + v;
    }
    let mut abc: Vec<Vec<Fp>> = r.mats.iter().map(|m| m.matvec(&z)).collect();
    let az_true = abc[0].clone();
    if cheat != R1csCheat::None {
        abc[0][nn - 1] = abc[0][nn - 1] + Fp::ONE;
    }
    let mut tr = init_transcript::<E>(p, &idx.roots, r, x);
    let mut salts = Vec::new();
    // round 1: (w, a, b, c)
    let g_wit = commit_group(
        p,
        vec![wit.to_vec(), abc[0].clone(), abc[1].clone(), abc[2].clone()],
        seed,
        b"r1cs-wit",
    );
    tr.absorb(b"root", &g_wit.tree.root());
    salts.push(round_salt(seed, 101, p.salt_len));
    tr.absorb(b"salt", salts.last().unwrap());
    // round 2: eta; e, zeta, p for each matrix
    let eta: E = tr.challenge();
    let mut l1 = Vec::new();
    for (mi, m) in r.mats.iter().enumerate() {
        let mut e: Vec<E> = m.row.iter().map(|&rw| eta.pow(rw as u64)).collect();
        let mut zeta: Vec<E> = m.col.iter().map(|&c| E::from(z[c])).collect();
        let mut pp: Vec<E> = e.iter().zip(&zeta).map(|(&a, &b)| a * b).collect();
        if mi == 0 && matches!(cheat, R1csCheat::WrongAForgeZeta | R1csCheat::WrongAForgeE) {
            // repair sum_k val_k p_k = sum_w eta^w a(w) at one entry k0 with val_k0 != 0
            let diff = (0..nn).fold(E::ZERO, |acc, w| {
                acc + eta.pow(w as u64) * (E::from(abc[0][w]) - E::from(az_true[w]))
            });
            let k0 = (0..nn).find(|&k| m.val[k] != Fp::ZERO).unwrap();
            pp[k0] = pp[k0] + diff * E::from(m.val[k0].inv());
            if cheat == R1csCheat::WrongAForgeZeta {
                zeta[k0] = pp[k0] * e[k0].inv();
            } else {
                e[k0] = pp[k0] * zeta[k0].inv();
            }
        }
        l1.push(e);
        l1.push(zeta);
        l1.push(pp);
    }
    let g_l1 = commit_group(p, l1.clone(), seed, b"r1cs-L1");
    tr.absorb(b"root", &g_l1.tree.root());
    salts.push(round_salt(seed, 102, p.salt_len));
    tr.absorb(b"salt", salts.last().unwrap());
    // round 3: x_R, y_R, x_C, y_C; phi, psi for each matrix, and the sums
    let ch: [E; 4] = [
        tr.challenge(),
        tr.challenge(),
        tr.challenge(),
        tr.challenge(),
    ];
    let [xr, yr, xc, yc] = ch;
    let fe = |w: usize| E::from(Fp::new(w as u64));
    let geo: Vec<E> = (0..nn)
        .scan(E::ONE, |acc, _| {
            let c = *acc;
            *acc = *acc * eta;
            Some(c)
        })
        .collect();
    let mut l2 = Vec::new();
    let mut sums = Vec::new();
    for (mi, m) in r.mats.iter().enumerate() {
        let (mr, mc) = m.multiplicities();
        let (e, zeta, pp) = (&l1[3 * mi], &l1[3 * mi + 1], &l1[3 * mi + 2]);
        let phr = batch_inv(
            &(0..nn)
                .map(|k| xr - fe(m.row[k]) - yr * e[k])
                .collect::<Vec<_>>(),
        );
        let psr: Vec<E> = batch_inv(
            &(0..nn)
                .map(|w| xr - fe(w) - yr * geo[w])
                .collect::<Vec<_>>(),
        )
        .into_iter()
        .zip(&mr)
        .map(|(d, &mm)| d * mm)
        .collect();
        let phc = batch_inv(
            &(0..nn)
                .map(|k| xc - fe(m.col[k]) - yc * zeta[k])
                .collect::<Vec<_>>(),
        );
        let psc: Vec<E> = batch_inv(
            &(0..nn)
                .map(|w| xc - fe(w) - yc * E::from(z[w]))
                .collect::<Vec<_>>(),
        )
        .into_iter()
        .zip(&mc)
        .map(|(d, &mm)| d * mm)
        .collect();
        let sum = |v: &[E]| v.iter().fold(E::ZERO, |s, &a| s + a);
        let s = (0..nn).fold(E::ZERO, |acc, k| acc + pp[k] * m.val[k]);
        sums.push([s, sum(&phr), sum(&phc)]);
        l2.push(phr);
        l2.push(psr);
        l2.push(phc);
        l2.push(psc);
    }
    let g_l2 = commit_group(p, l2, seed, b"r1cs-L2");
    tr.absorb(b"root", &g_l2.tree.root());
    for s3 in &sums {
        for v in s3 {
            tr.absorb(b"sum", &e_bytes(v));
        }
    }
    salts.push(round_salt(seed, 103, p.salt_len));
    tr.absorb(b"salt", salts.last().unwrap());
    // round 4: the engine
    let stmts = statements(r, x, eta, ch, &sums);
    let groups = [
        GData::Base(&g_wit),
        GData::Base(&idx.groups[0]),
        GData::Base(&idx.groups[1]),
        GData::Base(&idx.groups[2]),
        GData::Ext(&g_l1),
        GData::Ext(&g_l2),
    ];
    let engine = prove_affine(p, &mut tr, seed, 104, &groups, &stmts);
    R1csProof {
        root_wit: g_wit.tree.root(),
        root_l1: g_l1.tree.root(),
        root_l2: g_l2.tree.root(),
        salts,
        sums,
        engine,
    }
}

pub fn verify_r1cs<E: ExtField>(
    p: &Params,
    r: &R1cs,
    idx_roots: &[Digest],
    x: &[Fp],
    proof: &R1csProof<E>,
) -> Result<(), &'static str> {
    if idx_roots.len() != 3
        || x.len() != r.inputs.len()
        || proof.salts.len() != 3
        || proof.salts.iter().any(|s| s.len() != p.salt_len)
        || proof.sums.len() != 3
        || p.n != r.n
    {
        return Err("shape");
    }
    let mut tr = init_transcript::<E>(p, idx_roots, r, x);
    tr.absorb(b"root", &proof.root_wit);
    tr.absorb(b"salt", &proof.salts[0]);
    let eta: E = tr.challenge();
    tr.absorb(b"root", &proof.root_l1);
    tr.absorb(b"salt", &proof.salts[1]);
    let ch: [E; 4] = [
        tr.challenge(),
        tr.challenge(),
        tr.challenge(),
        tr.challenge(),
    ];
    tr.absorb(b"root", &proof.root_l2);
    for s3 in &proof.sums {
        for v in s3 {
            tr.absorb(b"sum", &e_bytes(v));
        }
    }
    tr.absorb(b"salt", &proof.salts[2]);
    let stmts = statements(r, x, eta, ch, &proof.sums);
    let roots = [
        proof.root_wit,
        idx_roots[0],
        idx_roots[1],
        idx_roots[2],
        proof.root_l1,
        proof.root_l2,
    ];
    let shapes = [
        Shape {
            base: true,
            words: 4,
        },
        Shape {
            base: true,
            words: 5,
        },
        Shape {
            base: true,
            words: 5,
        },
        Shape {
            base: true,
            words: 5,
        },
        Shape {
            base: false,
            words: 9,
        },
        Shape {
            base: false,
            words: 12,
        },
    ];
    verify_affine(p, &mut tr, &roots, &shapes, &stmts, &proof.engine)
}

/// A satisfiable test instance: variables [0, N/2) are free, variable N/2 + i holds the product
/// (A z)_i (B z)_i for constraint i < N/2; A and B read only free variables; C selects the
/// product slot. The first `ninputs` free variables are public.
pub fn sample_instance(
    n: usize,
    per_row: usize,
    ninputs: usize,
    seed: u64,
) -> (R1cs, Vec<Fp>, Vec<Fp>) {
    let nn = 1usize << n;
    let half = nn / 2;
    let mut s = seed | 1;
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    let mut ea = Vec::new();
    let mut eb = Vec::new();
    let mut ec = Vec::new();
    for i in 0..half {
        for _ in 0..per_row {
            if ea.len() < nn {
                ea.push((i, next() as usize % half, Fp::new(next())));
            }
            if eb.len() < nn {
                eb.push((i, next() as usize % half, Fp::new(next())));
            }
        }
        ec.push((i, half + i, Fp::ONE));
    }
    let a = Sparse::new(n, ea);
    let b = Sparse::new(n, eb);
    let c = Sparse::new(n, ec);
    let mut z: Vec<Fp> = (0..nn)
        .map(|i| if i < half { Fp::new(next()) } else { Fp::ZERO })
        .collect();
    let az = a.matvec(&z);
    let bz = b.matvec(&z);
    for i in 0..half {
        z[half + i] = az[i] * bz[i];
    }
    let inputs: Vec<usize> = (0..ninputs).collect();
    let x: Vec<Fp> = inputs.iter().map(|&i| z[i]).collect();
    let mut wit = z.clone();
    for &i in &inputs {
        wit[i] = Fp::ZERO;
    }
    (
        R1cs {
            n,
            mats: [a, b, c],
            inputs,
        },
        x,
        wit,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{Fp2, Fp4};

    fn run<E: ExtField>() {
        for (n, ell, fold_log, cap_log) in [(3, 1, 1, 0), (5, 3, 2, 1), (7, 5, 3, 3)] {
            let p = Params {
                n,
                log_inv_rate: 2,
                ell,
                queries: 20,
                salt_len: 16,
                fold_log,
                cap_log,
            };
            let (r, x, wit) = sample_instance(n, 2, 2, 7 + n as u64);
            let idx = index(&p, &r, &[1u8; 32]);
            let pr = prove_r1cs::<E>(&p, &r, &idx, &x, &wit, &[2u8; 32]);
            assert_eq!(verify_r1cs(&p, &r, &idx.roots, &x, &pr), Ok(()), "n={n}");
            // a wrong public input
            let mut x2 = x.clone();
            x2[0] = x2[0] + Fp::ONE;
            assert!(verify_r1cs(&p, &r, &idx.roots, &x2, &pr).is_err());
            // an unsatisfied constraint: change one product slot of the witness
            let mut w2 = wit.clone();
            let slot = (1usize << n) / 2;
            w2[slot] = w2[slot] + Fp::ONE;
            let pr2 = prove_r1cs::<E>(&p, &r, &idx, &x, &w2, &[3u8; 32]);
            assert_eq!(
                verify_r1cs(&p, &r, &idx.roots, &x, &pr2),
                Err("fold"),
                "n={n}"
            );
            // a false lincheck, alone or repaired by a forged lookup value
            for cheat in [
                R1csCheat::WrongA,
                R1csCheat::WrongAForgeZeta,
                R1csCheat::WrongAForgeE,
            ] {
                let pr = prove_r1cs_with::<E>(&p, &r, &idx, &x, &wit, &[5u8; 32], cheat);
                assert_eq!(
                    verify_r1cs(&p, &r, &idx.roots, &x, &pr),
                    Err("fold"),
                    "n={n} {cheat:?}"
                );
            }
            // a witness that is not zero on an input position
            let mut w3 = wit.clone();
            w3[0] = w3[0] + Fp::ONE;
            let pr3 = prove_r1cs::<E>(&p, &r, &idx, &x, &w3, &[4u8; 32]);
            assert!(verify_r1cs(&p, &r, &idx.roots, &x, &pr3).is_err(), "n={n}");
        }
    }

    #[test]
    fn r1cs_fp2() {
        run::<Fp2>();
    }

    #[test]
    fn r1cs_fp4() {
        run::<Fp4>();
    }
}
