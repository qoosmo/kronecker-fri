//! Baseline for the research note (`notes/inner-product`, Section 5.3): the core of a
//! Spartan-style R1CS argument on the same commitment, field, hash and instances as `r1cs`.
//!
//! Protocol (Setty, Spartan, CRYPTO 2020, without the SPARK compiler):
//! 1. the prover commits the witness table w with `pcs::commit_table` (the only commitment);
//! 2. tau <- F^n; outer sumcheck (degree 3) of sum_x eq(tau, x) (Az(x) Bz(x) - Cz(x)) = 0, with
//!    z = x_hat + w; the prover sends va = Az~(rx), vb = Bz~(rx), vc = Cz~(rx);
//! 3. rA, rB, rC <- F; inner sumcheck (degree 2) of
//!    sum_y (rA A~(rx, y) + rB B~(rx, y) + rC C~(rx, y)) z~(y) = rA va + rB vb + rC vc;
//! 4. the prover opens w at ry with Pi_KF; the verifier computes x_hat~(ry) and the matrix value
//!    M~(rx, ry) = sum_mat r_mat sum_k val_k eq(rx, row_k) eq(ry, col_k) itself.
//!
//! Step 4 makes the verifier linear in the number of nonzero entries: this is Spartan with a
//! non-succinct verifier. Full Spartan replaces the verifier's computation of M~(rx, ry) by SPARK
//! (a committed index and a memory-checking argument), which adds prover work; the prover time
//! measured here is therefore a lower bound for a Spartan prover on this commitment.
//!
//! Tables are indexed by w in [0, N), bit k of w being variable k (the convention of `pcs`), and
//! the sumchecks bind variable 0 first.

use crate::field::{ExtField, Field, Fp};
use crate::merkle::{Digest, Transcript};
use crate::pcs::{self, Params, e_bytes};
use crate::r1cs::R1cs;

/// A proof of the Spartan core.
pub struct SpartanProof<E> {
    pub root: Digest,
    /// outer sumcheck: the round polynomial at 0, 1, 2, 3 for each variable
    pub outer: Vec<[E; 4]>,
    /// Az~(rx), Bz~(rx), Cz~(rx)
    pub claims: [E; 3],
    /// inner sumcheck: the round polynomial at 0, 1, 2 for each variable
    pub inner: Vec<[E; 3]>,
    /// w~(ry)
    pub w_eval: E,
    pub pcs: pcs::Proof<E>,
}

impl<E: ExtField> SpartanProof<E> {
    pub fn size_bytes(&self) -> usize {
        let e = 8 * E::DEGREE;
        32 + e * (4 * self.outer.len() + 3 + 3 * self.inner.len() + 1) + self.pcs.size_bytes()
    }
}

/// Timings of the prover phases, in seconds.
#[derive(Clone, Copy, Debug, Default)]
pub struct SpartanTimes {
    pub commit: f64,
    pub sumchecks: f64,
    pub open: f64,
}

/// eq(t, x) for all x in [0, 2^n), bit k of x paired with t_k.
pub fn eq_table<E: ExtField>(t: &[E]) -> Vec<E> {
    let mut v = vec![E::ONE];
    for &tk in t {
        let len = v.len();
        let mut next = vec![E::ZERO; 2 * len];
        for j in 0..len {
            let hi = v[j] * tk;
            next[j + len] = hi;
            next[j] = v[j] - hi;
        }
        v = next;
    }
    v
}

/// eq(a, b) for two points.
fn eq_point<E: ExtField>(a: &[E], b: &[E]) -> E {
    a.iter().zip(b).fold(E::ONE, |acc, (&x, &y)| {
        acc * (x * y + (E::ONE - x) * (E::ONE - y))
    })
}

/// The polynomial of degree < vals.len() with values vals[i] at i, evaluated at r.
fn interpolate<E: ExtField>(vals: &[E], r: E) -> E {
    let d = vals.len();
    let mut acc = E::ZERO;
    for i in 0..d {
        let mut num = E::ONE;
        let mut den = Fp::ONE;
        for j in 0..d {
            if j != i {
                num = num * (r - E::from(Fp::new(j as u64)));
                den = den * (Fp::new(i as u64) - Fp::new(j as u64));
            }
        }
        acc = acc + vals[i] * num * den.inv();
    }
    acc
}

/// Fold a table on variable 0 at r: f'(i) = f(2i) + r (f(2i+1) - f(2i)).
fn fold<E: ExtField>(f: &[E], r: E) -> Vec<E> {
    (0..f.len() / 2)
        .map(|i| f[2 * i] + r * (f[2 * i + 1] - f[2 * i]))
        .collect()
}

fn absorb_es<E: ExtField>(tr: &mut Transcript, tag: &[u8], xs: &[E]) {
    let mut b = Vec::new();
    for x in xs {
        b.extend(e_bytes(x));
    }
    tr.absorb(tag, &b);
}

fn init_transcript(p: &Params, r: &R1cs, root: &Digest, x: &[Fp]) -> Transcript {
    let mut tr = Transcript::new(b"spartan-core-v1");
    let pb: Vec<u8> = [
        p.n,
        p.log_inv_rate,
        p.ell,
        p.queries,
        p.salt_len,
        p.fold_log,
        p.cap_log,
    ]
    .iter()
    .flat_map(|&v| (v as u64).to_le_bytes())
    .collect();
    tr.absorb(b"params", &pb);
    tr.absorb(b"root", root);
    let mut ib = Vec::new();
    for (&i, v) in r.inputs.iter().zip(x) {
        ib.extend((i as u64).to_le_bytes());
        v.to_bytes(&mut ib);
    }
    tr.absorb(b"input", &ib);
    tr
}

/// The table x_hat of the public input.
fn x_hat(r: &R1cs, x: &[Fp]) -> Vec<Fp> {
    let mut t = vec![Fp::ZERO; 1 << r.n];
    for (&i, &v) in r.inputs.iter().zip(x) {
        t[i] = v;
    }
    t
}

/// The prover. `wit` is zero on the input positions and z = x_hat + wit satisfies the instance.
pub fn prove_spartan<E: ExtField>(
    p: &Params,
    r: &R1cs,
    x: &[Fp],
    wit: &[Fp],
    seed: &Digest,
) -> (SpartanProof<E>, SpartanTimes) {
    let n = r.n;
    let nn = 1usize << n;
    let mut times = SpartanTimes::default();
    let t0 = std::time::Instant::now();
    let (root, pd) = pcs::commit_table(p, wit, seed);
    times.commit = t0.elapsed().as_secs_f64();

    let t1 = std::time::Instant::now();
    let mut tr = init_transcript(p, r, &root, x);
    let xh = x_hat(r, x);
    let z: Vec<Fp> = (0..nn).map(|i| xh[i] + wit[i]).collect();
    let [ma, mb, mc] = &r.mats;
    let lift = |v: Vec<Fp>| -> Vec<E> { v.into_iter().map(E::from).collect() };
    let mut az = lift(ma.matvec(&z));
    let mut bz = lift(mb.matvec(&z));
    let mut cz = lift(mc.matvec(&z));
    let tau: Vec<E> = (0..n).map(|_| tr.challenge()).collect();
    let mut eq = eq_table(&tau);

    // outer sumcheck, degree 3
    let mut outer = Vec::with_capacity(n);
    let mut rx = Vec::with_capacity(n);
    for _ in 0..n {
        let half = eq.len() / 2;
        let mut s = [E::ZERO; 4];
        for i in 0..half {
            let (e0, e1) = (eq[2 * i], eq[2 * i + 1]);
            let (a0, a1) = (az[2 * i], az[2 * i + 1]);
            let (b0, b1) = (bz[2 * i], bz[2 * i + 1]);
            let (c0, c1) = (cz[2 * i], cz[2 * i + 1]);
            let (de, da, db, dc) = (e1 - e0, a1 - a0, b1 - b0, c1 - c0);
            let (mut e, mut a, mut b, mut c) = (e0, a0, b0, c0);
            for t in 0..4 {
                if t > 0 {
                    e = e + de;
                    a = a + da;
                    b = b + db;
                    c = c + dc;
                }
                s[t] = s[t] + e * (a * b - c);
            }
        }
        absorb_es(&mut tr, b"outer", &s);
        let ri: E = tr.challenge();
        outer.push(s);
        rx.push(ri);
        eq = fold(&eq, ri);
        az = fold(&az, ri);
        bz = fold(&bz, ri);
        cz = fold(&cz, ri);
    }
    let claims = [az[0], bz[0], cz[0]];
    absorb_es(&mut tr, b"claims", &claims);
    let (ra, rb, rc): (E, E, E) = (tr.challenge(), tr.challenge(), tr.challenge());

    // inner sumcheck, degree 2
    let eq_rx = eq_table(&rx);
    let mut mt = vec![E::ZERO; nn];
    for (mat, rm) in [(ma, ra), (mb, rb), (mc, rc)] {
        for k in 0..mat.row.len() {
            let v = mat.val[k];
            if v != Fp::ZERO {
                mt[mat.col[k]] = mt[mat.col[k]] + rm * eq_rx[mat.row[k]] * v;
            }
        }
    }
    let mut zt = lift(z);
    let mut inner = Vec::with_capacity(n);
    let mut ry = Vec::with_capacity(n);
    for _ in 0..n {
        let half = mt.len() / 2;
        let mut s = [E::ZERO; 3];
        for i in 0..half {
            let (m0, m1) = (mt[2 * i], mt[2 * i + 1]);
            let (z0, z1) = (zt[2 * i], zt[2 * i + 1]);
            s[0] = s[0] + m0 * z0;
            s[1] = s[1] + m1 * z1;
            s[2] = s[2] + (m1 + m1 - m0) * (z1 + z1 - z0);
        }
        absorb_es(&mut tr, b"inner", &s);
        let ri: E = tr.challenge();
        inner.push(s);
        ry.push(ri);
        mt = fold(&mt, ri);
        zt = fold(&zt, ri);
    }
    times.sumchecks = t1.elapsed().as_secs_f64();

    let t2 = std::time::Instant::now();
    let (w_eval, pcs_proof) = pcs::open(p, &pd, &ry, seed);
    times.open = t2.elapsed().as_secs_f64();
    (
        SpartanProof {
            root,
            outer,
            claims,
            inner,
            w_eval,
            pcs: pcs_proof,
        },
        times,
    )
}

/// The verifier (linear in the number of nonzero entries: it computes M~(rx, ry) itself).
pub fn verify_spartan<E: ExtField>(
    p: &Params,
    r: &R1cs,
    x: &[Fp],
    pf: &SpartanProof<E>,
) -> Result<(), &'static str> {
    let n = r.n;
    if pf.outer.len() != n || pf.inner.len() != n {
        return Err("shape");
    }
    let mut tr = init_transcript(p, r, &pf.root, x);
    let tau: Vec<E> = (0..n).map(|_| tr.challenge()).collect();
    let mut claim = E::ZERO;
    let mut rx = Vec::with_capacity(n);
    for s in &pf.outer {
        if s[0] + s[1] != claim {
            return Err("outer sumcheck");
        }
        absorb_es(&mut tr, b"outer", s);
        let ri: E = tr.challenge();
        claim = interpolate(s, ri);
        rx.push(ri);
    }
    let [va, vb, vc] = pf.claims;
    if claim != eq_point(&tau, &rx) * (va * vb - vc) {
        return Err("outer final");
    }
    absorb_es(&mut tr, b"claims", &pf.claims);
    let (ra, rb, rc): (E, E, E) = (tr.challenge(), tr.challenge(), tr.challenge());
    let mut claim = ra * va + rb * vb + rc * vc;
    let mut ry = Vec::with_capacity(n);
    for s in &pf.inner {
        if s[0] + s[1] != claim {
            return Err("inner sumcheck");
        }
        absorb_es(&mut tr, b"inner", s);
        let ri: E = tr.challenge();
        claim = interpolate(s, ri);
        ry.push(ri);
    }
    // the verifier's own evaluations: x_hat~(ry) and M~(rx, ry)
    let eq_rx = eq_table(&rx);
    let eq_ry = eq_table(&ry);
    let mut xv = E::ZERO;
    for (&i, &v) in r.inputs.iter().zip(x) {
        xv = xv + eq_ry[i] * v;
    }
    let mut mv = E::ZERO;
    for (mat, rm) in r.mats.iter().zip([ra, rb, rc]) {
        let mut acc = E::ZERO;
        for k in 0..mat.row.len() {
            let v = mat.val[k];
            if v != Fp::ZERO {
                acc = acc + eq_rx[mat.row[k]] * eq_ry[mat.col[k]] * v;
            }
        }
        mv = mv + rm * acc;
    }
    if claim != mv * (xv + pf.w_eval) {
        return Err("inner final");
    }
    if !pcs::verify(p, &pf.root, &ry, pf.w_eval, &pf.pcs) {
        return Err("pcs");
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{Fp2, Fp4};
    use crate::r1cs::sample_instance;

    #[test]
    fn eq_table_matches_mle_convention() {
        // pcs::open returns f~(z) with bit k of the index paired with z_k
        let n = 5;
        let p = Params::recommended(n, 20, 16);
        let table: Vec<Fp> = (0..1u64 << n).map(|i| Fp::new(i * i + 3)).collect();
        let (_, pd) = pcs::commit_table(&p, &table, &[3u8; 32]);
        let z: Vec<Fp2> = (0..n)
            .map(|k| Fp2(Fp::new(5 + k as u64), Fp::new(7 * k as u64)))
            .collect();
        let (v, _) = pcs::open(&p, &pd, &z, &[4u8; 32]);
        let eq = eq_table(&z);
        let direct = table
            .iter()
            .zip(&eq)
            .fold(Fp2::ZERO, |acc, (&t, &e)| acc + e * t);
        assert_eq!(v, direct);
    }

    fn run<E: ExtField>() {
        for n in [4, 6, 8] {
            let p = Params::recommended(n, 20, 16);
            let (r, x, wit) = sample_instance(n, 2, 2, 11 + n as u64);
            let (pf, _) = prove_spartan::<E>(&p, &r, &x, &wit, &[5u8; 32]);
            assert_eq!(verify_spartan(&p, &r, &x, &pf), Ok(()));
            // a wrong public input
            let mut x2 = x.clone();
            x2[0] = x2[0] + Fp::ONE;
            assert!(verify_spartan(&p, &r, &x2, &pf).is_err());
            // an unsatisfied constraint
            let mut w2 = wit.clone();
            let last = w2.len() - 1;
            w2[last] = w2[last] + Fp::ONE;
            let (pf2, _) = prove_spartan::<E>(&p, &r, &x, &w2, &[6u8; 32]);
            assert!(verify_spartan(&p, &r, &x, &pf2).is_err());
            // a wrong claim Cz~(rx)
            let (mut pf4, _) = prove_spartan::<E>(&p, &r, &x, &wit, &[8u8; 32]);
            pf4.claims[2] = pf4.claims[2] + E::ONE;
            assert_eq!(verify_spartan(&p, &r, &x, &pf4), Err("outer final"));
            // a wrong opening value
            let (mut pf5, _) = prove_spartan::<E>(&p, &r, &x, &wit, &[9u8; 32]);
            pf5.w_eval = pf5.w_eval + E::ONE;
            assert_eq!(verify_spartan(&p, &r, &x, &pf5), Err("inner final"));
            // a tampered round polynomial
            let (mut pf3, _) = prove_spartan::<E>(&p, &r, &x, &wit, &[7u8; 32]);
            pf3.inner[1][2] = pf3.inner[1][2] + E::ONE;
            assert!(verify_spartan(&p, &r, &x, &pf3).is_err());
        }
    }

    #[test]
    fn spartan_fp2() {
        run::<Fp2>();
    }

    #[test]
    fn spartan_fp4() {
        run::<Fp4>();
    }
}
