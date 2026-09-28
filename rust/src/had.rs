//! Prototype of the sumcheck-free Hadamard check Pi_Had (research note `notes/inner-product`,
//! Section 3): for committed tables a, b, c (table form, as in `ip`), prove a(w) b(w) = c(w) for
//! all w in {0,1}^n.
//!
//! 1. gamma <- E \ F_p.  The prover sends w_Q = ev_L(Q), Q(X) = V_a(gamma X).
//! 2. theta <- E with theta, gamma theta outside F_p.  The prover sends y1 = V_a(gamma theta) = Q(theta),
//!    y3 = V_c(gamma), and w_A = ev_L(A) with X Q V_b^* = A + y3 X^N + X^{N+1} H.
//! 3. beta <- E.  w_0 = sum_{i=0}^{8} beta^i u_i with
//!    u = (w_a, w_c, w_Q, w_b^*, w_A, h, q_a, q_Q, q_c), where
//!    h = (X w_Q w_b^* - w_A - y3 X^N) / X^{N+1}, q_a = (w_a - y1)/(X - gamma theta),
//!    q_Q = (w_Q - y1)/(X - theta), q_c = (w_c - y3)/(X - gamma).
//! 4. The folding test on w_0.
//!
//! L lies in F_p, so gamma, theta, gamma theta outside F_p are outside L: no quotient has a pole on L.

use crate::error::Error;
use crate::field::{ExtField, Field, Fp, batch_inv};
use crate::ft::{
    CosetOpening, FtProof, check_level0, coset_of, ft_check_query, ft_prove, ft_replay,
    open_cosets, open_size, round_salt,
};
use crate::merkle::{Digest, Transcript, root_from_cap};
use crate::pcs::{Params, ProverData, coset_tree, distinct_positions, e_bytes};
use crate::poly::{horner, ntt};

/// Product of two polynomials over E by NTT.
pub fn poly_mul_e<E: ExtField>(a: &[E], b: &[E]) -> Vec<E> {
    let len = a.len() + b.len() - 1;
    let size = len.next_power_of_two();
    let omega = Fp::two_adic_root(size.trailing_zeros());
    let (mut fa, mut fb) = (a.to_vec(), b.to_vec());
    fa.resize(size, E::ZERO);
    fb.resize(size, E::ZERO);
    ntt(&mut fa, omega);
    ntt(&mut fb, omega);
    for i in 0..size {
        fa[i] = fa[i] * fb[i];
    }
    ntt(&mut fa, omega.inv());
    let inv = Fp::new(size as u64).inv();
    fa.truncate(len);
    fa.iter().map(|&x| x * inv).collect()
}

/// (P(X) - P(z)) / (X - z) for P of length N, padded to length N.
pub fn div_linear<E: ExtField>(pc: &[E], z: E) -> Vec<E> {
    let n = pc.len();
    let mut q = vec![E::ZERO; n];
    let mut acc = E::ZERO;
    for i in (1..n).rev() {
        acc = acc * z + pc[i];
        q[i - 1] = acc;
    }
    q
}

fn in_base<E: ExtField>(x: &E) -> bool {
    x.digits()[1..].iter().all(|d| *d == Fp::ZERO)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HadCheat {
    None,
    /// y1 + 1
    WrongY1,
    /// Q(X) = V_a(gamma X) + 1, with y1 = Q(theta) and the inner product computed with this Q
    WrongQ,
    /// y3 = V_c(gamma) (honest for c), used also as the claimed inner product
    UseVc,
    /// y3 = sum gamma^w a(w) b(w) (the true inner product)
    UseIp,
}

#[derive(Clone, Debug)]
pub struct HadProof<E> {
    pub cap_a: Vec<Digest>,
    pub cap_b: Vec<Digest>,
    pub cap_c: Vec<Digest>,
    pub cap_q: Vec<Digest>,
    pub cap_w: Vec<Digest>,
    /// salts of the rounds of w_Q and of (y1, y3, w_A)
    pub salts: Vec<Vec<u8>>,
    pub y1: E,
    pub y3: E,
    pub oa: Vec<CosetOpening<Fp>>,
    pub oc: Vec<CosetOpening<Fp>>,
    pub oq: Vec<CosetOpening<E>>,
    pub ow: Vec<CosetOpening<E>>,
    /// w_b on the inverse cosets
    pub ob: Vec<CosetOpening<Fp>>,
    pub ft: FtProof<E>,
}

impl<E: ExtField> HadProof<E> {
    pub fn size_bytes(&self) -> usize {
        let e = 8 * E::DEGREE;
        let caps = self.cap_a.len()
            + self.cap_b.len()
            + self.cap_c.len()
            + self.cap_q.len()
            + self.cap_w.len();
        let mut s = 32 * caps + 2 * e + self.salts.iter().map(|x| x.len()).sum::<usize>();
        s += self
            .oa
            .iter()
            .chain(&self.oc)
            .chain(&self.ob)
            .map(|o| open_size(o, 8))
            .sum::<usize>();
        s += self
            .oq
            .iter()
            .chain(&self.ow)
            .map(|o| open_size(o, e))
            .sum::<usize>();
        s + self.ft.size_bytes()
    }
}

fn init_transcript(p: &Params, roots: [&Digest; 3], degree: usize) -> Transcript {
    let mut tr = Transcript::new(b"kronecker-fri-had-v1");
    let params = [
        p.n,
        p.log_inv_rate,
        p.ell,
        p.queries,
        p.salt_len,
        p.fold_log,
        p.cap_log,
        degree,
    ];
    let pb: Vec<u8> = params
        .iter()
        .flat_map(|&x| (x as u64).to_le_bytes())
        .collect();
    tr.absorb(b"params", &pb);
    for r in roots {
        tr.absorb(b"commitment", r);
    }
    tr
}

/// gamma outside F_p (rejection sampling).
fn draw_gamma<E: ExtField>(tr: &mut Transcript) -> E {
    loop {
        let g: E = tr.challenge();
        if !in_base(&g) {
            return g;
        }
    }
}

/// theta with theta and gamma theta outside F_p (rejection sampling).
fn draw_theta<E: ExtField>(tr: &mut Transcript, gamma: E) -> E {
    loop {
        let t: E = tr.challenge();
        if !in_base(&t) && !in_base(&(gamma * t)) {
            return t;
        }
    }
}

#[inline(always)]
fn inv_pos(pos: usize, m: usize) -> usize {
    (m - pos) % m
}

pub fn prove_had<E: ExtField>(
    p: &Params,
    pda: &ProverData,
    pdb: &ProverData,
    pdc: &ProverData,
    seed: &Digest,
) -> HadProof<E> {
    prove_had_with(p, pda, pdb, pdc, seed, HadCheat::None)
}

pub fn prove_had_with<E: ExtField>(
    p: &Params,
    pda: &ProverData,
    pdb: &ProverData,
    pdc: &ProverData,
    seed: &Digest,
    cheat: HadCheat,
) -> HadProof<E> {
    p.check();
    let (nn, m) = (p.big_n(), p.m());
    let omega = p.omega();
    let g0 = p.groups()[0].1;
    let mut tr = init_transcript(
        p,
        [&pda.tree0.root(), &pdb.tree0.root(), &pdc.tree0.root()],
        E::DEGREE,
    );
    let mut salts = Vec::new();

    // round 1: gamma, then w_Q = ev_L(Q), Q(X) = V_a(gamma X)
    let gamma: E = draw_gamma(&mut tr);
    let mut q: Vec<E> = Vec::with_capacity(nn);
    let mut gp = E::ONE;
    for &ai in &pda.alpha {
        q.push(gp * ai);
        gp = gp * gamma;
    }
    if cheat == HadCheat::WrongQ {
        q[0] = q[0] + E::ONE;
    }
    let mut wq = q.clone();
    wq.resize(m, E::ZERO);
    ntt(&mut wq, omega);
    let tree_q = coset_tree(&wq, g0, seed, b"had-Q", p.salt_len);
    tr.absorb(b"root", &tree_q.root());
    salts.push(round_salt(seed, 1, p.salt_len));
    tr.absorb(b"salt", salts.last().unwrap());

    // round 2: theta, then y1, y3 and w_A
    let theta: E = draw_theta(&mut tr, gamma);
    let mut y1 = horner(&q, theta);
    if cheat == HadCheat::WrongY1 {
        y1 = y1 + E::ONE;
    }
    let vc_gamma = horner(
        &pdc.alpha.iter().map(|&x| E::from(x)).collect::<Vec<_>>(),
        gamma,
    );
    let brev: Vec<E> = pdb.alpha.iter().rev().map(|&x| E::from(x)).collect();
    let prod = poly_mul_e(&q, &brev); // X Q V_b^* = X prod
    let ip = prod[nn - 1];
    let y3 = match cheat {
        HadCheat::UseIp => ip,
        HadCheat::UseVc => vc_gamma,
        _ => vc_gamma, // honest: equal to ip when c = a o b
    };
    let mut a_poly = Vec::with_capacity(nn);
    a_poly.push(E::ZERO);
    a_poly.extend_from_slice(&prod[..nn - 1]);
    let mut h_poly = prod[nn..].to_vec();
    h_poly.push(E::ZERO);
    let mut wa_open = a_poly.clone();
    wa_open.resize(m, E::ZERO);
    ntt(&mut wa_open, omega);
    let tree_w = coset_tree(&wa_open, g0, seed, b"had-A", p.salt_len);
    tr.absorb(b"y1", &e_bytes(&y1));
    tr.absorb(b"y3", &e_bytes(&y3));
    tr.absorb(b"root", &tree_w.root());
    salts.push(round_salt(seed, 2, p.salt_len));
    tr.absorb(b"salt", salts.last().unwrap());
    let beta: E = tr.challenge();
    let bp: Vec<E> = (0..9)
        .scan(E::ONE, |acc, _| {
            let c = *acc;
            *acc = *acc * beta;
            Some(c)
        })
        .collect();

    // the batched word
    let gt = gamma * theta;
    let xs: Vec<Fp> = (0..m)
        .scan(Fp::ONE, |x, _| {
            let c = *x;
            *x = *x * omega;
            Some(c)
        })
        .collect();
    let mut den: Vec<E> = Vec::with_capacity(3 * m);
    for &x in &xs {
        den.push(E::from(x) - gt);
        den.push(E::from(x) - theta);
        den.push(E::from(x) - gamma);
    }
    let dinv = batch_inv(&den);
    drop(den);
    let (ya, yb, yc) = (&pda.y, &pdb.y, &pdc.y);
    let step_n = omega.pow(nn as u64);
    let step_nm1 = omega.pow((nn - 1) as u64);
    let step_inv = omega.pow((m - nn - 1) as u64);
    let (mut xn, mut xnm1, mut xinv) = (Fp::ONE, Fp::ONE, Fp::ONE);
    let mut w0 = Vec::with_capacity(m);
    for i in 0..m {
        let x = xs[i];
        let wbs = xnm1 * yb[inv_pos(i, m)];
        let h = ((wq[i] * x) * wbs - wa_open[i] - y3 * xn) * xinv;
        let qa = (E::from(ya[i]) - y1) * dinv[3 * i];
        let qq = (wq[i] - y1) * dinv[3 * i + 1];
        let qc = (E::from(yc[i]) - y3) * dinv[3 * i + 2];
        let u = [
            E::from(ya[i]),
            E::from(yc[i]),
            wq[i],
            E::from(wbs),
            wa_open[i],
            h,
            qa,
            qq,
            qc,
        ];
        w0.push((0..9).fold(E::ZERO, |acc, k| acc + bp[k] * u[k]));
        xn = xn * step_n;
        xnm1 = xnm1 * step_nm1;
        xinv = xinv * step_inv;
    }
    drop(dinv);
    let va: Vec<E> = pda.alpha.iter().map(|&x| E::from(x)).collect();
    let vc: Vec<E> = pdc.alpha.iter().map(|&x| E::from(x)).collect();
    let polys = [
        va.clone(),
        vc.clone(),
        q.clone(),
        brev,
        a_poly,
        h_poly,
        div_linear(&va, gt),
        div_linear(&q, theta),
        div_linear(&vc, gamma),
    ];
    let u0: Vec<E> = (0..nn)
        .map(|j| (0..9).fold(E::ZERO, |acc, k| acc + bp[k] * polys[k][j]))
        .collect();

    // the folding test, then the level-0 openings
    let (ft, idx) = ft_prove(p, &mut tr, seed, 3, w0, u0);
    let mg0 = m >> g0;
    let pos0 = distinct_positions(&idx, mg0);
    let inv_idx: Vec<usize> = idx.iter().map(|&i| inv_pos(i % mg0, mg0)).collect();
    let posb = distinct_positions(&inv_idx, mg0);
    let c0 = p.cap_for(m / 2, g0 - 1);
    HadProof {
        cap_a: pda.tree0.cap(c0),
        cap_b: pdb.tree0.cap(c0),
        cap_c: pdc.tree0.cap(c0),
        cap_q: tree_q.cap(c0),
        cap_w: tree_w.cap(c0),
        salts,
        y1,
        y3,
        oa: open_cosets(p, &pda.tree0, ya, &pos0, g0, 0),
        oc: open_cosets(p, &pdc.tree0, yc, &pos0, g0, 0),
        oq: open_cosets(p, &tree_q, &wq, &pos0, g0, 0),
        ow: open_cosets(p, &tree_w, &wa_open, &pos0, g0, 0),
        ob: open_cosets(p, &pdb.tree0, yb, &posb, g0, 0),
        ft,
    }
}

/// Verifier with the reason for rejection: "shape", "merkle" or "fold".
pub fn verify_had<E: ExtField>(
    p: &Params,
    roots: [&Digest; 3],
    proof: &HadProof<E>,
) -> Result<(), Error> {
    p.validate()?;
    let (nn, m) = (p.big_n(), p.m());
    let omega = p.omega();
    let g0 = p.groups()[0].1;
    if proof.salts.len() != 2 || proof.salts.iter().any(|s| s.len() != p.salt_len) {
        return Err(Error::Shape);
    }
    if root_from_cap(&proof.cap_a)? != *roots[0]
        || root_from_cap(&proof.cap_b)? != *roots[1]
        || root_from_cap(&proof.cap_c)? != *roots[2]
    {
        return Err(Error::Merkle);
    }
    let mut tr = init_transcript(p, roots, E::DEGREE);
    let gamma: E = draw_gamma(&mut tr);
    tr.absorb(b"root", &root_from_cap(&proof.cap_q)?);
    tr.absorb(b"salt", &proof.salts[0]);
    let theta: E = draw_theta(&mut tr, gamma);
    let (y1, y3) = (proof.y1, proof.y3);
    tr.absorb(b"y1", &e_bytes(&y1));
    tr.absorb(b"y3", &e_bytes(&y3));
    tr.absorb(b"root", &root_from_cap(&proof.cap_w)?);
    tr.absorb(b"salt", &proof.salts[1]);
    let beta: E = tr.challenge();
    let bp: Vec<E> = (0..9)
        .scan(E::ONE, |acc, _| {
            let c = *acc;
            *acc = *acc * beta;
            Some(c)
        })
        .collect();
    let (rs, idx) = ft_replay(p, &mut tr, &proof.ft)?;
    let mg0 = m >> g0;
    let pos0 = distinct_positions(&idx, mg0);
    let inv_idx: Vec<usize> = idx.iter().map(|&i| inv_pos(i % mg0, mg0)).collect();
    let posb = distinct_positions(&inv_idx, mg0);
    check_level0(p, &proof.cap_a, &proof.oa, &pos0)?;
    check_level0(p, &proof.cap_c, &proof.oc, &pos0)?;
    check_level0(p, &proof.cap_q, &proof.oq, &pos0)?;
    check_level0(p, &proof.cap_w, &proof.ow, &pos0)?;
    check_level0(p, &proof.cap_b, &proof.ob, &posb)?;
    let gt = gamma * theta;
    for &i0 in &idx {
        let a0 = i0 % mg0;
        let ab = inv_pos(a0, mg0);
        let (va, vc, vq, vw, vb) = (
            coset_of(&proof.oa, a0),
            coset_of(&proof.oc, a0),
            coset_of(&proof.oq, a0),
            coset_of(&proof.ow, a0),
            coset_of(&proof.ob, ab),
        );
        let w0: Vec<E> = (0..va.len())
            .map(|t| {
                let pos = a0 + t * mg0;
                let tb = (inv_pos(pos, m) - ab) / mg0;
                let x = omega.pow(pos as u64);
                let xn = omega.pow(((pos * nn) % m) as u64);
                let xnm1 = omega.pow(((pos * (nn - 1)) % m) as u64);
                let xinv = omega.pow(((m - (pos * (nn + 1)) % m) % m) as u64);
                let xe = E::from(x);
                let wbs = xnm1 * vb[tb];
                let h = ((vq[t] * x) * wbs - vw[t] - y3 * xn) * xinv;
                let qa = (E::from(va[t]) - y1) * (xe - gt).inv();
                let qq = (vq[t] - y1) * (xe - theta).inv();
                let qc = (E::from(vc[t]) - y3) * (xe - gamma).inv();
                let u = [
                    E::from(va[t]),
                    E::from(vc[t]),
                    vq[t],
                    E::from(wbs),
                    vw[t],
                    h,
                    qa,
                    qq,
                    qc,
                ];
                (0..9).fold(E::ZERO, |acc, k| acc + bp[k] * u[k])
            })
            .collect();
        ft_check_query(p, &proof.ft, &rs, i0, w0)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{Fp2, Fp4};
    use crate::ip::commit_table_form;

    struct Rng(u64);
    impl Rng {
        fn fp(&mut self) -> Fp {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            Fp::new(self.0)
        }
    }

    #[test]
    fn div_linear_is_quotient() {
        let mut rng = Rng(3);
        let pc: Vec<Fp2> = (0..16).map(|_| Fp2(rng.fp(), rng.fp())).collect();
        let z = Fp2(rng.fp(), rng.fp());
        let q = div_linear(&pc, z);
        assert_eq!(q[15], Fp2::ZERO);
        let v = horner(&pc, z);
        for _ in 0..5 {
            let x = Fp2(rng.fp(), rng.fp());
            assert_eq!(horner(&pc, x) - v, horner(&q, x) * (x - z));
        }
    }

    fn run<E: ExtField>() {
        let mut rng = Rng(2024);
        for (n, ell, fold_log, cap_log) in [
            (1, 1, 1, 0),
            (4, 2, 1, 0),
            (6, 3, 1, 2),
            (8, 8, 3, 3),
            (10, 5, 2, 0),
            (10, 9, 4, 4),
        ] {
            for r in [2, 3] {
                let p = Params {
                    n,
                    log_inv_rate: r,
                    ell,
                    queries: 30,
                    salt_len: 32,
                    fold_log,
                    cap_log,
                };
                let a: Vec<Fp> = (0..1 << n).map(|_| rng.fp()).collect();
                let b: Vec<Fp> = (0..1 << n).map(|_| rng.fp()).collect();
                let c: Vec<Fp> = a.iter().zip(&b).map(|(&x, &y)| x * y).collect();
                let (ra, pda) = commit_table_form(&p, &a, &[1u8; 32]);
                let (rb, pdb) = commit_table_form(&p, &b, &[2u8; 32]);
                let (rc, pdc) = commit_table_form(&p, &c, &[3u8; 32]);
                let proof = prove_had::<E>(&p, &pda, &pdb, &pdc, &[4u8; 32]);
                assert_eq!(
                    verify_had(&p, [&ra, &rb, &rc], &proof),
                    Ok(()),
                    "n={n} l={ell} R={r}"
                );
                for cheat in [HadCheat::WrongY1, HadCheat::WrongQ] {
                    let pr = prove_had_with::<E>(&p, &pda, &pdb, &pdc, &[5u8; 32], cheat);
                    assert_eq!(
                        verify_had(&p, [&ra, &rb, &rc], &pr),
                        Err(Error::Fold),
                        "n={n} l={ell} {cheat:?}"
                    );
                }
                // a false instance: c' differs from a o b in one entry
                let mut c2 = c.clone();
                let k = (rng.fp().0 as usize) % (1 << n);
                c2[k] = c2[k] + Fp::ONE;
                let (rc2, pdc2) = commit_table_form(&p, &c2, &[6u8; 32]);
                for cheat in [HadCheat::None, HadCheat::UseVc, HadCheat::UseIp] {
                    let pr = prove_had_with::<E>(&p, &pda, &pdb, &pdc2, &[7u8; 32], cheat);
                    assert_eq!(
                        verify_had(&p, [&ra, &rb, &rc2], &pr),
                        Err(Error::Fold),
                        "false instance n={n} l={ell} {cheat:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn had_complete_and_sound_fp2() {
        run::<Fp2>();
    }

    #[test]
    fn had_complete_and_sound_fp4() {
        run::<Fp4>();
    }
}
