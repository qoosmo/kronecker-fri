//! Prototype of the sumcheck-free inner-product protocol Pi_IP (research note
//! `notes/inner-product`, Section 2; Lean: `KroneckerFRI/InnerProduct.lean`).
//!
//! Commitments are table-form: the table f is committed as the coefficient vector of
//! V_f(X) = sum_w f(w) X^w, i.e. `commit_coeffs` applied to the table (no Moebius transform).
//! The protocol proves S = sum_w a(w) b(w) for two committed tables a, b:
//!
//! 1. X V_a V_b^* = A + S X^N + X^{N+1} H (V_b^* the reversal of V_b); the prover sends w_A = ev_L(A)
//!    (over F_p: every round-1 object lies in the base field);
//! 2. with beta from the verifier, w_0 = w_a + beta w_b^* + beta^2 w_A + beta^3 h, where
//!    w_b^*(xi) = xi^{N-1} w_b(xi^{-1}) and h(xi) = (xi w_a(xi) w_b^*(xi) - w_A(xi) - S xi^N) / xi^{N+1};
//! 3. the folding test of `pcs` runs on w_0.
//!
//! The inverse of the coset above position a of L_g is the coset above position (M_g - a) mod M_g,
//! so each query opens w_a and w_A on one coset and w_b on one coset, as `pcs` does for y and w_A.

use crate::error::Error;
use crate::field::{ExtField, Field, Fp};
use crate::merkle::{
    Digest, GroupOpening, MerkleTree, Transcript, root_from_cap, verify_group_capped,
};
use crate::pcs::{
    Params, ProverData, coset_tree, coset_values, distinct_positions, e_bytes, fold_coset,
    inv_powers, pair_bytes, unpair,
};
use crate::poly::{horner, ntt, pfold};

/// Commit to a table in table form: the table is the coefficient vector of V_f.
pub fn commit_table_form(p: &Params, table: &[Fp]) -> Result<(Digest, ProverData), Error> {
    p.validate()?;
    Ok(commit_table_form_seeded(
        p,
        table,
        &crate::rand::fresh_seed()?,
    ))
}

/// As [`commit_table_form`], with the seed of the prover's randomness given by the caller: for tests and
/// test vectors only (feature `insecure-test-vectors`); the seed must never be reused.
pub(crate) fn commit_table_form_seeded(
    p: &Params,
    table: &[Fp],
    seed: &Digest,
) -> (Digest, ProverData) {
    crate::pcs::commit_coeffs_seeded(p, table, seed)
}

/// Product of two polynomials over F_p by NTT (length a.len() + b.len() - 1).
pub fn poly_mul(a: &[Fp], b: &[Fp]) -> Vec<Fp> {
    let len = a.len() + b.len() - 1;
    let size = len.next_power_of_two();
    let omega = Fp::two_adic_root(size.trailing_zeros());
    let (mut fa, mut fb) = (a.to_vec(), b.to_vec());
    fa.resize(size, Fp::ZERO);
    fb.resize(size, Fp::ZERO);
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

/// The opening polynomials of X V_a V_b^* = A + S X^N + X^{N+1} H (Lemma gen-identity).
/// Returns (A, S, H), with A and H of length N.
pub fn ip_opening_polys(a: &[Fp], b: &[Fp]) -> (Vec<Fp>, Fp, Vec<Fp>) {
    let n = a.len();
    let brev: Vec<Fp> = b.iter().rev().copied().collect();
    let q = poly_mul(a, &brev); // degrees 0 .. 2N-2
    let mut aa = Vec::with_capacity(n);
    aa.push(Fp::ZERO);
    aa.extend_from_slice(&q[..n - 1]);
    let s = q[n - 1];
    let mut h = q[n..].to_vec();
    h.push(Fp::ZERO);
    (aa, s, h)
}

/// h(xi) = (xi w_a(xi) w_b^*(xi) - w_A(xi) - S xi^N) xi^{-(N+1)}, all in F_p.
#[inline(always)]
pub fn ip_virtual_value(
    xi: Fp,
    wa: Fp,
    wbs: Fp,
    w_a_open: Fp,
    s: Fp,
    xi_n: Fp,
    inv_xi_n1: Fp,
) -> Fp {
    (xi * wa * wbs - w_a_open - s * xi_n) * inv_xi_n1
}

/// Deviations from the honest prover, for the tests.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IpCheat {
    None,
    /// claim S + 1 with the honest A
    WrongValue,
    /// claim S + 1 and send w_A for A - X^N (degree N), so that h is the honest H
    AbsorbInA,
    /// compute A, H and S from a table b' != b (the committed b is unchanged)
    OtherB,
}

#[derive(Clone, Debug)]
pub struct IpLevel0Opening {
    pub pos: usize,
    /// w_a on the points above `pos`
    pub ya: Vec<[Fp; 2]>,
    pub ya_open: GroupOpening,
    /// w_A on the same points
    pub wa: Vec<[Fp; 2]>,
    pub wa_open: GroupOpening,
}

#[derive(Clone, Debug)]
pub struct IpBOpening {
    /// position (M_{g0} - a) mod M_{g0} for a queried position a of L_{g0}
    pub pos: usize,
    pub yb: Vec<[Fp; 2]>,
    pub open: GroupOpening,
}

#[derive(Clone, Debug)]
pub struct IpLevelOpening<E> {
    pub pos: usize,
    pub vals: Vec<[E; 2]>,
    pub open: GroupOpening,
}

#[derive(Clone, Debug)]
pub struct IpProof<E> {
    pub cap_a: Vec<Digest>,
    pub cap_b: Vec<Digest>,
    /// cap of the tree of w_A
    pub cap_w: Vec<Digest>,
    pub caps: Vec<Vec<Digest>>,
    pub round_salts: Vec<Vec<u8>>,
    pub p: Vec<E>,
    pub level0: Vec<IpLevel0Opening>,
    pub levelb: Vec<IpBOpening>,
    pub levels: Vec<Vec<IpLevelOpening<E>>>,
}

impl<E: ExtField> IpProof<E> {
    pub fn size_bytes(&self) -> usize {
        let e = 8 * E::DEGREE;
        let open =
            |o: &GroupOpening| 32 * o.path.len() + o.salts.iter().map(|s| s.len()).sum::<usize>();
        let mut s = 32 * (self.cap_a.len() + self.cap_b.len() + self.cap_w.len());
        s += 32 * self.caps.iter().map(|c| c.len()).sum::<usize>() + self.p.len() * e;
        s += self.round_salts.iter().map(|x| x.len()).sum::<usize>();
        for o in &self.level0 {
            s += 16 * o.ya.len() + open(&o.ya_open) + 16 * o.wa.len() + open(&o.wa_open);
        }
        for o in &self.levelb {
            s += 16 * o.yb.len() + open(&o.open);
        }
        for lv in &self.levels {
            for o in lv {
                s += 2 * e * o.vals.len() + open(&o.open);
            }
        }
        s
    }
}

fn init_transcript(
    p: &Params,
    root_a: &Digest,
    root_b: &Digest,
    s: Fp,
    degree: usize,
) -> Transcript {
    let mut tr = Transcript::new(b"kronecker-fri/v0.5/ip");
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
    tr.absorb(b"commitment-a", root_a);
    tr.absorb(b"commitment-b", root_b);
    let mut sb = Vec::new();
    s.to_bytes(&mut sb);
    tr.absorb(b"value", &sb);
    tr
}

/// Position of xi^{-1} for xi = omega^pos in L of order m.
#[inline(always)]
fn inv_pos(pos: usize, m: usize) -> usize {
    (m - pos) % m
}

/// Prover: returns S = sum_w a(w) b(w) and the proof.
pub fn prove_ip<E: ExtField>(
    p: &Params,
    pda: &ProverData,
    pdb: &ProverData,
) -> Result<(Fp, IpProof<E>), Error> {
    p.validate()?;
    Ok(prove_ip_seeded(p, pda, pdb, &crate::rand::fresh_seed()?))
}

/// As [`prove_ip`], with the seed of the prover's randomness given by the caller: for tests and
/// test vectors only (feature `insecure-test-vectors`); the seed must never be reused.
pub(crate) fn prove_ip_seeded<E: ExtField>(
    p: &Params,
    pda: &ProverData,
    pdb: &ProverData,
    seed: &Digest,
) -> (Fp, IpProof<E>) {
    prove_ip_with(p, pda, pdb, seed, IpCheat::None)
}

pub(crate) fn prove_ip_with<E: ExtField>(
    p: &Params,
    pda: &ProverData,
    pdb: &ProverData,
    seed: &Digest,
    cheat: IpCheat,
) -> (Fp, IpProof<E>) {
    p.check();
    let (nn, m, ell) = (p.big_n(), p.m(), p.ell);
    assert_eq!(pda.alpha.len(), nn);
    assert_eq!(pdb.alpha.len(), nn);
    let groups = p.groups();
    let omega = p.omega();
    let inv2 = Fp::new(2).inv();
    let inv_x0 = inv_powers(omega, m / 2);
    let salt = |r: usize| -> Vec<u8> {
        let mut h = blake3::Hasher::new_keyed(seed);
        h.update(b"round-salt");
        h.update(&(r as u64).to_le_bytes());
        let mut s = vec![0u8; p.salt_len];
        h.finalize_xof().fill(&mut s);
        s
    };
    let mut round_salts = Vec::with_capacity(ell + 2);

    // opening polynomials of X V_a V_b^*
    let b_used: Vec<Fp> = match cheat {
        IpCheat::OtherB => pdb.alpha.iter().map(|&x| x + Fp::ONE).collect(),
        _ => pdb.alpha.clone(),
    };
    let (mut a_poly, mut s, h_poly) = ip_opening_polys(&pda.alpha, &b_used);
    match cheat {
        IpCheat::WrongValue => s = s + Fp::ONE,
        IpCheat::AbsorbInA => {
            s = s + Fp::ONE;
            a_poly.push(-Fp::ONE);
        }
        _ => {}
    }
    let mut tr = init_transcript(p, &pda.tree0.root(), &pdb.tree0.root(), s, E::DEGREE);

    // round 1: w_A = ev_L(A)
    let mut w_a_open = a_poly.clone();
    w_a_open.resize(m, Fp::ZERO);
    ntt(&mut w_a_open, omega);
    let g0 = groups[0].1;
    let tree_w = coset_tree(&w_a_open, g0, seed, b"ip-round1", p.salt_len);
    tr.absorb(b"root", &tree_w.root());
    round_salts.push(salt(1));
    tr.absorb(b"salt", round_salts.last().unwrap());
    let beta: E = tr.challenge();
    let (beta2, beta3) = (beta * beta, beta * beta * beta);

    // batched word w_0 = w_a + beta w_b^* + beta^2 w_A + beta^3 h
    let (ya, yb) = (&pda.y, &pdb.y);
    let step_n = omega.pow(nn as u64);
    let step_nm1 = omega.pow((nn - 1) as u64);
    let step_inv = omega.pow((m - nn - 1) as u64);
    let (mut x, mut xn, mut xnm1, mut xinv) = (Fp::ONE, Fp::ONE, Fp::ONE, Fp::ONE);
    let mut w0 = Vec::with_capacity(m);
    for i in 0..m {
        let wbs = xnm1 * yb[inv_pos(i, m)];
        let hi = ip_virtual_value(x, ya[i], wbs, w_a_open[i], s, xn, xinv);
        w0.push(E::from(ya[i]) + beta * wbs + beta2 * w_a_open[i] + beta3 * hi);
        x = x * omega;
        xn = xn * step_n;
        xnm1 = xnm1 * step_nm1;
        xinv = xinv * step_inv;
    }
    let brev: Vec<Fp> = pdb.alpha.iter().rev().copied().collect();
    let u0: Vec<E> = (0..nn)
        .map(|i| {
            let ai = if i < a_poly.len() {
                a_poly[i]
            } else {
                Fp::ZERO
            };
            E::from(pda.alpha[i]) + beta * brev[i] + beta2 * ai + beta3 * h_poly[i]
        })
        .collect();

    // rounds 2 .. l+2: the folding test on w_0 (as in `pcs::open_with`)
    let committed: Vec<usize> = groups
        .iter()
        .map(|&(jc, _)| jc)
        .filter(|&jc| jc >= 1)
        .collect();
    let mut kept: Vec<(usize, Vec<E>, MerkleTree)> = Vec::new();
    let mut caps = Vec::new();
    let mut coeffs = u0;
    let mut cur = w0;
    let mut rs: Vec<E> = Vec::with_capacity(ell);
    for j in 1..=ell {
        if j >= 2 && committed.contains(&(j - 1)) {
            let g = groups.iter().find(|&&(st, _)| st == j - 1).unwrap().1;
            let tree = coset_tree(&cur, g, seed, format!("w{}", j - 1).as_bytes(), p.salt_len);
            tr.absorb(b"root", &tree.root());
            caps.push(tree.cap(p.cap_for(cur.len() / 2, g - 1)));
            kept.push((j - 1, cur.clone(), tree));
        }
        round_salts.push(salt(j + 1));
        tr.absorb(b"salt", round_salts.last().unwrap());
        let r: E = tr.challenge();
        rs.push(r);
        coeffs = pfold(&coeffs, r);
        if j < ell {
            cur = crate::poly::fold_word(&cur, r, &inv_x0, j - 1, inv2);
        }
    }
    drop(cur);
    let final_p = coeffs;
    let pb: Vec<u8> = final_p.iter().flat_map(e_bytes).collect();
    tr.absorb(b"final", &pb);
    round_salts.push(salt(ell + 2));
    tr.absorb(b"salt", round_salts.last().unwrap());
    let idx = tr.query_indices(p.queries, p.n + p.log_inv_rate);

    let mg0 = m >> g0;
    let c0 = p.cap_for(m / 2, g0 - 1);
    let level0 = distinct_positions(&idx, mg0)
        .into_iter()
        .map(|a0| IpLevel0Opening {
            pos: a0,
            ya: coset_values(ya, g0, a0),
            ya_open: pda.tree0.open_group_capped(a0 << (g0 - 1), g0 - 1, c0),
            wa: coset_values(&w_a_open, g0, a0),
            wa_open: tree_w.open_group_capped(a0 << (g0 - 1), g0 - 1, c0),
        })
        .collect();
    let inv_idx: Vec<usize> = idx.iter().map(|&i| inv_pos(i % mg0, mg0)).collect();
    let levelb = distinct_positions(&inv_idx, mg0)
        .into_iter()
        .map(|ab| IpBOpening {
            pos: ab,
            yb: coset_values(yb, g0, ab),
            open: pdb.tree0.open_group_capped(ab << (g0 - 1), g0 - 1, c0),
        })
        .collect();
    let levels = kept
        .iter()
        .map(|(jc, word, tree)| {
            let g = groups.iter().find(|&&(st, _)| st == *jc).unwrap().1;
            let c = p.cap_for(word.len() / 2, g - 1);
            distinct_positions(&idx, m >> (jc + g))
                .into_iter()
                .map(|aj| IpLevelOpening {
                    pos: aj,
                    vals: coset_values(word, g, aj),
                    open: tree.open_group_capped(aj << (g - 1), g - 1, c),
                })
                .collect()
        })
        .collect();
    (
        s,
        IpProof {
            cap_a: pda.tree0.cap(c0),
            cap_b: pdb.tree0.cap(c0),
            cap_w: tree_w.cap(c0),
            caps,
            round_salts,
            p: final_p,
            level0,
            levelb,
            levels,
        },
    )
}

/// Verifier with the reason for rejection: "shape", "merkle" or "fold".
pub fn verify_ip<E: ExtField>(
    p: &Params,
    root_a: &Digest,
    root_b: &Digest,
    s: Fp,
    proof: &IpProof<E>,
) -> Result<(), Error> {
    p.validate()?;
    let (nn, m, ell) = (p.big_n(), p.m(), p.ell);
    let groups = p.groups();
    let g0 = groups[0].1;
    let ncommit = groups.len() - 1;
    let h0 = 1usize << (g0 - 1);
    if proof.caps.len() != ncommit
        || proof.levels.len() != ncommit
        || proof.round_salts.len() != ell + 2
        || proof.p.len() != nn >> ell
        || proof
            .level0
            .iter()
            .any(|o| o.ya.len() != h0 || o.wa.len() != h0)
        || proof.levelb.iter().any(|o| o.yb.len() != h0)
    {
        return Err(Error::Shape);
    }
    for (i, &(_, g)) in groups.iter().enumerate().skip(1) {
        if proof.levels[i - 1]
            .iter()
            .any(|o| o.vals.len() != 1 << (g - 1))
        {
            return Err(Error::Shape);
        }
    }
    let sl = p.salt_len;
    let op_ok = |op: &GroupOpening, depth: usize, h: usize, c: usize| {
        op.path.len() == depth - h - c && op.salts.iter().all(|x| x.len() == sl)
    };
    let depth0 = (m / 2).trailing_zeros() as usize;
    let c0 = p.cap_for(m / 2, g0 - 1);
    if proof.round_salts.iter().any(|x| x.len() != sl)
        || proof.cap_a.len() != 1 << c0
        || proof.cap_b.len() != 1 << c0
        || proof.cap_w.len() != 1 << c0
        || proof.level0.iter().any(|o| {
            !op_ok(&o.ya_open, depth0, g0 - 1, c0) || !op_ok(&o.wa_open, depth0, g0 - 1, c0)
        })
        || proof
            .levelb
            .iter()
            .any(|o| !op_ok(&o.open, depth0, g0 - 1, c0))
    {
        return Err(Error::Shape);
    }
    for (i, &(jc, g)) in groups.iter().enumerate().skip(1) {
        let leaves = (m >> jc) / 2;
        let (depth, c) = (leaves.trailing_zeros() as usize, p.cap_for(leaves, g - 1));
        if proof.caps[i - 1].len() != 1 << c
            || proof.levels[i - 1]
                .iter()
                .any(|o| !op_ok(&o.open, depth, g - 1, c))
        {
            return Err(Error::Shape);
        }
    }
    if root_from_cap(&proof.cap_a)? != *root_a || root_from_cap(&proof.cap_b)? != *root_b {
        return Err(Error::Merkle);
    }
    let omega = p.omega();
    let mut tr = init_transcript(p, root_a, root_b, s, E::DEGREE);
    tr.absorb(b"root", &root_from_cap(&proof.cap_w)?);
    tr.absorb(b"salt", &proof.round_salts[0]);
    let beta: E = tr.challenge();
    let (beta2, beta3) = (beta * beta, beta * beta * beta);
    let mut rs: Vec<E> = Vec::with_capacity(ell);
    let mut ci = 0;
    for j in 1..=ell {
        if j >= 2 && groups.iter().any(|&(st, _)| st == j - 1) {
            tr.absorb(b"root", &root_from_cap(&proof.caps[ci])?);
            ci += 1;
        }
        tr.absorb(b"salt", &proof.round_salts[j]);
        rs.push(tr.challenge());
    }
    let pb: Vec<u8> = proof.p.iter().flat_map(e_bytes).collect();
    tr.absorb(b"final", &pb);
    tr.absorb(b"salt", &proof.round_salts[ell + 1]);
    let idx = tr.query_indices(p.queries, p.n + p.log_inv_rate);

    let mg0 = m >> g0;
    let pos0 = distinct_positions(&idx, mg0);
    let inv_idx: Vec<usize> = idx.iter().map(|&i| inv_pos(i % mg0, mg0)).collect();
    let posb = distinct_positions(&inv_idx, mg0);
    if proof.level0.len() != pos0.len()
        || proof.level0.iter().zip(&pos0).any(|(o, &a)| o.pos != a)
        || proof.levelb.len() != posb.len()
        || proof.levelb.iter().zip(&posb).any(|(o, &a)| o.pos != a)
    {
        return Err(Error::Shape);
    }
    for (gi, &(jc, g)) in groups.iter().enumerate().skip(1) {
        let pj = distinct_positions(&idx, m >> (jc + g));
        let lv = &proof.levels[gi - 1];
        if lv.len() != pj.len() || lv.iter().zip(&pj).any(|(o, &a)| o.pos != a) {
            return Err(Error::Shape);
        }
    }
    for o in &proof.level0 {
        let ad: Vec<Vec<u8>> = o.ya.iter().map(|[x, y]| pair_bytes(x, y)).collect();
        let wd: Vec<Vec<u8>> = o.wa.iter().map(|[x, y]| pair_bytes(x, y)).collect();
        if !verify_group_capped(&proof.cap_a, o.pos << (g0 - 1), g0 - 1, &ad, &o.ya_open)
            || !verify_group_capped(&proof.cap_w, o.pos << (g0 - 1), g0 - 1, &wd, &o.wa_open)
        {
            return Err(Error::Merkle);
        }
    }
    for o in &proof.levelb {
        let bd: Vec<Vec<u8>> = o.yb.iter().map(|[x, y]| pair_bytes(x, y)).collect();
        if !verify_group_capped(&proof.cap_b, o.pos << (g0 - 1), g0 - 1, &bd, &o.open) {
            return Err(Error::Merkle);
        }
    }
    for (gi, &(_, g)) in groups.iter().enumerate().skip(1) {
        for o in &proof.levels[gi - 1] {
            let d: Vec<Vec<u8>> = o.vals.iter().map(|[x, y]| pair_bytes(x, y)).collect();
            if !verify_group_capped(&proof.caps[gi - 1], o.pos << (g - 1), g - 1, &d, &o.open) {
                return Err(Error::Merkle);
            }
        }
    }
    let find = |list: &[usize], a: usize| list.binary_search(&a).unwrap();
    let level_pos: Vec<Vec<usize>> = proof
        .levels
        .iter()
        .map(|lv| lv.iter().map(|o| o.pos).collect())
        .collect();
    for &i0 in &idx {
        let a0 = i0 % mg0;
        let ab = inv_pos(a0, mg0);
        let o = &proof.level0[find(&pos0, a0)];
        let ob = &proof.levelb[find(&posb, ab)];
        let (yav, wav, ybv) = (unpair(&o.ya), unpair(&o.wa), unpair(&ob.yb));
        let w0: Vec<E> = (0..yav.len())
            .map(|t| {
                let pos = a0 + t * mg0;
                let ipos = inv_pos(pos, m);
                let tb = (ipos - ab) / mg0;
                let xi = omega.pow(pos as u64);
                let xi_n = omega.pow(((pos * nn) % m) as u64);
                let xi_nm1 = omega.pow(((pos * (nn - 1)) % m) as u64);
                let inv = omega.pow(((m - (pos * (nn + 1)) % m) % m) as u64);
                let wbs = xi_nm1 * ybv[tb];
                let h = ip_virtual_value(xi, yav[t], wbs, wav[t], s, xi_n, inv);
                E::from(yav[t]) + beta * wbs + beta2 * wav[t] + beta3 * h
            })
            .collect();
        let mut value = fold_coset(w0, a0, 0, mg0, &rs, m, omega);
        for (gi, &(jc, g)) in groups.iter().enumerate().skip(1) {
            let mg = m >> (jc + g);
            let aj = i0 % mg;
            let o = &proof.levels[gi - 1][find(&level_pos[gi - 1], aj)];
            let vals = unpair(&o.vals);
            let pos = i0 % (m >> jc);
            if vals[(pos - aj) / mg] != value {
                return Err(Error::Fold);
            }
            value = fold_coset(vals, aj, jc, mg, &rs, m, omega);
        }
        let pos = i0 % (m >> ell);
        let eta = omega.pow((pos as u64) << ell);
        if value != horner(&proof.p, E::from(eta)) {
            return Err(Error::Fold);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{Fp2, Fp4};

    struct Rng(u64);
    impl Rng {
        fn fp(&mut self) -> Fp {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            Fp::new(self.0)
        }
    }

    fn naive_mul(a: &[Fp], b: &[Fp]) -> Vec<Fp> {
        let mut c = vec![Fp::ZERO; a.len() + b.len() - 1];
        for (i, &x) in a.iter().enumerate() {
            for (j, &y) in b.iter().enumerate() {
                c[i + j] = c[i + j] + x * y;
            }
        }
        c
    }

    #[test]
    fn poly_mul_matches_naive() {
        let mut rng = Rng(5);
        for (la, lb) in [(1, 1), (2, 3), (8, 8), (13, 40), (64, 64)] {
            let a: Vec<Fp> = (0..la).map(|_| rng.fp()).collect();
            let b: Vec<Fp> = (0..lb).map(|_| rng.fp()).collect();
            assert_eq!(poly_mul(&a, &b), naive_mul(&a, &b));
        }
    }

    /// Lemma ip and Lemma gen-identity: S = sum a b, and X V_a V_b^* = A + S X^N + X^{N+1} H.
    #[test]
    fn opening_polys_and_inner_product() {
        let mut rng = Rng(7);
        for n in 1..=8usize {
            let nn = 1 << n;
            let a: Vec<Fp> = (0..nn).map(|_| rng.fp()).collect();
            let b: Vec<Fp> = (0..nn).map(|_| rng.fp()).collect();
            let (aa, s, h) = ip_opening_polys(&a, &b);
            let direct = a.iter().zip(&b).fold(Fp::ZERO, |acc, (&x, &y)| acc + x * y);
            assert_eq!(s, direct);
            let brev: Vec<Fp> = b.iter().rev().copied().collect();
            let mut lhs = vec![Fp::ZERO];
            lhs.extend(naive_mul(&a, &brev));
            let mut rhs = vec![Fp::ZERO; 2 * nn + 1];
            for i in 0..nn {
                rhs[i] = rhs[i] + aa[i];
                rhs[nn + 1 + i] = rhs[nn + 1 + i] + h[i];
            }
            rhs[nn] = rhs[nn] + s;
            lhs.resize(2 * nn + 1, Fp::ZERO);
            assert_eq!(lhs, rhs);
        }
    }

    /// Lemma rev(1): w_b^*(xi) = xi^{N-1} w_b(xi^{-1}) is ev_L(V_b^*).
    #[test]
    fn reversed_word_is_codeword() {
        let mut rng = Rng(11);
        for n in 1..=6usize {
            let p = Params::new(n, 2, 1, 1, 0);
            let (nn, m) = (p.big_n(), p.m());
            let b: Vec<Fp> = (0..nn).map(|_| rng.fp()).collect();
            let (_, pd) = commit_table_form_seeded(&p, &b, &[0u8; 32]);
            let brev: Vec<Fp> = b.iter().rev().copied().collect();
            let omega = p.omega();
            for i in 0..m {
                let x = omega.pow(i as u64);
                let wbs = x.pow((nn - 1) as u64) * pd.y[inv_pos(i, m)];
                assert_eq!(wbs, horner(&brev, x));
            }
        }
    }

    fn run<E: ExtField>() {
        let mut rng = Rng(99);
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
                let (ra, pda) = commit_table_form_seeded(&p, &a, &[1u8; 32]);
                let (rb, pdb) = commit_table_form_seeded(&p, &b, &[2u8; 32]);
                let (s, proof) = prove_ip_seeded::<E>(&p, &pda, &pdb, &[3u8; 32]);
                let direct = a.iter().zip(&b).fold(Fp::ZERO, |acc, (&x, &y)| acc + x * y);
                assert_eq!(s, direct);
                assert_eq!(verify_ip(&p, &ra, &rb, s, &proof), Ok(()), "n={n} l={ell}");
                // wrong claim, wrong commitment order, and the three cheating provers
                assert!(verify_ip(&p, &ra, &rb, s + Fp::ONE, &proof).is_err());
                if a != b {
                    assert!(verify_ip(&p, &rb, &ra, s, &proof).is_err());
                }
                for cheat in [IpCheat::WrongValue, IpCheat::AbsorbInA, IpCheat::OtherB] {
                    let (s1, pr1) = prove_ip_with::<E>(&p, &pda, &pdb, &[4u8; 32], cheat);
                    assert_eq!(
                        verify_ip(&p, &ra, &rb, s1, &pr1),
                        Err(Error::Fold),
                        "n={n} l={ell} {cheat:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn ip_complete_and_sound_fp2() {
        run::<Fp2>();
    }

    #[test]
    fn ip_complete_and_sound_fp4() {
        run::<Fp4>();
    }
}
