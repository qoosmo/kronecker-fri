//! Pi_Batch on affine forms (research note `notes/inner-product`, Proposition 5.1): evaluation,
//! inner-product and Hadamard statements whose arguments are affine forms
//! `sum_i c_i w_i + sum_j d_j P_j` of committed words `w_i` and public tables `P_j`, proved with
//! one folding test.
//!
//! Committed words live in *groups*: one Merkle tree per group whose leaves hold one value of
//! every word of the group (a group is committed at once, e.g. the index of a matrix, or all the
//! prover's tables of one round). A group holds base-field words (`Fp`) or extension words (`E`).
//!
//! The curve contains, in this order: the committed words read directly, the reversals of the
//! committed words read reversed, the w_Q of the Hadamard checks, the w_A and h of every
//! statement, and the quotient words of the Hadamard checks (q[lambda_a, y1, gamma theta] and
//! q[lambda_c, y3, gamma] only when the form has a committed part; otherwise the verifier checks
//! y1 = V(gamma theta), y3 = V(gamma) directly).

use crate::batch::{
    MultiOpening, draw_outside, evalker_coeffs, evalker_eval, evalker_on_domain, inv_pos,
    multi_check, multi_coset, multi_open, multi_tree, powers, split,
};
use crate::field::{ExtField, Field, Fp, batch_inv};
use crate::ft::{FtProof, ft_check_query, ft_prove, ft_replay, round_salt};
use crate::had::{div_linear, poly_mul_e};
use crate::lincheck::{v_id, v_one};
use crate::merkle::{Digest, MerkleTree, Transcript, root_from_cap};
use crate::pcs::{Params, distinct_positions, e_bytes};
use crate::poly::{horner, ntt};

/// A public table: its table-form polynomial is evaluated by the verifier.
#[derive(Clone, Debug, PartialEq)]
pub enum Pub<E> {
    One,
    Zero,
    Id,
    /// w -> eta^w
    Geo(E),
    /// explicit entries (w, value), zero elsewhere
    Sparse(Vec<(usize, E)>),
}

impl<E: ExtField> Pub<E> {
    fn coeffs(&self, nn: usize) -> Vec<E> {
        match self {
            Pub::One => vec![E::ONE; nn],
            Pub::Zero => vec![E::ZERO; nn],
            Pub::Id => (0..nn).map(|w| E::from(Fp::new(w as u64))).collect(),
            Pub::Geo(eta) => (0..nn)
                .scan(E::ONE, |acc, _| {
                    let c = *acc;
                    *acc = *acc * *eta;
                    Some(c)
                })
                .collect(),
            Pub::Sparse(es) => {
                let mut v = vec![E::ZERO; nn];
                for &(w, c) in es {
                    v[w] = v[w] + c;
                }
                v
            }
        }
    }
    /// V_P(x).
    pub fn eval(&self, n: usize, x: E) -> E {
        match self {
            Pub::One => v_one(n, x),
            Pub::Zero => E::ZERO,
            Pub::Id => v_id(n, x),
            Pub::Geo(eta) => v_one(n, *eta * x),
            Pub::Sparse(es) => es
                .iter()
                .fold(E::ZERO, |acc, &(w, c)| acc + c * x.pow(w as u64)),
        }
    }
}

/// A committed word: word `word` of group `group`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OId {
    pub group: usize,
    pub word: usize,
}

/// An affine form sum c_i w_i + sum d_j P_j.
#[derive(Clone, Debug, PartialEq)]
pub struct Form<E> {
    pub com: Vec<(OId, E)>,
    pub pubs: Vec<(Pub<E>, E)>,
}

impl<E: ExtField> Form<E> {
    pub fn word(o: OId) -> Self {
        Form {
            com: vec![(o, E::ONE)],
            pubs: vec![],
        }
    }
    pub fn public(p: Pub<E>) -> Self {
        Form {
            com: vec![],
            pubs: vec![(p, E::ONE)],
        }
    }
    fn has_committed(&self) -> bool {
        self.com.iter().any(|(_, c)| *c != E::ZERO)
    }
    fn oids(&self) -> impl Iterator<Item = OId> + '_ {
        self.com
            .iter()
            .filter(|(_, c)| *c != E::ZERO)
            .map(|(o, _)| *o)
    }
    fn eval_pub(&self, n: usize, x: E) -> E {
        self.pubs
            .iter()
            .fold(E::ZERO, |acc, (p, d)| acc + *d * p.eval(n, x))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum AStmt<E> {
    Eval(Form<E>, Vec<E>, E),
    Ip(Form<E>, Form<E>, E),
    Had(Form<E>, Form<E>, Form<E>),
}

/// The prover's data of a group: coefficients and evaluations on L of every word, and the tree.
pub struct GroupData<T> {
    pub coeffs: Vec<Vec<T>>,
    pub evals: Vec<Vec<T>>,
    pub tree: MerkleTree,
}

/// Commit to a group of words given by their coefficients (length N).
pub fn commit_group<T: Field + core::ops::Mul<Fp, Output = T>>(
    p: &Params,
    coeffs: Vec<Vec<T>>,
    seed: &Digest,
    label: &[u8],
) -> GroupData<T> {
    let m = p.m();
    let omega = p.omega();
    let evals: Vec<Vec<T>> = coeffs
        .iter()
        .map(|c| {
            let mut v = c.clone();
            v.resize(m, T::ZERO);
            ntt(&mut v, omega);
            v
        })
        .collect();
    let g0 = p.groups()[0].1;
    let refs: Vec<&[T]> = evals.iter().map(|v| v.as_slice()).collect();
    let tree = multi_tree(&refs, g0, seed, label, p.salt_len);
    GroupData {
        coeffs,
        evals,
        tree,
    }
}

/// A group seen by the engine's prover.
pub enum GData<'a, E> {
    Base(&'a GroupData<Fp>),
    Ext(&'a GroupData<E>),
}

impl<E: ExtField> GData<'_, E> {
    fn coeffs(&self, w: usize) -> Vec<E> {
        match self {
            GData::Base(g) => g.coeffs[w].iter().map(|&x| E::from(x)).collect(),
            GData::Ext(g) => g.coeffs[w].clone(),
        }
    }
    fn eval_at(&self, w: usize, i: usize) -> E {
        match self {
            GData::Base(g) => E::from(g.evals[w][i]),
            GData::Ext(g) => g.evals[w][i],
        }
    }
    fn cap(&self, c: usize) -> Vec<Digest> {
        match self {
            GData::Base(g) => g.tree.cap(c),
            GData::Ext(g) => g.tree.cap(c),
        }
    }
}

/// Shape of a group, known to the verifier: base or extension, number of words.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shape {
    pub base: bool,
    pub words: usize,
}

/// Openings of one group.
#[derive(Clone, Debug)]
pub enum GOpen<E> {
    Base {
        direct: Vec<MultiOpening<Fp>>,
        rev: Vec<MultiOpening<Fp>>,
    },
    Ext {
        direct: Vec<MultiOpening<E>>,
        rev: Vec<MultiOpening<E>>,
    },
}

#[derive(Clone, Debug)]
pub struct AffineProof<E> {
    pub gcaps: Vec<Vec<Digest>>,
    pub gopen: Vec<GOpen<E>>,
    pub cap_q: Vec<Digest>,
    pub cap_w: Vec<Digest>,
    pub salts: Vec<Vec<u8>>,
    pub ys: Vec<(E, E)>,
    pub oq: Vec<MultiOpening<E>>,
    pub ow: Vec<MultiOpening<E>>,
    pub ft: FtProof<E>,
}

fn mopen_size<T>(o: &MultiOpening<T>, elem: usize) -> usize {
    2 * elem * o.vals.iter().map(|v| v.len()).sum::<usize>()
        + 32 * o.open.path.len()
        + o.open.salts.iter().map(|s| s.len()).sum::<usize>()
}

impl<E: ExtField> AffineProof<E> {
    /// Size in bytes; the caps of the groups are counted by the caller if they are not already
    /// known to the verifier (`with_group_caps`).
    pub fn size_bytes(&self, with_group_caps: bool) -> usize {
        let e = 8 * E::DEGREE;
        let mut s = 32 * (self.cap_q.len() + self.cap_w.len()) + 2 * e * self.ys.len();
        if with_group_caps {
            s += 32 * self.gcaps.iter().map(|c| c.len()).sum::<usize>();
        }
        s += self.salts.iter().map(|x| x.len()).sum::<usize>();
        for g in &self.gopen {
            s += match g {
                GOpen::Base { direct, rev } => direct
                    .iter()
                    .chain(rev)
                    .map(|o| mopen_size(o, 8))
                    .sum::<usize>(),
                GOpen::Ext { direct, rev } => direct
                    .iter()
                    .chain(rev)
                    .map(|o| mopen_size(o, e))
                    .sum::<usize>(),
            };
        }
        s += self
            .oq
            .iter()
            .chain(&self.ow)
            .map(|o| mopen_size(o, e))
            .sum::<usize>();
        s + self.ft.size_bytes()
    }
}

/// The layout of the curve.
struct Plan {
    direct: Vec<OId>,
    rev: Vec<OId>,
    had: Vec<usize>,
    qa: Vec<bool>,
    qc: Vec<bool>,
    nwords: usize,
}

fn plan<E: ExtField>(stmts: &[AStmt<E>]) -> Plan {
    let (mut direct, mut rev, mut had, mut qa, mut qc) =
        (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new());
    for (j, s) in stmts.iter().enumerate() {
        match s {
            AStmt::Eval(f, _, _) => direct.extend(f.oids()),
            AStmt::Ip(f, g, _) => {
                direct.extend(f.oids());
                rev.extend(g.oids());
            }
            AStmt::Had(a, b, c) => {
                direct.extend(a.oids());
                direct.extend(c.oids());
                rev.extend(b.oids());
                had.push(j);
                qa.push(a.has_committed());
                qc.push(c.has_committed());
            }
        }
    }
    direct.sort_unstable();
    direct.dedup();
    rev.sort_unstable();
    rev.dedup();
    let nq = qa.iter().filter(|&&b| b).count() + qc.iter().filter(|&&b| b).count() + had.len();
    let nwords = direct.len() + rev.len() + had.len() + 2 * stmts.len() + nq;
    Plan {
        direct,
        rev,
        had,
        qa,
        qc,
        nwords,
    }
}

/// Number of words t + 1 of the curve for these statements.
pub fn affine_words<E: ExtField>(stmts: &[AStmt<E>]) -> usize {
    plan(stmts).nwords
}

fn absorb_stmts<E: ExtField>(tr: &mut Transcript, stmts: &[AStmt<E>]) {
    let form_bytes = |f: &Form<E>, b: &mut Vec<u8>| {
        b.extend((f.com.len() as u64).to_le_bytes());
        for (o, c) in &f.com {
            b.extend((o.group as u64).to_le_bytes());
            b.extend((o.word as u64).to_le_bytes());
            b.extend(e_bytes(c));
        }
        b.extend((f.pubs.len() as u64).to_le_bytes());
        for (pb, d) in &f.pubs {
            match pb {
                Pub::One => b.push(0),
                Pub::Zero => b.push(1),
                Pub::Id => b.push(2),
                Pub::Geo(eta) => {
                    b.push(3);
                    b.extend(e_bytes(eta));
                }
                Pub::Sparse(es) => {
                    b.push(4);
                    b.extend((es.len() as u64).to_le_bytes());
                    for (w, c) in es {
                        b.extend((*w as u64).to_le_bytes());
                        b.extend(e_bytes(c));
                    }
                }
            }
            b.extend(e_bytes(d));
        }
    };
    for s in stmts {
        let mut b = Vec::new();
        match s {
            AStmt::Eval(f, z, v) => {
                b.push(0);
                form_bytes(f, &mut b);
                for zi in z {
                    b.extend(e_bytes(zi));
                }
                b.extend(e_bytes(v));
            }
            AStmt::Ip(f, g, v) => {
                b.push(1);
                form_bytes(f, &mut b);
                form_bytes(g, &mut b);
                b.extend(e_bytes(v));
            }
            AStmt::Had(a, bb, c) => {
                b.push(2);
                form_bytes(a, &mut b);
                form_bytes(bb, &mut b);
                form_bytes(c, &mut b);
            }
        }
        tr.absorb(b"affine-statement", &b);
    }
}

/// The prover of the engine.  `tr` has absorbed the context (commitments, earlier rounds);
/// `first_round` numbers the salts.
pub fn prove_affine<E: ExtField>(
    p: &Params,
    tr: &mut Transcript,
    seed: &Digest,
    first_round: usize,
    groups: &[GData<E>],
    stmts: &[AStmt<E>],
) -> AffineProof<E> {
    let (nn, m) = (p.big_n(), p.m());
    let omega = p.omega();
    let g0 = p.groups()[0].1;
    let pl = plan(stmts);
    absorb_stmts(tr, stmts);
    let mut salts = Vec::new();

    let pub_evals = |pb: &Pub<E>| -> Vec<E> {
        let mut v = pb.coeffs(nn);
        v.resize(m, E::ZERO);
        ntt(&mut v, omega);
        v
    };
    let form_coeffs = |f: &Form<E>| -> Vec<E> {
        let mut out = vec![E::ZERO; nn];
        for (o, c) in &f.com {
            for (x, y) in out.iter_mut().zip(groups[o.group].coeffs(o.word)) {
                *x = *x + *c * y;
            }
        }
        for (pb, d) in &f.pubs {
            for (x, y) in out.iter_mut().zip(pb.coeffs(nn)) {
                *x = *x + *d * y;
            }
        }
        out
    };
    let form_evals = |f: &Form<E>| -> Vec<E> {
        let mut out = vec![E::ZERO; m];
        for (o, c) in &f.com {
            let g = &groups[o.group];
            for (i, x) in out.iter_mut().enumerate() {
                *x = *x + *c * g.eval_at(o.word, i);
            }
        }
        for (pb, d) in &f.pubs {
            for (x, y) in out.iter_mut().zip(pub_evals(pb)) {
                *x = *x + *d * y;
            }
        }
        out
    };
    let xs: Vec<Fp> = (0..m)
        .scan(Fp::ONE, |x, _| {
            let c = *x;
            *x = *x * omega;
            Some(c)
        })
        .collect();
    let step_nm1 = omega.pow((nn - 1) as u64);
    let xnm1: Vec<Fp> = (0..m)
        .scan(Fp::ONE, |x, _| {
            let c = *x;
            *x = *x * step_nm1;
            Some(c)
        })
        .collect();
    let reversed = |ev: &[E]| -> Vec<E> { (0..m).map(|i| ev[inv_pos(i, m)] * xnm1[i]).collect() };

    // round 1: gamma, the w_Q of the Hadamard checks
    let gamma: E = draw_outside(tr, None);
    let mut qcoef: Vec<Vec<E>> = Vec::new();
    for &j in &pl.had {
        if let AStmt::Had(a, _, _) = &stmts[j] {
            let mut gp = E::ONE;
            let q: Vec<E> = form_coeffs(a)
                .into_iter()
                .map(|x| {
                    let v = gp * x;
                    gp = gp * gamma;
                    v
                })
                .collect();
            qcoef.push(q);
        }
    }
    let tree_q = if pl.had.is_empty() {
        None
    } else {
        Some(commit_group(p, qcoef.clone(), seed, b"affine-Q"))
    };
    if let Some(t) = &tree_q {
        tr.absorb(b"root", &t.tree.root());
    }
    salts.push(round_salt(seed, first_round, p.salt_len));
    tr.absorb(b"salt", salts.last().unwrap());

    // round 2: theta, y1 and y3, the w_A of every statement
    let theta: E = draw_outside(tr, Some(gamma));
    let mut ys = Vec::new();
    let mut acoef = Vec::new();
    let mut hcoef = Vec::new();
    let mut vals = Vec::new();
    let mut ucoef = Vec::new(); // U_j
    let mut hi = 0;
    for s in stmts {
        let (u, k, v) = match s {
            AStmt::Eval(f, z, v) => (form_coeffs(f), evalker_coeffs(z), *v),
            AStmt::Ip(f, g, v) => {
                let mut gr = form_coeffs(g);
                gr.reverse();
                (form_coeffs(f), gr, *v)
            }
            AStmt::Had(_, b, c) => {
                let q = qcoef[hi].clone();
                let y1 = horner(&q, theta);
                let y3 = horner(&form_coeffs(c), gamma);
                ys.push((y1, y3));
                hi += 1;
                let mut br = form_coeffs(b);
                br.reverse();
                (q, br, y3)
            }
        };
        let prod = poly_mul_e(&u, &k);
        let (a, _, h) = split(&prod, nn);
        acoef.push(a);
        hcoef.push(h);
        vals.push(v);
        ucoef.push(u);
    }
    drop(ucoef);
    for (y1, y3) in &ys {
        tr.absorb(b"y1", &e_bytes(y1));
        tr.absorb(b"y3", &e_bytes(y3));
    }
    let tree_w = commit_group(p, acoef.clone(), seed, b"affine-A");
    tr.absorb(b"root", &tree_w.tree.root());
    salts.push(round_salt(seed, first_round + 1, p.salt_len));
    tr.absorb(b"salt", salts.last().unwrap());
    let beta: E = tr.challenge();
    let bp = powers(beta, pl.nwords);

    // the batched word, one word at a time
    let mut w0 = vec![E::ZERO; m];
    let mut u0 = vec![E::ZERO; nn];
    let mut s = 0usize;
    let mut add = |ev: &[E], co: &[E], s: &mut usize| {
        let b = bp[*s];
        for (x, y) in w0.iter_mut().zip(ev) {
            *x = *x + b * *y;
        }
        for (x, y) in u0.iter_mut().zip(co) {
            *x = *x + b * *y;
        }
        *s += 1;
    };
    for o in &pl.direct {
        let g = &groups[o.group];
        let ev: Vec<E> = (0..m).map(|i| g.eval_at(o.word, i)).collect();
        add(&ev, &g.coeffs(o.word), &mut s);
    }
    for o in &pl.rev {
        let g = &groups[o.group];
        let ev: Vec<E> = (0..m).map(|i| g.eval_at(o.word, i)).collect();
        let mut co = g.coeffs(o.word);
        co.reverse();
        add(&reversed(&ev), &co, &mut s);
    }
    let qd = tree_q.as_ref();
    for k in 0..pl.had.len() {
        let q = qd.unwrap();
        add(&q.evals[k], &q.coeffs[k], &mut s);
    }
    for j in 0..stmts.len() {
        add(&tree_w.evals[j], &tree_w.coeffs[j], &mut s);
    }
    // h_j
    let step_n = omega.pow(nn as u64);
    let step_inv = omega.pow((m - nn - 1) as u64);
    let xn: Vec<Fp> = (0..m)
        .scan(Fp::ONE, |x, _| {
            let c = *x;
            *x = *x * step_n;
            Some(c)
        })
        .collect();
    let xinv: Vec<Fp> = (0..m)
        .scan(Fp::ONE, |x, _| {
            let c = *x;
            *x = *x * step_inv;
            Some(c)
        })
        .collect();
    let mut hi = 0;
    for (j, st) in stmts.iter().enumerate() {
        let (uev, kev): (Vec<E>, Vec<E>) = match st {
            AStmt::Eval(f, z, _) => (form_evals(f), evalker_on_domain(z, omega, m)),
            AStmt::Ip(f, g, _) => (form_evals(f), reversed(&form_evals(g))),
            AStmt::Had(_, b, _) => {
                let q = qd.unwrap().evals[hi].clone();
                hi += 1;
                (q, reversed(&form_evals(b)))
            }
        };
        let aw = &tree_w.evals[j];
        let hev: Vec<E> = (0..m)
            .map(|i| ((uev[i] * xs[i]) * kev[i] - aw[i] - vals[j] * xn[i]) * xinv[i])
            .collect();
        add(&hev, &hcoef[j], &mut s);
    }
    // quotient words
    let gt = gamma * theta;
    let inv_of = |pt: E| -> Vec<E> {
        let den: Vec<E> = xs.iter().map(|&x| E::from(x) - pt).collect();
        batch_inv(&den)
    };
    let (di_gt, di_th, di_g) = if pl.had.is_empty() {
        (Vec::new(), Vec::new(), Vec::new())
    } else {
        (inv_of(gt), inv_of(theta), inv_of(gamma))
    };
    for (k, &j) in pl.had.iter().enumerate() {
        if let AStmt::Had(a, _, c) = &stmts[j] {
            let (y1, y3) = ys[k];
            if pl.qa[k] {
                let ev = form_evals(a);
                let qv: Vec<E> = (0..m).map(|i| (ev[i] - y1) * di_gt[i]).collect();
                add(&qv, &div_linear(&form_coeffs(a), gt), &mut s);
            }
            let q = qd.unwrap();
            let qv: Vec<E> = (0..m).map(|i| (q.evals[k][i] - y1) * di_th[i]).collect();
            add(&qv, &div_linear(&q.coeffs[k], theta), &mut s);
            if pl.qc[k] {
                let ev = form_evals(c);
                let qv: Vec<E> = (0..m).map(|i| (ev[i] - y3) * di_g[i]).collect();
                add(&qv, &div_linear(&form_coeffs(c), gamma), &mut s);
            }
        }
    }
    debug_assert_eq!(s, pl.nwords);

    // the folding test and the openings
    let (ft, idx) = ft_prove(p, tr, seed, first_round + 2, w0, u0);
    let mg0 = m >> g0;
    let pos0 = distinct_positions(&idx, mg0);
    let inv_idx: Vec<usize> = idx.iter().map(|&i| inv_pos(i % mg0, mg0)).collect();
    let posb = distinct_positions(&inv_idx, mg0);
    let c0 = p.cap_for(m / 2, g0 - 1);
    let gopen = groups
        .iter()
        .enumerate()
        .map(|(gi, g)| {
            let need_d = pl.direct.iter().any(|o| o.group == gi);
            let need_r = pl.rev.iter().any(|o| o.group == gi);
            match g {
                GData::Base(d) => {
                    let refs: Vec<&[Fp]> = d.evals.iter().map(|v| v.as_slice()).collect();
                    GOpen::Base {
                        direct: if need_d {
                            multi_open(p, &d.tree, &refs, &pos0, g0)
                        } else {
                            Vec::new()
                        },
                        rev: if need_r {
                            multi_open(p, &d.tree, &refs, &posb, g0)
                        } else {
                            Vec::new()
                        },
                    }
                }
                GData::Ext(d) => {
                    let refs: Vec<&[E]> = d.evals.iter().map(|v| v.as_slice()).collect();
                    GOpen::Ext {
                        direct: if need_d {
                            multi_open(p, &d.tree, &refs, &pos0, g0)
                        } else {
                            Vec::new()
                        },
                        rev: if need_r {
                            multi_open(p, &d.tree, &refs, &posb, g0)
                        } else {
                            Vec::new()
                        },
                    }
                }
            }
        })
        .collect();
    let refs_q: Vec<&[E]> = qd
        .map(|q| q.evals.iter().map(|v| v.as_slice()).collect())
        .unwrap_or_default();
    let refs_w: Vec<&[E]> = tree_w.evals.iter().map(|v| v.as_slice()).collect();
    AffineProof {
        gcaps: groups.iter().map(|g| g.cap(c0)).collect(),
        gopen,
        cap_q: qd.map(|q| q.tree.cap(c0)).unwrap_or_default(),
        cap_w: tree_w.tree.cap(c0),
        salts,
        ys,
        oq: match qd {
            Some(q) => multi_open(p, &q.tree, &refs_q, &pos0, g0),
            None => Vec::new(),
        },
        ow: multi_open(p, &tree_w.tree, &refs_w, &pos0, g0),
        ft,
    }
}

/// Values of every word of a group on the coset above `a` (index t), as E.
fn group_coset<E: ExtField>(g: &GOpen<E>, rev: bool, a: usize, nwords: usize) -> Vec<Vec<E>> {
    (0..nwords)
        .map(|k| match g {
            GOpen::Base { direct, rev: r } => {
                let ops = if rev { r } else { direct };
                multi_coset(ops, a, k).into_iter().map(E::from).collect()
            }
            GOpen::Ext { direct, rev: r } => {
                let ops = if rev { r } else { direct };
                multi_coset(ops, a, k)
            }
        })
        .collect()
}

/// The verifier of the engine: `roots` and `shapes` describe the groups, `tr` has absorbed the
/// same context as the prover's.
pub fn verify_affine<E: ExtField>(
    p: &Params,
    tr: &mut Transcript,
    roots: &[Digest],
    shapes: &[Shape],
    stmts: &[AStmt<E>],
    proof: &AffineProof<E>,
) -> Result<(), &'static str> {
    let (n, nn, m) = (p.n, p.big_n(), p.m());
    let omega = p.omega();
    let g0 = p.groups()[0].1;
    if stmts.is_empty()
        || roots.len() != shapes.len()
        || proof.gcaps.len() != roots.len()
        || proof.gopen.len() != roots.len()
        || proof.salts.len() != 2
        || proof.salts.iter().any(|s| s.len() != p.salt_len)
    {
        return Err("shape");
    }
    let pl = plan(stmts);
    let oid_ok = |o: &OId| o.group < shapes.len() && o.word < shapes[o.group].words;
    if pl.direct.iter().chain(&pl.rev).any(|o| !oid_ok(o))
        || proof.ys.len() != pl.had.len()
        || (pl.had.is_empty() && (!proof.cap_q.is_empty() || !proof.oq.is_empty()))
        || stmts
            .iter()
            .any(|s| matches!(s, AStmt::Eval(_, z, _) if z.len() != n))
    {
        return Err("shape");
    }
    if proof
        .gcaps
        .iter()
        .zip(roots)
        .any(|(c, r)| root_from_cap(c) != *r)
    {
        return Err("merkle");
    }
    absorb_stmts(tr, stmts);
    let gamma: E = draw_outside(tr, None);
    if !pl.had.is_empty() {
        tr.absorb(b"root", &root_from_cap(&proof.cap_q));
    }
    tr.absorb(b"salt", &proof.salts[0]);
    let theta: E = draw_outside(tr, Some(gamma));
    for (y1, y3) in &proof.ys {
        tr.absorb(b"y1", &e_bytes(y1));
        tr.absorb(b"y3", &e_bytes(y3));
    }
    tr.absorb(b"root", &root_from_cap(&proof.cap_w));
    tr.absorb(b"salt", &proof.salts[1]);
    let beta: E = tr.challenge();
    let bp = powers(beta, pl.nwords);
    let gt = gamma * theta;
    // direct checks for purely public forms of the Hadamard checks
    for (k, &j) in pl.had.iter().enumerate() {
        if let AStmt::Had(a, _, c) = &stmts[j] {
            let (y1, y3) = proof.ys[k];
            if !pl.qa[k] && y1 != a.eval_pub(n, gt) {
                return Err("value");
            }
            if !pl.qc[k] && y3 != c.eval_pub(n, gamma) {
                return Err("value");
            }
        }
    }
    let (rs, idx) = ft_replay(p, tr, &proof.ft)?;
    let mg0 = m >> g0;
    let pos0 = distinct_positions(&idx, mg0);
    let inv_idx: Vec<usize> = idx.iter().map(|&i| inv_pos(i % mg0, mg0)).collect();
    let posb = distinct_positions(&inv_idx, mg0);
    // openings of the groups
    for (gi, (g, sh)) in proof.gopen.iter().zip(shapes).enumerate() {
        let need_d = pl.direct.iter().any(|o| o.group == gi);
        let need_r = pl.rev.iter().any(|o| o.group == gi);
        let cap = &proof.gcaps[gi];
        match (g, sh.base) {
            (GOpen::Base { direct, rev }, true) => {
                if need_d {
                    multi_check(p, cap, direct, &pos0, sh.words)?;
                } else if !direct.is_empty() {
                    return Err("shape");
                }
                if need_r {
                    multi_check(p, cap, rev, &posb, sh.words)?;
                } else if !rev.is_empty() {
                    return Err("shape");
                }
            }
            (GOpen::Ext { direct, rev }, false) => {
                if need_d {
                    multi_check(p, cap, direct, &pos0, sh.words)?;
                } else if !direct.is_empty() {
                    return Err("shape");
                }
                if need_r {
                    multi_check(p, cap, rev, &posb, sh.words)?;
                } else if !rev.is_empty() {
                    return Err("shape");
                }
            }
            _ => return Err("shape"),
        }
    }
    if !pl.had.is_empty() {
        multi_check(p, &proof.cap_q, &proof.oq, &pos0, pl.had.len())?;
    }
    multi_check(p, &proof.cap_w, &proof.ow, &pos0, stmts.len())?;

    for &i0 in &idx {
        let a0 = i0 % mg0;
        let ab = inv_pos(a0, mg0);
        let gd: Vec<Option<Vec<Vec<E>>>> = (0..shapes.len())
            .map(|gi| {
                pl.direct
                    .iter()
                    .any(|o| o.group == gi)
                    .then(|| group_coset(&proof.gopen[gi], false, a0, shapes[gi].words))
            })
            .collect();
        let gr: Vec<Option<Vec<Vec<E>>>> = (0..shapes.len())
            .map(|gi| {
                pl.rev
                    .iter()
                    .any(|o| o.group == gi)
                    .then(|| group_coset(&proof.gopen[gi], true, ab, shapes[gi].words))
            })
            .collect();
        let qv: Vec<Vec<E>> = (0..pl.had.len())
            .map(|k| multi_coset(&proof.oq, a0, k))
            .collect();
        let wv: Vec<Vec<E>> = (0..stmts.len())
            .map(|k| multi_coset(&proof.ow, a0, k))
            .collect();
        let w0: Vec<E> = (0..2usize << (g0 - 1))
            .map(|t| {
                let pos = a0 + t * mg0;
                let tb = (inv_pos(pos, m) - ab) / mg0;
                let x = omega.pow(pos as u64);
                let xe = E::from(x);
                let xie = E::from(x.inv());
                let xn = omega.pow(((pos * nn) % m) as u64);
                let xnm1 = omega.pow(((pos * (nn - 1)) % m) as u64);
                let xinv = omega.pow(((m - (pos * (nn + 1)) % m) % m) as u64);
                let dval = |o: &OId| gd[o.group].as_ref().unwrap()[o.word][t];
                let rval = |o: &OId| gr[o.group].as_ref().unwrap()[o.word][tb] * xnm1;
                let fdir = |f: &Form<E>| {
                    f.com.iter().fold(f.eval_pub(n, xe), |acc, (o, c)| {
                        if *c == E::ZERO {
                            acc
                        } else {
                            acc + *c * dval(o)
                        }
                    })
                };
                let frev = |f: &Form<E>| {
                    f.com.iter().fold(f.eval_pub(n, xie) * xnm1, |acc, (o, c)| {
                        if *c == E::ZERO {
                            acc
                        } else {
                            acc + *c * rval(o)
                        }
                    })
                };
                let mut acc = E::ZERO;
                let mut s = 0usize;
                let mut push = |v: E, acc: &mut E| {
                    *acc = *acc + bp[s] * v;
                    s += 1;
                };
                for o in &pl.direct {
                    push(dval(o), &mut acc);
                }
                for o in &pl.rev {
                    push(rval(o), &mut acc);
                }
                for q in &qv {
                    push(q[t], &mut acc);
                }
                for w in &wv {
                    push(w[t], &mut acc);
                }
                let mut hi = 0;
                for (j, st) in stmts.iter().enumerate() {
                    let (u, k, v) = match st {
                        AStmt::Eval(f, z, v) => (fdir(f), evalker_eval(z, xe), *v),
                        AStmt::Ip(f, g, v) => (fdir(f), frev(g), *v),
                        AStmt::Had(_, b, _) => {
                            let r = (qv[hi][t], frev(b), proof.ys[hi].1);
                            hi += 1;
                            r
                        }
                    };
                    push(((u * x) * k - wv[j][t] - v * xn) * xinv, &mut acc);
                }
                for (k, &j) in pl.had.iter().enumerate() {
                    if let AStmt::Had(a, _, c) = &stmts[j] {
                        let (y1, y3) = proof.ys[k];
                        if pl.qa[k] {
                            push((fdir(a) - y1) * (xe - gt).inv(), &mut acc);
                        }
                        push((qv[k][t] - y1) * (xe - theta).inv(), &mut acc);
                        if pl.qc[k] {
                            push((fdir(c) - y3) * (xe - gamma).inv(), &mut acc);
                        }
                    }
                }
                acc
            })
            .collect();
        ft_check_query(p, &proof.ft, &rs, i0, w0)?;
    }
    Ok(())
}
