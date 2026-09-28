//! Prototype of the batched protocol Pi_Batch (research note `notes/inner-product`, Section 4):
//! any list of evaluation claims, inner-product claims and Hadamard checks on table-form
//! commitments, proved with one folding test.
//!
//! Statements (tables are indices into the list of commitments):
//! - `Eval { f, z, v }`: f~(z) = v, by X V_f E*_z = A + v X^N + X^{N+1} H (Lemma eval);
//! - `Ip { a, b, s }`: sum_w a(w) b(w) = s, by X V_a V_b^* = A + s X^N + X^{N+1} H;
//! - `Had { a, b, c }`: a o b = c, as in `had` (w_Q, y1, y3, three quotient words).
//!
//! Rounds: gamma; one tree holding all w_Q (one per Hadamard check); theta; the values y1, y3 of
//! every Hadamard check and one tree holding all w_A (one per statement); beta; the folding test
//! on w_0 = sum_i beta^i u_i, where u lists, without repetition, the committed words used directly,
//! the reversed committed words, the w_Q, the w_A, the virtual words h, and the quotient words.
//! gamma and theta are shared by all Hadamard checks.

use crate::error::Error;
use crate::field::{ExtField, Field, Fp, batch_inv};
use crate::ft::{FtProof, ft_check_query, ft_prove, ft_replay, round_salt};
use crate::had::{div_linear, poly_mul_e};
use crate::merkle::{
    Digest, GroupOpening, MerkleTree, Transcript, root_from_cap, verify_group_capped,
};
use crate::pcs::{Params, ProverData, distinct_positions, e_bytes, pair_bytes};
use crate::poly::{horner, ntt};

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt<E> {
    Eval { f: usize, z: Vec<E>, v: E },
    Ip { a: usize, b: usize, s: E },
    Had { a: usize, b: usize, c: usize },
}

/// Opening of several words committed in one tree, on the coset above one position.
#[derive(Clone, Debug)]
pub struct MultiOpening<T> {
    pub pos: usize,
    /// vals\[leaf\]\[word\] = \[u(x), u(-x)\]
    pub vals: Vec<Vec<[T; 2]>>,
    pub open: GroupOpening,
}

#[derive(Clone, Debug)]
pub struct BatchProof<E> {
    /// caps of the commitments, in the order of the instance
    pub caps: Vec<Vec<Digest>>,
    /// caps of the round-1 tree (all w_Q) and of the round-2 tree (all w_A)
    pub cap_q: Vec<Digest>,
    pub cap_w: Vec<Digest>,
    pub salts: Vec<Vec<u8>>,
    /// (y1, y3) of every Hadamard check, in order
    pub ys: Vec<(E, E)>,
    /// openings of the directly used commitments on the cosets of the queries
    pub direct: Vec<Vec<MultiOpening<Fp>>>,
    /// openings of the reversed commitments on the inverse cosets
    pub reversed: Vec<Vec<MultiOpening<Fp>>>,
    pub oq: Vec<MultiOpening<E>>,
    pub ow: Vec<MultiOpening<E>>,
    pub ft: FtProof<E>,
}

fn mopen_size<T>(o: &MultiOpening<T>, elem: usize) -> usize {
    2 * elem * o.vals.iter().map(|v| v.len()).sum::<usize>()
        + 32 * o.open.path.len()
        + o.open.salts.iter().map(|s| s.len()).sum::<usize>()
}

impl<E: ExtField> BatchProof<E> {
    pub fn size_bytes(&self) -> usize {
        let e = 8 * E::DEGREE;
        let caps: usize =
            self.caps.iter().map(|c| c.len()).sum::<usize>() + self.cap_q.len() + self.cap_w.len();
        let mut s = 32 * caps + 2 * e * self.ys.len();
        s += self.salts.iter().map(|x| x.len()).sum::<usize>();
        for lv in self.direct.iter().chain(&self.reversed) {
            s += lv.iter().map(|o| mopen_size(o, 8)).sum::<usize>();
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

/// The layout of the batch: which commitments are read directly and which reversed.
struct Layout {
    direct: Vec<usize>,
    reversed: Vec<usize>,
    nhad: usize,
}

fn layout<E>(stmts: &[Stmt<E>]) -> Layout {
    let (mut direct, mut reversed, mut nhad) = (Vec::new(), Vec::new(), 0);
    for s in stmts {
        match s {
            Stmt::Eval { f, .. } => direct.push(*f),
            Stmt::Ip { a, b, .. } => {
                direct.push(*a);
                reversed.push(*b);
            }
            Stmt::Had { a, b, c } => {
                direct.push(*a);
                direct.push(*c);
                reversed.push(*b);
                nhad += 1;
            }
        }
    }
    direct.sort_unstable();
    direct.dedup();
    reversed.sort_unstable();
    reversed.dedup();
    Layout {
        direct,
        reversed,
        nhad,
    }
}

impl Layout {
    /// Number of words in the batch: direct + reversed + w_Q + w_A + h + 3 quotients per Had.
    fn words(&self, nstmt: usize) -> usize {
        self.direct.len() + self.reversed.len() + self.nhad + 2 * nstmt + 3 * self.nhad
    }
}

/// Number of words t + 1 of the batch (the curve has degree t).
pub fn batch_words<E>(stmts: &[Stmt<E>]) -> usize {
    layout(stmts).words(stmts.len())
}

fn init_transcript<E: ExtField>(p: &Params, roots: &[Digest], stmts: &[Stmt<E>]) -> Transcript {
    let mut tr = Transcript::new(b"kronecker-fri-batch-v1");
    let params = [
        p.n,
        p.log_inv_rate,
        p.ell,
        p.queries,
        p.salt_len,
        p.fold_log,
        p.cap_log,
        E::DEGREE,
        roots.len(),
        stmts.len(),
    ];
    let pb: Vec<u8> = params
        .iter()
        .flat_map(|&x| (x as u64).to_le_bytes())
        .collect();
    tr.absorb(b"params", &pb);
    for r in roots {
        tr.absorb(b"commitment", r);
    }
    for s in stmts {
        let mut b = Vec::new();
        match s {
            Stmt::Eval { f, z, v } => {
                b.push(0u8);
                b.extend((*f as u64).to_le_bytes());
                for zi in z {
                    b.extend(e_bytes(zi));
                }
                b.extend(e_bytes(v));
            }
            Stmt::Ip { a, b: bb, s } => {
                b.push(1u8);
                b.extend((*a as u64).to_le_bytes());
                b.extend((*bb as u64).to_le_bytes());
                b.extend(e_bytes(s));
            }
            Stmt::Had { a, b: bb, c } => {
                b.push(2u8);
                for x in [a, bb, c] {
                    b.extend((*x as u64).to_le_bytes());
                }
            }
        }
        tr.absorb(b"statement", &b);
    }
    tr
}

pub(crate) fn in_base<E: ExtField>(x: &E) -> bool {
    x.digits()[1..].iter().all(|d| *d == Fp::ZERO)
}

pub(crate) fn draw_outside<E: ExtField>(tr: &mut Transcript, gamma: Option<E>) -> E {
    loop {
        let t: E = tr.challenge();
        if !in_base(&t) && gamma.is_none_or(|g| !in_base(&(g * t))) {
            return t;
        }
    }
}

#[inline(always)]
pub(crate) fn inv_pos(pos: usize, m: usize) -> usize {
    (m - pos) % m
}

/// Coefficients of E*_z = prod_k (z_k + (1 - z_k) X^{2^k}) (Lemma eval).
pub fn evalker_coeffs<E: ExtField>(z: &[E]) -> Vec<E> {
    let mut k = vec![E::ONE];
    for &zk in z {
        let mut next: Vec<E> = k.iter().map(|&c| c * zk).collect();
        next.extend(k.iter().map(|&c| c * (E::ONE - zk)));
        k = next;
    }
    k
}

/// E*_z(x) with n - 1 squarings.
pub fn evalker_eval<E: ExtField>(z: &[E], x: E) -> E {
    let mut acc = E::ONE;
    let mut p = x;
    for (k, &zk) in z.iter().enumerate() {
        if k > 0 {
            p = p.square();
        }
        acc = acc * (zk + (E::ONE - zk) * p);
    }
    acc
}

/// E*_z on the whole domain L = `<omega>` of order m (natural order), by the recursion along the
/// levels, as `poly::kernel_on_domain`.
pub fn evalker_on_domain<E: ExtField>(z: &[E], omega: Fp, m: usize) -> Vec<E> {
    let n = z.len();
    let mut cur = vec![E::ONE; m >> n];
    for k in (1..=n).rev() {
        let mk = m >> (k - 1);
        let half = mk / 2;
        let om = omega.pow(1u64 << (k - 1));
        let (zk, ck) = (z[k - 1], E::ONE - z[k - 1]);
        let mut next = vec![E::ZERO; mk];
        let mut x = Fp::ONE;
        for i in 0..half {
            let t = ck * x;
            next[i] = (zk + t) * cur[i];
            next[i + half] = (zk - t) * cur[i];
            x = x * om;
        }
        cur = next;
    }
    cur
}

/// Split of X U K (U K of length 2N - 1): (A, value, H), A and H of length N.
pub(crate) fn split<E: ExtField>(prod: &[E], nn: usize) -> (Vec<E>, E, Vec<E>) {
    let mut a = Vec::with_capacity(nn);
    a.push(E::ZERO);
    a.extend_from_slice(&prod[..nn - 1]);
    let mut h = prod[nn..].to_vec();
    h.push(E::ZERO);
    (a, prod[nn - 1], h)
}

pub(crate) fn multi_tree<T: Field>(
    words: &[&[T]],
    g: usize,
    seed: &Digest,
    label: &[u8],
    salt_len: usize,
) -> MerkleTree {
    let len = words[0].len();
    let half = len / 2;
    let mg = len >> g;
    let h = 1usize << (g - 1);
    MerkleTree::from_fn(
        half,
        |leaf, b| {
            let (a, t) = (leaf >> (g - 1), leaf & (h - 1));
            let q = a + t * mg;
            for w in words {
                w[q].to_bytes(b);
                w[q + half].to_bytes(b);
            }
        },
        seed,
        label,
        salt_len,
    )
}

pub(crate) fn multi_open<T: Field>(
    p: &Params,
    tree: &MerkleTree,
    words: &[&[T]],
    positions: &[usize],
    g: usize,
) -> Vec<MultiOpening<T>> {
    let len = words[0].len();
    let (half, mg) = (len / 2, len >> g);
    let c = p.cap_for(half, g - 1);
    positions
        .iter()
        .map(|&a| MultiOpening {
            pos: a,
            vals: (0..1usize << (g - 1))
                .map(|t| {
                    let q = a + t * mg;
                    words.iter().map(|w| [w[q], w[q + half]]).collect()
                })
                .collect(),
            open: tree.open_group_capped(a << (g - 1), g - 1, c),
        })
        .collect()
}

pub(crate) fn multi_check<T: Field>(
    p: &Params,
    cap: &[Digest],
    ops: &[MultiOpening<T>],
    positions: &[usize],
    nwords: usize,
) -> Result<(), Error> {
    let m = p.m();
    let g0 = p.groups()[0].1;
    let depth0 = (m / 2).trailing_zeros() as usize;
    let c0 = p.cap_for(m / 2, g0 - 1);
    if cap.len() != 1 << c0
        || ops.len() != positions.len()
        || ops.iter().zip(positions).any(|(o, &a)| {
            o.pos != a
                || o.vals.len() != 1 << (g0 - 1)
                || o.vals.iter().any(|v| v.len() != nwords)
                || o.open.path.len() != depth0 - (g0 - 1) - c0
                || o.open.salts.iter().any(|s| s.len() != p.salt_len)
        })
    {
        return Err(Error::Shape);
    }
    for o in ops {
        let d: Vec<Vec<u8>> = o
            .vals
            .iter()
            .map(|v| v.iter().flat_map(|[x, y]| pair_bytes(x, y)).collect())
            .collect();
        if !verify_group_capped(cap, o.pos << (g0 - 1), g0 - 1, &d, &o.open) {
            return Err(Error::Merkle);
        }
    }
    Ok(())
}

/// Values of word k on the coset above position a (index t: position a + t M_{g0}).
pub(crate) fn multi_coset<T: Copy>(ops: &[MultiOpening<T>], a: usize, k: usize) -> Vec<T> {
    let i = ops.binary_search_by_key(&a, |o| o.pos).unwrap();
    let v = &ops[i].vals;
    let h = v.len();
    (0..2 * h).map(|t| v[t % h][k][t / h]).collect()
}

pub(crate) fn powers<E: ExtField>(beta: E, count: usize) -> Vec<E> {
    (0..count)
        .scan(E::ONE, |acc, _| {
            let c = *acc;
            *acc = *acc * beta;
            Some(c)
        })
        .collect()
}

/// Deviations from the honest prover, for the tests.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BatchCheat {
    None,
    /// in every Hadamard check, y3 = [X^{N-1}] Q V_b^* (the weighted inner product) instead of
    /// V_c(gamma): the identity for h then holds, and only q[w_c, y3, gamma] can catch a false c
    HadUseIp,
}

/// Prover.  `pds[i]` is the prover data of commitment i (table form); the claimed values in
/// `stmts` are used as given (a false claim yields a rejected proof).
pub fn prove_batch<E: ExtField>(
    p: &Params,
    pds: &[&ProverData],
    stmts: &[Stmt<E>],
) -> Result<BatchProof<E>, Error> {
    p.validate()?;
    Ok(prove_batch_seeded(
        p,
        pds,
        stmts,
        &crate::rand::fresh_seed()?,
    ))
}

/// As [`prove_batch`], with the seed of the prover's randomness given by the caller: for tests and
/// test vectors only (feature `insecure-test-vectors`); the seed must never be reused.
pub(crate) fn prove_batch_seeded<E: ExtField>(
    p: &Params,
    pds: &[&ProverData],
    stmts: &[Stmt<E>],
    seed: &Digest,
) -> BatchProof<E> {
    prove_batch_with(p, pds, stmts, seed, BatchCheat::None)
}

pub(crate) fn prove_batch_with<E: ExtField>(
    p: &Params,
    pds: &[&ProverData],
    stmts: &[Stmt<E>],
    seed: &Digest,
    cheat: BatchCheat,
) -> BatchProof<E> {
    p.check();
    let (nn, m) = (p.big_n(), p.m());
    let omega = p.omega();
    let g0 = p.groups()[0].1;
    let lay = layout(stmts);
    let roots: Vec<Digest> = pds.iter().map(|d| d.tree0.root()).collect();
    let mut tr = init_transcript(p, &roots, stmts);
    let mut salts = Vec::new();
    let tab = |i: usize| -> Vec<E> { pds[i].alpha.iter().map(|&x| E::from(x)).collect() };
    let rev = |i: usize| -> Vec<E> { pds[i].alpha.iter().rev().map(|&x| E::from(x)).collect() };

    // round 1: gamma, then one tree with every w_Q
    let gamma: E = draw_outside(&mut tr, None);
    let mut qs: Vec<Vec<E>> = Vec::new();
    for s in stmts {
        if let Stmt::Had { a, .. } = s {
            let mut gp = E::ONE;
            let q: Vec<E> = pds[*a]
                .alpha
                .iter()
                .map(|&x| {
                    let v = gp * x;
                    gp = gp * gamma;
                    v
                })
                .collect();
            qs.push(q);
        }
    }
    let wqs: Vec<Vec<E>> = qs
        .iter()
        .map(|q| {
            let mut w = q.clone();
            w.resize(m, E::ZERO);
            ntt(&mut w, omega);
            w
        })
        .collect();
    let tree_q = if lay.nhad > 0 {
        let refs: Vec<&[E]> = wqs.iter().map(|w| w.as_slice()).collect();
        Some(multi_tree(&refs, g0, seed, b"batch-Q", p.salt_len))
    } else {
        None
    };
    if let Some(t) = &tree_q {
        tr.absorb(b"root", &t.root());
    }
    salts.push(round_salt(seed, 1, p.salt_len));
    tr.absorb(b"salt", salts.last().unwrap());

    // round 2: theta, the values y1, y3, and one tree with every w_A
    let theta: E = draw_outside(&mut tr, Some(gamma));
    let mut ys = Vec::new();
    let mut apolys: Vec<Vec<E>> = Vec::new();
    let mut hpolys: Vec<Vec<E>> = Vec::new();
    let mut vals: Vec<E> = Vec::new(); // the value in the identity of each statement
    let mut hi = 0;
    for s in stmts {
        let (prod, v) = match s {
            Stmt::Eval { f, z, v } => {
                let prod = poly_mul_e(&tab(*f), &evalker_coeffs(z));
                (prod, *v)
            }
            Stmt::Ip { a, b, s } => (poly_mul_e(&tab(*a), &rev(*b)), *s),
            Stmt::Had { b, c, .. } => {
                let q = &qs[hi];
                let y1 = horner(q, theta);
                let prod = poly_mul_e(q, &rev(*b));
                let y3 = match cheat {
                    BatchCheat::HadUseIp => prod[nn - 1],
                    BatchCheat::None => horner(&tab(*c), gamma),
                };
                ys.push((y1, y3));
                hi += 1;
                (prod, y3)
            }
        };
        let (a, _, h) = split(&prod, nn);
        apolys.push(a);
        hpolys.push(h);
        vals.push(v);
    }
    for (y1, y3) in &ys {
        tr.absorb(b"y1", &e_bytes(y1));
        tr.absorb(b"y3", &e_bytes(y3));
    }
    let was: Vec<Vec<E>> = apolys
        .iter()
        .map(|a| {
            let mut w = a.clone();
            w.resize(m, E::ZERO);
            ntt(&mut w, omega);
            w
        })
        .collect();
    let refs: Vec<&[E]> = was.iter().map(|w| w.as_slice()).collect();
    let tree_w = multi_tree(&refs, g0, seed, b"batch-A", p.salt_len);
    tr.absorb(b"root", &tree_w.root());
    salts.push(round_salt(seed, 2, p.salt_len));
    tr.absorb(b"salt", salts.last().unwrap());
    let beta: E = tr.challenge();
    let nw = lay.words(stmts.len());
    let bp = powers(beta, nw);

    // the batched word
    let xs: Vec<Fp> = (0..m)
        .scan(Fp::ONE, |x, _| {
            let c = *x;
            *x = *x * omega;
            Some(c)
        })
        .collect();
    let ekers: Vec<Option<Vec<E>>> = stmts
        .iter()
        .map(|s| match s {
            Stmt::Eval { z, .. } => Some(evalker_on_domain(z, omega, m)),
            _ => None,
        })
        .collect();
    let gt = gamma * theta;
    let dinv = if lay.nhad > 0 {
        let mut den = Vec::with_capacity(3 * m);
        for &x in &xs {
            den.push(E::from(x) - gt);
            den.push(E::from(x) - theta);
            den.push(E::from(x) - gamma);
        }
        batch_inv(&den)
    } else {
        Vec::new()
    };
    let step_n = omega.pow(nn as u64);
    let step_nm1 = omega.pow((nn - 1) as u64);
    let step_inv = omega.pow((m - nn - 1) as u64);
    let (mut xn, mut xnm1, mut xinv) = (Fp::ONE, Fp::ONE, Fp::ONE);
    let ridx: Vec<usize> = stmts
        .iter()
        .map(|s| match s {
            Stmt::Ip { b, .. } | Stmt::Had { b, .. } => lay.reversed.binary_search(b).unwrap(),
            Stmt::Eval { .. } => 0,
        })
        .collect();
    let mut w0 = Vec::with_capacity(m);
    let (mut u, mut rv, mut quots): (Vec<E>, Vec<Fp>, Vec<E>) = (
        Vec::with_capacity(nw),
        Vec::with_capacity(lay.reversed.len()),
        Vec::with_capacity(3 * lay.nhad),
    );
    for i in 0..m {
        let x = xs[i];
        u.clear();
        rv.clear();
        quots.clear();
        for &d in &lay.direct {
            u.push(E::from(pds[d].y[i]));
        }
        let ii = inv_pos(i, m);
        rv.extend(lay.reversed.iter().map(|&r| xnm1 * pds[r].y[ii]));
        u.extend(rv.iter().map(|&x| E::from(x)));
        for w in &wqs {
            u.push(w[i]);
        }
        for w in &was {
            u.push(w[i]);
        }
        let mut hi = 0;
        for (j, s) in stmts.iter().enumerate() {
            let (uu, kk): (E, E) = match s {
                Stmt::Eval { f, .. } => (E::from(pds[*f].y[i]), ekers[j].as_ref().unwrap()[i]),
                Stmt::Ip { a, .. } => (E::from(pds[*a].y[i]), E::from(rv[ridx[j]])),
                Stmt::Had { a, c, .. } => {
                    let (y1, y3) = ys[hi];
                    let wq = wqs[hi][i];
                    quots.push((E::from(pds[*a].y[i]) - y1) * dinv[3 * i]);
                    quots.push((wq - y1) * dinv[3 * i + 1]);
                    quots.push((E::from(pds[*c].y[i]) - y3) * dinv[3 * i + 2]);
                    hi += 1;
                    (wq, E::from(rv[ridx[j]]))
                }
            };
            u.push(((uu * x) * kk - was[j][i] - vals[j] * xn) * xinv);
        }
        u.extend_from_slice(&quots);
        w0.push(u.iter().zip(&bp).fold(E::ZERO, |acc, (&v, &b)| acc + b * v));
        xn = xn * step_n;
        xnm1 = xnm1 * step_nm1;
        xinv = xinv * step_inv;
    }
    drop(dinv);

    // the polynomial U_0, in the same order
    let mut polys: Vec<Vec<E>> = Vec::with_capacity(nw);
    for &d in &lay.direct {
        polys.push(tab(d));
    }
    for &r in &lay.reversed {
        polys.push(rev(r));
    }
    polys.extend(qs.iter().cloned());
    polys.extend(apolys);
    polys.extend(hpolys);
    let mut hi = 0;
    for s in stmts {
        if let Stmt::Had { a, c, .. } = s {
            polys.push(div_linear(&tab(*a), gt));
            polys.push(div_linear(&qs[hi], theta));
            polys.push(div_linear(&tab(*c), gamma));
            hi += 1;
        }
    }
    let u0: Vec<E> = (0..nn)
        .map(|j| (0..nw).fold(E::ZERO, |acc, k| acc + bp[k] * polys[k][j]))
        .collect();

    // the folding test and the level-0 openings
    let (ft, idx) = ft_prove(p, &mut tr, seed, 3, w0, u0);
    let mg0 = m >> g0;
    let pos0 = distinct_positions(&idx, mg0);
    let inv_idx: Vec<usize> = idx.iter().map(|&i| inv_pos(i % mg0, mg0)).collect();
    let posb = distinct_positions(&inv_idx, mg0);
    let c0 = p.cap_for(m / 2, g0 - 1);
    let one =
        |d: usize, pos: &[usize]| multi_open(p, &pds[d].tree0, &[pds[d].y.as_slice()], pos, g0);
    BatchProof {
        caps: pds.iter().map(|d| d.tree0.cap(c0)).collect(),
        cap_q: tree_q.as_ref().map(|t| t.cap(c0)).unwrap_or_default(),
        cap_w: tree_w.cap(c0),
        salts,
        ys,
        direct: lay.direct.iter().map(|&d| one(d, &pos0)).collect(),
        reversed: lay.reversed.iter().map(|&r| one(r, &posb)).collect(),
        oq: match &tree_q {
            Some(t) => {
                let refs: Vec<&[E]> = wqs.iter().map(|w| w.as_slice()).collect();
                multi_open(p, t, &refs, &pos0, g0)
            }
            None => Vec::new(),
        },
        ow: {
            let refs: Vec<&[E]> = was.iter().map(|w| w.as_slice()).collect();
            multi_open(p, &tree_w, &refs, &pos0, g0)
        },
        ft,
    }
}

/// Verifier with the reason for rejection: "shape", "merkle" or "fold".
pub fn verify_batch<E: ExtField>(
    p: &Params,
    roots: &[Digest],
    stmts: &[Stmt<E>],
    proof: &BatchProof<E>,
) -> Result<(), Error> {
    p.validate()?;
    let (nn, m) = (p.big_n(), p.m());
    let omega = p.omega();
    let g0 = p.groups()[0].1;
    if stmts.is_empty()
        || stmts.iter().any(|s| match s {
            Stmt::Eval { f, z, .. } => *f >= roots.len() || z.len() != p.n,
            Stmt::Ip { a, b, .. } => *a >= roots.len() || *b >= roots.len(),
            Stmt::Had { a, b, c } => [a, b, c].iter().any(|&&x| x >= roots.len()),
        })
    {
        return Err(Error::Shape);
    }
    let lay = layout(stmts);
    let nw = lay.words(stmts.len());
    if proof.caps.len() != roots.len()
        || proof.salts.len() != 2
        || proof.salts.iter().any(|s| s.len() != p.salt_len)
        || proof.ys.len() != lay.nhad
        || proof.direct.len() != lay.direct.len()
        || proof.reversed.len() != lay.reversed.len()
        || (lay.nhad == 0 && (!proof.cap_q.is_empty() || !proof.oq.is_empty()))
    {
        return Err(Error::Shape);
    }
    if proof
        .caps
        .iter()
        .zip(roots)
        .any(|(c, r)| root_from_cap(c) != Ok(*r))
    {
        return Err(Error::Merkle);
    }
    let mut tr = init_transcript(p, roots, stmts);
    let gamma: E = draw_outside(&mut tr, None);
    if lay.nhad > 0 {
        tr.absorb(b"root", &root_from_cap(&proof.cap_q)?);
    }
    tr.absorb(b"salt", &proof.salts[0]);
    let theta: E = draw_outside(&mut tr, Some(gamma));
    for (y1, y3) in &proof.ys {
        tr.absorb(b"y1", &e_bytes(y1));
        tr.absorb(b"y3", &e_bytes(y3));
    }
    tr.absorb(b"root", &root_from_cap(&proof.cap_w)?);
    tr.absorb(b"salt", &proof.salts[1]);
    let beta: E = tr.challenge();
    let bp = powers(beta, nw);
    let (rs, idx) = ft_replay(p, &mut tr, &proof.ft)?;
    let mg0 = m >> g0;
    let pos0 = distinct_positions(&idx, mg0);
    let inv_idx: Vec<usize> = idx.iter().map(|&i| inv_pos(i % mg0, mg0)).collect();
    let posb = distinct_positions(&inv_idx, mg0);
    for (k, &d) in lay.direct.iter().enumerate() {
        multi_check(p, &proof.caps[d], &proof.direct[k], &pos0, 1)?;
    }
    for (k, &r) in lay.reversed.iter().enumerate() {
        multi_check(p, &proof.caps[r], &proof.reversed[k], &posb, 1)?;
    }
    if lay.nhad > 0 {
        multi_check(p, &proof.cap_q, &proof.oq, &pos0, lay.nhad)?;
    }
    multi_check(p, &proof.cap_w, &proof.ow, &pos0, stmts.len())?;
    let gt = gamma * theta;
    let didx = |f: usize| lay.direct.binary_search(&f).unwrap();
    let ridx = |b: usize| lay.reversed.binary_search(&b).unwrap();
    for &i0 in &idx {
        let a0 = i0 % mg0;
        let ab = inv_pos(a0, mg0);
        let dv: Vec<Vec<Fp>> = (0..lay.direct.len())
            .map(|k| multi_coset(&proof.direct[k], a0, 0))
            .collect();
        let rvv: Vec<Vec<Fp>> = (0..lay.reversed.len())
            .map(|k| multi_coset(&proof.reversed[k], ab, 0))
            .collect();
        let qv: Vec<Vec<E>> = (0..lay.nhad)
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
                let xn = omega.pow(((pos * nn) % m) as u64);
                let xnm1 = omega.pow(((pos * (nn - 1)) % m) as u64);
                let xinv = omega.pow(((m - (pos * (nn + 1)) % m) % m) as u64);
                let mut u: Vec<E> = Vec::with_capacity(nw);
                u.extend(dv.iter().map(|v| E::from(v[t])));
                let rv: Vec<Fp> = rvv.iter().map(|v| xnm1 * v[tb]).collect();
                u.extend(rv.iter().map(|&y| E::from(y)));
                u.extend(qv.iter().map(|v| v[t]));
                u.extend(wv.iter().map(|v| v[t]));
                let mut hi = 0;
                let mut quots = Vec::new();
                for (j, s) in stmts.iter().enumerate() {
                    let (uu, kk, v): (E, E, E) = match s {
                        Stmt::Eval { f, z, v } => {
                            (E::from(dv[didx(*f)][t]), evalker_eval(z, xe), *v)
                        }
                        Stmt::Ip { a, b, s } => {
                            (E::from(dv[didx(*a)][t]), E::from(rv[ridx(*b)]), *s)
                        }
                        Stmt::Had { a, b, c } => {
                            let (y1, y3) = proof.ys[hi];
                            let wq = qv[hi][t];
                            quots.push((E::from(dv[didx(*a)][t]) - y1) * (xe - gt).inv());
                            quots.push((wq - y1) * (xe - theta).inv());
                            quots.push((E::from(dv[didx(*c)][t]) - y3) * (xe - gamma).inv());
                            hi += 1;
                            (wq, E::from(rv[ridx(*b)]), y3)
                        }
                    };
                    u.push(((uu * x) * kk - wv[j][t] - v * xn) * xinv);
                }
                u.extend(quots);
                (0..nw).fold(E::ZERO, |acc, k| acc + bp[k] * u[k])
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
    use crate::ip::commit_table_form_seeded;

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

    /// f~(z) from the table: sum_w f(w) prod_k (w_k z_k + (1 - w_k)(1 - z_k)).
    fn mle<E: ExtField>(t: &[Fp], z: &[E]) -> E {
        let mut acc = E::ZERO;
        for (w, &fw) in t.iter().enumerate() {
            let mut e = E::ONE;
            for (k, &zk) in z.iter().enumerate() {
                e = e * if w >> k & 1 == 1 { zk } else { E::ONE - zk };
            }
            acc = acc + e * fw;
        }
        acc
    }

    #[test]
    fn evalker_matches_mle_and_domain() {
        let mut rng = Rng(8);
        for n in 1..=6 {
            let t: Vec<Fp> = (0..1 << n).map(|_| rng.fp()).collect();
            let z: Vec<Fp2> = (0..n).map(|_| rng.e()).collect();
            let prod = poly_mul_e(
                &t.iter().map(|&x| Fp2::from(x)).collect::<Vec<_>>(),
                &evalker_coeffs(&z),
            );
            assert_eq!(prod[(1 << n) - 1], mle(&t, &z));
            let m = 4usize << n;
            let omega = Fp::two_adic_root((n + 2) as u32);
            let dom = evalker_on_domain(&z, omega, m);
            let k = evalker_coeffs(&z);
            for i in 0..m {
                let x = Fp2::from(omega.pow(i as u64));
                assert_eq!(dom[i], horner(&k, x));
                assert_eq!(evalker_eval(&z, x), dom[i]);
            }
        }
    }

    fn run<E: ExtField>() {
        let mut rng = Rng(777);
        for (n, ell, fold_log, cap_log) in [
            (1, 1, 1, 0),
            (4, 2, 1, 0),
            (6, 3, 2, 2),
            (8, 8, 3, 3),
            (10, 9, 4, 4),
        ] {
            let p = Params {
                n,
                log_inv_rate: 2,
                ell,
                queries: 30,
                salt_len: 32,
                fold_log,
                cap_log,
            };
            let nn = 1usize << n;
            let a: Vec<Fp> = (0..nn).map(|_| rng.fp()).collect();
            let b: Vec<Fp> = (0..nn).map(|_| rng.fp()).collect();
            let c: Vec<Fp> = a.iter().zip(&b).map(|(&x, &y)| x * y).collect();
            let d: Vec<Fp> = (0..nn).map(|_| rng.fp()).collect();
            let e2: Vec<Fp> = b.iter().zip(&d).map(|(&x, &y)| x * y).collect();
            let tables = [&a, &b, &c, &d, &e2];
            let com: Vec<(Digest, ProverData)> = tables
                .iter()
                .enumerate()
                .map(|(i, t)| commit_table_form_seeded(&p, t, &[i as u8 + 1; 32]))
                .collect();
            let roots: Vec<Digest> = com.iter().map(|x| x.0).collect();
            let pds: Vec<&ProverData> = com.iter().map(|x| &x.1).collect();
            let z1: Vec<E> = (0..n).map(|_| rng.e()).collect();
            let z2: Vec<E> = (0..n).map(|_| rng.e()).collect();
            let ip = |x: &[Fp], y: &[Fp]| {
                E::from(x.iter().zip(y).fold(Fp::ZERO, |s, (&u, &v)| s + u * v))
            };
            let stmts: Vec<Stmt<E>> = vec![
                Stmt::Had { a: 0, b: 1, c: 2 },
                Stmt::Had { a: 1, b: 3, c: 4 },
                Stmt::Ip {
                    a: 0,
                    b: 3,
                    s: ip(&a, &d),
                },
                Stmt::Eval {
                    f: 2,
                    z: z1.clone(),
                    v: mle(&c, &z1),
                },
                Stmt::Eval {
                    f: 0,
                    z: z2.clone(),
                    v: mle(&a, &z2),
                },
            ];
            let pr = prove_batch_seeded(&p, &pds, &stmts, &[9u8; 32]);
            assert_eq!(verify_batch(&p, &roots, &stmts, &pr), Ok(()), "n={n}");
            // sub-batches of one kind
            for sub in [&stmts[..1], &stmts[2..3], &stmts[3..4], &stmts[2..]] {
                let pr = prove_batch_seeded(&p, &pds, sub, &[10u8; 32]);
                assert_eq!(verify_batch(&p, &roots, sub, &pr), Ok(()), "n={n} sub");
            }
            // one false statement among true ones is rejected
            let mut bad_eval = stmts.clone();
            if let Stmt::Eval { v, .. } = &mut bad_eval[3] {
                *v = *v + E::ONE;
            }
            let mut bad_ip = stmts.clone();
            if let Stmt::Ip { s, .. } = &mut bad_ip[2] {
                *s = *s + E::ONE;
            }
            let mut bad_had = stmts.clone();
            bad_had[1] = Stmt::Had { a: 1, b: 3, c: 3 }; // b o d != d
            for (name, st) in [("eval", &bad_eval), ("ip", &bad_ip), ("had", &bad_had)] {
                let pr = prove_batch_seeded(&p, &pds, st, &[11u8; 32]);
                assert_eq!(
                    verify_batch(&p, &roots, st, &pr),
                    Err(Error::Fold),
                    "n={n} {name}"
                );
            }
            let pr = prove_batch_with(&p, &pds, &bad_had, &[13u8; 32], BatchCheat::HadUseIp);
            assert_eq!(
                verify_batch(&p, &roots, &bad_had, &pr),
                Err(Error::Fold),
                "n={n} had/ip"
            );
            // a valid proof does not verify for other statements
            assert!(verify_batch(&p, &roots, &bad_eval, &pr_ok(&p, &pds, &stmts)).is_err());
        }
    }

    fn pr_ok<E: ExtField>(p: &Params, pds: &[&ProverData], s: &[Stmt<E>]) -> BatchProof<E> {
        prove_batch_seeded(p, pds, s, &[12u8; 32])
    }

    #[test]
    fn batch_complete_and_sound_fp2() {
        run::<Fp2>();
    }

    #[test]
    fn batch_complete_and_sound_fp4() {
        run::<Fp4>();
    }
}
