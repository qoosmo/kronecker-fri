//! The evaluation protocol Pi_KF of Section 6.3, compiled with salted Merkle trees and a
//! Fiat-Shamir transcript (Sections 3.4 and 8.1), with folding of arity 2^k (Section 5.7) and
//! Merkle caps.
//!
//! The committed polynomial has coefficients in F_p (Goldilocks); the point z, the value v, the
//! challenges, the opening word w_A, the virtual word h and all folded words live in the extension
//! E = F_{p^e} (e = 2 or 4).
//!
//! Domain layout: L = `<omega>`, position i of a word on L_j is omega_j^i with omega_j = omega^{2^j};
//! the fibre over position q of L_{j+1} is {q, q + M_{j+1}}.
//!
//! Levels. The folding test runs l binary folds. Only the words at levels k, 2k, 3k, ... < l are
//! committed; the words in between are virtual (exact folds, Section 5.7). A *group* is a pair
//! (jc, g): the word at level jc (the commitment and w_A for jc = 0) is folded g <= k times
//! locally by the verifier, up to level jc + g, the next committed level or l.
//!
//! Leaves. The tree of a word u on L_jc whose group has length g has one leaf per fibre; the fibre
//! over position q of L_{jc+1}, with q = a + t M_{jc+g} (a < M_{jc+g}, t < 2^{g-1}), is leaf
//! a 2^{g-1} + t. A query at position a of L_{jc+g} opens the aligned group of 2^{g-1} leaves,
//! that is, u on the 2^g points above a, with one authentication path.

use crate::error::Error;
use crate::field::{ExtField, Field, Fp};
use crate::merkle::{
    Digest, GroupOpening, MerkleTree, Transcript, root_from_cap, verify_group_capped,
};
use crate::poly::{
    fold_pair, fold_word, horner, kernel_eval, kernel_on_domain, mobius, ntt, opening_polys, pfold,
};

#[derive(Clone, Copy, Debug)]
pub struct Params {
    /// number of variables n (N = 2^n)
    pub n: usize,
    /// R with rate rho = 2^-R (R >= 2, Section 6.1)
    pub log_inv_rate: usize,
    /// number of binary folding rounds l, 1 <= l <= n
    pub ell: usize,
    /// number of queries kappa
    pub queries: usize,
    /// salt length in bytes (0 = unsalted trees)
    pub salt_len: usize,
    /// folding arity 2^k: only every k-th folded word is committed (k = 1: every word)
    pub fold_log: usize,
    /// Merkle cap height c: the 2^c nodes below each root are sent once (c = 0: roots only)
    pub cap_log: usize,
}

impl Params {
    /// Parameters with binary folding and no caps.
    pub fn new(n: usize, log_inv_rate: usize, ell: usize, queries: usize, salt_len: usize) -> Self {
        Params {
            n,
            log_inv_rate,
            ell,
            queries,
            salt_len,
            fold_log: 1,
            cap_log: 0,
        }
    }
    /// The recommended configuration KF-8 of the paper (Section 10): rate 1/4, arity 8, caps of
    /// 128 nodes, and l = n - 8 folding rounds (at least 1).
    pub fn recommended(n: usize, queries: usize, salt_len: usize) -> Self {
        Params {
            n,
            log_inv_rate: 2,
            ell: n.saturating_sub(8).max(1),
            queries,
            salt_len,
            fold_log: 3,
            cap_log: 7,
        }
    }
    pub fn big_n(&self) -> usize {
        1 << self.n
    }
    pub fn m(&self) -> usize {
        1 << (self.n + self.log_inv_rate)
    }
    pub fn omega(&self) -> Fp {
        Fp::two_adic_root((self.n + self.log_inv_rate) as u32)
    }
    /// Checks the parameters; the verifiers call it and return [`Error::Params`] on failure.
    pub fn validate(&self) -> Result<(), Error> {
        if self.n < 1 || self.log_inv_rate < 2 || self.n + self.log_inv_rate > 32 {
            return Err(Error::Params(
                "need n >= 1, log_inv_rate >= 2, n + log_inv_rate <= 32",
            ));
        }
        if self.ell < 1 || self.ell > self.n {
            return Err(Error::Params("need 1 <= ell <= n"));
        }
        if self.queries < 1 || self.queries > 1 << 16 {
            return Err(Error::Params("need 1 <= queries <= 2^16"));
        }
        if self.fold_log < 1 || self.fold_log > self.ell.max(1) + 31 {
            return Err(Error::Params("need fold_log >= 1"));
        }
        if self.cap_log > 31 {
            return Err(Error::Params("need cap_log <= 31"));
        }
        if self.salt_len > 64 {
            return Err(Error::Params("need salt_len <= 64"));
        }
        Ok(())
    }
    /// Panics on invalid parameters (prover side; the prover API returns errors from 0.5 on).
    pub(crate) fn check(&self) {
        if let Err(e) = self.validate() {
            panic!("{e}");
        }
    }
    /// Groups (jc, g): start level and number of local folds.
    pub fn groups(&self) -> Vec<(usize, usize)> {
        let mut out = Vec::new();
        let mut jc = 0;
        while jc < self.ell {
            let g = self.fold_log.min(self.ell - jc);
            out.push((jc, g));
            jc += g;
        }
        out
    }
    /// Cap height actually used for a tree with `leaves` leaves opened in groups of 2^h leaves.
    pub(crate) fn cap_for(&self, leaves: usize, h: usize) -> usize {
        let depth = leaves.trailing_zeros() as usize;
        self.cap_log.min(depth - h)
    }
}

pub(crate) fn e_bytes<E: ExtField>(x: &E) -> Vec<u8> {
    let mut b = Vec::with_capacity(8 * E::DEGREE);
    x.to_bytes(&mut b);
    b
}

pub(crate) fn pair_bytes<T: Field>(a: &T, b: &T) -> Vec<u8> {
    let mut out = Vec::with_capacity(64);
    a.to_bytes(&mut out);
    b.to_bytes(&mut out);
    out
}

/// Tree over the fibres of a word u on L_jc (length mj = M_jc) for a group of length g.
pub(crate) fn coset_tree<T: Field>(
    u: &[T],
    g: usize,
    seed: &Digest,
    label: &[u8],
    salt_len: usize,
) -> MerkleTree {
    let half = u.len() / 2; // M_{jc+1}
    let mg = u.len() >> g; // M_{jc+g}
    let h = 1usize << (g - 1);
    MerkleTree::from_fn(
        half,
        |leaf, b| {
            let (a, t) = (leaf >> (g - 1), leaf & (h - 1));
            let q = a + t * mg;
            u[q].to_bytes(b);
            u[q + half].to_bytes(b)
        },
        seed,
        label,
        salt_len,
    )
}

/// Values of u on the 2^g points above position a of L_{jc+g}, in the order t = 0 .. 2^g - 1
/// of the positions a + t M_{jc+g} of L_jc.
pub(crate) fn coset_values<T: Field>(u: &[T], g: usize, a: usize) -> Vec<[T; 2]> {
    let half = u.len() / 2;
    let mg = u.len() >> g;
    (0..1usize << (g - 1))
        .map(|t| {
            let q = a + t * mg;
            [u[q], u[q + half]]
        })
        .collect()
}

/// Flatten leaf pairs into the 2^g values, position a + t M_{jc+g} at index t.
pub(crate) fn unpair<T: Copy>(pairs: &[[T; 2]]) -> Vec<T> {
    let h = pairs.len();
    (0..2 * h).map(|t| pairs[t % h][t / h]).collect()
}

/// Fold 2^g values at positions a + t M_{jc+g} of L_jc down to the value at position a of L_{jc+g}.
pub(crate) fn fold_coset<E: ExtField>(
    mut vals: Vec<E>,
    a: usize,
    jc: usize,
    mg: usize,
    rs: &[E],
    m: usize,
    omega: Fp,
) -> E {
    let inv2 = Fp::new(2).inv();
    let mut level = jc;
    while vals.len() > 1 {
        let half = vals.len() / 2;
        vals = (0..half)
            .map(|t| {
                let pos = a + t * mg; // position in L_level
                let inv_2xi = omega.pow((m - (pos << level)) as u64) * inv2;
                fold_pair(vals[t], vals[t + half], inv_2xi, rs[level], inv2)
            })
            .collect();
        level += 1;
    }
    vals[0]
}

pub struct ProverData {
    /// coefficient form of f (= coefficients of U_f), over F_p
    pub alpha: Vec<Fp>,
    /// the commitment word y = Enc(f) = ev_L(U_f)
    pub y: Vec<Fp>,
    pub(crate) tree0: MerkleTree,
}

/// Opening of the commitment and of w_A on the 2^{g_0} points above one position of L_{g_0}.
#[derive(Clone, Debug)]
pub struct Level0Opening<E> {
    /// the position a of L_{g_0} (recomputed by the verifier; not counted in the proof size)
    pub pos: usize,
    /// the commitment on the points above `pos`, as leaf pairs
    pub y: Vec<[Fp; 2]>,
    pub y_open: GroupOpening,
    /// w_A on the same points
    pub a: Vec<[E; 2]>,
    pub a_open: GroupOpening,
}

/// Opening of a committed folded word on the points above one position.
#[derive(Clone, Debug)]
pub struct LevelOpening<E> {
    /// the position (recomputed by the verifier; not counted in the proof size)
    pub pos: usize,
    pub vals: Vec<[E; 2]>,
    pub open: GroupOpening,
}

#[derive(Clone, Debug)]
pub struct Proof<E> {
    /// cap of the commitment tree (its root is the commitment)
    pub cap_y: Vec<Digest>,
    /// cap of the tree of w_A
    pub cap_a: Vec<Digest>,
    /// caps of the trees of the committed folded words
    pub caps: Vec<Vec<Digest>>,
    /// round salts of rounds 1 .. l+2
    pub round_salts: Vec<Vec<u8>>,
    /// coefficients of the final polynomial P (length N_l)
    pub p: Vec<E>,
    /// level-0 openings, one per distinct queried position, sorted by position
    pub level0: Vec<Level0Opening<E>>,
    /// for each committed level, one opening per distinct queried position, sorted by position
    pub levels: Vec<Vec<LevelOpening<E>>>,
}

impl<E: ExtField> Proof<E> {
    /// Serialized size in bytes: 32 per digest, 8 per F_p element, 8e per E element, salts.
    pub fn size_bytes(&self) -> usize {
        let e = 8 * E::DEGREE;
        let open =
            |o: &GroupOpening| 32 * o.path.len() + o.salts.iter().map(|s| s.len()).sum::<usize>();
        let mut s = 32 * (self.cap_y.len() + self.cap_a.len());
        s += 32 * self.caps.iter().map(|c| c.len()).sum::<usize>() + self.p.len() * e;
        s += self.round_salts.iter().map(|x| x.len()).sum::<usize>();
        for o in &self.level0 {
            s += 16 * o.y.len() + open(&o.y_open) + 2 * e * o.a.len() + open(&o.a_open);
        }
        for lv in &self.levels {
            for o in lv {
                s += 2 * e * o.vals.len() + open(&o.open);
            }
        }
        s
    }
}

/// Sorted distinct positions i0 mod modulus.
pub(crate) fn distinct_positions(idx: &[usize], modulus: usize) -> Vec<usize> {
    let mut v: Vec<usize> = idx.iter().map(|&i| i % modulus).collect();
    v.sort_unstable();
    v.dedup();
    v
}

/// Commit to f given in coefficient form (Definition 6.2): one NTT of size M.
/// The Merkle layout depends on the first group of `p` (its length min(k, l)).
pub fn commit_coeffs(p: &Params, alpha: &[Fp]) -> Result<(Digest, ProverData), Error> {
    p.validate()?;
    if alpha.len() != p.big_n() {
        return Err(Error::Input("the coefficient vector must have length 2^n"));
    }
    Ok(commit_coeffs_seeded(p, alpha, &crate::rand::fresh_seed()?))
}

/// As [`commit_coeffs`], with the seed of the prover's randomness given by the caller: for tests and
/// test vectors only (feature `insecure-test-vectors`); the seed must never be reused.
pub(crate) fn commit_coeffs_seeded(
    p: &Params,
    alpha: &[Fp],
    seed: &Digest,
) -> (Digest, ProverData) {
    p.check();
    assert_eq!(alpha.len(), p.big_n());
    let mut y = alpha.to_vec();
    y.resize(p.m(), Fp::ZERO);
    ntt(&mut y, p.omega());
    let g0 = p.groups()[0].1;
    let tree0 = coset_tree(&y, g0, seed, b"commit", p.salt_len);
    (
        tree0.root(),
        ProverData {
            alpha: alpha.to_vec(),
            y,
            tree0,
        },
    )
}

/// Commit to f given in table form: Moebius transform ((n/2) N subtractions), then commit.
pub fn commit_table(p: &Params, table: &[Fp]) -> Result<(Digest, ProverData), Error> {
    p.validate()?;
    if table.len() != p.big_n() {
        return Err(Error::Input("the table must have length 2^n"));
    }
    Ok(commit_table_seeded(p, table, &crate::rand::fresh_seed()?))
}

/// As [`commit_table`], with the seed of the prover's randomness given by the caller: for tests and
/// test vectors only (feature `insecure-test-vectors`); the seed must never be reused.
pub(crate) fn commit_table_seeded(p: &Params, table: &[Fp], seed: &Digest) -> (Digest, ProverData) {
    let mut alpha = table.to_vec();
    mobius(&mut alpha);
    commit_coeffs_seeded(p, &alpha, seed)
}

fn init_transcript<E: ExtField>(p: &Params, root: &Digest, z: &[E], v: E) -> Transcript {
    let mut tr = Transcript::new(b"kronecker-fri-v3");
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
        .flat_map(|&x| (x as u64).to_le_bytes())
        .collect();
    tr.absorb(b"params", &pb);
    tr.absorb(b"commitment", root);
    let zb: Vec<u8> = z.iter().flat_map(e_bytes).collect();
    tr.absorb(b"point", &zb);
    tr.absorb(b"value", &e_bytes(&v));
    tr
}

pub(crate) fn inv_powers(omega: Fp, count: usize) -> Vec<Fp> {
    let oi = omega.inv();
    let mut out = Vec::with_capacity(count);
    let mut acc = Fp::ONE;
    for _ in 0..count {
        out.push(acc);
        acc = acc * oi;
    }
    out
}

/// The virtual word at one point (Definition 6.5):
/// h(xi) = (xi w(xi) K_z(xi) - w_A(xi) - v xi^N) / xi^{N+1}, given K_z(xi), xi^N and xi^{-(N+1)}.
#[inline(always)]
pub fn virtual_value<E: ExtField>(xi: Fp, w: E, wa: E, kz: E, v: E, xi_n: Fp, inv_xi_n1: Fp) -> E {
    ((w * kz) * xi - wa - v * xi_n) * inv_xi_n1
}

/// Deviations from the honest prover, used by the tests (Section 9.5).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cheat {
    None,
    /// claim v + 1 with the honest opening polynomial A
    WrongValue,
    /// claim v + 1 and send w_A for A - X^N, of degree N, so that the virtual word is the
    /// honest H (Remark 4.13)
    AbsorbInA,
}

/// Prover: returns v = f(z) and the proof.  `seed` must be fresh and secret (salts).
pub fn open<E: ExtField>(p: &Params, pd: &ProverData, z: &[E]) -> Result<(E, Proof<E>), Error> {
    p.validate()?;
    if z.len() != p.n {
        return Err(Error::Input("the point must have n coordinates"));
    }
    if pd.alpha.len() != p.big_n() || pd.y.len() != p.m() {
        return Err(Error::Input(
            "the prover data was made with other parameters",
        ));
    }
    Ok(open_seeded(p, pd, z, &crate::rand::fresh_seed()?))
}

/// As [`open`], with the seed of the prover's randomness given by the caller: for tests and
/// test vectors only (feature `insecure-test-vectors`); the seed must never be reused.
pub(crate) fn open_seeded<E: ExtField>(
    p: &Params,
    pd: &ProverData,
    z: &[E],
    seed: &Digest,
) -> (E, Proof<E>) {
    open_with(p, pd, z, seed, Cheat::None)
}

pub(crate) fn open_with<E: ExtField>(
    p: &Params,
    pd: &ProverData,
    z: &[E],
    seed: &Digest,
    cheat: Cheat,
) -> (E, Proof<E>) {
    p.check();
    assert_eq!(z.len(), p.n);
    let (nn, m, ell) = (p.big_n(), p.m(), p.ell);
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

    // opening polynomials (Lemma 4.10), U = U_f over E
    let u: Vec<E> = pd.alpha.iter().map(|&x| E::from(x)).collect();
    let (mut a, mut v, h) = opening_polys(&u, z);
    match cheat {
        Cheat::None => {}
        Cheat::WrongValue => v = v + E::ONE,
        Cheat::AbsorbInA => {
            v = v + E::ONE;
            a.push(-E::ONE); // A - X^N: degree N
        }
    }
    let mut tr = init_transcript(p, &pd.tree0.root(), z, v);

    // round 1: w_A = ev_L(A)
    let mut wa = a.clone();
    wa.resize(m, E::ZERO);
    ntt(&mut wa, omega);
    let g0 = groups[0].1;
    let tree_a = coset_tree(&wa, g0, seed, b"round1", p.salt_len);
    tr.absorb(b"root", &tree_a.root());
    round_salts.push(salt(1));
    tr.absorb(b"salt", round_salts.last().unwrap());
    let beta: E = tr.challenge();
    let beta2 = beta * beta;

    // batched word w_0 = y + beta w_A + beta^2 h, with the virtual word h (Definition 6.5)
    let kz = kernel_on_domain(z, omega, m);
    let step_n = omega.pow(nn as u64);
    let step_inv = omega.pow((m - nn - 1) as u64); // omega^{-(N+1)}
    let mut w0 = vec![E::ZERO; m];
    crate::par::fill_chunks(&mut w0, |s, out| {
        let (mut x, mut xn, mut xinv) = (
            omega.pow(s as u64),
            step_n.pow(s as u64),
            step_inv.pow(s as u64),
        );
        for (t, o) in out.iter_mut().enumerate() {
            let i = s + t;
            let yi = E::from(pd.y[i]);
            let hi = virtual_value(x, yi, wa[i], kz[i], v, xn, xinv);
            *o = yi + beta * wa[i] + beta2 * hi;
            x = x * omega;
            xn = xn * step_n;
            xinv = xinv * step_inv;
        }
    });
    drop(kz);
    let u0: Vec<E> = crate::par::map_range(nn, |i| u[i] + beta * a[i] + beta2 * h[i]);

    // rounds 2 .. l+1: challenges r_1 .. r_l; the word of every committed level (a group start
    // jc >= 1) is sent before r_{jc+1}
    let committed: Vec<usize> = groups
        .iter()
        .map(|&(jc, _)| jc)
        .filter(|&jc| jc >= 1)
        .collect();
    let mut kept: Vec<(usize, Vec<E>, MerkleTree)> = Vec::new(); // (level, word, tree)
    let mut caps = Vec::new();
    let mut coeffs = u0;
    let mut cur = w0;
    let mut rs: Vec<E> = Vec::with_capacity(ell);
    for j in 1..=ell {
        if j >= 2 && committed.contains(&(j - 1)) {
            let g = groups.iter().find(|&&(s, _)| s == j - 1).unwrap().1;
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
            cur = fold_word(&cur, r, &inv_x0, j - 1, inv2);
        }
    }
    drop(cur);
    // round l+2: P = pfold^(l)(U_0)
    let final_p = coeffs;
    let pb: Vec<u8> = final_p.iter().flat_map(e_bytes).collect();
    tr.absorb(b"final", &pb);
    round_salts.push(salt(ell + 2));
    tr.absorb(b"salt", round_salts.last().unwrap());
    let idx = tr.query_indices(p.queries, p.n + p.log_inv_rate);

    let c0 = p.cap_for(m / 2, g0 - 1);
    let level0 = distinct_positions(&idx, m >> g0)
        .into_iter()
        .map(|a0| Level0Opening {
            pos: a0,
            y: coset_values(&pd.y, g0, a0),
            y_open: pd.tree0.open_group_capped(a0 << (g0 - 1), g0 - 1, c0),
            a: coset_values(&wa, g0, a0),
            a_open: tree_a.open_group_capped(a0 << (g0 - 1), g0 - 1, c0),
        })
        .collect();
    let levels = kept
        .iter()
        .map(|(jc, word, tree)| {
            let g = groups.iter().find(|&&(s, _)| s == *jc).unwrap().1;
            let c = p.cap_for(word.len() / 2, g - 1);
            distinct_positions(&idx, m >> (jc + g))
                .into_iter()
                .map(|aj| LevelOpening {
                    pos: aj,
                    vals: coset_values(word, g, aj),
                    open: tree.open_group_capped(aj << (g - 1), g - 1, c),
                })
                .collect()
        })
        .collect();
    (
        v,
        Proof {
            cap_y: pd.tree0.cap(c0),
            cap_a: tree_a.cap(c0),
            caps,
            round_salts,
            p: final_p,
            level0,
            levels,
        },
    )
}

/// Verifier with the reason for rejection: "shape", "merkle" or "fold".
pub fn verify<E: ExtField>(
    p: &Params,
    root: &Digest,
    z: &[E],
    v: E,
    proof: &Proof<E>,
) -> Result<(), Error> {
    p.validate()?;
    let (nn, m, ell) = (p.big_n(), p.m(), p.ell);
    let groups = p.groups();
    let g0 = groups[0].1;
    let ncommit = groups.len() - 1;
    if z.len() != p.n
        || proof.caps.len() != ncommit
        || proof.levels.len() != ncommit
        || proof.round_salts.len() != ell + 2
        || proof.p.len() != nn >> ell
        || proof
            .level0
            .iter()
            .any(|o| o.y.len() != 1 << (g0 - 1) || o.a.len() != 1 << (g0 - 1))
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
    // canonical form: caps, paths and salts have exactly the prescribed lengths
    let sl = p.salt_len;
    let op_ok = |op: &GroupOpening, depth: usize, h: usize, c: usize| {
        op.path.len() == depth - h - c && op.salts.iter().all(|x| x.len() == sl)
    };
    let depth0 = (m / 2).trailing_zeros() as usize;
    let c0 = p.cap_for(m / 2, g0 - 1);
    if proof.round_salts.iter().any(|x| x.len() != sl)
        || proof.cap_y.len() != 1 << c0
        || proof.cap_a.len() != 1 << c0
        || proof
            .level0
            .iter()
            .any(|o| !op_ok(&o.y_open, depth0, g0 - 1, c0) || !op_ok(&o.a_open, depth0, g0 - 1, c0))
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
    if root_from_cap(&proof.cap_y)? != *root {
        return Err(Error::Merkle);
    }
    let omega = p.omega();
    let mut tr = init_transcript(p, root, z, v);
    tr.absorb(b"root", &root_from_cap(&proof.cap_a)?);
    tr.absorb(b"salt", &proof.round_salts[0]);
    let beta: E = tr.challenge();
    let beta2 = beta * beta;
    let mut rs: Vec<E> = Vec::with_capacity(ell);
    let mut ci = 0;
    for j in 1..=ell {
        if j >= 2 && groups.iter().any(|&(s, _)| s == j - 1) {
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

    // the openings must be exactly one per distinct queried position, in increasing order
    let mg0 = m >> g0;
    let pos0 = distinct_positions(&idx, mg0);
    if proof.level0.len() != pos0.len() || proof.level0.iter().zip(&pos0).any(|(o, &a)| o.pos != a)
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
    // authenticate every opening once
    for o in &proof.level0 {
        let yd: Vec<Vec<u8>> = o.y.iter().map(|[x, y]| pair_bytes(x, y)).collect();
        let ad: Vec<Vec<u8>> = o.a.iter().map(|[x, y]| pair_bytes(x, y)).collect();
        if !verify_group_capped(&proof.cap_y, o.pos << (g0 - 1), g0 - 1, &yd, &o.y_open)
            || !verify_group_capped(&proof.cap_a, o.pos << (g0 - 1), g0 - 1, &ad, &o.a_open)
        {
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
        // level 0: the commitment and w_A on the 2^{g0} points above position a0 of L_{g0}
        let a0 = i0 % mg0;
        let o = &proof.level0[find(&pos0, a0)];
        let (yv, av) = (unpair(&o.y), unpair(&o.a));
        let w0: Vec<E> = (0..yv.len())
            .map(|t| {
                let pos = a0 + t * mg0;
                // xi = omega^pos, xi^N and xi^{-(N+1)} as powers of omega (no inversion)
                let xi = omega.pow(pos as u64);
                let xi_n = omega.pow(((pos * nn) % m) as u64);
                let inv = omega.pow(((m - (pos * (nn + 1)) % m) % m) as u64);
                let w = E::from(yv[t]);
                let h = virtual_value(xi, w, av[t], kernel_eval(z, E::from(xi)), v, xi_n, inv);
                w + beta * av[t] + beta2 * h
            })
            .collect();
        let mut value = fold_coset(w0, a0, 0, mg0, &rs, m, omega);
        // committed levels
        for (gi, &(jc, g)) in groups.iter().enumerate().skip(1) {
            let mg = m >> (jc + g);
            let aj = i0 % mg;
            let o = &proof.levels[gi - 1][find(&level_pos[gi - 1], aj)];
            let vals = unpair(&o.vals);
            // the previous group's result is the value at position (i0 mod M_jc) of L_jc
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
    use crate::poly::ml_eval_coeffs;

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

    /// Lemma 6.6(3): for honest openings, the virtual word is ev_L(H).
    #[test]
    fn virtual_word_is_h_for_honest_openings() {
        let mut rng = Rng(17);
        for n in 1..=6usize {
            let (nn, m) = (1usize << n, 4usize << n);
            let omega = Fp::two_adic_root((n + 2) as u32);
            let u: Vec<Fp4> = (0..nn).map(|_| Fp4::from(rng.fp())).collect();
            let z: Vec<Fp4> = (0..n).map(|_| rng.e()).collect();
            let (a, v, h) = opening_polys(&u, &z);
            for i in 0..m {
                let x = omega.pow(i as u64);
                let xn = x.pow(nn as u64);
                let val = virtual_value(
                    x,
                    horner(&u, Fp4::from(x)),
                    horner(&a, Fp4::from(x)),
                    kernel_eval(&z, Fp4::from(x)),
                    v,
                    xn,
                    (xn * x).inv(),
                );
                assert_eq!(val, horner(&h, Fp4::from(x)));
            }
        }
    }

    fn cheats<E: ExtField>() {
        let mut rng = Rng(99);
        for (n, ell, fold_log, cap_log) in [
            (4, 2, 1, 0),
            (6, 3, 1, 2),
            (8, 8, 3, 3),
            (10, 5, 2, 0),
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
            let alpha: Vec<Fp> = (0..1 << n).map(|_| rng.fp()).collect();
            let z: Vec<E> = (0..n).map(|_| rng.e()).collect();
            let (root, pd) = commit_coeffs_seeded(&p, &alpha, &[1u8; 32]);
            let (v, proof) = open_seeded(&p, &pd, &z, &[2u8; 32]);
            assert_eq!(
                v,
                ml_eval_coeffs(
                    &pd.alpha.iter().map(|&x| E::from(x)).collect::<Vec<_>>(),
                    &z
                )
            );
            assert!(verify(&p, &root, &z, v, &proof).is_ok());
            let (v1, pr1) = open_with(&p, &pd, &z, &[3u8; 32], Cheat::WrongValue);
            assert_eq!(
                verify(&p, &root, &z, v1, &pr1),
                Err(Error::Fold),
                "n={n} l={ell}"
            );
            let (v2, pr2) = open_with(&p, &pd, &z, &[4u8; 32], Cheat::AbsorbInA);
            assert_eq!(v2, v + E::ONE);
            assert_eq!(
                verify(&p, &root, &z, v2, &pr2),
                Err(Error::Fold),
                "n={n} l={ell}"
            );
        }
    }

    #[test]
    fn cheaters_are_rejected_fp2() {
        cheats::<Fp2>();
    }

    #[test]
    fn cheaters_are_rejected_fp4() {
        cheats::<Fp4>();
    }
}
