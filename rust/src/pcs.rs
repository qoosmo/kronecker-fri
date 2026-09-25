//! The evaluation protocol Pi_KF of Section 6.3, compiled with salted Merkle trees and a
//! Fiat-Shamir transcript (Sections 3.4 and 8.1).
//!
//! The committed polynomial has coefficients in F_p (Goldilocks); the point z, the value v, the
//! challenges, the opening word w_A, the virtual word h and all folded words live in the extension
//! E = F_{p^e} (e = 2 or 4).
//!
//! Domain layout: L = <omega>, position i of a word on L_j is omega_j^i with omega_j = omega^{2^j};
//! the fibre over position k of L_{j+1} is {k, k + M_{j+1}}.
//! Leaves are fibres (Section 8.1): leaf k of the tree of a word w on L_j holds (w[k], w[k + M_j/2]).

use crate::field::{ExtField, Field, Fp};
use crate::merkle::{Digest, GroupOpening, MerkleTree, Transcript, verify_group};
use crate::poly::{
    fold_pair, fold_word, horner, kernel_eval, kernel_on_domain, mobius, ntt, opening_polys, pfold,
};

#[derive(Clone, Copy, Debug)]
pub struct Params {
    /// number of variables n (N = 2^n)
    pub n: usize,
    /// R with rate rho = 2^-R (R >= 2, Section 6.1)
    pub log_inv_rate: usize,
    /// number of folding rounds l, 1 <= l <= n
    pub ell: usize,
    /// number of queries kappa
    pub queries: usize,
    /// salt length in bytes (0 = unsalted trees)
    pub salt_len: usize,
}

impl Params {
    pub fn big_n(&self) -> usize {
        1 << self.n
    }
    pub fn m(&self) -> usize {
        1 << (self.n + self.log_inv_rate)
    }
    pub fn omega(&self) -> Fp {
        Fp::two_adic_root((self.n + self.log_inv_rate) as u32)
    }
    pub fn check(&self) {
        assert!(self.n >= 1 && self.log_inv_rate >= 2 && self.n + self.log_inv_rate <= 32);
        assert!(self.ell >= 1 && self.ell <= self.n);
        assert!(self.queries >= 1);
    }
}

fn e_bytes<E: ExtField>(x: &E) -> Vec<u8> {
    let mut b = Vec::with_capacity(8 * E::DEGREE);
    x.to_bytes(&mut b);
    b
}

fn pair_bytes<T: Field>(a: &T, b: &T) -> Vec<u8> {
    let mut out = Vec::with_capacity(64);
    a.to_bytes(&mut out);
    b.to_bytes(&mut out);
    out
}

/// Tree over the fibres of a word: leaf k = (w[k], w[k + len/2]).
fn fibre_tree<T: Field>(w: &[T], seed: &Digest, label: &[u8], salt_len: usize) -> MerkleTree {
    let h = w.len() / 2;
    MerkleTree::from_fn(
        h,
        |k, b| {
            w[k].to_bytes(b);
            w[k + h].to_bytes(b)
        },
        seed,
        label,
        salt_len,
    )
}

pub struct ProverData {
    /// coefficient form of f (= coefficients of U_f), over F_p
    pub alpha: Vec<Fp>,
    /// the commitment word y = Enc(f) = ev_L(U_f)
    pub y: Vec<Fp>,
    tree0: MerkleTree,
}

#[derive(Clone, Debug)]
pub struct QueryProof<E> {
    /// y(xi), y(-xi) for the level-1 fibre xi = omega^k, k = i mod M/2
    pub y: [Fp; 2],
    pub y_open: GroupOpening,
    /// w_A(xi), w_A(-xi)
    pub a: [E; 2],
    pub a_open: GroupOpening,
    /// for levels j = 1 .. l-1: w_j on the fibre read by the level-(j+1) fold check
    pub levels: Vec<([E; 2], GroupOpening)>,
}

#[derive(Clone, Debug)]
pub struct Proof<E> {
    /// root of w_A
    pub root_a: Digest,
    /// roots of w_1 .. w_{l-1}
    pub roots: Vec<Digest>,
    /// round salts of rounds 1 .. l+2
    pub round_salts: Vec<Vec<u8>>,
    /// coefficients of the final polynomial P (length N_l)
    pub p: Vec<E>,
    pub queries: Vec<QueryProof<E>>,
}

impl<E: ExtField> Proof<E> {
    /// Serialized size in bytes: 32 per digest, 8 per F_p element, 8e per E element, salts.
    pub fn size_bytes(&self) -> usize {
        let e = 8 * E::DEGREE;
        let open =
            |o: &GroupOpening| 32 * o.path.len() + o.salts.iter().map(|s| s.len()).sum::<usize>();
        let mut s = 32 + 32 * self.roots.len() + self.p.len() * e;
        s += self.round_salts.iter().map(|x| x.len()).sum::<usize>();
        for q in &self.queries {
            s += 16 + open(&q.y_open) + 2 * e + open(&q.a_open);
            for (_, o) in &q.levels {
                s += 2 * e + open(o);
            }
        }
        s
    }
}

/// Commit to f given in coefficient form (Definition 6.2): one NTT of size M.
pub fn commit_coeffs(p: &Params, alpha: &[Fp], seed: &Digest) -> (Digest, ProverData) {
    p.check();
    assert_eq!(alpha.len(), p.big_n());
    let mut y = alpha.to_vec();
    y.resize(p.m(), Fp::ZERO);
    ntt(&mut y, p.omega());
    let tree0 = fibre_tree(&y, seed, b"commit", p.salt_len);
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
pub fn commit_table(p: &Params, table: &[Fp], seed: &Digest) -> (Digest, ProverData) {
    let mut alpha = table.to_vec();
    mobius(&mut alpha);
    commit_coeffs(p, &alpha, seed)
}

fn init_transcript<E: ExtField>(p: &Params, root: &Digest, z: &[E], v: E) -> Transcript {
    let mut tr = Transcript::new(b"kronecker-fri-v2");
    let params = [p.n, p.log_inv_rate, p.ell, p.queries, p.salt_len, E::DEGREE];
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

fn inv_powers(omega: Fp, count: usize) -> Vec<Fp> {
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
pub fn open<E: ExtField>(p: &Params, pd: &ProverData, z: &[E], seed: &Digest) -> (E, Proof<E>) {
    open_with(p, pd, z, seed, Cheat::None)
}

pub fn open_with<E: ExtField>(
    p: &Params,
    pd: &ProverData,
    z: &[E],
    seed: &Digest,
    cheat: Cheat,
) -> (E, Proof<E>) {
    p.check();
    assert_eq!(z.len(), p.n);
    let (nn, m, ell) = (p.big_n(), p.m(), p.ell);
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
    let tree_a = fibre_tree(&wa, seed, b"round1", p.salt_len);
    tr.absorb(b"root", &tree_a.root());
    round_salts.push(salt(1));
    tr.absorb(b"salt", round_salts.last().unwrap());
    let beta: E = tr.challenge();
    let beta2 = beta * beta;

    // batched word w_0 = y + beta w_A + beta^2 h, with the virtual word h (Definition 6.5)
    let kz = kernel_on_domain(z, omega, m);
    let step_n = omega.pow(nn as u64);
    let step_inv = omega.pow((m - nn - 1) as u64); // omega^{-(N+1)}
    let (mut x, mut xn, mut xinv) = (Fp::ONE, Fp::ONE, Fp::ONE);
    let mut w0 = Vec::with_capacity(m);
    for i in 0..m {
        let yi = E::from(pd.y[i]);
        let hi = virtual_value(x, yi, wa[i], kz[i], v, xn, xinv);
        w0.push(yi + beta * wa[i] + beta2 * hi);
        x = x * omega;
        xn = xn * step_n;
        xinv = xinv * step_inv;
    }
    drop(kz);
    // U_0 = U + beta A + beta^2 H (coefficients); for Cheat::AbsorbInA the degree-N term is
    // dropped, since P must have fewer than N_l coefficients.
    let u0: Vec<E> = (0..nn).map(|i| u[i] + beta * a[i] + beta2 * h[i]).collect();

    // round 2: no message, challenge r_1
    round_salts.push(salt(2));
    tr.absorb(b"salt", round_salts.last().unwrap());
    let mut r: E = tr.challenge();

    // rounds 3 .. l+1: w_1 .. w_{l-1}
    let mut words: Vec<Vec<E>> = Vec::with_capacity(ell.saturating_sub(1));
    let mut trees: Vec<MerkleTree> = Vec::new();
    let mut roots = Vec::new();
    let mut coeffs = u0;
    for j in 1..ell {
        let prev = if j == 1 { &w0 } else { &words[j - 2] };
        let wj = fold_word(prev, r, &inv_x0, j - 1, inv2);
        coeffs = pfold(&coeffs, r);
        let tree = fibre_tree(&wj, seed, format!("w{j}").as_bytes(), p.salt_len);
        tr.absorb(b"root", &tree.root());
        roots.push(tree.root());
        round_salts.push(salt(j + 2));
        tr.absorb(b"salt", round_salts.last().unwrap());
        words.push(wj);
        trees.push(tree);
        r = tr.challenge();
    }
    drop(w0);
    // round l+2: P = pfold^(l)(U_0)
    let final_p = pfold(&coeffs, r);
    let pb: Vec<u8> = final_p.iter().flat_map(e_bytes).collect();
    tr.absorb(b"final", &pb);
    round_salts.push(salt(ell + 2));
    tr.absorb(b"salt", round_salts.last().unwrap());
    let idx = tr.query_indices(p.queries, p.n + p.log_inv_rate);

    let queries = idx
        .iter()
        .map(|&i0| {
            let k0 = i0 % (m / 2);
            let levels = (1..ell)
                .map(|j| {
                    let mj = m >> j;
                    let k = i0 % (mj / 2);
                    let w = &words[j - 1];
                    ([w[k], w[k + mj / 2]], trees[j - 1].open_group(k, 0))
                })
                .collect();
            QueryProof {
                y: [pd.y[k0], pd.y[k0 + m / 2]],
                y_open: pd.tree0.open_group(k0, 0),
                a: [wa[k0], wa[k0 + m / 2]],
                a_open: tree_a.open_group(k0, 0),
                levels,
            }
        })
        .collect();
    (
        v,
        Proof {
            root_a: tree_a.root(),
            roots,
            round_salts,
            p: final_p,
            queries,
        },
    )
}

/// Verifier.
pub fn verify<E: ExtField>(p: &Params, root: &Digest, z: &[E], v: E, proof: &Proof<E>) -> bool {
    verify_detail(p, root, z, v, proof).is_ok()
}

/// Verifier with the reason for rejection: "shape", "merkle" or "fold".
pub fn verify_detail<E: ExtField>(
    p: &Params,
    root: &Digest,
    z: &[E],
    v: E,
    proof: &Proof<E>,
) -> Result<(), &'static str> {
    p.check();
    let (nn, m, ell) = (p.big_n(), p.m(), p.ell);
    if z.len() != p.n
        || proof.roots.len() != ell - 1
        || proof.round_salts.len() != ell + 2
        || proof.p.len() != nn >> ell
        || proof.queries.len() != p.queries
        || proof.queries.iter().any(|q| q.levels.len() != ell - 1)
    {
        return Err("shape");
    }
    let omega = p.omega();
    let inv2 = Fp::new(2).inv();
    let mut tr = init_transcript(p, root, z, v);
    tr.absorb(b"root", &proof.root_a);
    tr.absorb(b"salt", &proof.round_salts[0]);
    let beta: E = tr.challenge();
    let beta2 = beta * beta;
    tr.absorb(b"salt", &proof.round_salts[1]);
    let mut rs: Vec<E> = vec![tr.challenge()];
    for j in 1..ell {
        tr.absorb(b"root", &proof.roots[j - 1]);
        tr.absorb(b"salt", &proof.round_salts[j + 1]);
        rs.push(tr.challenge());
    }
    let pb: Vec<u8> = proof.p.iter().flat_map(e_bytes).collect();
    tr.absorb(b"final", &pb);
    tr.absorb(b"salt", &proof.round_salts[ell + 1]);
    let idx = tr.query_indices(p.queries, p.n + p.log_inv_rate);

    for (q, &i0) in proof.queries.iter().zip(&idx) {
        let k0 = i0 % (m / 2);
        if !verify_group(root, k0, 0, &[pair_bytes(&q.y[0], &q.y[1])], &q.y_open)
            || !verify_group(
                &proof.root_a,
                k0,
                0,
                &[pair_bytes(&q.a[0], &q.a[1])],
                &q.a_open,
            )
        {
            return Err("merkle");
        }
        // w_0 on the fibre {xi, -xi}, xi = omega^{k0}, through the virtual word (Definition 6.5)
        let xi = omega.pow(k0 as u64);
        let xi2 = xi.square();
        let xi_n = xi2.pow((nn / 2) as u64); // (+-xi)^N, N even
        let inv_xi_n1 = (xi_n * xi).inv(); // xi^{-(N+1)}; (-xi)^{-(N+1)} = -xi^{-(N+1)}
        // K_z(+-xi) = (z_1 +- xi) K_{z'}(xi^2)
        let k_rest = kernel_eval(&z[1..], E::from(xi2));
        let mut pair = [E::ZERO; 2];
        for s in 0..2 {
            let (x, inv) = if s == 0 {
                (xi, inv_xi_n1)
            } else {
                (-xi, -inv_xi_n1)
            };
            let kz = (z[0] + E::from(x)) * k_rest;
            let w = E::from(q.y[s]);
            let h = virtual_value(x, w, q.a[s], kz, v, xi_n, inv);
            pair[s] = w + beta * q.a[s] + beta2 * h;
        }
        // fold checks
        let mut k = k0; // fibre index at the current level
        for j in 1..=ell {
            // level j: fold w_{j-1} over the fibre {k, k + M_j} of L_{j-1}; result at position k of L_j
            // (2 xi_j)^{-1} = omega^{M - k 2^{j-1}} / 2, with xi_j = omega^{k 2^{j-1}} (no inversion)
            let inv_2xi = omega.pow((m - (k << (j - 1))) as u64) * inv2;
            let folded = fold_pair(pair[0], pair[1], inv_2xi, rs[j - 1], inv2);
            if j < ell {
                let mj = m >> j;
                let kn = k % (mj / 2);
                let (vals, op) = &q.levels[j - 1];
                if !verify_group(
                    &proof.roots[j - 1],
                    kn,
                    0,
                    &[pair_bytes(&vals[0], &vals[1])],
                    op,
                ) {
                    return Err("merkle");
                }
                let expected = if k < mj / 2 { vals[0] } else { vals[1] };
                if folded != expected {
                    return Err("fold");
                }
                pair = *vals;
                k = kn;
            } else {
                let eta = omega.pow((k as u64) << ell);
                if folded != horner(&proof.p, E::from(eta)) {
                    return Err("fold");
                }
            }
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
        for (n, ell) in [(4, 2), (6, 3), (8, 8), (10, 5)] {
            let p = Params {
                n,
                log_inv_rate: 2,
                ell,
                queries: 30,
                salt_len: 32,
            };
            let alpha: Vec<Fp> = (0..1 << n).map(|_| rng.fp()).collect();
            let z: Vec<E> = (0..n).map(|_| rng.e()).collect();
            let (root, pd) = commit_coeffs(&p, &alpha, &[1u8; 32]);
            let (v, proof) = open(&p, &pd, &z, &[2u8; 32]);
            assert_eq!(
                v,
                ml_eval_coeffs(
                    &pd.alpha.iter().map(|&x| E::from(x)).collect::<Vec<_>>(),
                    &z
                )
            );
            assert!(verify(&p, &root, &z, v, &proof));
            let (v1, pr1) = open_with(&p, &pd, &z, &[3u8; 32], Cheat::WrongValue);
            assert_eq!(
                verify_detail(&p, &root, &z, v1, &pr1),
                Err("fold"),
                "n={n} l={ell}"
            );
            let (v2, pr2) = open_with(&p, &pd, &z, &[4u8; 32], Cheat::AbsorbInA);
            assert_eq!(v2, v + E::ONE);
            assert_eq!(
                verify_detail(&p, &root, &z, v2, &pr2),
                Err("fold"),
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
