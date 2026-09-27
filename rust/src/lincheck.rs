//! Clear-text check of the sumcheck-free lincheck of the research note (`notes/inner-product`,
//! Section 5): the reduction of `a' = M z` (M a public sparse matrix, z and a' committed tables)
//! to evaluation, inner-product and Hadamard statements on affine forms of committed and public
//! tables.  This module computes the prover's tables and checks the statements directly (no
//! commitments, no folding test): it validates the algebra of the reduction before it is compiled
//! with `batch`.
//!
//! Notation (N = 2^n, tables indexed by w in [0, N)); the note writes eta for gamma, zeta for u,
//! phi for h and psi for g:
//! - index of M (K <= N entries, padded with val = 0, row = col = 0): tables row, col, val, and the
//!   multiplicities mR(w) = #{k : row_k = w}, mC(w) = #{k : col_k = w};
//! - public tables: one(w) = 1, id(w) = w, G_gamma(w) = gamma^w, with O(n) closed forms for their
//!   table-form polynomials (`v_one`, `v_id`, `v_geo`);
//! - round 1 (after gamma): e_k = gamma^{row_k}, u_k = z(col_k), p_k = e_k u_k;
//! - round 2 (after x_R, y_R, x_C, y_C): h^R_k = 1/(x_R - row_k - y_R e_k),
//!   g^R_w = mR(w)/(x_R - w - y_R gamma^w), h^C_k = 1/(x_C - col_k - y_C u_k),
//!   g^C_w = mC(w)/(x_C - w - y_C z(w));
//! - statements: IP(a', G_gamma) = IP(val, p) = s; Had(e, u, p);
//!   Had(h^R, x_R one - row - y_R e, one), Had(g^R, x_R one - id - y_R G_gamma, mR),
//!   IP(h^R, one) = IP(g^R, one); the same for the columns with (col, u) and (id, z).

use crate::field::{ExtField, Field, Fp};

/// V_one(x) = sum_{w < N} x^w = prod_{k < n} (1 + x^{2^k}).
pub fn v_one<E: ExtField>(n: usize, x: E) -> E {
    let mut acc = E::ONE;
    let mut p = x;
    for _ in 0..n {
        acc = acc * (E::ONE + p);
        p = p.square();
    }
    acc
}

/// V_{G_gamma}(x) = sum_w gamma^w x^w = V_one(gamma x).
pub fn v_geo<E: ExtField>(n: usize, gamma: E, x: E) -> E {
    v_one(n, gamma * x)
}

/// V_id(x) = sum_{w < N} w x^w, by S_{k+1} = (1 + x^{2^k}) S_k and
/// T_{k+1} = (1 + x^{2^k}) T_k + 2^k x^{2^k} S_k (S = V_one, T = V_id on 2^k points).
pub fn v_id<E: ExtField>(n: usize, x: E) -> E {
    let (mut s, mut t) = (E::ONE, E::ZERO);
    let mut p = x;
    let mut two_k = Fp::ONE;
    for _ in 0..n {
        let t_new = (E::ONE + p) * t + p * s * two_k;
        s = (E::ONE + p) * s;
        t = t_new;
        p = p.square();
        two_k = two_k.double();
    }
    t
}

/// A sparse N x N matrix given by K <= N entries (row, col, val), padded to N entries.
#[derive(Clone, Debug)]
pub struct Sparse {
    pub n: usize,
    pub row: Vec<usize>,
    pub col: Vec<usize>,
    pub val: Vec<Fp>,
}

impl Sparse {
    pub fn new(n: usize, mut entries: Vec<(usize, usize, Fp)>) -> Self {
        let nn = 1usize << n;
        assert!(entries.len() <= nn);
        entries.resize(nn, (0, 0, Fp::ZERO));
        Sparse {
            n,
            row: entries.iter().map(|e| e.0).collect(),
            col: entries.iter().map(|e| e.1).collect(),
            val: entries.iter().map(|e| e.2).collect(),
        }
    }
    pub fn matvec(&self, z: &[Fp]) -> Vec<Fp> {
        let mut out = vec![Fp::ZERO; 1 << self.n];
        for k in 0..self.row.len() {
            out[self.row[k]] = out[self.row[k]] + self.val[k] * z[self.col[k]];
        }
        out
    }
    /// Multiplicities mR, mC as field elements.
    pub fn multiplicities(&self) -> (Vec<Fp>, Vec<Fp>) {
        let nn = 1usize << self.n;
        let (mut mr, mut mc) = (vec![Fp::ZERO; nn], vec![Fp::ZERO; nn]);
        for k in 0..nn {
            mr[self.row[k]] = mr[self.row[k]] + Fp::ONE;
            mc[self.col[k]] = mc[self.col[k]] + Fp::ONE;
        }
        (mr, mc)
    }
}

/// The prover's round-1 tables.
#[derive(Clone, Debug)]
pub struct Round1<E> {
    pub e: Vec<E>,
    pub u: Vec<E>,
    pub p: Vec<E>,
}

/// The prover's round-2 tables.
#[derive(Clone, Debug)]
pub struct Round2<E> {
    pub hr: Vec<E>,
    pub gr: Vec<E>,
    pub hc: Vec<E>,
    pub gc: Vec<E>,
}

/// Challenges of the reduction.
#[derive(Clone, Copy, Debug)]
pub struct Chal<E> {
    pub gamma: E,
    pub xr: E,
    pub yr: E,
    pub xc: E,
    pub yc: E,
}

pub fn round1<E: ExtField>(m: &Sparse, z: &[Fp], gamma: E) -> Round1<E> {
    let e: Vec<E> = m.row.iter().map(|&r| gamma.pow(r as u64)).collect();
    let u: Vec<E> = m.col.iter().map(|&c| E::from(z[c])).collect();
    let p = e.iter().zip(&u).map(|(&a, &b)| a * b).collect();
    Round1 { e, u, p }
}

pub fn round2<E: ExtField>(m: &Sparse, z: &[Fp], r1: &Round1<E>, ch: &Chal<E>) -> Round2<E> {
    let (mr, mc) = m.multiplicities();
    let nn = 1usize << m.n;
    let fe = |w: usize| E::from(Fp::new(w as u64));
    let hr = (0..nn)
        .map(|k| (ch.xr - fe(m.row[k]) - ch.yr * r1.e[k]).inv())
        .collect();
    let gr = (0..nn)
        .map(|w| (ch.xr - fe(w) - ch.yr * ch.gamma.pow(w as u64)).inv() * mr[w])
        .collect();
    let hc = (0..nn)
        .map(|k| (ch.xc - fe(m.col[k]) - ch.yc * r1.u[k]).inv())
        .collect();
    let gc = (0..nn)
        .map(|w| (ch.xc - fe(w) - ch.yc * E::from(z[w])).inv() * mc[w])
        .collect();
    Round2 { hr, gr, hc, gc }
}

/// Checks every statement of the reduction in the clear; returns the first failing one.
pub fn check<E: ExtField>(
    m: &Sparse,
    z: &[Fp],
    a: &[Fp],
    r1: &Round1<E>,
    r2: &Round2<E>,
    ch: &Chal<E>,
) -> Result<(), &'static str> {
    let nn = 1usize << m.n;
    let (mr, mc) = m.multiplicities();
    let fe = |w: usize| E::from(Fp::new(w as u64));
    // IP(a', G_gamma) = IP(val, p)
    let s1 = (0..nn).fold(E::ZERO, |s, w| s + ch.gamma.pow(w as u64) * a[w]);
    let s2 = (0..nn).fold(E::ZERO, |s, k| s + r1.p[k] * m.val[k]);
    if s1 != s2 {
        return Err("weighted sum");
    }
    // Had(e, u, p)
    if (0..nn).any(|k| r1.e[k] * r1.u[k] != r1.p[k]) {
        return Err("hadamard p");
    }
    // row lookup
    if (0..nn).any(|k| r2.hr[k] * (ch.xr - fe(m.row[k]) - ch.yr * r1.e[k]) != E::ONE)
        || (0..nn)
            .any(|w| r2.gr[w] * (ch.xr - fe(w) - ch.yr * ch.gamma.pow(w as u64)) != E::from(mr[w]))
    {
        return Err("row hadamard");
    }
    let sum = |v: &[E]| v.iter().fold(E::ZERO, |s, &x| s + x);
    if sum(&r2.hr) != sum(&r2.gr) {
        return Err("row lookup");
    }
    // column lookup
    if (0..nn).any(|k| r2.hc[k] * (ch.xc - fe(m.col[k]) - ch.yc * r1.u[k]) != E::ONE)
        || (0..nn).any(|w| r2.gc[w] * (ch.xc - fe(w) - ch.yc * E::from(z[w])) != E::from(mc[w]))
    {
        return Err("column hadamard");
    }
    if sum(&r2.hc) != sum(&r2.gc) {
        return Err("column lookup");
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{Fp2, Fp4};
    use crate::poly::horner;

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn fp(&mut self) -> Fp {
            Fp::new(self.next())
        }
        fn e<E: ExtField>(&mut self) -> E {
            let d: Vec<Fp> = (0..E::DEGREE).map(|_| self.fp()).collect();
            E::from_digits(&d)
        }
    }

    #[test]
    fn public_tables_closed_forms() {
        let mut rng = Rng(5);
        for n in 0..=7 {
            let nn = 1usize << n;
            let x: Fp2 = rng.e();
            let g: Fp2 = rng.e();
            let one = vec![Fp2::ONE; nn];
            let id: Vec<Fp2> = (0..nn).map(|w| Fp2::from(Fp::new(w as u64))).collect();
            let geo: Vec<Fp2> = (0..nn).map(|w| g.pow(w as u64)).collect();
            assert_eq!(v_one(n, x), horner(&one, x));
            assert_eq!(v_id(n, x), horner(&id, x));
            assert_eq!(v_geo(n, g, x), horner(&geo, x));
        }
    }

    fn instance(rng: &mut Rng, n: usize) -> (Sparse, Vec<Fp>) {
        let nn = 1usize << n;
        let k = nn - nn / 4; // K < N: padding entries are exercised
        let entries: Vec<(usize, usize, Fp)> = (0..k)
            .map(|_| (rng.next() as usize % nn, rng.next() as usize % nn, rng.fp()))
            .collect();
        let z: Vec<Fp> = (0..nn).map(|_| rng.fp()).collect();
        (Sparse::new(n, entries), z)
    }

    fn run<E: ExtField>() {
        let mut rng = Rng(42);
        for n in 1..=8 {
            let (m, z) = instance(&mut rng, n);
            let a = m.matvec(&z);
            let ch: Chal<E> = Chal {
                gamma: rng.e(),
                xr: rng.e(),
                yr: rng.e(),
                xc: rng.e(),
                yc: rng.e(),
            };
            // honest
            let r1 = round1(&m, &z, ch.gamma);
            let r2 = round2(&m, &z, &r1, &ch);
            assert_eq!(check(&m, &z, &a, &r1, &r2, &ch), Ok(()), "n={n}");
            // a' wrong in one entry, honest tables: the weighted sums differ
            let mut a_bad = a.clone();
            a_bad[rng.next() as usize % (1 << n)] = a_bad[0] + Fp::ONE;
            let a_bad = if a_bad == a {
                let mut t = a.clone();
                t[0] = t[0] + Fp::ONE;
                t
            } else {
                a_bad
            };
            assert_eq!(check(&m, &z, &a_bad, &r1, &r2, &ch), Err("weighted sum"));
            let diff = (0..1usize << n).fold(E::ZERO, |s, w| {
                s + ch.gamma.pow(w as u64) * (E::from(a_bad[w]) - E::from(a[w]))
            });
            let k0 = (0..m.val.len()).find(|&k| m.val[k] != Fp::ZERO).unwrap();
            let dp = diff * E::from(m.val[k0].inv());
            // forge u_{k0} so that the weighted sums agree: the column lookup fails
            let mut f1 = r1.clone();
            f1.p[k0] = f1.p[k0] + dp;
            f1.u[k0] = f1.p[k0] * f1.e[k0].inv();
            let f2 = round2(&m, &z, &f1, &ch);
            assert_eq!(
                check(&m, &z, &a_bad, &f1, &f2, &ch),
                Err("column lookup"),
                "n={n}"
            );
            // forge e_{k0} instead: the row lookup fails
            let mut g1 = r1.clone();
            g1.p[k0] = g1.p[k0] + dp;
            g1.e[k0] = g1.p[k0] * g1.u[k0].inv();
            let g2 = round2(&m, &z, &g1, &ch);
            assert_eq!(
                check(&m, &z, &a_bad, &g1, &g2, &ch),
                Err("row lookup"),
                "n={n}"
            );
        }
    }

    #[test]
    fn lincheck_reduction_fp2() {
        run::<Fp2>();
    }

    #[test]
    fn lincheck_reduction_fp4() {
        run::<Fp4>();
    }
}
