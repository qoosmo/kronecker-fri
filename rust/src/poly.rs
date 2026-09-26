//! Univariate and multilinear helpers: Moebius transform (Lemma 2.6), NTT (Fact 6.4),
//! kernel polynomial and kernel product (Section 4), and the kernel fold (Section 5).
//!
//! Index conventions: bit k of the paper (k = 1..n) is bit k-1 here; z_k is z[k-1].

use crate::field::{Field, Fp};
use core::ops::Mul;

/// Table form -> coefficient form (Moebius transform, Lemma 2.6): (n/2) N subtractions.
/// Coefficient a multiplies the monomial x^a = prod_{k : a_k = 1} x_k.
pub fn mobius<F: Field>(v: &mut [F]) {
    let n = v.len();
    assert!(n.is_power_of_two());
    let mut half = 1;
    while half < n {
        for block in v.chunks_exact_mut(2 * half) {
            let (lo, hi) = block.split_at_mut(half);
            for (a, b) in lo.iter().zip(hi.iter_mut()) {
                *b = *b - *a;
            }
        }
        half *= 2;
    }
}

/// Evaluation of a multilinear polynomial in coefficient form: f(z) = sum_a alpha_a z^a.
pub fn ml_eval_coeffs<F: Field>(alpha: &[F], z: &[F]) -> F {
    assert_eq!(alpha.len(), 1 << z.len());
    // z^a for all a, built bit by bit (Lemma 4.9(2))
    let mut pw = vec![F::ONE];
    for &zk in z {
        let ext: Vec<F> = pw.iter().map(|&x| x * zk).collect();
        pw.extend(ext);
    }
    alpha
        .iter()
        .zip(&pw)
        .fold(F::ZERO, |acc, (&a, &b)| acc + a * b)
}

/// Horner evaluation of a coefficient vector.
pub fn horner<F: Field>(c: &[F], x: F) -> F {
    c.iter().rev().fold(F::ZERO, |acc, &a| acc * x + a)
}

fn bit_reverse<T>(v: &mut [T]) {
    let n = v.len();
    let bits = n.trailing_zeros();
    if bits == 0 {
        return;
    }
    for i in 0..n {
        let j = i.reverse_bits() >> (usize::BITS - bits);
        if i < j {
            v.swap(i, j);
        }
    }
}

/// In-place radix-2 NTT: coefficients -> evaluations at omega^i (natural order), omega in F_p of
/// order v.len(). The twiddles lie in F_p, so over an extension of degree e this costs e base NTTs.
pub fn ntt<F: Field + Mul<Fp, Output = F>>(v: &mut [F], omega: Fp) {
    let n = v.len();
    assert!(n.is_power_of_two());
    bit_reverse(v);
    let mut len = 2;
    while len <= n {
        let w_len = omega.pow((n / len) as u64);
        let half = len / 2;
        let mut tw = Vec::with_capacity(half);
        let mut w = Fp::ONE;
        for _ in 0..half {
            tw.push(w);
            w = w * w_len;
        }
        for block in v.chunks_exact_mut(len) {
            let (lo, hi) = block.split_at_mut(half);
            for k in 0..half {
                let u = lo[k];
                let t = hi[k] * tw[k];
                lo[k] = u + t;
                hi[k] = u - t;
            }
        }
        len *= 2;
    }
}

/// K_z(xi) = prod_k (xi^{2^{k-1}} + z_k), with n-1 squarings (Lemma 4.9(1)).
pub fn kernel_eval<F: Field>(z: &[F], xi: F) -> F {
    let mut acc = F::ONE;
    let mut x = xi;
    for (k, &zk) in z.iter().enumerate() {
        if k > 0 {
            x = x.square();
        }
        acc = acc * (x + zk);
    }
    acc
}

/// K_z on the whole domain L = <omega> of order m (natural order), by the recursion
/// K_z(x) = (x + z_1) K_{z'}(x^2) (Lemma 4.4(2)) along L_0, L_1, ..., L_n (Lemma 6.4):
/// fewer than 2m multiplications and additions in F, besides the powers of omega.
pub fn kernel_on_domain<F: Field + Mul<Fp, Output = F> + From<Fp>>(
    z: &[F],
    omega: Fp,
    m: usize,
) -> Vec<F> {
    let n = z.len();
    // level n: domain L_n of order m >> n, K = 1
    let mut cur = vec![F::ONE; m >> n];
    for k in (1..=n).rev() {
        let mk = m >> (k - 1); // order of L_{k-1}
        let half = mk / 2;
        let om = omega.pow(1u64 << (k - 1));
        let mut next = vec![F::ZERO; mk];
        let mut x = Fp::ONE;
        // positions i and i + half of L_{k-1} are x and -x, both squaring to position i of L_k
        for i in 0..half {
            let xf = F::from(x);
            next[i] = (z[k - 1] + xf) * cur[i];
            next[i + half] = (z[k - 1] - xf) * cur[i];
            x = x * om;
        }
        cur = next;
    }
    cur
}

/// Coefficients of K_z (length N): [X^j] K_z = prod_{k : j_k = 0} z_k (Lemma 4.4(3)).
pub fn kernel_coeffs<F: Field>(z: &[F]) -> Vec<F> {
    let mut k = vec![F::ONE];
    for &zk in z {
        // multiply by (X^{len} + z_k): new = z_k * old  ||  old
        let mut next: Vec<F> = k.iter().map(|&c| c * zk).collect();
        next.extend_from_slice(&k);
        k = next;
    }
    k
}

/// The product U * K_z (length 2N - 1) by n multiplications by binomials X^{2^{k-1}} + z_k
/// (Lemma 4.9(3)): [X^j] Q_k = z_k [X^j] Q_{k-1} + [X^{j - 2^{k-1}}] Q_{k-1}.
pub fn kernel_product<F: Field>(u: &[F], z: &[F]) -> Vec<F> {
    let n = u.len();
    assert_eq!(n, 1 << z.len());
    let mut q = u.to_vec();
    let mut shift = 1usize;
    for &zk in z {
        let len = q.len();
        let mut next = vec![F::ZERO; len + shift];
        for j in 0..len {
            next[j] = next[j] + zk * q[j];
            next[j + shift] = next[j + shift] + q[j];
        }
        q = next;
        shift <<= 1;
    }
    debug_assert_eq!(q.len(), 2 * n - 1);
    q
}

/// Opening polynomials (Lemma 4.10, Definition 4.11): X U K_z = A + v X^N + X^{N+1} H.
/// Returns (A, v, H), with A and H of length N (H padded with a zero).
pub fn opening_polys<F: Field>(u: &[F], z: &[F]) -> (Vec<F>, F, Vec<F>) {
    let n = u.len();
    let q = kernel_product(u, z); // degrees 0 .. 2N-2
    let mut a = Vec::with_capacity(n);
    a.push(F::ZERO); // [X^0] (X Q) = 0
    a.extend_from_slice(&q[..n - 1]); // [X^j] (X Q) = [X^{j-1}] Q
    let v = q[n - 1];
    let mut h = q[n..].to_vec(); // [X^{N+1+j}] (X Q) = [X^{N+j}] Q, j = 0 .. N-2
    h.push(F::ZERO);
    (a, v, h)
}

/// Kernel fold of a polynomial (Definition 5.1): pfold_r(P) = (2r-1) P_e + (1-r) P_o.
pub fn pfold<F: Field>(c: &[F], r: F) -> Vec<F> {
    let a = r.double() - F::ONE;
    let b = F::ONE - r;
    c.as_chunks::<2>()
        .0
        .iter()
        .map(|[e, o]| a * *e + b * *o)
        .collect()
}

/// Kernel fold of one fibre in line form (Lemma 5.3): with a = w(xi), b = w(-xi),
/// w_e = (a+b)/2, w_o = (a-b)/(2 xi), fold_r = (w_o - w_e) + r (2 w_e - w_o).  7 operations.
#[inline(always)]
pub fn fold_pair<F: Field + Mul<Fp, Output = F>>(a: F, b: F, inv_2xi: Fp, r: F, inv2: Fp) -> F {
    let we = (a + b) * inv2;
    let wo = (a - b) * inv_2xi;
    (wo - we) + r * (we.double() - wo)
}

/// Kernel fold of a word on L_j (natural order: position i is omega_j^i, and the fibre over
/// position k of L_{j+1} is {k, k + M_{j+1}}).  `inv_x0[t] = omega^{-t}` for t < M/2.
pub fn fold_word<F: Field + Mul<Fp, Output = F>>(
    w: &[F],
    r: F,
    inv_x0: &[Fp],
    level: usize,
    inv2: Fp,
) -> Vec<F> {
    let h = w.len() / 2;
    (0..h)
        .map(|k| {
            let inv_2xi = inv_x0[k << level] * inv2;
            fold_pair(w[k], w[k + h], inv_2xi, r, inv2)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{ExtField, Fp2, Fp4};

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

    fn naive_mul<F: Field>(a: &[F], b: &[F]) -> Vec<F> {
        let mut c = vec![F::ZERO; a.len() + b.len() - 1];
        for (i, &x) in a.iter().enumerate() {
            for (j, &y) in b.iter().enumerate() {
                c[i + j] = c[i + j] + x * y;
            }
        }
        c
    }

    #[test]
    fn ntt_matches_horner() {
        let mut r = Rng(7);
        for k in 1..10 {
            let n = 1 << k;
            let omega = Fp::two_adic_root(k);
            let c: Vec<Fp4> = (0..n).map(|_| r.e()).collect();
            let mut e = c.clone();
            ntt(&mut e, omega);
            for i in 0..n {
                assert_eq!(e[i], horner(&c, Fp4::from(omega.pow(i as u64))));
            }
        }
    }

    fn kernel_checks<E: ExtField>() {
        let mut r = Rng(11);
        for n in 1..=8 {
            let nn = 1usize << n;
            let z: Vec<E> = (0..n).map(|_| r.e()).collect();
            let kc = kernel_coeffs(&z);
            // Definition 4.3 as a product of binomials
            let mut direct = vec![E::ONE];
            for (k, &zk) in z.iter().enumerate() {
                let mut b = vec![E::ZERO; (1 << k) + 1];
                b[0] = zk;
                b[1 << k] = E::ONE;
                direct = naive_mul(&direct, &b);
            }
            assert_eq!(kc, direct, "coefficient rule, n={n}");
            // K_z(xi)
            let xi: E = r.e();
            assert_eq!(kernel_eval(&z, xi), horner(&kc, xi));
            // extraction identity (Theorem 4.5), from a table via Moebius (Lemma 2.6)
            let table: Vec<Fp> = (0..nn).map(|_| r.fp()).collect();
            let mut alpha = table.clone();
            mobius(&mut alpha);
            let u: Vec<E> = alpha.iter().map(|&x| E::from(x)).collect();
            let q = kernel_product(&u, &z);
            assert_eq!(q, naive_mul(&u, &kc), "kernel product, n={n}");
            let fz = ml_eval_coeffs(&u, &z);
            assert_eq!(q[nn - 1], fz, "extraction identity, n={n}");
            // table form: f(b) = sum_{a subset b} alpha_a
            for b in 0..nn {
                let bits: Vec<E> = (0..n)
                    .map(|k| if b >> k & 1 == 1 { E::ONE } else { E::ZERO })
                    .collect();
                assert_eq!(ml_eval_coeffs(&u, &bits), E::from(table[b]));
            }
            // split lemma (Lemma 4.10)
            let (a, v, h) = opening_polys(&u, &z);
            assert_eq!(v, fz);
            assert_eq!(a[0], E::ZERO);
            assert_eq!(h[nn - 1], E::ZERO);
            let x = r.e::<E>();
            let xn = x.pow(nn as u64);
            assert_eq!(
                x * horner(&u, x) * kernel_eval(&z, x),
                horner(&a, x) + v * xn + xn * x * horner(&h, x)
            );
        }
    }

    #[test]
    fn kernel_on_domain_matches_pointwise() {
        let mut r = Rng(21);
        for n in 1..=6usize {
            let m = 4usize << n;
            let omega = Fp::two_adic_root((n + 2) as u32);
            let z: Vec<Fp4> = (0..n).map(|_| r.e()).collect();
            let k = kernel_on_domain(&z, omega, m);
            for i in 0..m {
                assert_eq!(k[i], kernel_eval(&z, Fp4::from(omega.pow(i as u64))));
            }
        }
    }

    #[test]
    fn kernel_identities_fp2() {
        kernel_checks::<Fp2>();
    }

    #[test]
    fn kernel_identities_fp4() {
        kernel_checks::<Fp4>();
    }

    #[test]
    fn fold_consistency_and_iterated_formula() {
        let mut rg = Rng(3);
        for n in 1..=7usize {
            let nn = 1usize << n;
            let m = 4 * nn;
            let omega = Fp::two_adic_root((n + 2) as u32);
            let inv2 = Fp::new(2).inv();
            let oi = omega.inv();
            let inv_x0: Vec<Fp> = (0..m / 2)
                .scan(Fp::ONE, |s, _| {
                    let c = *s;
                    *s = *s * oi;
                    Some(c)
                })
                .collect();
            let u: Vec<Fp2> = (0..nn).map(|_| rg.e()).collect();
            let mut w = u.clone();
            w.resize(m, Fp2::ZERO);
            ntt(&mut w, omega);
            let mut q = u.clone();
            let rs: Vec<Fp2> = (0..n).map(|_| rg.e()).collect();
            for j in 0..n {
                // explicit formula (5.1) at one point versus the line form
                let xi = omega.pow(1 << j);
                let a = w[1];
                let b = w[1 + w.len() / 2];
                let two_xi = xi.double();
                let expl = (((rs[j].double() - Fp2::ONE) * xi + (Fp2::ONE - rs[j])) * a
                    + ((rs[j].double() - Fp2::ONE) * xi - (Fp2::ONE - rs[j])) * b)
                    * two_xi.inv();
                w = fold_word(&w, rs[j], &inv_x0, j, inv2);
                assert_eq!(w[1], expl, "explicit formula");
                q = pfold(&q, rs[j]);
                // Proposition 5.4: folded word = evaluations of folded polynomial
                let om_j = omega.pow(1 << (j + 1));
                for (i, &x) in w.iter().enumerate() {
                    assert_eq!(x, horner(&q, Fp2::from(om_j.pow(i as u64))));
                }
                // Lemma 5.5: [X^b] pfold^(j) = sum_t phi_t(r) [X^{2^j b + t}] U
                let jj = j + 1;
                for (bi, &qb) in q.iter().enumerate() {
                    let mut s = Fp2::ZERO;
                    for t in 0..1usize << jj {
                        let mut ph = Fp2::ONE;
                        for k in 0..jj {
                            ph = ph
                                * if t >> k & 1 == 0 {
                                    rs[k].double() - Fp2::ONE
                                } else {
                                    Fp2::ONE - rs[k]
                                };
                        }
                        s = s + ph * u[(bi << jj) + t];
                    }
                    assert_eq!(s, qb, "iterated fold");
                }
            }
        }
    }
}
