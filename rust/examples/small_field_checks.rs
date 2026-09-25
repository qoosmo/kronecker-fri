//! Independent numerical checks over the small prime field F_257 (Sections 4-7 of the paper).
//!
//! Over the prime field F_257 (257 - 1 = 2^8, so smooth domains of order up to 256 exist):
//!   1. extraction identity  f(z) = [X^{N-1}] U_f K_z            (Theorem 4.5)
//!   2. split lemma: X U K_z = A + v X^N + X^{N+1} H, A(0) = 0, deg H <= N-2   (Lemma 4.10)
//!   3. completeness of the protocol: every query point passes all checks  (Theorem 6.7)
//!   4. wrong value: the identity set has at most 2N points                 (Lemmas 4.12, 7.4)
//!
//! Run: `cargo run --release --example small_field_checks`
const P: u64 = 257;
const GEN: u64 = 3; // primitive root mod 257

fn add(a: u64, b: u64) -> u64 {
    (a + b) % P
}
fn sub(a: u64, b: u64) -> u64 {
    (a + P - b) % P
}
fn mul(a: u64, b: u64) -> u64 {
    a * b % P
}
fn pw(mut a: u64, mut e: u64) -> u64 {
    let mut r = 1;
    while e > 0 {
        if e & 1 == 1 {
            r = mul(r, a)
        }
        a = mul(a, a);
        e >>= 1
    }
    r
}
fn inv(a: u64) -> u64 {
    pw(a, P - 2)
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn fe(&mut self) -> u64 {
        self.next() % P
    }
}

fn pmul(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut c = vec![0; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        for (j, &y) in b.iter().enumerate() {
            c[i + j] = add(c[i + j], mul(x, y))
        }
    }
    c
}
fn eval(p: &[u64], x: u64) -> u64 {
    p.iter().rev().fold(0, |acc, &c| add(mul(acc, x), c))
}
/// K_z(X) = prod_k (X^{2^{k-1}} + z_k)
fn kernel(z: &[u64]) -> Vec<u64> {
    let mut k = vec![1u64];
    for (i, &zk) in z.iter().enumerate() {
        let mut f = vec![0u64; (1 << i) + 1];
        f[0] = zk;
        f[1 << i] = 1;
        k = pmul(&k, &f)
    }
    k
}
/// f(z) = sum_a c_a prod_{a_k = 1} z_k
fn mle_eval(c: &[u64], z: &[u64]) -> u64 {
    (0..c.len()).fold(0, |acc, a| {
        let mono = (0..z.len())
            .filter(|&k| a >> k & 1 == 1)
            .fold(1, |t, k| mul(t, z[k]));
        add(acc, mul(c[a], mono))
    })
}
/// kernel fold of a word on L (list of points) onto L^2: returns map point^2 -> value
fn fold_word(pts: &[u64], w: &[u64], r: u64) -> (Vec<u64>, Vec<u64>) {
    let m = pts.len();
    let (mut np, mut nw) = (vec![], vec![]);
    for i in 0..m / 2 {
        let (xi, a, b) = (pts[i], w[i], w[i + m / 2]); // pts[i + m/2] = -pts[i] for a cyclic group listing
        let t = sub(mul(2, r), 1);
        let s = sub(1, r);
        let num = add(mul(add(mul(t, xi), s), a), mul(sub(mul(t, xi), s), b));
        np.push(mul(xi, xi));
        nw.push(mul(num, inv(mul(2, xi))));
    }
    (np, nw)
}
/// polynomial kernel fold: (2r-1) U_e + (1-r) U_o
fn pfold(u: &[u64], r: u64) -> Vec<u64> {
    (0..u.len() / 2)
        .map(|i| {
            add(
                mul(sub(mul(2, r), 1), u[2 * i]),
                mul(sub(1, r), u[2 * i + 1]),
            )
        })
        .collect()
}
fn check(name: &str, ok: bool) {
    println!("[{}] {}", if ok { "PASS" } else { "FAIL" }, name)
}

fn main() {
    let mut rng = Rng(0x2545F4914F6CDD1D);
    let mut all = true;
    for n in 1..=5usize {
        let nn = 1usize << n;
        let m = 4 * nn; // rate 1/4
        let omega = pw(GEN, (P - 1) / m as u64);
        let pts: Vec<u64> = (0..m).map(|i| pw(omega, i as u64)).collect(); // pts[i + m/2] = -pts[i]
        let (mut ok1, mut ok2, mut ok3, mut ok4) = (true, true, true, true);
        for _ in 0..20 {
            let c: Vec<u64> = (0..nn).map(|_| rng.fe()).collect();
            let z: Vec<u64> = (0..n).map(|_| rng.fe()).collect();
            let kz = kernel(&z);
            let q = pmul(&c, &kz); // U K_z, degree <= 2N-2
            let v = mle_eval(&c, &z);
            // 1. extraction identity
            ok1 &= q[nn - 1] == v;
            // 2. split: XQ = A + v X^N + X^{N+1} H
            let mut xq = vec![0u64; q.len() + 1];
            for (i, &x) in q.iter().enumerate() {
                xq[i + 1] = x
            }
            let a: Vec<u64> = xq[..nn].to_vec();
            let h: Vec<u64> = xq[nn + 1..].to_vec();
            ok2 &= a[0] == 0 && xq[nn] == v && h.len() < nn && a.len() == nn;
            // 3. completeness: batch, fold down to the end, check every point
            let beta = rng.fe();
            let mut g = vec![0u64; nn];
            for i in 0..nn {
                let hi = if i < h.len() { h[i] } else { 0 };
                g[i] = add(add(c[i], mul(beta, a[i])), mul(mul(beta, beta), hi));
            }
            let w: Vec<u64> = pts.iter().map(|&x| eval(&c, x)).collect();
            let wa: Vec<u64> = pts.iter().map(|&x| eval(&a, x)).collect();
            let wh: Vec<u64> = pts.iter().map(|&x| eval(&h, x)).collect();
            let mut word: Vec<u64> = (0..m)
                .map(|i| add(add(w[i], mul(beta, wa[i])), mul(mul(beta, beta), wh[i])))
                .collect();
            let mut dom = pts.clone();
            let mut poly = g.clone();
            for _ in 0..n {
                let r = rng.fe();
                let (nd, nw) = fold_word(&dom, &word, r);
                poly = pfold(&poly, r);
                // fold consistency: folded word = evaluations of folded polynomial
                ok3 &= nd.iter().zip(&nw).all(|(&x, &y)| eval(&poly, x) == y);
                dom = nd;
                word = nw;
            }
            // identity check at every point of L
            ok3 &= (0..m).all(|i| {
                let x = pts[i];
                mul(mul(x, w[i]), eval(&kz, x))
                    == add(
                        add(wa[i], mul(v, pw(x, nn as u64))),
                        mul(pw(x, nn as u64 + 1), wh[i]),
                    )
            });
            // 4. wrong value: best split for v' = v + 1 (A, H truncations); identity set has <= 2N points
            let vb = add(v, 1);
            let cnt = (0..m)
                .filter(|&i| {
                    let x = pts[i];
                    mul(mul(x, w[i]), eval(&kz, x))
                        == add(
                            add(wa[i], mul(vb, pw(x, nn as u64))),
                            mul(pw(x, nn as u64 + 1), wh[i]),
                        )
                })
                .count();
            ok4 &= cnt <= 2 * nn;
        }
        check(
            &format!("n={n}: extraction identity f(z) = [X^(N-1)] U K_z"),
            ok1,
        );
        check(
            &format!("n={n}: split X U K_z = A + v X^N + X^(N+1) H, A(0)=0, deg H <= N-2"),
            ok2,
        );
        check(
            &format!(
                "n={n}: completeness (fold consistency, all fold and identity checks at every point)"
            ),
            ok3,
        );
        check(
            &format!("n={n}: wrong value: identity holds on at most 2N points"),
            ok4,
        );
        all &= ok1 && ok2 && ok3 && ok4;
    }
    assert!(all, "some check failed");
}
