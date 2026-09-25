//! Exact evaluation of the post-quantum bound (Theorem 3.15 of the paper, from CDHZ25)
//! for the parameters of Remark 8.8 of the Kronecker-FRI paper.
//!
//! Parameters: rho = 1/4, delta = 3/8, M <= 2^32 (n + R <= 32), quartic Goldilocks extension,
//! kappa = 248 queries, 320-bit challenges, 256-bit hashes, Q = 2^64 oracle queries.
//! Rounds nu = l + 2 <= 32; symbols are fibres, so the longest string has l_max = M/2 symbols;
//! q_s <= 2^30, q_V <= 2^36, q_CR <= 2^36.
//!
//! Run: `cargo run --release --example pq_params`
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive};

fn big(x: u128) -> BigInt {
    BigInt::from(x)
}
fn pow2(e: u32) -> BigInt {
    BigInt::one() << e
}
fn q(n: BigInt, d: BigInt) -> BigRational {
    BigRational::new(n, d)
}
fn log2(x: &BigRational) -> f64 {
    let bits = |b: &BigInt| {
        let s = b.bits() as i64;
        let sh = (s - 60).max(0);
        ((b >> sh).to_f64().unwrap()).log2() + sh as f64
    };
    bits(x.numer()) - bits(x.denom())
}

fn main() {
    let p: u128 = (1u128 << 64) - (1u128 << 32) + 1;
    let f = big(p).pow(4u32); // |F|
    let t = pow2(64); // Q
    let lam_h = 256u32; // hash output length
    let m_log = 32u32; // M = 2^32
    let kappa = 248u32;
    let lam_ch = 320u32; // challenge bits for beta and r_j
    let nu = big(32); // l + 2 rounds
    let lmax = pow2(m_log - 1); // M/2
    let lmax_log = m_log - 1; // ceil(log2 l_max)
    let (qv, qc, qs) = (pow2(36), pow2(36), pow2(30));
    let lam_min = lam_ch.min(kappa * m_log);
    let one = BigInt::one();
    let h = pow2(lam_h);

    // relaxed RBR errors: round 1 (batching) dominates the field terms
    let eps_1 = q(pow2(m_log + 1), one.clone())
        * (q(one.clone(), f.clone()) + q(one.clone(), pow2(lam_ch)));
    let eps_q = q(big(5).pow(kappa), big(8).pow(kappa));
    let e_rr = if eps_1 > eps_q {
        eps_1.clone()
    } else {
        eps_q.clone()
    };

    let a = q(big(320) * (&t + &nu + 1) * (&t + &nu), one.clone()) * &e_rr
        + q(big(4) * (&t + &nu + 1) * &nu, pow2(lam_min));
    let b = q(big(32) * &lmax, h.clone());
    let c = q(
        big(1280) * &t * (big(2) * &t + big(1)).pow(2u32) + big(128) * &qs * big(lmax_log as u128),
        h.clone(),
    );
    let t1: BigInt = &t + 1 + &qv + &nu + &qc;
    let d = q(big(960) * (&t + 1) * t1.pow(2u32), h.clone());
    let e = q(big(480) * qv.pow(2u32) * (&t + &nu + &qv + 2), h.clone());
    let tot = &a + &b + &c + &d + &e;
    for (name, x) in [
        ("eps_1 (batching)", &eps_1),
        ("(5/8)^kappa", &eps_q),
        ("sr term", &a),
        ("extract", &b),
        ("offline", &c),
        ("online", &d),
        ("com", &e),
        ("total", &tot),
    ] {
        println!("{name:18} 2^{:.2}", log2(x));
    }
    assert!(log2(&tot) < -31.8, "bound not met");
    // iota^4 - 7 is irreducible over F_p: 7 is a non-square (Euler) and p = 1 mod 4 (LN97, Thm 3.75)
    let mut r: u128 = 1;
    let (mut b, mut e) = (7u128, (p - 1) / 2);
    while e > 0 {
        if e & 1 == 1 {
            r = r * b % p
        }
        b = b * b % p;
        e >>= 1
    }
    assert!(r == p - 1 && p % 4 == 1, "iota^4 - 7 not irreducible");
    println!("PASS: 7 is a non-square mod p and p = 1 mod 4");
    println!("PASS: eps_ext(2^64) < 2^-31.8");
}
