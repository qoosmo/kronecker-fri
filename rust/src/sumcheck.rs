//! Baselines for the research note (`notes/inner-product`, Section 6): one inner product and one
//! Hadamard check on committed tables, by two routes that share the same commitments (one group
//! per table, `affine::commit_group`) and the same proof engine (`affine::prove_affine`):
//!
//! - the sumcheck route: a sumcheck (degree 2 for the inner product; for the Hadamard check the
//!   zerocheck sum_x eq(tau, x) (a(x) b(x) - c(x)) = 0 of degree 3) reduces the statement to the
//!   values of the tables at one point r; a random combination rho turns them into ONE evaluation
//!   statement on the affine form sum_i rho^i w_i (a batched opening at one point);
//! - the sumcheck-free route: the statement IP(a, b, S) or Had(a, b, c) itself.
//!
//! Only the reduction differs, so the comparison isolates the cost of the sumcheck-free
//! statements against a sumcheck followed by one opening.

use crate::affine::{
    AStmt, AffineProof, Form, GData, GroupData, OId, Shape, prove_affine, verify_affine,
};
use crate::field::{ExtField, Field, Fp};
use crate::merkle::{Digest, Transcript};
use crate::pcs::Params;
use crate::spartan::{absorb_es, eq_point, eq_table, fold, interpolate};

/// A proof of either route.
pub struct RouteProof<E> {
    /// sumcheck route: the round polynomials by their values at 0, 1, ..., d (empty otherwise)
    pub rounds: Vec<Vec<E>>,
    /// sumcheck route: the values of the tables at the sumcheck point (empty otherwise)
    pub evals: Vec<E>,
    pub engine: AffineProof<E>,
}

impl<E: ExtField> RouteProof<E> {
    /// Size in bytes (the group roots are the commitments, known to the verifier).
    pub fn size_bytes(&self) -> usize {
        let e = 8 * E::DEGREE;
        e * (self.rounds.iter().map(|r| r.len()).sum::<usize>() + self.evals.len())
            + self.engine.size_bytes(false)
    }
}

fn word(g: usize) -> OId {
    OId { group: g, word: 0 }
}

fn init(label: &[u8], roots: &[Digest]) -> Transcript {
    let mut tr = Transcript::new(label);
    for r in roots {
        tr.absorb(b"root", r);
    }
    tr
}

fn lift<E: ExtField>(t: &[Fp]) -> Vec<E> {
    t.iter().map(|&x| E::from(x)).collect()
}

/// Commit to a table in table form, as a group of one word.
pub fn commit_one(p: &Params, table: &[Fp], seed: &Digest) -> GroupData<Fp> {
    crate::affine::commit_group(p, vec![table.to_vec()], seed, b"route")
}

fn shapes(k: usize) -> Vec<Shape> {
    vec![
        Shape {
            base: true,
            words: 1
        };
        k
    ]
}

/// The batched opening of the sumcheck route: one evaluation of sum_i rho^i w_i at r.
fn eval_stmt<E: ExtField>(tr: &mut Transcript, r: &[E], evals: &[E]) -> AStmt<E> {
    absorb_es(tr, b"evals", evals);
    let rho: E = tr.challenge();
    let mut c = E::ONE;
    let mut com = Vec::new();
    let mut v = E::ZERO;
    for (g, &e) in evals.iter().enumerate() {
        com.push((word(g), c));
        v = v + c * e;
        c = c * rho;
    }
    AStmt::Eval(Form { com, pubs: vec![] }, r.to_vec(), v)
}

fn replay<E: ExtField>(
    tr: &mut Transcript,
    rounds: &[Vec<E>],
    d: usize,
    mut claim: E,
) -> Result<(Vec<E>, E), &'static str> {
    let mut r = Vec::with_capacity(rounds.len());
    for v in rounds {
        if v.len() != d + 1 {
            return Err("round shape");
        }
        if v[0] + v[1] != claim {
            return Err("sumcheck round");
        }
        absorb_es(tr, b"round", v);
        let ri: E = tr.challenge();
        claim = interpolate(v, ri);
        r.push(ri);
    }
    Ok((r, claim))
}

/// Inner product by sumcheck: returns S = sum_x a(x) b(x) and the proof.
pub fn prove_ip_sc<E: ExtField>(
    p: &Params,
    g: [&GroupData<Fp>; 2],
    seed: &Digest,
) -> (E, RouteProof<E>) {
    let (ta, tb) = (&g[0].coeffs[0], &g[1].coeffs[0]);
    let s = E::from(
        ta.iter()
            .zip(tb)
            .fold(Fp::ZERO, |acc, (&x, &y)| acc + x * y),
    );
    let roots = [g[0].tree.root(), g[1].tree.root()];
    let mut tr = init(b"ip-sumcheck-v2", &roots);
    absorb_es(&mut tr, b"s", &[s]);
    let (mut a, mut b) = (lift::<E>(ta), lift::<E>(tb));
    let mut rounds = Vec::with_capacity(p.n);
    let mut r = Vec::with_capacity(p.n);
    for _ in 0..p.n {
        let mut v = [E::ZERO; 3];
        for i in 0..a.len() / 2 {
            let (a0, a1, b0, b1) = (a[2 * i], a[2 * i + 1], b[2 * i], b[2 * i + 1]);
            v[0] = v[0] + a0 * b0;
            v[1] = v[1] + a1 * b1;
            v[2] = v[2] + (a1 + a1 - a0) * (b1 + b1 - b0);
        }
        absorb_es(&mut tr, b"round", &v);
        let ri: E = tr.challenge();
        rounds.push(v.to_vec());
        r.push(ri);
        a = fold(&a, ri);
        b = fold(&b, ri);
    }
    let evals = vec![a[0], b[0]];
    let st = eval_stmt(&mut tr, &r, &evals);
    let engine = prove_affine(
        p,
        &mut tr,
        seed,
        1,
        &[GData::Base(g[0]), GData::Base(g[1])],
        &[st],
    );
    (
        s,
        RouteProof {
            rounds,
            evals,
            engine,
        },
    )
}

pub fn verify_ip_sc<E: ExtField>(
    p: &Params,
    roots: [Digest; 2],
    s: E,
    pf: &RouteProof<E>,
) -> Result<(), &'static str> {
    if pf.rounds.len() != p.n || pf.evals.len() != 2 {
        return Err("shape");
    }
    let mut tr = init(b"ip-sumcheck-v2", &roots);
    absorb_es(&mut tr, b"s", &[s]);
    let (r, claim) = replay(&mut tr, &pf.rounds, 2, s)?;
    if claim != pf.evals[0] * pf.evals[1] {
        return Err("final");
    }
    let st = eval_stmt(&mut tr, &r, &pf.evals);
    verify_affine(p, &mut tr, &roots, &shapes(2), &[st], &pf.engine)
}

/// Hadamard check a o b = c by zerocheck.
pub fn prove_had_sc<E: ExtField>(
    p: &Params,
    g: [&GroupData<Fp>; 3],
    seed: &Digest,
) -> RouteProof<E> {
    let roots = [g[0].tree.root(), g[1].tree.root(), g[2].tree.root()];
    let mut tr = init(b"had-zerocheck-v2", &roots);
    let tau: Vec<E> = (0..p.n).map(|_| tr.challenge()).collect();
    let mut eq = eq_table(&tau);
    let (mut a, mut b, mut c) = (
        lift::<E>(&g[0].coeffs[0]),
        lift::<E>(&g[1].coeffs[0]),
        lift::<E>(&g[2].coeffs[0]),
    );
    let mut rounds = Vec::with_capacity(p.n);
    let mut r = Vec::with_capacity(p.n);
    for _ in 0..p.n {
        let mut v = [E::ZERO; 4];
        for i in 0..a.len() / 2 {
            let (e0, a0, b0, c0) = (eq[2 * i], a[2 * i], b[2 * i], c[2 * i]);
            let (de, da, db, dc) = (
                eq[2 * i + 1] - e0,
                a[2 * i + 1] - a0,
                b[2 * i + 1] - b0,
                c[2 * i + 1] - c0,
            );
            let (mut et, mut at, mut bt, mut ct) = (e0, a0, b0, c0);
            for t in 0..4 {
                if t > 0 {
                    et = et + de;
                    at = at + da;
                    bt = bt + db;
                    ct = ct + dc;
                }
                v[t] = v[t] + et * (at * bt - ct);
            }
        }
        absorb_es(&mut tr, b"round", &v);
        let ri: E = tr.challenge();
        rounds.push(v.to_vec());
        r.push(ri);
        eq = fold(&eq, ri);
        a = fold(&a, ri);
        b = fold(&b, ri);
        c = fold(&c, ri);
    }
    let evals = vec![a[0], b[0], c[0]];
    let st = eval_stmt(&mut tr, &r, &evals);
    let gd = [GData::Base(g[0]), GData::Base(g[1]), GData::Base(g[2])];
    let engine = prove_affine(p, &mut tr, seed, 1, &gd, &[st]);
    RouteProof {
        rounds,
        evals,
        engine,
    }
}

pub fn verify_had_sc<E: ExtField>(
    p: &Params,
    roots: [Digest; 3],
    pf: &RouteProof<E>,
) -> Result<(), &'static str> {
    if pf.rounds.len() != p.n || pf.evals.len() != 3 {
        return Err("shape");
    }
    let mut tr = init(b"had-zerocheck-v2", &roots);
    let tau: Vec<E> = (0..p.n).map(|_| tr.challenge()).collect();
    let (r, claim) = replay(&mut tr, &pf.rounds, 3, E::ZERO)?;
    if claim != eq_point(&tau, &r) * (pf.evals[0] * pf.evals[1] - pf.evals[2]) {
        return Err("final");
    }
    let st = eval_stmt(&mut tr, &r, &pf.evals);
    verify_affine(p, &mut tr, &roots, &shapes(3), &[st], &pf.engine)
}

/// The sumcheck-free route on the same commitments and engine: IP(a, b, S).
pub fn prove_ip_sf<E: ExtField>(
    p: &Params,
    g: [&GroupData<Fp>; 2],
    seed: &Digest,
) -> (E, RouteProof<E>) {
    let (ta, tb) = (&g[0].coeffs[0], &g[1].coeffs[0]);
    let s = E::from(
        ta.iter()
            .zip(tb)
            .fold(Fp::ZERO, |acc, (&x, &y)| acc + x * y),
    );
    let roots = [g[0].tree.root(), g[1].tree.root()];
    let mut tr = init(b"ip-free-v2", &roots);
    absorb_es(&mut tr, b"s", &[s]);
    let st = AStmt::Ip(Form::word(word(0)), Form::word(word(1)), s);
    let engine = prove_affine(
        p,
        &mut tr,
        seed,
        1,
        &[GData::Base(g[0]), GData::Base(g[1])],
        &[st],
    );
    (
        s,
        RouteProof {
            rounds: vec![],
            evals: vec![],
            engine,
        },
    )
}

pub fn verify_ip_sf<E: ExtField>(
    p: &Params,
    roots: [Digest; 2],
    s: E,
    pf: &RouteProof<E>,
) -> Result<(), &'static str> {
    let mut tr = init(b"ip-free-v2", &roots);
    absorb_es(&mut tr, b"s", &[s]);
    let st = AStmt::Ip(Form::word(word(0)), Form::word(word(1)), s);
    verify_affine(p, &mut tr, &roots, &shapes(2), &[st], &pf.engine)
}

/// The sumcheck-free route on the same commitments and engine: Had(a, b, c).
pub fn prove_had_sf<E: ExtField>(
    p: &Params,
    g: [&GroupData<Fp>; 3],
    seed: &Digest,
) -> RouteProof<E> {
    let roots = [g[0].tree.root(), g[1].tree.root(), g[2].tree.root()];
    let mut tr = init(b"had-free-v2", &roots);
    let st = AStmt::Had(
        Form::word(word(0)),
        Form::word(word(1)),
        Form::word(word(2)),
    );
    let gd = [GData::Base(g[0]), GData::Base(g[1]), GData::Base(g[2])];
    let engine = prove_affine(p, &mut tr, seed, 1, &gd, &[st]);
    RouteProof {
        rounds: vec![],
        evals: vec![],
        engine,
    }
}

pub fn verify_had_sf<E: ExtField>(
    p: &Params,
    roots: [Digest; 3],
    pf: &RouteProof<E>,
) -> Result<(), &'static str> {
    let mut tr = init(b"had-free-v2", &roots);
    let st = AStmt::Had(
        Form::word(word(0)),
        Form::word(word(1)),
        Form::word(word(2)),
    );
    verify_affine(p, &mut tr, &roots, &shapes(3), &[st], &pf.engine)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{Fp2, Fp4};

    fn tables(n: usize, seed: u64) -> (Vec<Fp>, Vec<Fp>) {
        let mut s = seed | 1;
        let mut next = || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            Fp::new(s)
        };
        let a = (0..1 << n).map(|_| next()).collect();
        let b = (0..1 << n).map(|_| next()).collect();
        (a, b)
    }

    fn run<E: ExtField>() {
        for n in [3, 5, 7] {
            let p = Params::recommended(n, 20, 16);
            let (a, b) = tables(n, 3 + n as u64);
            let c: Vec<Fp> = a.iter().zip(&b).map(|(&x, &y)| x * y).collect();
            let mut c2 = c.clone();
            c2[1] = c2[1] + Fp::ONE;
            let ga = commit_one(&p, &a, &[1u8; 32]);
            let gb = commit_one(&p, &b, &[2u8; 32]);
            let gc = commit_one(&p, &c, &[3u8; 32]);
            let gc2 = commit_one(&p, &c2, &[4u8; 32]);
            let (ra, rb, rc, rc2) = (
                ga.tree.root(),
                gb.tree.root(),
                gc.tree.root(),
                gc2.tree.root(),
            );
            // inner product, both routes
            let (s, pf) = prove_ip_sc::<E>(&p, [&ga, &gb], &[5u8; 32]);
            assert_eq!(verify_ip_sc(&p, [ra, rb], s, &pf), Ok(()));
            assert!(verify_ip_sc(&p, [ra, rb], s + E::ONE, &pf).is_err());
            let (s, mut pf) = prove_ip_sc::<E>(&p, [&ga, &gb], &[6u8; 32]);
            pf.evals[1] = pf.evals[1] + E::ONE;
            assert!(verify_ip_sc(&p, [ra, rb], s, &pf).is_err());
            let (s, pf) = prove_ip_sf::<E>(&p, [&ga, &gb], &[7u8; 32]);
            assert_eq!(verify_ip_sf(&p, [ra, rb], s, &pf), Ok(()));
            assert!(verify_ip_sf(&p, [ra, rb], s + E::ONE, &pf).is_err());
            // Hadamard check, both routes
            let pf = prove_had_sc::<E>(&p, [&ga, &gb, &gc], &[8u8; 32]);
            assert_eq!(verify_had_sc(&p, [ra, rb, rc], &pf), Ok(()));
            let pf = prove_had_sc::<E>(&p, [&ga, &gb, &gc2], &[9u8; 32]);
            assert!(verify_had_sc(&p, [ra, rb, rc2], &pf).is_err());
            let mut pf = prove_had_sc::<E>(&p, [&ga, &gb, &gc], &[10u8; 32]);
            pf.evals[2] = pf.evals[2] + E::ONE;
            assert_eq!(verify_had_sc(&p, [ra, rb, rc], &pf), Err("final"));
            let pf = prove_had_sf::<E>(&p, [&ga, &gb, &gc], &[11u8; 32]);
            assert_eq!(verify_had_sf(&p, [ra, rb, rc], &pf), Ok(()));
            let pf = prove_had_sf::<E>(&p, [&ga, &gb, &gc2], &[12u8; 32]);
            assert!(verify_had_sf(&p, [ra, rb, rc2], &pf).is_err());
        }
    }

    #[test]
    fn routes_fp2() {
        run::<Fp2>();
    }

    #[test]
    fn routes_fp4() {
        run::<Fp4>();
    }
}
