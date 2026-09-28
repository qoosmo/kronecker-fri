//! Test vectors and transcript composition.
//!
//! The expected values are fixed: a change in any of them changes every proof of the crate, which
//! must come with a new domain label (`kronecker-fri/vX.Y/...`) and a CHANGELOG entry.

use kronecker_fri::field::{Field, Fp, Fp2, Fp4};
use kronecker_fri::merkle::Transcript;
use kronecker_fri::pcs::{Params, commit_table, open, open_in, verify, verify_in};

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

/// Transcript outputs for fixed inputs.
fn transcript_outputs() -> (Fp2, Fp4, Vec<usize>, String) {
    let mut tr = Transcript::new(b"kronecker-fri/v0.5/test-vector");
    tr.absorb(b"a", b"abc");
    tr.absorb(b"b", &[0u8; 40]);
    let c2: Fp2 = tr.challenge();
    let c4: Fp4 = tr.challenge_nonzero();
    let idx = tr.query_indices(6, 13);
    let bytes = hex(&tr.squeeze(16));
    (c2, c4, idx, bytes)
}

#[test]
fn transcript_vector() {
    let (c2, c4, idx, bytes) = transcript_outputs();
    let got = format!("{c2:?} {c4:?} {idx:?} {bytes}");
    let expected = include_str!("vectors/transcript.txt").trim();
    assert_eq!(got, expected);
}

/// The opening continues the caller's transcript: the proof depends on what the caller absorbed
/// before, and verifies only against a transcript in the same state.
#[test]
fn open_in_binds_the_callers_statement() {
    let n = 7;
    let p = Params::recommended(n, 16, 32);
    let table: Vec<Fp> = (0..1u64 << n).map(|i| Fp::new(3 * i + 1)).collect();
    let z: Vec<Fp2> = (0..n as u64)
        .map(|i| Fp2(Fp::new(i + 5), Fp::ONE))
        .collect();
    let (root, pd) = commit_table(&p, &table).unwrap();
    let outer = |stmt: &[u8]| {
        let mut tr = Transcript::new(b"kronobol/v1/test");
        tr.absorb(b"statement", stmt);
        tr
    };
    let mut tp = outer(b"statement 1");
    let (v, proof) = open_in(&p, &mut tp, &pd, &z).unwrap();
    assert_eq!(
        verify_in(&p, &mut outer(b"statement 1"), &root, &z, v, &proof),
        Ok(())
    );
    assert!(verify_in(&p, &mut outer(b"statement 2"), &root, &z, v, &proof).is_err());
    assert!(verify(&p, &root, &z, v, &proof).is_err());
    // prover and verifier transcripts end in the same state
    let mut tv = outer(b"statement 1");
    verify_in(&p, &mut tv, &root, &z, v, &proof).unwrap();
    assert_eq!(tp.squeeze(8), tv.squeeze(8));
    // and the plain API is unaffected
    let (v2, pr2) = open(&p, &pd, &z).unwrap();
    assert_eq!(v2, v);
    assert!(verify(&p, &root, &z, v2, &pr2).is_ok());
}

/// A seeded proof has a fixed digest (feature `insecure-test-vectors`).
#[cfg(feature = "insecure-test-vectors")]
#[test]
fn proof_vector() {
    use kronecker_fri::insecure;
    let n = 6;
    let p = Params::recommended(n, 20, 32);
    let table: Vec<Fp> = (0..1u64 << n).map(|i| Fp::new(i * 7 + 3)).collect();
    let z: Vec<Fp2> = (0..n as u64)
        .map(|k| Fp2(Fp::new(k + 2), Fp::new(9)))
        .collect();
    let (root, pd) = insecure::commit_table(&p, &table, &[1u8; 32]);
    let (v, proof) = insecure::open(&p, &pd, &z, &[2u8; 32]);
    assert!(verify(&p, &root, &z, v, &proof).is_ok());
    let mut h = blake3::Hasher::new();
    h.update(&root);
    let mut b = Vec::new();
    v.to_bytes(&mut b);
    for c in &proof.p {
        c.to_bytes(&mut b);
    }
    h.update(&b);
    for s in &proof.round_salts {
        h.update(s);
    }
    for c in proof.cap_a.iter().chain(proof.caps.iter().flatten()) {
        h.update(c);
    }
    let got = h.finalize().to_hex().to_string();
    let expected = include_str!("vectors/proof_n6.txt").trim();
    assert_eq!(got, expected);
}
