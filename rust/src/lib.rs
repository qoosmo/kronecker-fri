//! Kronecker-FRI: a hash-based multilinear polynomial commitment from the coefficient-extraction
//! identity f(z) = [X^{N-1}] U_f(X) K_z(X).
//!
//! Reference implementation of the paper
//! <https://github.com/qoosmo/kronecker-fri/blob/main/paper/kronecker-fri.pdf>.
//!
//! ```
//! use kronecker_fri::field::{Fp, Fp2};
//! use kronecker_fri::pcs::{Params, commit_table, open, verify};
//!
//! // n = 10 variables; rate 1/4, arity 8, Merkle caps, 148 queries, 32-byte salts
//! let p = Params::recommended(10, 148, 32);
//! let table: Vec<Fp> = (0..1u64 << 10).map(Fp::new).collect(); // f on {0,1}^10
//! let z: Vec<Fp2> = (0..10u64).map(|i| Fp2(Fp::new(3 + i), Fp::new(7 * i))).collect();
//! // The seeds derive the Merkle salts: use fresh, secret randomness for every call.
//! let (root, pd) = commit_table(&p, &table, &[0x11; 32]);
//! let (v, proof) = open(&p, &pd, &z, &[0x22; 32]); // v = f(z)
//! assert!(verify(&p, &root, &z, v, &proof).is_ok());
//! ```
//!
//! The modules `field`, `poly`, `merkle` and `pcs` implement the paper and form the stable API.
//! The other public modules are research prototypes of the note
//! <https://github.com/qoosmo/kronecker-fri/blob/main/notes/inner-product/note.pdf>; their API may
//! change between versions. Feature `parallel`: multithreaded prover, identical proofs.
//!
//! Module map:
//! - `field`: Goldilocks F_p and the extensions F_{p^2}, F_{p^4} (Sections 6.1, 8.4);
//! - `poly`: Moebius transform, NTT, kernel polynomial and product, opening polynomials, folds
//!   (Sections 2, 4, 5);
//! - `merkle`: salted Merkle trees and the Fiat-Shamir transcript (Sections 3.4, 8.1);
//! - `pcs`: commitment, prover and verifier of Pi_KF (Section 6);
//! - `ip`: prototype of the sumcheck-free inner-product protocol Pi_IP (research note
//!   `notes/inner-product`, Section 2);
//! - `had`: prototype of the sumcheck-free Hadamard check Pi_Had (same note, Section 3);
//! - `affine`: Pi_Batch on affine forms of committed and public tables (same note, Prop. 5.1);
//! - `batch`: prototype of Pi_Batch, any list of evaluations, inner products and Hadamard checks
//!   in one folding test (same note, Section 4);
//! - `lincheck`: clear-text check of the sumcheck-free lincheck reduction (same note, Section 5);
//! - `r1cs`: prototype of the sumcheck-free R1CS argument (same note, Section 5.3);
//! - `spartan`: baseline, the core of a Spartan-style R1CS argument (two sumchecks and one
//!   Pi_KF opening) on the same commitment, for the comparison of the same note, Section 5.3;
//! - `sumcheck`: baselines, one inner product and one Hadamard check by sumcheck, closed by a
//!   batched opening (same note, Section 6);
//! - `par` (internal): the optional multithreaded prover (feature `parallel`, rayon); proofs
//!   are identical with and without it;
//! - `ft`: the folding test on a batched word and level-0 coset openings, shared by `had` and
//!   `batch`.

#![forbid(unsafe_code)]
#![allow(clippy::needless_range_loop)] // index loops mirror the formulas of the paper

pub mod affine;
pub mod batch;
pub mod error;
pub mod field;
pub mod ft;
pub mod had;
pub mod ip;
pub mod lincheck;
pub mod merkle;
mod par;
pub mod pcs;
pub mod poly;
pub mod r1cs;
pub mod spartan;
pub mod sumcheck;
