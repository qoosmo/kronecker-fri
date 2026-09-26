//! Kronecker-FRI: a hash-based multilinear polynomial commitment from the coefficient-extraction
//! identity f(z) = [X^{N-1}] U_f(X) K_z(X).
//!
//! Reference implementation of the paper in `paper/`. Module map:
//! - `field`: Goldilocks F_p and the extensions F_{p^2}, F_{p^4} (Sections 6.1, 8.4);
//! - `poly`: Moebius transform, NTT, kernel polynomial and product, opening polynomials, folds
//!   (Sections 2, 4, 5);
//! - `merkle`: salted Merkle trees and the Fiat-Shamir transcript (Sections 3.4, 8.1);
//! - `pcs`: commitment, prover and verifier of Pi_KF (Section 6);
//! - `ip`: prototype of the sumcheck-free inner-product protocol Pi_IP (research note
//!   `notes/inner-product`, Section 2);
//! - `had`: prototype of the sumcheck-free Hadamard check Pi_Had (same note, Section 3);
//! - `ft`: the folding test on a batched word and level-0 coset openings, shared by `had`.

#![allow(clippy::needless_range_loop)] // index loops mirror the formulas of the paper

pub mod field;
pub mod ft;
pub mod had;
pub mod ip;
pub mod merkle;
pub mod pcs;
pub mod poly;
