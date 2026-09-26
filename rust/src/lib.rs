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
//!   `notes/inner-product`).

#![allow(clippy::needless_range_loop)] // index loops mirror the formulas of the paper

pub mod field;
pub mod ip;
pub mod merkle;
pub mod pcs;
pub mod poly;
