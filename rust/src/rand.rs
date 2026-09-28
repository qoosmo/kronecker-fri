//! The prover's randomness: seeds for the Merkle salts, drawn from the operating system.

use crate::error::Error;
use crate::merkle::Digest;

/// A fresh 32-byte seed from the operating system's secure random number generator.
pub(crate) fn fresh_seed() -> Result<Digest, Error> {
    let mut s = [0u8; 32];
    getrandom::fill(&mut s).map_err(|_| Error::Randomness)?;
    Ok(s)
}
