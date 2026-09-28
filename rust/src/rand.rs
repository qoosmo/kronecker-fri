//! The prover's randomness: seeds for the Merkle salts, drawn from the operating system.

use crate::error::Error;
use crate::merkle::Digest;

/// A fresh 32-byte seed from the operating system's secure random number generator.
pub(crate) fn fresh_seed() -> Result<Digest, Error> {
    let mut s = [0u8; 32];
    getrandom::fill(&mut s).map_err(|_| Error::Randomness)?;
    Ok(s)
}

/// A stream of uniform field elements derived from a seed and a label (keyed BLAKE3 XOF), by
/// rejection sampling: each element is exactly uniform in `F_p`.
pub(crate) struct FieldStream(blake3::OutputReader);

impl FieldStream {
    pub(crate) fn new(seed: &Digest, label: &[u8]) -> Self {
        let mut h = blake3::Hasher::new_keyed(seed);
        h.update(b"kronecker-fri/v0.5/field-stream");
        h.update(&(label.len() as u64).to_le_bytes());
        h.update(label);
        FieldStream(h.finalize_xof())
    }
    pub(crate) fn next_fp(&mut self) -> crate::field::Fp {
        loop {
            let mut b = [0u8; 8];
            self.0.fill(&mut b);
            let x = u64::from_le_bytes(b);
            if x < crate::field::P {
                return crate::field::Fp::new(x);
            }
        }
    }
    pub(crate) fn next_ext<E: crate::field::ExtField>(&mut self) -> E {
        let d: Vec<crate::field::Fp> = (0..E::DEGREE).map(|_| self.next_fp()).collect();
        E::from_digits(&d)
    }
}
