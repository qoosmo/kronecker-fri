//! Salted BLAKE3 Merkle trees (Section 3.4, "Salted Merkle commitments") and the Fiat-Shamir
//! transcript with the challenge maps phi and pos of Section 8.1.
//!
//! Leaves are H(0x00 || data || salt), internal nodes H(0x01 || left || right).  With
//! `salt_len = 0` the trees are unsalted (used only to measure the cost of salting).

use crate::field::{ExtField, Fp, P};

pub type Digest = [u8; 32];

fn hash_leaf(data: &[u8], salt: &[u8]) -> Digest {
    let mut h = blake3::Hasher::new();
    h.update(&[0u8]);
    h.update(data);
    h.update(salt);
    *h.finalize().as_bytes()
}

fn hash_node(l: &Digest, r: &Digest) -> Digest {
    let mut h = blake3::Hasher::new();
    h.update(&[1u8]);
    h.update(l);
    h.update(r);
    *h.finalize().as_bytes()
}

/// Deterministic salt stream from a prover seed (the seed must be fresh and secret for each tree).
fn salt(seed: &Digest, label: &[u8], index: usize, len: usize) -> Vec<u8> {
    if len == 0 {
        return Vec::new();
    }
    let mut h = blake3::Hasher::new_keyed(seed);
    h.update(label);
    h.update(&(index as u64).to_le_bytes());
    let mut out = vec![0u8; len];
    h.finalize_xof().fill(&mut out);
    out
}

/// A salted Merkle tree over T = 2^t leaves.  Salts are recomputed from the seed when a group
/// is opened, so that only the hash layers are stored.
pub struct MerkleTree {
    layers: Vec<Vec<Digest>>, // layers[0] = leaf hashes, last = [root]
    seed: Digest,
    label: Vec<u8>,
    salt_len: usize,
}

/// Opening of an aligned group of 2^g consecutive leaves: their data are sent by the caller;
/// `salts` are the leaf salts and `path` holds the siblings from level g to the root.
#[derive(Clone, Debug)]
pub struct GroupOpening {
    pub salts: Vec<Vec<u8>>,
    pub path: Vec<Digest>,
}

impl MerkleTree {
    /// Tree over `count` leaves; `leaf(i, buf)` writes the data of leaf i into `buf`.
    pub fn from_fn(
        count: usize,
        leaf: impl Fn(usize, &mut Vec<u8>),
        seed: &Digest,
        label: &[u8],
        salt_len: usize,
    ) -> Self {
        assert!(count.is_power_of_two());
        let mut buf = Vec::with_capacity(64);
        let hashes: Vec<Digest> = (0..count)
            .map(|i| {
                buf.clear();
                leaf(i, &mut buf);
                hash_leaf(&buf, &salt(seed, label, i, salt_len))
            })
            .collect();
        let mut layers = vec![hashes];
        while layers.last().unwrap().len() > 1 {
            let prev = layers.last().unwrap();
            let next: Vec<Digest> = prev
                .as_chunks::<2>()
                .0
                .iter()
                .map(|[l, r]| hash_node(l, r))
                .collect();
            layers.push(next);
        }
        MerkleTree {
            layers,
            seed: *seed,
            label: label.to_vec(),
            salt_len,
        }
    }
    pub fn new(leaves: &[Vec<u8>], seed: &Digest, label: &[u8], salt_len: usize) -> Self {
        Self::from_fn(
            leaves.len(),
            |i, b| b.extend_from_slice(&leaves[i]),
            seed,
            label,
            salt_len,
        )
    }
    pub fn root(&self) -> Digest {
        self.layers.last().unwrap()[0]
    }
    /// Open the aligned group of 2^g leaves containing leaf `i`.
    pub fn open_group(&self, i: usize, g: usize) -> GroupOpening {
        let start = (i >> g) << g;
        let salts = (start..start + (1 << g))
            .map(|h| salt(&self.seed, &self.label, h, self.salt_len))
            .collect();
        let mut path = Vec::new();
        let mut idx = i >> g;
        for layer in &self.layers[g..self.layers.len() - 1] {
            path.push(layer[idx ^ 1]);
            idx >>= 1;
        }
        GroupOpening { salts, path }
    }
}

/// Check the opening of the aligned group of 2^g leaves containing leaf `i`, with leaf data `data`.
pub fn verify_group(
    root: &Digest,
    i: usize,
    g: usize,
    data: &[Vec<u8>],
    op: &GroupOpening,
) -> bool {
    if data.len() != 1 << g || op.salts.len() != 1 << g {
        return false;
    }
    let mut level: Vec<Digest> = data
        .iter()
        .zip(&op.salts)
        .map(|(d, s)| hash_leaf(d, s))
        .collect();
    while level.len() > 1 {
        level = level
            .as_chunks::<2>()
            .0
            .iter()
            .map(|[l, r]| hash_node(l, r))
            .collect();
    }
    let mut cur = level[0];
    let mut idx = i >> g;
    for sib in &op.path {
        cur = if idx & 1 == 0 {
            hash_node(&cur, sib)
        } else {
            hash_node(sib, &cur)
        };
        idx >>= 1;
    }
    idx == 0 && &cur == root
}

/// Hash-chain transcript: state_{k+1} = H(state_k || tag || len || data); outputs are
/// H(state || "squeeze" || counter).
pub struct Transcript {
    state: Digest,
    counter: u64,
}

impl Transcript {
    pub fn new(label: &[u8]) -> Self {
        Transcript {
            state: *blake3::hash(label).as_bytes(),
            counter: 0,
        }
    }
    pub fn absorb(&mut self, tag: &[u8], data: &[u8]) {
        let mut h = blake3::Hasher::new();
        h.update(&self.state);
        h.update(tag);
        h.update(&(data.len() as u64).to_le_bytes());
        h.update(data);
        self.state = *h.finalize().as_bytes();
        self.counter = 0;
    }
    /// `len` pseudorandom bytes.
    pub fn squeeze(&mut self, len: usize) -> Vec<u8> {
        let mut h = blake3::Hasher::new();
        h.update(&self.state);
        h.update(b"squeeze");
        h.update(&self.counter.to_le_bytes());
        self.counter += 1;
        let mut out = vec![0u8; len];
        h.finalize_xof().fill(&mut out);
        out
    }
    /// Challenge in F = F_{p^e} by the map phi of Section 8.1 from lambda_ch = 64 e + 64 bits:
    /// the integer int(vr) is reduced mod p^e, and its base-p digits are the coordinates.
    pub fn challenge<E: ExtField>(&mut self) -> E {
        let limbs = E::DEGREE + 1;
        let bytes = self.squeeze(8 * limbs);
        let mut x: Vec<u64> = bytes
            .as_chunks::<8>()
            .0
            .iter()
            .map(|c| u64::from_le_bytes(*c))
            .collect();
        let mut digits = Vec::with_capacity(E::DEGREE);
        for _ in 0..E::DEGREE {
            // x <- floor(x / p), digit = x mod p   (long division, most significant limb first)
            let mut rem: u128 = 0;
            for limb in x.iter_mut().rev() {
                let cur = (rem << 64) | *limb as u128;
                *limb = (cur / P as u128) as u64;
                rem = cur % P as u128;
            }
            digits.push(Fp(rem as u64));
        }
        E::from_digits(&digits)
    }
    /// kappa query indices in [0, 2^bits), from kappa * bits consecutive output bits (map pos).
    pub fn query_indices(&mut self, kappa: usize, bits: usize) -> Vec<usize> {
        let total = kappa * bits;
        let bytes = self.squeeze(total.div_ceil(8));
        (0..kappa)
            .map(|q| {
                let mut idx = 0usize;
                for b in 0..bits {
                    let pos = q * bits + b;
                    idx |= (((bytes[pos / 8] >> (pos % 8)) & 1) as usize) << b;
                }
                idx
            })
            .collect()
    }
}

/// Number of challenge bits used by `Transcript::challenge` for F_{p^e}.
pub fn lambda_ch(degree: usize) -> usize {
    64 * (degree + 1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{Field, Fp2, Fp4};

    #[test]
    fn group_openings() {
        let leaves: Vec<Vec<u8>> = (0..64u8).map(|i| vec![i, i ^ 0x5a]).collect();
        for salt_len in [0, 32] {
            let t = MerkleTree::new(&leaves, &[9u8; 32], b"t", salt_len);
            for g in 0..3 {
                for i in 0..64 {
                    let op = t.open_group(i, g);
                    let start = (i >> g) << g;
                    let data = leaves[start..start + (1 << g)].to_vec();
                    assert!(verify_group(&t.root(), i, g, &data, &op));
                    let mut bad = data.clone();
                    bad[0][0] ^= 1;
                    assert!(!verify_group(&t.root(), i, g, &bad, &op));
                }
            }
        }
    }

    #[test]
    fn challenge_digits_are_canonical() {
        let mut tr = Transcript::new(b"x");
        for _ in 0..100 {
            let a: Fp4 = tr.challenge();
            let b: Fp2 = tr.challenge();
            assert!(a.digits().iter().chain(b.digits().iter()).all(|d| d.0 < P));
            assert_ne!(a, Fp4::ZERO);
        }
        let idx = tr.query_indices(50, 13);
        assert!(idx.iter().all(|&i| i < 1 << 13));
    }
}
