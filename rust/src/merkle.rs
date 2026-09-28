//! Salted BLAKE3 Merkle trees (Section 3.4, "Salted Merkle commitments") and the Fiat-Shamir
//! transcript with the challenge maps phi and pos of Section 8.1.
//!
//! Leaves are H_{K0}(data || salt), internal nodes H_{K1}(left || right), with BLAKE3 in keyed
//! mode under two fixed keys K0 = 0^32, K1 = 1^32 (domain separation).  With
//! `salt_len = 0` the trees are unsalted (used only to measure the cost of salting).

use crate::error::Error;
use crate::field::{ExtField, Fp, P};

pub type Digest = [u8; 32];

/// Domain separation of leaves and internal nodes by two fixed BLAKE3 keys (keyed mode), so that
/// a node, and a salted leaf of one fibre over F_{p^2}, hash exactly 64 bytes: one compression.
const LEAF_KEY: [u8; 32] = [0u8; 32];
const NODE_KEY: [u8; 32] = [1u8; 32];

fn hash_leaf(data: &[u8], salt: &[u8]) -> Digest {
    let mut h = blake3::Hasher::new_keyed(&LEAF_KEY);
    h.update(data);
    h.update(salt);
    *h.finalize().as_bytes()
}

fn hash_node(l: &Digest, r: &Digest) -> Digest {
    let mut h = blake3::Hasher::new_keyed(&NODE_KEY);
    h.update(l);
    h.update(r);
    *h.finalize().as_bytes()
}

/// The salt stream of one tree: the extendable output of BLAKE3 keyed with the prover seed on the
/// tree label; leaf i gets the bytes [i len, (i+1) len) of the stream (the seed must be fresh and
/// secret for each tree). One stream per tree, read in bulk when the tree is built and at an
/// offset when a group is opened.
fn salt_stream(seed: &Digest, label: &[u8]) -> blake3::OutputReader {
    let mut h = blake3::Hasher::new_keyed(seed);
    h.update(b"leaf-salts");
    h.update(&(label.len() as u64).to_le_bytes());
    h.update(label);
    h.finalize_xof()
}

fn salt(seed: &Digest, label: &[u8], index: usize, len: usize) -> Vec<u8> {
    if len == 0 {
        return Vec::new();
    }
    let mut r = salt_stream(seed, label);
    r.set_position((index * len) as u64);
    let mut out = vec![0u8; len];
    r.fill(&mut out);
    out
}

/// A salted Merkle tree over T = 2^t leaves.  Salts are recomputed from the seed (at an offset of
/// the salt stream) when a group is opened, so that only the hash layers are stored.
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
        leaf: impl Fn(usize, &mut Vec<u8>) + Sync,
        seed: &Digest,
        label: &[u8],
        salt_len: usize,
    ) -> Self {
        assert!(count.is_power_of_two());
        let mut salts = vec![0u8; count * salt_len];
        if salt_len > 0 {
            salt_stream(seed, label).fill(&mut salts);
        }
        let hashes: Vec<Digest> = crate::par::map_range_buf(count, |buf, i| {
            buf.clear();
            leaf(i, buf);
            hash_leaf(buf, &salts[i * salt_len..(i + 1) * salt_len])
        });
        let mut layers = vec![hashes];
        while layers.last().unwrap().len() > 1 {
            let prev = layers.last().unwrap();
            let next: Vec<Digest> = crate::par::map_range(prev.len() / 2, |i| {
                hash_node(&prev[2 * i], &prev[2 * i + 1])
            });
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
    /// The cap of height `c`: the 2^c nodes at distance c from the root (the root itself for c = 0).
    pub fn cap(&self, c: usize) -> Vec<Digest> {
        let depth = self.layers.len() - 1;
        self.layers[depth - c.min(depth)].clone()
    }
    /// Open the aligned group of 2^g leaves containing leaf `i`, with the path stopping below a
    /// cap of height `c` (the verifier checks the result against the published cap).
    /// Requires g + c <= depth, so that the group node lies below the cap.
    pub fn open_group_capped(&self, i: usize, g: usize, c: usize) -> GroupOpening {
        let depth = self.layers.len() - 1;
        let top = depth - c.min(depth);
        let mut op = self.open_group(i, g);
        op.path.truncate(top.saturating_sub(g));
        op
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

/// Root of the tree whose cap (the 2^c nodes at height c below the root) is `cap`.
///
/// Returns [`Error::Shape`] if the cap is empty or its length is not a power of two.
pub fn root_from_cap(cap: &[Digest]) -> Result<Digest, Error> {
    if !cap.len().is_power_of_two() {
        return Err(Error::Shape);
    }
    let mut level = cap.to_vec();
    while level.len() > 1 {
        level = level
            .as_chunks::<2>()
            .0
            .iter()
            .map(|[l, r]| hash_node(l, r))
            .collect();
    }
    Ok(level[0])
}

/// Check a capped group opening (see `MerkleTree::open_group_capped`) against a cap.
pub fn verify_group_capped(
    cap: &[Digest],
    i: usize,
    g: usize,
    data: &[Vec<u8>],
    op: &GroupOpening,
) -> bool {
    if data.len() != 1 << g || op.salts.len() != 1 << g || !cap.len().is_power_of_two() {
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
    idx < cap.len() && cap[idx] == cur
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
    /// A challenge in `F \ {0}`: the first nonzero output of [`Transcript::challenge`]. A zero
    /// output has probability below `2^{-64}` per draw, so the loop runs once except with that
    /// probability.
    pub fn challenge_nonzero<E: ExtField>(&mut self) -> E {
        loop {
            let c: E = self.challenge();
            if c != E::ZERO {
                return c;
            }
        }
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
    fn capped_openings() {
        let leaves: Vec<Vec<u8>> = (0..64u8).map(|i| vec![i, 3 * i]).collect();
        let t = MerkleTree::new(&leaves, &[5u8; 32], b"c", 32);
        for c in 0..=6 {
            let cap = t.cap(c);
            assert_eq!(cap.len(), 1 << c);
            assert_eq!(root_from_cap(&cap), Ok(t.root()));
            for g in 0..3usize.min(7 - c) {
                for i in (0..64).step_by(5) {
                    let op = t.open_group_capped(i, g, c);
                    let start = (i >> g) << g;
                    let data = leaves[start..start + (1 << g)].to_vec();
                    assert!(verify_group_capped(&cap, i, g, &data, &op));
                    let mut bad = data.clone();
                    bad[0][1] ^= 1;
                    assert!(!verify_group_capped(&cap, i, g, &bad, &op));
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

#[cfg(test)]
mod salt_tests {
    use super::*;

    #[test]
    fn opened_salts_match_the_tree() {
        // the salts of an opened group are those hashed into the tree
        let leaves: Vec<Vec<u8>> = (0..16u8).map(|i| vec![i; 5]).collect();
        let t = MerkleTree::new(&leaves, &[9u8; 32], b"lbl", 32);
        for i in 0..16 {
            let op = t.open_group(i, 0);
            assert_eq!(hash_leaf(&leaves[i], &op.salts[0]), t.layers[0][i]);
        }
        // distinct labels give distinct streams
        assert_ne!(salt(&[9u8; 32], b"a", 0, 32), salt(&[9u8; 32], b"b", 0, 32));
    }
}
