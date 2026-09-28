//! Shared pieces of the protocols built on one folding test (`had`): the folding test Pi_FT on a
//! batched word w_0 (rounds 2 .. l+2 of `pcs::open_with`) and coset openings of level-0 oracles.
//! The code is that of `pcs`, factored so that a protocol only supplies w_0, its polynomial U_0,
//! and the level-0 oracles it reads.

use crate::error::Error;
use crate::field::{ExtField, Field, Fp};
use crate::merkle::{
    Digest, GroupOpening, MerkleTree, Transcript, root_from_cap, verify_group_capped,
};
use crate::pcs::{
    Params, coset_tree, coset_values, distinct_positions, e_bytes, fold_coset, inv_powers,
    pair_bytes, unpair,
};
use crate::poly::{fold_word, horner, pfold};

/// Salt of round r, derived from the prover's secret seed.
pub(crate) fn round_salt(seed: &Digest, r: usize, len: usize) -> Vec<u8> {
    let mut h = blake3::Hasher::new_keyed(seed);
    h.update(b"round-salt");
    h.update(&(r as u64).to_le_bytes());
    let mut s = vec![0u8; len];
    h.finalize_xof().fill(&mut s);
    s
}

/// Opening of a word on the points above one position.
#[derive(Clone, Debug)]
pub struct CosetOpening<T> {
    pub pos: usize,
    pub vals: Vec<[T; 2]>,
    pub open: GroupOpening,
}

/// The folding-test part of a proof.
#[derive(Clone, Debug)]
pub struct FtProof<E> {
    pub caps: Vec<Vec<Digest>>,
    /// salts of the rounds after the batching challenge (l + 1 of them)
    pub round_salts: Vec<Vec<u8>>,
    pub p: Vec<E>,
    pub levels: Vec<Vec<CosetOpening<E>>>,
}

pub(crate) fn open_size<T>(o: &CosetOpening<T>, elem: usize) -> usize {
    2 * elem * o.vals.len()
        + 32 * o.open.path.len()
        + o.open.salts.iter().map(|s| s.len()).sum::<usize>()
}

impl<E: ExtField> FtProof<E> {
    pub fn size_bytes(&self) -> usize {
        let e = 8 * E::DEGREE;
        let mut s = 32 * self.caps.iter().map(|c| c.len()).sum::<usize>() + self.p.len() * e;
        s += self.round_salts.iter().map(|x| x.len()).sum::<usize>();
        for lv in &self.levels {
            for o in lv {
                s += open_size(o, e);
            }
        }
        s
    }
}

/// Prover of Pi_FT on w_0 = ev_L(u0) (rounds 2 .. l+2). `first_round` is the index of the round
/// of r_1 (for the salts).  Returns the proof part and the query indices.
pub(crate) fn ft_prove<E: ExtField>(
    p: &Params,
    tr: &mut Transcript,
    seed: &Digest,
    first_round: usize,
    w0: Vec<E>,
    u0: Vec<E>,
) -> (FtProof<E>, Vec<usize>) {
    let (m, ell) = (p.m(), p.ell);
    let groups = p.groups();
    let omega = p.omega();
    let inv2 = Fp::new(2).inv();
    let inv_x0 = inv_powers(omega, m / 2);
    let mut round_salts = Vec::with_capacity(ell + 1);
    let committed: Vec<usize> = groups
        .iter()
        .map(|&(jc, _)| jc)
        .filter(|&jc| jc >= 1)
        .collect();
    let mut kept: Vec<(usize, Vec<E>, MerkleTree)> = Vec::new();
    let mut caps = Vec::new();
    let mut coeffs = u0;
    let mut cur = w0;
    for j in 1..=ell {
        if j >= 2 && committed.contains(&(j - 1)) {
            let g = groups.iter().find(|&&(st, _)| st == j - 1).unwrap().1;
            let tree = coset_tree(&cur, g, seed, format!("w{}", j - 1).as_bytes(), p.salt_len);
            tr.absorb(b"root", &tree.root());
            caps.push(tree.cap(p.cap_for(cur.len() / 2, g - 1)));
            kept.push((j - 1, cur.clone(), tree));
        }
        round_salts.push(round_salt(seed, first_round + j - 1, p.salt_len));
        tr.absorb(b"salt", round_salts.last().unwrap());
        let r: E = tr.challenge();
        coeffs = pfold(&coeffs, r);
        if j < ell {
            cur = fold_word(&cur, r, &inv_x0, j - 1, inv2);
        }
    }
    drop(cur);
    let pb: Vec<u8> = coeffs.iter().flat_map(e_bytes).collect();
    tr.absorb(b"final", &pb);
    round_salts.push(round_salt(seed, first_round + ell, p.salt_len));
    tr.absorb(b"salt", round_salts.last().unwrap());
    let idx = tr.query_indices(p.queries, p.n + p.log_inv_rate);
    let levels = kept
        .iter()
        .map(|(jc, word, tree)| {
            let g = groups.iter().find(|&&(st, _)| st == *jc).unwrap().1;
            open_cosets(
                p,
                tree,
                word,
                &distinct_positions(&idx, m >> (jc + g)),
                g,
                *jc,
            )
        })
        .collect();
    (
        FtProof {
            caps,
            round_salts,
            p: coeffs,
            levels,
        },
        idx,
    )
}

/// Openings of `word` (on L_jc, group length g) on the cosets above `positions`.
pub(crate) fn open_cosets<T: Field>(
    p: &Params,
    tree: &MerkleTree,
    word: &[T],
    positions: &[usize],
    g: usize,
    _jc: usize,
) -> Vec<CosetOpening<T>> {
    let c = p.cap_for(word.len() / 2, g - 1);
    positions
        .iter()
        .map(|&a| CosetOpening {
            pos: a,
            vals: coset_values(word, g, a),
            open: tree.open_group_capped(a << (g - 1), g - 1, c),
        })
        .collect()
}

/// Checks level-0 openings against a cap: shape, canonical positions, Merkle paths.
pub(crate) fn check_level0<T: Field>(
    p: &Params,
    cap: &[Digest],
    ops: &[CosetOpening<T>],
    positions: &[usize],
) -> Result<(), Error> {
    let m = p.m();
    let g0 = p.groups()[0].1;
    let depth0 = (m / 2).trailing_zeros() as usize;
    let c0 = p.cap_for(m / 2, g0 - 1);
    if cap.len() != 1 << c0
        || ops.len() != positions.len()
        || ops.iter().zip(positions).any(|(o, &a)| {
            o.pos != a
                || o.vals.len() != 1 << (g0 - 1)
                || o.open.path.len() != depth0 - (g0 - 1) - c0
                || o.open.salts.iter().any(|s| s.len() != p.salt_len)
        })
    {
        return Err(Error::Shape);
    }
    for o in ops {
        let d: Vec<Vec<u8>> = o.vals.iter().map(|[x, y]| pair_bytes(x, y)).collect();
        if !verify_group_capped(cap, o.pos << (g0 - 1), g0 - 1, &d, &o.open) {
            return Err(Error::Merkle);
        }
    }
    Ok(())
}

/// Values of a level-0 oracle on the coset above position a (index t: position a + t M_{g0}).
pub(crate) fn coset_of<T: Copy>(ops: &[CosetOpening<T>], a: usize) -> Vec<T> {
    let i = ops.binary_search_by_key(&a, |o| o.pos).unwrap();
    unpair(&ops[i].vals)
}

/// Verifier of Pi_FT, first part: checks the shape and Merkle openings of the folded words,
/// replays the transcript and returns (r_1 .. r_l, query indices).
pub(crate) fn ft_replay<E: ExtField>(
    p: &Params,
    tr: &mut Transcript,
    ft: &FtProof<E>,
) -> Result<(Vec<E>, Vec<usize>), Error> {
    let (d, m, ell) = (p.degree(), p.m(), p.ell);
    let groups = p.groups();
    let ncommit = groups.len() - 1;
    if ft.caps.len() != ncommit
        || ft.levels.len() != ncommit
        || ft.round_salts.len() != ell + 1
        || ft.round_salts.iter().any(|s| s.len() != p.salt_len)
        || ft.p.len() != d >> ell
    {
        return Err(Error::Shape);
    }
    let mut rs: Vec<E> = Vec::with_capacity(ell);
    let mut ci = 0;
    for j in 1..=ell {
        if j >= 2 && groups.iter().any(|&(st, _)| st == j - 1) {
            tr.absorb(b"root", &root_from_cap(&ft.caps[ci])?);
            ci += 1;
        }
        tr.absorb(b"salt", &ft.round_salts[j - 1]);
        rs.push(tr.challenge());
    }
    let pb: Vec<u8> = ft.p.iter().flat_map(e_bytes).collect();
    tr.absorb(b"final", &pb);
    tr.absorb(b"salt", &ft.round_salts[ell]);
    let idx = tr.query_indices(p.queries, p.n + p.log_inv_rate);
    for (gi, &(jc, g)) in groups.iter().enumerate().skip(1) {
        let leaves = (m >> jc) / 2;
        let (depth, c) = (leaves.trailing_zeros() as usize, p.cap_for(leaves, g - 1));
        let pj = distinct_positions(&idx, m >> (jc + g));
        let lv = &ft.levels[gi - 1];
        if ft.caps[gi - 1].len() != 1 << c
            || lv.len() != pj.len()
            || lv.iter().zip(&pj).any(|(o, &a)| {
                o.pos != a
                    || o.vals.len() != 1 << (g - 1)
                    || o.open.path.len() != depth - (g - 1) - c
                    || o.open.salts.iter().any(|s| s.len() != p.salt_len)
            })
        {
            return Err(Error::Shape);
        }
        for o in lv {
            let d: Vec<Vec<u8>> = o.vals.iter().map(|[x, y]| pair_bytes(x, y)).collect();
            if !verify_group_capped(&ft.caps[gi - 1], o.pos << (g - 1), g - 1, &d, &o.open) {
                return Err(Error::Merkle);
            }
        }
    }
    Ok((rs, idx))
}

/// Verifier of Pi_FT, per query: given w_0 on the coset above i0 mod M_{g0}, fold through the
/// committed levels and compare with the final polynomial.
pub(crate) fn ft_check_query<E: ExtField>(
    p: &Params,
    ft: &FtProof<E>,
    rs: &[E],
    i0: usize,
    w0: Vec<E>,
) -> Result<(), Error> {
    let (m, ell) = (p.m(), p.ell);
    let groups = p.groups();
    let omega = p.omega();
    let mg0 = m >> groups[0].1;
    let mut value = fold_coset(w0, i0 % mg0, 0, mg0, rs, m, omega);
    for (gi, &(jc, g)) in groups.iter().enumerate().skip(1) {
        let mg = m >> (jc + g);
        let aj = i0 % mg;
        let vals = coset_of(&ft.levels[gi - 1], aj);
        let pos = i0 % (m >> jc);
        if vals[(pos - aj) / mg] != value {
            return Err(Error::Fold);
        }
        value = fold_coset(vals, aj, jc, mg, rs, m, omega);
    }
    let pos = i0 % (m >> ell);
    let eta = omega.pow((pos as u64) << ell);
    if value != horner(&ft.p, E::from(eta)) {
        return Err(Error::Fold);
    }
    Ok(())
}
