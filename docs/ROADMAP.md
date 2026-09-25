# Roadmap

## Formal verification
- **Lean 4 formalisation** of §4 (extraction and opening identities), §5 (folding test), §6 (scheme, virtual word) and §7 (soundness), reusing the KBFold Lean project (Mathlib, `bciks_unique` as the only axiom).

## Theory
- **List decoding.** Extend the batching lemma and the folding test beyond (1−ρ)/2. The identity lemma still holds for every δ < 1 − 2ρ; at ρ = 1/4 and 100 bits this would bring κ from 148 to about 100 near the Johnson bound.
- **Rate 1/2.** The batching lemma needs ρ < 1/3; find an identity or argument that works at rate 1/2.
- **Post-quantum batched openings.** Carry the erasure analysis of §8 over to the batched protocol (its relation is already fibre-based).
- **Several points and several openings** of one commitment; Corollary 4.6 is a starting point.
- **Zero knowledge** by masking the opening polynomial and the folded words.

## Engineering
- Check the transcript and salts against Construction 11.7 of Chiesa–Di–Hu–Zheng, so that the post-quantum corollary applies to the code.
- Implement batched openings.
- Merkle multiproofs, parallel NTT and hashing, SIMD field arithmetic.
- Additional fields: BabyBear and KoalaBear (extension degree ≥ 5 for 100 bits).
- Measure the verifier inside a recursive verification circuit.
