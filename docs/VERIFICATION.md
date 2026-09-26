# Verification status

How each result of the paper is established (paper, Appendix B).

- **Proved:** proved in the paper.
- **From KBFold:** statement and proof reproduced from the companion paper [qoosmo/kbfold](https://github.com/qoosmo/kbfold) and its Lean 4 project.
- **Quoted:** cited, not reproved.
- **Lean:** machine-checked in [`lean/`](../lean/) (Lean 4.23.0, Mathlib v4.23.0). There is no `sorry`, and the only axiom is Theorem 2.16 (correlated agreement for curves, `KBFold.bciks_curves`). CI checks both on every push. [`lean/README.md`](../lean/README.md) gives the full paper ↔ Lean correspondence.
- **Tested:** checked on random instances by the Rust test suite or examples. Tests are evidence, not proofs.

| Result | Status | Lean | Tested |
|---|---|---|---|
| Facts 2.3, 2.13, 6.4 (cyclic group, unique decoding, NTT) | quoted | — | NTT against Horner evaluation |
| Theorem 2.16 (correlated agreement, BCIKS) | quoted | the single axiom `bciks_curves` | — |
| Theorem 3.15 (BCS for interactive oracle reductions, CDHZ) | quoted | — | bound of Remark 8.8 evaluated exactly (`pq_params`) |
| §2 lemmas (bits, roots, splits, Möbius, domains, RS codes) | proved; from KBFold | from KBFold | Möbius transform |
| Lemma 2.14 (descent), Lemma 3.12 (Merkle) | proved; from KBFold | — | Merkle openings |
| §3 lemmas (sequential challenges, queries, randomised provers, RBR ⇒ overall, binding) | proved; from KBFold | from KBFold | — |
| §4: Kronecker substitution, kernel polynomial, **extraction identity**, corollaries, reversal | proved | `extraction`, `kronEncLin_bijective`, `coeff_kernel_bits`, `bilinear`, `kernel_reflect`, `cube_sum_half` | n ≤ 8, both fields; F₂₅₇ |
| §4: split lemma, **identity lemma**, Remark 4.13 | proved | `split_iff`, `split_unique`, `identity_lemma`, `without_X_absorbs` | split, root bound |
| Lemma 4.9, Lemma 6.7, Proposition 6.11 (operation counts) | proved | — | kernel product, K_z on L |
| §5.1: word fold, line form, consistency | proved; from KBFold | from KBFold | n ≤ 7 |
| Lemma 5.5 (iterated fold) | proved | `coeff_pfoldUp` | n ≤ 7 |
| §5.3–5.4: fibre distance, unique decoding, far words, surviving errors, good challenges, one step | proved; from KBFold | from KBFold | — |
| §5.5–5.6: witness sets, one round, codeword chain, **Theorem 5.24** | proved; adapted from KBFold | `rbr_step`, `chain_final`, `fpt_sound` | — |
| §5.7: virtual levels, arity 2^k (**Proposition 5.28**) | proved | `acceptsC_iff`, `acceptsC_congr`, `orcC_virtual_local`, `fptC_sound` | arities 2–16, with and without Merkle caps |
| §6: encoding, virtual word, **completeness** (Theorem 6.10), Remark 6.9(1) | proved | `encode_injective`, `virt_honest`, `honestKF_prob_one`, `virt_wrong_value` | n ≤ 9, all ℓ, three rates, arities 2/4/8 |
| Lemma 6.3(3) (base field) | proved | — | — |
| §7: rate condition, value from agreement, **batching lemma**, fibre-closed witness sets | proved | `rate_condition`, `value_of_agreement`, `batching`, `negPt_mem_Wset` | — |
| **Theorem 7.8 (soundness)**, for any set of committed levels | proved | `soundness`, `soundnessC` | tampering tests |
| Definition 7.9, Lemma 7.10, **Theorem 7.11 (RBR knowledge soundness)**, Corollary 7.12 | proved | `extKF_witness`, `rbr_knowledge` (framework of Def 3.7), `knowledge`, `binding`, `rbr_binding` | — |
| §8: sampling, erasures, relaxed RBR knowledge soundness, PQ corollary, uniqueness | proved (using Thm 3.15) | — | — |
| Remark 8.8 (post-quantum parameters) | computed | — | exact rational evaluation; non-squareness of 7 |
| **Theorem 11.2, Corollary 11.3 (batched openings)** | proved | `batch_soundness`, `batch_knowledge`, `batch_binding` | not implemented |
