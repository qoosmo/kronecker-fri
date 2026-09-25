# Verification status

How each result of the paper is established (paper, Appendix B). **Proved**: proved in the paper. **From KBFold**: statement and proof reproduced from the companion paper [qoosmo/kbfold](https://github.com/qoosmo/kbfold), whose Lean 4 project formalises most of these statements (not Lemma 2.14 or Lemma 3.12). **Quoted**: cited, not reproved. **Tested**: checked on random instances by the Rust test suite or examples; tests are evidence, not proofs.

No result of this paper is formalised in Lean yet; see [ROADMAP.md](ROADMAP.md).

| Result | Status | Machine check |
|---|---|---|
| Facts 2.3, 2.13, 6.4 (cyclic group, unique decoding, NTT) | quoted | NTT tested against Horner evaluation |
| Theorem 2.16 (correlated agreement, BCIKS) | quoted | — |
| Theorem 3.15 (BCS for interactive oracle reductions, CDHZ) | quoted | bound of Remark 8.8 evaluated exactly (`pq_params`) |
| §2 lemmas (bits, roots, splits, Möbius, domains, RS codes, descent) | proved; from KBFold | Möbius transform tested |
| §3 lemmas (sequential challenges, queries, randomised provers, RBR ⇒ overall, binding, Merkle) | proved; from KBFold | Merkle openings tested |
| §4: Kronecker substitution, kernel polynomial, extraction identity, corollaries, reversal | proved | coefficient rule and extraction identity tested (n ≤ 8, both fields; F₂₅₇) |
| §4: costs, split lemma, identity lemma | proved | kernel product, split and root bound tested |
| §5.1: word fold, line form, consistency | proved; from KBFold | tested (n ≤ 7) |
| Lemma 5.5 (iterated fold, coefficient formula) | proved (new) | tested (n ≤ 7) |
| §5.3–5.4: fibre distance, unique decoding, far words, surviving errors, good challenges, one step | proved; from KBFold | — |
| §5.5–5.6: witness sets, one round, codeword chain, Theorem 5.24 | proved; adapted from KBFold | — |
| §6: encoding, virtual word, K_z on the domain, completeness | proved | virtual word, K_z on L, completeness tested (n ≤ 9, all ℓ, three rates, both fields) |
| Proposition 6.11 (costs) | proved | — |
| §7: rate condition, value from agreement, batching lemma, fibre-closed witness sets | proved | — |
| Remark 6.9(1), Remark 4.13 (wrong values, why the factor X) | proved | two cheating provers rejected |
| §7: soundness, extractor, round-by-round knowledge soundness, binding | proved | tampering tests |
| §8: sampling, erasures, relaxed RBR knowledge soundness, PQ corollary, uniqueness | proved (using Thm 3.15) | — |
| Remark 8.8 (post-quantum parameters) | computed | exact rational evaluation; non-squareness of 7 checked |
| Theorem 11.2, Corollary 11.3 (batched openings) | proved | not implemented |
