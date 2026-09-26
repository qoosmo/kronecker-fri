# Changelog

## v0.3.0 — 2026-09-26

### Lean 4 formalisation (`lean/`)
- Machine-checked proofs of §4 (extraction identity, split and identity lemmas, corollaries), §5 (iterated fold, folding test soundness, codeword chain, virtual levels and arity 2^k), §6 (encoding, virtual word, completeness), §7 (batching lemma, soundness for any set of committed levels, round-by-round knowledge soundness in the generic IOP framework, knowledge and binding) and §11 (batched openings).
- No `sorry`; single axiom: correlated agreement for curves (Theorem 2.16). CI job `Lean` builds, checks for `sorry`, and audits the axioms of every main theorem.

### Paper (64 pages)
- Appendix B gains a Lean column; introduction, abstract and conclusion updated.


## v0.2.0 — 2026-09-26

### Paper (63 pages)
- New §5.7: folding of arity $2^k$ with virtual levels (Definition 5.27, Proposition 5.28): committing to every $k$-th folded word only leaves every error term unchanged.
- §6–§8 stated for any set of committed levels; §8 justifies compressed openings (shared paths, caps, deduplication) as a re-encoding of the BCS proof.
- §9–§11 rewritten with new measurements from one session: arity/caps table, recommended configuration KF-8, new parameter sets (390 KiB salted proofs at $n = 20$, 100 bits; 755 KiB post-quantum).

### Code
- Folding arity $2^k$ (`Params::fold_log`), coset-grouped leaf layout, one path per coset.
- Merkle caps (`Params::cap_log`), deduplicated openings with a canonical order.
- `Params::recommended(n, queries, salt_len)`; transcript label `kronecker-fri-v3` (proofs are not compatible with v0.1.0).
- Tests for arities 2–16 with and without caps; new `bench arity` mode.
- Clippy clean on Rust 1.98 (`as_chunks`); CI pinned to Rust 1.95.0.


## v0.1.0 — 2026-09-25

First public release.

### Paper (`paper/kronecker-fri.pdf`, 60 pages)
- Extraction identity $f(z) = [X^{N-1}]\,U_f K_z$, opening identity and identity lemma, with exact algorithm costs.
- Self-contained analysis of the FRI-style folding test (kernel fold) for arbitrary words.
- The evaluation protocol $\Pi_{\mathrm{KF}}$: one opening oracle, a virtual word, batching, folding; no sumcheck.
- Completeness, soundness, round-by-round knowledge soundness and evaluation binding in the unique-decoding regime.
- Post-quantum straightline knowledge soundness of the compiled scheme (QROM) via Chiesa–Di–Hu–Zheng.
- Batched openings of several polynomials at one point.
- Experiments against KBFold and a coefficient-form baseline; recommended parameters; comparison with existing schemes.

### Code (`rust/`)
- Goldilocks field, quadratic and quartic extensions.
- Möbius transform, NTT, kernel polynomial and kernel product, opening polynomials, virtual word, kernel folds.
- Salted Merkle trees with fibre leaves, Fiat–Shamir transcript with the challenge maps of the paper.
- Prover and verifier of $\Pi_{\mathrm{KF}}$; tests, small-field checks, exact post-quantum bound, benchmarks.
