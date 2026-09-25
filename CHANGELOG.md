# Changelog

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
