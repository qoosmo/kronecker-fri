# Changelog

## Unreleased — R1CS prototype without sumcheck

### Code
- `rust/src/affine.rs`: Π_Batch on affine forms of committed and public tables (Proposition 5.1 of the note): committed words in groups (one Merkle tree per group, one value of each word per leaf), public tables 1, 0, id, η^w and explicit sparse tables.
- `rust/src/r1cs.rs`: indexer, prover and verifier of the sumcheck-free R1CS argument (Theorem 5.8): three linchecks with LogUp lookups, Had(a, b, c), public input; tests against a wrong input, an unsatisfied constraint, a nonzero input slot of the witness, a false lincheck, and a false lincheck repaired by a forged lookup value (row or column).
- `examples/r1cs_bench.rs`, `bench/r1cs.csv`: n = 16 (32768 constraints): prove 7.8 s, verify 68 ms, proof 2.6 MiB (unoptimised).

### Note (version 8)
- §5 status: the compiled protocol, its tests and measurements.

## Unreleased — sparse matrix–vector products (R1CS) without sumcheck

### Note (`notes/inner-product/`, version 7, 13 pages)
- New §5: statements on affine forms of committed and public tables (Proposition affine); the lincheck Π_Lin proving a = Mz for a public sparse M by random weights and two LogUp lookups (Lemma logup: LogUp with pairs, error (2N-1)/|F|); reduction and soundness theorems (ε_Lin = (7N-3)/|F|); R1CS without sumcheck with error (9N-5+tM)/|F| + ε_fold + (1-δ)^κ. Proofs written out and refereed; not yet compiled or in Lean.

### Code
- `rust/src/lincheck.rs`: clear-text check of the lincheck reduction (closed forms of the public tables; honest runs; a wrong a, a forged lookup value of the row or the column side are each caught by the expected statement).

## Unreleased — Lean formalisation of the batched protocol

### Lean (`lean/KroneckerFRI/BatchStmts.lean`)
- §4 of the note: statements (evaluation, inner product, Hadamard check) on table-form commitments, words indexed by a finite type, degree-t batching lemma, soundness 2(N-1)/|F| + tM/|F| + ε_fold + (1-δ)^κ for any folding arity, knowledge, completeness (probability ≥ 1 - 3M/|F|). Still no `sorry` and one axiom; 11 new entries in `Audit.lean`.

### Note (version 6)
- All four sections machine-checked; the refinement "no γ,θ term when there is no Hadamard check" is stated as a remark outside Lean.

## Unreleased — batched statements in one folding test

### Note (`notes/inner-product/`, version 5, 9 pages)
- New §4: Π_Batch proves any list of evaluations, inner products and Hadamard checks on table-form commitments with one folding test; soundness 2(N-1)/|F| + tM/|F| + ε_fold + (1-δ)^κ for t+1 batched words, with the γ,θ term paid once whatever the number of Hadamard checks. Proofs written out; Lean formalisation next.

### Code
- `rust/src/batch.rs`: prototype prover and verifier of Π_Batch (label `kronecker-fri-batch-v1`), one multi-value Merkle tree for all w_Q and one for all w_A; table-form evaluation kernel E*_z (coefficients, evaluation, whole domain); tests for mixed batches and for one false statement of each kind.
- `examples/batch_bench.rs`, `bench/batch.csv`: one batched proof against four separate proofs (n = 20: 805 KiB vs 1958 KiB, verification 11.3 ms vs 25.4 ms).

## Unreleased — Lean formalisation of the Hadamard check

### Lean (`lean/KroneckerFRI/Hadamard.lean`)
- §3 of the note: DEEP step on an agreement set, geometric weights, Π_Had with challenges γ, θ, β uniform in F, completeness (accepted when no pole lies in L; probability ≥ 1 - 3M/|F|), degree-8 batching lemma, soundness 2(N-1)/|F| + 8M/|F| + ε_fold + (1-δ)^κ for any folding arity, knowledge. Still no `sorry` and one axiom; 10 new entries in `Audit.lean`.
- `ft_family_bound`: the argument of Theorem 7.8 for any family of batched words.

### Note (version 4)
- §3 restated for unrestricted challenges, as formalised (a pole in L only affects completeness); Lean names added.

## Unreleased — research note: sumcheck-free Hadamard check

### Note (`notes/inner-product/`, version 3, 7 pages)
- §3: the Hadamard check Π_Had proving a∘b = c for three committed tables with one folding test and no sumcheck (geometric weights γ^w, a committed Q(X) = V_a(γX), DEEP quotient words in the batch); completeness, degree-8 batching lemma and soundness (N-1)/(|F|-M-1) + (N-1)/(|F|-2M) + 8M/|F| + ε_fold + (1-δ)^κ, proofs written out (not yet in Lean).

### Code
- `rust/src/had.rs`: prototype prover and verifier of Π_Had (label `kronecker-fri-had-v1`); tests for completeness, two cheating provers and a false instance with three strategies.
- `rust/src/ft.rs`: the folding test on a batched word and level-0 coset openings, factored out of `pcs` for new protocols.
- `examples/ip_bench.rs` and `bench/ip.csv` gain the Hadamard columns.

## Unreleased — research note: sumcheck-free inner products

### Note (`notes/inner-product/`, 5 pages)
- Table-form commitments (the table of values committed as the coefficient vector of V_f; the same Merkle commitment as `pcs`), the evaluation kernel E*_z, and the protocol Π_IP proving `∑_w a(w) b(w) = S` for two committed tables with one folding test and no sumcheck; soundness error 3M/|F| + ε_fold + (1-δ)^κ.

### Lean (`lean/KroneckerFRI/TableForm.lean`, `InnerProduct.lean`)
- §1–2 of the note: evaluation kernel, reversal, inner-product identity, general split and identity lemmas, reversed words, completeness, degree-3 batching lemma, soundness (any arity), knowledge and binding. Still no `sorry` and one axiom; 13 new entries in `Audit.lean`.
- `curve_agreement`: correlated agreement on one fibre-closed set for a curve of any degree.

### Code (`rust/src/ip.rs`, `examples/ip_bench.rs`)
- Prototype prover and verifier of Π_IP on the commitments of `pcs` (caps, arity 2^k, Fiat–Shamir label `kronecker-fri-ip-v1`); tests for completeness and three cheating provers; `bench/ip.csv`.

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
