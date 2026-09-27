# Changelog

## Unreleased — comparison with a sumcheck-based R1CS argument

### Code
- `rust/src/spartan.rs`: the core of Spartan (outer sumcheck of degree 3, inner sumcheck of degree 2, one Π_KF opening of the witness; verifier linear in the number of nonzero entries, no SPARK) on the same commitment, field, hash and instances as `r1cs`; tests against a wrong input, an unsatisfied constraint, a wrong claim, a wrong opening value and a tampered round polynomial, and a check of the variable order of `pcs`.
- `examples/spartan_bench.rs`, `bench/spartan.csv`; `bench/r1cs.csv` re-measured in the same session.
- At n = 16: Spartan core prove 288 ms, verify 11.7 ms, proof 251 KiB; the argument of the note prove 5469 ms, verify 43.6 ms, proof 1997 KiB.

### Note (version 12)
- §5: the comparison table, a profile of the prover, a floor for SPARK, and the verifier trade-off; Setty (Spartan) cited.

## Unreleased — completeness of the R1CS argument in Lean

### Lean
- `lean/KroneckerFRI/R1CS.lean`: the honest prover (`honestR1`: honest lincheck tables `fsH`, sums, and the honest `Π_Batch` prover of Proposition affine); the honest LogUp identity (`logup_honest`); the 21 statements hold when no row or column denominator vanishes (`honest_holds`); `r1cs_completeness`: the honest prover is accepted with probability at least `1 - 2N/|F| - 3M/|F|`.
- `Audit.lean`: the new theorems (no axiom beyond Lean's three).

### Note (version 11)
- §5 and the Lean status: completeness of the R1CS argument machine-checked.

## Unreleased — R1CS soundness machine-checked end to end

### Lean
- `lean/KroneckerFRI/AffineBatch.lean`: `Π_Batch` on affine forms of committed words and public tables (Proposition affine): forms with a declared support, statements on forms, direct checks of the quotient values of public forms; Lemma batchT (`batching_A`), soundness and knowledge (`prob_bad_A`, `soundness_A`, `knowledge_A`), completeness (`awords_honest`, `honestA_accepts`, `honestA_prob`).
- `lean/KroneckerFRI/Lincheck.lean`: tables indexed by any numbered finite set (`Numbering`), so that the lincheck applies to hypercube tables.
- `lean/KroneckerFRI/R1CS.lean`: the R1CS argument with its 21 statements; `tA_r1stmts` (127 words for every instance and challenges); `r1_bridge` (a batch witness gives the lincheck statements); `r1cs_soundness`: Theorem r1cs end to end, bound `(13N-3)/|F| + 2(N-1)/|F| + 126M/|F| + ε_fold + (1-δ)^κ`.
- `Audit.lean`: the new theorems (only the project's single axiom).

### Code
- `rust/src/affine.rs`: the words of a form are its declared support (zero coefficients included), as in the Lean model; the set of words no longer depends on the challenges. Proof sizes and timings are unchanged.
- `rust/src/r1cs.rs`: test `word_count_127` (127 words, also at zero challenges).

### Note (version 10)
- Proposition affine with declared supports; the word count of Theorem r1cs; Lean status of §5.

## Unreleased — Lean formalisation of §5; optimised R1CS prototype

### Lean
- `lean/KroneckerFRI/Lincheck.lean` (no `sorry`, standard axioms only): LogUp with pairs for any finite index types (`logup_prob`, bound `(K + 2N_t - 1)/|F|`); the lincheck reduction for `J` matrices with combined lookups at the level of tables (`lincheck_reduction`, bound `((2J + 7)N - 3)/|F|`); the two-phase composition (`prob_two_phase`, `lincheck_sound`, `r1cs_sound`). Proposition affine (the batch on affine forms and public tables) is not formalised and enters as a hypothesis.
- `Audit.lean`: the new theorems.

### Code
- `rust/src/r1cs.rs`: one index tree (row, col, val of A, B, C and the combined multiplicities); one combined row lookup and one combined column lookup for the three matrices; 21 statements, 127 words (was 179), six trees per query (was eight). Transcript label `kronecker-fri-r1cs-v2`.
- `bench/r1cs.csv`: n = 16: prove 5.6 s (was 7.8), verify 44 ms (was 68), proof 1.95 MiB (was 2.6).

### Note (version 9)
- §5 for J matrices with combined lookups: Definition lin, Lemma logup (univariate proof, bound `(K + 2N_t - 1)/|F|`, as in Lean), Theorem lin (`((2J + 7)N - 3)/|F|`), Theorem r1cs (`(15N - 5 + tM)/|F| + ε_fold + (1-δ)^κ`, `char F > 3N`); new measurements; Lean status.

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
