# Lean 4 formalisation of Kronecker-FRI

Machine-checked proofs of the results of §4–§7 and §11 of the paper
[`../paper/kronecker-fri.pdf`](../paper/kronecker-fri.pdf): the extraction identity, the
folding proximity test with any folding arity, the scheme, completeness, soundness,
round-by-round knowledge soundness, evaluation binding, and batched openings; and the
sumcheck-free inner-product protocol `Π_IP`, Hadamard check `Π_Had` and batched protocol `Π_Batch`
of the research note [`../notes/inner-product/note.pdf`](../notes/inner-product/note.pdf) (§1–4).

- **Toolchain:** Lean 4.23.0, Mathlib `v4.23.0` (pinned in `lakefile.lean` and `lake-manifest.json`).
- **No `sorry`.**
- **One axiom:** `KBFold.bciks_curves` in `KBFold/BCIKS.lean`. It is correlated agreement for curves in the unique-decoding regime (paper, Theorem 2.16; Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, J. ACM 2023, Thm 1.5 with Thm 1.2). The line version used by the folding test is derived from it (`bciks_unique`).
- `KroneckerFRI/Audit.lean` prints the axioms of every main theorem. The expected output is a subset of `[propext, Classical.choice, Quot.sound, KBFold.bciks_curves]`, and CI checks this.

## Build

```bash
cd lean
lake exe cache get      # prebuilt Mathlib
lake build              # builds KBFold/* and KroneckerFRI/*
lake env lean KroneckerFRI/Audit.lean
```

## Layout

| Directory | Contents |
|---|---|
| `KBFold/` | Modules shared with the KBFold formalisation ([qoosmo/kbfold](https://github.com/qoosmo/kbfold)): multilinear tables, smooth domains, Reed–Solomon codes, the kernel fold of words, fibre distance, decoding, good challenges, probability lemmas (Lemmas 3.2–3.4), and the generic IOP framework (Definitions 3.1, 3.5–3.7, 3.10, Lemmas 3.8, 3.11). Their docstrings use the numbering of the KBFold paper. Only `BCIKS.lean` differs from KBFold: its axiom is the curve version, and the line version is a theorem. |
| `KroneckerFRI/` | The results of this paper (table below). Docstrings use the numbering of this paper. |

## Paper ↔ Lean

| Paper | Lean | File |
|---|---|---|
| Def 4.1, Lem 4.2 (Kronecker encoding, substitution, linear bijection) | `kronEnc`, `kronEnc_eq_subst`, `kronEncLin_bijective`, `kronCoeffs_kronEnc`, `kronEnc_kronCoeffs` | `Kronecker.lean` |
| Def 4.3, Lem 4.4 (kernel polynomial: degree, recursion, coefficient rule) | `kernel`, `kernel_monic`, `natDegree_kernel`, `kernel_recursion`, `coeff_kernel_bits` | `Kronecker.lean` |
| **Thm 4.5 (extraction identity)** | `extraction`, `extraction'`, `extraction_table` | `Kronecker.lean` |
| Cor 4.6, Cor 4.7, Prop 4.8, Lem 4.14 | `extraction_comb`, `cube_sum`, `cube_sum_half`, `bilinear`, `kernel_mul_neg`, `kernel_reflect` | `Kronecker.lean` |
| **Lem 4.10 (split)**, Def 4.11 | `split_iff`, `split_unique`, `split_eq`, `openA_coeff_zero`, `openH_mem_pred`, `openA`, `openH` | `Opening.lean` |
| **Lem 4.12 (identity lemma)**, Rem 4.13 | `Phi_mem_degreeLT`, `identity_lemma`, `identity_lemma_eval`, `without_X_absorbs` | `Opening.lean` |
| Def 5.1–Prop 5.4 (kernel fold, line form, consistency) | `wfold`, `wfold_sqPt`, `wfold_line`, `wfold_ev` | `KBFold/WordFold.lean` |
| **Lem 5.5 (iterated fold)** | `coeff_pfoldUp`, `pfoldUp_mem_degreeLT`, `foldUp_ev_smooth` | `IteratedFold.lean` |
| Def 5.7, Lem 5.9(1) (the test, completeness) | `FTProver`, `FTProver.Accepts`, `honestFT_accepts` | `FoldTest.lean` |
| Def 5.10–Lem 5.19 (fibre distance, decoding, far words, good challenges, one step) | `fibDist`, `fibDist_le_iff`, `fib_unique`, `dec`, `far_fold`, `survive`, `Good`, `ncard_not_good_le`, `one_step`, `GoodAt`, `decAt`, `card_badFold_le` | `KBFold/Fibre.lean`, `Levels.lean` |
| Def 5.20, Lem 5.21 (witness sets, fold checks) | `Wset`, `dens`, `queryOK_iff`, `prob_accepts_fixed` | `FoldTest.lean` |
| Lem 5.22, **Prop 5.23 (codeword chain)** | `rbr_step`, `chain`, `chain_final` | `FoldTest.lean` |
| **Thm 5.24 (soundness of the folding test)** | `prob_notGood_le`, `dens_lt_of_far`, `fpt_sound` | `FoldTest.lean` |
| Def 5.27, **Prop 5.28 (virtual levels, arity 2^k)** | `orcC`, `FTProver.induced`, `FTProver.AcceptsC`, `acceptsC_iff`, `induced_Chk_virtual`, `acceptsC_congr`, `orcC_virtual_local`, `fptC_sound`, `sum_arity_lengths_lt` | `Arity.lean` |
| Def 6.2, Lem 6.3(1)–(2) (encoding) | `encode`, `polyOf_encode`, `encode_injective`, `encode_surj`, `encode_fib_unique`, `encode_unique` | `Scheme.lean` |
| Def 6.5, Lem 6.6 (virtual word) | `virt`, `virt_identity`, `virt_congr`, `virt_honest`, `virt_add`, `virt_smul` | `Scheme.lean` |
| Def 6.8 (Π_KF), Rem 6.9(1), **Thm 6.10 (completeness)** | `KFProver`, `KFProver.Accepts`, `wbat`, `virt_wrong_value`, `inv_agree_le`, `honestKF_accepts`, `honestKF_prob_one` | `Scheme.lean` |
| Def 7.1, Lem 7.2, Lem 7.3 | `RelKF`, `rate_condition`, `value_of_agreement` | `Scheme.lean`, `Soundness.lean` |
| **Lem 7.4 (batching)** | `goodBeta`, `batching`, `batching_witness` | `Soundness.lean` |
| Lem 7.7, **Thm 7.8 (soundness)** | `negPt_mem_Wset`, `epsKF`, `soundness`, `soundnessC` (any set of committed levels) | `FoldTest.lean`, `Soundness.lean` |
| Def 7.9, Lem 7.10 (doomed set, extractor) | `NotDoomedFT`, `extKF`, `extKF_eq`, `extKF_witness` | `RBR.lean` |
| **Thm 7.11 (round-by-round knowledge soundness)** | `rbr_item1`, `rbr_item2`, `rbr_item3`; in the framework of Def 3.7: `rbr_knowledge`, `rbr_knowledge'` | `RBR.lean`, `Generic.lean` |
| **Cor 7.12 (knowledge, soundness, binding)** | `knowledge`, `soundness`, `binding`; framework form `rbr_binding` | `RBR.lean`, `Generic.lean` |
| Def 11.1, **Thm 11.2, Cor 11.3 (batched openings)** | `wGamma`, `RelBatch`, `accProbBatch`, `wGamma_encode`, `batch_soundness`, `batch_knowledge`, `batch_binding` | `Batch.lean` |

## Research note: sumcheck-free inner products, Hadamard checks and batches (table form)

| Note | Lean | File |
|---|---|---|
| Def (table encoding): `V_f = ∑_w f(w) X^w`, `Enc^T(f) = ev_L(V_f)` | `kronEnc`, `encode` (same maps as the coefficient form) | `Kronecker.lean`, `Scheme.lean` |
| **Lemma eval** (`f~(z) = [X^{N-1}] V_f E*_z`) | `evalKer`, `coeff_evalKer_compl`, `eval_table` | `TableForm.lean` |
| Def (reversal), `(P*)* = P`, `P*(x) = x^{N-1} P(1/x)` | `revP`, `revP_revP`, `eval_revP` | `TableForm.lean` |
| **Lemma ip** (`∑_w a(w) b(w) = [X^{N-1}] V_a V_b*`) | `inner_product` | `TableForm.lean` |
| **Lemma gen-identity** (split and identity for any `K ∈ F[X]_{<N}`) | `splitG_eq`, `splitG_iff`, `PhiG`, `natDegree_PhiG_le`, `identityG` | `TableForm.lean` |
| **Lemma rev** (reversed words) | `invPt`, `wrev`, `wrev_ev`, `wrev_wrev`, `wrev_eq_iff`, `inv_image_closed`, `ncard_inv_image` | `TableForm.lean` |
| Def (`Π_IP`), virtual word, locality | `virtIP`, `virtIP_identity`, `virtIP_congr`, `wbatIP`, `AcceptsIP`, `accProbIP`, `AcceptsIPC` | `InnerProduct.lean` |
| **Thm (completeness)** | `virtIP_honest`, `wbatIP_honest`, `honestIP_accepts`, `honestIP_prob_one` | `InnerProduct.lean` |
| Def (relation `R^δ_IP`) | `RelIP`, `RelIP_unique` | `InnerProduct.lean` |
| Correlated agreement on a common fibre-closed set (any degree `t`) | `curve_agreement` | `InnerProduct.lean` |
| **Lemma batch3 (batching, degree 3)** | `goodBetaIP`, `batching_IP`, `card_goodBetaIP_le` | `InnerProduct.lean` |
| **Thm (soundness)**, `ε_IP = 3M/\|F\| + ε_fold + (1-δ)^κ` | `epsIP`, `epsIP_lt`, `soundness_IP`, `soundnessC_IP` (any set of committed levels) | `InnerProduct.lean` |
| Knowledge and binding | `knowledge_IP`, `binding_IP` | `InnerProduct.lean` |
| Def (quotient words), **Lemma deep** (DEEP step on an agreement set, and its converse) | `qword`, `deep_step`, `deep_honest`, `divq`, `divq_mem` | `Hadamard.lean` |
| Geometric weights: `V_a(γX)`, `∑_w γ^w a(w) b(w) = [X^{N-1}] V_a(γX) V_b*` | `gscale`, `eval_gscale`, `weighted_inner_product` | `Hadamard.lean` |
| Def (`Π_Had`), relation `R^δ_Had` | `curveHad`, `wbatHad`, `HadProver`, `HadProver.Accepts`, `HadProver.accProb`, `HadProver.AcceptsC`, `RelHad` | `Hadamard.lean` |
| **Thm (completeness)**: accepted when no pole lies in `L`; probability `≥ 1 - 3M/\|F\|` | `hadPolys`, `hadU0`, `curveHad_honest`, `wbatHad_honest`, `honestHad_accepts`, `honestHad_prob` | `Hadamard.lean` |
| **Lemma batch8 (batching, degree 8)** | `batching_Had` | `Hadamard.lean` |
| KF Thm 7.8 for any family of words `w_0(β)` | `goodSet`, `ft_family_bound` | `Hadamard.lean` |
| **Thm had (soundness)**, `2(N-1)/\|F\| + 8M/\|F\| + ε_fold + (1-δ)^κ`; knowledge | `prob_bad_le`, `soundness_Had`, `soundnessC_Had` (any set of committed levels), `knowledge_Had` | `Hadamard.lean` |
| Correlated agreement for words indexed by a finite type | `curve_agreement_idx` | `BatchStmts.lean` |
| Def (statements, `R^δ_Batch`), the words of `Π_Batch` | `BStmt`, `BStmt.Holds`, `Dset`, `Bset`, `Hpos`, `BWord`, `card_BWord`, `RelBatchS`, `virtG`, `bwords`, `benum`, `wbatB`, `BProver` | `BatchStmts.lean` |
| **Lemma batchT (batching, degree t)** | `virtG_value`, `batching_B` | `BatchStmts.lean` |
| **Thm batch (soundness)**, `2(N-1)/\|F\| + tM/\|F\| + ε_fold + (1-δ)^κ`; knowledge | `prob_bad_had`, `prob_bad_B`, `soundness_B`, `soundnessC_B` (any set of committed levels), `knowledge_B` | `BatchStmts.lean` |
| **Thm (completeness)**: accepted when no pole of a Hadamard check lies in `L`; probability `≥ 1 - 3M/\|F\|` | `bpolys`, `bU0`, `honestB`, `bwords_honest`, `honestB_accepts`, `prob_poles_ge`, `honestB_prob` | `BatchStmts.lean` |

## Modelling

- **Numbering.** The number of variables is `n = m + ℓ`, where ℓ ≥ 1 is the number of folding rounds. `L` is a subgroup of `Fˣ` of order `2^{n+R}`. Challenges are sequences `r : ℕ → F`, where `r i` is the paper's `r_{i+1}`.
- **Deterministic provers.** A deterministic prover is given by its messages as functions of the challenges: `FTProver` and `KFProver`. Two properties are hypotheses:
  - `Causal`: a message depends only on earlier challenges.
  - `DegOK`: the final polynomial has fewer than `N_ℓ` coefficients.

  In the generic IOP framework (`Generic.lean`) the prover is an arbitrary function of the transcript, and the verifier checks the degree itself, so neither hypothesis is needed there.
- **Distance.** δ is a rational number, which is enough since δ* = (1-ρ)/2 is rational.

## Not formalised

- Operation counts: Lem 4.9, Lem 5.9(2)–(3), Lem 6.7, Prop 6.11.
- The base-field statements: Lem 2.14, Lem 6.3(3), Rem 7.13. There is no separate base field `F_q` in the model.
- The running time of the extractor.
- The post-quantum analysis of §8. It rests on the BCS theorem of Chiesa, Di, Hu and Zheng (Thm 3.15), which has no Lean formalisation.
