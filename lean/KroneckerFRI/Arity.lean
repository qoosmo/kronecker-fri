/-
KroneckerFRI/Arity.lean
§5.7 of the paper: virtual levels and higher folding arity (Definition 5.27, Proposition 5.28).

`C : Set ℕ` is the set of committed levels (the paper's `C ⊆ [1, ℓ-1]`; elements outside that
range are ignored).  A prover of `Π^C_FT` is an `FTProver` whose oracles are used only at the
levels of `C`; at the other levels the word is virtual, the exact fold of the previous one.
-/
import KroneckerFRI.FoldTest

set_option autoImplicit false

open Polynomial Finset KBFold

namespace KroneckerFRI

variable {F : Type*} [Field F] {L : Subgroup Fˣ}

open Classical in
/-- The words of `Π^C_FT` below level `ℓ`: `w_0 = w₀`, `w_j = orc j` for `j ∈ C`, and the virtual
word `w_j = fold_{r_j}(w_{j-1})` otherwise (Definition 5.27). -/
noncomputable def orcC (P : FTProver F L) (C : Set ℕ) (w0 : L → F) (r : ℕ → F) :
    (j : ℕ) → lv L j → F
  | 0 => w0
  | j + 1 => if j + 1 ∈ C then P.orc (j + 1) r else wfold (r j) (orcC P C w0 r j)

/-- **Proposition 5.28(1), the induced prover:** the prover of `Π_FT` that sends the words of
`P` at the levels of `C` and the virtual words at the other levels. -/
noncomputable def FTProver.induced (P : FTProver F L) (C : Set ℕ) (w0 : L → F) : FTProver F L :=
  ⟨fun j r => orcC P C w0 r j, P.fin⟩

open Classical in
/-- **Definition 5.27:** the verifier of `Π^C_FT` makes the fold checks of the levels
`j + 1 ∈ C ∪ {ℓ}` only.  At such a level it computes `ŵ_{j+1}(ξ^{2^{j+1}})` from the last
committed word by successive folds, which is the value `what` of the induced prover
(`induced_what_local` gives the points it reads). -/
def FTProver.AcceptsC (P : FTProver F L) (C : Set ℕ) (ℓ : ℕ) (w0 : L → F) {κ : ℕ} (r : ℕ → F)
    (ξ : Fin κ → L) : Prop :=
  ∀ t, ∀ j < ℓ, (j + 1 ∈ C ∨ j + 1 = ℓ) → (P.induced C w0).Chk ℓ w0 r j (ptAt (ξ t) (j + 1))

/-- The acceptance probability of `Π^C_FT`. -/
noncomputable def FTProver.accProbC [Fintype F] [Fintype L] (P : FTProver F L) (C : Set ℕ)
    (ℓ : ℕ) (w0 : L → F) (κ : ℕ) : ℚ :=
  prob (fun ω : (Fin ℓ → F) × (Fin κ → L) => P.AcceptsC C ℓ w0 (extR ω.1) ω.2)

variable (P : FTProver F L) (C : Set ℕ) (ℓ : ℕ) (w0 : L → F)

/-- The words of the induced prover at a virtual level `j + 1 < ℓ` are the exact folds. -/
theorem induced_W_virtual (r : ℕ → F) {j : ℕ} (hC : j + 1 ∉ C) (hℓ : j + 1 < ℓ) :
    (P.induced C w0).W ℓ w0 r (j + 1) = (P.induced C w0).what ℓ w0 r j := by
  have hW : ∀ i, i ≠ ℓ → (P.induced C w0).W ℓ w0 r i = orcC P C w0 r i := by
    intro i hi
    cases i with
    | zero => rfl
    | succ i => simp only [FTProver.W, FTProver.induced, if_neg hi]
  rw [hW (j + 1) (by omega), FTProver.what, hW j (by omega)]
  simp only [orcC, if_neg hC]

/-- **Proposition 5.28(2):** `ℬ_{j+1} = ∅` at every virtual level `j + 1`. -/
theorem induced_Chk_virtual (r : ℕ → F) {j : ℕ} (hC : j + 1 ∉ C) (hℓ : j + 1 < ℓ)
    (η : lv L (j + 1)) : (P.induced C w0).Chk ℓ w0 r j η := by
  simp only [FTProver.Chk, induced_W_virtual P C ℓ w0 r hC hℓ]

/-- **Proposition 5.28(1):** for all challenges, the verifier of `Π^C_FT` accepts `P` iff the
verifier of `Π_FT` accepts the induced prover. -/
theorem acceptsC_iff {κ : ℕ} (r : ℕ → F) (ξ : Fin κ → L) :
    P.AcceptsC C ℓ w0 r ξ ↔ (P.induced C w0).Accepts ℓ w0 r ξ := by
  constructor
  · intro h t j hj
    by_cases hc : j + 1 ∈ C ∨ j + 1 = ℓ
    · exact h t j hj hc
    · push_neg at hc
      exact induced_Chk_virtual P C ℓ w0 r hc.1 (by omega) _
  · intro h t j hj _
    exact h t j hj

theorem accProbC_eq [Fintype F] [Fintype L] (κ : ℕ) :
    P.accProbC C ℓ w0 κ = (P.induced C w0).accProb ℓ w0 κ := by
  unfold FTProver.accProbC FTProver.accProb
  congr 1
  funext ω
  exact propext (acceptsC_iff P C ℓ w0 _ _)

/-- The induced prover is causal when `P` is. -/
theorem induced_causal (hC : P.Causal) : (P.induced C w0).Causal := by
  intro j r r' h
  simp only [FTProver.induced]
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [orcC]
    split_ifs
    · exact hC (j + 1) r r' h
    · rw [ih (fun k hk => h k (by omega)), h j (by omega)]

theorem induced_DegOK {m : ℕ} (hdeg : P.DegOK m) : (P.induced C w0).DegOK m := hdeg

/-- **Proposition 5.28(2), Theorem 5.24 for `Π^C_FT`:** if `Δ^fib₀(w₀, 𝒞₀) > δ`, the verifier of
`Π^C_FT` accepts a causal prover with probability at most `ε_fold + (1-δ)^κ`, the bound of
`Π_FT`. -/
theorem fptC_sound [Fintype F] [DecidableEq F] [Fintype L] {m R : ℕ} {δ : ℚ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hC : P.Causal) (hdeg : P.DegOK m) (κ : ℕ)
    (hfar : ¬ FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ) :
    P.accProbC C ℓ w0 κ ≤ epsFold F (m + ℓ + R) ℓ + (1 - δ) ^ κ := by
  rw [accProbC_eq]
  exact fpt_sound hL hℓ hδ0 hδ (induced_causal P C w0 hC) (induced_DegOK P C w0 hdeg) κ hfar

/-- **Proposition 5.28(3), points read:** at a level `j' + k` with previous committed level `j'`,
the value `ŵ_{j'+k}` computed by the verifier depends only on `w_{j'}` at the `2^k` points above
(stated for the folds of a word `w` on a domain `D`, applied with `D = L_{j'}`). -/
theorem induced_what_local {D : Subgroup Fˣ} (r : ℕ → F) {w w' : D → F} (k : ℕ) (η : lv D k)
    (h : ∀ ξ : D, ptAt ξ k = η → w ξ = w' ξ) : foldUp r w k η = foldUp r w' k η :=
  foldUp_congr_pts r k η h

/-- The point `η^{2^k}` of `L_{j+k}` for `η ∈ L_j`. -/
def ptUp {j : ℕ} : (k : ℕ) → lv L j → lv L (j + k)
  | 0, ζ => ζ
  | k + 1, ζ => sqPt (ptUp k ζ)

/-- **Proposition 5.28(1)–(3), what the verifier of `Π^C_FT` reads:** if the levels
`j' + 1, …, j' + k` are virtual, the word at level `j' + k` at a point `η` is determined by the
word at level `j'` at the `2^k` points `ζ` with `ζ^{2^k} = η`; so the value `ŵ_{j'+k+1}(η')` of a
fold check is computed from the last committed word by successive folds. -/
theorem orcC_virtual_local (P P' : FTProver F L) (C : Set ℕ) (w0 w0' : L → F) (r : ℕ → F)
    {j' : ℕ} : ∀ (k : ℕ) (η : lv L (j' + k)), (∀ i, 0 < i → i ≤ k → j' + i ∉ C) →
      (∀ ζ : lv L j', ptUp k ζ = η → orcC P C w0 r j' ζ = orcC P' C w0' r j' ζ) →
      orcC P C w0 r (j' + k) η = orcC P' C w0' r (j' + k) η
  | 0, η, _, h => h η rfl
  | k + 1, η, hC, h => by
      have hk : j' + k + 1 ∉ C := hC (k + 1) (by omega) le_rfl
      show orcC P C w0 r (j' + k + 1) η = orcC P' C w0' r (j' + k + 1) η
      simp only [orcC]
      rw [if_neg hk, if_neg hk]
      refine wfold_congr _ (fun ζ hζ => orcC_virtual_local P P' C w0 w0' r k ζ
        (fun i hi hik => hC i hi (by omega)) (fun ζ0 hζ0 => h ζ0 ?_))
      show sqPt (ptUp k ζ0) = η
      rw [hζ0]; exact hζ

/-- **Proposition 5.28(1):** the verifier of `Π^C_FT` reads only the oracles at the committed
levels: two provers with the same committed words and final polynomial are accepted together. -/
theorem acceptsC_congr (P P' : FTProver F L) (C : Set ℕ) (ℓ : ℕ) (w0 : L → F) {κ : ℕ}
    (r : ℕ → F) (ξ : Fin κ → L) (hC : ∀ j ∈ C, P.orc j r = P'.orc j r) (hfin : P.fin r = P'.fin r) :
    P.AcceptsC C ℓ w0 r ξ ↔ P'.AcceptsC C ℓ w0 r ξ := by
  have horc : ∀ j, orcC P C w0 r j = orcC P' C w0 r j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      simp only [orcC]
      split_ifs with h
      · exact hC _ h
      · rw [ih]
  have hW : ∀ j, (P.induced C w0).W ℓ w0 r j = (P'.induced C w0).W ℓ w0 r j := by
    intro j
    cases j with
    | zero => rfl
    | succ j => simp only [FTProver.W, FTProver.induced, hfin, horc]
  simp only [FTProver.AcceptsC, FTProver.Chk, FTProver.what, hW]

/-- **Proposition 5.28(3), oracle length:** for arity `2^k` the committed levels are
`k, 2k, …`, of total length `∑_{i ≥ 1} M_{ik} = M ∑_{i≥1} 2^{-ik} < M / (2^k - 1)`. -/
theorem sum_arity_lt {k : ℕ} (hk : 1 ≤ k) (t : ℕ) :
    ∑ i ∈ range t, ((1 : ℚ) / 2 ^ k) ^ (i + 1) < 1 / (2 ^ k - 1) := by
  set x : ℚ := 1 / 2 ^ k
  have h2k : (2 : ℚ) ≤ 2 ^ k := by
    calc (2 : ℚ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have key : ∀ t, (∑ i ∈ range t, x ^ (i + 1)) * (1 - x) = x * (1 - x ^ t) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [sum_range_succ, add_mul, ih]; ring
  have hxt : 0 < x ^ t := pow_pos hx0 t
  have h1x : 0 < 1 - x := by linarith
  have e : 1 / (2 ^ k - 1 : ℚ) = x / (1 - x) := by
    simp only [x]
    have : (2 : ℚ) ^ k - 1 ≠ 0 := by linarith
    field_simp
  rw [e, lt_div_iff₀ h1x, key t]
  nlinarith

/-- **Proposition 5.28(3), oracle length:** for arity `2^k` the committed levels are
`k, 2k, …, tk`, with `M_{k(i+1)} = 2^μ / 2^{k(i+1)}`, and their total length is less than
`M / (2^k - 1)`. -/
theorem sum_arity_lengths_lt {k : ℕ} (hk : 1 ≤ k) (μ t : ℕ) :
    ∑ i ∈ range t, (2 : ℚ) ^ μ / 2 ^ (k * (i + 1)) < 2 ^ μ / (2 ^ k - 1) := by
  have h := sum_arity_lt hk t
  have hμ : (0 : ℚ) < 2 ^ μ := by positivity
  have e : ∀ i, (2 : ℚ) ^ μ / 2 ^ (k * (i + 1)) = 2 ^ μ * ((1 : ℚ) / 2 ^ k) ^ (i + 1) := by
    intro i; rw [pow_mul, div_pow, one_pow]; ring
  simp_rw [e, ← mul_sum]
  rw [div_eq_mul_one_div (2 ^ μ : ℚ)]
  exact mul_lt_mul_of_pos_left h hμ

end KroneckerFRI
