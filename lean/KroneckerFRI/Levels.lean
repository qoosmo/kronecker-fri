/-
KroneckerFRI/Levels.lean
The setting of §5 of the paper: the levels `L_j`, the degree bounds `N_j`, the codes
`𝒞_j = RS[L_j, N_j]`, good challenges and decoding at each level, and counting and probability
tools.  Most statements are those of the KBFold formalisation (`KBFold/Soundness.lean`,
`KBFold/RBR.lean`), restated here without reference to the sumcheck.

Conventions (as in KBFold).
* The number of variables is `n = m + ℓ` (`ℓ` folding rounds, `m = n - ℓ`), and `L` is a smooth
  domain of order `M = 2^{n+R}`: `IsSmoothDomain L (m + ℓ + R)`.
* `N_j = 2^{n-j}` is `Nd m ℓ j`; `L_j = lv L j` has order `M_j = 2^{n+R-j}`; for a level `j < ℓ`
  the code `𝒞_j` is written `RS (lv L j) (2 * N_{j+1})`, the form used by `KBFold/Fibre.lean`.
* Challenges are sequences `r : ℕ → F` (`r i` is the paper's `r_{i+1}`); level `j + 1` uses
  `r j`.  The probability space `F^ℓ` is `Fin ℓ → F`, extended by `extR`.
-/
import KBFold.Protocol
import KBFold.RoundByRound

set_option autoImplicit false

open Polynomial Finset KBFold

namespace KroneckerFRI

variable {F : Type*} [Field F]

section Params

variable {L : Subgroup Fˣ} {m ℓ R : ℕ}

/-- The degree bound `N_j = 2^{n-j}` (with `n = m + ℓ`). -/
def Nd (m ℓ j : ℕ) : ℕ := 2 ^ (m + ℓ - j)

lemma Nd_pos (m ℓ j : ℕ) : 1 ≤ Nd m ℓ j := Nat.one_le_two_pow

/-- `N_j = 2 N_{j+1}` for `j < n`. -/
lemma Nd_succ {j : ℕ} (hj : j < m + ℓ) : 2 * Nd m ℓ (j + 1) = Nd m ℓ j := by
  unfold Nd
  rw [← pow_succ']; congr 1; omega

lemma Nd_last : Nd m ℓ ℓ = 2 ^ m := by unfold Nd; congr 1; omega

lemma Nd_zero : Nd m ℓ 0 = 2 ^ (m + ℓ) := rfl

/-- `|L_j| = M_j = 2^{n+R-j}`. -/
lemma card_lv (hL : IsSmoothDomain L (m + ℓ + R)) {j : ℕ} (hj : j ≤ m + ℓ + R) :
    Nat.card (lv L j) = 2 ^ (m + ℓ + R - j) :=
  lv_smooth hL hj

/-- All the codes `𝒞_j` have rate `ρ = 2^{-R}`. -/
lemma rate_lv (hL : IsSmoothDomain L (m + ℓ + R)) {j : ℕ} (hj : j ≤ m + ℓ) :
    rate (lv L j) (Nd m ℓ j) = 1 / 2 ^ R := by
  rw [rate, card_lv hL (by omega), Nd]
  have : m + ℓ + R - j = (m + ℓ - j) + R := by omega
  rw [this, pow_add]
  push_cast
  field_simp

lemma Nd_le_card (hL : IsSmoothDomain L (m + ℓ + R)) {j : ℕ} (hj : j ≤ m + ℓ) :
    Nd m ℓ j ≤ Nat.card (lv L j) := by
  rw [card_lv hL (by omega), Nd]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `|L_j| = 2 |L_{j+1}|` for `j < n + R`. -/
lemma card_lv_succ (hL : IsSmoothDomain L (m + ℓ + R)) {j : ℕ} (hj : j < m + ℓ + R) :
    Nat.card (lv L j) = 2 * Nat.card (lv L (j + 1)) := by
  rw [card_lv hL hj.le, card_lv hL hj, ← pow_succ']; congr 1; omega

/-- `M = 2^j M_j`. -/
lemma card_L_eq (hL : IsSmoothDomain L (m + ℓ + R)) {j : ℕ} (hj : j ≤ m + ℓ + R) :
    Nat.card L = 2 ^ j * Nat.card (lv L j) := by
  rw [show Nat.card L = Nat.card (lv L 0) from rfl, card_lv hL (by omega),
    card_lv hL hj, ← pow_add]
  congr 1; omega

/-- The fold lemmas of `KBFold/Fibre.lean` apply at every level `j < ℓ`. -/
lemma level_facts (hL : IsSmoothDomain L (m + ℓ + R)) {j : ℕ} (hj : j < ℓ) :
    IsSmoothDomain (lv L j) (m + ℓ + R - j) ∧ 1 ≤ m + ℓ + R - j ∧
      2 * Nd m ℓ (j + 1) ≤ Nat.card (lv L j) ∧
      rate (sqDom (lv L j)) (Nd m ℓ (j + 1)) = 1 / 2 ^ R :=
  ⟨lv_smooth hL (by omega), by omega, by rw [Nd_succ (by omega)]; exact Nd_le_card hL (by omega),
    rate_lv hL (j := j + 1) (by omega)⟩

/-- The power map `ξ ↦ ξ^{2^j}` is `2^j`-to-one from `L` onto `L_j` (Lemma 2.8(2)). -/
theorem ncard_preimage_ptAt {μ : ℕ} (hL : IsSmoothDomain L μ) :
    ∀ j ≤ μ, ∀ T : Set (lv L j), ((fun ξ : L => ptAt ξ j) ⁻¹' T).ncard = 2 ^ j * T.ncard
  | 0, _, T => by simp only [pow_zero, one_mul]; rfl
  | j + 1, hj, T => by
      haveI := hL.finite
      haveI := lv_finite (L := L) j
      have e : ((fun ξ : L => ptAt ξ (j + 1)) ⁻¹' T) =
          (fun ξ : L => ptAt ξ j) ⁻¹' (sqPt ⁻¹' T) := rfl
      rw [e, ncard_preimage_ptAt hL j (by omega),
        ncard_preimage_sqPt (lv_neg_one_mem hL (by omega)) (two_ne_zero_of_smooth hL (by omega)),
        pow_succ]
      ring

end Params

/-! ### Good challenges and decoding at level `j` (Definitions 5.13, 5.17) -/

section Good

variable {L : Subgroup Fˣ} (ℓ : ℕ) (δ : ℚ)

/-- **Definition 5.17 at level `j+1`:** `r` is good for the word `w ∈ F^{L_j}`. -/
def GoodAt (m : ℕ) (j : ℕ) (w : lv L j → F) (r : F) : Prop := Good δ (Nd m ℓ (j + 1)) w r

/-- **Definition 5.13 at level `j`:** the decoded codeword `dec_j(w)`, for `w ∈ F^{L_j}`, `j < ℓ`. -/
noncomputable def decAt (m : ℕ) (j : ℕ) (w : lv L j → F) : lv L j → F :=
  dec (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set (lv L j → F)) δ w

variable {ℓ δ}

/-- **Lemma 5.18 (few bad challenges) at level `j+1`:** at most `M_{j+1}` values are not good. -/
theorem card_badFold_le [Fintype F] {m R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) {j : ℕ} (hj : j < ℓ) (w : lv L j → F) :
    {c : F | ¬ GoodAt ℓ δ m j w c}.ncard ≤ Nat.card (lv L (j + 1)) := by
  obtain ⟨hDj, hμj, hdD, hrate⟩ := level_facts hL hj
  have hδj : δ ≤ (1 - rate (sqDom (lv L j)) (Nd m ℓ (j + 1))) / 2 := by rw [hrate]; exact hδ
  exact ncard_not_good_le hDj hμj (Nd_pos _ _ _) hdD hδ0 hδj w

end Good

/-- A sequence of words `c_j` on the levels with `fold_{r_{j+1}}(c_j) = c_{j+1}` is the sequence
of successive folds of `c_0`. -/
lemma foldUp_of_chain {L : Subgroup Fˣ} {ℓ : ℕ} (r : ℕ → F) (c : (j : ℕ) → lv L j → F)
    (h : ∀ j < ℓ, wfold (r j) (c j) = c (j + 1)) : ∀ j ≤ ℓ, c j = foldUp r (c 0) j
  | 0, _ => rfl
  | j + 1, hj => by
      rw [foldUp, ← foldUp_of_chain r c h j (by omega), h j (by omega)]

/-! ### Probability tools -/

section ProbTools

lemma prob_fst {A B : Type*} [Fintype A] [Fintype B] [Nonempty B] (E : A → Prop) :
    prob (fun p : A × B => E p.1) = prob E := by
  classical
  have e : (univ.filter fun p : A × B => E p.1) = (univ.filter E) ×ˢ (univ : Finset B) := by
    ext p; simp
  rw [prob_def, prob_def, e, card_product, Fintype.card_prod]
  have hB : (Fintype.card B : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  push_cast
  rw [card_univ, mul_div_mul_right _ _ hB]

lemma card_filter_eq_ncard {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (univ.filter p).card = {a | p a}.ncard := by
  rw [← Set.ncard_coe_finset]; congr 1; ext a; simp

/-- The geometric sum `∑_{j=1}^{ℓ} M_j = M (1 - 2^{-ℓ})`, with `M = 2^μ`, `M_j = 2^{μ-j}`. -/
theorem sum_Mj (μ : ℕ) : ∀ ℓ ≤ μ,
    ∑ j ∈ range ℓ, (2 : ℚ) ^ (μ - (j + 1)) = 2 ^ μ * (1 - 1 / 2 ^ ℓ)
  | 0, _ => by simp
  | ℓ + 1, h => by
      rw [sum_range_succ, sum_Mj μ ℓ (by omega)]
      have e : (2 : ℚ) ^ μ = 2 ^ (μ - (ℓ + 1)) * 2 ^ (ℓ + 1) := by
        rw [← pow_add]; congr 1; omega
      rw [e, pow_succ]
      field_simp
      ring

/-- `ε_fold = ∑_{j=1}^{ℓ} M_j / |F|` (§5.6), with `M_j = 2^{μ-j}`. -/
noncomputable def epsFold (F : Type*) [Fintype F] (μ ℓ : ℕ) : ℚ :=
  ∑ j ∈ range ℓ, (2 : ℚ) ^ (μ - (j + 1)) / Fintype.card F

/-- `ε_fold = M (1 - 2^{-ℓ}) / |F|`. -/
theorem epsFold_eq (F : Type*) [Fintype F] {μ ℓ : ℕ} (h : ℓ ≤ μ) :
    epsFold F μ ℓ = 2 ^ μ * (1 - 1 / 2 ^ ℓ) / Fintype.card F := by
  rw [epsFold, ← sum_div, sum_Mj μ ℓ h]

/-- `ε_fold < M / |F|`. -/
theorem epsFold_lt (F : Type*) [Fintype F] [Nonempty F] {μ ℓ : ℕ} (h : ℓ ≤ μ) :
    epsFold F μ ℓ < 2 ^ μ / Fintype.card F := by
  have hF : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [epsFold_eq F h]
  apply div_lt_div_of_pos_right _ hF
  have : (0 : ℚ) < 1 / 2 ^ ℓ := by positivity
  have : (0 : ℚ) < 2 ^ μ := by positivity
  nlinarith

lemma epsFold_nonneg (F : Type*) [Fintype F] (μ ℓ : ℕ) : 0 ≤ epsFold F μ ℓ := by
  unfold epsFold; positivity

end ProbTools

end KroneckerFRI
