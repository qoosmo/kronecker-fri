/-
KroneckerFRI/Lincheck.lean
§5 of the research note "Sumcheck-free hypercube inner products": LogUp with pairs
(Lemma logup) and the lincheck reduction (Theorem lin) at the level of tables.

Modelling.
* Tables are functions `W → F` on a finite index set `W` with a numbering `num : W → ℕ`
  (injective, values `< |W|`); the integer `num w` is read in `F`.
* A sparse matrix is given by `row col : W → W` and `val : W → F` (entry `k` is
  `(row k, col k, val k)`, padding entries have `val = 0`); `(M z)(w) = ∑_{k : row k = w} val k · z(col k)`.
* A deterministic prover: the round-1 tables `e, ζ, p` are functions of `η`; the round-2 tables
  `φ^R, ψ^R, φ^C, ψ^C` and the value `s` are functions of all the challenges.
* The challenge space is `F × ((F × F) × (F × F))`: `η`, then `(y_R, x_R)` and `(y_C, x_C)`.
-/
import KroneckerFRI.BatchStmts

set_option autoImplicit false

open Polynomial Finset KBFold

namespace KroneckerFRI

variable {F : Type*} [Field F]

/-! ### LogUp with pairs (Lemma logup) -/

section LogUp

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The LogUp event at `(x, y)`: all denominators are nonzero and
`∑_k 1/(x - α_k - y α'_k) = ∑_w m_w/(x - ω_w - y ω'_w)`. -/
def LogupEq (α α' : ι → F) (ω ω' m : κ → F) (x y : F) : Prop :=
  (∀ k, x - α k - y * α' k ≠ 0) ∧ (∀ w, x - ω w - y * ω' w ≠ 0) ∧
    ∑ k, (x - α k - y * α' k)⁻¹ = ∑ w, m w * (x - ω w - y * ω' w)⁻¹

omit [Field F] in
lemma prob_snd {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] (E : B → Prop) :
    prob (fun p : A × B => E p.2) = prob E := by
  classical
  have e : (univ.filter fun p : A × B => E p.2) = (univ : Finset A) ×ˢ (univ.filter E) := by
    ext p; simp
  rw [prob_def, prob_def, e, card_product, Fintype.card_prod]
  have hA : (Fintype.card A : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  push_cast
  rw [card_univ, mul_div_mul_left _ _ hA]

/-- The univariate numerator: for a fixed `y`, with `c_k = α_k + y α'_k`, `t_w = ω_w + y ω'_w`,
`S` the set of the `c_k` and `n_c` the number of `k` with `c_k = c`,
`Num = ∑_{c ∈ S} n_c ∏_{S∖c} (X - c') ∏_w (X - t_w) - ∑_w m_w ∏_S (X - c) ∏_{v ≠ w} (X - t_v)`. -/
noncomputable def logupNum [DecidableEq F] (c : ι → F) (t m : κ → F) : F[X] :=
  ∑ a ∈ univ.image c, C (((univ.filter fun k => c k = a).card : ℕ) : F) *
      (∏ b ∈ (univ.image c).erase a, (X - C b)) * ∏ w, (X - C (t w)) -
    ∑ w, C (m w) * (∏ b ∈ univ.image c, (X - C b)) * ∏ v ∈ univ.erase w, (X - C (t v))

lemma natDegree_logupNum_le [DecidableEq F] (c : ι → F) (t m : κ → F) :
    (logupNum c t m).natDegree ≤ Fintype.card ι + Fintype.card κ - 1 := by
  have hS : (univ.image c).card ≤ Fintype.card ι := (card_image_le).trans (by simp)
  unfold logupNum
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_sum_le_of_forall_le _ _ (fun a ha => ?_)
    refine (natDegree_mul_le).trans ?_
    refine (add_le_add ((natDegree_mul_le).trans (add_le_add (natDegree_C _).le le_rfl))
      le_rfl).trans ?_
    rw [natDegree_finset_prod_X_sub_C_eq_card, natDegree_finset_prod_X_sub_C_eq_card,
      card_erase_of_mem ha, card_univ]
    have := card_pos.2 ⟨a, ha⟩
    omega
  · refine natDegree_sum_le_of_forall_le _ _ (fun w _ => ?_)
    refine (natDegree_mul_le).trans ?_
    refine (add_le_add ((natDegree_mul_le).trans (add_le_add (natDegree_C _).le le_rfl))
      le_rfl).trans ?_
    rw [natDegree_finset_prod_X_sub_C_eq_card, natDegree_finset_prod_X_sub_C_eq_card,
      card_erase_of_mem (mem_univ w), card_univ]
    have : 1 ≤ Fintype.card κ := Fintype.card_pos_iff.2 ⟨w⟩
    omega

/-- `Num ≠ 0` when some `c_{k₀}` is not a table value and the counts are nonzero in `F`. -/
lemma logupNum_ne_zero [DecidableEq F] (hchar : ∀ n : ℕ, 1 ≤ n → n ≤ Fintype.card ι → (n : F) ≠ 0)
    (c : ι → F) (t m : κ → F) (k0 : ι) (hk0 : ∀ w, c k0 ≠ t w) :
    logupNum c t m ≠ 0 := by
  classical
  intro h0
  have hev := congrArg (fun P : F[X] => P.eval (c k0)) h0
  simp only [eval_zero] at hev
  have hmem : c k0 ∈ univ.image c := mem_image_of_mem c (mem_univ k0)
  unfold logupNum at hev
  simp only [eval_sub, eval_finset_sum, eval_mul, eval_C, eval_prod, eval_X] at hev
  -- the second sum vanishes at `c_{k₀}`
  have h2 : ∑ w, m w * (∏ b ∈ univ.image c, (c k0 - b)) * ∏ v ∈ univ.erase w, (c k0 - t v) = 0 := by
    refine sum_eq_zero (fun w _ => ?_)
    rw [prod_eq_zero hmem (sub_self _)]; ring
  rw [h2, sub_zero] at hev
  rw [sum_eq_single (c k0)] at hev
  · -- the surviving term is nonzero
    have hn : ((univ.filter fun k => c k = c k0).card : F) ≠ 0 := by
      apply hchar
      · exact card_pos.2 ⟨k0, by simp⟩
      · exact (card_filter_le _ _).trans (by simp)
    have hp1 : ∏ b ∈ (univ.image c).erase (c k0), (c k0 - b) ≠ 0 :=
      prod_ne_zero_iff.2 (fun b hb => sub_ne_zero.2 (fun h => (mem_erase.1 hb).1 h.symm))
    have hp2 : ∏ w, (c k0 - t w) ≠ 0 := prod_ne_zero_iff.2 (fun w _ => sub_ne_zero.2 (hk0 w))
    exact mul_ne_zero (mul_ne_zero hn hp1) hp2 hev
  · intro a ha hne
    rw [prod_eq_zero (mem_erase.2 ⟨fun h => hne h.symm, hmem⟩) (sub_self _)]; ring
  · intro h; exact absurd hmem h

/-- If the LogUp equation holds at `x` (all denominators nonzero), then `Num(x) = 0`. -/
lemma logupNum_eval_eq_zero [DecidableEq F] (c : ι → F) (t m : κ → F) (x : F)
    (hc : ∀ k, x - c k ≠ 0) (ht : ∀ w, x - t w ≠ 0)
    (heq : ∑ k, (x - c k)⁻¹ = ∑ w, m w * (x - t w)⁻¹) :
    (logupNum c t m).eval x = 0 := by
  classical
  set S := univ.image c
  have hS : ∀ b ∈ S, x - b ≠ 0 := by
    intro b hb
    obtain ⟨k, -, rfl⟩ := mem_image.1 hb
    exact hc k
  set DS := ∏ b ∈ S, (x - b)
  set DT := ∏ w, (x - t w)
  have herS : ∀ a ∈ S, ∏ b ∈ S.erase a, (x - b) = DS * (x - a)⁻¹ := by
    intro a ha
    rw [eq_mul_inv_iff_mul_eq₀ (hS a ha), mul_comm, mul_prod_erase S (fun b => x - b) ha]
  have herT : ∀ w, ∏ v ∈ univ.erase w, (x - t v) = DT * (x - t w)⁻¹ := by
    intro w
    rw [eq_mul_inv_iff_mul_eq₀ (ht w), mul_comm, mul_prod_erase univ (fun v => x - t v) (mem_univ w)]
  -- fiberwise form of the left side
  have hfib : ∑ k, (x - c k)⁻¹ =
      ∑ a ∈ S, (((univ.filter fun k => c k = a).card : ℕ) : F) * (x - a)⁻¹ := by
    rw [sum_comp (fun a => (x - a)⁻¹) c]
    simp only [nsmul_eq_mul]
    rfl
  unfold logupNum
  simp only [eval_sub, eval_finset_sum, eval_mul, eval_C, eval_prod, eval_X]
  have e1 : ∑ a ∈ S, (((univ.filter fun k => c k = a).card : ℕ) : F) *
      (∏ b ∈ S.erase a, (x - b)) * DT = DS * DT * ∑ k, (x - c k)⁻¹ := by
    rw [hfib, mul_sum]
    refine sum_congr rfl (fun a ha => ?_)
    rw [herS a ha]; ring
  have e2 : ∑ w, m w * DS * ∏ v ∈ univ.erase w, (x - t v) =
      DS * DT * ∑ w, m w * (x - t w)⁻¹ := by
    rw [mul_sum]
    refine sum_congr rfl (fun w _ => ?_)
    rw [herT w]; ring
  rw [e1, e2, heq, sub_self]

/-- **Lemma logup (LogUp with pairs).** If some pair `(α_{k₀}, α'_{k₀})` is not a table pair and
the counts `1, …, K` are nonzero in `F` (`K = |ι|` lookups, `Nt = |κ|` table pairs), then over `(y, x)` uniform in `F²` the LogUp event has
probability at most `(Nt + K + Nt - 1)/|F|`. -/
theorem logup_prob [Fintype F] [DecidableEq F] (hchar : ∀ n : ℕ, 1 ≤ n → n ≤ Fintype.card ι → (n : F) ≠ 0)
    (α α' : ι → F) (ω ω' m : κ → F) (k0 : ι)
    (hk0 : ∀ w, ¬ (α k0 = ω w ∧ α' k0 = ω' w)) :
    prob (fun p : F × F => LogupEq α α' ω ω' m p.2 p.1) ≤
      ((Fintype.card κ + (Fintype.card ι + Fintype.card κ - 1) : ℕ) : ℚ) / Fintype.card F := by
  classical
  haveI : Nonempty F := ⟨0⟩
  set BadY : Set F := {y | ∃ w, α k0 + y * α' k0 = ω w + y * ω' w}
  have hBadY : BadY.ncard ≤ Fintype.card κ := by
    let r : κ → F := fun w => (ω w - α k0) / (α' k0 - ω' w)
    have hsub : BadY ⊆ ↑(univ.image r) := by
      intro y ⟨w, hw⟩
      rw [coe_image, coe_univ, Set.image_univ]
      refine ⟨w, ?_⟩
      by_cases hd : α' k0 = ω' w
      · exfalso; apply hk0 w; refine ⟨?_, hd⟩
        rw [hd] at hw; linear_combination hw
      · have hd' : α' k0 - ω' w ≠ 0 := sub_ne_zero.2 hd
        show (ω w - α k0) / (α' k0 - ω' w) = y
        rw [div_eq_iff hd']; linear_combination -hw
    calc BadY.ncard ≤ (↑(univ.image r) : Set F).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = (univ.image r).card := Set.ncard_coe_finset _
      _ ≤ Fintype.card κ := card_image_le.trans (by simp)
  -- for a good `y`, the `x` of the event are roots of `Num_y`
  have hgood : ∀ y, y ∉ BadY →
      {x : F | LogupEq α α' ω ω' m x y}.ncard ≤ Fintype.card ι + Fintype.card κ - 1 := by
    intro y hy
    set c : ι → F := fun k => α k + y * α' k
    set t : κ → F := fun w => ω w + y * ω' w
    have hk0' : ∀ w, c k0 ≠ t w := fun w h => hy ⟨w, h⟩
    have hne := logupNum_ne_zero hchar c t m k0 hk0'
    have hsub : {x : F | LogupEq α α' ω ω' m x y} ⊆ {x | (logupNum c t m).eval x = 0} := by
      intro x ⟨h1, h2, h3⟩
      show (logupNum c t m).eval x = 0
      refine logupNum_eval_eq_zero c t m x (fun k => ?_) (fun w => ?_) ?_
      · have := h1 k; simp only [c]; intro h; apply this; linear_combination h
      · have := h2 w; simp only [t]; intro h; apply this; linear_combination h
      · have e1 : ∀ k, x - c k = x - α k - y * α' k := fun k => by simp only [c]; ring
        have e2 : ∀ w, x - t w = x - ω w - y * ω' w := fun w => by simp only [t]; ring
        simp only [e1, e2]; exact h3
    have hdeg : logupNum c t m ∈ degreeLT F (Fintype.card ι + Fintype.card κ) := by
      rw [mem_degreeLT]
      refine (degree_le_natDegree).trans_lt ?_
      have := natDegree_logupNum_le c t m
      have hK : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.2 ⟨k0⟩
      exact_mod_cast (show (logupNum c t m).natDegree < Fintype.card ι + Fintype.card κ by omega)
    have := ncard_roots_le hdeg hne
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (by omega)
  -- the two events
  have hsplit : ∀ p : F × F, LogupEq α α' ω ω' m p.2 p.1 →
      p.1 ∈ BadY ∨ (p.1 ∉ BadY ∧ LogupEq α α' ω ω' m p.2 p.1) := by
    intro p hp
    by_cases h : p.1 ∈ BadY
    · exact Or.inl h
    · exact Or.inr ⟨h, hp⟩
  calc prob (fun p : F × F => LogupEq α α' ω ω' m p.2 p.1)
      ≤ prob (fun p : F × F => p.1 ∈ BadY ∨ (p.1 ∉ BadY ∧ LogupEq α α' ω ω' m p.2 p.1)) :=
        prob_mono hsplit
    _ ≤ prob (fun p : F × F => p.1 ∈ BadY) +
        prob (fun p : F × F => p.1 ∉ BadY ∧ LogupEq α α' ω ω' m p.2 p.1) := prob_or_le _ _
    _ ≤ (Fintype.card κ : ℚ) / Fintype.card F + ((Fintype.card ι + Fintype.card κ - 1 : ℕ) : ℚ) / Fintype.card F := by
        gcongr
        · rw [prob_fst (fun y : F => y ∈ BadY)]
          exact prob_set_le BadY hBadY
        · rw [prob_prod_eq_expect (fun y x => y ∉ BadY ∧ LogupEq α α' ω ω' m x y)]
          refine expect_le_of_le _ _ (fun y => ?_)
          by_cases hy : y ∈ BadY
          · have : (fun x : F => y ∉ BadY ∧ LogupEq α α' ω ω' m x y) = fun _ => False := by
              funext x; simp [hy]
            rw [this, prob_false]; positivity
          · have : (fun x : F => y ∉ BadY ∧ LogupEq α α' ω ω' m x y) =
                fun x => x ∈ {x : F | LogupEq α α' ω ω' m x y} := by
              funext x; simp [hy]
            rw [this]
            exact prob_set_le _ (hgood y hy)
    _ = _ := by push_cast; ring

end LogUp

/-! ### The lincheck (Definition lin, Theorem lin), for `J` matrices with combined lookups -/

section Lincheck

/-- A numbering of the index set `W`: an injection `num : W → ℕ` with values `< |W|`. The
integer `num w` is read in `F` (`id(w) = num w`, `G_η(w) = η^{num w}`). For `W = Fin N` this is
`Fin.val`; for hypercube tables it is `bitsToNat`. -/
structure Numbering (W : Type*) [Fintype W] where
  num : W → ℕ
  inj : Function.Injective num
  lt : ∀ w, num w < Fintype.card W

/-- The numbering `Fin.val` of `Fin N`. -/
def Numbering.fin (N : ℕ) : Numbering (Fin N) :=
  ⟨Fin.val, Fin.val_injective, fun w => by simp⟩

variable {J : ℕ} {W : Type*} [Fintype W] [DecidableEq W]

/-- `(M_j z)(w) = ∑_{k : row_j k = w} val_j k · z(col_j k)`. -/
def matVec (row col : Fin J → W → W) (val : Fin J → W → F) (z : W → F)
    (j : Fin J) (w : W) : F :=
  ∑ k, if row j k = w then val j k * z (col j k) else 0

/-- The combined multiplicities `m(w) = #{(j, k) : idx_j k = w}`, read in `F`. -/
def mult (idx : Fin J → W → W) (w : W) : F :=
  (((univ : Finset (Fin J × W)).filter fun jk => idx jk.1 jk.2 = w).card : F)

variable (F J W) in
/-- A deterministic prover of `Π_Lin` at the level of tables: the round-1 tables `e, ζ, p` are
functions of `η`; the round-2 tables `φ^R, ψ^R, φ^C, ψ^C` and the sums `s_j` are functions of
`η` and of the pairs `(y_R, x_R)`, `(y_C, x_C)`. -/
structure LinProver where
  e : F → Fin J → W → F
  ζ : F → Fin J → W → F
  p : F → Fin J → W → F
  φR : F → F × F → F × F → Fin J → W → F
  ψR : F → F × F → F × F → W → F
  φC : F → F × F → F × F → Fin J → W → F
  ψC : F → F × F → F × F → W → F
  s : F → F × F → F × F → Fin J → F

/-- The statements of step 3 of `Π_Lin` on the tables, for `J` matrices with one combined row
lookup and one combined column lookup (`chR = (y_R, x_R)`, `chC = (y_C, x_C)`):
`IP(a_j, G_η) = s_j = IP(val_j, p_j)`, `Had(e_j, ζ_j, p_j)`,
`Had(φ^R_j, x_R 1 - row_j - y_R e_j, 1)`, `Had(ψ^R, x_R 1 - id - y_R G_η, m_R)`,
`IP(∑_j φ^R_j - ψ^R, 1) = 0`, and the same for the columns with `(col_j, ζ_j)`, `(id, z)`, `m_C`. -/
def HoldsLin (ν : Numbering W) (row col : Fin J → W → W) (val : Fin J → W → F) (z : W → F)
    (a : Fin J → W → F) (P : LinProver F J W) (η : F) (chR chC : F × F) : Prop :=
  (∀ j, ∑ w, a j w * η ^ ν.num w = P.s η chR chC j) ∧
  (∀ j, ∑ k, val j k * P.p η j k = P.s η chR chC j) ∧
  (∀ j k, P.e η j k * P.ζ η j k = P.p η j k) ∧
  (∀ j k, P.φR η chR chC j k * (chR.2 - (ν.num (row j k) : F) - chR.1 * P.e η j k) = 1) ∧
  (∀ w, P.ψR η chR chC w * (chR.2 - (ν.num w : F) - chR.1 * η ^ ν.num w) = mult row w) ∧
  (∑ jk : Fin J × W, P.φR η chR chC jk.1 jk.2 - ∑ w, P.ψR η chR chC w = 0) ∧
  (∀ j k, P.φC η chR chC j k * (chC.2 - (ν.num (col j k) : F) - chC.1 * P.ζ η j k) = 1) ∧
  (∀ w, P.ψC η chR chC w * (chC.2 - (ν.num w : F) - chC.1 * z w) = mult col w) ∧
  (∑ jk : Fin J × W, P.φC η chR chC jk.1 jk.2 - ∑ w, P.ψC η chR chC w = 0)

omit [DecidableEq W] in
/-- If `char F > J|W|` (`J ≥ 1`), the numbering read in `F` is injective. -/
lemma Numbering.cast_inj (ν : Numbering W)
    (hchar : ∀ n : ℕ, 1 ≤ n → n ≤ J * Fintype.card W → (n : F) ≠ 0) (hJ : 1 ≤ J) {u v : W}
    (h : (ν.num u : F) = (ν.num v : F)) : u = v := by
  have hN : Fintype.card W ≤ J * Fintype.card W := Nat.le_mul_of_pos_left _ hJ
  have hu := ν.lt u
  have hv := ν.lt v
  apply ν.inj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · apply hchar (ν.num v - ν.num u) (by omega) (by omega)
    rw [Nat.cast_sub hlt.le, h, sub_self]
  · apply hchar (ν.num u - ν.num v) (by omega) (by omega)
    rw [Nat.cast_sub hlt.le, h, sub_self]

omit [DecidableEq W] in
/-- `∑_w η^w (M_j z)(w) = ∑_k val_j k · η^{row_j k} z(col_j k)`. -/
lemma weighted_matVec [DecidableEq W] (ν : Numbering W) (row col : Fin J → W → W)
    (val : Fin J → W → F) (z : W → F) (j : Fin J) (η : F) :
    ∑ w, matVec row col val z j w * η ^ ν.num w =
      ∑ k, val j k * (η ^ ν.num (row j k) * z (col j k)) := by
  simp only [matVec, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl (fun k _ => ?_)
  simp only [ite_mul, zero_mul]
  rw [sum_ite_eq]
  simp only [mem_univ, if_true]
  ring

omit [DecidableEq W] in
/-- The table denominators `x - w - y g(w)` vanish for some `w` with probability `≤ |W|/|F|`. -/
lemma prob_den_bad [Fintype F] (ν : Numbering W) (g : W → F) :
    prob (fun q : F × F => ∃ w : W, q.2 - (ν.num w : F) - q.1 * g w = 0) ≤
      (Fintype.card W : ℚ) / Fintype.card F := by
  classical
  haveI : Nonempty F := ⟨0⟩
  rw [prob_prod_eq_expect (fun y x => ∃ w : W, x - (ν.num w : F) - y * g w = 0)]
  refine expect_le_of_le _ _ (fun y => ?_)
  refine prob_set_le {x : F | ∃ w : W, x - (ν.num w : F) - y * g w = 0} ?_
  have hsub : {x : F | ∃ w : W, x - (ν.num w : F) - y * g w = 0} ⊆
      ↑(univ.image fun w : W => (ν.num w : F) + y * g w) := by
    intro x ⟨w, hw⟩
    rw [coe_image, coe_univ, Set.image_univ]
    exact ⟨w, by linear_combination -hw⟩
  calc _ ≤ (↑(univ.image fun w : W => (ν.num w : F) + y * g w) : Set F).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = (univ.image fun w : W => (ν.num w : F) + y * g w).card := Set.ncard_coe_finset _
    _ ≤ Fintype.card W := card_image_le.trans (by simp)

/-- The failure event of one combined lookup `(idx_j k, v_j k) ∈ {(w, tab w)}` at `q = (y, x)`:
some looked-up value is wrong, and either a table denominator vanishes or the LogUp equation
holds. -/
def LookupFail (ν : Numbering W) (idx : Fin J → W → W) (v : Fin J → W → F) (tab : W → F)
    (q : F × F) : Prop :=
  (∃ j k, v j k ≠ tab (idx j k)) ∧
    ((∃ w : W, q.2 - (ν.num w : F) - q.1 * tab w = 0) ∨
      LogupEq (fun jk : Fin J × W => (ν.num (idx jk.1 jk.2) : F)) (fun jk => v jk.1 jk.2)
        (fun w : W => (ν.num w : F)) tab (mult idx) q.2 q.1)

/-- One combined lookup with `JN` looked-up pairs against `N = |W|` table pairs fails to catch a
wrong value with probability at most `(N + N + JN + N - 1)/|F|` over `(y, x)`. -/
theorem prob_lookupFail [Fintype F] [DecidableEq F] (ν : Numbering W)
    (hchar : ∀ n : ℕ, 1 ≤ n → n ≤ J * Fintype.card W → (n : F) ≠ 0) (hJ : 1 ≤ J)
    (idx : Fin J → W → W) (v : Fin J → W → F) (tab : W → F) :
    prob (LookupFail ν idx v tab) ≤
      ((Fintype.card W + (Fintype.card W + (J * Fintype.card W + Fintype.card W - 1)) : ℕ) : ℚ) /
        Fintype.card F := by
  classical
  by_cases hv : ∃ j k, v j k ≠ tab (idx j k)
  · obtain ⟨j, k, hjk⟩ := hv
    have hk0 : ∀ w : W, ¬ (((ν.num (idx (j, k).1 (j, k).2) : F) = (ν.num w : F)) ∧
        v (j, k).1 (j, k).2 = tab w) := by
      rintro w ⟨h1, h2⟩
      have := ν.cast_inj hchar hJ h1
      exact hjk (by rw [h2, this])
    have hc : ∀ n : ℕ, 1 ≤ n → n ≤ Fintype.card (Fin J × W) → (n : F) ≠ 0 := by
      intro n h1 h2; apply hchar n h1; simpa using h2
    have hl := logup_prob hc (fun jk : Fin J × W => (ν.num (idx jk.1 jk.2) : F))
      (fun jk => v jk.1 jk.2) (fun w : W => (ν.num w : F)) tab (mult idx) (j, k) hk0
    simp only [Fintype.card_prod, Fintype.card_fin] at hl
    calc prob (LookupFail ν idx v tab)
        ≤ prob (fun q : F × F => (∃ w : W, q.2 - (ν.num w : F) - q.1 * tab w = 0) ∨
            LogupEq (fun jk : Fin J × W => (ν.num (idx jk.1 jk.2) : F)) (fun jk => v jk.1 jk.2)
              (fun w : W => (ν.num w : F)) tab (mult idx) q.2 q.1) :=
          prob_mono (fun q hq => hq.2)
      _ ≤ _ := prob_or_le _ _
      _ ≤ (Fintype.card W : ℚ) / Fintype.card F +
            ((Fintype.card W + (J * Fintype.card W + Fintype.card W - 1) : ℕ) : ℚ) /
              Fintype.card F :=
          add_le_add (prob_den_bad ν tab) hl
      _ = _ := by rw [← add_div]; push_cast; ring
  · have : LookupFail ν idx v tab = fun _ => False := by
      funext q; simp only [LookupFail, eq_iff_iff, iff_false, not_and]
      intro h; exact absurd h hv
    rw [this, prob_false]; positivity

omit [DecidableEq W] in
/-- A nonzero table `d` has `∑_w d(w) η^{num w} = 0` for at most `|W| - 1` values of `η`. -/
lemma prob_root_le [Fintype F] [DecidableEq F] (ν : Numbering W) (d : W → F) (hd : d ≠ 0) :
    prob (fun η : F => ∑ w, d w * η ^ ν.num w = 0) ≤
      ((Fintype.card W - 1 : ℕ) : ℚ) / Fintype.card F := by
  classical
  set Q : F[X] := ∑ w : W, C (d w) * X ^ ν.num w
  have hQ : Q ∈ degreeLT F (Fintype.card W) := by
    refine Submodule.sum_mem _ (fun w _ => ?_)
    rw [mem_degreeLT]
    exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast ν.lt w)
  have hne : Q ≠ 0 := by
    obtain ⟨w0, hw0⟩ := Function.ne_iff.1 hd
    intro h0
    have := congrArg (fun P : F[X] => P.coeff (ν.num w0)) h0
    simp only [Q, finset_sum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    rw [sum_eq_single w0 (fun b _ hb => if_neg (fun h => hb (ν.inj h).symm))
      (fun h => absurd (mem_univ w0) h), if_pos rfl] at this
    exact hw0 this
  have hev : ∀ η, Q.eval η = ∑ w, d w * η ^ ν.num w := by
    intro η; simp [Q, eval_finset_sum]
  have := ncard_roots_le hQ hne
  simp only [hev] at this
  exact prob_set_le {η : F | ∑ w, d w * η ^ ν.num w = 0} this

/-- **Theorem lin (lincheck reduction), `J` matrices with combined lookups.** Let `N = |W|`, let
`char F` exceed `JN` (the counts `1, …, JN` are nonzero in `F`), let `z, a_j` be fixed tables with
`a_j ≠ M_j z` for some `j`, and let `P` be any deterministic prover. Over `η` and the pairs
`(y_R, x_R)`, `(y_C, x_C)` uniform in `F`, all the statements of step 3 hold with probability
at most `(N - 1 + 2(N + N + JN + N - 1))/|F| = ((2J + 7)N - 3)/|F|`. -/
theorem lincheck_reduction [Fintype F] [DecidableEq F] (ν : Numbering W)
    (hchar : ∀ n : ℕ, 1 ≤ n → n ≤ J * Fintype.card W → (n : F) ≠ 0)
    (row col : Fin J → W → W) (val : Fin J → W → F) (z : W → F)
    (a : Fin J → W → F) (hwrong : ∃ j, a j ≠ matVec row col val z j) (P : LinProver F J W) :
    prob (fun q : F × ((F × F) × (F × F)) => HoldsLin ν row col val z a P q.1 q.2.1 q.2.2) ≤
      ((Fintype.card W - 1 + 2 * (Fintype.card W + (Fintype.card W +
        (J * Fintype.card W + Fintype.card W - 1))) : ℕ) : ℚ) / Fintype.card F := by
  classical
  haveI : Nonempty F := ⟨0⟩
  obtain ⟨j0, hj0⟩ := hwrong
  have hJ : 1 ≤ J := Fin.pos_iff_nonempty.2 ⟨j0⟩
  set d : W → F := fun w => a j0 w - matVec row col val z j0 w
  have hd : d ≠ 0 := by
    intro h; apply hj0; funext w
    have := congrFun h w; simp only [d, Pi.zero_apply] at this
    exact sub_eq_zero.1 this
  -- the three failure events
  have himp : ∀ q : F × ((F × F) × (F × F)), HoldsLin ν row col val z a P q.1 q.2.1 q.2.2 →
      (∑ w, d w * q.1 ^ ν.num w = 0) ∨
        LookupFail ν row (P.e q.1) (fun w => q.1 ^ ν.num w) q.2.1 ∨
        LookupFail ν col (P.ζ q.1) z q.2.2 := by
    rintro ⟨η, chR, chC⟩ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢
    by_cases he : ∃ j k, P.e η j k ≠ η ^ ν.num (row j k)
    · right; left
      refine ⟨he, ?_⟩
      by_cases hden : ∃ w : W, chR.2 - (ν.num w : F) - chR.1 * η ^ ν.num w = 0
      · exact Or.inl hden
      · right
        push_neg at hden
        have hl : ∀ jk : Fin J × W,
            chR.2 - (ν.num (row jk.1 jk.2) : F) - chR.1 * P.e η jk.1 jk.2 ≠ 0 :=
          fun jk => right_ne_zero_of_mul_eq_one (h4 jk.1 jk.2)
        refine ⟨hl, hden, ?_⟩
        calc ∑ jk : Fin J × W, (chR.2 - (ν.num (row jk.1 jk.2) : F) - chR.1 * P.e η jk.1 jk.2)⁻¹
            = ∑ jk : Fin J × W, P.φR η chR chC jk.1 jk.2 :=
              sum_congr rfl (fun jk _ => (eq_inv_of_mul_eq_one_left (h4 jk.1 jk.2)).symm)
          _ = ∑ w, P.ψR η chR chC w := sub_eq_zero.1 h6
          _ = _ := sum_congr rfl (fun w _ => (eq_mul_inv_iff_mul_eq₀ (hden w)).2 (h5 w))
    by_cases hz : ∃ j k, P.ζ η j k ≠ z (col j k)
    · right; right
      refine ⟨hz, ?_⟩
      by_cases hden : ∃ w : W, chC.2 - (ν.num w : F) - chC.1 * z w = 0
      · exact Or.inl hden
      · right
        push_neg at hden
        have hl : ∀ jk : Fin J × W,
            chC.2 - (ν.num (col jk.1 jk.2) : F) - chC.1 * P.ζ η jk.1 jk.2 ≠ 0 :=
          fun jk => right_ne_zero_of_mul_eq_one (h7 jk.1 jk.2)
        refine ⟨hl, hden, ?_⟩
        calc ∑ jk : Fin J × W, (chC.2 - (ν.num (col jk.1 jk.2) : F) - chC.1 * P.ζ η jk.1 jk.2)⁻¹
            = ∑ jk : Fin J × W, P.φC η chR chC jk.1 jk.2 :=
              sum_congr rfl (fun jk _ => (eq_inv_of_mul_eq_one_left (h7 jk.1 jk.2)).symm)
          _ = ∑ w, P.ψC η chR chC w := sub_eq_zero.1 h9
          _ = _ := sum_congr rfl (fun w _ => (eq_mul_inv_iff_mul_eq₀ (hden w)).2 (h8 w))
    · left
      push_neg at he hz
      have hp : ∀ k, P.p η j0 k = η ^ ν.num (row j0 k) * z (col j0 k) := by
        intro k; rw [← h3, he, hz]
      have e1 : ∑ w, a j0 w * η ^ ν.num w =
          ∑ k, val j0 k * (η ^ ν.num (row j0 k) * z (col j0 k)) := by
        rw [h1 j0, ← h2 j0]; exact sum_congr rfl (fun k _ => by rw [hp])
      simp only [d, sub_mul, sum_sub_distrib, e1, weighted_matVec, sub_self]
  -- the probabilities
  have pRoot : prob (fun q : F × ((F × F) × (F × F)) => ∑ w, d w * q.1 ^ ν.num w = 0) ≤
      ((Fintype.card W - 1 : ℕ) : ℚ) / Fintype.card F := by
    rw [prob_fst (fun η : F => ∑ w, d w * η ^ ν.num w = 0)]
    exact prob_root_le ν d hd
  have pRow : prob (fun q : F × ((F × F) × (F × F)) =>
      LookupFail ν row (P.e q.1) (fun w => q.1 ^ ν.num w) q.2.1) ≤
      ((Fintype.card W + (Fintype.card W + (J * Fintype.card W + Fintype.card W - 1)) : ℕ) : ℚ) /
        Fintype.card F := by
    rw [prob_prod_eq_expect (fun η (c : (F × F) × (F × F)) =>
      LookupFail ν row (P.e η) (fun w => η ^ ν.num w) c.1)]
    refine expect_le_of_le _ _ (fun η => ?_)
    rw [prob_fst (LookupFail ν row (P.e η) (fun w => η ^ ν.num w))]
    exact prob_lookupFail ν hchar hJ _ _ _
  have pCol : prob (fun q : F × ((F × F) × (F × F)) => LookupFail ν col (P.ζ q.1) z q.2.2) ≤
      ((Fintype.card W + (Fintype.card W + (J * Fintype.card W + Fintype.card W - 1)) : ℕ) : ℚ) /
        Fintype.card F := by
    rw [prob_prod_eq_expect (fun η (c : (F × F) × (F × F)) => LookupFail ν col (P.ζ η) z c.2)]
    refine expect_le_of_le _ _ (fun η => ?_)
    rw [prob_snd (LookupFail ν col (P.ζ η) z)]
    exact prob_lookupFail ν hchar hJ _ _ _
  calc _ ≤ _ := prob_mono himp
    _ ≤ _ := prob_or_le _ _
    _ ≤ _ := add_le_add le_rfl (prob_or_le _ _)
    _ ≤ ((Fintype.card W - 1 : ℕ) : ℚ) / Fintype.card F +
          (((Fintype.card W + (Fintype.card W + (J * Fintype.card W + Fintype.card W - 1)) : ℕ) :
              ℚ) / Fintype.card F +
            ((Fintype.card W + (Fintype.card W + (J * Fintype.card W + Fintype.card W - 1)) : ℕ) :
              ℚ) / Fintype.card F) :=
        add_le_add pRoot (add_le_add pRow pCol)
    _ = _ := by rw [← add_div, ← add_div]; push_cast; ring

/-- **Two-phase composition (the structure of Theorem linsound and Theorem r1cs).** If the
event `E` over the first-phase challenges `τ` has probability `≤ ε₁`, and outside `E` the second
phase accepts with probability `≤ ε₂` for every `τ`, the whole protocol accepts with probability
`≤ ε₁ + ε₂`. -/
theorem prob_two_phase {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂] [Nonempty Ω₂]
    (E : Ω₁ → Prop) (Acc : Ω₁ → Ω₂ → Prop) {ε₂ : ℚ} (hε : 0 ≤ ε₂)
    (h : ∀ τ, ¬ E τ → prob (Acc τ) ≤ ε₂) :
    prob (fun p : Ω₁ × Ω₂ => Acc p.1 p.2) ≤ prob E + ε₂ := by
  classical
  by_cases h1 : Nonempty Ω₁
  · calc prob (fun p : Ω₁ × Ω₂ => Acc p.1 p.2)
        ≤ prob (fun p : Ω₁ × Ω₂ => E p.1 ∨ (¬ E p.1 ∧ Acc p.1 p.2)) :=
          prob_mono (fun p hp => by by_cases hE : E p.1 <;> simp [hE, hp])
      _ ≤ _ := prob_or_le _ _
      _ ≤ prob E + ε₂ := by
          rw [prob_fst E]
          refine add_le_add le_rfl ?_
          rw [prob_prod_eq_expect (fun τ ω => ¬ E τ ∧ Acc τ ω)]
          refine expect_le_of_le _ _ (fun τ => ?_)
          by_cases hE : E τ
          · have : (fun ω => ¬ E τ ∧ Acc τ ω) = fun _ => False := by funext ω; simp [hE]
            rw [this, prob_false]; exact hε
          · exact (prob_mono (fun ω hω => hω.2)).trans (h τ hE)
  · haveI : IsEmpty Ω₁ := not_nonempty_iff.1 h1
    rw [prob_def]; simp only [Fintype.card_eq_zero, Nat.cast_zero, div_zero]
    exact add_nonneg (prob_nonneg _) hε

/-- **Theorem linsound, reduced form.** Any second phase whose acceptance probability is
`≤ ε₂` whenever the statements of step 3 fail (for `Π_Batch` on affine forms this is Theorem
batch through Proposition affine) gives, after `Π_Lin` on a false instance, acceptance
probability at most `((2J + 7)N - 3)/|F| + ε₂`. -/
theorem lincheck_sound [Fintype F] [DecidableEq F] {Ω₂ : Type*} [Fintype Ω₂] [Nonempty Ω₂]
    (ν : Numbering W) (hchar : ∀ n : ℕ, 1 ≤ n → n ≤ J * Fintype.card W → (n : F) ≠ 0)
    (row col : Fin J → W → W) (val : Fin J → W → F) (z : W → F)
    (a : Fin J → W → F) (hwrong : ∃ j, a j ≠ matVec row col val z j) (P : LinProver F J W)
    (Acc : F × ((F × F) × (F × F)) → Ω₂ → Prop) {ε₂ : ℚ} (hε : 0 ≤ ε₂)
    (hB : ∀ τ, ¬ HoldsLin ν row col val z a P τ.1 τ.2.1 τ.2.2 → prob (Acc τ) ≤ ε₂) :
    prob (fun p : (F × ((F × F) × (F × F))) × Ω₂ => Acc p.1 p.2) ≤
      ((Fintype.card W - 1 + 2 * (Fintype.card W + (Fintype.card W +
        (J * Fintype.card W + Fintype.card W - 1))) : ℕ) : ℚ) / Fintype.card F + ε₂ :=
  (prob_two_phase _ Acc hε hB).trans
    (add_le_add (lincheck_reduction ν hchar row col val z a hwrong P) le_rfl)

/-- **Theorem r1cs, reduced form.** `J` linchecks share their challenges and their combined
lookups; `Extra` stands for the remaining statements on the decoded tables (for R1CS,
`a ∘ b = c` and `w = 0` on the input positions). If the instance has no witness — some
`a_j ≠ M_j z`, or `¬ Extra` — then any second phase that accepts with probability `≤ ε₂`
whenever a statement fails gives acceptance probability at most `((2J + 7)N - 3)/|F| + ε₂`. -/
theorem r1cs_sound [Fintype F] [DecidableEq F] {Ω₂ : Type*} [Fintype Ω₂] [Nonempty Ω₂]
    (ν : Numbering W) (hchar : ∀ n : ℕ, 1 ≤ n → n ≤ J * Fintype.card W → (n : F) ≠ 0)
    (row col : Fin J → W → W) (val : Fin J → W → F) (z : W → F)
    (a : Fin J → W → F) (Extra : Prop)
    (hno : ¬ ((∀ j, a j = matVec row col val z j) ∧ Extra)) (P : LinProver F J W)
    (Acc : F × ((F × F) × (F × F)) → Ω₂ → Prop) {ε₂ : ℚ} (hε : 0 ≤ ε₂)
    (hB : ∀ τ, ¬ (HoldsLin ν row col val z a P τ.1 τ.2.1 τ.2.2 ∧ Extra) → prob (Acc τ) ≤ ε₂) :
    prob (fun p : (F × ((F × F) × (F × F))) × Ω₂ => Acc p.1 p.2) ≤
      ((Fintype.card W - 1 + 2 * (Fintype.card W + (Fintype.card W +
        (J * Fintype.card W + Fintype.card W - 1))) : ℕ) : ℚ) / Fintype.card F + ε₂ := by
  by_cases hall : ∀ j, a j = matVec row col val z j
  · have hE : ¬ Extra := fun h => hno ⟨hall, h⟩
    refine (prob_two_phase (fun _ => False) Acc hε (fun τ _ => hB τ (fun h => hE h.2))).trans ?_
    rw [prob_false, zero_add]
    exact le_add_of_nonneg_left (by positivity)
  · push_neg at hall
    exact lincheck_sound ν hchar row col val z a hall P Acc hε (fun τ h => hB τ (fun h' => h h'.1))

end Lincheck

end KroneckerFRI
