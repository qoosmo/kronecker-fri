/-
KroneckerFRI/Batch.lean
§11.2 of the paper: opening several polynomials at one point (Definition 11.1), soundness of
batched openings (Theorem 11.2) and knowledge and binding (Corollary 11.3).

The number of polynomials is `t + 1` with `t ≥ 1` (the paper's `m = t + 1 ≥ 2`), so that the
batched words `w_γ = ∑_{i ≤ t} γ^i w^{(i)}` form a curve of degree `t` (`thm:curves`).
A deterministic prover of `Π^{t+1}_KF` is, for each `γ`, a prover of `Π_KF` on
`(w_γ; z, v_γ)`; the challenge space is `F × ((F × F^ℓ) × L^κ)` (`γ`, then the challenges of
`Π_KF`).
-/
import KroneckerFRI.RBR

set_option autoImplicit false

open Polynomial Finset KBFold

namespace KroneckerFRI

variable {F : Type*} [Field F] {L : Subgroup Fˣ}

/-! ### Definition 11.1 -/

section Defs

variable {t n : ℕ}

/-- `w_γ = ∑_{i ≤ t} γ^i w^{(i)}`. -/
def wGamma (ws : Fin (t + 1) → L → F) (γ : F) : L → F := ∑ i : Fin (t + 1), γ ^ (i : ℕ) • ws i

/-- `v_γ = ∑_{i ≤ t} γ^i v_i`. -/
def vGamma (vs : Fin (t + 1) → F) (γ : F) : F := ∑ i : Fin (t + 1), γ ^ (i : ℕ) * vs i

/-- **The relation `R^{δ,m}_KF`:** the commitments are jointly close to the encodings of the
`f_i`, on one common fibre-closed set of at least `(1-δ)M` points, and `f_i(z) = v_i`. -/
def RelBatch (δ : ℚ) (ws : Fin (t + 1) → L → F) (z : Fin n → F) (vs : Fin (t + 1) → F)
    (αs : Fin (t + 1) → Table F n) : Prop :=
  (∃ S : Set L, (∀ ξ ∈ S, negPt ξ ∈ S) ∧ (1 - δ) * Nat.card L ≤ S.ncard ∧
      ∀ i, ∀ ξ ∈ S, ws i ξ = encode L (αs i) ξ) ∧ ∀ i, cEval (αs i) z = vs i

/-- The acceptance probability of `Π^{t+1}_KF` for the provers `P γ` of `Π_KF`. -/
noncomputable def accProbBatch [Fintype F] [Fintype L] (P : F → KFProver F L) (ℓ κ : ℕ)
    (ws : Fin (t + 1) → L → F) (z : Fin n → F) (vs : Fin (t + 1) → F) : ℚ :=
  prob (fun p : F × ((F × (Fin ℓ → F)) × (Fin κ → L)) =>
    (P p.1).Accepts ℓ (wGamma ws p.1) z (vGamma vs p.1) p.2.1.1 (extR p.2.1.2) p.2.2)

/-- `Enc` as a linear map. -/
noncomputable def encodeLin (L : Subgroup Fˣ) (n : ℕ) : Table F n →ₗ[F] (L → F) where
  toFun := encode L
  map_add' := encode_add
  map_smul' := encode_smul

/-- `f ↦ f(z)` as a linear map. -/
def cEvalLin {n : ℕ} (z : Fin n → F) : Table F n →ₗ[F] F where
  toFun α := cEval α z
  map_add' α β := cEval_add α β z
  map_smul' c α := cEval_smul c α z

/-- Completeness (after Definition 11.1): `w_γ = Enc(f_γ)`. -/
theorem wGamma_encode (αs : Fin (t + 1) → Table F n) (γ : F) :
    wGamma (fun i => encode L (αs i)) γ = encode L (∑ i : Fin (t + 1), γ ^ (i : ℕ) • αs i) := by
  have := map_sum (encodeLin L n) (fun i : Fin (t + 1) => γ ^ (i : ℕ) • αs i) univ
  simp only [map_smul] at this
  rw [wGamma]
  exact this.symm

/-- Completeness (after Definition 11.1): `v_γ = f_γ(z)`. -/
theorem vGamma_cEval (αs : Fin (t + 1) → Table F n) (z : Fin n → F) (γ : F) :
    vGamma (fun i => cEval (αs i) z) γ = cEval (∑ i : Fin (t + 1), γ ^ (i : ℕ) • αs i) z := by
  have := map_sum (cEvalLin z) (fun i : Fin (t + 1) => γ ^ (i : ℕ) • αs i) univ
  simp only [map_smul, smul_eq_mul] at this
  rw [vGamma]
  exact this.symm

end Defs

/-! ### Polynomials of degree `t` in the batching challenge -/

section CurvePoly

variable {t : ℕ}

/-- `∑_{i ≤ t} a_i Z^i`. -/
noncomputable def curvePoly (a : Fin (t + 1) → F) : F[X] := ∑ i : Fin (t + 1), C (a i) * X ^ (i : ℕ)

lemma eval_curvePoly (a : Fin (t + 1) → F) (γ : F) :
    (curvePoly a).eval γ = ∑ i : Fin (t + 1), γ ^ (i : ℕ) * a i := by
  simp only [curvePoly, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  exact sum_congr rfl fun i _ => mul_comm _ _

lemma natDegree_curvePoly (a : Fin (t + 1) → F) : (curvePoly a).natDegree ≤ t := by
  unfold curvePoly
  refine natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

lemma coeff_curvePoly (a : Fin (t + 1) → F) (i : Fin (t + 1)) : (curvePoly a).coeff i = a i := by
  simp only [curvePoly, finset_sum_coeff, coeff_C_mul_X_pow]
  rw [sum_eq_single i]
  · simp
  · intro j _ hj; rw [if_neg (fun h => hj (Fin.ext h.symm))]
  · simp

lemma curvePoly_ne_zero {a : Fin (t + 1) → F} (h : ∃ i, a i ≠ 0) : curvePoly a ≠ 0 := by
  obtain ⟨i, hi⟩ := h
  intro h0
  apply hi
  rw [← coeff_curvePoly a i, h0, coeff_zero]

/-- A polynomial of degree `≤ t` with more than `t` roots in a set is zero. -/
lemma curvePoly_eq_zero_of_roots [Fintype F] {a : Fin (t + 1) → F} (S : Set F)
    (hS : t < S.ncard) (hroot : ∀ γ ∈ S, (curvePoly a).eval γ = 0) : ∀ i, a i = 0 := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  have h0 : curvePoly a = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero (curvePoly a) (f := fun γ : S => (γ : F))
      Subtype.val_injective (fun γ => hroot γ γ.2) ?_
    rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]
    exact lt_of_le_of_lt (natDegree_curvePoly a) hS
  intro i
  rw [← coeff_curvePoly a i, h0, coeff_zero]

end CurvePoly

/-! ### Theorem 11.2 (soundness of batched openings) -/

section Theorem

variable {m ℓ R t : ℕ} {δ : ℚ}

/-- The set `Γ` of Theorem 11.2 has at most `t M` elements when there is no witness. -/
theorem card_Gamma_le [Fintype F] [DecidableEq F] (hL : IsSmoothDomain L (m + ℓ + R))
    (hR : 1 ≤ R) (ht : 1 ≤ t) (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (ws : Fin (t + 1) → L → F) (z : Fin (m + ℓ) → F) (vs : Fin (t + 1) → F)
    (hnw : ∀ αs, ¬ RelBatch δ ws z vs αs) :
    {γ : F | ∃ α, RelKF δ (wGamma ws γ) z (vGamma vs γ) α}.ncard ≤ t * Nat.card L := by
  classical
  haveI := hL.finite
  letI : Fintype L := Fintype.ofFinite L
  set Γ := {γ : F | ∃ α, RelKF δ (wGamma ws γ) z (vGamma vs γ) α}
  by_contra hΓ
  push_neg at hΓ
  have hcardL : Nat.card L = 2 ^ (m + ℓ + R) := hL
  have hNM : 2 ^ (m + ℓ) ≤ Nat.card L := by
    rw [hcardL]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrate : rate L (2 ^ (m + ℓ)) = 1 / 2 ^ R := by
    rw [rate, hcardL]; push_cast
    rw [pow_add (2 : ℚ) (m + ℓ) R]
    have : (2 : ℚ) ^ (m + ℓ) ≠ 0 := by positivity
    field_simp
  have hδ' : δ ≤ (1 - rate L (2 ^ (m + ℓ))) / 2 := by rw [hrate]; exact hδ
  have hneg : (-1 : Fˣ) ∈ L := hL.neg_one_mem (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_smooth hL (by omega)
  have hMpos : 1 ≤ Nat.card L := by rw [hcardL]; exact Nat.one_le_two_pow
  -- correlated agreement for the curve of degree `t`
  have hsub : Γ ⊆ {γ : F | DistLE (∑ i : Fin (t + 1), γ ^ (i : ℕ) • ws i)
      (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ} := by
    rintro γ ⟨α, hα, -⟩
    exact ⟨encode L α, encode_mem_RS α, (relDist_le_fibDist hneg h2 _ _).trans hα⟩
  obtain ⟨L', hL', c, hc, hagreeL'⟩ := bciks_curves L (m + ℓ + R) hL (2 ^ (m + ℓ))
    Nat.one_le_two_pow hNM δ hδ0 hδ' t ht ws
    (lt_of_lt_of_le hΓ (Set.ncard_le_ncard hsub (Set.toFinite _)))
  set Agr : Set L := {ξ | ∀ i, ws i ξ = c i ξ}
  have hAgr : (1 - δ) * Nat.card L ≤ Agr.ncard := by
    refine hL'.trans ?_
    exact_mod_cast Set.ncard_le_ncard (fun ξ hξ => hagreeL' ξ hξ) (Set.toFinite _)
  set αh : Fin (t + 1) → Table F (m + ℓ) := fun i => kronCoeffs (m + ℓ) (polyOf (c i))
  have hencα : ∀ i, encode L (αh i) = c i := fun i => encode_surj hNM (hc i)
  -- for `γ ∈ Γ`, the witness is `∑ γ^i f̂_i`
  have hwit : ∀ γ ∈ Γ, ∀ α, RelKF δ (wGamma ws γ) z (vGamma vs γ) α →
      α = ∑ i : Fin (t + 1), γ ^ (i : ℕ) • αh i := by
    intro γ _ α hα
    apply encode_injective hNM
    have hcomb : encode L (∑ i : Fin (t + 1), γ ^ (i : ℕ) • αh i) = wGamma (fun i => c i) γ := by
      rw [← wGamma_encode]; simp [hencα]
    have hmem : encode L (∑ i : Fin (t + 1), γ ^ (i : ℕ) • αh i) ∈ RS L (2 ^ (m + ℓ)) := encode_mem_RS _
    refine RS_unique_decoding' δ hδ' (wGamma ws γ) (encode_mem_RS α) hmem
      ((relDist_le_fibDist hneg h2 _ _).trans hα.1) ?_
    rw [hcomb]
    refine relDist_le_of_agree Agr hAgr (fun ξ hξ => ?_)
    simp only [wGamma, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact sum_congr rfl (fun i _ => by rw [hξ i])
  -- the values: `∑ γ^i (f̂_i(z) - v_i) = 0` on `Γ`, so `f̂_i(z) = v_i`
  have hval : ∀ i, cEval (αh i) z - vs i = 0 := by
    refine curvePoly_eq_zero_of_roots Γ ?_ (fun γ hγ => ?_)
    · calc t ≤ t * Nat.card L := Nat.le_mul_of_pos_right _ hMpos
        _ < _ := hΓ
    · obtain ⟨α, hα⟩ := id hγ
      have e := hα.2
      rw [hwit γ hγ α hα, ← vGamma_cEval] at e
      rw [eval_curvePoly]
      simp only [vGamma] at e
      simp only [mul_sub, sum_sub_distrib, e, sub_self]
  -- the bad challenges
  let a : L → Fin (t + 1) → F := fun ξ i => ws i ξ - c i ξ
  let Bad : Set F := {γ | ∃ ξ : L, ξ ∉ Agr ∧ (curvePoly (a ξ)).eval γ = 0}
  have hBad : Bad.ncard ≤ t * Nat.card L := by
    have hsub : (univ.filter fun γ : F => ∃ ξ : L, ξ ∉ Agr ∧ (curvePoly (a ξ)).eval γ = 0) ⊆
        univ.biUnion (fun ξ : L => if ξ ∈ Agr then ∅ else (curvePoly (a ξ)).roots.toFinset) := by
      intro γ hγ
      simp only [mem_filter, mem_univ, true_and] at hγ
      obtain ⟨ξ, hξ, h0⟩ := hγ
      simp only [mem_biUnion, mem_univ, true_and]
      refine ⟨ξ, ?_⟩
      have hne : curvePoly (a ξ) ≠ 0 := curvePoly_ne_zero (by
        by_contra hall; push_neg at hall; exact hξ (fun i => sub_eq_zero.1 (hall i)))
      simp [hξ, Multiset.mem_toFinset, mem_roots hne, IsRoot, h0]
    have hle : ∀ ξ : L, (if ξ ∈ Agr then (∅ : Finset F) else
        (curvePoly (a ξ)).roots.toFinset).card ≤ t := by
      intro ξ
      split_ifs
      · simp
      · exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (natDegree_curvePoly _))
    rw [← card_filter_eq_ncard]
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_biUnion_le
      _ ≤ ∑ _ξ : L, t := sum_le_sum (fun ξ _ => hle ξ)
      _ = t * Nat.card L := by rw [sum_const, card_univ, smul_eq_mul, Nat.card_eq_fintype_card,
          mul_comm]
  obtain ⟨γ, hγ, hγB⟩ : ∃ γ ∈ Γ, γ ∉ Bad := by
    by_contra hne
    push_neg at hne
    have := Set.ncard_le_ncard (fun γ hγ => hne γ hγ) (Set.toFinite Bad)
    omega
  obtain ⟨g, hg⟩ := hγ
  -- a common fibre-closed set on which `w_γ = Enc(g)`, contained in `Agr`
  obtain ⟨S', hS', hagreeS'⟩ := (fibDist_le_iff _ _ δ).1 hg.1
  set S := sqPt ⁻¹' S'
  have hSneg : ∀ ξ ∈ S, negPt ξ ∈ S := by
    intro ξ hξ; show sqPt (negPt ξ) ∈ S'; rw [sqPt_negPt]; exact hξ
  have hScard : (1 - δ) * Nat.card L ≤ S.ncard := by
    have h1 := ncard_preimage_sqPt hneg h2 S'
    have h3 := card_eq_two_mul_sqDom (D := L) hneg h2
    rw [h1, h3]; push_cast; linarith
  have hgα := hwit γ ⟨g, hg⟩ g hg
  have hSA : S ⊆ Agr := by
    intro ξ hξ
    by_contra hξA
    apply hγB
    refine ⟨ξ, hξA, ?_⟩
    have hw : wGamma ws γ ξ = encode L g ξ := hagreeS' _ hξ ξ rfl
    rw [hgα, ← wGamma_encode] at hw
    simp only [wGamma, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hencα] at hw
    rw [eval_curvePoly]
    simp only [a, mul_sub, sum_sub_distrib, hw, sub_self]
  exact hnw αh ⟨⟨S, hSneg, hScard, fun i ξ hξ => by rw [hencα]; exact hSA hξ i⟩,
    fun i => sub_eq_zero.1 (hval i)⟩

/-- **Theorem 11.2 (soundness of batched openings).** If `((w^{(i)})_i; z, (v_i)_i)` has no
witness in `R^{δ,t+1}_KF`, every family of causal provers is accepted with probability at most
`t M / |F| + ε_KF`. -/
theorem batch_soundness [Fintype F] [DecidableEq F] [Fintype L]
    (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) (ht : 1 ≤ t) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : F → KFProver F L) (hC : ∀ γ, (P γ).Causal)
    (hdeg : ∀ γ, (P γ).DegOK m) (κ : ℕ) (ws : Fin (t + 1) → L → F) (z : Fin (m + ℓ) → F)
    (vs : Fin (t + 1) → F) (hnw : ∀ αs, ¬ RelBatch δ ws z vs αs) :
    accProbBatch P ℓ κ ws z vs ≤
      t * Nat.card L / Fintype.card F + epsKF F (m + ℓ + R) ℓ κ δ := by
  classical
  haveI : Nonempty F := ⟨0⟩
  set Γ := {γ : F | ∃ α, RelKF δ (wGamma ws γ) z (vGamma vs γ) α}
  have hΓ := card_Gamma_le hL (by omega) ht hδ0 hδ ws z vs hnw
  unfold accProbBatch
  rw [prob_prod_eq_expect (fun γ (ω : (F × (Fin ℓ → F)) × (Fin κ → L)) =>
    (P γ).Accepts ℓ (wGamma ws γ) z (vGamma vs γ) ω.1.1 (extR ω.1.2) ω.2)]
  have hpt : ∀ γ, (P γ).accProb ℓ κ (wGamma ws γ) z (vGamma vs γ) ≤
      (if γ ∈ Γ then 1 else 0) + epsKF F (m + ℓ + R) ℓ κ δ := by
    intro γ
    have hε : 0 ≤ epsKF F (m + ℓ + R) ℓ κ δ := by
      have hR' : (0 : ℚ) < 1 / 2 ^ R := by positivity
      unfold epsKF
      have := epsFold_nonneg F (m + ℓ + R) ℓ
      have : (0 : ℚ) ≤ (1 - δ) ^ κ := pow_nonneg (by linarith) κ
      positivity
    split_ifs with h
    · have := prob_le_one (fun ω : (F × (Fin ℓ → F)) × (Fin κ → L) =>
        (P γ).Accepts ℓ (wGamma ws γ) z (vGamma vs γ) ω.1.1 (extR ω.1.2) ω.2)
      unfold KFProver.accProb; linarith
    · rw [zero_add]
      refine soundness hL hR hℓ hδ0 hδ (P γ) (hC γ) (hdeg γ) κ _ z _ (fun α hα => h ⟨α, hα⟩)
  have hF : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  calc expect (fun γ => prob (fun ω : (F × (Fin ℓ → F)) × (Fin κ → L) =>
        (P γ).Accepts ℓ (wGamma ws γ) z (vGamma vs γ) ω.1.1 (extR ω.1.2) ω.2))
      ≤ expect (fun γ : F => (if γ ∈ Γ then (1 : ℚ) else 0) + epsKF F (m + ℓ + R) ℓ κ δ) := by
        unfold expect
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact sum_le_sum (fun γ _ => hpt γ)
    _ = (Γ.ncard : ℚ) / Fintype.card F + epsKF F (m + ℓ + R) ℓ κ δ := by
        unfold expect
        rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, add_div,
          mul_div_cancel_left₀ _ hF.ne', sum_boole, card_filter_eq_ncard]
        rfl
    _ ≤ _ := by
        apply add_le_add_right
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact_mod_cast hΓ

/-- **Corollary 11.3 (knowledge for batched openings).** If the verifier accepts with probability
greater than `t M / |F| + ε_KF`, then the extracted polynomials `Ext(w^{(i)})` form a witness. -/
theorem batch_knowledge [Fintype F] [DecidableEq F] [Fintype L]
    (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) (ht : 1 ≤ t) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : F → KFProver F L) (hC : ∀ γ, (P γ).Causal)
    (hdeg : ∀ γ, (P γ).DegOK m) (κ : ℕ) (ws : Fin (t + 1) → L → F) (z : Fin (m + ℓ) → F)
    (vs : Fin (t + 1) → F)
    (hacc : t * Nat.card L / Fintype.card F + epsKF F (m + ℓ + R) ℓ κ δ <
      accProbBatch P ℓ κ ws z vs) :
    RelBatch δ ws z vs (fun i => extKF (m + ℓ) R (ws i)) := by
  by_cases h : ∃ αs, RelBatch δ ws z vs αs
  · obtain ⟨αs, ⟨S, hSneg, hScard, hS⟩, hv⟩ := h
    haveI := hL.finite
    have hneg : (-1 : Fˣ) ∈ L := hL.neg_one_mem (by omega)
    have h2 : (2 : F) ≠ 0 := two_ne_zero_of_smooth hL (by omega)
    have hext : ∀ i, extKF (m + ℓ) R (ws i) = αs i := fun i =>
      extKF_eq hL (by omega) hδ (fibDist_le_of_closed hneg h2 S hSneg hScard (hS i))
    simp only [hext]
    exact ⟨⟨S, hSneg, hScard, hS⟩, hv⟩
  · push_neg at h
    have := batch_soundness hL hR hℓ ht hδ0 hδ P hC hdeg κ ws z vs h
    linarith

/-- **Corollary 11.3 (binding for batched openings):** for fixed commitments and point, two
families of values that differ in some coordinate cannot both be accepted with probability
greater than `t M / |F| + ε_KF`. -/
theorem batch_binding [Fintype F] [DecidableEq F] [Fintype L]
    (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) (ht : 1 ≤ t) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P P' : F → KFProver F L) (hC : ∀ γ, (P γ).Causal)
    (hdeg : ∀ γ, (P γ).DegOK m) (hC' : ∀ γ, (P' γ).Causal) (hdeg' : ∀ γ, (P' γ).DegOK m)
    (κ : ℕ) (ws : Fin (t + 1) → L → F) (z : Fin (m + ℓ) → F) {vs vs' : Fin (t + 1) → F}
    (hvv : vs ≠ vs') :
    ¬ (t * Nat.card L / Fintype.card F + epsKF F (m + ℓ + R) ℓ κ δ < accProbBatch P ℓ κ ws z vs ∧
        t * Nat.card L / Fintype.card F + epsKF F (m + ℓ + R) ℓ κ δ <
          accProbBatch P' ℓ κ ws z vs') := by
  rintro ⟨h1, h2⟩
  have e1 := (batch_knowledge hL hR hℓ ht hδ0 hδ P hC hdeg κ ws z vs h1).2
  have e2 := (batch_knowledge hL hR hℓ ht hδ0 hδ P' hC' hdeg' κ ws z vs' h2).2
  exact hvv (funext fun i => (e1 i).symm.trans (e2 i))

end Theorem

end KroneckerFRI
