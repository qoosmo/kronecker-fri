/-
KroneckerFRI/Soundness.lean
§7.1–7.4 of the paper: the rate condition (Lemma 7.2), the value on an agreement set (Lemma 7.3),
the batching lemma (Lemma 7.4) and direct soundness (Theorem 7.8).

Throughout: `n = m + ℓ`, `N = 2^n`, `L` a smooth domain of order `M = 2^{n+R}` with `R ≥ 2`, and
`0 < δ ≤ δ* = (1-ρ)/2` with `ρ = 2^{-R}`.  A set `T ⊆ L` is fibre-closed if `-ξ ∈ T` for every
`ξ ∈ T`.
-/
import KroneckerFRI.Scheme

set_option autoImplicit false

open Polynomial Finset KBFold

namespace KroneckerFRI

variable {F : Type*} [Field F]

/-! ### Lemma 7.2 (rate condition) -/

/-- **Lemma 7.2:** `2N < (1-δ) M` for `R ≥ 2` and `δ ≤ (1-ρ)/2`. -/
theorem rate_condition {n R : ℕ} (hR : 2 ≤ R) {δ : ℚ} (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) :
    2 * (2 : ℚ) ^ n < (1 - δ) * 2 ^ (n + R) := by
  have h4 : (4 : ℚ) ≤ 2 ^ R := by
    calc (4 : ℚ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ R := pow_le_pow_right₀ (by norm_num) hR
  rw [pow_add]
  generalize ht : (2 : ℚ) ^ R = t at h4 hδ ⊢
  generalize hx : (2 : ℚ) ^ n = x
  have ht0 : 0 < t := by linarith
  have hx0 : 0 < x := by rw [← hx]; positivity
  have h1 : (1 + 1 / t) / 2 ≤ 1 - δ := by linarith
  have key : (1 + 1 / t) / 2 * (x * t) = (x * t + x) / 2 := by field_simp
  have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt (mul_pos hx0 ht0))
  rw [key] at h2
  nlinarith

/-! ### Fibre-closed agreement and fibre distance -/

section FibreClosed

variable {L : Subgroup Fˣ}

/-- If `w` and `c` agree on a fibre-closed set `T` with `|T| ≥ (1-δ)M`, then
`Δ^fib₀(w, c) ≤ δ` (Lemma 5.11(2)). -/
theorem fibDist_le_of_closed [Finite L] (hL : (-1 : Fˣ) ∈ L) (h2 : (2 : F) ≠ 0) {w c : L → F}
    {δ : ℚ} (T : Set L) (hT : ∀ ξ ∈ T, negPt ξ ∈ T) (hcard : (1 - δ) * Nat.card L ≤ T.ncard)
    (hagree : ∀ ξ ∈ T, w ξ = c ξ) : fibDist w c ≤ δ := by
  rw [fibDist_le_iff]
  refine ⟨sqPt '' T, ?_, ?_⟩
  · have h1 := ncard_eq_two_mul_image hL h2 T hT
    have h3 := card_eq_two_mul_sqDom (D := L) hL h2
    rw [h1, h3] at hcard
    push_cast at hcard
    linarith
  · rintro _ ⟨ξ, hξ, rfl⟩ ζ hζ
    rw [fibre_sqPt hL] at hζ
    rcases hζ with rfl | rfl
    · exact hagree _ hξ
    · exact hagree _ (hT _ hξ)

/-- Agreement on `(1-δ)M` points gives relative distance `≤ δ`. -/
theorem relDist_le_of_agree [Finite L] {w c : L → F} {δ : ℚ} (T : Set L)
    (hcard : (1 - δ) * Nat.card L ≤ T.ncard) (hagree : ∀ ξ ∈ T, w ξ = c ξ) : relDist w c ≤ δ := by
  have hpos : (0 : ℚ) < Nat.card L := by
    haveI : Nonempty L := ⟨1⟩; exact_mod_cast Nat.card_pos
  have hsub : T ⊆ agreeSet w c := fun ξ hξ => hagree ξ hξ
  have h1 : (T.ncard : ℚ) ≤ (agreeSet w c).ncard := by
    exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ((agreeSet w c).ncard : ℚ) + hdist w c = Nat.card L := by
    exact_mod_cast agree_add_hdist w c
  unfold relDist
  rw [div_le_iff₀ hpos]
  linarith

end FibreClosed

/-! ### Lemma 7.3 (the value on an agreement set) -/

section Value

variable {L : Subgroup Fˣ} {n : ℕ}

/-- **Lemma 7.3:** if `w = ev_L(Û)`, `w_A = ev_L(Â)` and `h = ev_L(Ĥ)` on a set of more than
`2N` points, with `Û, Â, Ĥ ∈ F[X]_{<N}`, then `v = [X^{N-1}] Û K_z`. -/
theorem value_of_agreement [Finite L] {w wA : L → F} (z : Fin n → F) (v : F) {U A H : F[X]}
    (hU : U ∈ degreeLT F (2 ^ n)) (hA : A ∈ degreeLT F (2 ^ n)) (hH : H ∈ degreeLT F (2 ^ n))
    (S : Set L) (hS : 2 * 2 ^ n < S.ncard)
    (hagree : ∀ ξ ∈ S, w ξ = U.eval (xv' ξ) ∧ wA ξ = A.eval (xv' ξ) ∧
      virt w wA z v ξ = H.eval (xv' ξ)) :
    v = (U * kernel z).coeff (2 ^ n - 1) := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  refine identity_lemma hA z (eq_zero_of_natDegree_lt_card_of_eval_eq_zero (Phi U A H z v)
    (f := fun i : S => xv' (i : L)) ?_ ?_ ?_)
  · intro a b hab
    exact Subtype.ext (Subtype.ext (Units.ext hab))
  · intro i
    obtain ⟨h1, h2, h3⟩ := hagree i i.2
    have hid := virt_identity w wA z v (i : L)
    simp only [Phi, assemble, eval_sub, eval_add, eval_mul, eval_X, eval_C, eval_pow]
    rw [← h1, ← h2, ← h3, hid]; ring
  · rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]
    exact lt_of_le_of_lt (natDegree_Phi_le hU hA hH z v) hS

end Value

/-! ### Lemma 7.4 (batching) -/

section Batching

variable {L : Subgroup Fˣ}

/-- The set `𝒢` of Lemma 7.4: the `β` for which `w_β` agrees with a codeword of `𝒞_0` on a
fibre-closed subset `T ⊆ Y` with `|T| ≥ (1-δ)M`. -/
def goodBeta {n : ℕ} (δ : ℚ) (w wA : L → F) (z : Fin n → F) (v : F) (Y : Set L) : Set F :=
  {β | ∃ c ∈ RS L (2 ^ n), ∃ T ⊆ Y, (∀ ξ ∈ T, negPt ξ ∈ T) ∧ (1 - δ) * Nat.card L ≤ T.ncard ∧
    ∀ ξ ∈ T, wbat w wA z v β ξ = c ξ}

/-- The three words of the curve `w_β = u_0 + β u_1 + β² u_2`. -/
noncomputable def curveU {n : ℕ} (w wA : L → F) (z : Fin n → F) (v : F) : Fin 3 → L → F :=
  ![w, wA, virt w wA z v]

lemma curve_eq {n : ℕ} (w wA : L → F) (z : Fin n → F) (v β : F) :
    (∑ i : Fin 3, β ^ (i : ℕ) • curveU w wA z v i) = wbat w wA z v β := by
  simp [curveU, wbat, Fin.sum_univ_three]

/-- The polynomial `d_ξ(Z) = (u_0 - ĉ_0)(ξ) + Z (u_1 - ĉ_1)(ξ) + Z² (u_2 - ĉ_2)(ξ)`. -/
noncomputable def dpoly (a : Fin 3 → F) : F[X] := C (a 0) + C (a 1) * X + C (a 2) * X ^ 2

lemma natDegree_dpoly (a : Fin 3 → F) : (dpoly a).natDegree ≤ 2 := by
  unfold dpoly
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
  · simp
  · exact (natDegree_C_mul_le _ _).trans (by simp)
  · exact (natDegree_C_mul_X_pow_le _ _).trans le_rfl

lemma eval_dpoly (a : Fin 3 → F) (β : F) :
    (dpoly a).eval β = a 0 + β * a 1 + β ^ 2 * a 2 := by
  simp [dpoly]; ring

lemma dpoly_ne_zero {a : Fin 3 → F} (h : ∃ i, a i ≠ 0) : dpoly a ≠ 0 := by
  obtain ⟨i, hi⟩ := h
  intro h0
  have c0 := congrArg (fun P : F[X] => P.coeff 0) h0
  have c1 := congrArg (fun P : F[X] => P.coeff 1) h0
  have c2 := congrArg (fun P : F[X] => P.coeff 2) h0
  simp [dpoly, coeff_X_pow, coeff_X, coeff_C] at c0 c1 c2
  fin_cases i <;> simp_all

/-- **Lemma 7.4 (batching).** Let `Y ⊆ L` and let `𝒢` be the set of `β` for which `w_β` agrees
with a codeword of `𝒞_0` on a fibre-closed `T ⊆ Y` with `|T| ≥ (1-δ)M`.  If `|𝒢| > 2M`, there is
`f` with `f(z) = v` such that `w` agrees with `Enc(f)` on a fibre-closed subset of `Y` of size at
least `(1-δ)M`. -/
theorem batching [Fintype F] [DecidableEq F] {m ℓ R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hR : 2 ≤ R) {δ : ℚ} (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (w wA : L → F) (z : Fin (m + ℓ) → F) (v : F) (Y : Set L)
    (hG : 2 * Nat.card L < (goodBeta δ w wA z v Y).ncard) :
    ∃ α : Table F (m + ℓ), cEval α z = v ∧ ∃ T ⊆ Y, (∀ ξ ∈ T, negPt ξ ∈ T) ∧
      (1 - δ) * Nat.card L ≤ T.ncard ∧ ∀ ξ ∈ T, w ξ = encode L α ξ := by
  classical
  haveI := hL.finite
  letI : Fintype L := Fintype.ofFinite L
  have hcardL : Nat.card L = 2 ^ (m + ℓ + R) := hL
  have hNM : 2 ^ (m + ℓ) ≤ Nat.card L := by
    rw [hcardL]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrate : rate L (2 ^ (m + ℓ)) = 1 / 2 ^ R := by
    rw [rate, hcardL]; push_cast
    rw [pow_add (2 : ℚ) (m + ℓ) R]
    have : (2 : ℚ) ^ (m + ℓ) ≠ 0 := by positivity
    field_simp
  have hδ' : δ ≤ (1 - rate L (2 ^ (m + ℓ))) / 2 := by rw [hrate]; exact hδ
  set u := curveU w wA z v
  -- correlated agreement for the curve of degree 2
  have hGZ : goodBeta δ w wA z v Y ⊆
      {β : F | DistLE (∑ i : Fin (2 + 1), β ^ (i : ℕ) • u i) (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ} := by
    rintro β ⟨c, hc, T, -, -, hT, hagree⟩
    refine ⟨c, hc, ?_⟩
    rw [curve_eq]
    exact relDist_le_of_agree T hT hagree
  have hZ : 2 * Nat.card L <
      {β : F | DistLE (∑ i : Fin (2 + 1), β ^ (i : ℕ) • u i) (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ}.ncard :=
    lt_of_lt_of_le hG (Set.ncard_le_ncard hGZ (Set.toFinite _))
  obtain ⟨L', hL', c, hc, hagreeL'⟩ :=
    bciks_curves L (m + ℓ + R) hL (2 ^ (m + ℓ)) Nat.one_le_two_pow hNM δ hδ0 hδ' 2 (by norm_num) u hZ
  -- the agreement set
  set Agr : Set L := {ξ | ∀ i, u i ξ = c i ξ}
  have hAgr : (1 - δ) * Nat.card L ≤ Agr.ncard := by
    refine hL'.trans ?_
    exact_mod_cast Set.ncard_le_ncard (fun ξ hξ => hagreeL' ξ hξ) (Set.toFinite _)
  -- the polynomials of the codewords
  obtain ⟨hP0, hev0⟩ := polyOf_spec hNM (hc 0)
  obtain ⟨hP1, hev1⟩ := polyOf_spec hNM (hc 1)
  obtain ⟨hP2, hev2⟩ := polyOf_spec hNM (hc 2)
  -- the value
  have hrc := rate_condition (n := m + ℓ) hR hδ
  have hS : 2 * 2 ^ (m + ℓ) < Agr.ncard := by
    have : (2 * 2 ^ (m + ℓ) : ℚ) < Agr.ncard := by
      calc (2 * 2 ^ (m + ℓ) : ℚ) = 2 * (2 : ℚ) ^ (m + ℓ) := by simp
        _ < (1 - δ) * 2 ^ (m + ℓ + R) := hrc
        _ = (1 - δ) * Nat.card L := by rw [hcardL]; push_cast; ring
        _ ≤ Agr.ncard := hAgr
    exact_mod_cast this
  have hval : v = (polyOf (c 0) * kernel z).coeff (2 ^ (m + ℓ) - 1) := by
    refine value_of_agreement (w := w) (wA := wA) z v hP0 hP1 hP2 Agr hS (fun ξ hξ => ?_)
    have e0 := congrFun hev0 ξ
    have e1 := congrFun hev1 ξ
    have e2 := congrFun hev2 ξ
    simp only [ev] at e0 e1 e2
    refine ⟨?_, ?_, ?_⟩
    · rw [e0]; exact hξ 0
    · rw [e1]; exact hξ 1
    · rw [e2]; exact hξ 2
  set α : Table F (m + ℓ) := kronCoeffs (m + ℓ) (polyOf (c 0))
  have hαv : cEval α z = v := by rw [hval, extraction' hP0]
  have hencα : encode L α = c 0 := by rw [encode, kronEnc_kronCoeffs hP0, hev0]
  -- the bad challenges
  let a : L → Fin 3 → F := fun ξ i => u i ξ - c i ξ
  let Bad : Set F := {β | ∃ ξ : L, ξ ∉ Agr ∧ (dpoly (a ξ)).eval β = 0}
  have hBad : Bad.ncard ≤ 2 * Nat.card L := by
    have hsub : (univ.filter fun β : F => ∃ ξ : L, ξ ∉ Agr ∧ (dpoly (a ξ)).eval β = 0) ⊆
        univ.biUnion (fun ξ : L =>
          if ξ ∈ Agr then ∅ else univ.filter fun β : F => (dpoly (a ξ)).eval β = (0 : F[X]).eval β) := by
      intro β hβ
      simp only [mem_filter, mem_univ, true_and] at hβ
      obtain ⟨ξ, hξ, h0⟩ := hβ
      simp only [mem_biUnion, mem_univ, true_and]
      exact ⟨ξ, by simp [hξ, h0]⟩
    have hcard := (card_le_card hsub).trans card_biUnion_le
    have hle : ∀ ξ : L, (if ξ ∈ Agr then (∅ : Finset F) else univ.filter fun β : F =>
        (dpoly (a ξ)).eval β = (0 : F[X]).eval β).card ≤ 2 := by
      intro ξ
      split_ifs with hξ
      · simp
      · refine card_agree_le_two _ _ (dpoly_ne_zero ?_) (natDegree_dpoly _) (by simp)
        by_contra hall
        push_neg at hall
        exact hξ (fun i => sub_eq_zero.1 (hall i))
    rw [← card_filter_eq_ncard]
    calc _ ≤ _ := hcard
      _ ≤ ∑ _ξ : L, 2 := sum_le_sum (fun ξ _ => hle ξ)
      _ = 2 * Nat.card L := by rw [sum_const, card_univ, smul_eq_mul, Nat.card_eq_fintype_card,
          mul_comm]
  -- a good `β` outside `Bad`
  obtain ⟨β, hβG, hβB⟩ : ∃ β ∈ goodBeta δ w wA z v Y, β ∉ Bad := by
    by_contra hne
    push_neg at hne
    have := Set.ncard_le_ncard (fun β hβ => hne β hβ) (Set.toFinite Bad)
    omega
  obtain ⟨cβ, hcβ, T, hTY, hTneg, hTcard, hTagree⟩ := hβG
  set ch := c 0 + β • c 1 + β ^ 2 • c 2
  have hch : ch ∈ RS L (2 ^ (m + ℓ)) :=
    Submodule.add_mem _ (Submodule.add_mem _ (hc 0) (Submodule.smul_mem _ _ (hc 1)))
      (Submodule.smul_mem _ _ (hc 2))
  have hwbat : ∀ ξ, wbat w wA z v β ξ - ch ξ = (dpoly (a ξ)).eval β := by
    intro ξ
    rw [eval_dpoly, ← curve_eq]
    simp [a, ch, u, curveU, Fin.sum_univ_three]
    ring
  -- `c_β = ĉ`
  have hceq : cβ = ch := by
    by_contra hne
    have hlt := RS_agree_lt hcβ hch hne
    have hsub : T ∩ Agr ⊆ agreeSet cβ ch := by
      rintro ξ ⟨hξT, hξA⟩
      show cβ ξ = ch ξ
      rw [← hTagree ξ hξT]
      have := hwbat ξ
      rw [eval_dpoly] at this
      have h0 : a ξ = 0 := funext fun i => sub_eq_zero.2 (hξA i)
      rw [h0] at this
      simp at this
      exact sub_eq_zero.1 this
    have h1 : (T ∩ Agr).ncard ≤ (agreeSet cβ ch).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_inter_add_ncard_union T Agr
    have h3 : (T ∪ Agr).ncard ≤ Nat.card L := by
      rw [← Set.ncard_univ]; exact Set.ncard_le_ncard (Set.subset_univ _)
    have h4 : (2 ^ (m + ℓ) : ℚ) ≤ (1 - 2 * δ) * Nat.card L := by
      rw [hcardL]; push_cast
      rw [show (2 : ℚ) ^ (m + ℓ + R) = 2 ^ (m + ℓ) * 2 ^ R from pow_add _ _ _]
      have hR' : (0 : ℚ) < 2 ^ R := by positivity
      have hδ2 : 1 / 2 ^ R ≤ 1 - 2 * δ := by linarith
      calc (2 : ℚ) ^ (m + ℓ) = 1 / 2 ^ R * (2 ^ (m + ℓ) * 2 ^ R) := by field_simp
        _ ≤ (1 - 2 * δ) * (2 ^ (m + ℓ) * 2 ^ R) := by
          apply mul_le_mul_of_nonneg_right hδ2 (by positivity)
    have h1' : ((T ∩ Agr).ncard : ℚ) ≤ (agreeSet cβ ch).ncard := by exact_mod_cast h1
    have h2' : ((T ∩ Agr).ncard : ℚ) + (T ∪ Agr).ncard = T.ncard + Agr.ncard := by
      exact_mod_cast h2
    have h3' : ((T ∪ Agr).ncard : ℚ) ≤ Nat.card L := by exact_mod_cast h3
    have hlt' : ((agreeSet cβ ch).ncard : ℚ) < 2 ^ (m + ℓ) := by exact_mod_cast hlt
    linarith
  -- `T ⊆ Agr`
  have hTA : T ⊆ Agr := by
    intro ξ hξ
    by_contra hξA
    apply hβB
    refine ⟨ξ, hξA, ?_⟩
    rw [← hwbat, hTagree ξ hξ, hceq, sub_self]
  refine ⟨α, hαv, T, hTY, hTneg, hTcard, fun ξ hξ => ?_⟩
  rw [hencα]
  exact hTA hξ 0

/-- **Lemma 7.4, `Y = L`:** if `|𝒢| > 2M`, the instance `(w; z, v)` has a witness. -/
theorem batching_witness [Fintype F] [DecidableEq F] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (w wA : L → F) (z : Fin (m + ℓ) → F) (v : F)
    (hG : 2 * Nat.card L < (goodBeta δ w wA z v Set.univ).ncard) :
    ∃ α : Table F (m + ℓ), RelKF δ w z v α := by
  obtain ⟨α, hαv, T, -, hTneg, hTcard, hTagree⟩ := batching hL hR hδ0 hδ w wA z v _ hG
  haveI := hL.finite
  refine ⟨α, fibDist_le_of_closed (hL.neg_one_mem (by omega))
    (two_ne_zero_of_smooth hL (by omega)) T hTneg hTcard hTagree, hαv⟩

end Batching

/-! ### Theorem 7.8 (soundness) -/

section Sound

variable {L : Subgroup Fˣ}

/-- `ε_KF = 2M/|F| + ε_fold + (1-δ)^κ`. -/
noncomputable def epsKF (F : Type*) [Fintype F] (μ ℓ κ : ℕ) (δ : ℚ) : ℚ :=
  2 * 2 ^ μ / Fintype.card F + epsFold F μ ℓ + (1 - δ) ^ κ

/-- `ε_KF < 3M/|F| + (1-δ)^κ`. -/
theorem epsKF_lt (F : Type*) [Fintype F] [Nonempty F] {μ ℓ : ℕ} (h : ℓ ≤ μ) (κ : ℕ) (δ : ℚ) :
    epsKF F μ ℓ κ δ < 3 * 2 ^ μ / Fintype.card F + (1 - δ) ^ κ := by
  have := epsFold_lt F h
  unfold epsKF
  have e : (3 : ℚ) * 2 ^ μ / Fintype.card F = 2 * 2 ^ μ / Fintype.card F + 2 ^ μ / Fintype.card F := by
    ring
  rw [e]; linarith

lemma expect_le_of_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℚ) (ε : ℚ) (h : ∀ ω, f ω ≤ ε) :
    expect f ≤ ε := by
  have hc : (0 : ℚ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  rw [expect, div_le_iff₀ hc]
  calc ∑ ω, f ω ≤ ∑ _ω : Ω, ε := sum_le_sum fun ω _ => h ω
    _ = ε * Fintype.card Ω := by rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]

/-- The key step of Theorems 5.24 and 7.8: if `r` is good and `dens_ℓ(w_ℓ) ≥ 1 - δ`, then
`β ∈ 𝒢`. -/
theorem mem_goodBeta_of_dens {m ℓ R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    {δ : ℚ} (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : FTProver F L) (hdeg : P.DegOK m)
    (w wA : L → F) (z : Fin (m + ℓ) → F) (v β : F) (r : ℕ → F)
    (hgood : ¬ NotGood P m ℓ (wbat w wA z v β) δ r)
    (hd : 1 - δ ≤ dens P ℓ (wbat w wA z v β) r ℓ (P.W ℓ (wbat w wA z v β) r ℓ)) :
    β ∈ goodBeta δ w wA z v Set.univ := by
  haveI := hL.finite
  obtain ⟨-, hmem, hagree, -⟩ := chain_final hL hℓ hδ hdeg r (fun j hj => by
    by_contra hb; exact hgood ⟨j, hj, hb⟩) hd
  have hLpos : (0 : ℚ) < Nat.card L := by
    haveI : Nonempty L := ⟨1⟩; exact_mod_cast Nat.card_pos
  refine ⟨_, hmem, _, Set.subset_univ _, fun ξ hξ => negPt_mem_Wset
    (lv_neg_one_mem hL (j := 0) (by omega)) r ℓ _ ξ hξ, ?_, fun ξ hξ => (hagree ξ hξ).1⟩
  rw [dens, le_div_iff₀ hLpos] at hd
  exact hd

/-- **Theorem 7.8 (soundness).** Let `R ≥ 2`, `1 ≤ ℓ`, `0 < δ ≤ (1-ρ)/2`, and let `(w; z, v)` have
no witness in `R^δ_KF`.  Then every causal prover whose final polynomials lie in `F[X]_{<N_ℓ}` is
accepted with probability at most `ε_KF = 2M/|F| + ε_fold + (1-δ)^κ`. -/
theorem soundness [Fintype F] [DecidableEq F] [Fintype L] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : KFProver F L) (hC : P.Causal) (hdeg : P.DegOK m)
    (κ : ℕ) (w : L → F) (z : Fin (m + ℓ) → F) (v : F)
    (hnw : ∀ α : Table F (m + ℓ), ¬ RelKF δ w z v α) :
    P.accProb ℓ κ w z v ≤ epsKF F (m + ℓ + R) ℓ κ δ := by
  classical
  haveI : Nonempty L := ⟨1⟩
  set G := goodBeta δ w P.wA z v Set.univ
  have hG : G.ncard ≤ 2 * Nat.card L := by
    by_contra h
    push_neg at h
    obtain ⟨α, hα⟩ := batching_witness hL hR hδ0 hδ w P.wA z v h
    exact hnw α hα
  have hLpos : (0 : ℚ) < Fintype.card L := by exact_mod_cast Fintype.card_pos
  have hR' : (0 : ℚ) < 1 / 2 ^ R := by positivity
  let B : F × (Fin ℓ → F) → Prop := fun p =>
    p.1 ∈ G ∨ NotGood (P.ft p.1) m ℓ (wbat w P.wA z v p.1) δ (extR p.2)
  have hacc := accept_le (Ω' := F × (Fin ℓ → F)) κ (δ := δ) (by linarith)
    (fun p => Wset (P.ft p.1) ℓ (wbat w P.wA z v p.1) (extR p.2) ℓ
      ((P.ft p.1).W ℓ (wbat w P.wA z v p.1) (extR p.2) ℓ))
    (fun p ξ => P.Accepts ℓ w z v p.1 (extR p.2) ξ) B
    (fun p ξ h t => (queryOK_iff hℓ _ _).1 (h t)) (by
      rintro ⟨β, ρ⟩ hB
      simp only [B, not_or] at hB
      by_contra hlt
      push_neg at hlt
      apply hB.1
      refine mem_goodBeta_of_dens hL hℓ hδ (P.ft β) (hdeg β) w P.wA z v β (extR ρ) hB.2 ?_
      rw [dens, Nat.card_eq_fintype_card, le_div_iff₀ hLpos]
      exact hlt.le)
  refine hacc.trans ?_
  unfold epsKF
  have hB1 : prob B ≤ prob (fun p : F × (Fin ℓ → F) => p.1 ∈ G) +
      prob (fun p : F × (Fin ℓ → F) => NotGood (P.ft p.1) m ℓ (wbat w P.wA z v p.1) δ (extR p.2)) :=
    prob_or_le _ _
  have hB2 : prob (fun p : F × (Fin ℓ → F) => p.1 ∈ G) ≤ 2 * 2 ^ (m + ℓ + R) / Fintype.card F := by
    haveI : Nonempty (Fin ℓ → F) := ⟨fun _ => 0⟩
    rw [prob_fst (fun β : F => β ∈ G), prob_def, card_filter_eq_ncard]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have : (Nat.card L : ℚ) = 2 ^ (m + ℓ + R) := by exact_mod_cast (hL : Nat.card L = _)
    rw [← this]; exact_mod_cast hG
  have hB3 : prob (fun p : F × (Fin ℓ → F) =>
      NotGood (P.ft p.1) m ℓ (wbat w P.wA z v p.1) δ (extR p.2)) ≤ epsFold F (m + ℓ + R) ℓ := by
    rw [prob_prod_eq_expect (fun β ρ => NotGood (P.ft β) m ℓ (wbat w P.wA z v β) δ (extR ρ))]
    haveI : Nonempty F := ⟨0⟩
    exact expect_le_of_le _ _ (fun β => prob_notGood_le hL hδ0 hδ (hC β))
  linarith

/-- `Π^C_KF` (Definition 6.8 with a set `C` of committed levels): the verifier accepts
`(β, r, ξ)` if the verifier of `Π^C_FT` accepts on `w_0 = w_β`. -/
def KFProver.AcceptsC (P : KFProver F L) (C : Set ℕ) (ℓ : ℕ) {n κ : ℕ} (w : L → F)
    (z : Fin n → F) (v : F) (β : F) (r : ℕ → F) (ξ : Fin κ → L) : Prop :=
  (P.ft β).AcceptsC C ℓ (wbat w P.wA z v β) r ξ

noncomputable def KFProver.accProbC [Fintype F] [Fintype L] (P : KFProver F L) (C : Set ℕ)
    (ℓ κ : ℕ) {n : ℕ} (w : L → F) (z : Fin n → F) (v : F) : ℚ :=
  prob (fun ω : (F × (Fin ℓ → F)) × (Fin κ → L) => P.AcceptsC C ℓ w z v ω.1.1 (extR ω.1.2) ω.2)

/-- The induced prover of `Π_KF` (Proposition 5.28(1) applied for every `β`). -/
noncomputable def KFProver.inducedC (P : KFProver F L) (C : Set ℕ) {n : ℕ} (w : L → F)
    (z : Fin n → F) (v : F) : KFProver F L :=
  ⟨P.wA, fun β => (P.ft β).induced C (wbat w P.wA z v β)⟩

/-- **Theorem 7.8 for `Π^C_KF`** (§7: "the set `C` of committed levels is arbitrary"): the
soundness bound `ε_KF` holds for every set `C` of committed levels. -/
theorem soundnessC [Fintype F] [DecidableEq F] [Fintype L] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : KFProver F L) (hC : P.Causal) (hdeg : P.DegOK m)
    (C : Set ℕ) (κ : ℕ) (w : L → F) (z : Fin (m + ℓ) → F) (v : F)
    (hnw : ∀ α : Table F (m + ℓ), ¬ RelKF δ w z v α) :
    P.accProbC C ℓ κ w z v ≤ epsKF F (m + ℓ + R) ℓ κ δ := by
  have e : P.accProbC C ℓ κ w z v = (P.inducedC C w z v).accProb ℓ κ w z v := by
    unfold KFProver.accProbC KFProver.accProb
    congr 1
    funext ω
    exact propext (acceptsC_iff (P.ft ω.1.1) C ℓ _ _ _)
  rw [e]
  exact soundness hL hR hℓ hδ0 hδ (P.inducedC C w z v) (fun β => induced_causal _ C _ (hC β))
    (fun β => induced_DegOK _ C _ (hdeg β)) κ w z v hnw

end Sound

end KroneckerFRI
