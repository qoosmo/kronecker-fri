/-
KroneckerFRI/InnerProduct.lean
§2 of the research note "Sumcheck-free hypercube inner products": the protocol `Π_IP`, its
completeness, the relation `R^δ_IP`, the batching lemma for the curve of degree 3
(Lemma batch3), soundness, knowledge and binding.

Modelling (as for `Π_KF`, `KroneckerFRI/Scheme.lean`).
* `n = m + ℓ`, `N = 2^n`, `L` a smooth domain of order `M = 2^{n+R}`, `R ≥ 2`.
* The instance is `(w_a, w_b; S)`.  A deterministic prover is a `KFProver`: the round-1 oracle
  `w_A` and, for each `β`, a prover of the folding test on
  `w_0 = w_a + β w_b* + β² w_A + β³ h`.
* The challenge space is `(F × F^ℓ) × L^κ` (`β`, `r`, query points).
-/
import KroneckerFRI.TableForm
import KroneckerFRI.Batch

set_option autoImplicit false

open Polynomial Finset KBFold

namespace KroneckerFRI

variable {F : Type*} [Field F] {L : Subgroup Fˣ}

/-! ### Correlated agreement on a common fibre-closed set -/

section CurveAgreement

/-- Batching step shared by Lemma 7.4 of Kronecker-FRI and Lemma batch3 of the note, for a curve
of any degree `t ≥ 1`: if more than `t M` challenges `β` make `∑ β^i u_i` agree with a codeword
on a fibre-closed set of `(1-δ)M` points, then all the `u_i` agree with codewords `c_i` on one
common fibre-closed set of `(1-δ)M` points. -/
theorem curve_agreement [Fintype F] [DecidableEq F] {n R : ℕ} (hL : IsSmoothDomain L (n + R))
    {δ : ℚ} (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) {t : ℕ} (ht : 1 ≤ t)
    (u : Fin (t + 1) → L → F)
    (hG : t * Nat.card L < {β : F | ∃ c ∈ RS L (2 ^ n), ∃ T : Set L, (∀ ξ ∈ T, negPt ξ ∈ T) ∧
      (1 - δ) * Nat.card L ≤ T.ncard ∧ ∀ ξ ∈ T, (∑ i : Fin (t + 1), β ^ (i : ℕ) • u i) ξ = c ξ}.ncard) :
    ∃ c : Fin (t + 1) → L → F, (∀ i, c i ∈ RS L (2 ^ n)) ∧ ∃ T : Set L,
      (∀ ξ ∈ T, negPt ξ ∈ T) ∧ (1 - δ) * Nat.card L ≤ T.ncard ∧ ∀ i, ∀ ξ ∈ T, u i ξ = c i ξ := by
  classical
  haveI := hL.finite
  letI : Fintype L := Fintype.ofFinite L
  set G := {β : F | ∃ c ∈ RS L (2 ^ n), ∃ T : Set L, (∀ ξ ∈ T, negPt ξ ∈ T) ∧
      (1 - δ) * Nat.card L ≤ T.ncard ∧ ∀ ξ ∈ T, (∑ i : Fin (t + 1), β ^ (i : ℕ) • u i) ξ = c ξ}
  have hcardL : Nat.card L = 2 ^ (n + R) := hL
  have hNM : 2 ^ n ≤ Nat.card L := by
    rw [hcardL]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrate : rate L (2 ^ n) = 1 / 2 ^ R := by
    rw [rate, hcardL]; push_cast
    rw [pow_add (2 : ℚ) n R]
    have : (2 : ℚ) ^ n ≠ 0 := by positivity
    field_simp
  have hδ' : δ ≤ (1 - rate L (2 ^ n)) / 2 := by rw [hrate]; exact hδ
  have hGZ : G ⊆ {β : F | DistLE (∑ i : Fin (t + 1), β ^ (i : ℕ) • u i)
      (RS L (2 ^ n) : Set (L → F)) δ} := by
    rintro β ⟨c, hc, T, -, hT, hagree⟩
    exact ⟨c, hc, relDist_le_of_agree T hT hagree⟩
  obtain ⟨L', hL', c, hc, hagreeL'⟩ := bciks_curves L (n + R) hL (2 ^ n) Nat.one_le_two_pow hNM
    δ hδ0 hδ' t ht u (lt_of_lt_of_le hG (Set.ncard_le_ncard hGZ (Set.toFinite _)))
  set Agr : Set L := {ξ | ∀ i, u i ξ = c i ξ}
  -- the bad challenges
  let a : L → Fin (t + 1) → F := fun ξ i => u i ξ - c i ξ
  let Bad : Set F := {β | ∃ ξ : L, ξ ∉ Agr ∧ (curvePoly (a ξ)).eval β = 0}
  have hBad : Bad.ncard ≤ t * Nat.card L := by
    have hsub : (univ.filter fun β : F => ∃ ξ : L, ξ ∉ Agr ∧ (curvePoly (a ξ)).eval β = 0) ⊆
        univ.biUnion (fun ξ : L => if ξ ∈ Agr then ∅ else (curvePoly (a ξ)).roots.toFinset) := by
      intro β hβ
      simp only [mem_filter, mem_univ, true_and] at hβ
      obtain ⟨ξ, hξ, h0⟩ := hβ
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
  obtain ⟨β, hβG, hβB⟩ : ∃ β ∈ G, β ∉ Bad := by
    by_contra hne
    push_neg at hne
    have := Set.ncard_le_ncard (fun β hβ => hne β hβ) (Set.toFinite Bad)
    omega
  obtain ⟨cβ, hcβ, T, hTneg, hTcard, hTagree⟩ := hβG
  set ch : L → F := ∑ i : Fin (t + 1), β ^ (i : ℕ) • c i
  have hch : ch ∈ RS L (2 ^ n) := Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hc i))
  have hdiff : ∀ ξ, (∑ i : Fin (t + 1), β ^ (i : ℕ) • u i) ξ - ch ξ = (curvePoly (a ξ)).eval β := by
    intro ξ
    simp only [ch, eval_curvePoly, a, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
      sum_sub_distrib]
  -- `c_β = ĉ`
  have hceq : cβ = ch := by
    by_contra hne
    have hlt := RS_agree_lt hcβ hch hne
    have hsub : T ∩ Agr ⊆ agreeSet cβ ch := by
      rintro ξ ⟨hξT, hξA⟩
      show cβ ξ = ch ξ
      rw [← hTagree ξ hξT]
      have := hdiff ξ
      have h0 : a ξ = 0 := funext fun i => sub_eq_zero.2 (hξA i)
      rw [h0, eval_curvePoly] at this
      simp only [Pi.zero_apply, mul_zero, sum_const_zero] at this
      exact sub_eq_zero.1 this
    have hAgr : (1 - δ) * Nat.card L ≤ Agr.ncard := by
      refine hL'.trans ?_
      exact_mod_cast Set.ncard_le_ncard (fun ξ hξ => hagreeL' ξ hξ) (Set.toFinite _)
    have h1 : (T ∩ Agr).ncard ≤ (agreeSet cβ ch).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_inter_add_ncard_union T Agr
    have h3 : (T ∪ Agr).ncard ≤ Nat.card L := by
      rw [← Set.ncard_univ]; exact Set.ncard_le_ncard (Set.subset_univ _)
    have h4 : (2 ^ n : ℚ) ≤ (1 - 2 * δ) * Nat.card L := by
      rw [hcardL]; push_cast
      rw [show (2 : ℚ) ^ (n + R) = 2 ^ n * 2 ^ R from pow_add _ _ _]
      have hR' : (0 : ℚ) < 2 ^ R := by positivity
      have hδ2 : 1 / 2 ^ R ≤ 1 - 2 * δ := by linarith
      calc (2 : ℚ) ^ n = 1 / 2 ^ R * (2 ^ n * 2 ^ R) := by field_simp
        _ ≤ (1 - 2 * δ) * (2 ^ n * 2 ^ R) := by
          apply mul_le_mul_of_nonneg_right hδ2 (by positivity)
    have h1' : ((T ∩ Agr).ncard : ℚ) ≤ (agreeSet cβ ch).ncard := by exact_mod_cast h1
    have h2' : ((T ∩ Agr).ncard : ℚ) + (T ∪ Agr).ncard = T.ncard + Agr.ncard := by
      exact_mod_cast h2
    have h3' : ((T ∪ Agr).ncard : ℚ) ≤ Nat.card L := by exact_mod_cast h3
    have hlt' : ((agreeSet cβ ch).ncard : ℚ) < 2 ^ n := by exact_mod_cast hlt
    linarith
  -- `T ⊆ Agr`
  have hTA : T ⊆ Agr := by
    intro ξ hξ
    by_contra hξA
    apply hβB
    refine ⟨ξ, hξA, ?_⟩
    rw [← hdiff, hTagree ξ hξ, hceq, sub_self]
  exact ⟨c, hc, T, hTneg, hTcard, fun i ξ hξ => hTA hξ i⟩

end CurveAgreement

/-! ### The protocol `Π_IP` -/

section Protocol

variable {n : ℕ}

/-- The virtual word `h(ξ) = (ξ w_a(ξ) w_b*(ξ) - w_A(ξ) - S ξ^N) / ξ^{N+1}`. -/
noncomputable def virtIP (n : ℕ) (wa wb wA : L → F) (S : F) : L → F := fun ξ =>
  (xv' ξ * wa ξ * wrev (2 ^ n) wb ξ - wA ξ - S * xv' ξ ^ (2 ^ n)) / xv' ξ ^ (2 ^ n + 1)

/-- `ξ w_a(ξ) w_b*(ξ) = w_A(ξ) + S ξ^N + ξ^{N+1} h(ξ)`. -/
theorem virtIP_identity (wa wb wA : L → F) (S : F) (ξ : L) :
    xv' ξ * wa ξ * wrev (2 ^ n) wb ξ =
      wA ξ + S * xv' ξ ^ (2 ^ n) + xv' ξ ^ (2 ^ n + 1) * virtIP n wa wb wA S ξ := by
  have h := pow_ne_zero (2 ^ n + 1) (xv'_ne_zero ξ)
  rw [virtIP, mul_div_cancel₀ _ h]; ring

/-- `h(ξ)` reads `w_a(ξ)`, `w_b(ξ⁻¹)` and `w_A(ξ)` only (Lemma rev(4)). -/
theorem virtIP_congr {wa wb wA wa' wb' wA' : L → F} (S : F) {ξ : L} (h1 : wa ξ = wa' ξ)
    (h2 : wb (invPt ξ) = wb' (invPt ξ)) (h3 : wA ξ = wA' ξ) :
    virtIP n wa wb wA S ξ = virtIP n wa' wb' wA' S ξ := by
  simp [virtIP, wrev, h1, h2, h3]

/-- The batched word `w_0 = w_a + β w_b* + β² w_A + β³ h`. -/
noncomputable def wbatIP (n : ℕ) (wa wb wA : L → F) (S β : F) : L → F :=
  wa + β • wrev (2 ^ n) wb + β ^ 2 • wA + β ^ 3 • virtIP n wa wb wA S

/-- The four words of the curve of degree 3. -/
noncomputable def curveIP (n : ℕ) (wa wb wA : L → F) (S : F) : Fin 4 → L → F :=
  ![wa, wrev (2 ^ n) wb, wA, virtIP n wa wb wA S]

lemma curveIP_eq (wa wb wA : L → F) (S β : F) :
    (∑ i : Fin 4, β ^ (i : ℕ) • curveIP n wa wb wA S i) = wbatIP n wa wb wA S β := by
  simp [curveIP, wbatIP, Fin.sum_univ_four]

/-- The verifier of `Π_IP` accepts `(β, r, ξ)` on `(w_a, w_b; S)`: all the fold checks of `Π_FT`
on `w_0` pass. -/
def AcceptsIP (P : KFProver F L) (ℓ : ℕ) {κ : ℕ} (n : ℕ) (wa wb : L → F) (S β : F) (r : ℕ → F)
    (ξ : Fin κ → L) : Prop :=
  (P.ft β).Accepts ℓ (wbatIP n wa wb P.wA S β) r ξ

noncomputable def accProbIP [Fintype F] [Fintype L] (P : KFProver F L) (ℓ κ n : ℕ)
    (wa wb : L → F) (S : F) : ℚ :=
  prob (fun ω : (F × (Fin ℓ → F)) × (Fin κ → L) =>
    AcceptsIP P ℓ n wa wb S ω.1.1 (extR ω.1.2) ω.2)

/-- **The relation `R^δ_IP`:** `(a, b)` is a witness for `(w_a, w_b; S)` iff
`Δ^fib₀(w_a, Enc^T(a)) ≤ δ`, `Δ^fib₀(w_b, Enc^T(b)) ≤ δ` and `∑_w a(w) b(w) = S`. -/
def RelIP (δ : ℚ) (wa wb : L → F) (S : F) (a b : Table F n) : Prop :=
  fibDist wa (encode L a) ≤ δ ∧ fibDist wb (encode L b) ≤ δ ∧ ∑ w, a w * b w = S

end Protocol

/-! ### Completeness -/

section Complete

variable {n : ℕ}

/-- The honest opening polynomials `A, H` of `X V_a V_b* = A + S X^N + X^{N+1} H`. -/
noncomputable def ipA (a b : Table F n) : F[X] := openAG (2 ^ n) (kronEnc a) (revP (2 ^ n) (kronEnc b))
noncomputable def ipH (a b : Table F n) : F[X] := openHG (2 ^ n) (kronEnc a) (revP (2 ^ n) (kronEnc b))

/-- The honest batched polynomial `V_a + β V_b* + β² A + β³ H`. -/
noncomputable def ipU0 (a b : Table F n) (β : F) : F[X] :=
  kronEnc a + C β * revP (2 ^ n) (kronEnc b) + C (β ^ 2) * ipA a b + C (β ^ 3) * ipH a b

lemma ipU0_mem (a b : Table F n) (β : F) : ipU0 a b β ∈ degreeLT F (2 ^ n) := by
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (kronEnc_mem_degreeLT a)
    ?_) ?_) ?_ <;> rw [← smul_eq_C_mul] <;> refine Submodule.smul_mem _ _ ?_
  · exact revP_mem _ _
  · exact openAG_mem _ _ _
  · exact openHG_mem _ _ _

/-- The honest virtual word is `ev_L(H)`. -/
theorem virtIP_honest (a b : Table F n) :
    virtIP n (encode L a) (encode L b) (ev L (ipA a b)) (∑ w, a w * b w) = ev L (ipH a b) := by
  funext ξ
  have hx := pow_ne_zero (2 ^ n + 1) (xv'_ne_zero ξ)
  have hs := congrArg (fun P : F[X] => P.eval (xv' ξ))
    (splitG_eq Nat.one_le_two_pow (kronEnc_mem_degreeLT a) (revP_mem (2 ^ n) (kronEnc b)))
  simp only [assemble, eval_add, eval_mul, eval_X, eval_C, eval_pow] at hs
  rw [virtIP, div_eq_iff hx, encode, encode, wrev_ev (kronEnc_mem_degreeLT b), inner_product]
  simp only [ev, ipA, ipH]
  rw [hs]; ring

/-- The honest batched word is the codeword `ev_L(V_a + β V_b* + β² A + β³ H)`. -/
theorem wbatIP_honest (a b : Table F n) (β : F) :
    wbatIP n (encode L a) (encode L b) (ev L (ipA a b)) (∑ w, a w * b w) β = ev L (ipU0 a b β) := by
  rw [wbatIP, virtIP_honest, ipU0, encode, encode, wrev_ev (kronEnc_mem_degreeLT b)]
  simp only [ev_add, ev_C_mul]

/-- The honest prover of `Π_IP`. -/
noncomputable def honestIP (a b : Table F n) (ℓ : ℕ) : KFProver F L :=
  ⟨ev L (ipA a b), fun β => honestFT (ipU0 a b β) ℓ⟩

/-- **Theorem (completeness):** if `w_a = Enc^T(a)`, `w_b = Enc^T(b)` and `S = ∑_w a(w) b(w)`,
the honest prover is accepted for all challenges. -/
theorem honestIP_accepts {m ℓ R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (a b : Table F (m + ℓ))
    (β : F) (r : ℕ → F) {κ : ℕ} (ξ : Fin κ → L) :
    AcceptsIP (honestIP (L := L) a b ℓ) ℓ (m + ℓ) (encode L a) (encode L b) (∑ w, a w * b w)
      β r ξ := by
  unfold AcceptsIP
  rw [show (honestIP (L := L) a b ℓ).wA = ev L (ipA a b) from rfl, wbatIP_honest]
  exact honestFT_accepts hL _ r ξ

theorem honestIP_prob_one [Fintype F] [Fintype L] {m ℓ R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (a b : Table F (m + ℓ)) (κ : ℕ) :
    accProbIP (honestIP (L := L) a b ℓ) ℓ κ (m + ℓ) (encode L a) (encode L b)
      (∑ w, a w * b w) = 1 := by
  haveI : Nonempty L := ⟨1⟩
  unfold accProbIP
  have : (fun ω : (F × (Fin ℓ → F)) × (Fin κ → L) =>
      AcceptsIP (honestIP (L := L) a b ℓ) ℓ (m + ℓ) (encode L a) (encode L b) (∑ w, a w * b w)
        ω.1.1 (extR ω.1.2) ω.2) = fun _ => True := by
    funext ω; simp only [eq_iff_iff, iff_true]; exact honestIP_accepts hL a b _ _ _
  rw [this, prob_true]

theorem honestIP_DegOK {m ℓ : ℕ} (a b : Table F (m + ℓ)) :
    (honestIP (L := L) a b ℓ).DegOK m := fun β => honestFT_DegOK (ipU0_mem a b β)

theorem honestIP_causal {n ℓ : ℕ} (a b : Table F n) : (honestIP (L := L) a b ℓ).Causal := by
  intro β j r r' h
  simp only [honestIP, honestFT]
  rw [pfoldUp_congr _ j h]

end Complete

/-! ### Lemma batch3 (batching, degree 3) -/

section Batching

/-- The set `𝒢` of Lemma batch3. -/
def goodBetaIP (n : ℕ) (δ : ℚ) (wa wb wA : L → F) (S : F) : Set F :=
  {β | ∃ c ∈ RS L (2 ^ n), ∃ T : Set L, (∀ ξ ∈ T, negPt ξ ∈ T) ∧
    (1 - δ) * Nat.card L ≤ T.ncard ∧ ∀ ξ ∈ T, wbatIP n wa wb wA S β ξ = c ξ}

/-- **Lemma batch3.** If `|𝒢| > 3M`, then `(w_a, w_b; S)` has a witness in `R^δ_IP`. -/
theorem batching_IP [Fintype F] [DecidableEq F] {n R : ℕ} (hL : IsSmoothDomain L (n + R))
    (hR : 2 ≤ R) {δ : ℚ} (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (wa wb wA : L → F) (S : F)
    (hG : 3 * Nat.card L < (goodBetaIP n δ wa wb wA S).ncard) :
    ∃ a b : Table F n, RelIP δ wa wb S a b := by
  classical
  haveI := hL.finite
  have hcardL : Nat.card L = 2 ^ (n + R) := hL
  have hNM : 2 ^ n ≤ Nat.card L := by
    rw [hcardL]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hneg : (-1 : Fˣ) ∈ L := hL.neg_one_mem (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_smooth hL (by omega)
  set u := curveIP n wa wb wA S
  obtain ⟨c, hc, T, hTneg, hTcard, hTu⟩ := curve_agreement hL hδ0 hδ (t := 3) (by norm_num) u (by
    refine lt_of_lt_of_le hG (Set.ncard_le_ncard ?_ (Set.toFinite _))
    rintro β ⟨c, hc, T, h1, h2, h3⟩
    exact ⟨c, hc, T, h1, h2, fun ξ hξ => by rw [curveIP_eq]; exact h3 ξ hξ⟩)
  obtain ⟨hP0, hev0⟩ := polyOf_spec hNM (hc 0)
  obtain ⟨hP1, hev1⟩ := polyOf_spec hNM (hc 1)
  obtain ⟨hP2, hev2⟩ := polyOf_spec hNM (hc 2)
  obtain ⟨hP3, hev3⟩ := polyOf_spec hNM (hc 3)
  set P0 := polyOf (c 0)
  set P1 := polyOf (c 1)
  set P2 := polyOf (c 2)
  set P3 := polyOf (c 3)
  have e : ∀ (i : Fin 4) (ξ : L), c i ξ = (polyOf (c i)).eval (xv' ξ) := by
    intro i ξ
    have := congrFun (polyOf_spec hNM (hc i)).2 ξ
    simp only [ev] at this
    exact this.symm
  -- the value: `Φ` vanishes on `T`, which has more than `2N` points
  have hTbig : 2 * 2 ^ n < T.ncard := by
    have hrc := rate_condition (n := n) hR hδ
    have : (2 * 2 ^ n : ℚ) < T.ncard := by
      calc (2 * 2 ^ n : ℚ) = 2 * (2 : ℚ) ^ n := by simp
        _ < (1 - δ) * 2 ^ (n + R) := hrc
        _ = (1 - δ) * Nat.card L := by rw [hcardL]; push_cast; ring
        _ ≤ T.ncard := hTcard
    exact_mod_cast this
  have hval : S = (P0 * P1).coeff (2 ^ n - 1) := by
    letI : Fintype T := Fintype.ofFinite T
    refine identityG Nat.one_le_two_pow hP2 (eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (PhiG (2 ^ n) P0 P1 P2 P3 S) (f := fun i : T => xv' (i : L)) ?_ ?_ ?_)
    · intro x y hxy
      exact Subtype.ext (Subtype.ext (Units.ext hxy))
    · intro i
      have hid := virtIP_identity (n := n) wa wb wA S (i : L)
      have h0 := hTu 0 i i.2
      have h1 := hTu 1 i i.2
      have h2' := hTu 2 i i.2
      have h3 := hTu 3 i i.2
      simp only [u, curveIP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at h0 h1 h2' h3
      rw [e 0, ← show P0 = polyOf (c 0) from rfl] at h0
      rw [e 1, ← show P1 = polyOf (c 1) from rfl] at h1
      rw [e 2, ← show P2 = polyOf (c 2) from rfl] at h2'
      rw [e 3, ← show P3 = polyOf (c 3) from rfl] at h3
      simp only [PhiG, assemble, eval_sub, eval_add, eval_mul, eval_X, eval_C, eval_pow]
      rw [← h0, ← h1, ← h2', ← h3, hid]; ring
    · rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]
      exact lt_of_le_of_lt (natDegree_PhiG_le hP0 hP1 hP2 hP3 S) hTbig
  -- the witness
  set a : Table F n := kronCoeffs n P0
  set b : Table F n := kronCoeffs n (revP (2 ^ n) P1)
  have hVa : kronEnc a = P0 := kronEnc_kronCoeffs hP0
  have hVb : kronEnc b = revP (2 ^ n) P1 := kronEnc_kronCoeffs (revP_mem _ _)
  refine ⟨a, b, ?_, ?_, ?_⟩
  · -- `w_a = Enc^T(a)` on `T`
    refine fibDist_le_of_closed hneg h2 T hTneg hTcard (fun ξ hξ => ?_)
    rw [encode, hVa, hev0]
    exact hTu 0 ξ hξ
  · -- `w_b = Enc^T(b)` on `T⁻¹`
    refine fibDist_le_of_closed hneg h2 (invPt '' T) (inv_image_closed hneg hTneg)
      (by rw [ncard_inv_image]; exact hTcard) ?_
    rintro _ ⟨ξ, hξ, rfl⟩
    have h1 : wrev (2 ^ n) wb ξ = wrev (2 ^ n) (encode L b) ξ := by
      rw [encode, hVb, wrev_ev (revP_mem _ _), revP_revP hP1, hev1]
      exact hTu 1 ξ hξ
    exact (wrev_eq_iff _ _ _ ξ).1 h1
  · -- the inner product
    rw [inner_product, hVa, hVb, revP_revP hP1, hval]

/-- **Lemma batch3** in the form used by soundness. -/
theorem card_goodBetaIP_le [Fintype F] [DecidableEq F] {n R : ℕ} (hL : IsSmoothDomain L (n + R))
    (hR : 2 ≤ R) {δ : ℚ} (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (wa wb wA : L → F) (S : F)
    (hnw : ∀ a b : Table F n, ¬ RelIP δ wa wb S a b) :
    (goodBetaIP n δ wa wb wA S).ncard ≤ 3 * Nat.card L := by
  by_contra h
  push_neg at h
  obtain ⟨a, b, hab⟩ := batching_IP hL hR hδ0 hδ wa wb wA S h
  exact hnw a b hab

end Batching

/-! ### Soundness, knowledge, binding -/

section Sound

/-- `ε_IP = 3M/|F| + ε_fold + (1-δ)^κ`. -/
noncomputable def epsIP (F : Type*) [Fintype F] (μ ℓ κ : ℕ) (δ : ℚ) : ℚ :=
  3 * 2 ^ μ / Fintype.card F + epsFold F μ ℓ + (1 - δ) ^ κ

/-- `ε_IP < 4M/|F| + (1-δ)^κ`. -/
theorem epsIP_lt (F : Type*) [Fintype F] [Nonempty F] {μ ℓ : ℕ} (h : ℓ ≤ μ) (κ : ℕ) (δ : ℚ) :
    epsIP F μ ℓ κ δ < 4 * 2 ^ μ / Fintype.card F + (1 - δ) ^ κ := by
  have := epsFold_lt F h
  unfold epsIP
  have e : (4 : ℚ) * 2 ^ μ / Fintype.card F = 3 * 2 ^ μ / Fintype.card F + 2 ^ μ / Fintype.card F := by
    ring
  rw [e]; linarith

/-- If `r` is good and `dens_ℓ(w_ℓ) ≥ 1 - δ`, then `β ∈ 𝒢`. -/
theorem mem_goodBetaIP_of_dens {m ℓ R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    {δ : ℚ} (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : FTProver F L) (hdeg : P.DegOK m)
    (wa wb wA : L → F) (S β : F) (r : ℕ → F)
    (hgood : ¬ NotGood P m ℓ (wbatIP (m + ℓ) wa wb wA S β) δ r)
    (hd : 1 - δ ≤ dens P ℓ (wbatIP (m + ℓ) wa wb wA S β) r ℓ
      (P.W ℓ (wbatIP (m + ℓ) wa wb wA S β) r ℓ)) :
    β ∈ goodBetaIP (m + ℓ) δ wa wb wA S := by
  haveI := hL.finite
  obtain ⟨-, hmem, hagree, -⟩ := chain_final hL hℓ hδ hdeg r (fun j hj => by
    by_contra hb; exact hgood ⟨j, hj, hb⟩) hd
  have hLpos : (0 : ℚ) < Nat.card L := by
    haveI : Nonempty L := ⟨1⟩; exact_mod_cast Nat.card_pos
  refine ⟨_, hmem, _, fun ξ hξ => negPt_mem_Wset
    (lv_neg_one_mem hL (j := 0) (by omega)) r ℓ _ ξ hξ, ?_, fun ξ hξ => (hagree ξ hξ).1⟩
  rw [dens, le_div_iff₀ hLpos] at hd
  exact hd

/-- **Theorem (soundness of `Π_IP`).** If `(w_a, w_b; S)` has no witness in `R^δ_IP`, every causal
prover whose final polynomials lie in `F[X]_{<N_ℓ}` is accepted with probability at most
`ε_IP = 3M/|F| + ε_fold + (1-δ)^κ`. -/
theorem soundness_IP [Fintype F] [DecidableEq F] [Fintype L] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : KFProver F L) (hC : P.Causal) (hdeg : P.DegOK m)
    (κ : ℕ) (wa wb : L → F) (S : F)
    (hnw : ∀ a b : Table F (m + ℓ), ¬ RelIP δ wa wb S a b) :
    accProbIP P ℓ κ (m + ℓ) wa wb S ≤ epsIP F (m + ℓ + R) ℓ κ δ := by
  classical
  haveI : Nonempty L := ⟨1⟩
  set G := goodBetaIP (m + ℓ) δ wa wb P.wA S
  have hG : G.ncard ≤ 3 * Nat.card L :=
    card_goodBetaIP_le (n := m + ℓ) (R := R) hL hR hδ0 hδ wa wb P.wA S hnw
  have hLpos : (0 : ℚ) < Fintype.card L := by exact_mod_cast Fintype.card_pos
  have hR' : (0 : ℚ) < 1 / 2 ^ R := by positivity
  let B : F × (Fin ℓ → F) → Prop := fun p =>
    p.1 ∈ G ∨ NotGood (P.ft p.1) m ℓ (wbatIP (m + ℓ) wa wb P.wA S p.1) δ (extR p.2)
  have hacc := accept_le (Ω' := F × (Fin ℓ → F)) κ (δ := δ) (by linarith)
    (fun p => Wset (P.ft p.1) ℓ (wbatIP (m + ℓ) wa wb P.wA S p.1) (extR p.2) ℓ
      ((P.ft p.1).W ℓ (wbatIP (m + ℓ) wa wb P.wA S p.1) (extR p.2) ℓ))
    (fun p ξ => AcceptsIP P ℓ (m + ℓ) wa wb S p.1 (extR p.2) ξ) B
    (fun p ξ h t => (queryOK_iff hℓ _ _).1 (h t)) (by
      rintro ⟨β, ρ⟩ hB
      simp only [B, not_or] at hB
      by_contra hlt
      push_neg at hlt
      apply hB.1
      refine mem_goodBetaIP_of_dens hL hℓ hδ (P.ft β) (hdeg β) wa wb P.wA S β (extR ρ) hB.2 ?_
      rw [dens, Nat.card_eq_fintype_card, le_div_iff₀ hLpos]
      exact hlt.le)
  refine hacc.trans ?_
  unfold epsIP
  have hB1 : prob B ≤ prob (fun p : F × (Fin ℓ → F) => p.1 ∈ G) +
      prob (fun p : F × (Fin ℓ → F) =>
        NotGood (P.ft p.1) m ℓ (wbatIP (m + ℓ) wa wb P.wA S p.1) δ (extR p.2)) :=
    prob_or_le _ _
  have hB2 : prob (fun p : F × (Fin ℓ → F) => p.1 ∈ G) ≤ 3 * 2 ^ (m + ℓ + R) / Fintype.card F := by
    haveI : Nonempty (Fin ℓ → F) := ⟨fun _ => 0⟩
    rw [prob_fst (fun β : F => β ∈ G), prob_def, card_filter_eq_ncard]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have : (Nat.card L : ℚ) = 2 ^ (m + ℓ + R) := by exact_mod_cast (hL : Nat.card L = _)
    rw [← this]; exact_mod_cast hG
  have hB3 : prob (fun p : F × (Fin ℓ → F) =>
      NotGood (P.ft p.1) m ℓ (wbatIP (m + ℓ) wa wb P.wA S p.1) δ (extR p.2)) ≤
        epsFold F (m + ℓ + R) ℓ := by
    rw [prob_prod_eq_expect (fun β ρ =>
      NotGood (P.ft β) m ℓ (wbatIP (m + ℓ) wa wb P.wA S β) δ (extR ρ))]
    haveI : Nonempty F := ⟨0⟩
    exact expect_le_of_le _ _ (fun β => prob_notGood_le hL hδ0 hδ (hC β))
  linarith

/-- **Knowledge:** if the verifier accepts with probability greater than `ε_IP`, the instance has a
witness. -/
theorem knowledge_IP [Fintype F] [DecidableEq F] [Fintype L] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : KFProver F L) (hC : P.Causal) (hdeg : P.DegOK m)
    (κ : ℕ) (wa wb : L → F) (S : F)
    (hacc : epsIP F (m + ℓ + R) ℓ κ δ < accProbIP P ℓ κ (m + ℓ) wa wb S) :
    ∃ a b : Table F (m + ℓ), RelIP δ wa wb S a b := by
  by_contra h
  push_neg at h
  have := soundness_IP hL hR hℓ hδ0 hδ P hC hdeg κ wa wb S h
  linarith

/-- The witness of `R^δ_IP` is unique (unique decoding, Lemma 6.3(2)). -/
theorem RelIP_unique {m ℓ R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 1 ≤ R) {δ : ℚ}
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) {wa wb : L → F} {S S' : F} {a b a' b' : Table F (m + ℓ)}
    (h : RelIP δ wa wb S a b) (h' : RelIP δ wa wb S' a' b') : a = a' ∧ b = b' ∧ S = S' := by
  haveI := hL.finite
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
  have ha := encode_fib_unique hNM hneg h2 hδ' wa h.1 h'.1
  have hb := encode_fib_unique hNM hneg h2 hδ' wb h.2.1 h'.2.1
  refine ⟨ha, hb, ?_⟩
  rw [← h.2.2, ← h'.2.2, ha, hb]

/-- **Binding:** for fixed commitments `w_a, w_b`, two different claimed inner products cannot
both be accepted with probability greater than `ε_IP`. -/
theorem binding_IP [Fintype F] [DecidableEq F] [Fintype L] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P P' : KFProver F L) (hC : P.Causal) (hdeg : P.DegOK m)
    (hC' : P'.Causal) (hdeg' : P'.DegOK m) (κ : ℕ) (wa wb : L → F) {S S' : F} (hS : S ≠ S') :
    ¬ (epsIP F (m + ℓ + R) ℓ κ δ < accProbIP P ℓ κ (m + ℓ) wa wb S ∧
        epsIP F (m + ℓ + R) ℓ κ δ < accProbIP P' ℓ κ (m + ℓ) wa wb S') := by
  rintro ⟨h1, h2⟩
  obtain ⟨a, b, hab⟩ := knowledge_IP hL hR hℓ hδ0 hδ P hC hdeg κ wa wb S h1
  obtain ⟨a', b', hab'⟩ := knowledge_IP hL hR hℓ hδ0 hδ P' hC' hdeg' κ wa wb S' h2
  exact hS (RelIP_unique hL (by omega) hδ hab hab').2.2

/-- `Π^C_IP`: the verifier accepts `(β, r, ξ)` if the verifier of `Π^C_FT` accepts on `w_0`. -/
def AcceptsIPC (P : KFProver F L) (C : Set ℕ) (ℓ : ℕ) {κ : ℕ} (n : ℕ) (wa wb : L → F) (S β : F)
    (r : ℕ → F) (ξ : Fin κ → L) : Prop :=
  (P.ft β).AcceptsC C ℓ (wbatIP n wa wb P.wA S β) r ξ

noncomputable def accProbIPC [Fintype F] [Fintype L] (P : KFProver F L) (C : Set ℕ) (ℓ κ n : ℕ)
    (wa wb : L → F) (S : F) : ℚ :=
  prob (fun ω : (F × (Fin ℓ → F)) × (Fin κ → L) =>
    AcceptsIPC P C ℓ n wa wb S ω.1.1 (extR ω.1.2) ω.2)

/-- The induced prover of `Π_IP` (Proposition 5.28(1) for every `β`). -/
noncomputable def inducedIP (P : KFProver F L) (C : Set ℕ) (n : ℕ) (wa wb : L → F) (S : F) :
    KFProver F L :=
  ⟨P.wA, fun β => (P.ft β).induced C (wbatIP n wa wb P.wA S β)⟩

/-- **Soundness of `Π^C_IP`** for every set `C` of committed levels (arity `2^k`). -/
theorem soundnessC_IP [Fintype F] [DecidableEq F] [Fintype L] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : KFProver F L) (hC : P.Causal) (hdeg : P.DegOK m)
    (C : Set ℕ) (κ : ℕ) (wa wb : L → F) (S : F)
    (hnw : ∀ a b : Table F (m + ℓ), ¬ RelIP δ wa wb S a b) :
    accProbIPC P C ℓ κ (m + ℓ) wa wb S ≤ epsIP F (m + ℓ + R) ℓ κ δ := by
  have e : accProbIPC P C ℓ κ (m + ℓ) wa wb S =
      accProbIP (inducedIP P C (m + ℓ) wa wb S) ℓ κ (m + ℓ) wa wb S := by
    unfold accProbIPC accProbIP
    congr 1
    funext ω
    exact propext (acceptsC_iff (P.ft ω.1.1) C ℓ _ _ _)
  rw [e]
  exact soundness_IP hL hR hℓ hδ0 hδ (inducedIP P C (m + ℓ) wa wb S)
    (fun β => induced_causal _ C _ (hC β)) (fun β => induced_DegOK _ C _ (hdeg β)) κ wa wb S hnw

end Sound

end KroneckerFRI
