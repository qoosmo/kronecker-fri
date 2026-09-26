/-
KroneckerFRI/Hadamard.lean
§3 of the research note "Sumcheck-free hypercube inner products": the Hadamard check `Π_Had`
proving `a(w) b(w) = c(w)` for all `w`, for three committed tables.

Modelling.
* `n = m + ℓ`, `N = 2^n`, `L` a smooth domain of order `M = 2^{n+R}`, `R ≥ 2`.
* The challenges `γ, θ, β` are uniform in `F` (the verifier does not restrict them).  Soundness
  holds for all values; completeness holds when the three poles `γθ, θ, γ` lie outside `L`.
* A deterministic prover (`HadProver`) sends `w_Q` as a function of `γ`; `y₁`, `y₃`, `w_A` as
  functions of `(γ, θ)`; and, for each `(γ, θ, β)`, a prover of the folding test on the batched
  word `w_0 = ∑_{i ≤ 8} β^i u_i`.
* The challenge space is `(F × F) × ((F × F^ℓ) × L^κ)`: `(γ, θ)`, then `(β, r, ξ)`.
-/
import KroneckerFRI.InnerProduct

set_option autoImplicit false

open Polynomial Finset KBFold

namespace KroneckerFRI

variable {F : Type*} [Field F] {L : Subgroup Fˣ}

/-! ### Quotient words and the DEEP step (Lemma deep) -/

section Deep

/-- The quotient word `q[w, y, x](ξ) = (w(ξ) - y) / (ξ - x)`. -/
noncomputable def qword (w : L → F) (y x : F) : L → F := fun ξ => (w ξ - y) / (xv' ξ - x)

/-- **Lemma deep.** If `w = ev(P)` and `q[w, y, x] = ev(R)` on `T ⊆ L`, with `P, R ∈ F[X]_{<N}`
and more than `N + 1` points in `T`, then `P(x) = y`.  (The pole `x` may lie in `L`: it removes
at most one point of `T`.) -/
theorem deep_step [Finite L] {N : ℕ} {w : L → F} {y x : F} {P R : F[X]} (hP : P ∈ degreeLT F N)
    (hR : R ∈ degreeLT F N) (T : Set L) (hT : N + 1 < T.ncard)
    (hw : ∀ ξ ∈ T, w ξ = P.eval (xv' ξ)) (hq : ∀ ξ ∈ T, qword w y x ξ = R.eval (xv' ξ)) :
    P.eval x = y := by
  classical
  set T' : Set L := {ξ | ξ ∈ T ∧ xv' ξ ≠ x}
  have hT' : N < T'.ncard := by
    have hsub : T ⊆ T' ∪ {ξ | xv' ξ = x} := by
      intro ξ hξ
      by_cases h : xv' ξ = x
      · exact Or.inr h
      · exact Or.inl ⟨hξ, h⟩
    have hone : {ξ : L | xv' ξ = x}.ncard ≤ 1 := by
      rw [Set.ncard_le_one]
      intro a ha b hb
      exact Subtype.ext (Units.ext (ha.trans hb.symm))
    have := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)
    omega
  set Φ : F[X] := (X - C x) * R - P + C y
  have hΦdeg : Φ.natDegree ≤ N := by
    have h1 := natDegree_le_of_mem_degreeLT hR
    have h2 := natDegree_le_of_mem_degreeLT hP
    have hXR : ((X - C x) * R).natDegree ≤ N := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · have : R = 0 := by
          rw [h0, mem_degreeLT] at hR; exact degree_eq_bot.1 (by simpa using hR)
        simp [this]
      · refine (natDegree_mul_le).trans ?_
        rw [natDegree_X_sub_C]; omega
    refine (natDegree_add_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le hXR ?_)) ?_)
    · omega
    · simp
  have hΦ : Φ = 0 := by
    letI : Fintype T' := Fintype.ofFinite T'
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero Φ (f := fun i : T' => xv' (i : L)) ?_ ?_ ?_
    · intro a b hab
      exact Subtype.ext (Subtype.ext (Units.ext hab))
    · intro i
      obtain ⟨hiT, hix⟩ := i.2
      have e1 := hw i hiT
      have e2 := hq i hiT
      simp only [qword] at e2
      have hne : xv' (i : L) - x ≠ 0 := sub_ne_zero.2 hix
      rw [div_eq_iff hne] at e2
      simp only [Φ, eval_add, eval_sub, eval_mul, eval_X, eval_C]
      rw [← e1]
      linear_combination -e2
    · rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]; omega
  have h := congrArg (fun Q : F[X] => Q.eval x) hΦ
  simp only [Φ, eval_add, eval_sub, eval_mul, eval_X, eval_C, sub_self, zero_mul, eval_zero] at h
  linear_combination -h

/-- **Lemma deep (converse):** for `P(x) = y` and `x ∉ L`, `q[ev P, y, x] = ev((P - y)/(X - x))`,
a polynomial of degree `< N` when `P ∈ F[X]_{<N}`. -/
theorem deep_honest {N : ℕ} {P : F[X]} (hP : P ∈ degreeLT F N) (x : F)
    (hx : ∀ ξ : L, xv' ξ ≠ x) :
    qword (ev L P) (P.eval x) x = ev L ((P - C (P.eval x)) /ₘ (X - C x)) ∧
      (P - C (P.eval x)) /ₘ (X - C x) ∈ degreeLT F N := by
  have hroot : IsRoot (P - C (P.eval x)) x := by simp [IsRoot]
  have hmul := (mul_divByMonic_eq_iff_isRoot).2 hroot
  constructor
  · funext ξ
    simp only [qword, ev]
    have hne : xv' ξ - x ≠ 0 := sub_ne_zero.2 (hx ξ)
    rw [div_eq_iff hne]
    have := congrArg (fun Q : F[X] => Q.eval (xv' ξ)) hmul
    simp only [eval_mul, eval_sub, eval_X, eval_C] at this
    rw [mul_comm]; exact this.symm
  · rw [mem_degreeLT]
    have hdeg : (P - C (P.eval x)) ∈ degreeLT F N := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · have : P = 0 := by
          rw [h0, mem_degreeLT] at hP; exact degree_eq_bot.1 (by simpa using hP)
        simp [this]
      · refine Submodule.sub_mem _ hP ?_
        rw [mem_degreeLT]; exact (degree_C_le).trans_lt (by exact_mod_cast h0)
    rw [mem_degreeLT] at hdeg
    exact (degree_divByMonic_le _ _).trans_lt hdeg

end Deep

/-! ### Geometric weights -/

section Weights

variable {n : ℕ}

/-- The table `w ↦ γ^w a(w)`, so that `V_{γ·a}(X) = V_a(γ X)`. -/
def gscale (γ : F) (a : Table F n) : Table F n := fun w => γ ^ bitsToNat w * a w

lemma eval_kronEnc (a : Table F n) (x : F) : (kronEnc a).eval x = ∑ w, a w * x ^ bitsToNat w := by
  simp [kronEnc, eval_finset_sum]

/-- `V_{γ·a}(θ) = V_a(γ θ)`. -/
theorem eval_gscale (γ θ : F) (a : Table F n) :
    (kronEnc (gscale γ a)).eval θ = (kronEnc a).eval (γ * θ) := by
  rw [eval_kronEnc, eval_kronEnc]
  refine sum_congr rfl (fun w _ => ?_)
  simp only [gscale, mul_pow]; ring

/-- `∑_w γ^w a(w) b(w) = [X^{N-1}] V_a(γX) V_b*`. -/
theorem weighted_inner_product (γ : F) (a b : Table F n) :
    ∑ w, γ ^ bitsToNat w * (a w * b w) =
      (kronEnc (gscale γ a) * revP (2 ^ n) (kronEnc b)).coeff (2 ^ n - 1) := by
  rw [← inner_product]
  exact sum_congr rfl (fun w _ => by simp [gscale]; ring)

end Weights

/-! ### A generic bound for one folding test on a family of batched words -/

section Generic

/-- The `β` for which `w_0(β)` agrees with a codeword of `𝒞_0` on a fibre-closed set of at least
`(1-δ)M` points. -/
def goodSet (n : ℕ) (δ : ℚ) (w0 : F → L → F) : Set F :=
  {β | ∃ c ∈ RS L (2 ^ n), ∃ T : Set L, (∀ ξ ∈ T, negPt ξ ∈ T) ∧
    (1 - δ) * Nat.card L ≤ T.ncard ∧ ∀ ξ ∈ T, w0 β ξ = c ξ}

/-- The argument of KF Theorem 7.8 for any family of words `w_0(β)`: the acceptance probability
over `(β, r, ξ)` is at most `|𝒢|/|F| + ε_fold + (1-δ)^κ`. -/
theorem ft_family_bound [Fintype F] [DecidableEq F] [Fintype L] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (ft : F → FTProver F L) (hC : ∀ β, (ft β).Causal)
    (hdeg : ∀ β, (ft β).DegOK m) (κ : ℕ) (w0 : F → L → F) :
    prob (fun ω : (F × (Fin ℓ → F)) × (Fin κ → L) =>
        (ft ω.1.1).Accepts ℓ (w0 ω.1.1) (extR ω.1.2) ω.2) ≤
      (goodSet (m + ℓ) δ w0).ncard / Fintype.card F + epsFold F (m + ℓ + R) ℓ + (1 - δ) ^ κ := by
  classical
  haveI : Nonempty L := ⟨1⟩
  set G := goodSet (m + ℓ) δ w0
  have hLpos : (0 : ℚ) < Fintype.card L := by exact_mod_cast Fintype.card_pos
  have hR' : (0 : ℚ) < 1 / 2 ^ R := by positivity
  let B : F × (Fin ℓ → F) → Prop := fun p =>
    p.1 ∈ G ∨ NotGood (ft p.1) m ℓ (w0 p.1) δ (extR p.2)
  have hacc := accept_le (Ω' := F × (Fin ℓ → F)) κ (δ := δ) (by linarith)
    (fun p => Wset (ft p.1) ℓ (w0 p.1) (extR p.2) ℓ ((ft p.1).W ℓ (w0 p.1) (extR p.2) ℓ))
    (fun p ξ => (ft p.1).Accepts ℓ (w0 p.1) (extR p.2) ξ) B
    (fun p ξ h t => (queryOK_iff hℓ _ _).1 (h t)) (by
      rintro ⟨β, ρ⟩ hB
      simp only [B, not_or] at hB
      by_contra hlt
      push_neg at hlt
      apply hB.1
      haveI := hL.finite
      obtain ⟨-, hmem, hagree, -⟩ := chain_final hL hℓ hδ (hdeg β) (extR ρ) (fun j hj => by
        by_contra hb; exact hB.2 ⟨j, hj, hb⟩) (by
          rw [dens, Nat.card_eq_fintype_card, le_div_iff₀ hLpos]; exact hlt.le)
      refine ⟨_, hmem, _, fun ξ hξ => negPt_mem_Wset
        (lv_neg_one_mem hL (j := 0) (by omega)) _ ℓ _ ξ hξ, ?_, fun ξ hξ => (hagree ξ hξ).1⟩
      rw [Nat.card_eq_fintype_card]; exact hlt.le)
  refine hacc.trans ?_
  have hB1 : prob B ≤ prob (fun p : F × (Fin ℓ → F) => p.1 ∈ G) +
      prob (fun p : F × (Fin ℓ → F) => NotGood (ft p.1) m ℓ (w0 p.1) δ (extR p.2)) :=
    prob_or_le _ _
  have hB2 : prob (fun p : F × (Fin ℓ → F) => p.1 ∈ G) = G.ncard / Fintype.card F := by
    haveI : Nonempty (Fin ℓ → F) := ⟨fun _ => 0⟩
    rw [prob_fst (fun β : F => β ∈ G), prob_def, card_filter_eq_ncard]
    rfl
  have hB3 : prob (fun p : F × (Fin ℓ → F) => NotGood (ft p.1) m ℓ (w0 p.1) δ (extR p.2)) ≤
      epsFold F (m + ℓ + R) ℓ := by
    rw [prob_prod_eq_expect (fun β ρ => NotGood (ft β) m ℓ (w0 β) δ (extR ρ))]
    haveI : Nonempty F := ⟨0⟩
    exact expect_le_of_le _ _ (fun β => prob_notGood_le hL hδ0 hδ (hC β))
  linarith

end Generic

/-! ### The protocol `Π_Had` -/

section Protocol

/-- The nine words of the curve of degree 8:
`(w_a, w_c, w_Q, w_b*, w_A, h, q[w_a, y₁, γθ], q[w_Q, y₁, θ], q[w_c, y₃, γ])`. -/
noncomputable def curveHad (n : ℕ) (wa wb wc wQ wA : L → F) (y1 y3 γ θ : F) : Fin 9 → L → F :=
  ![wa, wc, wQ, wrev (2 ^ n) wb, wA, virtIP n wQ wb wA y3, qword wa y1 (γ * θ), qword wQ y1 θ,
    qword wc y3 γ]

/-- The batched word `w_0 = ∑_{i ≤ 8} β^i u_i`. -/
noncomputable def wbatHad (n : ℕ) (wa wb wc wQ wA : L → F) (y1 y3 γ θ β : F) : L → F :=
  ∑ i : Fin 9, β ^ (i : ℕ) • curveHad n wa wb wc wQ wA y1 y3 γ θ i

/-- A deterministic prover of `Π_Had`. -/
structure HadProver (F : Type*) [Field F] (L : Subgroup Fˣ) where
  /-- round 1: `w_Q` as a function of `γ` -/
  wQ : F → L → F
  /-- round 2: `y₁`, `y₃` and `w_A` as functions of `(γ, θ)` -/
  y1 : F → F → F
  y3 : F → F → F
  wA : F → F → L → F
  /-- the folding test, for each `(γ, θ, β)` -/
  ft : F → F → F → FTProver F L

namespace HadProver

variable (P : HadProver F L)

def Causal : Prop := ∀ γ θ β, (P.ft γ θ β).Causal
def DegOK (m : ℕ) : Prop := ∀ γ θ β, (P.ft γ θ β).DegOK m

/-- The batched word of the prover at `(γ, θ)`, as a function of `β`. -/
noncomputable def w0 (n : ℕ) (wa wb wc : L → F) (γ θ : F) : F → L → F := fun β =>
  wbatHad n wa wb wc (P.wQ γ) (P.wA γ θ) (P.y1 γ θ) (P.y3 γ θ) γ θ β

/-- The verifier of `Π_Had` accepts `(γ, θ, β, r, ξ)`. -/
def Accepts (ℓ : ℕ) {κ : ℕ} (n : ℕ) (wa wb wc : L → F) (γ θ β : F) (r : ℕ → F)
    (ξ : Fin κ → L) : Prop :=
  (P.ft γ θ β).Accepts ℓ (P.w0 n wa wb wc γ θ β) r ξ

/-- The acceptance probability over `(γ, θ) ∈ F²` and `(β, r, ξ) ∈ F × F^ℓ × L^κ`. -/
noncomputable def accProb [Fintype F] [Fintype L] (ℓ κ n : ℕ) (wa wb wc : L → F) : ℚ :=
  prob (fun ω : (F × F) × ((F × (Fin ℓ → F)) × (Fin κ → L)) =>
    P.Accepts ℓ n wa wb wc ω.1.1 ω.1.2 ω.2.1.1 (extR ω.2.1.2) ω.2.2)

end HadProver

/-- **The relation `R^δ_Had`.** -/
def RelHad {n : ℕ} (δ : ℚ) (wa wb wc : L → F) (a b c : Table F n) : Prop :=
  fibDist wa (encode L a) ≤ δ ∧ fibDist wb (encode L b) ≤ δ ∧ fibDist wc (encode L c) ≤ δ ∧
    ∀ w, a w * b w = c w

end Protocol

/-! ### Lemma batch8 (batching, degree 8) -/

section Batching

/-- **Lemma batch8.** If more than `8M` challenges `β` are good for `w_0`, there are tables
`a, b, c` and `Q̂ ∈ F[X]_{<N}` such that (1) `w_a, w_b, w_c, w_Q` are within fibre distance `δ`
of `Enc^T(a), Enc^T(b), Enc^T(c), ev(Q̂)`; (2) `V_a(γθ) = y₁ = Q̂(θ)`; (3) `V_c(γ) = y₃` and
`y₃ = [X^{N-1}] Q̂ V_b*`. -/
theorem batching_Had [Fintype F] [DecidableEq F] {n R : ℕ} (hL : IsSmoothDomain L (n + R))
    (hR : 2 ≤ R) {δ : ℚ} (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (wa wb wc wQ wA : L → F) (y1 y3 γ θ : F)
    (hG : 8 * Nat.card L <
      (goodSet n δ (fun β => wbatHad n wa wb wc wQ wA y1 y3 γ θ β)).ncard) :
    ∃ a b c : Table F n, ∃ Qh ∈ degreeLT F (2 ^ n),
      fibDist wa (encode L a) ≤ δ ∧ fibDist wb (encode L b) ≤ δ ∧
      fibDist wc (encode L c) ≤ δ ∧ fibDist wQ (ev L Qh) ≤ δ ∧
      (kronEnc a).eval (γ * θ) = y1 ∧ Qh.eval θ = y1 ∧
      (kronEnc c).eval γ = y3 ∧ y3 = (Qh * revP (2 ^ n) (kronEnc b)).coeff (2 ^ n - 1) := by
  classical
  haveI := hL.finite
  have hcardL : Nat.card L = 2 ^ (n + R) := hL
  have hNM : 2 ^ n ≤ Nat.card L := by
    rw [hcardL]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hneg : (-1 : Fˣ) ∈ L := hL.neg_one_mem (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_smooth hL (by omega)
  set u := curveHad n wa wb wc wQ wA y1 y3 γ θ
  obtain ⟨c, hc, T, hTneg, hTcard, hTu⟩ := curve_agreement hL hδ0 hδ (t := 8) (by norm_num) u hG
  have hpoly : ∀ i, polyOf (c i) ∈ degreeLT F (2 ^ n) := fun i => (polyOf_spec hNM (hc i)).1
  have e : ∀ (i : Fin 9) (ξ : L), c i ξ = (polyOf (c i)).eval (xv' ξ) := by
    intro i ξ
    have := congrFun (polyOf_spec hNM (hc i)).2 ξ
    simp only [ev] at this
    exact this.symm
  have hv : ∀ (i : Fin 9), ∀ ξ ∈ T, u i ξ = (polyOf (c i)).eval (xv' ξ) := fun i ξ hξ => by
    rw [hTu i ξ hξ, e]
  have hTbig : 2 * 2 ^ n < T.ncard := by
    have hrc := rate_condition (n := n) hR hδ
    have : (2 * 2 ^ n : ℚ) < T.ncard := by
      calc (2 * 2 ^ n : ℚ) = 2 * (2 : ℚ) ^ n := by simp
        _ < (1 - δ) * 2 ^ (n + R) := hrc
        _ = (1 - δ) * Nat.card L := by rw [hcardL]; push_cast; ring
        _ ≤ T.ncard := hTcard
    exact_mod_cast this
  have hTN : 2 ^ n + 1 < T.ncard := by
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  set P0 := polyOf (c 0)
  set P1 := polyOf (c 1)
  set P2 := polyOf (c 2)
  set P3 := polyOf (c 3)
  set P4 := polyOf (c 4)
  set P5 := polyOf (c 5)
  -- the inner-product identity
  have hval : y3 = (P2 * P3).coeff (2 ^ n - 1) := by
    letI : Fintype T := Fintype.ofFinite T
    refine identityG Nat.one_le_two_pow (hpoly 4) (eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (PhiG (2 ^ n) P2 P3 P4 P5 y3) (f := fun i : T => xv' (i : L)) ?_ ?_ ?_)
    · intro x y hxy
      exact Subtype.ext (Subtype.ext (Units.ext hxy))
    · intro i
      have hid := virtIP_identity (n := n) wQ wb wA y3 (i : L)
      have h2' := hv 2 i i.2
      have h3 := hv 3 i i.2
      have h4 := hv 4 i i.2
      have h5 := hv 5 i i.2
      change wQ (i : L) = P2.eval _ at h2'
      change wrev (2 ^ n) wb (i : L) = P3.eval _ at h3
      change wA (i : L) = P4.eval _ at h4
      change virtIP n wQ wb wA y3 (i : L) = P5.eval _ at h5
      simp only [PhiG, assemble, eval_sub, eval_add, eval_mul, eval_X, eval_C, eval_pow]
      rw [← h2', ← h3, ← h4, ← h5, hid]; ring
    · rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]
      exact lt_of_le_of_lt (natDegree_PhiG_le (hpoly 2) (hpoly 3) (hpoly 4) (hpoly 5) y3) hTbig
  -- the three DEEP steps
  have d0 : P0.eval (γ * θ) = y1 :=
    deep_step (hpoly 0) (hpoly 6) T hTN (fun ξ hξ => hv 0 ξ hξ) (fun ξ hξ => hv 6 ξ hξ)
  have d2 : P2.eval θ = y1 :=
    deep_step (hpoly 2) (hpoly 7) T hTN (fun ξ hξ => hv 2 ξ hξ) (fun ξ hξ => hv 7 ξ hξ)
  have d1 : P1.eval γ = y3 :=
    deep_step (hpoly 1) (hpoly 8) T hTN (fun ξ hξ => hv 1 ξ hξ) (fun ξ hξ => hv 8 ξ hξ)
  -- the witness
  set a : Table F n := kronCoeffs n P0
  set cc : Table F n := kronCoeffs n P1
  set b : Table F n := kronCoeffs n (revP (2 ^ n) P3)
  have hVa : kronEnc a = P0 := kronEnc_kronCoeffs (hpoly 0)
  have hVc : kronEnc cc = P1 := kronEnc_kronCoeffs (hpoly 1)
  have hVb : kronEnc b = revP (2 ^ n) P3 := kronEnc_kronCoeffs (revP_mem _ _)
  have hev : ∀ i, ev L (polyOf (c i)) = c i := fun i => (polyOf_spec hNM (hc i)).2
  refine ⟨a, b, cc, P2, hpoly 2, ?_, ?_, ?_, ?_, by rw [hVa]; exact d0, d2,
    by rw [hVc]; exact d1, by rw [hVb, revP_revP (hpoly 3)]; exact hval⟩
  · refine fibDist_le_of_closed hneg h2 T hTneg hTcard (fun ξ hξ => ?_)
    rw [encode, hVa, hev 0]; exact hTu 0 ξ hξ
  · refine fibDist_le_of_closed hneg h2 (invPt '' T) (inv_image_closed hneg hTneg)
      (by rw [ncard_inv_image]; exact hTcard) ?_
    rintro _ ⟨ξ, hξ, rfl⟩
    have h1 : wrev (2 ^ n) wb ξ = wrev (2 ^ n) (encode L b) ξ := by
      rw [encode, hVb, wrev_ev (revP_mem _ _), revP_revP (hpoly 3), hev 3]
      exact hTu 3 ξ hξ
    exact (wrev_eq_iff _ _ _ ξ).1 h1
  · refine fibDist_le_of_closed hneg h2 T hTneg hTcard (fun ξ hξ => ?_)
    rw [encode, hVc, hev 1]; exact hTu 1 ξ hξ
  · refine fibDist_le_of_closed hneg h2 T hTneg hTcard (fun ξ hξ => ?_)
    rw [hev 2]; exact hTu 2 ξ hξ

end Batching

/-! ### Soundness -/

section Sound

/-- A nonzero polynomial of `F[X]_{<N}` has at most `N - 1` roots. -/
lemma ncard_roots_le [Fintype F] [DecidableEq F] {N : ℕ} {Q : F[X]} (hQ : Q ∈ degreeLT F N)
    (hne : Q ≠ 0) : {θ : F | Q.eval θ = 0}.ncard ≤ N - 1 := by
  have hsub : {θ : F | Q.eval θ = 0} ⊆ (Q.roots.toFinset : Set F) := by
    intro θ hθ
    simp only [Set.mem_setOf_eq] at hθ
    simp [Multiset.mem_toFinset, mem_roots hne, IsRoot, hθ]
  calc _ ≤ (Q.roots.toFinset : Set F).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Q.roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ Q.roots.card := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := card_roots' _
    _ ≤ N - 1 := natDegree_le_of_mem_degreeLT hQ

omit [Field F] in
lemma prob_set_le [Fintype F] (S : Set F) {k : ℕ} (hS : S.ncard ≤ k) :
    prob (fun γ : F => γ ∈ S) ≤ (k : ℚ) / Fintype.card F := by
  classical
  rw [prob_def, card_filter_eq_ncard]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hS

/-- The pairs `(γ, θ)` for which more than `8M` challenges `β` are good have probability at most
`2(N-1)/|F|` when the instance has no witness (proof of Theorem had). -/
theorem prob_bad_le [Fintype F] [DecidableEq F] {m ℓ R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hR : 2 ≤ R) {δ : ℚ} (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : HadProver F L)
    (wa wb wc : L → F) (hnw : ∀ a b c : Table F (m + ℓ), ¬ RelHad δ wa wb wc a b c) :
    prob (fun p : F × F => 8 * Nat.card L <
        (goodSet (m + ℓ) δ (P.w0 (m + ℓ) wa wb wc p.1 p.2)).ncard) ≤
      2 * ((2 ^ (m + ℓ) - 1 : ℕ) : ℚ) / Fintype.card F := by
  classical
  haveI := hL.finite
  set n := m + ℓ
  have hcardL : Nat.card L = 2 ^ (n + R) := hL
  have hNM : 2 ^ n ≤ Nat.card L := by
    rw [hcardL]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrate : rate L (2 ^ n) = 1 / 2 ^ R := by
    rw [rate, hcardL]; push_cast
    rw [pow_add (2 : ℚ) n R]
    have : (2 : ℚ) ^ n ≠ 0 := by positivity
    field_simp
  have hδ' : δ ≤ (1 - rate L (2 ^ n)) / 2 := by rw [hrate]; exact hδ
  have hneg : (-1 : Fˣ) ∈ L := hL.neg_one_mem (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_smooth hL (by omega)
  have hF : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  set Bad : F × F → Prop := fun p =>
    8 * Nat.card L < (goodSet n δ (P.w0 n wa wb wc p.1 p.2)).ncard
  have hbatch : ∀ p, Bad p → _ := fun p hp =>
    batching_Had (n := n) (R := R) hL hR hδ0 hδ wa wb wc (P.wQ p.1) (P.wA p.1 p.2) (P.y1 p.1 p.2)
      (P.y3 p.1 p.2) p.1 p.2 hp
  by_cases hex : ∃ a b c : Table F n, fibDist wa (encode L a) ≤ δ ∧
      fibDist wb (encode L b) ≤ δ ∧ fibDist wc (encode L c) ≤ δ
  swap
  · -- no decoding: no pair is bad
    refine (prob_mono (F := fun _ => False) (fun p hp => ?_)).trans ?_
    · obtain ⟨a, b, c, -, -, h1, h2', h3, -⟩ := hbatch p hp
      exact hex ⟨a, b, c, h1, h2', h3⟩
    · rw [prob_false]; positivity
  obtain ⟨ah, bh, ch, ha, hb, hc⟩ := hex
  have hne : ¬ ∀ w, ah w * bh w = ch w := fun h => hnw ah bh ch ⟨ha, hb, hc, h⟩
  set D : F[X] := kronEnc (fun w => ah w * bh w - ch w)
  have hD : D ≠ 0 := by
    intro h0
    apply hne
    intro w
    have := congrFun (kronCoeffs_kronEnc (fun w => ah w * bh w - ch w)) w
    rw [show kronEnc (fun w => ah w * bh w - ch w) = D from rfl, h0] at this
    simp [kronCoeffs] at this
    exact sub_eq_zero.1 this.symm
  set Z1 : Set F := {γ | D.eval γ = 0}
  have hZ1 : Z1.ncard ≤ 2 ^ n - 1 := ncard_roots_le (kronEnc_mem_degreeLT _) hD
  set Z2 : F → Set F := fun γ => {θ | ∃ Qh ∈ degreeLT F (2 ^ n), fibDist (P.wQ γ) (ev L Qh) ≤ δ ∧
    Qh ≠ kronEnc (gscale γ ah) ∧ Qh.eval θ = (kronEnc ah).eval (γ * θ)}
  have hZ2 : ∀ γ, (Z2 γ).ncard ≤ 2 ^ n - 1 := by
    intro γ
    by_cases hZ : (Z2 γ).Nonempty
    · obtain ⟨θ0, Q0, hQ0, hd0, hn0, -⟩ := hZ
      have hsub : Z2 γ ⊆ {θ | (Q0 - kronEnc (gscale γ ah)).eval θ = 0} := by
        rintro θ ⟨Q1, hQ1, hd1, -, he1⟩
        have hQeq : Q1 = Q0 := by
          have := fib_unique hneg h2 hδ' (P.wQ γ) (ev_mem_RS hQ1) (ev_mem_RS hQ0) hd1 hd0
          exact ev_injOn hNM hQ1 hQ0 this
        simp only [Set.mem_setOf_eq, eval_sub, eval_gscale]
        rw [← hQeq, he1, sub_self]
      refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (ncard_roots_le ?_ (sub_ne_zero.2 hn0))
      exact Submodule.sub_mem _ hQ0 (kronEnc_mem_degreeLT _)
    · rw [Set.not_nonempty_iff_eq_empty.1 hZ, Set.ncard_empty]; exact Nat.zero_le _
  -- a bad pair has `γ ∈ Z₁` or `θ ∈ Z₂(γ)`
  have hBad : ∀ p, Bad p → p.1 ∈ Z1 ∨ p.2 ∈ Z2 p.1 := by
    intro p hp
    obtain ⟨a, b, c, Qh, hQh, hda, hdb, hdc, hdQ, e1, e2, e3, e4⟩ := hbatch p hp
    have ha' := encode_fib_unique hNM hneg h2 hδ' wa hda ha
    have hb' := encode_fib_unique hNM hneg h2 hδ' wb hdb hb
    have hc' := encode_fib_unique hNM hneg h2 hδ' wc hdc hc
    subst ha' hb' hc'
    by_cases hQ : Qh = kronEnc (gscale p.1 a)
    · left
      show D.eval p.1 = 0
      have hw := weighted_inner_product p.1 a b
      rw [← hQ, ← e4] at hw
      have hcv : (kronEnc c).eval p.1 = ∑ w, p.1 ^ bitsToNat w * c w := by
        rw [eval_kronEnc]; exact sum_congr rfl (fun w _ => by ring)
      rw [e3] at hcv
      simp only [D, eval_kronEnc, sub_mul, sum_sub_distrib]
      rw [sub_eq_zero]
      calc (∑ x, a x * b x * p.1 ^ bitsToNat x) = ∑ w, p.1 ^ bitsToNat w * (a w * b w) :=
            sum_congr rfl (fun w _ => by ring)
        _ = ∑ w, p.1 ^ bitsToNat w * c w := by rw [hw, hcv]
        _ = ∑ x, c x * p.1 ^ bitsToNat x := sum_congr rfl (fun w _ => by ring)
    · right
      exact ⟨Qh, hQh, hdQ, hQ, by rw [e2, e1]⟩
  calc prob Bad ≤ prob (fun p : F × F => p.1 ∈ Z1 ∨ p.2 ∈ Z2 p.1) := prob_mono hBad
    _ ≤ prob (fun p : F × F => p.1 ∈ Z1) + prob (fun p : F × F => p.2 ∈ Z2 p.1) := prob_or_le _ _
    _ ≤ ((2 ^ n - 1 : ℕ) : ℚ) / Fintype.card F + ((2 ^ n - 1 : ℕ) : ℚ) / Fintype.card F := by
        gcongr
        · rw [prob_fst (fun γ : F => γ ∈ Z1)]
          exact prob_set_le Z1 hZ1
        · rw [prob_prod_eq_expect (fun γ θ => θ ∈ Z2 γ)]
          exact expect_le_of_le _ _ (fun γ => prob_set_le (Z2 γ) (hZ2 γ))
    _ = _ := by ring

/-- **Theorem had (soundness of `Π_Had`).** If `(w_a, w_b, w_c)` has no witness in `R^δ_Had`, every
causal prover whose final polynomials lie in `F[X]_{<N_ℓ}` is accepted with probability at most
`2(N-1)/|F| + 8M/|F| + ε_fold + (1-δ)^κ`. -/
theorem soundness_Had [Fintype F] [DecidableEq F] [Fintype L] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : HadProver F L) (hC : P.Causal) (hdeg : P.DegOK m)
    (κ : ℕ) (wa wb wc : L → F) (hnw : ∀ a b c : Table F (m + ℓ), ¬ RelHad δ wa wb wc a b c) :
    P.accProb ℓ κ (m + ℓ) wa wb wc ≤
      2 * ((2 ^ (m + ℓ) - 1 : ℕ) : ℚ) / Fintype.card F + 8 * 2 ^ (m + ℓ + R) / Fintype.card F +
        epsFold F (m + ℓ + R) ℓ + (1 - δ) ^ κ := by
  classical
  haveI : Nonempty F := ⟨0⟩
  set n := m + ℓ
  set Bad : F × F → Prop := fun p =>
    8 * Nat.card L < (goodSet n δ (P.w0 n wa wb wc p.1 p.2)).ncard
  set K : ℚ := 8 * 2 ^ (m + ℓ + R) / Fintype.card F + epsFold F (m + ℓ + R) ℓ + (1 - δ) ^ κ
  have hF : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hML : (Nat.card L : ℚ) = 2 ^ (m + ℓ + R) := by exact_mod_cast (hL : Nat.card L = _)
  have hpt : ∀ p : F × F, prob (fun ω : (F × (Fin ℓ → F)) × (Fin κ → L) =>
      P.Accepts ℓ n wa wb wc p.1 p.2 ω.1.1 (extR ω.1.2) ω.2) ≤ (if Bad p then 1 else 0) + K := by
    intro p
    have h := ft_family_bound hL hℓ hδ0 hδ (P.ft p.1 p.2) (fun β => hC p.1 p.2 β)
      (fun β => hdeg p.1 p.2 β) κ (P.w0 n wa wb wc p.1 p.2)
    refine h.trans ?_
    have hG1 : ((goodSet n δ (P.w0 n wa wb wc p.1 p.2)).ncard : ℚ) ≤ Fintype.card F := by
      have := Set.ncard_le_ncard (Set.subset_univ (goodSet n δ (P.w0 n wa wb wc p.1 p.2)))
        (Set.toFinite _)
      rw [Set.ncard_univ, Nat.card_eq_fintype_card] at this
      exact_mod_cast this
    simp only [K]
    split_ifs with hB
    · have : ((goodSet n δ (P.w0 n wa wb wc p.1 p.2)).ncard : ℚ) / Fintype.card F ≤ 1 := by
        rw [div_le_one hF]; exact hG1
      have : (0 : ℚ) ≤ 8 * 2 ^ (m + ℓ + R) / Fintype.card F := by positivity
      linarith
    · have hle : ((goodSet n δ (P.w0 n wa wb wc p.1 p.2)).ncard : ℚ) ≤ 8 * 2 ^ (m + ℓ + R) := by
        rw [← hML]; exact_mod_cast not_lt.1 hB
      have : ((goodSet n δ (P.w0 n wa wb wc p.1 p.2)).ncard : ℚ) / Fintype.card F ≤
          8 * 2 ^ (m + ℓ + R) / Fintype.card F := div_le_div_of_nonneg_right hle hF.le
      linarith
  have hbad := prob_bad_le hL hR hδ0 hδ P wa wb wc hnw
  unfold HadProver.accProb
  rw [prob_prod_eq_expect (fun (p : F × F) (ω : (F × (Fin ℓ → F)) × (Fin κ → L)) =>
    P.Accepts ℓ n wa wb wc p.1 p.2 ω.1.1 (extR ω.1.2) ω.2)]
  have hF2 : (0 : ℚ) < Fintype.card (F × F) := by exact_mod_cast Fintype.card_pos
  calc expect (fun p : F × F => prob (fun ω : (F × (Fin ℓ → F)) × (Fin κ → L) =>
        P.Accepts ℓ n wa wb wc p.1 p.2 ω.1.1 (extR ω.1.2) ω.2))
      ≤ expect (fun p : F × F => (if Bad p then (1 : ℚ) else 0) + K) := by
        unfold expect
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact sum_le_sum (fun p _ => hpt p)
    _ = prob Bad + K := by
        unfold expect
        rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, add_div,
          mul_div_cancel_left₀ _ hF2.ne', sum_boole, prob_def]
    _ ≤ _ := by
        simp only [K] at *
        linarith

end Sound

/-! ### Completeness -/

section Complete

variable {n : ℕ}

/-- `(P - P(x)) / (X - x)`. -/
noncomputable def divq (P : F[X]) (x : F) : F[X] := (P - C (P.eval x)) /ₘ (X - C x)

lemma divq_mem {N : ℕ} {P : F[X]} (hP : P ∈ degreeLT F N) (x : F) : divq P x ∈ degreeLT F N := by
  rw [divq, mem_degreeLT]
  have hdeg : (P - C (P.eval x)) ∈ degreeLT F N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · have : P = 0 := by
        rw [h0, mem_degreeLT] at hP; exact degree_eq_bot.1 (by simpa using hP)
      simp [this]
    · refine Submodule.sub_mem _ hP ?_
      rw [mem_degreeLT]; exact (degree_C_le).trans_lt (by exact_mod_cast h0)
  rw [mem_degreeLT] at hdeg
  exact (degree_divByMonic_le _ _).trans_lt hdeg

/-- The nine honest polynomials, in the order of `curveHad`. -/
noncomputable def hadPolys (a b c : Table F n) (γ θ : F) : Fin 9 → F[X] :=
  ![kronEnc a, kronEnc c, kronEnc (gscale γ a), revP (2 ^ n) (kronEnc b), ipA (gscale γ a) b,
    ipH (gscale γ a) b, divq (kronEnc a) (γ * θ), divq (kronEnc (gscale γ a)) θ,
    divq (kronEnc c) γ]

/-- The honest batched polynomial `U_0 = ∑_{i ≤ 8} β^i P_i`. -/
noncomputable def hadU0 (a b c : Table F n) (γ θ β : F) : F[X] :=
  ∑ i : Fin 9, C (β ^ (i : ℕ)) * hadPolys a b c γ θ i

lemma hadPolys_mem (a b c : Table F n) (γ θ : F) (i : Fin 9) :
    hadPolys a b c γ θ i ∈ degreeLT F (2 ^ n) := by
  have hd : ∀ (P : F[X]) (x : F), P ∈ degreeLT F (2 ^ n) → divq P x ∈ degreeLT F (2 ^ n) :=
    fun P x hP => divq_mem hP x
  fin_cases i
  · exact kronEnc_mem_degreeLT a
  · exact kronEnc_mem_degreeLT c
  · exact kronEnc_mem_degreeLT _
  · exact revP_mem _ _
  · exact openAG_mem _ _ _
  · exact openHG_mem _ _ _
  · exact hd _ _ (kronEnc_mem_degreeLT a)
  · exact hd _ _ (kronEnc_mem_degreeLT _)
  · exact hd _ _ (kronEnc_mem_degreeLT c)

lemma hadU0_mem (a b c : Table F n) (γ θ β : F) : hadU0 a b c γ θ β ∈ degreeLT F (2 ^ n) :=
  Submodule.sum_mem _ (fun i _ => by
    rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (hadPolys_mem a b c γ θ i))

/-- The honest prover of `Π_Had`. -/
noncomputable def honestHad (a b c : Table F n) (ℓ : ℕ) : HadProver F L where
  wQ γ := encode L (gscale γ a)
  y1 γ θ := (kronEnc a).eval (γ * θ)
  y3 γ _ := (kronEnc c).eval γ
  wA γ _ := ev L (ipA (gscale γ a) b)
  ft γ θ β := honestFT (hadU0 a b c γ θ β) ℓ

/-- With `a ∘ b = c`, `V_c(γ) = ∑_w γ^w a(w) b(w)`. -/
lemma eval_c_eq (a b c : Table F n) (hab : ∀ w, a w * b w = c w) (γ : F) :
    (kronEnc c).eval γ = ∑ w, gscale γ a w * b w := by
  rw [eval_kronEnc]
  exact sum_congr rfl (fun w _ => by rw [← hab w, gscale]; ring)

/-- The honest curve words are the codewords of `hadPolys`, when no pole lies in `L`. -/
theorem curveHad_honest (a b c : Table F n) (hab : ∀ w, a w * b w = c w) (γ θ : F)
    (hpoles : ∀ ξ : L, xv' ξ ≠ γ * θ ∧ xv' ξ ≠ θ ∧ xv' ξ ≠ γ) (i : Fin 9) :
    curveHad n (encode L a) (encode L b) (encode L c) (encode L (gscale γ a))
      (ev L (ipA (gscale γ a) b)) ((kronEnc a).eval (γ * θ)) ((kronEnc c).eval γ) γ θ i =
      ev L (hadPolys a b c γ θ i) := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact wrev_ev (kronEnc_mem_degreeLT b)
  · rfl
  · show virtIP n (encode L (gscale γ a)) (encode L b) (ev L (ipA (gscale γ a) b))
      ((kronEnc c).eval γ) = ev L (ipH (gscale γ a) b)
    rw [eval_c_eq a b c hab γ]
    exact virtIP_honest _ _
  · exact (deep_honest (kronEnc_mem_degreeLT a) _ (fun ξ => (hpoles ξ).1)).1
  · show qword (encode L (gscale γ a)) ((kronEnc a).eval (γ * θ)) θ =
      ev L (divq (kronEnc (gscale γ a)) θ)
    rw [← eval_gscale]
    exact (deep_honest (kronEnc_mem_degreeLT _) _ (fun ξ => (hpoles ξ).2.1)).1
  · exact (deep_honest (kronEnc_mem_degreeLT c) _ (fun ξ => (hpoles ξ).2.2)).1

/-- The honest batched word is `ev_L(U_0)`. -/
theorem wbatHad_honest (a b c : Table F n) (hab : ∀ w, a w * b w = c w) (γ θ β : F)
    (hpoles : ∀ ξ : L, xv' ξ ≠ γ * θ ∧ xv' ξ ≠ θ ∧ xv' ξ ≠ γ) :
    (honestHad (L := L) a b c 0).w0 n (encode L a) (encode L b) (encode L c) γ θ β =
      ev L (hadU0 a b c γ θ β) := by
  show wbatHad n (encode L a) (encode L b) (encode L c) (encode L (gscale γ a))
      (ev L (ipA (gscale γ a) b)) ((kronEnc a).eval (γ * θ)) ((kronEnc c).eval γ) γ θ β = _
  unfold wbatHad
  simp_rw [curveHad_honest a b c hab γ θ hpoles]
  funext ξ
  simp [hadU0, ev, eval_finset_sum, Finset.sum_apply]

/-- **Theorem (completeness):** if `w_f = Enc^T(f)` for `f ∈ {a, b, c}` and `a ∘ b = c`, the
honest prover is accepted whenever the poles `γθ, θ, γ` lie outside `L`. -/
theorem honestHad_accepts {m ℓ R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (a b c : Table F (m + ℓ)) (hab : ∀ w, a w * b w = c w) (γ θ β : F)
    (hpoles : ∀ ξ : L, xv' ξ ≠ γ * θ ∧ xv' ξ ≠ θ ∧ xv' ξ ≠ γ) (r : ℕ → F) {κ : ℕ}
    (ξ : Fin κ → L) :
    (honestHad (L := L) a b c ℓ).Accepts ℓ (m + ℓ) (encode L a) (encode L b) (encode L c)
      γ θ β r ξ := by
  unfold HadProver.Accepts
  have e : (honestHad (L := L) a b c ℓ).w0 (m + ℓ) (encode L a) (encode L b) (encode L c) γ θ β =
      ev L (hadU0 a b c γ θ β) := wbatHad_honest a b c hab γ θ β hpoles
  rw [e]
  exact honestFT_accepts hL _ r ξ

theorem honestHad_causal {n ℓ : ℕ} (a b c : Table F n) : (honestHad (L := L) a b c ℓ).Causal := by
  intro γ θ β j r r' h
  simp only [honestHad, honestFT]
  rw [pfoldUp_congr _ j h]

theorem honestHad_DegOK {m ℓ : ℕ} (a b c : Table F (m + ℓ)) :
    (honestHad (L := L) a b c ℓ).DegOK m := fun γ θ β => honestFT_DegOK (hadU0_mem a b c γ θ β)

omit [Field F] in
lemma prob_add_prob_not {Ω : Type*} [Fintype Ω] (E : Ω → Prop) :
    prob E + prob (fun ω => ¬ E ω) = 1 ∨ Fintype.card Ω = 0 := by
  classical
  by_cases h : Fintype.card Ω = 0
  · exact Or.inr h
  left
  have hc : (0 : ℚ) < Fintype.card Ω := by exact_mod_cast Nat.pos_of_ne_zero h
  rw [prob_def, prob_def, ← add_div, div_eq_one_iff_eq hc.ne']
  exact_mod_cast filter_card_add_filter_neg_card_eq_card E

/-- **Completeness, probability:** the honest prover is accepted with probability at least
`1 - 3M/|F|`. -/
theorem honestHad_prob [Fintype F] [DecidableEq F] [Fintype L] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (a b c : Table F (m + ℓ)) (hab : ∀ w, a w * b w = c w)
    (κ : ℕ) :
    1 - 3 * (Nat.card L : ℚ) / Fintype.card F ≤
      (honestHad (L := L) a b c ℓ).accProb ℓ κ (m + ℓ) (encode L a) (encode L b) (encode L c) := by
  classical
  haveI : Nonempty L := ⟨1⟩
  haveI : Nonempty F := ⟨0⟩
  set S : Set F := Set.range (fun ξ : L => xv' ξ)
  have hS : S.ncard ≤ Nat.card L := by
    have e : S = (fun ξ : L => xv' ξ) '' Set.univ := Set.image_univ.symm
    rw [e]
    exact (Set.ncard_image_le (Set.toFinite _)).trans (by rw [Set.ncard_univ])
  have h0S : (0 : F) ∉ S := by
    rintro ⟨ξ, hξ⟩; exact xv'_ne_zero ξ hξ
  set Valid : F × F → Prop := fun p => ∀ ξ : L, xv' ξ ≠ p.1 * p.2 ∧ xv' ξ ≠ p.2 ∧ xv' ξ ≠ p.1
  have hacc : prob (fun ω : (F × F) × ((F × (Fin ℓ → F)) × (Fin κ → L)) => Valid ω.1) ≤
      (honestHad (L := L) a b c ℓ).accProb ℓ κ (m + ℓ) (encode L a) (encode L b) (encode L c) :=
    prob_mono (fun ω hω => honestHad_accepts hL a b c hab _ _ _ hω _ _)
  haveI : Nonempty ((F × (Fin ℓ → F)) × (Fin κ → L)) := ⟨⟨⟨0, fun _ => 0⟩, fun _ => 1⟩⟩
  rw [prob_fst Valid] at hacc
  have hnot : prob (fun p : F × F => ¬ Valid p) ≤ 3 * (Nat.card L : ℚ) / Fintype.card F := by
    have hsub : ∀ p : F × F, ¬ Valid p → (p.1 * p.2 ∈ S ∨ p.2 ∈ S) ∨ p.1 ∈ S := by
      intro p hp
      simp only [Valid, not_forall, not_and_or, not_not] at hp
      obtain ⟨ξ, h | h | h⟩ := hp
      · exact Or.inl (Or.inl ⟨ξ, h⟩)
      · exact Or.inl (Or.inr ⟨ξ, h⟩)
      · exact Or.inr ⟨ξ, h⟩
    have h1 : prob (fun p : F × F => p.1 * p.2 ∈ S) ≤ (Nat.card L : ℚ) / Fintype.card F := by
      rw [prob_prod_eq_expect (fun γ θ => γ * θ ∈ S)]
      refine expect_le_of_le _ _ (fun γ => prob_set_le {θ | γ * θ ∈ S} ?_)
      by_cases hγ : γ = 0
      · have : {θ : F | γ * θ ∈ S} = ∅ := by
          ext θ; simp only [hγ, zero_mul, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          exact h0S
        rw [this, Set.ncard_empty]; exact Nat.zero_le _
      · have hsub' : {θ : F | γ * θ ∈ S} ⊆ (fun s => γ⁻¹ * s) '' S := by
          intro θ hθ
          exact ⟨γ * θ, hθ, by field_simp⟩
        exact (Set.ncard_le_ncard hsub' (Set.toFinite _)).trans
          ((Set.ncard_image_le (Set.toFinite _)).trans hS)
    have h2 : prob (fun p : F × F => p.2 ∈ S) ≤ (Nat.card L : ℚ) / Fintype.card F := by
      rw [prob_prod_eq_expect (fun (_ : F) θ => θ ∈ S)]
      exact expect_le_of_le _ _ (fun γ => prob_set_le S hS)
    have h3 : prob (fun p : F × F => p.1 ∈ S) ≤ (Nat.card L : ℚ) / Fintype.card F := by
      rw [prob_fst (fun γ : F => γ ∈ S)]; exact prob_set_le S hS
    calc prob (fun p : F × F => ¬ Valid p)
        ≤ prob (fun p : F × F => (p.1 * p.2 ∈ S ∨ p.2 ∈ S) ∨ p.1 ∈ S) := prob_mono hsub
      _ ≤ prob (fun p : F × F => p.1 * p.2 ∈ S ∨ p.2 ∈ S) + prob (fun p : F × F => p.1 ∈ S) :=
          prob_or_le _ _
      _ ≤ (prob (fun p : F × F => p.1 * p.2 ∈ S) + prob (fun p : F × F => p.2 ∈ S)) +
            prob (fun p : F × F => p.1 ∈ S) := by gcongr; exact prob_or_le _ _
      _ ≤ _ := by
          have : 3 * (Nat.card L : ℚ) / Fintype.card F = (Nat.card L : ℚ) / Fintype.card F +
              (Nat.card L : ℚ) / Fintype.card F + (Nat.card L : ℚ) / Fintype.card F := by ring
          linarith
  rcases prob_add_prob_not Valid with h | h
  · linarith
  · exact absurd h (Fintype.card_ne_zero)

end Complete

/-- **Knowledge:** if the verifier accepts with probability greater than
`2(N-1)/|F| + 8M/|F| + ε_fold + (1-δ)^κ`, then `(w_a, w_b, w_c)` has a witness. -/
theorem knowledge_Had [Fintype F] [DecidableEq F] [Fintype L] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : HadProver F L) (hC : P.Causal) (hdeg : P.DegOK m)
    (κ : ℕ) (wa wb wc : L → F)
    (hacc : 2 * ((2 ^ (m + ℓ) - 1 : ℕ) : ℚ) / Fintype.card F + 8 * 2 ^ (m + ℓ + R) / Fintype.card F +
        epsFold F (m + ℓ + R) ℓ + (1 - δ) ^ κ < P.accProb ℓ κ (m + ℓ) wa wb wc) :
    ∃ a b c : Table F (m + ℓ), RelHad δ wa wb wc a b c := by
  by_contra h
  push_neg at h
  have := soundness_Had hL hR hℓ hδ0 hδ P hC hdeg κ wa wb wc h
  linarith

/-- `Π^C_Had`: the folding test with the set `C` of committed levels (arity `2^k`). -/
def HadProver.AcceptsC (P : HadProver F L) (C : Set ℕ) (ℓ : ℕ) {κ : ℕ} (n : ℕ) (wa wb wc : L → F)
    (γ θ β : F) (r : ℕ → F) (ξ : Fin κ → L) : Prop :=
  (P.ft γ θ β).AcceptsC C ℓ (P.w0 n wa wb wc γ θ β) r ξ

noncomputable def HadProver.accProbC [Fintype F] [Fintype L] (P : HadProver F L) (C : Set ℕ)
    (ℓ κ n : ℕ) (wa wb wc : L → F) : ℚ :=
  prob (fun ω : (F × F) × ((F × (Fin ℓ → F)) × (Fin κ → L)) =>
    P.AcceptsC C ℓ n wa wb wc ω.1.1 ω.1.2 ω.2.1.1 (extR ω.2.1.2) ω.2.2)

/-- The induced prover (Proposition 5.28(1) for every `(γ, θ, β)`). -/
noncomputable def HadProver.inducedC (P : HadProver F L) (C : Set ℕ) (n : ℕ) (wa wb wc : L → F) :
    HadProver F L :=
  { P with ft := fun γ θ β => (P.ft γ θ β).induced C (P.w0 n wa wb wc γ θ β) }

/-- **Soundness of `Π^C_Had`** for every set `C` of committed levels. -/
theorem soundnessC_Had [Fintype F] [DecidableEq F] [Fintype L] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : HadProver F L) (hC : P.Causal) (hdeg : P.DegOK m)
    (C : Set ℕ) (κ : ℕ) (wa wb wc : L → F)
    (hnw : ∀ a b c : Table F (m + ℓ), ¬ RelHad δ wa wb wc a b c) :
    P.accProbC C ℓ κ (m + ℓ) wa wb wc ≤
      2 * ((2 ^ (m + ℓ) - 1 : ℕ) : ℚ) / Fintype.card F + 8 * 2 ^ (m + ℓ + R) / Fintype.card F +
        epsFold F (m + ℓ + R) ℓ + (1 - δ) ^ κ := by
  have e : P.accProbC C ℓ κ (m + ℓ) wa wb wc =
      (P.inducedC C (m + ℓ) wa wb wc).accProb ℓ κ (m + ℓ) wa wb wc := by
    unfold HadProver.accProbC HadProver.accProb
    congr 1
    funext ω
    exact propext (acceptsC_iff (P.ft ω.1.1 ω.1.2 ω.2.1.1) C ℓ _ _ _)
  rw [e]
  exact soundness_Had hL hR hℓ hδ0 hδ (P.inducedC C (m + ℓ) wa wb wc)
    (fun γ θ β => induced_causal _ C _ (hC γ θ β))
    (fun γ θ β => induced_DegOK _ C _ (hdeg γ θ β)) κ wa wb wc hnw

end KroneckerFRI
