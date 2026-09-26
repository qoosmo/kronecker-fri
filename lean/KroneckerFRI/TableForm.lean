/-
KroneckerFRI/TableForm.lean
§1 of the research note "Sumcheck-free hypercube inner products": the table-form encoding, the
evaluation kernel `E*_z` (Lemma eval), the reversal and the inner-product identity (Lemma ip),
the general split and identity lemmas (Lemma gen-identity), and reversed words (Lemma rev).

Conventions.
* A table `f : Table F n` is encoded by `V_f = ∑_w f(w) X^w`; this is `kronEnc f`, so the
  table-form commitment `Enc^T(f) = ev_L(V_f)` is `encode L f`: the same map as the
  coefficient-form commitment, applied to the table of values.
* `N = 2^n`; the reversal of `P ∈ F[X]_{<N}` is `P* = ∑_{j<N} [X^{N-1-j}]P X^j` (`revP`).
* The inverse `ξ⁻¹` of a point `ξ ∈ L` is `invPt ξ`.
-/
import KroneckerFRI.Opening
import KroneckerFRI.Scheme

set_option autoImplicit false

open Polynomial Finset KBFold

namespace KroneckerFRI

variable {F : Type*} [Field F]

/-! ### Lemma eval: the table-form evaluation kernel -/

section Eval

variable {n : ℕ}

/-- The table-form evaluation kernel `E*_z(X) = ∏_k (z_k + (1 - z_k) X^{2^k})`. -/
noncomputable def evalKer (z : Fin n → F) : F[X] := tprod (fun k => 1 - z k) z

lemma evalKer_mem (z : Fin n → F) : evalKer z ∈ degreeLT F (2 ^ n) := tprod_mem_degreeLT _ _

/-- `[X^{N-1-w}] E*_z = eq(w, z)`. -/
lemma coeff_evalKer_compl (z : Fin n → F) (a : Fin n → Bool) :
    (evalKer z).coeff (2 ^ n - 1 - bitsToNat a) = eqv (pt a) z := by
  rw [← bitsToNat_bcompl, evalKer, coeff_tprod, eqv]
  refine prod_congr rfl (fun k _ => ?_)
  cases h : a k <;> simp [bcompl, h, pt, eq1, bval]

/-- **Lemma eval:** `f~(z) = [X^{N-1}] V_f E*_z`. -/
theorem eval_table (f : Table F n) (z : Fin n → F) :
    mle f z = (kronEnc f * evalKer z).coeff (2 ^ n - 1) := by
  rw [coeff_mul_top, mle]
  exact sum_congr rfl (fun a _ => by rw [coeff_evalKer_compl])

end Eval

/-! ### The reversal and Lemma ip -/

section Reversal

variable {N : ℕ}

/-- The reversal `P*(X) = X^{N-1} P(1/X)` of `P ∈ F[X]_{<N}`, as `∑_{j<N} [X^{N-1-j}]P X^j`. -/
noncomputable def revP (N : ℕ) (P : F[X]) : F[X] := ofFn N (fun j => P.coeff (N - 1 - j))

lemma revP_mem (N : ℕ) (P : F[X]) : revP N P ∈ degreeLT F N := ofFn_mem_degreeLT _ _

lemma coeff_revP (P : F[X]) (j : ℕ) :
    (revP N P).coeff j = if j < N then P.coeff (N - 1 - j) else 0 := coeff_ofFn _ _ _

/-- `(P*)* = P` for `P ∈ F[X]_{<N}`. -/
theorem revP_revP {P : F[X]} (hP : P ∈ degreeLT F N) : revP N (revP N P) = P := by
  ext j
  rw [coeff_revP]
  split_ifs with h
  · rw [coeff_revP, if_pos (by omega), show N - 1 - (N - 1 - j) = j by omega]
  · rw [coeff_eq_zero_of_mem_degreeLT hP (by omega)]

/-- `P*(x) = x^{N-1} P(x⁻¹)` for `x ≠ 0` and `P ∈ F[X]_{<N}`. -/
theorem eval_revP {P : F[X]} (hP : P ∈ degreeLT F N) {x : F} (hx : x ≠ 0) :
    (revP N P).eval x = x ^ (N - 1) * P.eval x⁻¹ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : P = 0 := by
      rw [mem_degreeLT] at hP
      exact degree_eq_bot.1 (by simpa using hP)
    simp [revP, ofFn, this]
  have hPsum : P.eval x⁻¹ = ∑ i ∈ range N, P.coeff i * x⁻¹ ^ i :=
    eval_eq_sum_range' (lt_of_le_of_lt (natDegree_le_of_mem_degreeLT hP) (by omega)) _
  rw [hPsum, mul_sum, revP, ofFn]
  simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  rw [← sum_range_reflect]
  refine sum_congr rfl (fun i hi => ?_)
  rw [mem_range] at hi
  rw [show N - 1 - (N - 1 - i) = i by omega]
  rw [inv_pow, mul_left_comm, ← div_eq_mul_inv, pow_sub₀ _ hx (by omega), div_eq_mul_inv]

/-- **Lemma ip:** `∑_w a(w) b(w) = [X^{N-1}] V_a V_b*`. -/
theorem inner_product {n : ℕ} (a b : Table F n) :
    ∑ w, a w * b w = (kronEnc a * revP (2 ^ n) (kronEnc b)).coeff (2 ^ n - 1) := by
  rw [coeff_mul_top]
  refine sum_congr rfl (fun w _ => ?_)
  have hw := bitsToNat_lt w
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [coeff_revP, if_pos (by omega), show 2 ^ n - 1 - (2 ^ n - 1 - bitsToNat w) = bitsToNat w by
    omega, coeff_kronEnc_bits]

end Reversal

/-! ### Lemma gen-identity: split and identity for a general `K ∈ F[X]_{<N}` -/

section General

variable {N : ℕ}

lemma coeff_mul_eq_zero_of_lt {U K : F[X]} (hU : U ∈ degreeLT F N) (hK : K ∈ degreeLT F N)
    {m : ℕ} (hm : 2 * N - 1 ≤ m) : (U * K).coeff m = 0 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : U = 0 := by
      rw [mem_degreeLT] at hU; exact degree_eq_bot.1 (by simpa using hU)
    simp [this]
  have h1 := natDegree_le_of_mem_degreeLT hU
  have h2 := natDegree_le_of_mem_degreeLT hK
  refine coeff_eq_zero_of_natDegree_lt ((natDegree_mul_le).trans_lt ?_)
  omega

/-- The opening polynomial `A_{U,K} = ∑_{j<N} [X^j](X U K) X^j`. -/
noncomputable def openAG (N : ℕ) (U K : F[X]) : F[X] := ofFn N (fun j => (X * (U * K)).coeff j)

/-- The opening polynomial `H_{U,K} = ∑_{j<N} [X^{N+1+j}](X U K) X^j`. -/
noncomputable def openHG (N : ℕ) (U K : F[X]) : F[X] :=
  ofFn N (fun j => (X * (U * K)).coeff (N + 1 + j))

lemma openAG_mem (N : ℕ) (U K : F[X]) : openAG N U K ∈ degreeLT F N := ofFn_mem_degreeLT _ _
lemma openHG_mem (N : ℕ) (U K : F[X]) : openHG N U K ∈ degreeLT F N := ofFn_mem_degreeLT _ _

/-- The split `X U K = A + [X^{N-1}](UK) X^N + X^{N+1} H`. -/
theorem splitG_eq {U K : F[X]} (hN : 1 ≤ N) (hU : U ∈ degreeLT F N) (hK : K ∈ degreeLT F N) :
    X * U * K = assemble N (openAG N U K) ((U * K).coeff (N - 1)) (openHG N U K) := by
  ext i
  rw [coeff_assemble (openAG_mem N U K), mul_assoc]
  by_cases h1 : i < N
  · rw [if_pos h1, openAG, coeff_ofFn, if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : i = N
    · rw [if_pos h2, h2, show N = (N - 1) + 1 by omega, coeff_X_mul,
        show N - 1 + 1 - 1 = N - 1 by omega]
    · rw [if_neg h2, openHG, coeff_ofFn]
      by_cases h3 : i - (N + 1) < N
      · rw [if_pos h3, show N + 1 + (i - (N + 1)) = i by omega]
      · rw [if_neg h3]
        obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
        rw [coeff_X_mul, coeff_mul_eq_zero_of_lt hU hK (by omega)]

/-- **Lemma gen-identity(1) (split).** -/
theorem splitG_iff {U K : F[X]} (hN : 1 ≤ N) (hU : U ∈ degreeLT F N) (hK : K ∈ degreeLT F N)
    (v : F) :
    (∃ A ∈ degreeLT F N, ∃ H ∈ degreeLT F N, X * U * K = assemble N A v H) ↔
      v = (U * K).coeff (N - 1) := by
  constructor
  · rintro ⟨A, hA, H, -, h⟩
    rw [splitG_eq hN hU hK] at h
    exact ((assemble_inj (openAG_mem N U K) hA h).2.1).symm
  · rintro rfl
    exact ⟨_, openAG_mem N U K, _, openHG_mem N U K, splitG_eq hN hU hK⟩

/-- `Φ = X U K - A - v X^N - X^{N+1} H`. -/
noncomputable def PhiG (N : ℕ) (U K A H : F[X]) (v : F) : F[X] := X * U * K - assemble N A v H

/-- **Lemma gen-identity(2):** `deg Φ ≤ 2N` … -/
theorem natDegree_PhiG_le {U K A H : F[X]} (hU : U ∈ degreeLT F N) (hK : K ∈ degreeLT F N)
    (hA : A ∈ degreeLT F N) (hH : H ∈ degreeLT F N) (v : F) :
    (PhiG N U K A H v).natDegree ≤ 2 * N := by
  refine natDegree_le_iff_coeff_eq_zero.2 (fun m hm => ?_)
  have hm' : 2 * N < m := by exact_mod_cast hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [PhiG, coeff_sub, mul_assoc, coeff_X_mul, coeff_mul_eq_zero_of_lt hU hK (by omega),
    coeff_assemble hA, if_neg (by omega), if_neg (by omega),
    coeff_eq_zero_of_mem_degreeLT hH (by omega), sub_zero]

/-- … **and `Φ = 0` implies `v = [X^{N-1}] U K`.** -/
theorem identityG {U K A H : F[X]} (hN : 1 ≤ N) (hA : A ∈ degreeLT F N) {v : F}
    (h : PhiG N U K A H v = 0) : v = (U * K).coeff (N - 1) := by
  have h' : X * U * K = assemble N A v H := sub_eq_zero.1 h
  have hc := congrArg (fun P : F[X] => P.coeff N) h'
  simp only at hc
  rw [coeff_assemble hA, if_neg (lt_irrefl _), if_pos rfl, mul_assoc,
    show N = (N - 1) + 1 by omega, coeff_X_mul] at hc
  rw [← hc]

end General

/-! ### Lemma rev: reversed words -/

section RevWords

variable {L : Subgroup Fˣ}

/-- The point `ξ⁻¹ ∈ L`. -/
def invPt (ξ : L) : L := ξ⁻¹

lemma xv'_invPt (ξ : L) : xv' (invPt ξ) = (xv' ξ)⁻¹ := by
  simp [invPt, xv']

lemma invPt_invPt (ξ : L) : invPt (invPt ξ) = ξ := inv_inv ξ

lemma invPt_injective : Function.Injective (invPt (L := L)) := inv_injective

/-- `(-ξ)⁻¹ = -(ξ⁻¹)`. -/
lemma negPt_invPt (hL : (-1 : Fˣ) ∈ L) (ξ : L) : negPt (invPt ξ) = invPt (negPt ξ) := by
  apply Subtype.ext
  rw [coe_negPt hL]
  simp only [invPt, InvMemClass.coe_inv, coe_negPt hL, inv_neg]

/-- The reversed word `w*(ξ) = ξ^{N-1} w(ξ⁻¹)`. -/
noncomputable def wrev (N : ℕ) (w : L → F) : L → F := fun ξ => xv' ξ ^ (N - 1) * w (invPt ξ)

/-- **Lemma rev(1):** `(ev_L P)* = ev_L(P*)` for `P ∈ F[X]_{<N}`. -/
theorem wrev_ev {N : ℕ} {P : F[X]} (hP : P ∈ degreeLT F N) : wrev N (ev L P) = ev L (revP N P) := by
  funext ξ
  simp only [wrev, ev]
  rw [eval_revP hP (xv'_ne_zero ξ), ← xv'_invPt]

/-- **Lemma rev(2):** `w ↦ w*` is linear … -/
theorem wrev_add (N : ℕ) (w w' : L → F) : wrev N (w + w') = wrev N w + wrev N w' := by
  funext ξ; simp [wrev, mul_add]

theorem wrev_smul (N : ℕ) (c : F) (w : L → F) : wrev N (c • w) = c • wrev N w := by
  funext ξ; simp [wrev]; ring

/-- … and involutive. -/
theorem wrev_wrev (N : ℕ) (w : L → F) : wrev N (wrev N w) = w := by
  funext ξ
  simp only [wrev, invPt_invPt, xv'_invPt]
  have hx := xv'_ne_zero ξ
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hx, one_pow, one_mul]

/-- **Lemma rev(2), pointwise:** `w*(ξ) = c*(ξ)` iff `w(ξ⁻¹) = c(ξ⁻¹)`. -/
theorem wrev_eq_iff (N : ℕ) (w c : L → F) (ξ : L) :
    wrev N w ξ = wrev N c ξ ↔ w (invPt ξ) = c (invPt ξ) := by
  simp only [wrev]
  exact mul_right_inj' (pow_ne_zero _ (xv'_ne_zero ξ))

/-- **Lemma rev(3):** `T⁻¹` is fibre-closed if `T` is … -/
theorem inv_image_closed (hL : (-1 : Fˣ) ∈ L) {T : Set L} (hT : ∀ ξ ∈ T, negPt ξ ∈ T) :
    ∀ ζ ∈ invPt '' T, negPt ζ ∈ invPt '' T := by
  rintro _ ⟨ξ, hξ, rfl⟩
  exact ⟨negPt ξ, hT ξ hξ, (negPt_invPt hL ξ).symm⟩

/-- … and `|T⁻¹| = |T|`. -/
theorem ncard_inv_image (T : Set L) : (invPt '' T).ncard = T.ncard :=
  Set.ncard_image_of_injective T invPt_injective

end RevWords

end KroneckerFRI
