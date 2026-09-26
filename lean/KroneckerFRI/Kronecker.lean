/-
KroneckerFRI/Kronecker.lean
§4 of the paper: the Kronecker encoding (Definition 4.1, Lemma 4.2), the kernel polynomial
(Definition 4.3, Lemma 4.4), the extraction identity (Theorem 4.5) and its corollaries
(Corollaries 4.6, 4.7, Proposition 4.8), the split lemma (Lemma 4.10), the opening polynomials
(Definition 4.11), the identity lemma (Lemma 4.12) and the reversal (Lemma 4.14).

Conventions.
* A multilinear polynomial in coefficient form is its coefficient table `α : Table F n`,
  `α a = α_a` for the bit vector `a : Fin n → Bool` (bit `k` of the code is the paper's bit
  `k+1`); its value at `z` is `cEval α z = ∑_a α_a z^a` with `z^a = mono a z`.
  The table form is related to it by the Möbius transform (`mle_eq_cEval`).
* `N = 2^n`; the integer with bit vector `a` is `bitsToNat a`, and its complement
  `ā = N - 1 - a` is `bitsToNat (bcompl a)` (`bitsToNat_bcompl`).
* The kernel polynomial `K_z = ∏_k (X^{2^k} + z_k)` is `kernel z` of `KBFold/Kernel.lean`.
-/
import KBFold.Mobius

set_option autoImplicit false

open Polynomial Finset KBFold

namespace KroneckerFRI

/-! ### Coefficient form -/

section CoeffForm

variable {A : Type*} [CommRing A]

/-- The value `f(z) = ∑_a α_a z^a` of the multilinear polynomial with coefficient table `α`
(Definition 2.5 of the paper, coefficient form). -/
def cEval {n : ℕ} (α : Table A n) (z : Fin n → A) : A := ∑ a, α a * mono a z

lemma cEval_add {n : ℕ} (α β : Table A n) (z : Fin n → A) :
    cEval (α + β) z = cEval α z + cEval β z := by
  simp [cEval, add_mul, sum_add_distrib]

lemma cEval_smul {n : ℕ} (c : A) (α : Table A n) (z : Fin n → A) :
    cEval (c • α) z = c * cEval α z := by
  simp [cEval, mul_sum, mul_assoc]

/-- The table form and the coefficient form give the same function: `f~(z) = ∑_a α_a z^a` with
`α = mobius f` (Lemma 2.6). -/
theorem mle_eq_cEval {n : ℕ} (f : Table A n) (z : Fin n → A) : mle f z = cEval (mobius f) z :=
  mle_eq_sum_mono f z

end CoeffForm

/-! ### Bits -/

/-- `∑_{k<n} 2^k + 1 = 2^n`. -/
lemma sum_two_pow_fin (n : ℕ) : ∑ k : Fin n, 2 ^ (k : ℕ) + 1 = 2 ^ n := by
  rw [Fin.sum_univ_eq_sum_range (fun k => 2 ^ k)]
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, pow_succ]; omega

/-- `a + ā = N - 1` (Lemma 2.1 of the paper, complement). -/
lemma bitsToNat_add_bcompl {n : ℕ} (a : Fin n → Bool) :
    bitsToNat a + bitsToNat (bcompl a) + 1 = 2 ^ n := by
  rw [← sum_two_pow_fin n, bitsToNat, bitsToNat, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl (fun k _ => ?_)
  cases h : a k <;> simp [bcompl, h]

lemma bitsToNat_bcompl {n : ℕ} (a : Fin n → Bool) :
    bitsToNat (bcompl a) = 2 ^ n - 1 - bitsToNat a := by
  have := bitsToNat_add_bcompl a; omega

lemma bcompl_bcompl {n : ℕ} (a : Fin n → Bool) : bcompl (bcompl a) = a := by
  funext k; simp [bcompl]

/-- Every `j < 2^n` is `bitsToNat a` for a unique bit vector `a`. -/
lemma exists_bits {n j : ℕ} (hj : j < 2 ^ n) : ∃ a : Fin n → Bool, bitsToNat a = j := by
  obtain ⟨a, ha⟩ := (bitsToNat_bijective n).2 ⟨j, hj⟩
  exact ⟨a, congrArg Fin.val ha⟩

/-! ### Products of binomials `∏_k (a_k X^{2^k} + b_k)` -/

section TProd

variable {F : Type*} [Field F]

/-- `T_{a,b}(X) = ∏_k (a_k X^{2^k} + b_k)`; the kernel polynomial is `T_{1,z}`, its reversal
`T_{z,1}`, and the polynomial of Corollary 4.7 is `T_{2,1}`. -/
noncomputable def tprod {n : ℕ} (a b : Fin n → F) : F[X] :=
  ∏ k : Fin n, (C (a k) * X ^ (2 ^ (k : ℕ)) + C (b k))

lemma tprod_cons {n : ℕ} (a0 b0 : F) (a b : Fin n → F) :
    tprod (Fin.cons a0 a : Fin (n + 1) → F) (Fin.cons b0 b) =
      (C a0 * X + C b0) * expand F 2 (tprod a b) := by
  unfold tprod
  rw [Fin.prod_univ_succ, map_prod]
  congr 1
  · simp
  · refine prod_congr rfl (fun k _ => ?_)
    simp [map_add, map_mul, expand_C, expand_X_pow_two_pow]

/-- `T_{a,b}` has degree at most `N - 1`. -/
theorem natDegree_tprod_le {n : ℕ} (a b : Fin n → F) : (tprod a b).natDegree ≤ 2 ^ n - 1 := by
  unfold tprod
  refine (natDegree_prod_le _ _).trans ?_
  have hk : ∀ k : Fin n, (C (a k) * X ^ (2 ^ (k : ℕ)) + C (b k)).natDegree ≤ 2 ^ (k : ℕ) :=
    fun k => (natDegree_add_le _ _).trans (max_le (natDegree_C_mul_X_pow_le _ _) (by simp))
  refine (sum_le_sum fun k _ => hk k).trans ?_
  have := sum_two_pow_fin n; omega

/-- `T_{a,b}` has degree less than `N = 2^n`. -/
theorem tprod_mem_degreeLT {n : ℕ} (a b : Fin n → F) : tprod a b ∈ degreeLT F (2 ^ n) := by
  rw [mem_degreeLT]
  refine lt_of_le_of_lt degree_le_natDegree ?_
  have h := natDegree_tprod_le a b
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  exact_mod_cast (by omega : (tprod a b).natDegree < 2 ^ n)

/-- **Coefficient rule** for `T_{a,b}` (proof of Lemma 4.4(3)):
`[X^c] T_{a,b} = ∏_k (a_k if c_k = 1, b_k if c_k = 0)`. -/
theorem coeff_tprod : ∀ {n : ℕ} (a b : Fin n → F) (c : Fin n → Bool),
    (tprod a b).coeff (bitsToNat c) = ∏ k, if c k then a k else b k
  | 0, a, b, c => by simp [tprod, bitsToNat]
  | n + 1, a, b, c => by
      rw [← Fin.cons_self_tail a, ← Fin.cons_self_tail b, ← Fin.cons_self_tail c, tprod_cons,
        bitsToNat_cons, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← coeff_tprod (Fin.tail a) (Fin.tail b) (Fin.tail c), add_mul, coeff_add,
        mul_assoc, coeff_C_mul, coeff_C_mul]
      cases c 0
      · simp only [Bool.false_eq_true, if_false, zero_add]
        rw [coeff_X_mul_expand_even, coeff_expand_two_even, mul_zero, zero_add]
      · simp only [if_true]
        rw [add_comm 1, coeff_X_mul_expand_odd, coeff_expand_two_odd, mul_zero, add_zero]

lemma coeff_tprod_of_ge {n : ℕ} (a b : Fin n → F) {i : ℕ} (hi : 2 ^ n ≤ i) :
    (tprod a b).coeff i = 0 := by
  have h := tprod_mem_degreeLT a b
  rw [mem_degreeLT, degree_lt_iff_coeff_zero] at h
  exact h i hi

end TProd

/-! ### Definition 4.1 and Lemma 4.2: the Kronecker encoding -/

section Encoding

variable {F : Type*} [Field F]

/-- **Definition 4.1 (Kronecker encoding):** `U_f(X) = ∑_a α_a X^a`. -/
noncomputable def kronEnc {n : ℕ} (α : Table F n) : F[X] := ∑ a, C (α a) * X ^ bitsToNat a

/-- The coefficient table of a polynomial of degree `< N` (inverse of `kronEnc`). -/
noncomputable def kronCoeffs (n : ℕ) (U : F[X]) : Table F n := fun a => U.coeff (bitsToNat a)

lemma coeff_kronEnc {n : ℕ} (α : Table F n) (j : ℕ) :
    (kronEnc α).coeff j = ∑ a, if bitsToNat a = j then α a else 0 := by
  simp only [kronEnc, finset_sum_coeff, coeff_C_mul, coeff_X_pow]
  refine sum_congr rfl (fun a _ => ?_)
  by_cases h : bitsToNat a = j
  · subst h; simp
  · simp [h, Ne.symm h]

lemma coeff_kronEnc_bits {n : ℕ} (α : Table F n) (a : Fin n → Bool) :
    (kronEnc α).coeff (bitsToNat a) = α a := by
  rw [coeff_kronEnc, sum_eq_single a]
  · simp
  · intro b _ hb; rw [if_neg (fun h => hb (bitsToNat_injective h))]
  · simp

lemma coeff_kronEnc_of_ge {n : ℕ} (α : Table F n) {j : ℕ} (hj : 2 ^ n ≤ j) :
    (kronEnc α).coeff j = 0 := by
  rw [coeff_kronEnc]
  refine sum_eq_zero (fun a _ => ?_)
  have := bitsToNat_lt a
  rw [if_neg (by omega)]

lemma kronEnc_mem_degreeLT {n : ℕ} (α : Table F n) : kronEnc α ∈ degreeLT F (2 ^ n) := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero]
  intro j hj; exact coeff_kronEnc_of_ge α hj

/-- **Lemma 4.2(1) (Kronecker substitution):** `U_f(X) = f(X, X^2, …, X^{2^{n-1}})`. -/
theorem kronEnc_eq_subst {n : ℕ} (α : Table F n) :
    kronEnc α = cEval (fun a => C (α a)) (fun k : Fin n => (X : F[X]) ^ (2 ^ (k : ℕ))) := by
  unfold kronEnc cEval
  refine sum_congr rfl (fun a _ => ?_)
  congr 1
  unfold mono bitsToNat
  rw [← prod_pow_eq_pow_sum]
  refine prod_congr rfl (fun k _ => ?_)
  split_ifs <;> simp

lemma kronEnc_add {n : ℕ} (α β : Table F n) : kronEnc (α + β) = kronEnc α + kronEnc β := by
  simp [kronEnc, add_mul, sum_add_distrib]

lemma kronEnc_smul {n : ℕ} (c : F) (α : Table F n) : kronEnc (c • α) = C c * kronEnc α := by
  simp [kronEnc, mul_sum, mul_assoc]

/-- `kronCoeffs ∘ kronEnc = id`. -/
theorem kronCoeffs_kronEnc {n : ℕ} (α : Table F n) : kronCoeffs n (kronEnc α) = α := by
  funext a; exact coeff_kronEnc_bits α a

/-- `kronEnc ∘ kronCoeffs = id` on `F[X]_{<N}`. -/
theorem kronEnc_kronCoeffs {n : ℕ} {U : F[X]} (hU : U ∈ degreeLT F (2 ^ n)) :
    kronEnc (kronCoeffs n U) = U := by
  ext j
  by_cases hj : j < 2 ^ n
  · obtain ⟨a, rfl⟩ := exists_bits hj
    rw [coeff_kronEnc_bits]; rfl
  · rw [coeff_kronEnc_of_ge _ (by omega)]
    rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hU
    exact (hU j (by omega)).symm

/-- **Lemma 4.2(2):** `f ↦ U_f` is an `F`-linear bijection from `ℒ_n(F)` onto `F[X]_{<N}`. -/
noncomputable def kronEncLin (n : ℕ) : Table F n →ₗ[F] degreeLT F (2 ^ n) where
  toFun α := ⟨kronEnc α, kronEnc_mem_degreeLT α⟩
  map_add' α β := by ext1; simp [kronEnc_add]
  map_smul' c α := by ext1; simp [kronEnc_smul, smul_eq_C_mul]

theorem kronEncLin_bijective (n : ℕ) : Function.Bijective (kronEncLin (F := F) n) := by
  constructor
  · intro α β h
    have h' : kronEnc α = kronEnc β := congrArg Subtype.val h
    rw [← kronCoeffs_kronEnc α, ← kronCoeffs_kronEnc β, h']
  · rintro ⟨U, hU⟩
    exact ⟨kronCoeffs n U, Subtype.ext (kronEnc_kronCoeffs hU)⟩

end Encoding

/-! ### Definition 4.3 and Lemma 4.4: the kernel polynomial -/

section KernelPoly

variable {F : Type*} [Field F]

lemma kernel_eq_tprod {n : ℕ} (z : Fin n → F) : kernel z = tprod (fun _ => 1) z := by
  simp [kernel, tprod]

/-- **Lemma 4.4(1):** `K_z` is monic of degree `N - 1`. -/
theorem kernel_monic {n : ℕ} (z : Fin n → F) : (kernel z).Monic := by
  unfold kernel
  refine monic_prod_of_monic _ _ (fun k _ => ?_)
  exact monic_X_pow_add_C _ (pow_ne_zero _ two_ne_zero)

theorem natDegree_kernel {n : ℕ} (z : Fin n → F) : (kernel z).natDegree = 2 ^ n - 1 := by
  unfold kernel
  rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_pow_add_C _ (pow_ne_zero _ two_ne_zero))]
  have : ∀ k : Fin n, (X ^ (2 ^ (k : ℕ)) + C (z k)).natDegree = 2 ^ (k : ℕ) := by
    intro k; rw [natDegree_X_pow_add_C]
  simp_rw [this]
  have := sum_two_pow_fin n; omega

/-- **Lemma 4.4(2) (recursion):** `K_z(X) = (X + z_1) K_{z'}(X^2)`. -/
theorem kernel_recursion {n : ℕ} (z : Fin (n + 1) → F) :
    kernel z = (X + C (z 0)) * expand F 2 (kernel (Fin.tail z)) := by
  conv_lhs => rw [← Fin.cons_self_tail z]
  exact kernel_cons _ _

/-- Lemma 4.4(2) evaluated (the recursion of Lemma 6.7): `K_z(x) = (x + z_1) K_{z'}(x^2)`. -/
theorem kernel_eval_recursion {n : ℕ} (z : Fin (n + 1) → F) (x : F) :
    (kernel z).eval x = (x + z 0) * (kernel (Fin.tail z)).eval (x ^ 2) := by
  rw [kernel_recursion, eval_mul, eval_add, eval_X, eval_C, expand_eval]

/-- **Lemma 4.4(3) (coefficient rule):** `[X^j] K_z = ∏_{k : j_k = 0} z_k = z^{j̄}`. -/
theorem coeff_kernel_bits {n : ℕ} (z : Fin n → F) (j : Fin n → Bool) :
    (kernel z).coeff (bitsToNat j) = mono (bcompl j) z := by
  rw [coeff_kernel, mono]
  refine prod_congr rfl (fun k _ => ?_)
  cases h : j k <;> simp [bcompl, h]

/-- `[X^{N-1-a}] K_z = z^a`. -/
theorem coeff_kernel_compl {n : ℕ} (z : Fin n → F) (a : Fin n → Bool) :
    (kernel z).coeff (2 ^ n - 1 - bitsToNat a) = mono a z := by
  rw [← bitsToNat_bcompl, coeff_kernel_bits, bcompl_bcompl]

end KernelPoly

/-! ### Theorem 4.5: the extraction identity -/

section Extraction

variable {F : Type*} [Field F]

/-- `[X^{N-1}] (U · K) = ∑_{i<N} [X^i]U · [X^{N-1-i}]K` for `U` of degree `< N`. -/
lemma coeff_mul_top {n : ℕ} (α : Table F n) (K : F[X]) :
    (kronEnc α * K).coeff (2 ^ n - 1) = ∑ a, α a * K.coeff (2 ^ n - 1 - bitsToNat a) := by
  simp only [kronEnc, sum_mul, finset_sum_coeff, mul_assoc, coeff_C_mul]
  refine sum_congr rfl (fun a _ => ?_)
  congr 1
  have ha := bitsToNat_lt a
  rw [coeff_X_pow_mul', if_pos (by omega)]

/-- **Theorem 4.5 (extraction identity):** `f(z) = [X^{N-1}] U_f(X) K_z(X)`. -/
theorem extraction {n : ℕ} (α : Table F n) (z : Fin n → F) :
    cEval α z = (kronEnc α * kernel z).coeff (2 ^ n - 1) := by
  rw [coeff_mul_top, cEval]
  refine sum_congr rfl (fun a _ => ?_)
  rw [coeff_kernel_compl]

/-- Theorem 4.5 for a polynomial of degree `< N`: `[X^{N-1}] U K_z = f(z)` with `U = U_f`. -/
theorem extraction' {n : ℕ} {U : F[X]} (hU : U ∈ degreeLT F (2 ^ n)) (z : Fin n → F) :
    (U * kernel z).coeff (2 ^ n - 1) = cEval (kronCoeffs n U) z := by
  rw [extraction, kronEnc_kronCoeffs hU]

/-- Theorem 4.5 in table form: `f~(z) = [X^{N-1}] U_{mobius f} K_z`. -/
theorem extraction_table {n : ℕ} (f : Table F n) (z : Fin n → F) :
    mle f z = (kronEnc (mobius f) * kernel z).coeff (2 ^ n - 1) := by
  rw [mle_eq_cEval, extraction]

/-- **Corollary 4.6 (linear combinations of points).** -/
theorem extraction_comb {n s : ℕ} (α : Table F n) (zs : Fin s → Fin n → F) (γ : Fin s → F) :
    ∑ i, γ i * cEval α (zs i) =
      (kronEnc α * ∑ i, C (γ i) * kernel (zs i)).coeff (2 ^ n - 1) := by
  simp only [mul_sum, finset_sum_coeff, extraction]
  refine sum_congr rfl (fun i _ => ?_)
  rw [mul_left_comm, coeff_C_mul]

/-- **Corollary 4.7 (sums over the hypercube):**
`∑_b f(b) = [X^{N-1}] U_f ∏_k (1 + 2 X^{2^k})`. -/
theorem cube_sum {n : ℕ} (α : Table F n) :
    ∑ b : Fin n → Bool, cEval α (pt b) =
      (kronEnc α * tprod (fun _ : Fin n => (2 : F)) (fun _ => 1)).coeff (2 ^ n - 1) := by
  rw [coeff_mul_top]
  simp only [cEval]
  rw [sum_comm]
  refine sum_congr rfl (fun a _ => ?_)
  rw [← mul_sum, ← bitsToNat_bcompl, coeff_tprod]
  congr 1
  -- `∑_b b^a = ∏_k (1 if a_k = 1, 2 if a_k = 0)`
  have hs : (∑ b : Fin n → Bool, mono a (pt b : Fin n → F)) =
      ∏ k, ∑ β : Bool, (if a k then (bval β : F) else 1) :=
    (prod_sum_bool (fun k (β : Bool) => if a k then (bval β : F) else 1)).symm
  rw [hs]
  refine prod_congr rfl (fun k _ => ?_)
  cases h : a k <;> simp [bcompl, bval, h]

/-- `∏_k (1 + 2 X^{2^k}) = 2^n K_{(1/2,…,1/2)}` in characteristic `≠ 2`. -/
lemma tprod_two_one {n : ℕ} (h2 : (2 : F) ≠ 0) :
    tprod (fun _ : Fin n => (2 : F)) (fun _ => 1) = C (2 ^ n) * kernel (fun _ : Fin n => (1 / 2 : F)) := by
  unfold tprod kernel
  rw [show (C (2 ^ n) : F[X]) = ∏ _k : Fin n, C 2 by simp [prod_const], ← prod_mul_distrib]
  refine prod_congr rfl (fun k _ => ?_)
  rw [mul_add, ← C_mul, mul_one_div_cancel h2]

/-- Corollary 4.7, second part: in characteristic `≠ 2`, both sides equal `2^n f(1/2,…,1/2)`. -/
theorem cube_sum_half {n : ℕ} (h2 : (2 : F) ≠ 0) (α : Table F n) :
    ∑ b : Fin n → Bool, cEval α (pt b) = 2 ^ n * cEval α (fun _ => 1 / 2) := by
  rw [cube_sum, tprod_two_one h2, mul_left_comm, coeff_C_mul, ← extraction]

end Extraction

/-! ### Proposition 4.8 and Lemma 4.14 -/

section Further

variable {F : Type*} [Field F]

/-- A polynomial of degree `< N` has `natDegree ≤ N - 1`. -/
lemma natDegree_le_of_mem_degreeLT {U : F[X]} {N : ℕ} (hU : U ∈ degreeLT F N) :
    U.natDegree ≤ N - 1 := by
  by_cases h0 : U = 0
  · simp [h0]
  · rw [mem_degreeLT, ← natDegree_lt_iff_degree_lt h0] at hU; omega

/-- **Proposition 4.8(1):** `[X^{N-1}] K_y K_z = ∏_k (y_k + z_k)`. -/
theorem bilinear {n : ℕ} (y z : Fin n → F) :
    (kernel y * kernel z).coeff (2 ^ n - 1) = ∏ k, (y k + z k) := by
  have hK : kernel y ∈ degreeLT F (2 ^ n) := by rw [kernel_eq_tprod]; exact tprod_mem_degreeLT _ _
  rw [extraction' hK, cEval]
  have e : ∏ k, (y k + z k) = ∏ k, ∑ β : Bool, (if β then z k else y k) := by
    refine prod_congr rfl (fun k _ => ?_); simp [add_comm]
  rw [e, prod_sum_bool]
  refine sum_congr rfl (fun c _ => ?_)
  simp only [kronCoeffs, coeff_kernel_bits, mono, ← prod_mul_distrib]
  refine prod_congr rfl (fun k _ => ?_)
  cases h : c k <;> simp [bcompl, h]

/-- **Proposition 4.8(2):** `K_y(X) K_{-y}(X) = ∏_k (X^{2^{k+1}} - y_k^2)`. -/
theorem kernel_mul_neg {n : ℕ} (y : Fin n → F) :
    kernel y * kernel (-y) = ∏ k : Fin n, (X ^ (2 ^ ((k : ℕ) + 1)) - C (y k ^ 2)) := by
  unfold kernel
  rw [← prod_mul_distrib]
  refine prod_congr rfl (fun k _ => ?_)
  have e : (X : F[X]) ^ (2 ^ ((k : ℕ) + 1)) = (X ^ (2 ^ (k : ℕ))) ^ 2 := by
    rw [← pow_mul, pow_succ]
  rw [e, Pi.neg_apply, C_neg, C_pow]
  ring

/-- **Lemma 4.14 (reversal):** `K*_z(X) = X^{N-1} K_z(1/X) = ∏_k (1 + z_k X^{2^k})`
(the reversal is `reflect (N-1)`). -/
theorem kernel_reflect {n : ℕ} (z : Fin n → F) :
    reflect (2 ^ n - 1) (kernel z) = tprod z (fun _ => 1) := by
  ext i
  rw [coeff_reflect]
  by_cases hi : i < 2 ^ n
  · obtain ⟨a, rfl⟩ := exists_bits hi
    rw [revAt_le (by omega), ← bitsToNat_bcompl, coeff_kernel_bits, bcompl_bcompl, coeff_tprod,
      mono]
  · have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [coeff_tprod_of_ge _ _ (by omega), revAt, Function.Embedding.coeFn_mk, if_neg (by omega)]
    rw [kernel_eq_tprod, coeff_tprod_of_ge _ _ (by omega)]

/-- Lemma 4.14, coefficients: `[X^a] K*_z = z^a`. -/
theorem coeff_kernel_reflect {n : ℕ} (z : Fin n → F) (a : Fin n → Bool) :
    (reflect (2 ^ n - 1) (kernel z)).coeff (bitsToNat a) = mono a z := by
  rw [kernel_reflect, coeff_tprod, mono]

end Further

end KroneckerFRI
