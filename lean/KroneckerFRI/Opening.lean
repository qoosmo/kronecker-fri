/-
KroneckerFRI/Opening.lean
§4.5 of the paper: the split lemma (Lemma 4.10), the opening polynomials (Definition 4.11), the
identity lemma (Lemma 4.12) and Remark 4.13 (why the factor `X`).

`N = 2^n`.  The right-hand side `A + v X^N + X^{N+1} H` of the identity (4.1) is
`assemble N A v H`; its coefficients occupy the disjoint ranges `[0, N-1]`, `{N}` and
`[N+1, 2N]` (`coeff_assemble`), which is the whole content of the uniqueness statements.
-/
import KroneckerFRI.Kronecker

set_option autoImplicit false

open Polynomial Finset KBFold

namespace KroneckerFRI

variable {F : Type*} [Field F]

/-- The polynomial `A + v X^N + X^{N+1} H` of the identity (4.1). -/
noncomputable def assemble (N : ℕ) (A : F[X]) (v : F) (H : F[X]) : F[X] :=
  A + C v * X ^ N + X ^ (N + 1) * H

lemma coeff_eq_zero_of_mem_degreeLT {A : F[X]} {N i : ℕ} (hA : A ∈ degreeLT F N) (hi : N ≤ i) :
    A.coeff i = 0 := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hA; exact hA i hi

/-- The coefficients of `A + v X^N + X^{N+1} H` for `deg A < N`. -/
theorem coeff_assemble {N : ℕ} {A : F[X]} (hA : A ∈ degreeLT F N) (v : F) (H : F[X]) (i : ℕ) :
    (assemble N A v H).coeff i =
      if i < N then A.coeff i else if i = N then v else H.coeff (i - (N + 1)) := by
  simp only [assemble, coeff_add, coeff_C_mul_X_pow, coeff_X_pow_mul']
  by_cases h1 : i < N
  · rw [if_pos h1, if_neg (by omega), if_neg (by omega)]; ring
  · rw [if_neg h1, coeff_eq_zero_of_mem_degreeLT hA (by omega), zero_add]
    by_cases h2 : i = N
    · rw [if_pos h2, if_pos h2, if_neg (by omega), add_zero]
    · rw [if_neg h2, if_neg h2, if_pos (by omega), zero_add]

/-- Uniqueness of the decomposition: `A + v X^N + X^{N+1} H` determines `A`, `v` and `H` when
`deg A < N`. -/
theorem assemble_inj {N : ℕ} {A A' H H' : F[X]} {v v' : F} (hA : A ∈ degreeLT F N)
    (hA' : A' ∈ degreeLT F N) (h : assemble N A v H = assemble N A' v' H') :
    A = A' ∧ v = v' ∧ H = H' := by
  have hc : ∀ i, (assemble N A v H).coeff i = (assemble N A' v' H').coeff i := fun i => by rw [h]
  refine ⟨?_, ?_, ?_⟩
  · ext i
    by_cases hi : i < N
    · have := hc i; rwa [coeff_assemble hA, coeff_assemble hA', if_pos hi, if_pos hi] at this
    · rw [coeff_eq_zero_of_mem_degreeLT hA (by omega), coeff_eq_zero_of_mem_degreeLT hA' (by omega)]
  · have := hc N
    rwa [coeff_assemble hA, coeff_assemble hA', if_neg (lt_irrefl N), if_neg (lt_irrefl N),
      if_pos rfl, if_pos rfl] at this
  · ext j
    have := hc (N + 1 + j)
    rwa [coeff_assemble hA, coeff_assemble hA', if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), show N + 1 + j - (N + 1) = j by omega] at this

/-- The polynomial `∑_{j<N} c_j X^j`. -/
noncomputable def ofFn (N : ℕ) (c : ℕ → F) : F[X] := ∑ j ∈ range N, C (c j) * X ^ j

lemma coeff_ofFn (N : ℕ) (c : ℕ → F) (i : ℕ) : (ofFn N c).coeff i = if i < N then c i else 0 := by
  simp only [ofFn, finset_sum_coeff, coeff_C_mul_X_pow]
  rw [sum_ite_eq (range N) i c]
  simp

lemma ofFn_mem_degreeLT (N : ℕ) (c : ℕ → F) : ofFn N c ∈ degreeLT F N := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero]
  intro m hm; rw [coeff_ofFn, if_neg (by omega)]

section Split

variable {n : ℕ}

/-- `U K_z` has degree at most `2N - 2` for `deg U < N`. -/
lemma coeff_mul_kernel_eq_zero {U : F[X]} (hU : U ∈ degreeLT F (2 ^ n)) (z : Fin n → F) {m : ℕ}
    (hm : 2 * 2 ^ n - 1 ≤ m) : (U * kernel z).coeff m = 0 := by
  have h1 := natDegree_le_of_mem_degreeLT hU
  have h2 := natDegree_kernel z
  have hN : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  refine coeff_eq_zero_of_natDegree_lt ((natDegree_mul_le).trans_lt ?_)
  omega

/-- **Definition 4.11 (opening polynomial `A`):** `A_{U,z} = ∑_{j<N} [X^j](X U K_z) X^j`. -/
noncomputable def openA (U : F[X]) (z : Fin n → F) : F[X] :=
  ofFn (2 ^ n) (fun j => (X * (U * kernel z)).coeff j)

/-- **Definition 4.11 (opening polynomial `H`):** `H_{U,z} = ∑_{j<N} [X^{N+1+j}](X U K_z) X^j`. -/
noncomputable def openH (U : F[X]) (z : Fin n → F) : F[X] :=
  ofFn (2 ^ n) (fun j => (X * (U * kernel z)).coeff (2 ^ n + 1 + j))

/-- The value `v = [X^{N-1}] U K_z`. -/
noncomputable def openV (U : F[X]) (z : Fin n → F) : F := (U * kernel z).coeff (2 ^ n - 1)

lemma openA_mem (U : F[X]) (z : Fin n → F) : openA U z ∈ degreeLT F (2 ^ n) := ofFn_mem_degreeLT _ _
lemma openH_mem (U : F[X]) (z : Fin n → F) : openH U z ∈ degreeLT F (2 ^ n) := ofFn_mem_degreeLT _ _

/-- The split `X U K_z = A + v X^N + X^{N+1} H` with the opening polynomials. -/
theorem split_eq {U : F[X]} (hU : U ∈ degreeLT F (2 ^ n)) (z : Fin n → F) :
    X * U * kernel z = assemble (2 ^ n) (openA U z) (openV U z) (openH U z) := by
  have hN : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  ext i
  rw [coeff_assemble (openA_mem U z), mul_assoc]
  by_cases h1 : i < 2 ^ n
  · rw [if_pos h1, openA, coeff_ofFn, if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : i = 2 ^ n
    · rw [if_pos h2, h2, openV, show 2 ^ n = (2 ^ n - 1) + 1 by omega, coeff_X_mul,
        show 2 ^ n - 1 + 1 - 1 = 2 ^ n - 1 by omega]
    · rw [if_neg h2, openH, coeff_ofFn]
      by_cases h3 : i - (2 ^ n + 1) < 2 ^ n
      · rw [if_pos h3, show 2 ^ n + 1 + (i - (2 ^ n + 1)) = i by omega]
      · rw [if_neg h3]
        obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
        rw [coeff_X_mul, coeff_mul_kernel_eq_zero hU z (by omega)]

/-- **Lemma 4.10 (split).** For `U ∈ F[X]_{<N}`, there are `A, H ∈ F[X]_{<N}` with
`X U K_z = A + v X^N + X^{N+1} H` if and only if `v = [X^{N-1}] U K_z`. -/
theorem split_iff {U : F[X]} (hU : U ∈ degreeLT F (2 ^ n)) (z : Fin n → F) (v : F) :
    (∃ A ∈ degreeLT F (2 ^ n), ∃ H ∈ degreeLT F (2 ^ n), X * U * kernel z = assemble (2 ^ n) A v H)
      ↔ v = (U * kernel z).coeff (2 ^ n - 1) := by
  constructor
  · rintro ⟨A, hA, H, -, h⟩
    rw [split_eq hU z] at h
    exact ((assemble_inj (openA_mem U z) hA h).2.1).symm
  · rintro rfl
    exact ⟨openA U z, openA_mem U z, openH U z, openH_mem U z, split_eq hU z⟩

/-- **Lemma 4.10, uniqueness:** in that case `A` and `H` are the opening polynomials. -/
theorem split_unique {U A H : F[X]} (hU : U ∈ degreeLT F (2 ^ n)) (z : Fin n → F) {v : F}
    (hA : A ∈ degreeLT F (2 ^ n)) (h : X * U * kernel z = assemble (2 ^ n) A v H) :
    A = openA U z ∧ v = openV U z ∧ H = openH U z := by
  rw [split_eq hU z] at h
  obtain ⟨h1, h2, h3⟩ := assemble_inj (openA_mem U z) hA h
  exact ⟨h1.symm, h2.symm, h3.symm⟩

/-- **Lemma 4.10:** `A(0) = 0`. -/
theorem openA_coeff_zero (U : F[X]) (z : Fin n → F) : (openA U z).coeff 0 = 0 := by
  rw [openA, coeff_ofFn, if_pos (by positivity), coeff_X_mul_zero]

/-- **Lemma 4.10:** `deg H ≤ N - 2`, i.e. `H ∈ F[X]_{<N-1}`. -/
theorem openH_mem_pred {U : F[X]} (hU : U ∈ degreeLT F (2 ^ n)) (z : Fin n → F) :
    openH U z ∈ degreeLT F (2 ^ n - 1) := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero]
  intro m hm
  rw [openH, coeff_ofFn]
  split_ifs with h
  · rw [show 2 ^ n + 1 + m = (2 ^ n + m) + 1 by omega, coeff_X_mul,
      coeff_mul_kernel_eq_zero hU z (by omega)]
  · rfl

/-- By Theorem 4.5, for `U = U_f` the value is `v = f(z)`. -/
theorem openV_kronEnc (α : Table F n) (z : Fin n → F) : openV (kronEnc α) z = cEval α z :=
  (extraction α z).symm

end Split

/-! ### Lemma 4.12 (identity lemma) -/

section Identity

variable {n : ℕ}

/-- `Φ = X U K_z - A - v X^N - X^{N+1} H`. -/
noncomputable def Phi (U A H : F[X]) (z : Fin n → F) (v : F) : F[X] :=
  X * U * kernel z - assemble (2 ^ n) A v H

/-- **Lemma 4.12:** `deg Φ ≤ 2N` for `U, A, H ∈ F[X]_{<N}`. -/
theorem Phi_mem_degreeLT {U A H : F[X]} (hU : U ∈ degreeLT F (2 ^ n))
    (hA : A ∈ degreeLT F (2 ^ n)) (hH : H ∈ degreeLT F (2 ^ n)) (z : Fin n → F) (v : F) :
    Phi U A H z v ∈ degreeLT F (2 * 2 ^ n + 1) := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero]
  intro m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Phi, coeff_sub, mul_assoc, coeff_X_mul, coeff_mul_kernel_eq_zero hU z (by omega),
    coeff_assemble hA, if_neg (by omega), if_neg (by omega),
    coeff_eq_zero_of_mem_degreeLT hH (by omega), sub_zero]

theorem natDegree_Phi_le {U A H : F[X]} (hU : U ∈ degreeLT F (2 ^ n))
    (hA : A ∈ degreeLT F (2 ^ n)) (hH : H ∈ degreeLT F (2 ^ n)) (z : Fin n → F) (v : F) :
    (Phi U A H z v).natDegree ≤ 2 * 2 ^ n := by
  have := natDegree_le_of_mem_degreeLT (Phi_mem_degreeLT hU hA hH z v); omega

/-- **Lemma 4.12:** if `Φ = 0` then `v = [X^{N-1}] U K_z`. -/
theorem identity_lemma {U A H : F[X]} (hA : A ∈ degreeLT F (2 ^ n)) (z : Fin n → F) {v : F}
    (h : Phi U A H z v = 0) : v = (U * kernel z).coeff (2 ^ n - 1) := by
  have hN : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h' : X * U * kernel z = assemble (2 ^ n) A v H := sub_eq_zero.1 h
  have hc := congrArg (fun P : F[X] => P.coeff (2 ^ n)) h'
  simp only at hc
  rw [coeff_assemble hA, if_neg (lt_irrefl _), if_pos rfl, mul_assoc,
    show 2 ^ n = (2 ^ n - 1) + 1 by omega, coeff_X_mul] at hc
  rw [← hc]

/-- **Lemma 4.12, "in particular":** if `U = U_f` and `Φ = 0`, then `v = f(z)`. -/
theorem identity_lemma_eval (α : Table F n) {A H : F[X]} (hA : A ∈ degreeLT F (2 ^ n))
    (z : Fin n → F) {v : F} (h : Phi (kronEnc α) A H z v = 0) : v = cEval α z := by
  rw [identity_lemma hA z h, extraction]

/-- **Remark 4.13 (why the factor `X`):** without it, a polynomial `A_0` of degree `N - 1` absorbs
any error in `v`: for every `v` there are `A_0, H_0 ∈ F[X]_{<N}` with
`U K_z = A_0 + v X^{N-1} + X^N H_0`. -/
theorem without_X_absorbs {U : F[X]} (hU : U ∈ degreeLT F (2 ^ n)) (z : Fin n → F) (v : F) :
    ∃ A0 ∈ degreeLT F (2 ^ n), ∃ H0 ∈ degreeLT F (2 ^ n),
      U * kernel z = A0 + C v * X ^ (2 ^ n - 1) + X ^ (2 ^ n) * H0 := by
  have hN : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  refine ⟨ofFn (2 ^ n) (fun j => (U * kernel z).coeff j) - C v * X ^ (2 ^ n - 1), ?_,
    ofFn (2 ^ n) (fun j => (U * kernel z).coeff (2 ^ n + j)), ofFn_mem_degreeLT _ _, ?_⟩
  · refine Submodule.sub_mem _ (ofFn_mem_degreeLT _ _) ?_
    rw [mem_degreeLT]
    refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
    exact_mod_cast (by omega : 2 ^ n - 1 < 2 ^ n)
  · ext i
    simp only [coeff_add, coeff_sub, coeff_C_mul_X_pow, coeff_X_pow_mul', coeff_ofFn]
    by_cases h1 : i < 2 ^ n
    · simp [h1, show ¬ 2 ^ n ≤ i by omega]
    · have h1' : 2 ^ n ≤ i := by omega
      by_cases h2 : i - 2 ^ n < 2 ^ n
      · simp [h1, h1', h2, show i ≠ 2 ^ n - 1 by omega]
      · simp [h1, h1', h2, show i ≠ 2 ^ n - 1 by omega]
        exact coeff_mul_kernel_eq_zero hU z (by omega)

end Identity

end KroneckerFRI
