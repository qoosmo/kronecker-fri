/-
KroneckerFRI/PublicTables.lean
§5.1 of the research note "Sumcheck-free hypercube inner products": the closed forms of the
public tables that the verifier evaluates in `O(n)` operations.

* `1(w) = 1`:        `V_1 = ∏_{k<n} (1 + X^{2^k})`                       (`kronEnc_one`);
* `G_η(w) = η^w`:     `V_{G_η}(x) = V_1(η x)`                             (`eval_kronEnc_geo`);
* `id(w) = w`:        `V_id = X · V_1'`, computed by the recursion
  `S_0 = 1, T_0 = 0, S_{k+1} = (1 + X^{2^k}) S_k, T_{k+1} = (1 + X^{2^k}) T_k + 2^k X^{2^k} S_k`
  (`recS`, `recT`, `kronEnc_id_eq_recT`), the recursion of the Rust functions `v_one`, `v_id`;
* reversed words: `V* (x) = x^{N-1} V(x⁻¹)` (`eval_revP`), used as is by the verifier.
-/
import KroneckerFRI.TableForm

set_option autoImplicit false

open Polynomial Finset KBFold

namespace KroneckerFRI

variable {F : Type*} [Field F] {n : ℕ}

/-- `x^w = ∏_k (x^{2^k} if bit k of w is set)`. -/
lemma pow_bitsToNat {R : Type*} [CommMonoid R] (x : R) (a : Fin n → Bool) :
    x ^ bitsToNat a = ∏ k : Fin n, if a k then x ^ (2 ^ (k : ℕ)) else 1 := by
  unfold bitsToNat
  rw [← prod_pow_eq_pow_sum]
  refine prod_congr rfl (fun k _ => ?_)
  split_ifs <;> simp

/-- **Product tables.** `kronEnc (∏_k φ_k(a_k)) = ∏_k (φ_k(0) + φ_k(1) X^{2^k})`. -/
theorem kronEnc_prod (φ : Fin n → Bool → F) :
    kronEnc (fun a : Fin n → Bool => ∏ k, φ k (a k)) =
      ∏ k : Fin n, (C (φ k false) + C (φ k true) * X ^ (2 ^ (k : ℕ))) := by
  classical
  have h1 : ∀ k : Fin n, C (φ k false) + C (φ k true) * X ^ (2 ^ (k : ℕ)) =
      ∑ b : Bool, C (φ k b) * (if b then (X : F[X]) ^ (2 ^ (k : ℕ)) else 1) := by
    intro k; simp [add_comm]
  simp_rw [h1]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  unfold kronEnc
  refine sum_congr rfl (fun a _ => ?_)
  rw [prod_mul_distrib, map_prod, pow_bitsToNat]

/-- **The table `1`.** `V_1 = ∏_{k<n} (1 + X^{2^k})`. -/
theorem kronEnc_one :
    kronEnc (fun _ : Fin n → Bool => (1 : F)) = ∏ k : Fin n, (1 + X ^ (2 ^ (k : ℕ))) := by
  have := kronEnc_prod (F := F) (n := n) (fun _ _ => 1)
  simp only [prod_const_one, map_one, one_mul] at this
  exact this

/-- **The table `G_η`.** `V_{G_η} = ∏_k (1 + η^{2^k} X^{2^k})`. -/
theorem kronEnc_geo (η : F) :
    kronEnc (fun a : Fin n → Bool => η ^ bitsToNat a) =
      ∏ k : Fin n, (1 + C (η ^ (2 ^ (k : ℕ))) * X ^ (2 ^ (k : ℕ))) := by
  have := kronEnc_prod (F := F) (n := n)
    (fun k b => if b then η ^ (2 ^ (k : ℕ)) else 1)
  simp only [Bool.false_eq_true, if_false, if_true, map_one] at this
  rw [← this]
  congr 1
  funext a
  rw [pow_bitsToNat]

/-- `V_{G_η}(x) = V_1(η x)`: the verifier evaluates `G_η` as `v_one(η x)`. -/
theorem eval_kronEnc_geo (η x : F) :
    (kronEnc (fun a : Fin n → Bool => η ^ bitsToNat a)).eval x =
      (kronEnc (fun _ : Fin n → Bool => (1 : F))).eval (η * x) := by
  rw [kronEnc_geo, kronEnc_one, eval_prod, eval_prod]
  refine prod_congr rfl (fun k _ => ?_)
  simp [mul_pow]

/-- `X · (X^m)' = m X^m`. -/
lemma X_mul_derivative_X_pow (m : ℕ) :
    (X : F[X]) * derivative (X ^ m) = C (m : F) * X ^ m := by
  rw [derivative_X_pow]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [mul_left_comm, ← pow_succ', Nat.sub_add_cancel hm]

/-- **The table `id`.** `V_id = X · V_1'`. -/
theorem kronEnc_id :
    kronEnc (fun a : Fin n → Bool => ((bitsToNat a : ℕ) : F)) =
      X * derivative (kronEnc (fun _ : Fin n → Bool => (1 : F))) := by
  unfold kronEnc
  rw [derivative_sum, mul_sum]
  refine sum_congr rfl (fun a _ => ?_)
  rw [map_one, one_mul, X_mul_derivative_X_pow]

/-- The recursion of the Rust functions `v_one`, `v_id`: `S_{k+1} = (1 + X^{2^k}) S_k`,
`T_{k+1} = (1 + X^{2^k}) T_k + 2^k X^{2^k} S_k`. -/
noncomputable def recS : ℕ → F[X]
  | 0 => 1
  | k + 1 => (1 + X ^ (2 ^ k)) * recS k

noncomputable def recT : ℕ → F[X]
  | 0 => 0
  | k + 1 => (1 + X ^ (2 ^ k)) * recT k + C ((2 : F) ^ k) * X ^ (2 ^ k) * recS k

lemma recS_eq (m : ℕ) : (recS m : F[X]) = ∏ k : Fin m, (1 + X ^ (2 ^ (k : ℕ))) := by
  induction m with
  | zero => simp [recS]
  | succ m ih => rw [recS, ih, Fin.prod_univ_castSucc, mul_comm]; rfl

/-- `T_m = X · S_m'` (product rule). -/
lemma recT_eq (m : ℕ) : (recT m : F[X]) = X * derivative (recS m) := by
  induction m with
  | zero => simp [recT, recS]
  | succ m ih =>
    rw [recT, recS, derivative_mul, ih, derivative_add, derivative_one, zero_add, mul_add]
    have h := X_mul_derivative_X_pow (F := F) (2 ^ m)
    have e : X * (derivative ((X : F[X]) ^ (2 ^ m)) * recS m) = C ((2 : F) ^ m) * X ^ (2 ^ m) * recS m := by
      rw [← mul_assoc, h]; push_cast; ring
    rw [e]; ring

/-- **`V_1` and `V_id` are the recursion of the verifier.** -/
theorem kronEnc_one_eq_recS : kronEnc (fun _ : Fin n → Bool => (1 : F)) = recS n := by
  rw [kronEnc_one, recS_eq]

theorem kronEnc_id_eq_recT :
    kronEnc (fun a : Fin n → Bool => ((bitsToNat a : ℕ) : F)) = recT n := by
  rw [kronEnc_id, kronEnc_one_eq_recS, recT_eq]

end KroneckerFRI
