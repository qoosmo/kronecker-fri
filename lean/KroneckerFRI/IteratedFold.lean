/-
KroneckerFRI/IteratedFold.lean
§5.1 of the paper: the iterated fold (Lemma 5.5, new in this paper), and the locality of iterated
folds used by Proposition 5.28(3).

The kernel fold of words (`wfold`), its explicit formula, linearity, locality, line form and
consistency with the polynomial fold (Definition 5.1, Lemmas 5.2, 5.3, Proposition 5.4) are those
of the KBFold formalisation (`KBFold/WordFold.lean`: `wfold_sqPt`, `wfold_add`, `wfold_smul`,
`wfold_congr`, `wfold_line`, `evenW_line`, `oddW_line`, `wfold_ev`, `pfold_mem_degreeLT`).

`χ_0(x) = 2x - 1`, `χ_1(x) = 1 - x` is `chiB x false`, `chiB x true`, and for a bit vector `c`
of length `j`, `χ_c(r) = ∏_k χ_{c_k}(r_k)` is `chiC r c`; the integer `t` of the paper is
`bitsToNat c`.
-/
import KroneckerFRI.Levels
import KroneckerFRI.Kronecker

set_option autoImplicit false

open Polynomial Finset KBFold

namespace KroneckerFRI

variable {F : Type*} [Field F]

/-- `χ_0(x) = 2x - 1`, `χ_1(x) = 1 - x`. -/
def chiB (x : F) : Bool → F
  | false => 2 * x - 1
  | true => 1 - x

/-- `χ_t(r) = ∏_{k} χ_{t_k}(r_k)` for the bit vector `t = c`. -/
def chiC {j : ℕ} (r : ℕ → F) (c : Fin j → Bool) : F := ∏ k : Fin j, chiB (r k) (c k)

/-- The coefficients of `pfold_r(U)`: `[X^i] pfold_r(U) = (2r-1)[X^{2i}]U + (1-r)[X^{2i+1}]U`. -/
lemma coeff_pfold (r : F) (U : F[X]) (i : ℕ) :
    (pfold r U).coeff i = (2 * r - 1) * U.coeff (2 * i) + (1 - r) * U.coeff (2 * i + 1) := by
  rw [pfold, coeff_add, coeff_C_mul, coeff_C_mul, coeff_evenPart, coeff_oddPart]

/-- **Lemma 5.5 (iterated fold), coefficients**, for the front-to-back iteration `pfoldSeq`. -/
theorem coeff_pfoldSeq : ∀ (j : ℕ) (r : ℕ → F) (P : F[X]) (b : ℕ),
    (pfoldSeq j r P).coeff b =
      ∑ c : Fin j → Bool, chiC r c * P.coeff (2 ^ j * b + bitsToNat c)
  | 0, r, P, b => by simp [pfoldSeq, chiC, bitsToNat]
  | j + 1, r, P, b => by
      rw [pfoldSeq, coeff_pfoldSeq j (shiftSeq r) (pfold (r 0) P) b, sum_cons_bool]
      refine sum_congr rfl (fun c _ => ?_)
      rw [coeff_pfold]
      simp only [chiC, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, bitsToNat_cons, chiB,
        shiftSeq, Fin.val_succ, Fin.val_zero, Bool.false_eq_true, if_false, if_true]
      have e1 : 2 * (2 ^ j * b + bitsToNat c) = 2 ^ (j + 1) * b + (0 + 2 * bitsToNat c) := by ring
      have e2 : 2 * (2 ^ j * b + bitsToNat c) + 1 = 2 ^ (j + 1) * b + (1 + 2 * bitsToNat c) := by
        ring
      rw [e2, e1]
      ring

/-- **Lemma 5.5 (iterated fold):** `[X^b] pfold^{(j)}_r(P) = ∑_{t < 2^j} χ_t(r) [X^{2^j b + t}] P`. -/
theorem coeff_pfoldUp (j : ℕ) (r : ℕ → F) (P : F[X]) (b : ℕ) :
    (pfoldUp r P j).coeff b = ∑ c : Fin j → Bool, chiC r c * P.coeff (2 ^ j * b + bitsToNat c) := by
  rw [pfoldUp_eq_pfoldSeq, coeff_pfoldSeq]

/-- **Lemma 5.5:** `pfold^{(j)}_r(P) ∈ F[X]_{<N_j}` for `P ∈ F[X]_{<N}`, `N = 2^{n}`, `j ≤ n`. -/
theorem pfoldUp_mem_degreeLT (r : ℕ → F) {n : ℕ} {P : F[X]} (hP : P ∈ degreeLT F (2 ^ n)) :
    ∀ j ≤ n, pfoldUp r P j ∈ degreeLT F (2 ^ (n - j))
  | 0, _ => by simpa using hP
  | j + 1, hj => by
      rw [pfoldUp]
      refine pfold_mem_degreeLT _ ?_
      rw [← pow_succ', show n - (j + 1) + 1 = n - j by omega]
      exact pfoldUp_mem_degreeLT r hP j (by omega)

/-- **Lemma 5.5, words:** if `w_0 = ev_L(P)` and `w_j = fold_{r_j}(w_{j-1})`, then
`w_j = ev_{L_j}(pfold^{(j)}_r(P))`, for a smooth domain of order `2^μ` and `j ≤ μ`. -/
theorem foldUp_ev_smooth {L : Subgroup Fˣ} {μ : ℕ} (hL : IsSmoothDomain L μ) (r : ℕ → F)
    (P : F[X]) {j : ℕ} (hj : j ≤ μ) :
    foldUp r (ev L P) j = ev (lv L j) (pfoldUp r P j) := by
  rcases Nat.eq_zero_or_pos μ with rfl | hμ
  · obtain rfl : j = 0 := by omega
    rfl
  exact foldUp_ev (two_ne_zero_of_smooth hL hμ) r P j (fun i hi => lv_neg_one_mem hL (by omega))

/-- **Locality of iterated folds** (Lemma 5.2(3) iterated; used in Definition 5.27 and
Proposition 5.28(3)): `fold^{(k)}(w)(η)` depends only on the values of `w` at the `2^k` points
`ξ` with `ξ^{2^k} = η`. -/
theorem foldUp_congr_pts {L : Subgroup Fˣ} (r : ℕ → F) {w w' : L → F} :
    ∀ (k : ℕ) (η : lv L k), (∀ ξ : L, ptAt ξ k = η → w ξ = w' ξ) →
      foldUp r w k η = foldUp r w' k η
  | 0, η, h => h η rfl
  | k + 1, η, h => by
      rw [foldUp, foldUp]
      refine wfold_congr _ (fun ζ hζ => foldUp_congr_pts r k ζ (fun ξ hξ => h ξ ?_))
      show sqPt (ptAt ξ k) = η
      rw [hξ]; exact hζ

/-- The points read: there are exactly `2^k` points `ξ ∈ L` above each `η ∈ L_k`. -/
theorem ncard_above {L : Subgroup Fˣ} {μ : ℕ} (hL : IsSmoothDomain L μ) {k : ℕ} (hk : k ≤ μ)
    (η : lv L k) : {ξ : L | ptAt ξ k = η}.ncard = 2 ^ k := by
  have := ncard_preimage_ptAt hL k hk {η}
  simpa using this

end KroneckerFRI
