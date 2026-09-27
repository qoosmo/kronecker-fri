/-
KroneckerFRI/BatchStmts.lean
§4 of the research note "Sumcheck-free hypercube inner products": one folding test for a list of
evaluations, inner products and Hadamard checks on table-form commitments (`Π_Batch`).

Modelling.
* Commitments `ws : Fin r → L → F`; statements `stmts : Fin J → BStmt F r n`.
* The words of the curve are indexed by the finite type `BWord stmts`: the commitments read
  directly (`D`), the commitments read reversed (`B`), one `w_Q` per Hadamard check, one `w_A` and
  one `h` per statement, and three quotient words per Hadamard check.  The batched word is
  `∑_s β^{e(s)} u_s` for a fixed enumeration `e` of the words.
* A deterministic prover (`BProver`) sends `w_Q^{(j)}` as a function of `γ`, `y₁^{(j)}, y₃^{(j)}`
  and `w_A^{(j)}` as functions of `(γ, θ)`, and a prover of the folding test for each
  `(γ, θ, β)`.  The challenges `γ, θ, β` are uniform in `F`.
-/
import KroneckerFRI.Hadamard

set_option autoImplicit false

open Polynomial Finset KBFold

namespace KroneckerFRI

variable {F : Type*} [Field F] {L : Subgroup Fˣ}

/-! ### Correlated agreement for a curve indexed by a finite type -/

section Index

/-- `curve_agreement` for words indexed by a finite type `W` of cardinality `t + 1`, with the
powers of `β` given by an enumeration `e : W ≃ Fin (t + 1)`. -/
theorem curve_agreement_idx [Fintype F] [DecidableEq F] {n R : ℕ} (hL : IsSmoothDomain L (n + R))
    {δ : ℚ} (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) {t : ℕ} (ht : 1 ≤ t) {W : Type*}
    [Fintype W] (e : W ≃ Fin (t + 1)) (u : W → L → F)
    (hG : t * Nat.card L <
      (goodSet n δ (fun β : F => ∑ s, β ^ ((e s : Fin (t + 1)) : ℕ) • u s)).ncard) :
    ∃ c : W → L → F, (∀ s, c s ∈ RS L (2 ^ n)) ∧ ∃ T : Set L,
      (∀ ξ ∈ T, negPt ξ ∈ T) ∧ (1 - δ) * Nat.card L ≤ T.ncard ∧ ∀ s, ∀ ξ ∈ T, u s ξ = c s ξ := by
  have hsum : ∀ β : F, (∑ s, β ^ ((e s : Fin (t + 1)) : ℕ) • u s) =
      ∑ i : Fin (t + 1), β ^ (i : ℕ) • u (e.symm i) := by
    intro β
    rw [← Equiv.sum_comp e.symm]
    simp
  have hG' : t * Nat.card L < {β : F | ∃ c ∈ RS L (2 ^ n), ∃ T : Set L, (∀ ξ ∈ T, negPt ξ ∈ T) ∧
      (1 - δ) * Nat.card L ≤ T.ncard ∧
        ∀ ξ ∈ T, (∑ i : Fin (t + 1), β ^ (i : ℕ) • (u ∘ e.symm) i) ξ = c ξ}.ncard := by
    refine lt_of_lt_of_le hG (le_of_eq ?_)
    congr 1
    ext β
    simp only [goodSet, Set.mem_setOf_eq, hsum, Function.comp]
  obtain ⟨c, hc, T, hT1, hT2, hT3⟩ := curve_agreement hL hδ0 hδ ht (u ∘ e.symm) hG'
  refine ⟨fun s => c (e s), fun s => hc _, T, hT1, hT2, fun s ξ hξ => ?_⟩
  have := hT3 (e s) ξ hξ
  simpa using this

end Index

/-! ### Statements -/

section Statements

variable (F) in
/-- A statement on the commitments `w_1, …, w_r`. -/
inductive BStmt (r n : ℕ)
  | eval (i : Fin r) (z : Fin n → F) (v : F)
  | ip (i i' : Fin r) (S : F)
  | had (i i' k : Fin r)

variable {r n : ℕ}

namespace BStmt

/-- The indices read directly. -/
def direct : BStmt F r n → Finset (Fin r)
  | eval i _ _ => {i}
  | ip i _ _ => {i}
  | had i _ k => {i, k}

/-- The indices read reversed. -/
def rev : BStmt F r n → Finset (Fin r)
  | eval _ _ _ => ∅
  | ip _ i' _ => {i'}
  | had _ i' _ => {i'}

def isHad : BStmt F r n → Bool
  | had _ _ _ => true
  | _ => false

/-- The statement holds for the tables `fs`. -/
def Holds (fs : Fin r → Table F n) : BStmt F r n → Prop
  | eval i z v => mle (fs i) z = v
  | ip i i' S => ∑ w, fs i w * fs i' w = S
  | had i i' k => ∀ w, fs i w * fs i' w = fs k w

end BStmt

variable {J : ℕ}

/-- `D`: the commitments read directly. -/
def Dset (stmts : Fin J → BStmt F r n) : Finset (Fin r) := univ.biUnion fun j => (stmts j).direct
/-- `B`: the commitments read reversed. -/
def Bset (stmts : Fin J → BStmt F r n) : Finset (Fin r) := univ.biUnion fun j => (stmts j).rev
/-- The positions of the Hadamard checks. -/
abbrev Hpos (stmts : Fin J → BStmt F r n) := {j : Fin J // (stmts j).isHad = true}

/-- The index type of the words:
`D ⊕ B ⊕ ℋ (w_Q) ⊕ [J] (w_A) ⊕ [J] (h) ⊕ ℋ × [3] (quotient words)`. -/
abbrev BWord (stmts : Fin J → BStmt F r n) :=
  {i // i ∈ Dset stmts} ⊕ {i // i ∈ Bset stmts} ⊕ Hpos stmts ⊕ Fin J ⊕ Fin J ⊕ (Hpos stmts × Fin 3)

omit [Field F] in
lemma card_BWord (stmts : Fin J → BStmt F r n) :
    Fintype.card (BWord stmts) =
      (Dset stmts).card + (Bset stmts).card + 2 * J + 4 * Fintype.card (Hpos stmts) := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  ring

/-- **The relation `R^δ_Batch`.** -/
def RelBatchS (δ : ℚ) (ws : Fin r → L → F) (stmts : Fin J → BStmt F r n)
    (fs : Fin r → Table F n) : Prop :=
  (∀ i ∈ Dset stmts ∪ Bset stmts, fibDist (ws i) (encode L (fs i)) ≤ δ) ∧
    ∀ j, (stmts j).Holds fs

omit [Field F] in
lemma mem_Dset {stmts : Fin J → BStmt F r n} {j : Fin J} {i : Fin r}
    (h : i ∈ (stmts j).direct) : i ∈ Dset stmts :=
  mem_biUnion.2 ⟨j, mem_univ _, h⟩

omit [Field F] in
lemma mem_Bset {stmts : Fin J → BStmt F r n} {j : Fin J} {i : Fin r}
    (h : i ∈ (stmts j).rev) : i ∈ Bset stmts :=
  mem_biUnion.2 ⟨j, mem_univ _, h⟩

end Statements

/-! ### The words of `Π_Batch` -/

section Words

variable {r n J : ℕ}

/-- The general virtual word `h(ξ) = (ξ U(ξ) K(ξ) - A(ξ) - v ξ^N) / ξ^{N+1}`. -/
noncomputable def virtG (n : ℕ) (U K A : L → F) (v : F) : L → F := fun ξ =>
  (xv' ξ * U ξ * K ξ - A ξ - v * xv' ξ ^ (2 ^ n)) / xv' ξ ^ (2 ^ n + 1)

theorem virtG_identity (U K A : L → F) (v : F) (ξ : L) :
    xv' ξ * U ξ * K ξ = A ξ + v * xv' ξ ^ (2 ^ n) + xv' ξ ^ (2 ^ n + 1) * virtG n U K A v ξ := by
  have h := pow_ne_zero (2 ^ n + 1) (xv'_ne_zero ξ)
  rw [virtG, mul_div_cancel₀ _ h]; ring

/-- The honest virtual word is `ev_L(H)`. -/
theorem virtG_honest {U K : F[X]} (hU : U ∈ degreeLT F (2 ^ n)) (hK : K ∈ degreeLT F (2 ^ n)) :
    virtG n (ev L U) (ev L K) (ev L (openAG (2 ^ n) U K)) ((U * K).coeff (2 ^ n - 1)) =
      ev L (openHG (2 ^ n) U K) := by
  funext ξ
  have hx := pow_ne_zero (2 ^ n + 1) (xv'_ne_zero ξ)
  have hs := congrArg (fun P : F[X] => P.eval (xv' ξ)) (splitG_eq Nat.one_le_two_pow hU hK)
  simp only [assemble, eval_add, eval_mul, eval_X, eval_C, eval_pow] at hs
  rw [virtG, div_eq_iff hx]
  simp only [ev]
  rw [hs]; ring

/-- On a set of more than `2N` points where `U, K, A, h` agree with polynomials of degree `< N`,
`v = [X^{N-1}] U K` (Lemma gen-identity). -/
theorem virtG_value [Finite L] {U K A : L → F} {v : F} {PU PK PA PH : F[X]}
    (hU : PU ∈ degreeLT F (2 ^ n)) (hK : PK ∈ degreeLT F (2 ^ n)) (hA : PA ∈ degreeLT F (2 ^ n))
    (hH : PH ∈ degreeLT F (2 ^ n)) (T : Set L) (hT : 2 * 2 ^ n < T.ncard)
    (e : ∀ ξ ∈ T, U ξ = PU.eval (xv' ξ) ∧ K ξ = PK.eval (xv' ξ) ∧ A ξ = PA.eval (xv' ξ) ∧
      virtG n U K A v ξ = PH.eval (xv' ξ)) :
    v = (PU * PK).coeff (2 ^ n - 1) := by
  classical
  letI : Fintype T := Fintype.ofFinite T
  refine identityG Nat.one_le_two_pow hA (eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (PhiG (2 ^ n) PU PK PA PH v) (f := fun i : T => xv' (i : L)) ?_ ?_ ?_)
  · intro x y hxy
    exact Subtype.ext (Subtype.ext (Units.ext hxy))
  · intro i
    obtain ⟨e1, e2, e3, e4⟩ := e i i.2
    have hid := virtG_identity (n := n) U K A v (i : L)
    simp only [PhiG, assemble, eval_sub, eval_add, eval_mul, eval_X, eval_C, eval_pow]
    rw [← e1, ← e2, ← e3, ← e4, hid]; ring
  · rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]
    exact lt_of_le_of_lt (natDegree_PhiG_le hU hK hA hH v) hT

variable (n) in
/-- The words `U_j`, `K_j` and the value `v_j` of a statement (`wQ` is the prover's `w_Q^{(j)}`,
`y3` its `y₃^{(j)}`). -/
noncomputable def Uw (ws : Fin r → L → F) (wQ : L → F) : BStmt F r n → L → F
  | .eval i _ _ => ws i
  | .ip i _ _ => ws i
  | .had _ _ _ => wQ

noncomputable def Kw (ws : Fin r → L → F) : BStmt F r n → L → F
  | .eval _ z _ => ev L (evalKer z)
  | .ip _ i' _ => wrev (2 ^ n) (ws i')
  | .had _ i' _ => wrev (2 ^ n) (ws i')

def vS (y3 : F) : BStmt F r n → F
  | .eval _ _ v => v
  | .ip _ _ S => S
  | .had _ _ _ => y3

/-- The three quotient words of a Hadamard check. -/
noncomputable def quotW (ws : Fin r → L → F) (wQ : L → F) (y1 y3 γ θ : F) :
    BStmt F r n → Fin 3 → L → F
  | .had i _ k => ![qword (ws i) y1 (γ * θ), qword wQ y1 θ, qword (ws k) y3 γ]
  | _ => fun _ _ => 0

/-- The words of `Π_Batch`, for the prover's messages `wQ, y1, y3, wA` at `(γ, θ)`. -/
noncomputable def bwords (ws : Fin r → L → F) (stmts : Fin J → BStmt F r n) (wQ : Fin J → L → F)
    (y1 y3 : Fin J → F) (wA : Fin J → L → F) (γ θ : F) : BWord stmts → L → F :=
  Sum.elim (fun d => ws d.1) <| Sum.elim (fun b => wrev (2 ^ n) (ws b.1)) <|
    Sum.elim (fun h => wQ h.1) <| Sum.elim (fun j => wA j) <|
      Sum.elim (fun j => virtG n (Uw n ws (wQ j) (stmts j)) (Kw ws (stmts j)) (wA j)
        (vS (y3 j) (stmts j))) (fun p => quotW ws (wQ p.1.1) (y1 p.1.1) (y3 p.1.1) γ θ
          (stmts p.1.1) p.2)

end Words

/-! ### Lemma batchT -/

section Batching

variable {r n J : ℕ}

/-- `t` for a list of statements: the number of words minus one. -/
def tB (stmts : Fin J → BStmt F r n) : ℕ := Fintype.card (BWord stmts) - 1

omit [Field F] in
lemma card_BWord_eq (stmts : Fin J → BStmt F r n) (hJ : 1 ≤ J) :
    Fintype.card (BWord stmts) = tB stmts + 1 := by
  have := card_BWord stmts
  unfold tB; omega

omit [Field F] in
lemma one_le_tB (stmts : Fin J → BStmt F r n) (hJ : 1 ≤ J) : 1 ≤ tB stmts := by
  have := card_BWord stmts
  unfold tB; omega

/-- The fixed enumeration of the words. -/
noncomputable def benum (stmts : Fin J → BStmt F r n) (hJ : 1 ≤ J) :
    BWord stmts ≃ Fin (tB stmts + 1) :=
  Fintype.equivFinOfCardEq (card_BWord_eq stmts hJ)

/-- The batched word `w_0 = ∑_s β^{e(s)} u_s`. -/
noncomputable def wbatB (ws : Fin r → L → F) (stmts : Fin J → BStmt F r n) (hJ : 1 ≤ J)
    (wQ : Fin J → L → F) (y1 y3 : Fin J → F) (wA : Fin J → L → F) (γ θ β : F) : L → F :=
  ∑ s, β ^ ((benum stmts hJ s : Fin (tB stmts + 1)) : ℕ) •
    bwords (n := n) ws stmts wQ y1 y3 wA γ θ s

/-- **Lemma batchT.** If more than `tM` challenges `β` are good, there are tables `fs` and
polynomials `Q̂_j` such that every commitment read is within fibre distance `δ` of `Enc^T(f_i)`,
every `w_Q^{(j)}` (`j` a Hadamard check) is within `δ` of `ev(Q̂_j)`, every evaluation and inner
product statement holds, and every Hadamard check satisfies the two equalities of (2). -/
theorem batching_B [Fintype F] [DecidableEq F] {R : ℕ} (hL : IsSmoothDomain L (n + R))
    (hR : 2 ≤ R) {δ : ℚ} (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (ws : Fin r → L → F) (stmts : Fin J → BStmt F r n) (hJ : 1 ≤ J) (wQ : Fin J → L → F)
    (y1 y3 : Fin J → F) (wA : Fin J → L → F) (γ θ : F)
    (hG : tB stmts * Nat.card L <
      (goodSet n δ (fun β => wbatB ws stmts hJ wQ y1 y3 wA γ θ β)).ncard) :
    ∃ fs : Fin r → Table F n, ∃ Qh : Fin J → F[X],
      (∀ i ∈ Dset stmts ∪ Bset stmts, fibDist (ws i) (encode L (fs i)) ≤ δ) ∧
      (∀ j, (stmts j).isHad = true → Qh j ∈ degreeLT F (2 ^ n) ∧
        fibDist (wQ j) (ev L (Qh j)) ≤ δ) ∧
      (∀ j, (stmts j).isHad = false → (stmts j).Holds fs) ∧
      (∀ j i i' k, stmts j = .had i i' k →
        (kronEnc (fs i)).eval (γ * θ) = y1 j ∧ (Qh j).eval θ = y1 j ∧
        (kronEnc (fs k)).eval γ = y3 j ∧
        y3 j = (Qh j * revP (2 ^ n) (kronEnc (fs i'))).coeff (2 ^ n - 1)) := by
  classical
  haveI := hL.finite
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
  set u := bwords (n := n) ws stmts wQ y1 y3 wA γ θ
  obtain ⟨c, hc, T, hTneg, hTcard, hTu⟩ :=
    curve_agreement_idx hL hδ0 hδ (one_le_tB stmts hJ) (benum stmts hJ) u hG
  set P : BWord stmts → F[X] := fun s => polyOf (c s)
  have hP : ∀ s, P s ∈ degreeLT F (2 ^ n) := fun s => (polyOf_spec hNM (hc s)).1
  have hev : ∀ s, ev L (P s) = c s := fun s => (polyOf_spec hNM (hc s)).2
  have hv : ∀ s, ∀ ξ ∈ T, u s ξ = (P s).eval (xv' ξ) := fun s ξ hξ => by
    rw [hTu s ξ hξ, ← hev s]; rfl
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
  -- the words, by kind
  let sD : {i // i ∈ Dset stmts} → BWord stmts := Sum.inl
  let sB : {i // i ∈ Bset stmts} → BWord stmts := fun b => Sum.inr (Sum.inl b)
  let sQ : Hpos stmts → BWord stmts := fun h => Sum.inr (Sum.inr (Sum.inl h))
  let sA : Fin J → BWord stmts := fun j => Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))
  let sH : Fin J → BWord stmts := fun j => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))
  let sq : Hpos stmts → Fin 3 → BWord stmts :=
    fun h q => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (h, q)))))
  -- tables from the direct words
  have hdist_rev : ∀ b : {i // i ∈ Bset stmts},
      fibDist (ws b.1) (encode L (kronCoeffs n (revP (2 ^ n) (P (sB b))))) ≤ δ := by
    intro b
    refine fibDist_le_of_closed hneg h2 (invPt '' T) (inv_image_closed hneg hTneg)
      (by rw [ncard_inv_image]; exact hTcard) ?_
    rintro _ ⟨ξ, hξ, rfl⟩
    have h1 : wrev (2 ^ n) (ws b.1) ξ =
        wrev (2 ^ n) (encode L (kronCoeffs n (revP (2 ^ n) (P (sB b))))) ξ := by
      rw [encode, kronEnc_kronCoeffs (revP_mem _ _), wrev_ev (revP_mem _ _), revP_revP (hP _)]
      exact hv (sB b) ξ hξ
    exact (wrev_eq_iff _ _ _ ξ).1 h1
  have hdist_dir : ∀ d : {i // i ∈ Dset stmts},
      fibDist (ws d.1) (encode L (kronCoeffs n (P (sD d)))) ≤ δ := by
    intro d
    refine fibDist_le_of_closed hneg h2 T hTneg hTcard (fun ξ hξ => ?_)
    rw [encode, kronEnc_kronCoeffs (hP _)]
    exact hv (sD d) ξ hξ
  let fs : Fin r → Table F n := fun i =>
    if hi : i ∈ Dset stmts then kronCoeffs n (P (sD ⟨i, hi⟩))
    else if hb : i ∈ Bset stmts then kronCoeffs n (revP (2 ^ n) (P (sB ⟨i, hb⟩))) else 0
  have hfsD : ∀ (i : Fin r) (hi : i ∈ Dset stmts), kronEnc (fs i) = P (sD ⟨i, hi⟩) := by
    intro i hi
    simp only [fs, dif_pos hi]
    exact kronEnc_kronCoeffs (hP _)
  have hfsB : ∀ (i : Fin r) (hb : i ∈ Bset stmts), kronEnc (fs i) = revP (2 ^ n) (P (sB ⟨i, hb⟩)) := by
    intro i hb
    by_cases hi : i ∈ Dset stmts
    · have := encode_fib_unique hNM hneg h2 hδ' (ws i) (hdist_dir ⟨i, hi⟩) (hdist_rev ⟨i, hb⟩)
      simp only [fs, dif_pos hi]
      rw [this]; exact kronEnc_kronCoeffs (revP_mem _ _)
    · simp only [fs, dif_neg hi, dif_pos hb]
      exact kronEnc_kronCoeffs (revP_mem _ _)
  have hdist : ∀ i ∈ Dset stmts ∪ Bset stmts, fibDist (ws i) (encode L (fs i)) ≤ δ := by
    intro i hi
    by_cases hd : i ∈ Dset stmts
    · have := hdist_dir ⟨i, hd⟩
      simp only [fs, dif_pos hd]; exact this
    · have hb : i ∈ Bset stmts := by simpa [hd] using hi
      have := hdist_rev ⟨i, hb⟩
      simp only [fs, dif_neg hd, dif_pos hb]; exact this
  -- the polynomial of `w_Q^{(j)}`
  let Qh : Fin J → F[X] := fun j => if h : (stmts j).isHad = true then P (sQ ⟨j, h⟩) else 0
  -- the identity of `h_j`: `v_j = [X^{N-1}] U_j K_j`
  have hval : ∀ j, ∀ PU PK : F[X], PU ∈ degreeLT F (2 ^ n) → PK ∈ degreeLT F (2 ^ n) →
      (∀ ξ ∈ T, Uw n ws (wQ j) (stmts j) ξ = PU.eval (xv' ξ) ∧
        Kw ws (stmts j) ξ = PK.eval (xv' ξ)) →
      vS (y3 j) (stmts j) = (PU * PK).coeff (2 ^ n - 1) := by
    intro j PU PK hU hK hUK
    refine virtG_value hU hK (hP (sA j)) (hP (sH j)) T hTbig (fun ξ hξ => ⟨(hUK ξ hξ).1,
      (hUK ξ hξ).2, hv (sA j) ξ hξ, hv (sH j) ξ hξ⟩)
  have hdirT : ∀ (i : Fin r) (hi : i ∈ Dset stmts), ∀ ξ ∈ T,
      ws i ξ = (kronEnc (fs i)).eval (xv' ξ) := by
    intro i hi ξ hξ; rw [hfsD i hi]; exact hv (sD ⟨i, hi⟩) ξ hξ
  have hrevT : ∀ (i : Fin r) (hb : i ∈ Bset stmts), ∀ ξ ∈ T,
      wrev (2 ^ n) (ws i) ξ = (revP (2 ^ n) (kronEnc (fs i))).eval (xv' ξ) := by
    intro i hb ξ hξ; rw [hfsB i hb, revP_revP (hP _)]; exact hv (sB ⟨i, hb⟩) ξ hξ
  refine ⟨fs, Qh, hdist, ?_, ?_, ?_⟩
  · intro j hj
    simp only [Qh, dif_pos hj]
    refine ⟨hP _, fibDist_le_of_closed hneg h2 T hTneg hTcard (fun ξ hξ => ?_)⟩
    rw [hev]; exact hTu (sQ ⟨j, hj⟩) ξ hξ
  · intro j hj
    cases hs : stmts j with
    | eval i z v =>
      have hi : i ∈ Dset stmts := mem_Dset (j := j) (by rw [hs]; simp [BStmt.direct])
      have := hval j (kronEnc (fs i)) (evalKer z) (kronEnc_mem_degreeLT _) (evalKer_mem z)
        (fun ξ hξ => by
          rw [hs]
          exact ⟨hdirT i hi ξ hξ, rfl⟩)
      rw [hs] at this
      show mle (fs i) z = v
      rw [eval_table]; exact this.symm
    | ip i i' S =>
      have hi : i ∈ Dset stmts := mem_Dset (j := j) (by rw [hs]; simp [BStmt.direct])
      have hi' : i' ∈ Bset stmts := mem_Bset (j := j) (by rw [hs]; simp [BStmt.rev])
      have := hval j (kronEnc (fs i)) (revP (2 ^ n) (kronEnc (fs i'))) (kronEnc_mem_degreeLT _)
        (revP_mem _ _) (fun ξ hξ => by
          rw [hs]
          exact ⟨hdirT i hi ξ hξ, hrevT i' hi' ξ hξ⟩)
      rw [hs] at this
      show ∑ w, fs i w * fs i' w = S
      rw [inner_product]; exact this.symm
    | had i i' k => rw [hs] at hj; simp [BStmt.isHad] at hj
  · intro j i i' k hs
    have hj : (stmts j).isHad = true := by rw [hs]; rfl
    have hi : i ∈ Dset stmts := mem_Dset (j := j) (by rw [hs]; simp [BStmt.direct])
    have hk : k ∈ Dset stmts := mem_Dset (j := j) (by rw [hs]; simp [BStmt.direct])
    have hi' : i' ∈ Bset stmts := mem_Bset (j := j) (by rw [hs]; simp [BStmt.rev])
    have hQ : ∀ ξ ∈ T, wQ j ξ = (Qh j).eval (xv' ξ) := by
      intro ξ hξ
      simp only [Qh, dif_pos hj]
      exact hv (sQ ⟨j, hj⟩) ξ hξ
    have hQmem : Qh j ∈ degreeLT F (2 ^ n) := by simp only [Qh, dif_pos hj]; exact hP _
    have hq : ∀ q : Fin 3, ∀ ξ ∈ T, quotW ws (wQ j) (y1 j) (y3 j) γ θ (stmts j) q ξ =
        (P (sq ⟨j, hj⟩ q)).eval (xv' ξ) := fun q ξ hξ => hv (sq ⟨j, hj⟩ q) ξ hξ
    rw [hs] at hq
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact deep_step (kronEnc_mem_degreeLT _) (hP (sq ⟨j, hj⟩ 0)) T hTN (hdirT i hi)
        (fun ξ hξ => hq 0 ξ hξ)
    · exact deep_step hQmem (hP (sq ⟨j, hj⟩ 1)) T hTN hQ (fun ξ hξ => hq 1 ξ hξ)
    · exact deep_step (kronEnc_mem_degreeLT _) (hP (sq ⟨j, hj⟩ 2)) T hTN (hdirT k hk)
        (fun ξ hξ => hq 2 ξ hξ)
    · have := hval j (Qh j) (revP (2 ^ n) (kronEnc (fs i'))) hQmem (revP_mem _ _)
        (fun ξ hξ => by
          rw [hs]
          exact ⟨hQ ξ hξ, hrevT i' hi' ξ hξ⟩)
      rw [hs] at this
      exact this

end Batching

/-! ### The prover and the Hadamard bad pairs -/

section Sound

variable {r n J : ℕ}

/-- A deterministic prover of `Π_Batch`. -/
structure BProver (F : Type*) [Field F] (L : Subgroup Fˣ) (J : ℕ) where
  wQ : F → Fin J → L → F
  y1 : F → F → Fin J → F
  y3 : F → F → Fin J → F
  wA : F → F → Fin J → L → F
  ft : F → F → F → FTProver F L

namespace BProver

variable (P : BProver F L J)

def Causal : Prop := ∀ γ θ β, (P.ft γ θ β).Causal
def DegOK (m : ℕ) : Prop := ∀ γ θ β, (P.ft γ θ β).DegOK m

noncomputable def w0 (ws : Fin r → L → F) (stmts : Fin J → BStmt F r n) (hJ : 1 ≤ J) (γ θ : F) :
    F → L → F := fun β =>
  wbatB ws stmts hJ (P.wQ γ) (P.y1 γ θ) (P.y3 γ θ) (P.wA γ θ) γ θ β

def Accepts (ℓ : ℕ) {κ : ℕ} (ws : Fin r → L → F) (stmts : Fin J → BStmt F r n) (hJ : 1 ≤ J)
    (γ θ β : F) (r' : ℕ → F) (ξ : Fin κ → L) : Prop :=
  (P.ft γ θ β).Accepts ℓ (P.w0 ws stmts hJ γ θ β) r' ξ

noncomputable def accProb [Fintype F] [Fintype L] (ℓ κ : ℕ) (ws : Fin r → L → F)
    (stmts : Fin J → BStmt F r n) (hJ : 1 ≤ J) : ℚ :=
  prob (fun ω : (F × F) × ((F × (Fin ℓ → F)) × (Fin κ → L)) =>
    P.Accepts ℓ ws stmts hJ ω.1.1 ω.1.2 ω.2.1.1 (extR ω.2.1.2) ω.2.2)

end BProver

/-- The bad pairs `(γ, θ)` of one false Hadamard check `â ∘ b̂ ≠ ĉ` have probability at most
`2(N-1)/|F|` (proof of Theorem had, for one check). -/
theorem prob_bad_had [Fintype F] [DecidableEq F] {R : ℕ} (hL : IsSmoothDomain L (n + R))
    (hR : 2 ≤ R) {δ : ℚ} (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (wQ : F → L → F) (ah bh ch : Table F n)
    (hne : ¬ ∀ w, ah w * bh w = ch w) (Bad : F × F → Prop)
    (hBad : ∀ p, Bad p → ∃ Qh ∈ degreeLT F (2 ^ n), fibDist (wQ p.1) (ev L Qh) ≤ δ ∧
      Qh.eval p.2 = (kronEnc ah).eval (p.1 * p.2) ∧
      (kronEnc ch).eval p.1 = (Qh * revP (2 ^ n) (kronEnc bh)).coeff (2 ^ n - 1)) :
    prob Bad ≤ 2 * ((2 ^ n - 1 : ℕ) : ℚ) / Fintype.card F := by
  classical
  haveI := hL.finite
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
  set Z2 : F → Set F := fun γ => {θ | ∃ Qh ∈ degreeLT F (2 ^ n), fibDist (wQ γ) (ev L Qh) ≤ δ ∧
    Qh ≠ kronEnc (gscale γ ah) ∧ Qh.eval θ = (kronEnc ah).eval (γ * θ)}
  have hZ2 : ∀ γ, (Z2 γ).ncard ≤ 2 ^ n - 1 := by
    intro γ
    by_cases hZ : (Z2 γ).Nonempty
    · obtain ⟨θ0, Q0, hQ0, hd0, hn0, -⟩ := hZ
      have hsub : Z2 γ ⊆ {θ | (Q0 - kronEnc (gscale γ ah)).eval θ = 0} := by
        rintro θ ⟨Q1, hQ1, hd1, -, he1⟩
        have hQeq : Q1 = Q0 := by
          have := fib_unique hneg h2 hδ' (wQ γ) (ev_mem_RS hQ1) (ev_mem_RS hQ0) hd1 hd0
          exact ev_injOn hNM hQ1 hQ0 this
        simp only [Set.mem_setOf_eq, eval_sub, eval_gscale]
        rw [← hQeq, he1, sub_self]
      refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (ncard_roots_le ?_ (sub_ne_zero.2 hn0))
      exact Submodule.sub_mem _ hQ0 (kronEnc_mem_degreeLT _)
    · rw [Set.not_nonempty_iff_eq_empty.1 hZ, Set.ncard_empty]; exact Nat.zero_le _
  have hB : ∀ p, Bad p → p.1 ∈ Z1 ∨ p.2 ∈ Z2 p.1 := by
    intro p hp
    obtain ⟨Qh, hQh, hdQ, e1, e2⟩ := hBad p hp
    by_cases hQ : Qh = kronEnc (gscale p.1 ah)
    · left
      show D.eval p.1 = 0
      have hw := weighted_inner_product p.1 ah bh
      rw [← hQ, ← e2] at hw
      have hcv : (kronEnc ch).eval p.1 = ∑ w, p.1 ^ bitsToNat w * ch w := by
        rw [eval_kronEnc]; exact sum_congr rfl (fun w _ => by ring)
      simp only [D, eval_kronEnc, sub_mul, sum_sub_distrib]
      rw [sub_eq_zero]
      calc (∑ x, ah x * bh x * p.1 ^ bitsToNat x) = ∑ w, p.1 ^ bitsToNat w * (ah w * bh w) :=
            sum_congr rfl (fun w _ => by ring)
        _ = ∑ w, p.1 ^ bitsToNat w * ch w := by rw [hw, hcv]
        _ = ∑ x, ch x * p.1 ^ bitsToNat x := sum_congr rfl (fun w _ => by ring)
    · right
      exact ⟨Qh, hQh, hdQ, hQ, e1⟩
  calc prob Bad ≤ prob (fun p : F × F => p.1 ∈ Z1 ∨ p.2 ∈ Z2 p.1) := prob_mono hB
    _ ≤ prob (fun p : F × F => p.1 ∈ Z1) + prob (fun p : F × F => p.2 ∈ Z2 p.1) := prob_or_le _ _
    _ ≤ ((2 ^ n - 1 : ℕ) : ℚ) / Fintype.card F + ((2 ^ n - 1 : ℕ) : ℚ) / Fintype.card F := by
        gcongr
        · rw [prob_fst (fun γ : F => γ ∈ Z1)]
          exact prob_set_le Z1 hZ1
        · rw [prob_prod_eq_expect (fun γ θ => θ ∈ Z2 γ)]
          exact expect_le_of_le _ _ (fun γ => prob_set_le (Z2 γ) (hZ2 γ))
    _ = _ := by ring

/-- The pairs `(γ, θ)` for which more than `tM` challenges `β` are good have probability at most
`2(N-1)/|F|` when the instance has no witness (proof of Theorem batch). -/
theorem prob_bad_B [Fintype F] [DecidableEq F] {m ℓ R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hR : 2 ≤ R) {δ : ℚ} (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : BProver F L J)
    (ws : Fin r → L → F) (stmts : Fin J → BStmt F r (m + ℓ)) (hJ : 1 ≤ J)
    (hnw : ∀ fs, ¬ RelBatchS δ ws stmts fs) :
    prob (fun p : F × F => tB stmts * Nat.card L <
        (goodSet (m + ℓ) δ (P.w0 ws stmts hJ p.1 p.2)).ncard) ≤
      2 * ((2 ^ (m + ℓ) - 1 : ℕ) : ℚ) / Fintype.card F := by
  classical
  haveI := hL.finite
  have hcardL : Nat.card L = 2 ^ ((m + ℓ) + R) := hL
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
  have hbound0 : (0 : ℚ) ≤ 2 * ((2 ^ (m + ℓ) - 1 : ℕ) : ℚ) / Fintype.card F := by positivity
  set U := Dset stmts ∪ Bset stmts
  set Bad : F × F → Prop := fun p =>
    tB stmts * Nat.card L < (goodSet (m + ℓ) δ (P.w0 ws stmts hJ p.1 p.2)).ncard
  have hbatch : ∀ p, Bad p → _ := fun p hp =>
    batching_B (n := m + ℓ) (R := R) hL hR hδ0 hδ ws stmts hJ (P.wQ p.1) (P.y1 p.1 p.2)
      (P.y3 p.1 p.2) (P.wA p.1 p.2) p.1 p.2 hp
  by_cases hex : ∀ i ∈ U, ∃ f : Table F (m + ℓ), fibDist (ws i) (encode L f) ≤ δ
  swap
  · refine (prob_mono (F := fun _ => False) (fun p hp => ?_)).trans ?_
    · obtain ⟨fs, -, hd, -⟩ := hbatch p hp
      exact hex (fun i hi => ⟨fs i, hd i hi⟩)
    · rw [prob_false]; exact hbound0
  let fs0 : Fin r → Table F (m + ℓ) := fun i => if h : i ∈ U then Classical.choose (hex i h) else 0
  have hfs0 : ∀ i ∈ U, fibDist (ws i) (encode L (fs0 i)) ≤ δ := by
    intro i hi
    simp only [fs0, dif_pos hi]
    exact Classical.choose_spec (hex i hi)
  have huniq : ∀ fs : Fin r → Table F (m + ℓ), (∀ i ∈ U, fibDist (ws i) (encode L (fs i)) ≤ δ) →
      ∀ i ∈ U, fs i = fs0 i := fun fs hd i hi =>
    encode_fib_unique hNM hneg h2 hδ' (ws i) (hd i hi) (hfs0 i hi)
  obtain ⟨js, hjs⟩ : ∃ j, ¬ (stmts j).Holds fs0 := by
    by_contra h
    push_neg at h
    exact hnw fs0 ⟨hfs0, h⟩
  have hD : ∀ {i}, i ∈ (stmts js).direct → i ∈ U := fun h =>
    mem_union_left _ (mem_Dset (j := js) h)
  have hBm : ∀ {i}, i ∈ (stmts js).rev → i ∈ U := fun h =>
    mem_union_right _ (mem_Bset (j := js) h)
  -- an evaluation or inner-product statement is false: no pair is bad
  have hnothad : (stmts js).isHad = false → prob Bad ≤ 2 * ((2 ^ (m + ℓ) - 1 : ℕ) : ℚ) / Fintype.card F := by
    intro hh
    refine (prob_mono (F := fun _ => False) (fun p hp => ?_)).trans ?_
    · obtain ⟨fs, -, hd, -, hholds, -⟩ := hbatch p hp
      have hh' := hholds js hh
      apply hjs
      revert hh hh' hD hBm
      cases stmts js with
      | eval i z v =>
        intro hD _ _ hh'
        have e := huniq fs hd i (hD (by simp [BStmt.direct]))
        simpa [BStmt.Holds, e] using hh'
      | ip i i' S =>
        intro hD hBm _ hh'
        have e := huniq fs hd i (hD (by simp [BStmt.direct]))
        have e' := huniq fs hd i' (hBm (by simp [BStmt.rev]))
        simpa [BStmt.Holds, e, e'] using hh'
      | had i i' k => intro _ _ hh _; simp [BStmt.isHad] at hh
    · rw [prob_false]; exact hbound0
  cases hs : stmts js with
  | eval i z v => exact hnothad (by rw [hs]; rfl)
  | ip i i' S => exact hnothad (by rw [hs]; rfl)
  | had i i' k =>
    have hj : (stmts js).isHad = true := by rw [hs]; rfl
    have hiU : i ∈ U := hD (by rw [hs]; simp [BStmt.direct])
    have hkU : k ∈ U := hD (by rw [hs]; simp [BStmt.direct])
    have hi'U : i' ∈ U := hBm (by rw [hs]; simp [BStmt.rev])
    have hne : ¬ ∀ w, fs0 i w * fs0 i' w = fs0 k w := by
      intro h; apply hjs; rw [hs]; exact h
    refine prob_bad_had (n := m + ℓ) (hL := hL) hR hδ (fun γ => P.wQ γ js) (fs0 i) (fs0 i') (fs0 k)
      hne Bad (fun p hp => ?_)
    obtain ⟨fs, Qh, hd, hQ, -, hhad⟩ := hbatch p hp
    obtain ⟨e1, e2, e3, e4⟩ := hhad js i i' k hs
    obtain ⟨hQm, hQd⟩ := hQ js hj
    rw [huniq fs hd i hiU] at e1
    rw [huniq fs hd k hkU] at e3
    rw [huniq fs hd i' hi'U] at e4
    exact ⟨Qh js, hQm, hQd, e2.trans e1.symm, e3.trans e4⟩

/-- **Theorem batch (soundness of `Π_Batch`).** If `((w_i)_i, Σ)` has no witness in `R^δ_Batch`,
every causal prover whose final polynomials lie in `F[X]_{<N_ℓ}` is accepted with probability at
most `2(N-1)/|F| + tM/|F| + ε_fold + (1-δ)^κ`. -/
theorem soundness_B [Fintype F] [DecidableEq F] [Fintype L] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : BProver F L J) (hC : P.Causal) (hdeg : P.DegOK m)
    (κ : ℕ) (ws : Fin r → L → F) (stmts : Fin J → BStmt F r (m + ℓ)) (hJ : 1 ≤ J)
    (hnw : ∀ fs, ¬ RelBatchS δ ws stmts fs) :
    P.accProb ℓ κ ws stmts hJ ≤
      2 * ((2 ^ (m + ℓ) - 1 : ℕ) : ℚ) / Fintype.card F +
        tB stmts * 2 ^ (m + ℓ + R) / Fintype.card F + epsFold F (m + ℓ + R) ℓ + (1 - δ) ^ κ := by
  classical
  haveI : Nonempty F := ⟨0⟩
  set Bad : F × F → Prop := fun p =>
    tB stmts * Nat.card L < (goodSet (m + ℓ) δ (P.w0 ws stmts hJ p.1 p.2)).ncard
  set K : ℚ := tB stmts * 2 ^ (m + ℓ + R) / Fintype.card F + epsFold F (m + ℓ + R) ℓ +
    (1 - δ) ^ κ
  have hF : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hML : (Nat.card L : ℚ) = 2 ^ (m + ℓ + R) := by exact_mod_cast (hL : Nat.card L = _)
  have hpt : ∀ p : F × F, prob (fun ω : (F × (Fin ℓ → F)) × (Fin κ → L) =>
      P.Accepts ℓ ws stmts hJ p.1 p.2 ω.1.1 (extR ω.1.2) ω.2) ≤ (if Bad p then 1 else 0) + K := by
    intro p
    have h := ft_family_bound hL hℓ hδ0 hδ (P.ft p.1 p.2) (fun β => hC p.1 p.2 β)
      (fun β => hdeg p.1 p.2 β) κ (P.w0 ws stmts hJ p.1 p.2)
    refine h.trans ?_
    have hG1 : ((goodSet (m + ℓ) δ (P.w0 ws stmts hJ p.1 p.2)).ncard : ℚ) ≤ Fintype.card F := by
      have := Set.ncard_le_ncard (Set.subset_univ (goodSet (m + ℓ) δ (P.w0 ws stmts hJ p.1 p.2)))
        (Set.toFinite _)
      rw [Set.ncard_univ, Nat.card_eq_fintype_card] at this
      exact_mod_cast this
    simp only [K]
    split_ifs with hB
    · have : ((goodSet (m + ℓ) δ (P.w0 ws stmts hJ p.1 p.2)).ncard : ℚ) / Fintype.card F ≤ 1 := by
        rw [div_le_one hF]; exact hG1
      have : (0 : ℚ) ≤ tB stmts * 2 ^ (m + ℓ + R) / Fintype.card F := by positivity
      linarith
    · have hle : ((goodSet (m + ℓ) δ (P.w0 ws stmts hJ p.1 p.2)).ncard : ℚ) ≤
          tB stmts * 2 ^ (m + ℓ + R) := by
        rw [← hML]; exact_mod_cast not_lt.1 hB
      have : ((goodSet (m + ℓ) δ (P.w0 ws stmts hJ p.1 p.2)).ncard : ℚ) / Fintype.card F ≤
          tB stmts * 2 ^ (m + ℓ + R) / Fintype.card F := div_le_div_of_nonneg_right hle hF.le
      linarith
  have hbad := prob_bad_B hL hR hδ0 hδ P ws stmts hJ hnw
  unfold BProver.accProb
  rw [prob_prod_eq_expect (fun (p : F × F) (ω : (F × (Fin ℓ → F)) × (Fin κ → L)) =>
    P.Accepts ℓ ws stmts hJ p.1 p.2 ω.1.1 (extR ω.1.2) ω.2)]
  have hF2 : (0 : ℚ) < Fintype.card (F × F) := by exact_mod_cast Fintype.card_pos
  calc expect (fun p : F × F => prob (fun ω : (F × (Fin ℓ → F)) × (Fin κ → L) =>
        P.Accepts ℓ ws stmts hJ p.1 p.2 ω.1.1 (extR ω.1.2) ω.2))
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

/-- **Knowledge:** acceptance probability above the bound of Theorem batch implies a witness. -/
theorem knowledge_B [Fintype F] [DecidableEq F] [Fintype L] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : BProver F L J) (hC : P.Causal) (hdeg : P.DegOK m)
    (κ : ℕ) (ws : Fin r → L → F) (stmts : Fin J → BStmt F r (m + ℓ)) (hJ : 1 ≤ J)
    (hacc : 2 * ((2 ^ (m + ℓ) - 1 : ℕ) : ℚ) / Fintype.card F +
        tB stmts * 2 ^ (m + ℓ + R) / Fintype.card F + epsFold F (m + ℓ + R) ℓ + (1 - δ) ^ κ <
      P.accProb ℓ κ ws stmts hJ) :
    ∃ fs, RelBatchS δ ws stmts fs := by
  by_contra h
  push_neg at h
  have := soundness_B hL hR hℓ hδ0 hδ P hC hdeg κ ws stmts hJ h
  linarith

end Sound

/-! ### Completeness -/

section Complete

variable {r n J : ℕ}

/-- The honest `U_j` (with `Q_j = V_{f_i}(γX)` for a Hadamard check). -/
noncomputable def hU (fs : Fin r → Table F n) (γ : F) : BStmt F r n → F[X]
  | .eval i _ _ => kronEnc (fs i)
  | .ip i _ _ => kronEnc (fs i)
  | .had i _ _ => kronEnc (gscale γ (fs i))

/-- The honest `K_j`. -/
noncomputable def hK (fs : Fin r → Table F n) : BStmt F r n → F[X]
  | .eval _ z _ => evalKer z
  | .ip _ i' _ => revP (2 ^ n) (kronEnc (fs i'))
  | .had _ i' _ => revP (2 ^ n) (kronEnc (fs i'))

noncomputable def hy1 (fs : Fin r → Table F n) (γ θ : F) : BStmt F r n → F
  | .had i _ _ => (kronEnc (fs i)).eval (γ * θ)
  | _ => 0

noncomputable def hy3 (fs : Fin r → Table F n) (γ : F) : BStmt F r n → F
  | .had _ _ k => (kronEnc (fs k)).eval γ
  | _ => 0

noncomputable def hquot (fs : Fin r → Table F n) (γ θ : F) : BStmt F r n → Fin 3 → F[X]
  | .had i _ k => ![divq (kronEnc (fs i)) (γ * θ), divq (kronEnc (gscale γ (fs i))) θ,
      divq (kronEnc (fs k)) γ]
  | _ => fun _ => 0

lemma hU_mem (fs : Fin r → Table F n) (γ : F) (s : BStmt F r n) : hU fs γ s ∈ degreeLT F (2 ^ n) := by
  cases s <;> exact kronEnc_mem_degreeLT _

lemma hK_mem (fs : Fin r → Table F n) (s : BStmt F r n) : hK fs s ∈ degreeLT F (2 ^ n) := by
  cases s
  · exact evalKer_mem _
  · exact revP_mem _ _
  · exact revP_mem _ _

lemma hquot_mem (fs : Fin r → Table F n) (γ θ : F) (s : BStmt F r n) (q : Fin 3) :
    hquot fs γ θ s q ∈ degreeLT F (2 ^ n) := by
  cases s
  · exact Submodule.zero_mem _
  · exact Submodule.zero_mem _
  · fin_cases q
    · exact divq_mem (kronEnc_mem_degreeLT _) _
    · exact divq_mem (kronEnc_mem_degreeLT _) _
    · exact divq_mem (kronEnc_mem_degreeLT _) _

/-- The honest polynomials of the words. -/
noncomputable def bpolys (fs : Fin r → Table F n) (stmts : Fin J → BStmt F r n) (γ θ : F) :
    BWord stmts → F[X] :=
  Sum.elim (fun d => kronEnc (fs d.1)) <| Sum.elim (fun b => revP (2 ^ n) (kronEnc (fs b.1))) <|
    Sum.elim (fun h => hU fs γ (stmts h.1)) <|
      Sum.elim (fun j => openAG (2 ^ n) (hU fs γ (stmts j)) (hK fs (stmts j))) <|
        Sum.elim (fun j => openHG (2 ^ n) (hU fs γ (stmts j)) (hK fs (stmts j)))
          (fun p => hquot fs γ θ (stmts p.1.1) p.2)

lemma bpolys_mem (fs : Fin r → Table F n) (stmts : Fin J → BStmt F r n) (γ θ : F)
    (s : BWord stmts) : bpolys fs stmts γ θ s ∈ degreeLT F (2 ^ n) := by
  rcases s with d | b | h | j | j | p
  · exact kronEnc_mem_degreeLT _
  · exact revP_mem _ _
  · exact hU_mem _ _ _
  · exact openAG_mem _ _ _
  · exact openHG_mem _ _ _
  · exact hquot_mem _ _ _ _ _

/-- The honest batched polynomial `U_0 = ∑_s β^{e(s)} P_s`. -/
noncomputable def bU0 (fs : Fin r → Table F n) (stmts : Fin J → BStmt F r n) (hJ : 1 ≤ J)
    (γ θ β : F) : F[X] :=
  ∑ s, C (β ^ ((benum stmts hJ s : Fin (tB stmts + 1)) : ℕ)) * bpolys fs stmts γ θ s

lemma bU0_mem (fs : Fin r → Table F n) (stmts : Fin J → BStmt F r n) (hJ : 1 ≤ J) (γ θ β : F) :
    bU0 fs stmts hJ γ θ β ∈ degreeLT F (2 ^ n) :=
  Submodule.sum_mem _ (fun s _ => by
    rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (bpolys_mem fs stmts γ θ s))

/-- The honest prover of `Π_Batch` for the tables `fs`. -/
noncomputable def honestB (fs : Fin r → Table F n) (stmts : Fin J → BStmt F r n) (hJ : 1 ≤ J)
    (ℓ : ℕ) : BProver F L J where
  wQ γ j := ev L (hU fs γ (stmts j))
  y1 γ θ j := hy1 fs γ θ (stmts j)
  y3 γ _ j := hy3 fs γ (stmts j)
  wA γ _ j := ev L (openAG (2 ^ n) (hU fs γ (stmts j)) (hK fs (stmts j)))
  ft γ θ β := honestFT (bU0 fs stmts hJ γ θ β) ℓ

/-- The honest words are the codewords of `bpolys`, when the statements hold and no pole of a
Hadamard check lies in `L`. -/
theorem bwords_honest (fs : Fin r → Table F n) (stmts : Fin J → BStmt F r n)
    (hholds : ∀ j, (stmts j).Holds fs) (γ θ : F)
    (hpoles : (∃ j, (stmts j).isHad = true) → ∀ ξ : L, xv' ξ ≠ γ * θ ∧ xv' ξ ≠ θ ∧ xv' ξ ≠ γ)
    (s : BWord stmts) :
    bwords (n := n) (fun i => encode L (fs i)) stmts (fun j => ev L (hU fs γ (stmts j)))
      (fun j => hy1 fs γ θ (stmts j)) (fun j => hy3 fs γ (stmts j))
      (fun j => ev L (openAG (2 ^ n) (hU fs γ (stmts j)) (hK fs (stmts j)))) γ θ s =
      ev L (bpolys fs stmts γ θ s) := by
  rcases s with d | b | h | j | j | ⟨⟨j, hj⟩, q⟩
  · rfl
  · exact wrev_ev (kronEnc_mem_degreeLT _)
  · rfl
  · rfl
  · -- the virtual word `h_j`
    show virtG n (Uw n (fun i => encode L (fs i)) (ev L (hU fs γ (stmts j))) (stmts j))
      (Kw (fun i => encode L (fs i)) (stmts j))
      (ev L (openAG (2 ^ n) (hU fs γ (stmts j)) (hK fs (stmts j)))) (vS (hy3 fs γ (stmts j)) (stmts j)) =
      ev L (openHG (2 ^ n) (hU fs γ (stmts j)) (hK fs (stmts j)))
    have hh := hholds j
    have key : Uw n (fun i => encode L (fs i)) (ev L (hU fs γ (stmts j))) (stmts j) =
        ev L (hU fs γ (stmts j)) ∧ Kw (fun i => encode L (fs i)) (stmts j) = ev L (hK fs (stmts j)) ∧
        vS (hy3 fs γ (stmts j)) (stmts j) = (hU fs γ (stmts j) * hK fs (stmts j)).coeff (2 ^ n - 1) := by
      revert hh
      cases stmts j with
      | eval i z v =>
        intro hh
        refine ⟨rfl, rfl, ?_⟩
        show v = (kronEnc (fs i) * evalKer z).coeff (2 ^ n - 1)
        rw [← eval_table]; exact hh.symm
      | ip i i' S =>
        intro hh
        refine ⟨rfl, wrev_ev (kronEnc_mem_degreeLT _), ?_⟩
        show S = (kronEnc (fs i) * revP (2 ^ n) (kronEnc (fs i'))).coeff (2 ^ n - 1)
        rw [← inner_product]; exact hh.symm
      | had i i' k =>
        intro hh
        refine ⟨rfl, wrev_ev (kronEnc_mem_degreeLT _), ?_⟩
        show (kronEnc (fs k)).eval γ =
          (kronEnc (gscale γ (fs i)) * revP (2 ^ n) (kronEnc (fs i'))).coeff (2 ^ n - 1)
        rw [eval_c_eq (fs i) (fs i') (fs k) hh γ, inner_product]
    rw [key.1, key.2.1, key.2.2]
    exact virtG_honest (hU_mem _ _ _) (hK_mem _ _)
  · -- the quotient words
    have hp := hpoles ⟨j, hj⟩
    show quotW (fun i => encode L (fs i)) (ev L (hU fs γ (stmts j))) (hy1 fs γ θ (stmts j))
      (hy3 fs γ (stmts j)) γ θ (stmts j) q = ev L (hquot fs γ θ (stmts j) q)
    revert hj
    cases stmts j with
    | eval i z v => intro hj; simp [BStmt.isHad] at hj
    | ip i i' S => intro hj; simp [BStmt.isHad] at hj
    | had i i' k =>
      intro _
      fin_cases q
      · exact (deep_honest (kronEnc_mem_degreeLT _) _ (fun ξ => (hp ξ).1)).1
      · show qword (ev L (kronEnc (gscale γ (fs i)))) ((kronEnc (fs i)).eval (γ * θ)) θ =
          ev L (divq (kronEnc (gscale γ (fs i))) θ)
        rw [← eval_gscale]
        exact (deep_honest (kronEnc_mem_degreeLT _) _ (fun ξ => (hp ξ).2.1)).1
      · exact (deep_honest (kronEnc_mem_degreeLT _) _ (fun ξ => (hp ξ).2.2)).1

/-- **Theorem (completeness):** if `w_i = Enc^T(f_i)` and every statement holds, the honest
prover is accepted whenever no pole of a Hadamard check lies in `L` (always, if there is none). -/
theorem honestB_accepts {m ℓ R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (fs : Fin r → Table F (m + ℓ)) (stmts : Fin J → BStmt F r (m + ℓ)) (hJ : 1 ≤ J)
    (hholds : ∀ j, (stmts j).Holds fs) (γ θ β : F)
    (hpoles : (∃ j, (stmts j).isHad = true) → ∀ ξ : L, xv' ξ ≠ γ * θ ∧ xv' ξ ≠ θ ∧ xv' ξ ≠ γ)
    (r' : ℕ → F) {κ : ℕ} (ξ : Fin κ → L) :
    (honestB (L := L) fs stmts hJ ℓ).Accepts ℓ (fun i => encode L (fs i)) stmts hJ γ θ β r' ξ := by
  unfold BProver.Accepts
  have e : (honestB (L := L) fs stmts hJ ℓ).w0 (fun i => encode L (fs i)) stmts hJ γ θ β =
      ev L (bU0 fs stmts hJ γ θ β) := by
    show wbatB (fun i => encode L (fs i)) stmts hJ (fun j => ev L (hU fs γ (stmts j)))
      (fun j => hy1 fs γ θ (stmts j)) (fun j => hy3 fs γ (stmts j))
      (fun j => ev L (openAG (2 ^ (m + ℓ)) (hU fs γ (stmts j)) (hK fs (stmts j)))) γ θ β = _
    unfold wbatB
    simp_rw [bwords_honest fs stmts hholds γ θ hpoles]
    funext x
    simp [bU0, ev, eval_finset_sum, Finset.sum_apply]
  rw [e]
  exact honestFT_accepts hL _ r' ξ

theorem honestB_causal (fs : Fin r → Table F n) (stmts : Fin J → BStmt F r n) (hJ : 1 ≤ J)
    (ℓ : ℕ) : (honestB (L := L) fs stmts hJ ℓ).Causal := by
  intro γ θ β j r1 r2 h
  simp only [honestB, honestFT]
  rw [pfoldUp_congr _ j h]

theorem honestB_DegOK {m ℓ : ℕ} (fs : Fin r → Table F (m + ℓ))
    (stmts : Fin J → BStmt F r (m + ℓ)) (hJ : 1 ≤ J) :
    (honestB (L := L) fs stmts hJ ℓ).DegOK m :=
  fun γ θ β => honestFT_DegOK (bU0_mem fs stmts hJ γ θ β)

/-- The pairs `(γ, θ)` with `γθ, θ, γ ∉ L` have probability at least `1 - 3M/|F|`. -/
theorem prob_poles_ge [Fintype F] [DecidableEq F] [Fintype L] :
    1 - 3 * (Nat.card L : ℚ) / Fintype.card F ≤
      prob (fun p : F × F => ∀ ξ : L, xv' ξ ≠ p.1 * p.2 ∧ xv' ξ ≠ p.2 ∧ xv' ξ ≠ p.1) := by
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

/-- **Completeness, probability:** the honest prover is accepted with probability at least
`1 - 3M/|F|`. -/
theorem honestB_prob [Fintype F] [DecidableEq F] [Fintype L] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (fs : Fin r → Table F (m + ℓ))
    (stmts : Fin J → BStmt F r (m + ℓ)) (hJ : 1 ≤ J) (hholds : ∀ j, (stmts j).Holds fs) (κ : ℕ) :
    1 - 3 * (Nat.card L : ℚ) / Fintype.card F ≤
      (honestB (L := L) fs stmts hJ ℓ).accProb ℓ κ (fun i => encode L (fs i)) stmts hJ := by
  classical
  haveI : Nonempty ((F × (Fin ℓ → F)) × (Fin κ → L)) := ⟨⟨⟨0, fun _ => 0⟩, fun _ => 1⟩⟩
  refine (prob_poles_ge (L := L)).trans ?_
  rw [← prob_fst (fun p : F × F => ∀ ξ : L, xv' ξ ≠ p.1 * p.2 ∧ xv' ξ ≠ p.2 ∧ xv' ξ ≠ p.1)
    (B := (F × (Fin ℓ → F)) × (Fin κ → L))]
  exact prob_mono (fun ω hω => honestB_accepts hL fs stmts hJ hholds _ _ _ (fun _ => hω) _ _)

end Complete

/-! ### Any folding arity -/

section Arity

variable {r n J : ℕ}

def BProver.AcceptsC (P : BProver F L J) (C : Set ℕ) (ℓ : ℕ) {κ : ℕ} (ws : Fin r → L → F)
    (stmts : Fin J → BStmt F r n) (hJ : 1 ≤ J) (γ θ β : F) (r' : ℕ → F) (ξ : Fin κ → L) : Prop :=
  (P.ft γ θ β).AcceptsC C ℓ (P.w0 ws stmts hJ γ θ β) r' ξ

noncomputable def BProver.accProbC [Fintype F] [Fintype L] (P : BProver F L J) (C : Set ℕ)
    (ℓ κ : ℕ) (ws : Fin r → L → F) (stmts : Fin J → BStmt F r n) (hJ : 1 ≤ J) : ℚ :=
  prob (fun ω : (F × F) × ((F × (Fin ℓ → F)) × (Fin κ → L)) =>
    P.AcceptsC C ℓ ws stmts hJ ω.1.1 ω.1.2 ω.2.1.1 (extR ω.2.1.2) ω.2.2)

noncomputable def BProver.inducedC (P : BProver F L J) (C : Set ℕ) (ws : Fin r → L → F)
    (stmts : Fin J → BStmt F r n) (hJ : 1 ≤ J) : BProver F L J :=
  { P with ft := fun γ θ β => (P.ft γ θ β).induced C (P.w0 ws stmts hJ γ θ β) }

/-- **Soundness of `Π^C_Batch`** for every set `C` of committed levels. -/
theorem soundnessC_B [Fintype F] [DecidableEq F] [Fintype L] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : BProver F L J) (hC : P.Causal) (hdeg : P.DegOK m)
    (C : Set ℕ) (κ : ℕ) (ws : Fin r → L → F) (stmts : Fin J → BStmt F r (m + ℓ)) (hJ : 1 ≤ J)
    (hnw : ∀ fs, ¬ RelBatchS δ ws stmts fs) :
    P.accProbC C ℓ κ ws stmts hJ ≤
      2 * ((2 ^ (m + ℓ) - 1 : ℕ) : ℚ) / Fintype.card F +
        tB stmts * 2 ^ (m + ℓ + R) / Fintype.card F + epsFold F (m + ℓ + R) ℓ + (1 - δ) ^ κ := by
  have e : P.accProbC C ℓ κ ws stmts hJ = (P.inducedC C ws stmts hJ).accProb ℓ κ ws stmts hJ := by
    unfold BProver.accProbC BProver.accProb
    congr 1
    funext ω
    exact propext (acceptsC_iff (P.ft ω.1.1 ω.1.2 ω.2.1.1) C ℓ _ _ _)
  rw [e]
  exact soundness_B hL hR hℓ hδ0 hδ (P.inducedC C ws stmts hJ)
    (fun γ θ β => induced_causal _ C _ (hC γ θ β)) (fun γ θ β => induced_DegOK _ C _ (hdeg γ θ β))
    κ ws stmts hJ hnw

end Arity

end KroneckerFRI
