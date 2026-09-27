/-
KroneckerFRI/AffineBatch.lean
§5.1 of the research note "Sumcheck-free hypercube inner products": `Π_Batch` on affine forms of
committed words and public tables (Proposition affine).

Modelling.
* Commitments are named by a type `ι` (`ws : ι → L → F`).
* An affine form `λ = ∑_{i ∈ S} c_i w_i + P` has a declared support `S` (a finite set of
  commitments, the coefficients may vanish), coefficients `c` and a public table `P`, whose
  polynomial `V_P = kronEnc P` the verifier evaluates.  Its word is
  `ξ ↦ ∑_{i ∈ S} c_i w_i(ξ) + V_P(ξ)` and, for tables `f_i`, its table is `∑_{i∈S} c_i f_i + P`.
* A form is *public* when its support is empty.  The quotient word of a public form is not in
  the curve: the verifier checks `y = V_P(x)` directly (`DirOK`).
* The words of the curve: the commitments read directly (`D`), those read reversed (`B`), one
  `w_Q` per Hadamard check, one `w_A` and one `h` per statement, and the quotient words of the
  non-public forms of the Hadamard checks (`QIdx`).
-/
import KroneckerFRI.BatchStmts

set_option autoImplicit false

open Polynomial Finset KBFold

namespace KroneckerFRI

variable {F : Type*} [Field F] {L : Subgroup Fˣ}

/-! ### Affine forms -/

section Forms

variable {ι : Type*} {n : ℕ}

variable (F) in
/-- An affine form `∑_{i ∈ supp} c_i w_i + P`. -/
structure AForm (ι : Type*) (n : ℕ) where
  supp : Finset ι
  c : ι → F
  p : Table F n

namespace AForm

/-- A form without committed part. -/
def isPub (a : AForm F ι n) : Prop := a.supp = ∅

/-- The word of a form. -/
noncomputable def word (ws : ι → L → F) (a : AForm F ι n) : L → F :=
  fun ξ => ∑ i ∈ a.supp, a.c i * ws i ξ + (kronEnc a.p).eval (xv' ξ)

/-- The table of a form. -/
def table (fs : ι → Table F n) (a : AForm F ι n) : Table F n :=
  fun w => ∑ i ∈ a.supp, a.c i * fs i w + a.p w

lemma encode_table (fs : ι → Table F n) (a : AForm F ι n) (ξ : L) :
    encode L (a.table fs) ξ = ∑ i ∈ a.supp, a.c i * encode L (fs i) ξ + (kronEnc a.p).eval (xv' ξ) := by
  simp only [encode, ev, eval_kronEnc, table, add_mul, sum_add_distrib, sum_mul, mul_sum]
  congr 1
  rw [sum_comm]
  exact sum_congr rfl (fun i _ => sum_congr rfl (fun w _ => by ring))

/-- If the committed words of a form agree with `Enc^T(f_i)` on `S`, the word of the form agrees
with `Enc^T` of its table on `S`. -/
lemma word_agree (ws : ι → L → F) (fs : ι → Table F n) (a : AForm F ι n) (S : Set L)
    (h : ∀ i ∈ a.supp, ∀ ξ ∈ S, ws i ξ = encode L (fs i) ξ) :
    ∀ ξ ∈ S, a.word ws ξ = encode L (a.table fs) ξ := by
  intro ξ hξ
  rw [encode_table, word]
  congr 1
  exact sum_congr rfl (fun i hi => by rw [h i hi ξ hξ])

lemma table_congr {fs fs' : ι → Table F n} (a : AForm F ι n) (h : ∀ i ∈ a.supp, fs i = fs' i) :
    a.table fs = a.table fs' := by
  funext w
  simp only [table]
  congr 1
  exact sum_congr rfl (fun i hi => by rw [h i hi])

lemma table_pub (fs : ι → Table F n) {a : AForm F ι n} (h : a.isPub) : a.table fs = a.p := by
  funext w; simp [table, show a.supp = ∅ from h]

end AForm

end Forms

/-! ### Statements on affine forms -/

section Statements

variable {ι : Type*} [DecidableEq ι] {n : ℕ}

variable (F) in
/-- A statement on affine forms. -/
inductive AStmt (ι : Type*) (n : ℕ)
  | eval (a : AForm F ι n) (z : Fin n → F) (v : F)
  | ip (a a' : AForm F ι n) (S : F)
  | had (a a' k : AForm F ι n)

namespace AStmt

/-- The commitments read directly. -/
def direct : AStmt F ι n → Finset ι
  | eval a _ _ => a.supp
  | ip a _ _ => a.supp
  | had a _ k => a.supp ∪ k.supp

/-- The commitments read reversed. -/
def rev : AStmt F ι n → Finset ι
  | eval _ _ _ => ∅
  | ip _ a' _ => a'.supp
  | had _ a' _ => a'.supp

def isHad : AStmt F ι n → Bool
  | had _ _ _ => true
  | _ => false

/-- The statement holds for the tables `fs`. -/
def Holds (fs : ι → Table F n) : AStmt F ι n → Prop
  | eval a z v => mle (a.table fs) z = v
  | ip a a' S => ∑ w, a.table fs w * a'.table fs w = S
  | had a a' k => ∀ w, a.table fs w * a'.table fs w = k.table fs w

/-- The `q`-th quotient word of a Hadamard check is in the curve (its form is not public). -/
def qIn : AStmt F ι n → Fin 3 → Bool
  | had a _ k => ![decide (a.supp ≠ ∅), true, decide (k.supp ≠ ∅)]
  | _ => fun _ => false

end AStmt

variable {J : ℕ}

def DsetA (stmts : Fin J → AStmt F ι n) : Finset ι := univ.biUnion fun j => (stmts j).direct
def BsetA (stmts : Fin J → AStmt F ι n) : Finset ι := univ.biUnion fun j => (stmts j).rev
abbrev HposA (stmts : Fin J → AStmt F ι n) := {j : Fin J // (stmts j).isHad = true}
/-- The quotient words in the curve. -/
abbrev QIdx (stmts : Fin J → AStmt F ι n) :=
  {x : HposA stmts × Fin 3 // (stmts x.1.1).qIn x.2 = true}

/-- The index type of the words: `D ⊕ B ⊕ ℋ (w_Q) ⊕ [J] (w_A) ⊕ [J] (h) ⊕ QIdx`. -/
abbrev AWord (stmts : Fin J → AStmt F ι n) :=
  {i // i ∈ DsetA stmts} ⊕ {i // i ∈ BsetA stmts} ⊕ HposA stmts ⊕ Fin J ⊕ Fin J ⊕ QIdx stmts

/-- **The relation `R^δ_Batch` on affine forms.** Tables are required for the commitments of the
supports only; public tables carry no condition. -/
def RelBatchA (δ : ℚ) (ws : ι → L → F) (stmts : Fin J → AStmt F ι n) (fs : ι → Table F n) : Prop :=
  (∀ i ∈ DsetA stmts ∪ BsetA stmts, fibDist (ws i) (encode L (fs i)) ≤ δ) ∧
    ∀ j, (stmts j).Holds fs

/-- The direct checks of the quotient values of public forms. -/
def DirOK (stmts : Fin J → AStmt F ι n) (y1 y3 : Fin J → F) (γ θ : F) : Prop :=
  ∀ j a a' k, stmts j = .had a a' k →
    (a.isPub → (kronEnc a.p).eval (γ * θ) = y1 j) ∧ (k.isPub → (kronEnc k.p).eval γ = y3 j)

omit [Field F] in
lemma mem_DsetA {stmts : Fin J → AStmt F ι n} {j : Fin J} {i : ι}
    (h : i ∈ (stmts j).direct) : i ∈ DsetA stmts :=
  mem_biUnion.2 ⟨j, mem_univ _, h⟩

omit [Field F] in
lemma mem_BsetA {stmts : Fin J → AStmt F ι n} {j : Fin J} {i : ι}
    (h : i ∈ (stmts j).rev) : i ∈ BsetA stmts :=
  mem_biUnion.2 ⟨j, mem_univ _, h⟩

end Statements

/-! ### The words -/

section Words

variable {ι : Type*} [DecidableEq ι] {n J : ℕ}

variable (n) in
noncomputable def UwA (ws : ι → L → F) (wQ : L → F) : AStmt F ι n → L → F
  | .eval a _ _ => a.word ws
  | .ip a _ _ => a.word ws
  | .had _ _ _ => wQ

noncomputable def KwA (ws : ι → L → F) : AStmt F ι n → L → F
  | .eval _ z _ => ev L (evalKer z)
  | .ip _ a' _ => wrev (2 ^ n) (a'.word ws)
  | .had _ a' _ => wrev (2 ^ n) (a'.word ws)

def vSA (y3 : F) : AStmt F ι n → F
  | .eval _ _ v => v
  | .ip _ _ S => S
  | .had _ _ _ => y3

/-- The three quotient words of a Hadamard check (only those of non-public forms enter the
curve). -/
noncomputable def quotWA (ws : ι → L → F) (wQ : L → F) (y1 y3 γ θ : F) :
    AStmt F ι n → Fin 3 → L → F
  | .had a _ k => ![qword (a.word ws) y1 (γ * θ), qword wQ y1 θ, qword (k.word ws) y3 γ]
  | _ => fun _ _ => 0

/-- The words of `Π_Batch` on affine forms. -/
noncomputable def awords (ws : ι → L → F) (stmts : Fin J → AStmt F ι n) (wQ : Fin J → L → F)
    (y1 y3 : Fin J → F) (wA : Fin J → L → F) (γ θ : F) : AWord stmts → L → F :=
  Sum.elim (fun d => ws d.1) <| Sum.elim (fun b => wrev (2 ^ n) (ws b.1)) <|
    Sum.elim (fun h => wQ h.1) <| Sum.elim (fun j => wA j) <|
      Sum.elim (fun j => virtG n (UwA n ws (wQ j) (stmts j)) (KwA ws (stmts j)) (wA j)
        (vSA (y3 j) (stmts j))) (fun x => quotWA ws (wQ x.1.1.1) (y1 x.1.1.1) (y3 x.1.1.1) γ θ
          (stmts x.1.1.1) x.1.2)

/-- `t`: the number of words minus one. -/
def tA (stmts : Fin J → AStmt F ι n) : ℕ := Fintype.card (AWord stmts) - 1

omit [Field F] in
lemma card_AWord_eq (stmts : Fin J → AStmt F ι n) (hJ : 1 ≤ J) :
    Fintype.card (AWord stmts) = tA stmts + 1 := by
  have : 2 ≤ Fintype.card (AWord stmts) := by
    simp only [Fintype.card_sum, Fintype.card_fin]; omega
  unfold tA; omega

omit [Field F] in
lemma one_le_tA (stmts : Fin J → AStmt F ι n) (hJ : 1 ≤ J) : 1 ≤ tA stmts := by
  have : 2 ≤ Fintype.card (AWord stmts) := by
    simp only [Fintype.card_sum, Fintype.card_fin]; omega
  unfold tA; omega

noncomputable def aenum (stmts : Fin J → AStmt F ι n) (hJ : 1 ≤ J) :
    AWord stmts ≃ Fin (tA stmts + 1) :=
  Fintype.equivFinOfCardEq (card_AWord_eq stmts hJ)

/-- The batched word `w_0 = ∑_s β^{e(s)} u_s`. -/
noncomputable def wbatA (ws : ι → L → F) (stmts : Fin J → AStmt F ι n) (hJ : 1 ≤ J)
    (wQ : Fin J → L → F) (y1 y3 : Fin J → F) (wA : Fin J → L → F) (γ θ β : F) : L → F :=
  ∑ s, β ^ ((aenum stmts hJ s : Fin (tA stmts + 1)) : ℕ) •
    awords (n := n) ws stmts wQ y1 y3 wA γ θ s

end Words

/-! ### Lemma batchT on affine forms -/

section Batching

variable {ι : Type*} [DecidableEq ι] {n J : ℕ}

/-- **Lemma batchT on affine forms.** If the direct checks pass and more than `tM` challenges `β`
are good, there are tables `fs` and polynomials `Q̂_j` such that every commitment read is within
fibre distance `δ` of `Enc^T(f_i)`, every `w_Q^{(j)}` is within `δ` of `ev(Q̂_j)`, every
evaluation and inner product holds for the tables of the forms, and every Hadamard check
satisfies the two equalities of (2) for the tables of its forms. -/
theorem batching_A [Fintype F] [DecidableEq F] {R : ℕ} (hL : IsSmoothDomain L (n + R))
    (hR : 2 ≤ R) {δ : ℚ} (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (ws : ι → L → F) (stmts : Fin J → AStmt F ι n) (hJ : 1 ≤ J) (wQ : Fin J → L → F)
    (y1 y3 : Fin J → F) (wA : Fin J → L → F) (γ θ : F) (hdir : DirOK stmts y1 y3 γ θ)
    (hG : tA stmts * Nat.card L <
      (goodSet n δ (fun β => wbatA ws stmts hJ wQ y1 y3 wA γ θ β)).ncard) :
    ∃ fs : ι → Table F n, ∃ Qh : Fin J → F[X],
      (∀ i ∈ DsetA stmts ∪ BsetA stmts, fibDist (ws i) (encode L (fs i)) ≤ δ) ∧
      (∀ j, (stmts j).isHad = true → Qh j ∈ degreeLT F (2 ^ n) ∧
        fibDist (wQ j) (ev L (Qh j)) ≤ δ) ∧
      (∀ j, (stmts j).isHad = false → (stmts j).Holds fs) ∧
      (∀ j a a' k, stmts j = .had a a' k →
        (kronEnc (a.table fs)).eval (γ * θ) = y1 j ∧ (Qh j).eval θ = y1 j ∧
        (kronEnc (k.table fs)).eval γ = y3 j ∧
        y3 j = (Qh j * revP (2 ^ n) (kronEnc (a'.table fs))).coeff (2 ^ n - 1)) := by
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
  set u := awords (n := n) ws stmts wQ y1 y3 wA γ θ
  obtain ⟨c, hc, T, hTneg, hTcard, hTu⟩ :=
    curve_agreement_idx hL hδ0 hδ (one_le_tA stmts hJ) (aenum stmts hJ) u hG
  set P : AWord stmts → F[X] := fun s => polyOf (c s)
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
  let sD : {i // i ∈ DsetA stmts} → AWord stmts := Sum.inl
  let sB : {i // i ∈ BsetA stmts} → AWord stmts := fun b => Sum.inr (Sum.inl b)
  let sQ : HposA stmts → AWord stmts := fun h => Sum.inr (Sum.inr (Sum.inl h))
  let sA : Fin J → AWord stmts := fun j => Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))
  let sH : Fin J → AWord stmts := fun j => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))
  let sq : QIdx stmts → AWord stmts := fun x => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr x))))
  -- tables of the commitments
  have hdist_rev : ∀ b : {i // i ∈ BsetA stmts},
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
  have hdist_dir : ∀ d : {i // i ∈ DsetA stmts},
      fibDist (ws d.1) (encode L (kronCoeffs n (P (sD d)))) ≤ δ := by
    intro d
    refine fibDist_le_of_closed hneg h2 T hTneg hTcard (fun ξ hξ => ?_)
    rw [encode, kronEnc_kronCoeffs (hP _)]
    exact hv (sD d) ξ hξ
  let fs : ι → Table F n := fun i =>
    if hi : i ∈ DsetA stmts then kronCoeffs n (P (sD ⟨i, hi⟩))
    else if hb : i ∈ BsetA stmts then kronCoeffs n (revP (2 ^ n) (P (sB ⟨i, hb⟩))) else 0
  have hfsD : ∀ (i : ι) (hi : i ∈ DsetA stmts), kronEnc (fs i) = P (sD ⟨i, hi⟩) := by
    intro i hi
    simp only [fs, dif_pos hi]
    exact kronEnc_kronCoeffs (hP _)
  have hfsB : ∀ (i : ι) (hb : i ∈ BsetA stmts),
      kronEnc (fs i) = revP (2 ^ n) (P (sB ⟨i, hb⟩)) := by
    intro i hb
    by_cases hi : i ∈ DsetA stmts
    · have := encode_fib_unique hNM hneg h2 hδ' (ws i) (hdist_dir ⟨i, hi⟩) (hdist_rev ⟨i, hb⟩)
      simp only [fs, dif_pos hi]
      rw [this]; exact kronEnc_kronCoeffs (revP_mem _ _)
    · simp only [fs, dif_neg hi, dif_pos hb]
      exact kronEnc_kronCoeffs (revP_mem _ _)
  have hdist : ∀ i ∈ DsetA stmts ∪ BsetA stmts, fibDist (ws i) (encode L (fs i)) ≤ δ := by
    intro i hi
    by_cases hd : i ∈ DsetA stmts
    · have := hdist_dir ⟨i, hd⟩
      simp only [fs, dif_pos hd]; exact this
    · have hb : i ∈ BsetA stmts := by simpa [hd] using hi
      have := hdist_rev ⟨i, hb⟩
      simp only [fs, dif_neg hd, dif_pos hb]; exact this
  -- agreement of the commitments with their encodings: on `T` (direct), on `T⁻¹` (reversed)
  have hdirT : ∀ i ∈ DsetA stmts, ∀ ξ ∈ T, ws i ξ = encode L (fs i) ξ := by
    intro i hi ξ hξ
    rw [encode, ev, hfsD i hi]; exact hv (sD ⟨i, hi⟩) ξ hξ
  have hrevT : ∀ i ∈ BsetA stmts, ∀ ζ ∈ invPt '' T, ws i ζ = encode L (fs i) ζ := by
    rintro i hb _ ⟨ξ, hξ, rfl⟩
    refine (wrev_eq_iff (2 ^ n) _ _ ξ).1 ?_
    rw [encode, wrev_ev (kronEnc_mem_degreeLT _), hfsB i hb, revP_revP (hP _)]
    exact hv (sB ⟨i, hb⟩) ξ hξ
  -- forms read directly agree on `T`; forms read reversed give `ev((V_λ)*)` on `T`
  have hformD : ∀ a : AForm F ι n, a.supp ⊆ DsetA stmts →
      ∀ ξ ∈ T, a.word ws ξ = (kronEnc (a.table fs)).eval (xv' ξ) := by
    intro a ha ξ hξ
    exact a.word_agree ws fs T (fun i hi => hdirT i (ha hi)) ξ hξ
  have hformB : ∀ a : AForm F ι n, a.supp ⊆ BsetA stmts →
      ∀ ξ ∈ T, wrev (2 ^ n) (a.word ws) ξ = (revP (2 ^ n) (kronEnc (a.table fs))).eval (xv' ξ) := by
    intro a ha ξ hξ
    have h1 : a.word ws (invPt ξ) = encode L (a.table fs) (invPt ξ) :=
      a.word_agree ws fs (invPt '' T) (fun i hi => hrevT i (ha hi)) (invPt ξ) ⟨ξ, hξ, rfl⟩
    have h2 : wrev (2 ^ n) (a.word ws) ξ = wrev (2 ^ n) (encode L (a.table fs)) ξ :=
      (wrev_eq_iff (2 ^ n) _ _ ξ).2 h1
    rw [h2, encode, wrev_ev (kronEnc_mem_degreeLT _)]; rfl
  have hsubD : ∀ j, (stmts j).direct ⊆ DsetA stmts := fun j i hi => mem_DsetA hi
  have hsubB : ∀ j, (stmts j).rev ⊆ BsetA stmts := fun j i hi => mem_BsetA hi
  let Qh : Fin J → F[X] := fun j => if h : (stmts j).isHad = true then P (sQ ⟨j, h⟩) else 0
  have hval : ∀ j, ∀ PU PK : F[X], PU ∈ degreeLT F (2 ^ n) → PK ∈ degreeLT F (2 ^ n) →
      (∀ ξ ∈ T, UwA n ws (wQ j) (stmts j) ξ = PU.eval (xv' ξ) ∧
        KwA ws (stmts j) ξ = PK.eval (xv' ξ)) →
      vSA (y3 j) (stmts j) = (PU * PK).coeff (2 ^ n - 1) := by
    intro j PU PK hU hK hUK
    refine virtG_value hU hK (hP (sA j)) (hP (sH j)) T hTbig (fun ξ hξ => ⟨(hUK ξ hξ).1,
      (hUK ξ hξ).2, hv (sA j) ξ hξ, hv (sH j) ξ hξ⟩)
  refine ⟨fs, Qh, hdist, ?_, ?_, ?_⟩
  · intro j hj
    simp only [Qh, dif_pos hj]
    refine ⟨hP _, fibDist_le_of_closed hneg h2 T hTneg hTcard (fun ξ hξ => ?_)⟩
    rw [hev]; exact hTu (sQ ⟨j, hj⟩) ξ hξ
  · intro j hj
    have hD := hsubD j
    have hB := hsubB j
    cases hs : stmts j with
    | eval a z v =>
      rw [hs] at hD
      have := hval j (kronEnc (a.table fs)) (evalKer z) (kronEnc_mem_degreeLT _) (evalKer_mem z)
        (fun ξ hξ => by
          rw [hs]
          exact ⟨hformD a hD ξ hξ, rfl⟩)
      rw [hs] at this
      show mle (a.table fs) z = v
      rw [eval_table]; exact this.symm
    | ip a a' S =>
      rw [hs] at hD hB
      have := hval j (kronEnc (a.table fs)) (revP (2 ^ n) (kronEnc (a'.table fs)))
        (kronEnc_mem_degreeLT _) (revP_mem _ _) (fun ξ hξ => by
          rw [hs]
          exact ⟨hformD a hD ξ hξ, hformB a' hB ξ hξ⟩)
      rw [hs] at this
      show ∑ w, a.table fs w * a'.table fs w = S
      rw [inner_product]; exact this.symm
    | had a a' k => rw [hs] at hj; simp [AStmt.isHad] at hj
  · intro j a a' k hs
    have hj : (stmts j).isHad = true := by rw [hs]; rfl
    have hD := hsubD j
    have hB := hsubB j
    rw [hs] at hD hB
    have hDa : a.supp ⊆ DsetA stmts := fun i hi => hD (mem_union_left _ hi)
    have hDk : k.supp ⊆ DsetA stmts := fun i hi => hD (mem_union_right _ hi)
    have hQ : ∀ ξ ∈ T, wQ j ξ = (Qh j).eval (xv' ξ) := by
      intro ξ hξ
      simp only [Qh, dif_pos hj]
      exact hv (sQ ⟨j, hj⟩) ξ hξ
    have hQmem : Qh j ∈ degreeLT F (2 ^ n) := by simp only [Qh, dif_pos hj]; exact hP _
    have hqin : ∀ (q : Fin 3) (hq : (stmts j).qIn q = true), ∀ ξ ∈ T,
        quotWA ws (wQ j) (y1 j) (y3 j) γ θ (stmts j) q ξ =
          (P (sq ⟨(⟨j, hj⟩, q), hq⟩)).eval (xv' ξ) :=
      fun q hq ξ hξ => hv (sq ⟨(⟨j, hj⟩, q), hq⟩) ξ hξ
    obtain ⟨hdA, hdK⟩ := hdir j a a' k hs
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_cases hpa : a.isPub
      · rw [AForm.table_pub fs hpa]; exact hdA hpa
      · have hq0 : (stmts j).qIn 0 = true := by rw [hs]; simpa [AStmt.qIn, AForm.isPub] using hpa
        have := hqin 0 hq0
        rw [hs] at this
        exact deep_step (kronEnc_mem_degreeLT _) (hP _) T hTN (hformD a hDa)
          (fun ξ hξ => this ξ hξ)
    · have hq1 : (stmts j).qIn 1 = true := by rw [hs]; simp [AStmt.qIn]
      have := hqin 1 hq1
      rw [hs] at this
      exact deep_step hQmem (hP _) T hTN hQ (fun ξ hξ => this ξ hξ)
    · by_cases hpk : k.isPub
      · rw [AForm.table_pub fs hpk]; exact hdK hpk
      · have hq2 : (stmts j).qIn 2 = true := by rw [hs]; simpa [AStmt.qIn, AForm.isPub] using hpk
        have := hqin 2 hq2
        rw [hs] at this
        exact deep_step (kronEnc_mem_degreeLT _) (hP _) T hTN (hformD k hDk)
          (fun ξ hξ => this ξ hξ)
    · have := hval j (Qh j) (revP (2 ^ n) (kronEnc (a'.table fs))) hQmem (revP_mem _ _)
        (fun ξ hξ => by
          rw [hs]
          exact ⟨hQ ξ hξ, hformB a' hB ξ hξ⟩)
      rw [hs] at this
      exact this

end Batching

/-! ### Soundness -/

section Sound

variable {ι : Type*} [DecidableEq ι] {n J : ℕ}

namespace BProver

variable (P : BProver F L J)

/-- The batched word of the prover at `(γ, θ)`, as a function of `β`. -/
noncomputable def w0A (ws : ι → L → F) (stmts : Fin J → AStmt F ι n) (hJ : 1 ≤ J) (γ θ : F) :
    F → L → F := fun β =>
  wbatA ws stmts hJ (P.wQ γ) (P.y1 γ θ) (P.y3 γ θ) (P.wA γ θ) γ θ β

/-- The verifier of `Π_Batch` on affine forms accepts: the direct checks pass and the folding
test accepts. -/
def AcceptsA (ℓ : ℕ) {κ : ℕ} (ws : ι → L → F) (stmts : Fin J → AStmt F ι n) (hJ : 1 ≤ J)
    (γ θ β : F) (r' : ℕ → F) (ξ : Fin κ → L) : Prop :=
  DirOK stmts (P.y1 γ θ) (P.y3 γ θ) γ θ ∧
    (P.ft γ θ β).Accepts ℓ (P.w0A ws stmts hJ γ θ β) r' ξ

noncomputable def accProbA [Fintype F] [Fintype L] (ℓ κ : ℕ) (ws : ι → L → F)
    (stmts : Fin J → AStmt F ι n) (hJ : 1 ≤ J) : ℚ :=
  prob (fun ω : (F × F) × ((F × (Fin ℓ → F)) × (Fin κ → L)) =>
    P.AcceptsA ℓ ws stmts hJ ω.1.1 ω.1.2 ω.2.1.1 (extR ω.2.1.2) ω.2.2)

end BProver

/-- The pairs `(γ, θ)` at which the direct checks pass and more than `tM` challenges `β` are
good have probability at most `2(N-1)/|F|` when the instance has no witness. -/
theorem prob_bad_A [Fintype F] [DecidableEq F] {m ℓ R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hR : 2 ≤ R) {δ : ℚ} (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : BProver F L J)
    (ws : ι → L → F) (stmts : Fin J → AStmt F ι (m + ℓ)) (hJ : 1 ≤ J)
    (hnw : ∀ fs, ¬ RelBatchA δ ws stmts fs) :
    prob (fun p : F × F => DirOK stmts (P.y1 p.1 p.2) (P.y3 p.1 p.2) p.1 p.2 ∧
        tA stmts * Nat.card L < (goodSet (m + ℓ) δ (P.w0A ws stmts hJ p.1 p.2)).ncard) ≤
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
  set U := DsetA stmts ∪ BsetA stmts
  set Bad : F × F → Prop := fun p => DirOK stmts (P.y1 p.1 p.2) (P.y3 p.1 p.2) p.1 p.2 ∧
    tA stmts * Nat.card L < (goodSet (m + ℓ) δ (P.w0A ws stmts hJ p.1 p.2)).ncard
  have hbatch : ∀ p, Bad p → _ := fun p hp =>
    batching_A (n := m + ℓ) (R := R) hL hR hδ0 hδ ws stmts hJ (P.wQ p.1) (P.y1 p.1 p.2)
      (P.y3 p.1 p.2) (P.wA p.1 p.2) p.1 p.2 hp.1 hp.2
  by_cases hex : ∀ i ∈ U, ∃ f : Table F (m + ℓ), fibDist (ws i) (encode L f) ≤ δ
  swap
  · refine (prob_mono (F := fun _ => False) (fun p hp => ?_)).trans ?_
    · obtain ⟨fs, -, hd, -⟩ := hbatch p hp
      exact hex (fun i hi => ⟨fs i, hd i hi⟩)
    · rw [prob_false]; exact hbound0
  let fs0 : ι → Table F (m + ℓ) := fun i => if h : i ∈ U then Classical.choose (hex i h) else 0
  have hfs0 : ∀ i ∈ U, fibDist (ws i) (encode L (fs0 i)) ≤ δ := by
    intro i hi
    simp only [fs0, dif_pos hi]
    exact Classical.choose_spec (hex i hi)
  have huniq : ∀ fs : ι → Table F (m + ℓ), (∀ i ∈ U, fibDist (ws i) (encode L (fs i)) ≤ δ) →
      ∀ i ∈ U, fs i = fs0 i := fun fs hd i hi =>
    encode_fib_unique hNM hneg h2 hδ' (ws i) (hd i hi) (hfs0 i hi)
  have htab : ∀ fs : ι → Table F (m + ℓ), (∀ i ∈ U, fibDist (ws i) (encode L (fs i)) ≤ δ) →
      ∀ a : AForm F ι (m + ℓ), a.supp ⊆ U → a.table fs = a.table fs0 := fun fs hd a ha =>
    a.table_congr (fun i hi => huniq fs hd i (ha hi))
  obtain ⟨js, hjs⟩ : ∃ j, ¬ (stmts j).Holds fs0 := by
    by_contra h
    push_neg at h
    exact hnw fs0 ⟨hfs0, h⟩
  have hD : (stmts js).direct ⊆ U := fun i h => mem_union_left _ (mem_DsetA (j := js) h)
  have hB : (stmts js).rev ⊆ U := fun i h => mem_union_right _ (mem_BsetA (j := js) h)
  have hnothad : (stmts js).isHad = false →
      prob Bad ≤ 2 * ((2 ^ (m + ℓ) - 1 : ℕ) : ℚ) / Fintype.card F := by
    intro hh
    refine (prob_mono (F := fun _ => False) (fun p hp => ?_)).trans ?_
    · obtain ⟨fs, -, hd, -, hholds, -⟩ := hbatch p hp
      have hh' := hholds js hh
      apply hjs
      revert hh hh' hD hB
      cases stmts js with
      | eval a z v =>
        intro hD _ _ hh'
        have e := htab fs hd a hD
        simpa [AStmt.Holds, e] using hh'
      | ip a a' S =>
        intro hD hB _ hh'
        have e := htab fs hd a hD
        have e' := htab fs hd a' hB
        simpa [AStmt.Holds, e, e'] using hh'
      | had a a' k => intro _ _ hh _; simp [AStmt.isHad] at hh
    · rw [prob_false]; exact hbound0
  cases hs : stmts js with
  | eval a z v => exact hnothad (by rw [hs]; rfl)
  | ip a a' S => exact hnothad (by rw [hs]; rfl)
  | had a a' k =>
    have hj : (stmts js).isHad = true := by rw [hs]; rfl
    rw [hs] at hD hB
    have haU : a.supp ⊆ U := fun i hi => hD (mem_union_left _ hi)
    have hkU : k.supp ⊆ U := fun i hi => hD (mem_union_right _ hi)
    have hne : ¬ ∀ w, a.table fs0 w * a'.table fs0 w = k.table fs0 w := by
      intro h; apply hjs; rw [hs]; exact h
    refine prob_bad_had (n := m + ℓ) (hL := hL) hR hδ (fun γ => P.wQ γ js) (a.table fs0)
      (a'.table fs0) (k.table fs0) hne Bad (fun p hp => ?_)
    obtain ⟨fs, Qh, hd, hQ, -, hhad⟩ := hbatch p hp
    obtain ⟨e1, e2, e3, e4⟩ := hhad js a a' k hs
    obtain ⟨hQm, hQd⟩ := hQ js hj
    rw [htab fs hd a haU] at e1
    rw [htab fs hd k hkU] at e3
    rw [htab fs hd a' hB] at e4
    exact ⟨Qh js, hQm, hQd, e2.trans e1.symm, e3.trans e4⟩

/-- **Proposition affine (soundness).** If `((w_i)_i, Σ)` has no witness in `R^δ_Batch` on affine
forms, every causal prover whose final polynomials lie in `F[X]_{<N_ℓ}` is accepted with
probability at most `2(N-1)/|F| + tM/|F| + ε_fold + (1-δ)^κ`, with `t + 1` the number of words of
the curve. -/
theorem soundness_A [Fintype F] [DecidableEq F] [Fintype L] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : BProver F L J) (hC : P.Causal) (hdeg : P.DegOK m)
    (κ : ℕ) (ws : ι → L → F) (stmts : Fin J → AStmt F ι (m + ℓ)) (hJ : 1 ≤ J)
    (hnw : ∀ fs, ¬ RelBatchA δ ws stmts fs) :
    P.accProbA ℓ κ ws stmts hJ ≤
      2 * ((2 ^ (m + ℓ) - 1 : ℕ) : ℚ) / Fintype.card F +
        tA stmts * 2 ^ (m + ℓ + R) / Fintype.card F + epsFold F (m + ℓ + R) ℓ + (1 - δ) ^ κ := by
  classical
  haveI : Nonempty F := ⟨0⟩
  set Bad : F × F → Prop := fun p => DirOK stmts (P.y1 p.1 p.2) (P.y3 p.1 p.2) p.1 p.2 ∧
    tA stmts * Nat.card L < (goodSet (m + ℓ) δ (P.w0A ws stmts hJ p.1 p.2)).ncard
  set K : ℚ := tA stmts * 2 ^ (m + ℓ + R) / Fintype.card F + epsFold F (m + ℓ + R) ℓ +
    (1 - δ) ^ κ
  have hF : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hML : (Nat.card L : ℚ) = 2 ^ (m + ℓ + R) := by exact_mod_cast (hL : Nat.card L = _)
  have hδ1 : δ ≤ 1 := by
    have : (0 : ℚ) < 1 / 2 ^ R := by positivity
    linarith
  have hK0 : 0 ≤ K := by
    have h1 : 0 ≤ epsFold F (m + ℓ + R) ℓ := by
      unfold epsFold; exact sum_nonneg (fun j _ => by positivity)
    have h2 : (0 : ℚ) ≤ (1 - δ) ^ κ := pow_nonneg (by linarith) _
    have h3 : (0 : ℚ) ≤ tA stmts * 2 ^ (m + ℓ + R) / Fintype.card F := by positivity
    simp only [K]; linarith
  have hpt : ∀ p : F × F, prob (fun ω : (F × (Fin ℓ → F)) × (Fin κ → L) =>
      P.AcceptsA ℓ ws stmts hJ p.1 p.2 ω.1.1 (extR ω.1.2) ω.2) ≤ (if Bad p then 1 else 0) + K := by
    intro p
    by_cases hdir : DirOK stmts (P.y1 p.1 p.2) (P.y3 p.1 p.2) p.1 p.2
    swap
    · have : (fun ω : (F × (Fin ℓ → F)) × (Fin κ → L) =>
          P.AcceptsA ℓ ws stmts hJ p.1 p.2 ω.1.1 (extR ω.1.2) ω.2) = fun _ => False := by
        funext ω; simp [BProver.AcceptsA, hdir]
      rw [this, prob_false]
      have : (0 : ℚ) ≤ if Bad p then 1 else 0 := by split_ifs <;> norm_num
      linarith
    have h := ft_family_bound hL hℓ hδ0 hδ (P.ft p.1 p.2) (fun β => hC p.1 p.2 β)
      (fun β => hdeg p.1 p.2 β) κ (P.w0A ws stmts hJ p.1 p.2)
    refine (prob_mono (fun ω hω => hω.2)).trans (h.trans ?_)
    have hG1 : ((goodSet (m + ℓ) δ (P.w0A ws stmts hJ p.1 p.2)).ncard : ℚ) ≤ Fintype.card F := by
      have := Set.ncard_le_ncard (Set.subset_univ (goodSet (m + ℓ) δ (P.w0A ws stmts hJ p.1 p.2)))
        (Set.toFinite _)
      rw [Set.ncard_univ, Nat.card_eq_fintype_card] at this
      exact_mod_cast this
    simp only [K]
    split_ifs with hB
    · have : ((goodSet (m + ℓ) δ (P.w0A ws stmts hJ p.1 p.2)).ncard : ℚ) / Fintype.card F ≤ 1 := by
        rw [div_le_one hF]; exact hG1
      have : (0 : ℚ) ≤ tA stmts * 2 ^ (m + ℓ + R) / Fintype.card F := by positivity
      linarith
    · have hB' : ¬ tA stmts * Nat.card L <
          (goodSet (m + ℓ) δ (P.w0A ws stmts hJ p.1 p.2)).ncard := fun h => hB ⟨hdir, h⟩
      have hle : ((goodSet (m + ℓ) δ (P.w0A ws stmts hJ p.1 p.2)).ncard : ℚ) ≤
          tA stmts * 2 ^ (m + ℓ + R) := by
        rw [← hML]; exact_mod_cast not_lt.1 hB'
      have : ((goodSet (m + ℓ) δ (P.w0A ws stmts hJ p.1 p.2)).ncard : ℚ) / Fintype.card F ≤
          tA stmts * 2 ^ (m + ℓ + R) / Fintype.card F := div_le_div_of_nonneg_right hle hF.le
      linarith
  have hbad := prob_bad_A hL hR hδ0 hδ P ws stmts hJ hnw
  unfold BProver.accProbA
  rw [prob_prod_eq_expect (fun (p : F × F) (ω : (F × (Fin ℓ → F)) × (Fin κ → L)) =>
    P.AcceptsA ℓ ws stmts hJ p.1 p.2 ω.1.1 (extR ω.1.2) ω.2)]
  have hF2 : (0 : ℚ) < Fintype.card (F × F) := by exact_mod_cast Fintype.card_pos
  calc expect (fun p : F × F => prob (fun ω : (F × (Fin ℓ → F)) × (Fin κ → L) =>
        P.AcceptsA ℓ ws stmts hJ p.1 p.2 ω.1.1 (extR ω.1.2) ω.2))
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

/-- **Proposition affine (knowledge).** -/
theorem knowledge_A [Fintype F] [DecidableEq F] [Fintype L] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : BProver F L J) (hC : P.Causal) (hdeg : P.DegOK m)
    (κ : ℕ) (ws : ι → L → F) (stmts : Fin J → AStmt F ι (m + ℓ)) (hJ : 1 ≤ J)
    (hacc : 2 * ((2 ^ (m + ℓ) - 1 : ℕ) : ℚ) / Fintype.card F +
        tA stmts * 2 ^ (m + ℓ + R) / Fintype.card F + epsFold F (m + ℓ + R) ℓ + (1 - δ) ^ κ <
      P.accProbA ℓ κ ws stmts hJ) :
    ∃ fs, RelBatchA δ ws stmts fs := by
  by_contra h
  push_neg at h
  have := soundness_A hL hR hℓ hδ0 hδ P hC hdeg κ ws stmts hJ h
  linarith

end Sound

/-! ### Completeness -/

section Complete

variable {ι : Type*} [DecidableEq ι] {n J : ℕ}

omit [DecidableEq ι] in
/-- With honest commitments `w_i = Enc^T(f_i)`, the word of a form is `Enc^T` of its table. -/
lemma AForm.word_encode (fs : ι → Table F n) (a : AForm F ι n) :
    a.word (fun i => encode L (fs i)) = encode L (a.table fs) := by
  funext ξ
  exact a.word_agree _ fs Set.univ (fun _ _ _ _ => rfl) ξ (Set.mem_univ _)

noncomputable def hUA (fs : ι → Table F n) (γ : F) : AStmt F ι n → F[X]
  | .eval a _ _ => kronEnc (a.table fs)
  | .ip a _ _ => kronEnc (a.table fs)
  | .had a _ _ => kronEnc (gscale γ (a.table fs))

noncomputable def hKA (fs : ι → Table F n) : AStmt F ι n → F[X]
  | .eval _ z _ => evalKer z
  | .ip _ a' _ => revP (2 ^ n) (kronEnc (a'.table fs))
  | .had _ a' _ => revP (2 ^ n) (kronEnc (a'.table fs))

noncomputable def hy1A (fs : ι → Table F n) (γ θ : F) : AStmt F ι n → F
  | .had a _ _ => (kronEnc (a.table fs)).eval (γ * θ)
  | _ => 0

noncomputable def hy3A (fs : ι → Table F n) (γ : F) : AStmt F ι n → F
  | .had _ _ k => (kronEnc (k.table fs)).eval γ
  | _ => 0

noncomputable def hquotA (fs : ι → Table F n) (γ θ : F) : AStmt F ι n → Fin 3 → F[X]
  | .had a _ k => ![divq (kronEnc (a.table fs)) (γ * θ), divq (kronEnc (gscale γ (a.table fs))) θ,
      divq (kronEnc (k.table fs)) γ]
  | _ => fun _ => 0

omit [DecidableEq ι] in
lemma hUA_mem (fs : ι → Table F n) (γ : F) (s : AStmt F ι n) :
    hUA fs γ s ∈ degreeLT F (2 ^ n) := by
  cases s <;> exact kronEnc_mem_degreeLT _

omit [DecidableEq ι] in
lemma hKA_mem (fs : ι → Table F n) (s : AStmt F ι n) : hKA fs s ∈ degreeLT F (2 ^ n) := by
  cases s
  · exact evalKer_mem _
  · exact revP_mem _ _
  · exact revP_mem _ _

omit [DecidableEq ι] in
lemma hquotA_mem (fs : ι → Table F n) (γ θ : F) (s : AStmt F ι n) (q : Fin 3) :
    hquotA fs γ θ s q ∈ degreeLT F (2 ^ n) := by
  cases s
  · exact Submodule.zero_mem _
  · exact Submodule.zero_mem _
  · fin_cases q
    · exact divq_mem (kronEnc_mem_degreeLT _) _
    · exact divq_mem (kronEnc_mem_degreeLT _) _
    · exact divq_mem (kronEnc_mem_degreeLT _) _

/-- The honest polynomials of the words. -/
noncomputable def apolys (fs : ι → Table F n) (stmts : Fin J → AStmt F ι n) (γ θ : F) :
    AWord stmts → F[X] :=
  Sum.elim (fun d => kronEnc (fs d.1)) <| Sum.elim (fun b => revP (2 ^ n) (kronEnc (fs b.1))) <|
    Sum.elim (fun h => hUA fs γ (stmts h.1)) <|
      Sum.elim (fun j => openAG (2 ^ n) (hUA fs γ (stmts j)) (hKA fs (stmts j))) <|
        Sum.elim (fun j => openHG (2 ^ n) (hUA fs γ (stmts j)) (hKA fs (stmts j)))
          (fun x => hquotA fs γ θ (stmts x.1.1.1) x.1.2)

lemma apolys_mem (fs : ι → Table F n) (stmts : Fin J → AStmt F ι n) (γ θ : F)
    (s : AWord stmts) : apolys fs stmts γ θ s ∈ degreeLT F (2 ^ n) := by
  rcases s with d | b | h | j | j | x
  · exact kronEnc_mem_degreeLT _
  · exact revP_mem _ _
  · exact hUA_mem _ _ _
  · exact openAG_mem _ _ _
  · exact openHG_mem _ _ _
  · exact hquotA_mem _ _ _ _ _

noncomputable def aU0 (fs : ι → Table F n) (stmts : Fin J → AStmt F ι n) (hJ : 1 ≤ J)
    (γ θ β : F) : F[X] :=
  ∑ s, C (β ^ ((aenum stmts hJ s : Fin (tA stmts + 1)) : ℕ)) * apolys fs stmts γ θ s

lemma aU0_mem (fs : ι → Table F n) (stmts : Fin J → AStmt F ι n) (hJ : 1 ≤ J) (γ θ β : F) :
    aU0 fs stmts hJ γ θ β ∈ degreeLT F (2 ^ n) :=
  Submodule.sum_mem _ (fun s _ => by
    rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (apolys_mem fs stmts γ θ s))

/-- The honest prover of `Π_Batch` on affine forms for the tables `fs`. -/
noncomputable def honestA (fs : ι → Table F n) (stmts : Fin J → AStmt F ι n) (hJ : 1 ≤ J)
    (ℓ : ℕ) : BProver F L J where
  wQ γ j := ev L (hUA fs γ (stmts j))
  y1 γ θ j := hy1A fs γ θ (stmts j)
  y3 γ _ j := hy3A fs γ (stmts j)
  wA γ _ j := ev L (openAG (2 ^ n) (hUA fs γ (stmts j)) (hKA fs (stmts j)))
  ft γ θ β := honestFT (aU0 fs stmts hJ γ θ β) ℓ

/-- The honest words are the codewords of `apolys`, when the statements hold and no pole of a
Hadamard check lies in `L`. -/
theorem awords_honest (fs : ι → Table F n) (stmts : Fin J → AStmt F ι n)
    (hholds : ∀ j, (stmts j).Holds fs) (γ θ : F)
    (hpoles : (∃ j, (stmts j).isHad = true) → ∀ ξ : L, xv' ξ ≠ γ * θ ∧ xv' ξ ≠ θ ∧ xv' ξ ≠ γ)
    (s : AWord stmts) :
    awords (n := n) (fun i => encode L (fs i)) stmts (fun j => ev L (hUA fs γ (stmts j)))
      (fun j => hy1A fs γ θ (stmts j)) (fun j => hy3A fs γ (stmts j))
      (fun j => ev L (openAG (2 ^ n) (hUA fs γ (stmts j)) (hKA fs (stmts j)))) γ θ s =
      ev L (apolys fs stmts γ θ s) := by
  rcases s with d | b | h | j | j | ⟨⟨⟨j, hj⟩, q⟩, hq⟩
  · rfl
  · exact wrev_ev (kronEnc_mem_degreeLT _)
  · rfl
  · rfl
  · show virtG n (UwA n (fun i => encode L (fs i)) (ev L (hUA fs γ (stmts j))) (stmts j))
      (KwA (fun i => encode L (fs i)) (stmts j))
      (ev L (openAG (2 ^ n) (hUA fs γ (stmts j)) (hKA fs (stmts j))))
      (vSA (hy3A fs γ (stmts j)) (stmts j)) =
      ev L (openHG (2 ^ n) (hUA fs γ (stmts j)) (hKA fs (stmts j)))
    have hh := hholds j
    have key : UwA n (fun i => encode L (fs i)) (ev L (hUA fs γ (stmts j))) (stmts j) =
        ev L (hUA fs γ (stmts j)) ∧
        KwA (fun i => encode L (fs i)) (stmts j) = ev L (hKA fs (stmts j)) ∧
        vSA (hy3A fs γ (stmts j)) (stmts j) =
          (hUA fs γ (stmts j) * hKA fs (stmts j)).coeff (2 ^ n - 1) := by
      revert hh
      cases stmts j with
      | eval a z v =>
        intro hh
        refine ⟨a.word_encode fs, rfl, ?_⟩
        show v = (kronEnc (a.table fs) * evalKer z).coeff (2 ^ n - 1)
        rw [← eval_table]; exact hh.symm
      | ip a a' S =>
        intro hh
        refine ⟨a.word_encode fs, ?_, ?_⟩
        · show wrev (2 ^ n) (a'.word _) = _
          rw [a'.word_encode fs]; exact wrev_ev (kronEnc_mem_degreeLT _)
        · show S = (kronEnc (a.table fs) * revP (2 ^ n) (kronEnc (a'.table fs))).coeff (2 ^ n - 1)
          rw [← inner_product]; exact hh.symm
      | had a a' k =>
        intro hh
        refine ⟨rfl, ?_, ?_⟩
        · show wrev (2 ^ n) (a'.word _) = _
          rw [a'.word_encode fs]; exact wrev_ev (kronEnc_mem_degreeLT _)
        · show (kronEnc (k.table fs)).eval γ =
            (kronEnc (gscale γ (a.table fs)) * revP (2 ^ n) (kronEnc (a'.table fs))).coeff (2 ^ n - 1)
          rw [eval_c_eq (a.table fs) (a'.table fs) (k.table fs) hh γ, inner_product]
    rw [key.1, key.2.1, key.2.2]
    exact virtG_honest (hUA_mem _ _ _) (hKA_mem _ _)
  · have hp := hpoles ⟨j, hj⟩
    show quotWA (fun i => encode L (fs i)) (ev L (hUA fs γ (stmts j))) (hy1A fs γ θ (stmts j))
      (hy3A fs γ (stmts j)) γ θ (stmts j) q = ev L (hquotA fs γ θ (stmts j) q)
    clear hq
    revert hj
    cases stmts j with
    | eval a z v => intro hj; simp [AStmt.isHad] at hj
    | ip a a' S => intro hj; simp [AStmt.isHad] at hj
    | had a a' k =>
      intro _
      fin_cases q
      · show qword (a.word _) ((kronEnc (a.table fs)).eval (γ * θ)) (γ * θ) =
          ev L (divq (kronEnc (a.table fs)) (γ * θ))
        rw [a.word_encode fs]
        exact (deep_honest (kronEnc_mem_degreeLT _) _ (fun ξ => (hp ξ).1)).1
      · show qword (ev L (kronEnc (gscale γ (a.table fs)))) ((kronEnc (a.table fs)).eval (γ * θ)) θ =
          ev L (divq (kronEnc (gscale γ (a.table fs))) θ)
        rw [← eval_gscale]
        exact (deep_honest (kronEnc_mem_degreeLT _) _ (fun ξ => (hp ξ).2.1)).1
      · show qword (k.word _) ((kronEnc (k.table fs)).eval γ) γ = ev L (divq (kronEnc (k.table fs)) γ)
        rw [k.word_encode fs]
        exact (deep_honest (kronEnc_mem_degreeLT _) _ (fun ξ => (hp ξ).2.2)).1

omit [DecidableEq ι] in
/-- The honest values pass the direct checks. -/
lemma honestA_dirOK (fs : ι → Table F n) (stmts : Fin J → AStmt F ι n) (γ θ : F) :
    DirOK stmts (fun j => hy1A fs γ θ (stmts j)) (fun j => hy3A fs γ (stmts j)) γ θ := by
  intro j a a' k hs
  refine ⟨fun ha => ?_, fun hk => ?_⟩
  · show (kronEnc a.p).eval (γ * θ) = hy1A fs γ θ (stmts j)
    rw [hs]; show _ = (kronEnc (a.table fs)).eval (γ * θ)
    rw [AForm.table_pub fs ha]
  · show (kronEnc k.p).eval γ = hy3A fs γ (stmts j)
    rw [hs]; show _ = (kronEnc (k.table fs)).eval γ
    rw [AForm.table_pub fs hk]

/-- **Proposition affine (completeness):** if `w_i = Enc^T(f_i)` and every statement holds for
the tables of its forms, the honest prover is accepted whenever no pole of a Hadamard check lies
in `L`. -/
theorem honestA_accepts {m ℓ R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (fs : ι → Table F (m + ℓ)) (stmts : Fin J → AStmt F ι (m + ℓ)) (hJ : 1 ≤ J)
    (hholds : ∀ j, (stmts j).Holds fs) (γ θ β : F)
    (hpoles : (∃ j, (stmts j).isHad = true) → ∀ ξ : L, xv' ξ ≠ γ * θ ∧ xv' ξ ≠ θ ∧ xv' ξ ≠ γ)
    (r' : ℕ → F) {κ : ℕ} (ξ : Fin κ → L) :
    (honestA (L := L) fs stmts hJ ℓ).AcceptsA ℓ (fun i => encode L (fs i)) stmts hJ γ θ β r' ξ := by
  refine ⟨honestA_dirOK fs stmts γ θ, ?_⟩
  have e : (honestA (L := L) fs stmts hJ ℓ).w0A (fun i => encode L (fs i)) stmts hJ γ θ β =
      ev L (aU0 fs stmts hJ γ θ β) := by
    show wbatA (fun i => encode L (fs i)) stmts hJ (fun j => ev L (hUA fs γ (stmts j)))
      (fun j => hy1A fs γ θ (stmts j)) (fun j => hy3A fs γ (stmts j))
      (fun j => ev L (openAG (2 ^ (m + ℓ)) (hUA fs γ (stmts j)) (hKA fs (stmts j)))) γ θ β = _
    unfold wbatA
    simp_rw [awords_honest fs stmts hholds γ θ hpoles]
    funext x
    simp [aU0, ev, eval_finset_sum, Finset.sum_apply]
  rw [e]
  exact honestFT_accepts hL _ r' ξ

theorem honestA_causal (fs : ι → Table F n) (stmts : Fin J → AStmt F ι n) (hJ : 1 ≤ J)
    (ℓ : ℕ) : (honestA (L := L) fs stmts hJ ℓ).Causal := by
  intro γ θ β j r1 r2 h
  simp only [honestA, honestFT]
  rw [pfoldUp_congr _ j h]

theorem honestA_DegOK {m ℓ : ℕ} (fs : ι → Table F (m + ℓ))
    (stmts : Fin J → AStmt F ι (m + ℓ)) (hJ : 1 ≤ J) :
    (honestA (L := L) fs stmts hJ ℓ).DegOK m :=
  fun γ θ β => honestFT_DegOK (aU0_mem fs stmts hJ γ θ β)

/-- **Proposition affine (completeness, probability):** the honest prover is accepted with
probability at least `1 - 3M/|F|`. -/
theorem honestA_prob [Fintype F] [DecidableEq F] [Fintype L] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (fs : ι → Table F (m + ℓ))
    (stmts : Fin J → AStmt F ι (m + ℓ)) (hJ : 1 ≤ J) (hholds : ∀ j, (stmts j).Holds fs) (κ : ℕ) :
    1 - 3 * (Nat.card L : ℚ) / Fintype.card F ≤
      (honestA (L := L) fs stmts hJ ℓ).accProbA ℓ κ (fun i => encode L (fs i)) stmts hJ := by
  classical
  haveI : Nonempty ((F × (Fin ℓ → F)) × (Fin κ → L)) := ⟨⟨⟨0, fun _ => 0⟩, fun _ => 1⟩⟩
  refine (prob_poles_ge (L := L)).trans ?_
  rw [← prob_fst (fun p : F × F => ∀ ξ : L, xv' ξ ≠ p.1 * p.2 ∧ xv' ξ ≠ p.2 ∧ xv' ξ ≠ p.1)
    (B := (F × (Fin ℓ → F)) × (Fin κ → L))]
  exact prob_mono (fun ω hω => honestA_accepts hL fs stmts hJ hholds _ _ _ (fun _ => hω) _ _)

end Complete

end KroneckerFRI
