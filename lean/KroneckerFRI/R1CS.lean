/-
KroneckerFRI/R1CS.lean
§5.3 of the research note "Sumcheck-free hypercube inner products": the R1CS argument without
sumcheck, end to end (Theorem r1cs).

Modelling.
* Tables are hypercube tables `Table F n`, numbered by `bitsToNat` (`hcNum`).
* The committed words are named by `RW`: the witness `w`, `a_0, a_1, a_2` (for `Az, Bz, Cz`),
  the index `row_j, col_j, val_j, m_R, m_C` (committed honestly, `Enc^T` of the honest tables),
  the lincheck words `e_j, ζ_j, p_j` (round 1, functions of `η`) and `φ^R_j, ψ^R, φ^C_j, ψ^C`
  (round 2, functions of `η, (y_R, x_R), (y_C, x_C)`).
* A deterministic prover (`R1Prover`) gives its words and the sums `s_j` as functions of the
  challenges, and a prover of `Π_Batch` on affine forms for each `τ = (η, (y_R, x_R), (y_C, x_C))`.
* The 21 statements of step 4 (`r1stmts`) are statements on affine forms (`AffineBatch.lean`);
  `z = x̂ + w` is the affine form of the column lookup.
-/
import KroneckerFRI.AffineBatch
import KroneckerFRI.Lincheck

set_option autoImplicit false

open Polynomial Finset KBFold

namespace KroneckerFRI

variable {F : Type*} [Field F] {L : Subgroup Fˣ}

section R1CS

variable {n : ℕ}

/-- The numbering `bitsToNat` of the hypercube. -/
def hcNum (n : ℕ) : Numbering (Fin n → Bool) :=
  ⟨bitsToNat, bitsToNat_injective, fun w => by simpa using bitsToNat_lt w⟩

/-- The names of the committed words. -/
inductive RW
  | w | a (j : Fin 3) | row (j : Fin 3) | col (j : Fin 3) | val (j : Fin 3) | mR | mC
  | e (j : Fin 3) | ζ (j : Fin 3) | p (j : Fin 3) | φR (j : Fin 3) | ψR | φC (j : Fin 3) | ψC
  deriving DecidableEq

variable (F n) in
/-- An R1CS instance: the three sparse matrices (entry `k` of `M_j` is
`(row_j k, col_j k, val_j k)`), the input positions `I` and the public input table `x̂`. -/
structure R1CSInst where
  row : Fin 3 → (Fin n → Bool) → (Fin n → Bool)
  col : Fin 3 → (Fin n → Bool) → (Fin n → Bool)
  val : Fin 3 → Table F n
  I : Finset (Fin n → Bool)
  x : Table F n

/-- The `0/1` table `χ` of the input positions. -/
def R1CSInst.chi (inst : R1CSInst F n) : Table F n := fun u => if u ∈ inst.I then 1 else 0

/-- **The R1CS relation** for the commitments `(w_w, w_a, w_b, w_c)`: tables within fibre
distance `δ`, `w = 0` on `I`, and with `z = x̂ + w`: `a_j = M_j z` and `a_0 ∘ a_1 = a_2`. -/
def R1CSRel (δ : ℚ) (inst : R1CSInst F n) (ww : L → F) (wa : Fin 3 → L → F) : Prop :=
  ∃ (wt : Table F n) (atab : Fin 3 → Table F n), fibDist ww (encode L wt) ≤ δ ∧
    (∀ j, fibDist (wa j) (encode L (atab j)) ≤ δ) ∧ (∀ u ∈ inst.I, wt u = 0) ∧
    (∀ j, atab j = matVec inst.row inst.col inst.val (inst.x + wt) j) ∧
    ∀ u, atab 0 u * atab 1 u = atab 2 u

variable (F L) in
/-- A deterministic prover of the R1CS argument. -/
structure R1Prover where
  ww : L → F
  wa : Fin 3 → L → F
  we : F → Fin 3 → L → F
  wz : F → Fin 3 → L → F
  wp : F → Fin 3 → L → F
  wφR : F → F × F → F × F → Fin 3 → L → F
  wψR : F → F × F → F × F → L → F
  wφC : F → F × F → F × F → Fin 3 → L → F
  wψC : F → F × F → F × F → L → F
  s : F → F × F → F × F → Fin 3 → F
  batch : F → F × F → F × F → BProver F L 21

/-- The honest index tables. -/
def rowTab (inst : R1CSInst F n) (j : Fin 3) : Table F n := fun k => (bitsToNat (inst.row j k) : F)
def colTab (inst : R1CSInst F n) (j : Fin 3) : Table F n := fun k => (bitsToNat (inst.col j k) : F)

/-- The committed words at `τ = (η, (y_R, x_R), (y_C, x_C))`. -/
noncomputable def r1ws (inst : R1CSInst F n) (P : R1Prover F L) (τ : F × ((F × F) × (F × F))) :
    RW → L → F
  | .w => P.ww
  | .a j => P.wa j
  | .row j => encode L (rowTab inst j)
  | .col j => encode L (colTab inst j)
  | .val j => encode L (inst.val j)
  | .mR => encode L (mult inst.row)
  | .mC => encode L (mult inst.col)
  | .e j => P.we τ.1 j
  | .ζ j => P.wz τ.1 j
  | .p j => P.wp τ.1 j
  | .φR j => P.wφR τ.1 τ.2.1 τ.2.2 j
  | .ψR => P.wψR τ.1 τ.2.1 τ.2.2
  | .φC j => P.wφC τ.1 τ.2.1 τ.2.2 j
  | .ψC => P.wψC τ.1 τ.2.1 τ.2.2

/-! ### The affine forms and the statements -/

/-- The form of one committed word. -/
def cf (i : RW) : AForm F RW n := ⟨{i}, fun _ => 1, 0⟩
/-- A public table. -/
def pubF (t : Table F n) : AForm F RW n := ⟨∅, fun _ => 0, t⟩
/-- `c w_i + t`. -/
def lin1 (i : RW) (c : F) (t : Table F n) : AForm F RW n := ⟨{i}, fun _ => c, t⟩
/-- `c₁ w_{i₁} + c₂ w_{i₂} + t`. -/
def lin2 (i₁ : RW) (c₁ : F) (i₂ : RW) (c₂ : F) (t : Table F n) : AForm F RW n :=
  ⟨{i₁, i₂}, fun i => if i = i₁ then c₁ else c₂, 0 + t⟩
/-- `∑_j w_{φ_j} - w_ψ`. -/
def sumF (φ : Fin 3 → RW) (ψ : RW) : AForm F RW n :=
  ⟨{φ 0, φ 1, φ 2, ψ}, fun i => if i = ψ then -1 else 1, 0⟩

/-- `1`, `η^w`. -/
def oneT : Table F n := fun _ => 1
def geoT (η : F) : Table F n := fun w => η ^ bitsToNat w

/-- The five statements of matrix `j`: `IP(a_j, G_η, s_j)`, `IP(val_j, p_j, s_j)`,
`Had(e_j, ζ_j, p_j)`, `Had(φ^R_j, x_R 1 - row_j - y_R e_j, 1)`,
`Had(φ^C_j, x_C 1 - col_j - y_C ζ_j, 1)`. -/
def r1blk (P : R1Prover F L) (τ : F × ((F × F) × (F × F))) (j : Fin 3) : Fin 5 → AStmt F RW n :=
  ![.ip (cf (.a j)) (pubF (geoT τ.1)) (P.s τ.1 τ.2.1 τ.2.2 j),
    .ip (cf (.val j)) (cf (.p j)) (P.s τ.1 τ.2.1 τ.2.2 j),
    .had (cf (.e j)) (cf (.ζ j)) (cf (.p j)),
    .had (cf (.φR j)) (lin2 (.row j) (-1) (.e j) (-τ.2.1.1) (fun _ => τ.2.1.2)) (pubF oneT),
    .had (cf (.φC j)) (lin2 (.col j) (-1) (.ζ j) (-τ.2.2.1) (fun _ => τ.2.2.2)) (pubF oneT)]

/-- The six other statements: `Had(ψ^R, x_R 1 - id - y_R G_η, m_R)`, `IP(∑_j φ^R_j - ψ^R, 1, 0)`,
`Had(ψ^C, x_C 1 - id - y_C (x̂ + w), m_C)`, `IP(∑_j φ^C_j - ψ^C, 1, 0)`, `Had(a_0, a_1, a_2)`,
`Had(w, χ, 0)`. -/
def r1once (inst : R1CSInst F n) (τ : F × ((F × F) × (F × F))) : Fin 6 → AStmt F RW n :=
  ![.had (cf .ψR) (pubF (fun w => τ.2.1.2 - bitsToNat w - τ.2.1.1 * τ.1 ^ bitsToNat w)) (cf .mR),
    .ip (sumF .φR .ψR) (pubF oneT) 0,
    .had (cf .ψC) (lin1 .w (-τ.2.2.1) (fun w => τ.2.2.2 - bitsToNat w - τ.2.2.1 * inst.x w))
      (cf .mC),
    .ip (sumF .φC .ψC) (pubF oneT) 0,
    .had (cf (.a 0)) (cf (.a 1)) (cf (.a 2)),
    .had (cf .w) (pubF inst.chi) (pubF 0)]

/-- The 21 statements of step 4 (statement `5j + q` is `r1blk j q`, statement `15 + q` is
`r1once q`). -/
def r1stmts (inst : R1CSInst F n) (P : R1Prover F L) (τ : F × ((F × F) × (F × F))) :
    Fin 21 → AStmt F RW n := fun i =>
  if h : i.val < 15 then r1blk P τ ⟨i.val / 5, by omega⟩ ⟨i.val % 5, by omega⟩
  else r1once inst τ ⟨i.val - 15, by omega⟩

lemma r1stmts_blk (inst : R1CSInst F n) (P : R1Prover F L) (τ : F × ((F × F) × (F × F)))
    (j : Fin 3) (q : Fin 5) :
    r1stmts inst P τ ⟨5 * j + q, by omega⟩ = r1blk P τ j q := by
  unfold r1stmts
  rw [dif_pos (show (5 * (j : ℕ) + q) < 15 by omega)]
  congr 1
  · ext; simp only; omega
  · ext; simp only; omega

lemma r1stmts_once (inst : R1CSInst F n) (P : R1Prover F L) (τ : F × ((F × F) × (F × F)))
    (q : Fin 6) : r1stmts inst P τ ⟨15 + q, by omega⟩ = r1once inst τ q := by
  unfold r1stmts
  rw [dif_neg (show ¬ (15 + (q : ℕ)) < 15 by omega)]
  congr 1
  ext; simp only; omega

/-! ### Tables of the forms -/

lemma table_cf (fs : RW → Table F n) (i : RW) : (cf i : AForm F RW n).table fs = fs i := by
  funext w; simp [cf, AForm.table]

lemma table_pubF (fs : RW → Table F n) (t : Table F n) : (pubF t).table fs = t := by
  funext w; simp [pubF, AForm.table]

lemma table_lin1 (fs : RW → Table F n) (i : RW) (c : F) (t : Table F n) :
    (lin1 i c t).table fs = fun w => c * fs i w + t w := by
  funext w; simp [lin1, AForm.table]

lemma table_lin2 (fs : RW → Table F n) {i₁ i₂ : RW} (h : i₁ ≠ i₂) (c₁ c₂ : F) (t : Table F n) :
    (lin2 i₁ c₁ i₂ c₂ t).table fs = fun w => c₁ * fs i₁ w + c₂ * fs i₂ w + t w := by
  funext w
  simp [lin2, AForm.table, sum_pair h, if_neg h.symm]

lemma table_sumF (fs : RW → Table F n) (φ : Fin 3 → RW) (ψ : RW)
    (h01 : φ 0 ≠ φ 1) (h02 : φ 0 ≠ φ 2) (h12 : φ 1 ≠ φ 2) (h0 : φ 0 ≠ ψ) (h1 : φ 1 ≠ ψ)
    (h2 : φ 2 ≠ ψ) :
    (sumF φ ψ).table fs = fun w => fs (φ 0) w + fs (φ 1) w + fs (φ 2) w - fs ψ w := by
  funext w
  simp only [sumF, AForm.table, Pi.zero_apply, add_zero]
  rw [sum_insert (by simp [h01, h02, h0]), sum_insert (by simp [h12, h1]),
    sum_insert (by simp [h2]), sum_singleton]
  simp only [if_neg h0, if_neg h1, if_neg h2, if_true]
  ring

/-! ### Decoding -/

/-- The table of a word within fibre distance `δ` of `Enc^T`, if there is one. -/
noncomputable def dec (δ : ℚ) (w : L → F) : Table F n := by
  classical
  exact if h : ∃ f : Table F n, fibDist w (encode L f) ≤ δ then Classical.choose h else 0

lemma dec_eq [Fintype F] [DecidableEq F] {m ℓ R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hR : 2 ≤ R) {δ : ℚ} (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) {w : L → F} {f : Table F (m + ℓ)}
    (h : fibDist w (encode L f) ≤ δ) : dec δ w = f := by
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
  have hex : ∃ f : Table F (m + ℓ), fibDist w (encode L f) ≤ δ := ⟨f, h⟩
  unfold dec
  simp only [dif_pos hex]
  exact encode_fib_unique hNM hneg h2 hδ' w (Classical.choose_spec hex) h

lemma fibDist_self (w : L → F) : fibDist w w = 0 := by
  simp [fibDist, fibBad]

/-- The table-level prover of the lincheck: the decodings of the prover's words. -/
noncomputable def decProver (δ : ℚ) (P : R1Prover F L) : LinProver F 3 (Fin n → Bool) where
  e η j := dec δ (P.we η j)
  ζ η j := dec δ (P.wz η j)
  p η j := dec δ (P.wp η j)
  φR η cR cC j := dec δ (P.wφR η cR cC j)
  ψR η cR cC := dec δ (P.wψR η cR cC)
  φC η cR cC j := dec δ (P.wφC η cR cC j)
  ψC η cR cC := dec δ (P.wψC η cR cC)
  s := P.s

/-! ### From a batch witness to the lincheck statements -/

section Bridge

variable (inst : R1CSInst F n) (P : R1Prover F L) (τ : F × ((F × F) × (F × F)))

/-- Every committed word is read by some statement. -/
lemma r1_mem (i : RW) : i ∈ DsetA (r1stmts inst P τ) ∪ BsetA (r1stmts inst P τ) := by
  have hbD : ∀ j q, (r1blk P τ j q).direct ⊆ DsetA (r1stmts inst P τ) := fun j q x hx =>
    mem_DsetA (j := ⟨5 * j + q, by omega⟩) (by rw [r1stmts_blk]; exact hx)
  have hbB : ∀ j q, (r1blk P τ j q).rev ⊆ BsetA (r1stmts inst P τ) := fun j q x hx =>
    mem_BsetA (j := ⟨5 * j + q, by omega⟩) (by rw [r1stmts_blk]; exact hx)
  have hoD : ∀ q, (r1once inst τ q).direct ⊆ DsetA (r1stmts inst P τ) := fun q x hx =>
    mem_DsetA (j := ⟨15 + q, by omega⟩) (by rw [r1stmts_once]; exact hx)
  have hoB : ∀ q, (r1once inst τ q).rev ⊆ BsetA (r1stmts inst P τ) := fun q x hx =>
    mem_BsetA (j := ⟨15 + q, by omega⟩) (by rw [r1stmts_once]; exact hx)
  cases i with
  | w => exact mem_union_left _ (hoD 5 (by simp [r1once, AStmt.direct, cf, pubF]))
  | a j => exact mem_union_left _ (hbD j 0 (by simp [r1blk, AStmt.direct, cf]))
  | row j => exact mem_union_right _ (hbB j 3 (by simp [r1blk, AStmt.rev, lin2]))
  | col j => exact mem_union_right _ (hbB j 4 (by simp [r1blk, AStmt.rev, lin2]))
  | val j => exact mem_union_left _ (hbD j 1 (by simp [r1blk, AStmt.direct, cf]))
  | mR => exact mem_union_left _ (hoD 0 (by simp [r1once, AStmt.direct, cf]))
  | mC => exact mem_union_left _ (hoD 2 (by simp [r1once, AStmt.direct, cf]))
  | e j => exact mem_union_left _ (hbD j 2 (by simp [r1blk, AStmt.direct, cf]))
  | ζ j => exact mem_union_right _ (hbB j 2 (by simp [r1blk, AStmt.rev, cf]))
  | p j => exact mem_union_left _ (hbD j 2 (by simp [r1blk, AStmt.direct, cf]))
  | φR j => exact mem_union_left _ (hbD j 3 (by simp [r1blk, AStmt.direct, cf, pubF]))
  | ψR => exact mem_union_left _ (hoD 0 (by simp [r1once, AStmt.direct, cf]))
  | φC j => exact mem_union_left _ (hbD j 4 (by simp [r1blk, AStmt.direct, cf, pubF]))
  | ψC => exact mem_union_left _ (hoD 2 (by simp [r1once, AStmt.direct, cf]))

end Bridge

/-- **Bridge.** A witness of the batch relation for the 21 statements gives, for the decodings
of the prover's words, all the lincheck statements (`HoldsLin`), `a_0 ∘ a_1 = a_2` and
`w ∘ χ = 0`. -/
theorem r1_bridge [Fintype F] [DecidableEq F] {m ℓ R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hR : 2 ≤ R) {δ : ℚ} (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (inst : R1CSInst F (m + ℓ)) (P : R1Prover F L) (τ : F × ((F × F) × (F × F)))
    (fs : RW → Table F (m + ℓ)) (hrel : RelBatchA δ (r1ws inst P τ) (r1stmts inst P τ) fs) :
    HoldsLin (hcNum (m + ℓ)) inst.row inst.col inst.val (inst.x + dec δ P.ww)
        (fun j => dec δ (P.wa j)) (decProver δ P) τ.1 τ.2.1 τ.2.2 ∧
      (∀ u : Fin (m + ℓ) → Bool, dec δ (P.wa 0) u * dec δ (P.wa 1) u = dec δ (P.wa 2) u) ∧
      ∀ u, dec (n := m + ℓ) δ P.ww u * inst.chi u = 0 := by
  obtain ⟨hd, hH⟩ := hrel
  have hfs : ∀ i, fs i = dec δ (r1ws inst P τ i) := fun i =>
    (dec_eq hL hR hδ (hd i (r1_mem inst P τ i))).symm
  have henc : ∀ t : Table F (m + ℓ), dec δ (encode L t) = t := fun t =>
    dec_eq hL hR hδ (by rw [fibDist_self]; exact hδ0.le)
  have hB : ∀ j q, (r1blk P τ j q).Holds fs := fun j q => by
    rw [← r1stmts_blk inst]; exact hH _
  have hO : ∀ q, (r1once inst τ q).Holds fs := fun q => by
    rw [← r1stmts_once inst P]; exact hH _
  obtain ⟨η, ⟨yR, xR⟩, ⟨yC, xC⟩⟩ := τ
  have hsum : ∀ φ : Fin 3 → RW, ∀ ψ : RW, (∀ j, φ j ≠ ψ) → (∀ j j', j ≠ j' → φ j ≠ φ j') →
      (AStmt.ip (sumF φ ψ) (pubF oneT) 0 : AStmt F RW (m + ℓ)).Holds fs →
      ∑ jk : Fin 3 × (Fin (m + ℓ) → Bool), fs (φ jk.1) jk.2 - ∑ w, fs ψ w = 0 := by
    intro φ ψ hψ hφ h
    simp only [AStmt.Holds] at h
    rw [table_sumF _ _ _ (hφ 0 1 (by decide)) (hφ 0 2 (by decide)) (hφ 1 2 (by decide)) (hψ 0)
      (hψ 1) (hψ 2), table_pubF] at h
    simp only [oneT, mul_one, sum_sub_distrib, sum_add_distrib] at h
    rw [Fintype.sum_prod_type, Fin.sum_univ_three]
    linear_combination h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j
    have h : (AStmt.ip (cf (RW.a j)) (pubF (geoT η)) (P.s η (yR, xR) (yC, xC) j) :
        AStmt F RW (m + ℓ)).Holds fs := hB j 0
    simp only [AStmt.Holds, table_cf, table_pubF, geoT] at h
    rw [hfs] at h
    simpa [decProver, hcNum, r1ws] using h
  · intro j
    have h : (AStmt.ip (cf (RW.val j)) (cf (RW.p j)) (P.s η (yR, xR) (yC, xC) j) :
        AStmt F RW (m + ℓ)).Holds fs := hB j 1
    simp only [AStmt.Holds, table_cf] at h
    rw [hfs (RW.val j), hfs (RW.p j)] at h
    simpa [decProver, r1ws, henc] using h
  · intro j k
    have h : (AStmt.had (cf (RW.e j)) (cf (RW.ζ j)) (cf (RW.p j)) :
        AStmt F RW (m + ℓ)).Holds fs := hB j 2
    simp only [AStmt.Holds, table_cf] at h
    have h' := h k
    rw [hfs (RW.e j), hfs (RW.ζ j), hfs (RW.p j)] at h'
    simpa [decProver, r1ws] using h'
  · intro j k
    have h : (AStmt.had (cf (RW.φR j)) (lin2 (RW.row j) (-1) (RW.e j) (-yR) (fun _ => xR))
        (pubF oneT) : AStmt F RW (m + ℓ)).Holds fs := hB j 3
    simp only [AStmt.Holds] at h
    have h' := h k
    rw [table_cf, table_lin2 _ (by simp), table_pubF] at h'
    simp only [hfs (RW.φR j), hfs (RW.row j), hfs (RW.e j), r1ws, henc, rowTab, oneT] at h'
    simp only [decProver, hcNum]
    linear_combination h'
  · intro w
    have h : (AStmt.had (cf RW.ψR) (pubF (fun w => xR - bitsToNat w - yR * η ^ bitsToNat w))
        (cf RW.mR) : AStmt F RW (m + ℓ)).Holds fs := hO 0
    simp only [AStmt.Holds, table_cf, table_pubF] at h
    have h' := h w
    rw [hfs RW.ψR, hfs RW.mR] at h'
    simp only [r1ws, henc] at h'
    simp only [decProver, hcNum]
    linear_combination h'
  · have h := hsum RW.φR RW.ψR (fun j => by simp) (fun j j' hjj' => by simpa using hjj') (hO 1)
    simp only [hfs, r1ws] at h
    simpa [decProver] using h
  · intro j k
    have h : (AStmt.had (cf (RW.φC j)) (lin2 (RW.col j) (-1) (RW.ζ j) (-yC) (fun _ => xC))
        (pubF oneT) : AStmt F RW (m + ℓ)).Holds fs := hB j 4
    simp only [AStmt.Holds] at h
    have h' := h k
    rw [table_cf, table_lin2 _ (by simp), table_pubF] at h'
    simp only [hfs (RW.φC j), hfs (RW.col j), hfs (RW.ζ j), r1ws, henc, colTab, oneT] at h'
    simp only [decProver, hcNum]
    linear_combination h'
  · intro w
    have h : (AStmt.had (cf RW.ψC) (lin1 RW.w (-yC) (fun w => xC - bitsToNat w - yC * inst.x w))
        (cf RW.mC) : AStmt F RW (m + ℓ)).Holds fs := hO 2
    simp only [AStmt.Holds] at h
    have h' := h w
    rw [table_cf, table_lin1, table_cf] at h'
    simp only [hfs RW.ψC, hfs RW.w, hfs RW.mC, r1ws, henc] at h'
    simp only [decProver, hcNum, Pi.add_apply]
    linear_combination h'
  · have h := hsum RW.φC RW.ψC (fun j => by simp) (fun j j' hjj' => by simpa using hjj') (hO 3)
    simp only [hfs, r1ws] at h
    simpa [decProver] using h
  · intro u
    have h : (AStmt.had (cf (RW.a 0)) (cf (RW.a 1)) (cf (RW.a 2)) :
        AStmt F RW (m + ℓ)).Holds fs := hO 4
    simp only [AStmt.Holds, table_cf] at h
    have h' := h u
    rw [hfs (RW.a 0), hfs (RW.a 1), hfs (RW.a 2)] at h'
    exact h'
  · intro u
    have h : (AStmt.had (cf RW.w) (pubF inst.chi) (pubF 0) : AStmt F RW (m + ℓ)).Holds fs := hO 5
    simp only [AStmt.Holds, table_cf, table_pubF] at h
    have h' := h u
    rw [hfs RW.w] at h'
    simpa using h'

/-! ### The number of words: `t + 1 = 127` -/

section Count

/-- The supports read directly, reversed, the Hadamard positions and the quotient words of the
21 statements (they do not depend on the instance, the prover or the challenges). -/
def shD : Fin 21 → Finset RW :=
  ![{.a 0}, {.val 0}, {.e 0} ∪ {.p 0}, {.φR 0} ∪ ∅, {.φC 0} ∪ ∅,
    {.a 1}, {.val 1}, {.e 1} ∪ {.p 1}, {.φR 1} ∪ ∅, {.φC 1} ∪ ∅,
    {.a 2}, {.val 2}, {.e 2} ∪ {.p 2}, {.φR 2} ∪ ∅, {.φC 2} ∪ ∅,
    {.ψR} ∪ {.mR}, {.φR 0, .φR 1, .φR 2, .ψR}, {.ψC} ∪ {.mC}, {.φC 0, .φC 1, .φC 2, .ψC},
    {.a 0} ∪ {.a 2}, {.w} ∪ ∅]

def shB : Fin 21 → Finset RW :=
  ![∅, {.p 0}, {.ζ 0}, {.row 0, .e 0}, {.col 0, .ζ 0},
    ∅, {.p 1}, {.ζ 1}, {.row 1, .e 1}, {.col 1, .ζ 1},
    ∅, {.p 2}, {.ζ 2}, {.row 2, .e 2}, {.col 2, .ζ 2},
    ∅, ∅, {.w}, ∅, {.a 1}, ∅]

def shH : Fin 21 → Bool :=
  ![false, false, true, true, true, false, false, true, true, true,
    false, false, true, true, true, true, false, true, false, true, true]

def shQ : Fin 21 → Fin 3 → Bool :=
  ![![false, false, false], ![false, false, false], ![true, true, true], ![true, true, false],
    ![true, true, false],
    ![false, false, false], ![false, false, false], ![true, true, true], ![true, true, false],
    ![true, true, false],
    ![false, false, false], ![false, false, false], ![true, true, true], ![true, true, false],
    ![true, true, false],
    ![true, true, true], ![false, false, false], ![true, true, true], ![false, false, false],
    ![true, true, true], ![true, true, false]]

variable (inst : R1CSInst F n) (P : R1Prover F L) (τ : F × ((F × F) × (F × F)))

lemma r1_direct (j : Fin 21) : (r1stmts inst P τ j).direct = shD j := by
  fin_cases j <;> rfl

lemma r1_rev (j : Fin 21) : (r1stmts inst P τ j).rev = shB j := by
  fin_cases j <;> rfl

lemma r1_isHad (j : Fin 21) : (r1stmts inst P τ j).isHad = shH j := by
  fin_cases j <;> rfl

lemma r1_qIn (j : Fin 21) (q : Fin 3) : (r1stmts inst P τ j).qIn q = shQ j q := by
  fin_cases j <;> fin_cases q <;> rfl

/-- **The number of words of the curve is `127`** (`t = 126`), for every instance, prover and
challenges: `23` words read directly, `17` reversed, `13` words `w_Q`, `21` words `w_A`, `21`
words `h` and `32` quotient words. -/
theorem tA_r1stmts : tA (r1stmts inst P τ) = 126 := by
  classical
  have hD : DsetA (r1stmts inst P τ) = univ.biUnion shD := by
    unfold DsetA; congr 1; funext j; exact r1_direct inst P τ j
  have hB : BsetA (r1stmts inst P τ) = univ.biUnion shB := by
    unfold BsetA; congr 1; funext j; exact r1_rev inst P τ j
  have hH : Fintype.card (HposA (r1stmts inst P τ)) = 13 := by
    rw [Fintype.card_subtype]
    simp only [r1_isHad inst P τ]
    decide
  have hQ : Fintype.card (QIdx (r1stmts inst P τ)) = 32 := by
    let e : QIdx (r1stmts inst P τ) ≃
        {y : Fin 21 × Fin 3 // (r1stmts inst P τ y.1).isHad = true ∧
          (r1stmts inst P τ y.1).qIn y.2 = true} :=
      { toFun := fun x => ⟨(x.1.1.1, x.1.2), x.1.1.2, x.2⟩
        invFun := fun y => ⟨(⟨y.1.1, y.2.1⟩, y.1.2), y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_subtype]
    simp only [r1_isHad inst P τ, r1_qIn inst P τ]
    decide
  unfold tA
  simp only [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin, hD, hB, hH, hQ]
  decide

end Count

/-! ### Theorem r1cs, end to end -/

/-- The verifier of the whole argument accepts at `τ` (lincheck challenges) and `ω` (the
challenges of `Π_Batch`: `(γ, θ)`, then `β` with the folding challenges, then the queries). -/
def R1Prover.Acc (inst : R1CSInst F n) (P : R1Prover F L) (ℓ κ : ℕ)
    (τ : F × ((F × F) × (F × F))) (ω : (F × F) × ((F × (Fin ℓ → F)) × (Fin κ → L))) : Prop :=
  (P.batch τ.1 τ.2.1 τ.2.2).AcceptsA ℓ (r1ws inst P τ) (r1stmts inst P τ) (by norm_num)
    ω.1.1 ω.1.2 ω.2.1.1 (extR ω.2.1.2) ω.2.2

/-- **Theorem r1cs (R1CS without sumcheck), end to end.** Let `N = 2^n` (`n = m + ℓ`),
`char F > 3N`, and let the index be honest. If `(w_w, w_a, w_b, w_c)` has no witness in the R1CS
relation, every prover whose batch provers are causal and send final polynomials in
`F[X]_{<N_ℓ}` is accepted with probability at most
`ε_Lin + 2(N-1)/|F| + tM/|F| + ε_fold + (1-δ)^κ` with `ε_Lin = (N - 1 + 2(N + N + 3N + N - 1))/|F|
= (13N - 3)/|F|` and `t = 126` (`tA_r1stmts`). -/
theorem r1cs_soundness [Fintype F] [DecidableEq F] [Fintype L] {m ℓ R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (hchar : ∀ k : ℕ, 1 ≤ k → k ≤ 3 * 2 ^ (m + ℓ) → (k : F) ≠ 0)
    (inst : R1CSInst F (m + ℓ)) (P : R1Prover F L)
    (hC : ∀ τ : F × ((F × F) × (F × F)), (P.batch τ.1 τ.2.1 τ.2.2).Causal)
    (hdeg : ∀ τ : F × ((F × F) × (F × F)), (P.batch τ.1 τ.2.1 τ.2.2).DegOK m) (κ : ℕ)
    (hno : ¬ R1CSRel δ inst P.ww P.wa) :
    prob (fun q : (F × ((F × F) × (F × F))) × ((F × F) × ((F × (Fin ℓ → F)) × (Fin κ → L))) =>
        P.Acc inst ℓ κ q.1 q.2) ≤
      ((2 ^ (m + ℓ) - 1 + 2 * (2 ^ (m + ℓ) + (2 ^ (m + ℓ) +
        (3 * 2 ^ (m + ℓ) + 2 ^ (m + ℓ) - 1))) : ℕ) : ℚ) / Fintype.card F +
      (2 * ((2 ^ (m + ℓ) - 1 : ℕ) : ℚ) / Fintype.card F +
        126 * 2 ^ (m + ℓ + R) / Fintype.card F + epsFold F (m + ℓ + R) ℓ +
          (1 - δ) ^ κ) := by
  classical
  haveI : Nonempty F := ⟨0⟩
  haveI : Nonempty L := ⟨1⟩
  set ε₂ : ℚ := 2 * ((2 ^ (m + ℓ) - 1 : ℕ) : ℚ) / Fintype.card F +
    126 * 2 ^ (m + ℓ + R) / Fintype.card F + epsFold F (m + ℓ + R) ℓ + (1 - δ) ^ κ
  have hδ1 : δ ≤ 1 := by
    have : (0 : ℚ) < 1 / 2 ^ R := by positivity
    linarith
  have hε : 0 ≤ ε₂ := by
    have h1 : 0 ≤ epsFold F (m + ℓ + R) ℓ := by
      unfold epsFold; exact sum_nonneg (fun j _ => by positivity)
    have h2 : (0 : ℚ) ≤ (1 - δ) ^ κ := pow_nonneg (by linarith) _
    have h3 : (0 : ℚ) ≤ 2 * ((2 ^ (m + ℓ) - 1 : ℕ) : ℚ) / Fintype.card F := by positivity
    have h4 : (0 : ℚ) ≤ 126 * 2 ^ (m + ℓ + R) / Fintype.card F := by positivity
    simp only [ε₂]; linarith
  -- the batch phase: Proposition affine
  have hbatch : ∀ τ : F × ((F × F) × (F × F)),
      (∀ fs, ¬ RelBatchA δ (r1ws inst P τ) (r1stmts inst P τ) fs) →
      prob (P.Acc inst ℓ κ τ) ≤ ε₂ := by
    intro τ hnw
    have h := soundness_A hL hR hℓ hδ0 hδ (P.batch τ.1 τ.2.1 τ.2.2) (hC τ) (hdeg τ) κ
      (r1ws inst P τ) (r1stmts inst P τ) (by norm_num) hnw
    rw [tA_r1stmts] at h
    push_cast at h
    exact h
  set N := 2 ^ (m + ℓ)
  have hW : Fintype.card (Fin (m + ℓ) → Bool) = N := by simp [N]
  have hmemU : ∀ τ i, i ∈ DsetA (r1stmts inst P τ) ∪ BsetA (r1stmts inst P τ) :=
    fun τ i => r1_mem inst P τ i
  by_cases hdec : (∃ f : Table F (m + ℓ), fibDist P.ww (encode L f) ≤ δ) ∧
      ∀ j, ∃ f : Table F (m + ℓ), fibDist (P.wa j) (encode L f) ≤ δ
  swap
  · -- a witness word has no decoding: the batch relation never has a witness
    have hall : ∀ τ, ∀ fs, ¬ RelBatchA δ (r1ws inst P τ) (r1stmts inst P τ) fs := by
      rintro τ fs ⟨hd, -⟩
      apply hdec
      exact ⟨⟨fs RW.w, hd RW.w (hmemU τ _)⟩, fun j => ⟨fs (RW.a j), hd (RW.a j) (hmemU τ _)⟩⟩
    refine (prob_two_phase (fun _ => False) (P.Acc inst ℓ κ) hε
      (fun τ _ => hbatch τ (hall τ))).trans ?_
    rw [prob_false, zero_add]
    exact le_add_of_nonneg_left (by positivity)
  obtain ⟨⟨fw, hfw⟩, hfa⟩ := hdec
  have hdw : dec δ P.ww = fw := dec_eq hL hR hδ hfw
  -- the lincheck phase: Theorem lin
  have hchar' : ∀ k : ℕ, 1 ≤ k → k ≤ 3 * Fintype.card (Fin (m + ℓ) → Bool) → (k : F) ≠ 0 := by
    rw [hW]; exact hchar
  have hno' : ¬ ((∀ j, (fun j => dec δ (P.wa j)) j =
        matVec inst.row inst.col inst.val (inst.x + dec δ P.ww) j) ∧
      ((∀ u : Fin (m + ℓ) → Bool, dec δ (P.wa 0) u * dec δ (P.wa 1) u = dec δ (P.wa 2) u) ∧
        ∀ u, dec (n := m + ℓ) δ P.ww u * inst.chi u = 0)) := by
    rintro ⟨hM, hab, hwχ⟩
    apply hno
    refine ⟨dec δ P.ww, fun j => dec δ (P.wa j), by rw [hdw]; exact hfw, fun j => ?_,
      fun u hu => ?_, hM, hab⟩
    · obtain ⟨f, hf⟩ := hfa j
      show fibDist (P.wa j) (encode L (dec δ (P.wa j))) ≤ δ
      rw [dec_eq hL hR hδ hf]; exact hf
    · have := hwχ u
      simpa [R1CSInst.chi, hu] using this
  have := r1cs_sound (hcNum (m + ℓ)) hchar' inst.row inst.col inst.val (inst.x + dec δ P.ww)
    (fun j => dec δ (P.wa j)) _ hno' (decProver δ P) (P.Acc inst ℓ κ) hε
    (fun τ hnot => hbatch τ (fun fs hfs => hnot (r1_bridge hL hR hδ0 hδ inst P τ fs hfs)))
  rw [hW] at this
  exact this

end R1CS

end KroneckerFRI
