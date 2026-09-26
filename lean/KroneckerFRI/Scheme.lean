/-
KroneckerFRI/Scheme.lean
§6 of the paper: the encoding (Definition 6.2, Lemma 6.3(1)–(2)), the virtual word
(Definition 6.5, Lemma 6.6), the evaluation protocol `Π_KF` (Definition 6.8), completeness
(Theorem 6.10) and Remark 6.9(1).

Modelling.
* `n = m + ℓ` variables; `L` is a smooth domain of order `M = 2^{n+R}`; the evaluation point is
  `z : Fin (m + ℓ) → F`.  Multilinear polynomials are given by their coefficient tables
  (`KroneckerFRI/Kronecker.lean`).
* A deterministic prover of `Π_KF` (`KFProver`) sends the round-1 oracle `w_A` and then, for each
  value of `β`, runs a prover of the folding test (`ft β`) on the batched word
  `w_0 = w + β w_A + β² h`.  By Proposition 5.28 (`KroneckerFRI/Arity.lean`) this covers every
  set `C` of committed levels: a prover of `Π^C_KF` is analysed through its induced prover.
* The challenge space is `(F × F^ℓ) × L^κ` (`β`, `r`, query points).
-/
import KroneckerFRI.Arity
import KroneckerFRI.Opening

set_option autoImplicit false

open Polynomial Finset KBFold

namespace KroneckerFRI

variable {F : Type*} [Field F]

/-- The value `ξ ∈ F` of a point `ξ ∈ L`. -/
abbrev xv' {L : Subgroup Fˣ} (ξ : L) : F := (((ξ : L) : Fˣ) : F)

/-! ### Definition 6.2 and Lemma 6.3 (encoding) -/

section Encoding

variable (L : Subgroup Fˣ)

/-- **Definition 6.2:** `Enc(f) = ev_L(U_f)`. -/
noncomputable def encode {n : ℕ} (α : Table F n) : L → F := ev L (kronEnc α)

variable {L}

theorem encode_mem_RS {n : ℕ} (α : Table F n) : encode L α ∈ RS L (2 ^ n) :=
  ev_mem_RS (kronEnc_mem_degreeLT α)

theorem encode_add {n : ℕ} (α β : Table F n) : encode L (α + β) = encode L α + encode L β := by
  simp [encode, kronEnc_add, ev_add]

theorem encode_smul {n : ℕ} (c : F) (α : Table F n) : encode L (c • α) = c • encode L α := by
  simp [encode, kronEnc_smul, ev_C_mul]

/-- **Lemma 6.3(1):** `P_{Enc(f)} = U_f`. -/
theorem polyOf_encode [Finite L] {n : ℕ} (hn : 2 ^ n ≤ Nat.card L) (α : Table F n) :
    polyOf (encode L α) = kronEnc α :=
  polyOf_ev (degreeLT_mono' hn (kronEnc_mem_degreeLT α))

/-- **Lemma 6.3(1):** `Enc` is injective … -/
theorem encode_injective [Finite L] {n : ℕ} (hn : 2 ^ n ≤ Nat.card L) :
    Function.Injective (encode L : Table F n → L → F) := by
  intro α β h
  have := ev_injOn hn (kronEnc_mem_degreeLT α) (kronEnc_mem_degreeLT β) h
  rw [← kronCoeffs_kronEnc α, ← kronCoeffs_kronEnc β, this]

/-- … and onto `𝒞_0 = RS[L, N]`. -/
theorem encode_surj [Finite L] {n : ℕ} (hn : 2 ^ n ≤ Nat.card L) {c : L → F}
    (hc : c ∈ RS L (2 ^ n)) : encode L (kronCoeffs n (polyOf c)) = c := by
  obtain ⟨hP, hev⟩ := polyOf_spec hn hc
  rw [encode, kronEnc_kronCoeffs hP, hev]

/-- **Lemma 6.3(2):** for `δ ≤ (1-ρ)/2`, every word is within fibre distance `δ` of `Enc(f)` for
at most one `f`. -/
theorem encode_fib_unique [Finite L] {n : ℕ} (hn : 2 ^ n ≤ Nat.card L) (hL : (-1 : Fˣ) ∈ L)
    (h2 : (2 : F) ≠ 0) {δ : ℚ} (hδ : δ ≤ (1 - rate L (2 ^ n)) / 2) (w : L → F)
    {α β : Table F n} (hα : fibDist w (encode L α) ≤ δ) (hβ : fibDist w (encode L β) ≤ δ) :
    α = β :=
  encode_injective hn (fib_unique hL h2 hδ w (encode_mem_RS α) (encode_mem_RS β) hα hβ)

/-- **Lemma 6.3(2)**, with the Hamming distance. -/
theorem encode_unique [Finite L] {n : ℕ} (hn : 2 ^ n ≤ Nat.card L) {δ : ℚ}
    (hδ : δ ≤ (1 - rate L (2 ^ n)) / 2) (w : L → F) {α β : Table F n}
    (hα : relDist w (encode L α) ≤ δ) (hβ : relDist w (encode L β) ≤ δ) : α = β :=
  encode_injective hn (RS_unique_decoding' δ hδ w (encode_mem_RS α) (encode_mem_RS β) hα hβ)

end Encoding

/-! ### Definition 6.5 and Lemma 6.6 (the virtual word) -/

section Virtual

variable {L : Subgroup Fˣ} {n : ℕ}

/-- **Definition 6.5 (virtual word):**
`h(ξ) = (ξ w(ξ) K_z(ξ) - w_A(ξ) - v ξ^N) / ξ^{N+1}`. -/
noncomputable def virt (w wA : L → F) (z : Fin n → F) (v : F) : L → F := fun ξ =>
  (xv' ξ * w ξ * (kernel z).eval (xv' ξ) - wA ξ - v * xv' ξ ^ (2 ^ n)) / xv' ξ ^ (2 ^ n + 1)

lemma xv'_ne_zero (ξ : L) : xv' ξ ≠ 0 := Units.ne_zero _

/-- **Lemma 6.6(1) (identity):** `ξ w(ξ) K_z(ξ) = w_A(ξ) + v ξ^N + ξ^{N+1} h(ξ)`. -/
theorem virt_identity (w wA : L → F) (z : Fin n → F) (v : F) (ξ : L) :
    xv' ξ * w ξ * (kernel z).eval (xv' ξ) =
      wA ξ + v * xv' ξ ^ (2 ^ n) + xv' ξ ^ (2 ^ n + 1) * virt w wA z v ξ := by
  have h := pow_ne_zero (2 ^ n + 1) (xv'_ne_zero ξ)
  rw [virt, mul_div_cancel₀ _ h]; ring

/-- **Lemma 6.6(2) (locality):** `h(ξ)` depends only on `w(ξ)` and `w_A(ξ)`. -/
theorem virt_congr {w wA w' wA' : L → F} (z : Fin n → F) (v : F) {ξ : L} (h1 : w ξ = w' ξ)
    (h2 : wA ξ = wA' ξ) : virt w wA z v ξ = virt w' wA' z v ξ := by
  simp [virt, h1, h2]

/-- **Lemma 6.6(3) (honest openings):** for `w = ev_L(U)`, `v = [X^{N-1}] U K_z` and
`w_A = ev_L(A_{U,z})`, `h = ev_L(H_{U,z})`. -/
theorem virt_honest {U : F[X]} (hU : U ∈ degreeLT F (2 ^ n)) (z : Fin n → F) :
    virt (ev L U) (ev L (openA U z)) z (openV U z) = ev L (openH U z) := by
  funext ξ
  have hx := pow_ne_zero (2 ^ n + 1) (xv'_ne_zero ξ)
  have hs := congrArg (fun P : F[X] => P.eval (xv' ξ)) (split_eq hU z)
  simp only [assemble, eval_add, eval_mul, eval_X, eval_C, eval_pow] at hs
  rw [virt, div_eq_iff hx]
  simp only [ev]
  rw [hs]; ring

/-- **Lemma 6.6(4) (linearity).** -/
theorem virt_add (w w' wA wA' : L → F) (z : Fin n → F) (v v' : F) :
    virt (w + w') (wA + wA') z (v + v') = virt w wA z v + virt w' wA' z v' := by
  funext ξ; simp only [virt, Pi.add_apply]; ring

theorem virt_smul (c : F) (w wA : L → F) (z : Fin n → F) (v : F) :
    virt (c • w) (c • wA) z (c * v) = c • virt w wA z v := by
  funext ξ; simp only [virt, Pi.smul_apply, smul_eq_mul]; ring

/-- **Remark 6.9(1):** with honest `w`, `w_A` and a claim `v'`, the virtual word is
`ev_L(H) + (v - v') · (ξ ↦ ξ^{-1})`. -/
theorem virt_wrong_value {U : F[X]} (hU : U ∈ degreeLT F (2 ^ n)) (z : Fin n → F) (v' : F) :
    virt (ev L U) (ev L (openA U z)) z v' =
      ev L (openH U z) + (openV U z - v') • (fun ξ : L => (xv' ξ)⁻¹) := by
  rw [← virt_honest hU z]
  funext ξ
  have hx := xv'_ne_zero ξ
  simp only [virt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **Remark 6.9(1):** the word `ξ ↦ ξ^{-1}` agrees with every codeword of `𝒞_0` on at most `N`
points: `1 - ξ T(ξ)` is a nonzero polynomial of degree at most `N`. -/
theorem inv_agree_le [Finite L] {T : F[X]} (hT : T ∈ degreeLT F (2 ^ n)) :
    (agreeSet (fun ξ : L => (xv' ξ)⁻¹) (ev L T)).ncard ≤ 2 ^ n := by
  classical
  set S := agreeSet (fun ξ : L => (xv' ξ)⁻¹) (ev L T)
  letI : Fintype S := Fintype.ofFinite S
  set Q : F[X] := 1 - X * T
  have hQ0 : Q ≠ 0 := by
    intro h
    have := congrArg (fun P : F[X] => P.coeff 0) h
    simp [Q] at this
  have hQdeg : Q.natDegree ≤ 2 ^ n := by
    refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    refine (natDegree_mul_le).trans ?_
    have := natDegree_le_of_mem_degreeLT hT
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    simp only [natDegree_X]; omega
  by_contra hlt
  push_neg at hlt
  apply hQ0
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q
    (f := fun i : S => xv' (i : L)) ?_ ?_ ?_
  · intro a b hab
    exact Subtype.ext (Subtype.ext (Units.ext hab))
  · intro i
    have hi := i.2
    simp only [S, agreeSet, Set.mem_setOf_eq, ev] at hi
    have hx := xv'_ne_zero (i : L)
    simp only [Q, eval_sub, eval_one, eval_mul, eval_X]
    rw [← hi, mul_inv_cancel₀ hx, sub_self]
  · rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]; omega

end Virtual

/-! ### Definition 6.8 (the protocol `Π_KF`) -/

section Protocol

variable {L : Subgroup Fˣ}

/-- The batched word `w_0 = w + β w_A + β² h[w, w_A; z, v]`. -/
noncomputable def wbat {n : ℕ} (w wA : L → F) (z : Fin n → F) (v : F) (β : F) : L → F :=
  w + β • wA + β ^ 2 • virt w wA z v

/-- A deterministic prover of `Π_KF`: the round-1 oracle `w_A`, and for each `β` a prover of the
folding test on `w_0 = w_β` (rounds `2` to `ℓ + 2`). -/
structure KFProver (F : Type*) [Field F] (L : Subgroup Fˣ) where
  /-- the round-1 oracle `w_A` -/
  wA : L → F
  /-- rounds `2, …, ℓ+2` as a function of `β` -/
  ft : F → FTProver F L

namespace KFProver

variable (P : KFProver F L) (ℓ : ℕ)

def Causal : Prop := ∀ β, (P.ft β).Causal
def DegOK (m : ℕ) : Prop := ∀ β, (P.ft β).DegOK m

/-- The verifier of `Π_KF` accepts `(β, r, ξ)` on the instance `(w; z, v)`: all the fold checks of
`Π_FT` on `w_0 = w_β` pass. -/
def Accepts {n κ : ℕ} (w : L → F) (z : Fin n → F) (v : F) (β : F) (r : ℕ → F) (ξ : Fin κ → L) :
    Prop :=
  (P.ft β).Accepts ℓ (wbat w P.wA z v β) r ξ

/-- The acceptance probability over the uniform challenges `(β, r, ξ) ∈ F × F^ℓ × L^κ`. -/
noncomputable def accProb [Fintype F] [Fintype L] {n : ℕ} (κ : ℕ) (w : L → F) (z : Fin n → F)
    (v : F) : ℚ :=
  prob (fun ω : (F × (Fin ℓ → F)) × (Fin κ → L) => P.Accepts ℓ w z v ω.1.1 (extR ω.1.2) ω.2)

end KFProver

/-- **Definition 7.1 (relation `R^δ_KF`):** `f` is a witness for `(w; z, v)` iff
`Δ^fib₀(w, Enc(f)) ≤ δ` and `f(z) = v`. -/
def RelKF {n : ℕ} (δ : ℚ) (w : L → F) (z : Fin n → F) (v : F) (α : Table F n) : Prop :=
  fibDist w (encode L α) ≤ δ ∧ cEval α z = v

/-! ### Theorem 6.10 (completeness) -/

/-- The honest prover of `Π_KF` for the coefficient table `α`: `w_A = ev_L(A_{U_f,z})` and the
honest folding prover on `U_0 = U_f + β A + β² H`. -/
noncomputable def honestKF {n : ℕ} (α : Table F n) (z : Fin n → F) (ℓ : ℕ) : KFProver F L :=
  ⟨ev L (openA (kronEnc α) z),
    fun β => honestFT (kronEnc α + C β * openA (kronEnc α) z + C (β ^ 2) * openH (kronEnc α) z) ℓ⟩

/-- The honest batched word is the codeword `ev_L(U_0)`. -/
theorem wbat_honest {n : ℕ} (α : Table F n) (z : Fin n → F) (β : F) :
    wbat (encode L α) (ev L (openA (kronEnc α) z)) z (cEval α z) β =
      ev L (kronEnc α + C β * openA (kronEnc α) z + C (β ^ 2) * openH (kronEnc α) z) := by
  rw [wbat, encode, ← openV_kronEnc, virt_honest (kronEnc_mem_degreeLT α) z]
  simp only [ev_add, ev_C_mul]

/-- **Theorem 6.10 (completeness):** if `w = Enc(f)` and `v = f(z)`, the honest prover makes the
verifier accept for all challenges. -/
theorem honestKF_accepts {m ℓ R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (α : Table F (m + ℓ)) (z : Fin (m + ℓ) → F) (β : F) (r : ℕ → F) {κ : ℕ} (ξ : Fin κ → L) :
    (honestKF (L := L) α z ℓ).Accepts ℓ (encode L α) z (cEval α z) β r ξ := by
  unfold KFProver.Accepts
  rw [show (honestKF (L := L) α z ℓ).wA = ev L (openA (kronEnc α) z) from rfl, wbat_honest]
  exact honestFT_accepts hL _ r ξ

theorem honestKF_prob_one [Fintype F] [Fintype L] {m ℓ R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (α : Table F (m + ℓ)) (z : Fin (m + ℓ) → F) (κ : ℕ) :
    (honestKF (L := L) α z ℓ).accProb ℓ κ (encode L α) z (cEval α z) = 1 := by
  haveI : Nonempty L := ⟨1⟩
  unfold KFProver.accProb
  have : (fun ω : (F × (Fin ℓ → F)) × (Fin κ → L) =>
      (honestKF (L := L) α z ℓ).Accepts ℓ (encode L α) z (cEval α z) ω.1.1 (extR ω.1.2) ω.2) =
      fun _ => True := by
    funext ω; simp only [eq_iff_iff, iff_true]; exact honestKF_accepts hL α z _ _ _
  rw [this, prob_true]

/-- The honest prover is causal and sends final polynomials of degree `< N_ℓ`. -/
theorem honestKF_DegOK {m ℓ : ℕ} (α : Table F (m + ℓ)) (z : Fin (m + ℓ) → F) :
    (honestKF (L := L) α z ℓ).DegOK m := by
  intro β
  refine honestFT_DegOK ?_
  refine Submodule.add_mem _ (Submodule.add_mem _ (kronEnc_mem_degreeLT α) ?_) ?_
  · rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (openA_mem _ z)
  · rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (openH_mem _ z)

/-- `pfold^{(j)}_r(U)` depends only on `r_{<j}`. -/
lemma pfoldUp_congr (U : F[X]) {r r' : ℕ → F} :
    ∀ j, (∀ i < j, r i = r' i) → pfoldUp r U j = pfoldUp r' U j
  | 0, _ => rfl
  | j + 1, h => by
      rw [pfoldUp, pfoldUp, pfoldUp_congr U j (fun i hi => h i (by omega)), h j (by omega)]

theorem honestKF_causal {n ℓ : ℕ} (α : Table F n) (z : Fin n → F) :
    (honestKF (L := L) α z ℓ).Causal := by
  intro β j r r' h
  simp only [honestKF, honestFT]
  rw [pfoldUp_congr _ j h]

end Protocol

end KroneckerFRI
