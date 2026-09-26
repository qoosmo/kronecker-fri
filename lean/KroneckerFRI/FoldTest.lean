/-
KroneckerFRI/FoldTest.lean
§5.2 and §5.5–5.6 of the paper: the folding proximity test `Π_FT[ℓ,κ]` (Definition 5.7), its
completeness (Lemma 5.9(1)), witness sets (Definition 5.20), fold checks and witness sets
(Lemma 5.21), one round of the chain (Lemma 5.22), the codeword chain (Proposition 5.23) and the
soundness of the test (Theorem 5.24).  Fibre distance, unique decoding, folding far words,
survival of fibre errors, good challenges and the one-step lemma (Definitions 5.10–5.17,
Lemmas 5.11–5.19) are those of `KBFold/Fibre.lean`.

Modelling (see `KroneckerFRI/Levels.lean` for the parameters).
* A deterministic prover (`FTProver`) is given by its messages as functions of the challenge
  sequence `r`: the oracles `orc j r` (`w_j`, used for `1 ≤ j ≤ ℓ-1`) and the final polynomial
  `fin r` (`P`).  `Causal` states that `w_j` depends only on `r_{<j}` (0-based:
  `r 0, …, r (j-1)`), and `DegOK` that `P ∈ F[X]_{<N_ℓ}` (it is sent as `N_ℓ` coefficients).
* The words are `W r 0 = w₀`, `W r j = w_j` and `W r ℓ = ev_{L_ℓ}(P)`; `what r j` is
  `ŵ_{j+1} = fold_{r_{j+1}}(w_j)`, and the fold check of level `j+1` at `η` is `Chk r j η`.
* The query point `ξ` passes if all fold checks at `ξ^{2^{j+1}}`, `j < ℓ`, hold (`QueryOK`), and
  the verifier accepts `(r, ξ^{(1)}, …, ξ^{(κ)})` if every query point passes.
-/
import KroneckerFRI.IteratedFold

set_option autoImplicit false

open Polynomial Finset KBFold

namespace KroneckerFRI

variable {F : Type*} [Field F]

/-! ### Definition 5.7 (the test) -/

/-- A deterministic prover for `Π_FT[ℓ,κ]`: oracles `w_j` and final polynomial `P` as functions
of the challenges. -/
structure FTProver (F : Type*) [Field F] (L : Subgroup Fˣ) where
  /-- the oracles `w_j`, `1 ≤ j ≤ ℓ - 1` -/
  orc : (j : ℕ) → (ℕ → F) → (lv L j → F)
  /-- the final polynomial `P` -/
  fin : (ℕ → F) → F[X]

namespace FTProver

variable {L : Subgroup Fˣ} (P : FTProver F L) (ℓ : ℕ) (w0 : L → F)

/-- `w_j` depends only on `r_{<j}`. -/
def Causal : Prop := ∀ j (r r' : ℕ → F), (∀ k < j, r k = r' k) → P.orc j r = P.orc j r'

/-- `P ∈ F[X]_{<N_ℓ}`, with `N_ℓ = 2^m`. -/
def DegOK (m : ℕ) : Prop := ∀ r, P.fin r ∈ degreeLT F (2 ^ m)

/-- The words `w_0 = w₀`, `w_j = orc j` (`1 ≤ j ≤ ℓ-1`) and `w_ℓ = ev_{L_ℓ}(P)`. -/
noncomputable def W (r : ℕ → F) : (j : ℕ) → (lv L j → F)
  | 0 => w0
  | j + 1 => if j + 1 = ℓ then ev (lv L (j + 1)) (P.fin r) else P.orc (j + 1) r

/-- `ŵ_{j+1} = fold_{r_{j+1}}(w_j)`. -/
noncomputable def what (r : ℕ → F) (j : ℕ) : lv L (j + 1) → F := wfold (r j) (P.W ℓ w0 r j)

/-- The fold check of level `j+1` at `η ∈ L_{j+1}` (equation (5.3)). -/
def Chk (r : ℕ → F) (j : ℕ) (η : lv L (j + 1)) : Prop := P.what ℓ w0 r j η = P.W ℓ w0 r (j + 1) η

/-- The query point `ξ` passes all the fold checks. -/
def QueryOK (r : ℕ → F) (ξ : L) : Prop := ∀ j < ℓ, P.Chk ℓ w0 r j (ptAt ξ (j + 1))

/-- The verifier accepts the challenges `r` and the query points `ξ`. -/
def Accepts {κ : ℕ} (r : ℕ → F) (ξ : Fin κ → L) : Prop := ∀ t, P.QueryOK ℓ w0 r (ξ t)

/-- The acceptance probability over the uniform challenges `(r, ξ) ∈ F^ℓ × L^κ`. -/
noncomputable def accProb [Fintype F] [Fintype L] (κ : ℕ) : ℚ :=
  prob (fun ω : (Fin ℓ → F) × (Fin κ → L) => P.Accepts ℓ w0 (extR ω.1) ω.2)

lemma W_zero (r : ℕ → F) : P.W ℓ w0 r 0 = w0 := rfl

lemma W_last (hℓ : 1 ≤ ℓ) (r : ℕ → F) : P.W ℓ w0 r ℓ = ev (lv L ℓ) (P.fin r) := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  simp [W]

lemma W_mid {j : ℕ} (hj0 : 0 < j) (hj : j < ℓ) (r : ℕ → F) : P.W ℓ w0 r j = P.orc j r := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [W]; rw [if_neg (by omega)]

/-- The words `w_j`, `j < ℓ`, depend only on `r_{<j}`. -/
lemma W_congr (hC : P.Causal) {j : ℕ} (hj : j < ℓ) {r r' : ℕ → F}
    (h : ∀ k < j, r k = r' k) : P.W ℓ w0 r j = P.W ℓ w0 r' j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rfl
  · rw [P.W_mid ℓ w0 hj0 hj, P.W_mid ℓ w0 hj0 hj, hC j r r' h]

lemma W_last_mem_RS {m : ℕ} (hdeg : P.DegOK m) (hℓ : 1 ≤ ℓ) (r : ℕ → F) :
    P.W ℓ w0 r ℓ ∈ RS (lv L ℓ) (Nd m ℓ ℓ) := by
  rw [P.W_last ℓ w0 hℓ, Nd_last]; exact ev_mem_RS (hdeg r)

end FTProver

/-! ### Lemma 5.9(1) (completeness) -/

section Completeness

variable {L : Subgroup Fˣ}

/-- The honest prover for `w₀ = ev_L(U)`: `w_j = ev_{L_j}(pfold^{(j)}_r(U))`, `P = pfold^{(ℓ)}_r(U)`. -/
noncomputable def honestFT (U : F[X]) (ℓ : ℕ) : FTProver F L :=
  ⟨fun j r => ev (lv L j) (pfoldUp r U j), fun r => pfoldUp r U ℓ⟩

/-- **Lemma 5.9(1):** if `w₀ = ev_L(U)` with `U ∈ F[X]_{<N}`, the honest prover makes every fold
check hold at every point, so the verifier accepts with probability `1`. -/
theorem honestFT_accepts {m ℓ R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (U : F[X])
    (r : ℕ → F) {κ : ℕ} (ξ : Fin κ → L) :
    (honestFT (L := L) U ℓ).Accepts ℓ (ev L U) r ξ := by
  have hW : ∀ j ≤ ℓ, (honestFT (L := L) U ℓ).W ℓ (ev L U) r j = ev (lv L j) (pfoldUp r U j) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rfl
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp only [FTProver.W, honestFT]
    split_ifs with h
    · subst h; rfl
    · rfl
  intro t i hi
  simp only [FTProver.Chk, FTProver.what]
  rw [hW i (by omega), hW (i + 1) (by omega), ← foldUp_ev_smooth hL r U (by omega : i ≤ m + ℓ + R),
    ← foldUp_ev_smooth hL r U (by omega : i + 1 ≤ m + ℓ + R)]
  rfl

theorem honestFT_DegOK {m ℓ : ℕ} {U : F[X]} (hU : U ∈ degreeLT F (2 ^ (m + ℓ))) :
    (honestFT (L := L) U ℓ).DegOK m := by
  intro r
  have := pfoldUp_mem_degreeLT r hU ℓ (by omega)
  rwa [show m + ℓ - ℓ = m by omega] at this

end Completeness

/-! ### Definition 5.20 (witness sets), Lemma 5.21 and Lemma 7.7 -/

section Witness

variable {L : Subgroup Fˣ} (P : FTProver F L) (ℓ : ℕ) (w0 : L → F)

/-- **Definition 5.20 (witness sets):** `𝒲_0(c) = {ξ ∈ L : w₀(±ξ) = c(±ξ)}` and, for
`j ≥ 1`, `𝒲_j(c) = {ξ ∈ L : ξ^{2^i} ∉ ℬ_i for i ∈ [1, j-1], and ŵ_j(ξ^{2^j}) = c(ξ^{2^j})}`. -/
def Wset (r : ℕ → F) : (j : ℕ) → (lv L j → F) → Set L
  | 0, c => {ξ | w0 ξ = c ξ ∧ w0 (negPt ξ) = c (negPt ξ)}
  | j + 1, c => {ξ | (∀ i < j, P.Chk ℓ w0 r i (ptAt ξ (i + 1))) ∧
      P.what ℓ w0 r j (ptAt ξ (j + 1)) = c (ptAt ξ (j + 1))}

/-- `dens_j(c) = |𝒲_j(c)| / M`. -/
noncomputable def dens (r : ℕ → F) (j : ℕ) (c : lv L j → F) : ℚ :=
  ((Wset P ℓ w0 r j c).ncard : ℚ) / Nat.card L

variable {P ℓ w0}

/-- **Lemma 5.21(1):** a query point passes all the fold checks iff it lies in `𝒲_ℓ(w_ℓ)`. -/
theorem queryOK_iff (hℓ : 1 ≤ ℓ) (r : ℕ → F) (ξ : L) :
    P.QueryOK ℓ w0 r ξ ↔ ξ ∈ Wset P ℓ w0 r ℓ (P.W ℓ w0 r ℓ) := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  simp only [FTProver.QueryOK, Wset, Set.mem_setOf_eq]
  constructor
  · intro h; exact ⟨fun i hi => h i (by omega), h k (by omega)⟩
  · rintro ⟨h1, h2⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact h1 i hi
    · exact h2

/-- **Lemma 5.21(2):** for fixed `r`, the verifier accepts with probability `dens_ℓ(w_ℓ)^κ` over
the independent uniform query points. -/
theorem prob_accepts_fixed [Fintype L] (hℓ : 1 ≤ ℓ) (r : ℕ → F) (κ : ℕ) :
    prob (fun ξ : Fin κ → L => P.Accepts ℓ w0 r ξ) = dens P ℓ w0 r ℓ (P.W ℓ w0 r ℓ) ^ κ := by
  classical
  set S := Wset P ℓ w0 r ℓ (P.W ℓ w0 r ℓ)
  have hf : (univ.filter fun ξ : Fin κ → L => P.Accepts ℓ w0 r ξ) =
      Fintype.piFinset (fun _ : Fin κ => (Set.toFinite S).toFinset) := by
    ext ξ
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, Set.Finite.mem_toFinset,
      FTProver.Accepts]
    exact forall_congr' (fun t => queryOK_iff hℓ r (ξ t))
  rw [prob_def, hf, Fintype.card_piFinset, dens, Nat.card_eq_fintype_card,
    Set.ncard_eq_toFinset_card S (Set.toFinite S)]
  simp [div_pow]

/-- **Lemma 7.7 (witness sets are fibre-closed).** -/
theorem negPt_mem_Wset (hL : (-1 : Fˣ) ∈ L) (r : ℕ → F) :
    ∀ (j : ℕ) (c : lv L j → F) (ξ : L), ξ ∈ Wset P ℓ w0 r j c → negPt ξ ∈ Wset P ℓ w0 r j c
  | 0, c, ξ, h => by
      simp only [Wset, Set.mem_setOf_eq, negPt_negPt hL] at h ⊢
      exact ⟨h.2, h.1⟩
  | j + 1, c, ξ, h => by
      have e : ∀ i, ptAt (negPt ξ) (i + 1) = ptAt ξ (i + 1) := by
        intro i
        have h1 : ptAt (negPt ξ) 1 = ptAt ξ 1 := by
          show sqPt (negPt ξ) = sqPt ξ
          exact Subtype.ext (negPt_sq ξ)
        induction i with
        | zero => exact h1
        | succ i ih => show sqPt (ptAt (negPt ξ) (i + 1)) = sqPt (ptAt ξ (i + 1)); rw [ih]
      simp only [Wset, Set.mem_setOf_eq, e] at h ⊢
      exact h

end Witness

/-! ### Lemma 5.22 (one round of the chain) -/

section Step

variable {L : Subgroup Fˣ} {P : FTProver F L} {m ℓ : ℕ} {w0 : L → F} {δ : ℚ}

/-- **Lemma 5.22 (one round of the chain).** Let `j < ℓ` (the paper's level `j+1`) and let
`r_{j+1}` be good for `w_j`.  If `c' ∈ 𝒞_{j+1}` has `dens_{j+1}(c') ≥ 1-δ`, then
`Δ^fib_j(w_j, 𝒞_j) ≤ δ`, `c = dec_j(w_j)` satisfies `fold_{r_{j+1}}(c) = c'`, and
`𝒲_{j+1}(c') ⊆ 𝒲_j(c)`. -/
theorem rbr_step {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (r : ℕ → F) {j : ℕ} (hj : j < ℓ) (hgood : GoodAt ℓ δ m j (P.W ℓ w0 r j) (r j))
    (c' : lv L (j + 1) → F) (hc' : c' ∈ RS (lv L (j + 1)) (Nd m ℓ (j + 1)))
    (hdens : 1 - δ ≤ dens P ℓ w0 r (j + 1) c') :
    FibDistLE (P.W ℓ w0 r j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
      wfold (r j) (decAt ℓ δ m j (P.W ℓ w0 r j)) = c' ∧
      Wset P ℓ w0 r (j + 1) c' ⊆ Wset P ℓ w0 r j (decAt ℓ δ m j (P.W ℓ w0 r j)) := by
  obtain ⟨hDj, hμj, hdD, hrate⟩ := level_facts hL hj
  have hδj : δ ≤ (1 - rate (sqDom (lv L j)) (Nd m ℓ (j + 1))) / 2 := by rw [hrate]; exact hδ
  haveI := hL.finite
  haveI : Finite (sqDom (lv L j)) := lv_finite (L := L) (j + 1)
  haveI := lv_finite (L := L) (j + 1)
  set Y := agreeSet (P.what ℓ w0 r j) c'
  have hsubY : Wset P ℓ w0 r (j + 1) c' ⊆ (fun ξ : L => ptAt ξ (j + 1)) ⁻¹' Y := by
    intro ξ hξ; exact hξ.2
  have hcardW : (Wset P ℓ w0 r (j + 1) c').ncard ≤ 2 ^ (j + 1) * Y.ncard := by
    rw [← ncard_preimage_ptAt hL (j + 1) (by omega) Y]
    exact Set.ncard_le_ncard hsubY (Set.toFinite _)
  have hML : Nat.card L = 2 ^ (j + 1) * Nat.card (lv L (j + 1)) := card_L_eq hL (by omega)
  have hLpos : (0 : ℚ) < Nat.card L := by
    haveI : Nonempty L := ⟨1⟩; exact_mod_cast Nat.card_pos
  have hY : (1 - δ) * Nat.card (sqDom (lv L j)) ≤ Y.ncard := by
    have h1 : (1 - δ) * Nat.card L ≤ (Wset P ℓ w0 r (j + 1) c').ncard := by
      rw [dens, le_div_iff₀ hLpos] at hdens; exact hdens
    have h2 : ((Wset P ℓ w0 r (j + 1) c').ncard : ℚ) ≤ 2 ^ (j + 1) * Y.ncard := by
      exact_mod_cast hcardW
    rw [hML] at h1
    push_cast at h1
    have h3 : (0 : ℚ) < 2 ^ (j + 1) := by positivity
    have : (1 - δ) * Nat.card (lv L (j + 1)) ≤ Y.ncard := by nlinarith
    exact this
  obtain ⟨hF, hfold, hagree⟩ := one_step hDj hμj hδj (P.W ℓ w0 r j) (r j) hgood c' hc' hY
  refine ⟨hF, hfold, fun ξ hξ => ?_⟩
  have hη : ptAt ξ (j + 1) ∈ Y := hξ.2
  have hfib1 : ptAt ξ j ∈ fibre (ptAt ξ (j + 1)) := rfl
  have hfib2 : negPt (ptAt ξ j) ∈ fibre (ptAt ξ (j + 1)) := negPt_mem_fibre hfib1
  cases j with
  | zero =>
    exact ⟨hagree _ hη _ hfib1, hagree _ hη _ hfib2⟩
  | succ k =>
    refine ⟨fun i hi => hξ.1 i (by omega), ?_⟩
    have hk := hξ.1 k (by omega)
    simp only [FTProver.Chk] at hk
    show P.what ℓ w0 r k (ptAt ξ (k + 1)) = _
    rw [hk]
    exact hagree _ hη _ hfib1

end Step

/-! ### Proposition 5.23 (the codeword chain) -/

section Chain

variable {L : Subgroup Fˣ} (P : FTProver F L) (m ℓ : ℕ) (w0 : L → F) (δ : ℚ)

/-- The codeword chain: `c_j = dec_j(w_j)` for `j < ℓ` and `c_ℓ = w_ℓ`. -/
noncomputable def chainCw (r : ℕ → F) (j : ℕ) : lv L j → F :=
  if j < ℓ then decAt ℓ δ m j (P.W ℓ w0 r j) else P.W ℓ w0 r j

variable {P m ℓ w0 δ}

/-- **Proposition 5.23 (the codeword chain).** Let `r` be such that `r_{j+1}` is good for `w_j`
for every `j < ℓ`, and `dens_ℓ(w_ℓ) ≥ 1-δ`.  Then for every `j < ℓ`,
`Δ^fib_j(w_j, 𝒞_j) ≤ δ` and `fold_{r_{j+1}}(c_j) = c_{j+1}`, and for every `j ≤ ℓ`,
`𝒲_ℓ(w_ℓ) ⊆ 𝒲_j(c_j)`. -/
theorem chain {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hdeg : P.DegOK m) (r : ℕ → F)
    (hgood : ∀ j < ℓ, GoodAt ℓ δ m j (P.W ℓ w0 r j) (r j))
    (hd : 1 - δ ≤ dens P ℓ w0 r ℓ (P.W ℓ w0 r ℓ)) :
    (∀ j < ℓ, FibDistLE (P.W ℓ w0 r j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
        wfold (r j) (chainCw P m ℓ w0 δ r j) = chainCw P m ℓ w0 δ r (j + 1)) ∧
      ∀ j ≤ ℓ, Wset P ℓ w0 r ℓ (P.W ℓ w0 r ℓ) ⊆ Wset P ℓ w0 r j (chainCw P m ℓ w0 δ r j) := by
  haveI := hL.finite
  have hLpos : (0 : ℚ) < Nat.card L := by
    haveI : Nonempty L := ⟨1⟩; exact_mod_cast Nat.card_pos
  let Q : ℕ → Prop := fun j =>
    (j < ℓ → FibDistLE (P.W ℓ w0 r j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
        wfold (r j) (chainCw P m ℓ w0 δ r j) = chainCw P m ℓ w0 δ r (j + 1)) ∧
      Wset P ℓ w0 r ℓ (P.W ℓ w0 r ℓ) ⊆ Wset P ℓ w0 r j (chainCw P m ℓ w0 δ r j)
  have key : ∀ k j, j + k = ℓ → Q j := by
    intro k
    induction k with
    | zero =>
      intro j hj
      simp only [add_zero] at hj
      subst hj
      refine ⟨fun h => absurd h (lt_irrefl _), ?_⟩
      simp [chainCw]
    | succ k ih =>
      intro j hjk
      have hj : j < ℓ := by omega
      obtain ⟨ihF, ihW⟩ := ih (j + 1) (by omega)
      -- `c_{j+1} ∈ 𝒞_{j+1}`
      have hc' : chainCw P m ℓ w0 δ r (j + 1) ∈ RS (lv L (j + 1)) (Nd m ℓ (j + 1)) := by
        by_cases hj1 : j + 1 < ℓ
        · have hF := (ihF hj1).1
          have hmem := (dec_spec hF).1
          simp only [chainCw, if_pos hj1, decAt]
          have e : 2 * Nd m ℓ (j + 1 + 1) = Nd m ℓ (j + 1) := Nd_succ (by omega)
          rw [e] at hmem ⊢
          exact hmem
        · have e : j + 1 = ℓ := by omega
          simp only [chainCw, if_neg hj1]
          have := P.W_last_mem_RS ℓ w0 hdeg hℓ r
          subst e
          exact this
      -- `dens_{j+1}(c_{j+1}) ≥ 1 - δ`
      have hdj : 1 - δ ≤ dens P ℓ w0 r (j + 1) (chainCw P m ℓ w0 δ r (j + 1)) := by
        refine hd.trans ?_
        rw [dens, dens]
        exact div_le_div_of_nonneg_right
          (by exact_mod_cast Set.ncard_le_ncard ihW (Set.toFinite _)) (Nat.cast_nonneg _)
      obtain ⟨hF, hfold, hsub⟩ := rbr_step hL hδ r hj (hgood j hj) _ hc' hdj
      have hcj : chainCw P m ℓ w0 δ r j = decAt ℓ δ m j (P.W ℓ w0 r j) := by
        simp only [chainCw, if_pos hj]
      refine ⟨fun _ => ⟨hF, by rw [hcj]; exact hfold⟩, ?_⟩
      rw [hcj]
      exact ihW.trans hsub
  exact ⟨fun j hj => (key (ℓ - j) j (by omega)).1 hj, fun j hj => (key (ℓ - j) j (by omega)).2⟩

/-- **Proposition 5.23(1)–(2).** Under the hypotheses of `chain`: `Δ^fib₀(w₀, 𝒞₀) ≤ δ`, `w₀`
agrees with `c₀` at every point of `𝒲_ℓ(w_ℓ)` (and at its negative), and
`P = pfold^{(ℓ)}_r(P_{c₀})`. -/
theorem chain_final {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hdeg : P.DegOK m) (r : ℕ → F)
    (hgood : ∀ j < ℓ, GoodAt ℓ δ m j (P.W ℓ w0 r j) (r j))
    (hd : 1 - δ ≤ dens P ℓ w0 r ℓ (P.W ℓ w0 r ℓ)) :
    FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ ∧
      decAt ℓ δ m 0 w0 ∈ RS L (2 ^ (m + ℓ)) ∧
      (∀ ξ ∈ Wset P ℓ w0 r ℓ (P.W ℓ w0 r ℓ),
        w0 ξ = decAt ℓ δ m 0 w0 ξ ∧ w0 (negPt ξ) = decAt ℓ δ m 0 w0 (negPt ξ)) ∧
      P.fin r = pfoldUp r (polyOf (decAt ℓ δ m 0 w0)) ℓ := by
  obtain ⟨h1, h2⟩ := chain hL hℓ hδ hdeg r hgood hd
  haveI := hL.finite
  have e0 : 2 * Nd m ℓ (0 + 1) = 2 ^ (m + ℓ) := by rw [Nd_succ (by omega)]; rfl
  have hF0 : FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ := by
    have := (h1 0 (by omega)).1
    rw [e0] at this
    exact this
  have hc0 : chainCw P m ℓ w0 δ r 0 = decAt ℓ δ m 0 w0 := by
    simp only [chainCw, if_pos (show 0 < ℓ by omega)]; rfl
  have hmem : decAt ℓ δ m 0 w0 ∈ RS L (2 ^ (m + ℓ)) := by
    rw [← e0]; exact (dec_spec (h1 0 (by omega)).1).1
  refine ⟨hF0, hmem, fun ξ hξ => ?_, ?_⟩
  · have := h2 0 (Nat.zero_le _) hξ
    rw [hc0] at this
    exact this
  · -- the chain is the sequence of folds of `c₀ = ev_L(P_{c₀})`
    have hchain := foldUp_of_chain r (chainCw P m ℓ w0 δ r) (fun j hj => (h1 j hj).2) ℓ le_rfl
    obtain ⟨hP0, hev0⟩ := polyOf_spec (show 2 ^ (m + ℓ) ≤ Nat.card L from
      Nd_le_card hL (j := 0) (by omega)) hmem
    rw [hc0, ← hev0, foldUp_ev_smooth hL r _ (by omega)] at hchain
    have hcl : chainCw P m ℓ w0 δ r ℓ = ev (lv L ℓ) (P.fin r) := by
      simp only [chainCw, lt_irrefl, if_false]
      exact P.W_last ℓ w0 hℓ r
    rw [hcl] at hchain
    haveI := lv_finite (L := L) ℓ
    have hdl : 2 ^ m ≤ Nat.card (lv L ℓ) := by
      rw [← Nd_last (ℓ := ℓ)]; exact Nd_le_card hL (by omega)
    have hfold := pfoldUp_mem_degreeLT r hP0 ℓ (by omega)
    rw [show m + ℓ - ℓ = m by omega] at hfold
    exact ev_injOn hdl (hdeg r) hfold hchain

end Chain

/-! ### Theorem 5.24 (soundness of the test) -/

section Soundness

/-- The acceptance bound of Theorem 5.24(3) and Theorem 7.8 (Lemma 3.3 with a bad event):
if every accepted query point lies in `S(ω)`, and `|S(ω)| ≤ (1-δ) M` outside a bad event `B`,
then `Pr[accept] ≤ Pr[B] + (1-δ)^κ`. -/
theorem accept_le {Ω' L : Type*} [Fintype Ω'] [Fintype L] [Nonempty L] (κ : ℕ) {δ : ℚ}
    (hδ1 : δ ≤ 1) (S : Ω' → Set L) (Acc : Ω' → (Fin κ → L) → Prop) (B : Ω' → Prop)
    (hacc : ∀ ω ξ, Acc ω ξ → ∀ t, ξ t ∈ S ω)
    (hS : ∀ ω, ¬ B ω → ((S ω).ncard : ℚ) ≤ (1 - δ) * Fintype.card L) :
    prob (fun p : Ω' × (Fin κ → L) => Acc p.1 p.2) ≤ prob B + (1 - δ) ^ κ := by
  classical
  let S' : Ω' → Finset L := fun ω => (Set.toFinite (S ω)).toFinset
  have hq := independent_queries_le κ S' (fun ω => ¬ B ω) (1 - δ) (by linarith) (by
    intro ω hω
    simp only [S']
    rw [← Set.ncard_eq_toFinset_card]
    exact hS ω hω)
  calc prob (fun p : Ω' × (Fin κ → L) => Acc p.1 p.2)
      ≤ prob (fun p : Ω' × (Fin κ → L) => B p.1 ∨ (¬ B p.1 ∧ ∀ t, p.2 t ∈ S' p.1)) := by
        apply prob_mono
        rintro ⟨ω, ξ⟩ h
        by_cases hB : B ω
        · exact Or.inl hB
        · refine Or.inr ⟨hB, fun t => ?_⟩
          simp only [S', Set.Finite.mem_toFinset]
          exact hacc ω ξ h t
    _ ≤ prob (fun p : Ω' × (Fin κ → L) => B p.1) +
          prob (fun p : Ω' × (Fin κ → L) => ¬ B p.1 ∧ ∀ t, p.2 t ∈ S' p.1) := prob_or_le _ _
    _ ≤ _ := by
        haveI : Nonempty (Fin κ → L) := ⟨fun _ => Classical.arbitrary L⟩
        rw [prob_fst B]
        exact add_le_add_left (hq.1.trans hq.2) _

variable {L : Subgroup Fˣ} (P : FTProver F L) (m ℓ : ℕ) (w0 : L → F) (δ : ℚ)

/-- The event `¬ Good`: some `r_{j+1}` is not good for `w_j`. -/
def NotGood (r : ℕ → F) : Prop := ∃ j < ℓ, ¬ GoodAt ℓ δ m j (P.W ℓ w0 r j) (r j)

variable {P m ℓ w0 δ}

/-- **Theorem 5.24(1):** `Pr_r[¬ Good] ≤ ε_fold = ∑_{j=1}^{ℓ} M_j / |F|` (for a causal prover). -/
theorem prob_notGood_le [Fintype F] [DecidableEq F] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hC : P.Causal) :
    prob (fun ρ : Fin ℓ → F => NotGood P m ℓ w0 δ (extR ρ)) ≤ epsFold F (m + ℓ + R) ℓ := by
  classical
  let E : Fin ℓ → (Fin ℓ → F) → Prop := fun i ρ =>
    ¬ GoodAt ℓ δ m i (P.W ℓ w0 (extR ρ) i) (extR ρ i)
  have hseq := sequential_challenges (Ch := fun _ : Fin ℓ => F) E
    (fun i => (Nat.card (lv L ((i : ℕ) + 1)) : ℚ)) ?_
  · calc prob (fun ρ : Fin ℓ → F => NotGood P m ℓ w0 δ (extR ρ))
        ≤ prob (fun ρ : Fin ℓ → F => ∃ i, E i ρ) := by
          apply prob_mono
          rintro ρ ⟨j, hj, h⟩
          exact ⟨⟨j, hj⟩, h⟩
      _ ≤ _ := hseq
      _ = epsFold F (m + ℓ + R) ℓ := by
          rw [epsFold, ← Fin.sum_univ_eq_sum_range]
          refine sum_congr rfl (fun i _ => ?_)
          rw [card_lv hL (by omega)]; push_cast; rfl
  · intro i ρ
    have hE : ∀ c : F, E i (Function.update ρ i c) ↔
        ¬ GoodAt ℓ δ m i (P.W ℓ w0 (extR ρ) i) c := by
      intro c
      simp only [E, extR_update]
      rw [P.W_congr ℓ w0 hC i.isLt (fun k hk => Function.update_of_ne (by omega) _ _),
        Function.update_self]
    simp_rw [hE]
    rw [card_filter_eq_ncard]
    exact_mod_cast card_badFold_le hL hδ0 hδ i.isLt _

/-- **Theorem 5.24(2)–(3), core:** for good `r`, if `Δ^fib₀(w₀, 𝒞₀) > δ` then
`dens_ℓ(w_ℓ) < 1 - δ`. -/
theorem dens_lt_of_far {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hdeg : P.DegOK m)
    (hfar : ¬ FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ) (r : ℕ → F)
    (hgood : ¬ NotGood P m ℓ w0 δ r) : dens P ℓ w0 r ℓ (P.W ℓ w0 r ℓ) < 1 - δ := by
  by_contra h
  push_neg at h
  exact hfar (chain_final hL hℓ hδ hdeg r (fun j hj => by
    by_contra hb; exact hgood ⟨j, hj, hb⟩) h).1

/-- **Theorem 5.24(3) (soundness of the folding test).** For a causal prover sending a final
polynomial in `F[X]_{<N_ℓ}`, if `Δ^fib₀(w₀, 𝒞₀) > δ`, the verifier accepts with probability at
most `ε_fold + (1-δ)^κ`. -/
theorem fpt_sound [Fintype F] [DecidableEq F] [Fintype L] {R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hC : P.Causal) (hdeg : P.DegOK m) (κ : ℕ)
    (hfar : ¬ FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ) :
    P.accProb ℓ w0 κ ≤ epsFold F (m + ℓ + R) ℓ + (1 - δ) ^ κ := by
  classical
  haveI : Nonempty L := ⟨1⟩
  have hR : (0 : ℚ) < 1 / 2 ^ R := by positivity
  have hLpos : (0 : ℚ) < Fintype.card L := by exact_mod_cast Fintype.card_pos
  refine (accept_le (Ω' := Fin ℓ → F) κ (δ := δ) (by linarith)
    (fun ρ => Wset P ℓ w0 (extR ρ) ℓ (P.W ℓ w0 (extR ρ) ℓ))
    (fun ρ ξ => P.Accepts ℓ w0 (extR ρ) ξ) (fun ρ => NotGood P m ℓ w0 δ (extR ρ))
    (fun ρ ξ h t => (queryOK_iff hℓ _ _).1 (h t)) (fun ρ hρ => ?_)).trans ?_
  · have := dens_lt_of_far hL hℓ hδ hdeg hfar (extR ρ) hρ
    rw [dens, Nat.card_eq_fintype_card, div_lt_iff₀ hLpos] at this
    exact this.le
  · exact add_le_add_right (prob_notGood_le hL hδ0 hδ hC) _

end Soundness

end KroneckerFRI
