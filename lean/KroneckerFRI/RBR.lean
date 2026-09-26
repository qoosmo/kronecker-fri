/-
KroneckerFRI/RBR.lean
§7.5–7.6 of the paper: the doomed set and extractor (Definition 7.9, Lemma 7.10), the three items
of round-by-round knowledge soundness (Theorem 7.11), and knowledge, soundness and binding
(Corollary 7.12).  The instantiation in the generic framework of Definition 3.7 is in
`KroneckerFRI/Generic.lean`.

A partial transcript `τ_{j+1}` (`j ∈ [0, ℓ]`) determines `w_A`, `β` (hence `w_0 = w_β`), the
words `w_1, …, w_{j-1}` and the challenges `r_1, …, r_j`; it is represented by a folding prover
`P`, the word `w0` and the challenge sequence `r`, of which only this part is read
(`Wset_congr`).
-/
import KroneckerFRI.Soundness

set_option autoImplicit false

open Polynomial Finset KBFold

namespace KroneckerFRI

variable {F : Type*} [Field F] {L : Subgroup Fˣ}

/-! ### Definition 7.9 (doomed set) -/

/-- **Definition 7.9:** `τ_{j+1}` is *not doomed* iff some `c ∈ 𝒞_j` has `dens_j(c) ≥ 1-δ`. -/
def NotDoomedFT (P : FTProver F L) (m ℓ : ℕ) (w0 : L → F) (δ : ℚ) (r : ℕ → F) (j : ℕ) : Prop :=
  ∃ c ∈ RS (lv L j) (Nd m ℓ j), 1 - δ ≤ dens P ℓ w0 r j c

section Congr

variable (P : FTProver F L) {ℓ : ℕ} (w0 : L → F)

/-- `𝒲_j(c)` depends only on `r_{<j}` (and on the words `w_i`, `i < j`), for `j ≤ ℓ` and a
causal prover. -/
theorem Wset_congr (hC : P.Causal) {j : ℕ} (hj : j ≤ ℓ) {r r' : ℕ → F}
    (h : ∀ i < j, r i = r' i) (c : lv L j → F) :
    Wset P ℓ w0 r j c = Wset P ℓ w0 r' j c := by
  cases j with
  | zero => rfl
  | succ k =>
    have hW : ∀ i ≤ k, P.W ℓ w0 r i = P.W ℓ w0 r' i := fun i hi =>
      P.W_congr ℓ w0 hC (by omega) (fun t ht => h t (by omega))
    have hwhat : ∀ i ≤ k, P.what ℓ w0 r i = P.what ℓ w0 r' i := by
      intro i hi; simp only [FTProver.what, hW i hi, h i (by omega)]
    ext ξ
    simp only [Wset, Set.mem_setOf_eq, FTProver.Chk]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [← hwhat i (by omega), ← hW (i + 1) (by omega)]; exact h1 i hi
      · rw [← hwhat k le_rfl]; exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [hwhat i (by omega), hW (i + 1) (by omega)]; exact h1 i hi
      · rw [hwhat k le_rfl]; exact h2

theorem dens_congr (hC : P.Causal) {j : ℕ} (hj : j ≤ ℓ) {r r' : ℕ → F}
    (h : ∀ i < j, r i = r' i) (c : lv L j → F) :
    dens P ℓ w0 r j c = dens P ℓ w0 r' j c := by
  rw [dens, dens, Wset_congr P w0 hC hj h]

/-- `𝒲_0(c)` depends only on `w_0`. -/
theorem Wset_zero (P P' : FTProver F L) (ℓ ℓ' : ℕ) (r r' : ℕ → F) (c : lv L 0 → F) :
    Wset P ℓ w0 r 0 c = Wset P' ℓ' w0 r' 0 c := rfl

end Congr

/-! ### Definition 7.9 (extractor) and Lemma 7.10 -/

section Extractor

/-- `δ* = (1-ρ)/2` with `ρ = 2^{-R}`. -/
noncomputable def δstar (R : ℕ) : ℚ := (1 - 1 / 2 ^ R) / 2

/-- **Definition 7.9 (extractor):** the coefficient table of the codeword of `𝒞_0` within fibre
distance `δ*` of `w`, if there is one, and `0` otherwise.  It reads only the commitment `w`. -/
noncomputable def extKF (n R : ℕ) (w : L → F) : Table F n := by
  classical exact
    if FibDistLE w (RS L (2 ^ n) : Set (L → F)) (δstar R) then
      kronCoeffs n (polyOf (dec (RS L (2 ^ n) : Set (L → F)) (δstar R) w))
    else 0

/-- **Lemma 7.10:** whenever a witness exists, the extractor outputs it. -/
theorem extKF_eq {m ℓ R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 1 ≤ R) {δ : ℚ}
    (hδ : δ ≤ δstar R) {w : L → F} {α : Table F (m + ℓ)} (hα : fibDist w (encode L α) ≤ δ) :
    extKF (m + ℓ) R w = α := by
  classical
  haveI := hL.finite
  have hNM : 2 ^ (m + ℓ) ≤ Nat.card L := by
    rw [show Nat.card L = 2 ^ (m + ℓ + R) from hL]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrate : rate L (2 ^ (m + ℓ)) = 1 / 2 ^ R := by
    rw [rate, show Nat.card L = 2 ^ (m + ℓ + R) from hL]; push_cast
    rw [pow_add (2 : ℚ) (m + ℓ) R]
    have : (2 : ℚ) ^ (m + ℓ) ≠ 0 := by positivity
    field_simp
  have hδs : δstar R ≤ (1 - rate L (2 ^ (m + ℓ))) / 2 := by rw [hrate]; rfl
  have hF : FibDistLE w (RS L (2 ^ (m + ℓ)) : Set (L → F)) (δstar R) :=
    ⟨encode L α, encode_mem_RS α, hα.trans hδ⟩
  obtain ⟨hmem, hdist⟩ := dec_spec hF
  have hneg : (-1 : Fˣ) ∈ L := hL.neg_one_mem (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_smooth hL (by omega)
  have heq := fib_unique hneg h2 hδs w hmem (encode_mem_RS α) hdist (hα.trans hδ)
  simp only [extKF, if_pos hF, heq, polyOf_encode hNM, kronCoeffs_kronEnc]

/-- **Lemma 7.10:** the output of `Ext` is a witness whenever a witness exists. -/
theorem extKF_witness {m ℓ R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 1 ≤ R) {δ : ℚ}
    (hδ : δ ≤ δstar R) {w : L → F} {z : Fin (m + ℓ) → F} {v : F} {α : Table F (m + ℓ)}
    (hα : RelKF δ w z v α) : RelKF δ w z v (extKF (m + ℓ) R w) := by
  rw [extKF_eq hL hR hδ hα.1]; exact hα

end Extractor

/-! ### Theorem 7.11 (round-by-round knowledge soundness), items 1–3 -/

section Items

variable {m ℓ R : ℕ} {δ : ℚ}

/-- **Theorem 7.11, item 1 (round 1).** If `(w; z, v)` has no witness, then for every round-1
message `w_A`, `τ_1` is not doomed for at most `2M` values of `β`. -/
theorem rbr_item1 [Fintype F] [DecidableEq F] (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R)
    (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (w wA : L → F) (z : Fin (m + ℓ) → F) (v : F)
    (hnw : ∀ α : Table F (m + ℓ), ¬ RelKF δ w z v α) (P : F → FTProver F L) (r : F → ℕ → F) :
    {β : F | NotDoomedFT (P β) m ℓ (wbat w wA z v β) δ (r β) 0}.ncard ≤ 2 * Nat.card L := by
  have hsub : {β : F | NotDoomedFT (P β) m ℓ (wbat w wA z v β) δ (r β) 0} ⊆
      goodBeta δ w wA z v Set.univ := by
    rintro β ⟨c, hc, hd⟩
    haveI := hL.finite
    have hLpos : (0 : ℚ) < Nat.card L := by
      haveI : Nonempty L := ⟨1⟩; exact_mod_cast Nat.card_pos
    refine ⟨c, by simpa [Nd] using hc, Wset (P β) ℓ (wbat w wA z v β) (r β) 0 c,
      Set.subset_univ _, fun ξ hξ => negPt_mem_Wset (hL.neg_one_mem (by omega)) _ 0 c ξ hξ, ?_,
      fun ξ hξ => hξ.1⟩
    rw [dens, le_div_iff₀ hLpos] at hd
    exact hd
  by_contra h
  push_neg at h
  obtain ⟨α, hα⟩ := batching_witness hL hR hδ0 hδ w wA z v
    (lt_of_lt_of_le h (Set.ncard_le_ncard hsub (Set.toFinite _)))
  exact hnw α hα

/-- **Theorem 7.11, item 2 (round `j+1`, `j ∈ [1, ℓ]`; here `k = j - 1 < ℓ`).** If `τ_{k+1}` is
doomed, then for every round-`(k+2)` message (which fixes `w_k`), `τ_{k+2}` is not doomed for at
most `M_{k+1}` values of `r_{k+1}`. -/
theorem rbr_item2 [Fintype F] (hL : IsSmoothDomain L (m + ℓ + R)) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : FTProver F L) (hC : P.Causal) (w0 : L → F)
    (r : ℕ → F) {k : ℕ} (hk : k < ℓ) (hdoom : ¬ NotDoomedFT P m ℓ w0 δ r k) :
    {a : F | NotDoomedFT P m ℓ w0 δ (Function.update r k a) (k + 1)}.ncard ≤
      Nat.card (lv L (k + 1)) := by
  refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
    (card_badFold_le hL hδ0 hδ hk (P.W ℓ w0 r k))
  rintro a ⟨c', hc', hd⟩
  intro hgood
  apply hdoom
  set r' := Function.update r k a
  have hlt : ∀ i < k, r' i = r i := fun i hi => Function.update_of_ne (by omega) _ _
  have hWk : P.W ℓ w0 r' k = P.W ℓ w0 r k := P.W_congr ℓ w0 hC hk hlt
  have hgood' : GoodAt ℓ δ m k (P.W ℓ w0 r' k) (r' k) := by
    rw [hWk, show r' k = a from Function.update_self _ _ _]; exact hgood
  obtain ⟨hF, -, hsub⟩ := rbr_step hL hδ r' hk hgood' c' hc' hd
  have hmem : decAt ℓ δ m k (P.W ℓ w0 r' k) ∈ RS (lv L k) (Nd m ℓ k) := by
    rw [← Nd_succ (show k < m + ℓ by omega)]; exact (dec_spec hF).1
  refine ⟨_, hmem, hd.trans ?_⟩
  haveI := hL.finite
  rw [← dens_congr P w0 hC hk.le hlt]
  rw [dens, dens]
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)) (Nat.cast_nonneg _)

/-- **Theorem 7.11, item 3 (round `ℓ + 2`).** If `τ_{ℓ+1}` is doomed, then for every final
polynomial `P ∈ F[X]_{<N_ℓ}` the verifier accepts with probability at most `(1-δ)^κ` over the
query points. -/
theorem rbr_item3 [Fintype L] (hℓ : 1 ≤ ℓ) (P : FTProver F L) (hdeg : P.DegOK m) (w0 : L → F)
    (r : ℕ → F) (hdoom : ¬ NotDoomedFT P m ℓ w0 δ r ℓ) (κ : ℕ) :
    prob (fun ξ : Fin κ → L => P.Accepts ℓ w0 r ξ) ≤ (1 - δ) ^ κ := by
  rw [prob_accepts_fixed hℓ r κ]
  have hd : dens P ℓ w0 r ℓ (P.W ℓ w0 r ℓ) < 1 - δ := by
    by_contra h
    push_neg at h
    exact hdoom ⟨_, P.W_last_mem_RS ℓ w0 hdeg hℓ r, h⟩
  have h0 : 0 ≤ dens P ℓ w0 r ℓ (P.W ℓ w0 r ℓ) := by unfold dens; positivity
  exact pow_le_pow_left₀ h0 hd.le κ

end Items

/-! ### Corollary 7.12 (knowledge, soundness, binding) -/

section Consequences

variable {m ℓ R : ℕ} {δ : ℚ}

/-- **Corollary 7.12(1) (knowledge).** If a causal prover is accepted on `(w; z, v)` with
probability greater than `ε_KF`, then `f = Ext(w)` satisfies `Δ^fib₀(w, Enc(f)) ≤ δ` and
`f(z) = v`. -/
theorem knowledge [Fintype F] [DecidableEq F] [Fintype L] (hL : IsSmoothDomain L (m + ℓ + R))
    (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (P : KFProver F L)
    (hC : P.Causal) (hdeg : P.DegOK m) (κ : ℕ) (w : L → F) (z : Fin (m + ℓ) → F) (v : F)
    (hacc : epsKF F (m + ℓ + R) ℓ κ δ < P.accProb ℓ κ w z v) :
    RelKF δ w z v (extKF (m + ℓ) R w) := by
  by_cases h : ∃ α, RelKF δ w z v α
  · obtain ⟨α, hα⟩ := h
    exact extKF_witness hL (by omega) hδ hα
  · push_neg at h
    have := soundness hL hR hℓ hδ0 hδ P hC hdeg κ w z v h
    linarith

/-- **Corollary 7.12(3) (evaluation binding).** For a fixed commitment `w` and point `z`, no two
causal provers are accepted with probability greater than `ε_KF` on two distinct values. -/
theorem binding [Fintype F] [DecidableEq F] [Fintype L] (hL : IsSmoothDomain L (m + ℓ + R))
    (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (P P' : KFProver F L) (hC : P.Causal) (hdeg : P.DegOK m) (hC' : P'.Causal)
    (hdeg' : P'.DegOK m) (κ : ℕ) (w : L → F) (z : Fin (m + ℓ) → F) {v v' : F} (hvv : v ≠ v') :
    ¬ (epsKF F (m + ℓ + R) ℓ κ δ < P.accProb ℓ κ w z v ∧
        epsKF F (m + ℓ + R) ℓ κ δ < P'.accProb ℓ κ w z v') := by
  rintro ⟨h1, h2⟩
  have e1 := (knowledge hL hR hℓ hδ0 hδ P hC hdeg κ w z v h1).2
  have e2 := (knowledge hL hR hℓ hδ0 hδ P' hC' hdeg' κ w z v' h2).2
  exact hvv (e1.symm.trans e2)

end Consequences

end KroneckerFRI
