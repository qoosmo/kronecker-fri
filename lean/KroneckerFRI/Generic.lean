/-
KroneckerFRI/Generic.lean
Theorem 7.11, "Consequently": `Π_KF` is round-by-round knowledge sound for `R^δ_KF` in the sense
of Definition 3.7 (`IsRBRKnowledgeWith` of `KBFold/RoundByRound.lean`), with the doomed set and
extractor of Definition 7.9 and errors `ε_1 = 2M/|F|`, `ε_{j+1} = M_j/|F|`, `ε_{ℓ+2} = (1-δ)^κ`;
and evaluation binding by Lemma 3.11 (`rbr_knowledge_binding`).

`Π_KF` as a generic public-coin IOP (Definition 3.1 as modelled in `KBFold/RoundByRound.lean`):
* `ℓ + 2` rounds, indexed `0, …, ℓ+1`; challenge sets `ChK i = F` for `i ≤ ℓ` and
  `ChK (ℓ+1) = L^κ`;
* one message type `MsgK = F^L × (∏_j F^{L_j}) × F[X]`: the message of round `0` carries `w_A`
  (first component); the message of round `i ∈ [1, ℓ]` carries the oracle `w_{i-1}` (the level
  `i - 1` entry of the second component, read for `2 ≤ i ≤ ℓ`); the last message carries the
  final polynomial `P` (third component); unused components are ignored;
* instances `x = (w, z, v)`;
* the verifier `VK` parses a full transcript, checks `P ∈ F[X]_{<N_ℓ}`, and runs the fold checks;
* the doomed set `DK` is Definition 7.9 on parsed transcripts, and the extractor is `extKF`.
-/
import KroneckerFRI.RBR

set_option autoImplicit false

open Polynomial Finset KBFold

namespace KroneckerFRI

universe u

noncomputable section Generic

variable {F : Type u} [Field F] {L : Subgroup Fˣ} (ℓ κ : ℕ)

/-- The challenge sets: `F` in rounds `0, …, ℓ` and `L^κ` in round `ℓ + 1`. -/
def ChK (i : Fin (ℓ + 2)) : Type u := if (i : ℕ) < ℓ + 1 then F else (Fin κ → L)

instance [Fintype F] [DecidableEq F] [Fintype L] (i : Fin (ℓ + 2)) :
    Fintype (ChK (F := F) (L := L) ℓ κ i) := by
  unfold ChK; split <;> infer_instance

instance (i : Fin (ℓ + 2)) : Nonempty (ChK (F := F) (L := L) ℓ κ i) := by
  unfold ChK; split
  · exact ⟨(0 : F)⟩
  · exact ⟨fun _ => (1 : L)⟩

variable {ℓ κ}

def chF {i : Fin (ℓ + 2)} (h : (i : ℕ) < ℓ + 1) : ChK (F := F) (L := L) ℓ κ i ≃ F :=
  Equiv.cast (by simp [ChK, h])

def chQ {i : Fin (ℓ + 2)} (h : ¬ (i : ℕ) < ℓ + 1) : ChK (F := F) (L := L) ℓ κ i ≃ (Fin κ → L) :=
  Equiv.cast (by simp [ChK, h])

variable (L)

/-- The message type (see the header). -/
abbrev MsgK : Type u := (L → F) × ((j : ℕ) → lv L j → F) × F[X]

variable {L}

/-- Transcript entries. -/
abbrev EntK (ℓ κ : ℕ) := Entry (ChK (F := F) (L := L) ℓ κ) (MsgK (F := F) L)

/-- The field challenge of an entry (`0` for the last round). -/
def entR (e : EntK (F := F) (L := L) ℓ κ) : F :=
  if h : (e.2.1 : ℕ) < ℓ + 1 then chF h e.2.2 else 0

/-- The query points of an entry (a default value for rounds `≤ ℓ`). -/
def entQ (e : EntK (F := F) (L := L) ℓ κ) : Fin κ → L :=
  if h : (e.2.1 : ℕ) < ℓ + 1 then fun _ => 1 else chQ h e.2.2

variable (τ : List (EntK (F := F) (L := L) ℓ κ))

/-- `w_A` (round `0`). -/
def pWA : L → F := (τ[0]?.map (fun e => e.1.1)).getD 0
/-- `β` (challenge of round `0`). -/
def pBeta : F := (τ[0]?.map entR).getD 0
/-- the oracle `w_j` (round `j + 1`). -/
def pOrc (j : ℕ) : lv L j → F := (τ[j + 1]?.map (fun e => e.1.2.1 j)).getD 0
/-- `r_{i+1}` (challenge of round `i + 1`). -/
def pR (i : ℕ) : F := (τ[i + 1]?.map entR).getD 0
/-- the final polynomial (round `ℓ + 1`). -/
def pFin : F[X] := (τ[ℓ + 1]?.map (fun e => e.1.2.2)).getD 0
/-- the query points (challenge of round `ℓ + 1`). -/
def pXi : Fin κ → L := (τ[ℓ + 1]?.map entQ).getD (fun _ => 1)

/-- The folding prover whose messages are those of the transcript. -/
def pFT : FTProver F L := ⟨fun j _ => pOrc τ j, fun _ => pFin τ⟩

variable (m : ℕ) (δ : ℚ) (R : ℕ)

/-- Instances `(w, z, v)`. -/
abbrev InstK (L : Subgroup Fˣ) (n : ℕ) := (L → F) × (Fin n → F) × F

/-- The batched word of a transcript. -/
noncomputable def pW0 (x : InstK L (m + ℓ)) : L → F := wbat x.1 (pWA τ) x.2.1 x.2.2 (pBeta τ)

/-- The verifier of `Π_KF` on a full transcript. -/
def VK (x : InstK L (m + ℓ)) (τ : List (EntK (F := F) (L := L) ℓ κ)) : Prop :=
  pFin τ ∈ degreeLT F (2 ^ m) ∧ (pFT τ).Accepts ℓ (pW0 τ m x) (pR τ) (pXi τ)

/-- The relation `R^δ_KF` (Definition 7.1) in the form `evalRel` of §3.4. -/
def RK : InstK L (m + ℓ) → Table F (m + ℓ) → Prop :=
  evalRel (encode L) fibDist δ (fun α (z : Fin (m + ℓ) → F) => cEval α z)

/-- **Definition 7.9** on list transcripts: `τ_0` is doomed; `τ_{j+1}` (`j ≤ ℓ`) is doomed iff
not "not doomed" at level `j`; a full transcript is doomed iff the verifier rejects it. -/
def DK (x : InstK L (m + ℓ)) (τ : List (EntK (F := F) (L := L) ℓ κ)) : Prop :=
  if τ.length = 0 then True
  else if τ.length ≤ ℓ + 1 then ¬ NotDoomedFT (pFT τ) m ℓ (pW0 τ m x) δ (pR τ) (τ.length - 1)
  else ¬ VK m x τ

/-- **Definition 7.9 (extractor)**, reading only the commitment `w` of the instance. -/
noncomputable def ExtK (x : InstK L (m + ℓ)) (_τ : List (EntK (F := F) (L := L) ℓ κ))
    (_msg : MsgK (F := F) L) : Table F (m + ℓ) :=
  extKF (m + ℓ) R x.1

variable (ℓ κ)

/-- The round errors of Theorem 7.11: `ε_1 = 2M/|F|`, `ε_{j+1} = M_j/|F|` (`j ∈ [1, ℓ]`),
`ε_{ℓ+2} = (1-δ)^κ`. -/
noncomputable def εK [Fintype F] (i : Fin (ℓ + 2)) : ℚ :=
  if (i : ℕ) = 0 then 2 * (Nat.card L : ℚ) / Fintype.card F
  else if (i : ℕ) < ℓ + 1 then (Nat.card (lv L i) : ℚ) / Fintype.card F else (1 - δ) ^ κ

end Generic

/-! ### Congruence -/

section Congr

variable {F : Type*} [Field F] {L : Subgroup Fˣ} {ℓ m : ℕ} {δ : ℚ}

/-- `NotDoomed` at level `j ≤ ℓ` depends only on the words `w_i` and challenges `r_i`, `i < j`. -/
theorem NotDoomedFT_congr {P P' : FTProver F L} {w0 : L → F} {r r' : ℕ → F} {j : ℕ}
    (hj : j ≤ ℓ) (h : ∀ i < j, P.W ℓ w0 r i = P'.W ℓ w0 r' i ∧ r i = r' i) :
    NotDoomedFT P m ℓ w0 δ r j ↔ NotDoomedFT P' m ℓ w0 δ r' j := by
  have hWset : ∀ c, Wset P ℓ w0 r j c = Wset P' ℓ w0 r' j c := by
    intro c
    cases j with
    | zero => rfl
    | succ k =>
      have hwhat : ∀ i ≤ k, P.what ℓ w0 r i = P'.what ℓ w0 r' i := by
        intro i hi; simp only [FTProver.what, (h i (by omega)).1, (h i (by omega)).2]
      ext ξ
      simp only [Wset, Set.mem_setOf_eq, FTProver.Chk]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun i hi => ?_, ?_⟩
        · rw [← hwhat i (by omega), ← (h (i + 1) (by omega)).1]; exact h1 i hi
        · rw [← hwhat k le_rfl]; exact h2
      · rintro ⟨h1, h2⟩
        refine ⟨fun i hi => ?_, ?_⟩
        · rw [hwhat i (by omega), (h (i + 1) (by omega)).1]; exact h1 i hi
        · rw [hwhat k le_rfl]; exact h2
  simp only [NotDoomedFT, dens, hWset]

end Congr

/-! ### Parsing lemmas -/

section Parse

variable {F : Type u} [Field F] {L : Subgroup Fˣ} {ℓ κ : ℕ}

lemma length_of_isPartial' {τ : List (EntK (F := F) (L := L) ℓ κ)} {i : ℕ} (h : IsPartial τ i) :
    τ.length = i := by
  have := congrArg List.length h
  simpa using this

/-- Uniform probability is invariant under an equivalence of finite types. -/
lemma prob_equiv' {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (P : B → Prop) :
    prob (fun a => P (e a)) = prob P := by
  classical
  rw [prob_def, prob_def, Fintype.card_congr e]
  congr 2
  exact_mod_cast Finset.card_equiv e (fun a => by simp)

/-- Two transcripts that agree at the indices `≤ t` have the same `w_A`, `β`, the same oracles
`w_i` for `i + 1 ≤ t` and the same challenges `r_i` for `i + 1 ≤ t`. -/
lemma parse_congr {τ τ' : List (EntK (F := F) (L := L) ℓ κ)} {t : ℕ}
    (h : ∀ s ≤ t, τ[s]? = τ'[s]?) :
    pWA τ = pWA τ' ∧ pBeta τ = pBeta τ' ∧ (∀ i, i + 1 ≤ t → pOrc τ i = pOrc τ' i) ∧
      (∀ i, i + 1 ≤ t → pR τ i = pR τ' i) := by
  refine ⟨by simp [pWA, h 0 (Nat.zero_le _)], by simp [pBeta, h 0 (Nat.zero_le _)],
    fun i hi => by simp [pOrc, h (i + 1) hi], fun i hi => by simp [pR, h (i + 1) hi]⟩

lemma getElem?_append_lt' (τ : List (EntK (F := F) (L := L) ℓ κ)) (e : EntK ℓ κ) {s : ℕ}
    (hs : s < τ.length) : (τ ++ [e])[s]? = τ[s]? := List.getElem?_append_left hs

lemma getElem?_append_len' (τ : List (EntK (F := F) (L := L) ℓ κ)) (e : EntK ℓ κ) :
    (τ ++ [e])[τ.length]? = some e := by simp

/-- The words of the parsed prover at the levels `0 < i < ℓ`. -/
lemma pFT_W (τ : List (EntK (F := F) (L := L) ℓ κ)) (w0 : L → F) (r : ℕ → F) {i : ℕ}
    (hi0 : 0 < i) (hi : i < ℓ) : (pFT τ).W ℓ w0 r i = pOrc τ i := by
  rw [(pFT τ).W_mid ℓ w0 hi0 hi]; rfl

/-- Congruence of the parsed words below level `j ≤ ℓ`. -/
lemma pFT_W_congr {τ τ' : List (EntK (F := F) (L := L) ℓ κ)} (w0 : L → F) (r r' : ℕ → F)
    {t : ℕ} (ht : t < ℓ) (h : 0 < t → pOrc τ t = pOrc τ' t) :
    (pFT τ).W ℓ w0 r t = (pFT τ').W ℓ w0 r' t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · rfl
  · rw [pFT_W _ _ _ ht0 ht, pFT_W _ _ _ ht0 ht, h ht0]

end Parse

/-! ### Theorem 7.11, "Consequently" -/

section Main

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F] {L : Subgroup Fˣ} [Fintype L]
  {m ℓ : ℕ} (κ : ℕ) {δ : ℚ} {R : ℕ}

/-- **Theorem 7.11 ("Consequently")**: `Π_KF` is round-by-round knowledge sound for `R^δ_KF`
(Definition 3.7) with doomed set `DK`, extractor `ExtK` and errors `εK`. -/
theorem rbr_knowledge (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ)
    (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) :
    IsRBRKnowledgeWith (VK (F := F) (L := L) (ℓ := ℓ) (κ := κ) m) (RK m δ) (εK (L := L) ℓ κ δ)
      (DK m δ) (ExtK m R) := by
  classical
  have hδR : δ ≤ δstar R := hδ
  refine ⟨fun x => by simp [DK], ?_, ?_⟩
  · -- condition 2
    rintro ⟨w, z, v⟩ i τ hτ hD msg hε
    have hlen := length_of_isPartial' hτ
    by_cases hi : (i : ℕ) < ℓ + 1
    · -- rounds `0, …, ℓ`
      let c0 : ChK (F := F) (L := L) ℓ κ i := (chF (F := F) (L := L) (κ := κ) hi).symm 0
      let τ0 := τ ++ [((msg, ⟨i, c0⟩) : EntK (F := F) (L := L) ℓ κ)]
      -- the data of `τ ++ [(msg, c)]` for a free challenge `c`
      have hcur : ∀ c : ChK (F := F) (L := L) ℓ κ i,
          (τ ++ [((msg, ⟨i, c⟩) : EntK (F := F) (L := L) ℓ κ)])[(i : ℕ)]? = some (msg, ⟨i, c⟩) := by
        intro c; rw [← hlen]; exact getElem?_append_len' _ _
      have hcur0 : τ0[(i : ℕ)]? = some (msg, ⟨i, c0⟩) := hcur c0
      have hentR : ∀ c : ChK (F := F) (L := L) ℓ κ i,
          entR ((msg, ⟨i, c⟩) : EntK (F := F) (L := L) ℓ κ) = chF hi c := by
        intro c; simp [entR, hi]
      by_cases hi0 : (i : ℕ) = 0
      · -- round `1` of the paper (item 1)
        simp only [εK, if_pos hi0] at hε
        by_contra hnw
        have hnw' : ∀ α : Table F (m + ℓ), ¬ RelKF δ w z v α := by
          intro α hα
          exact hnw (extKF_witness hL (by omega) hδR hα)
        -- `¬ D` after round `0` is "not doomed" at level `0` for `β = c`
        have hpar : ∀ c : ChK (F := F) (L := L) ℓ κ i,
            ¬ DK m δ (w, z, v) (τ ++ [((msg, ⟨i, c⟩) : EntK (F := F) (L := L) ℓ κ)]) ↔
              NotDoomedFT (pFT τ0) m ℓ (wbat w msg.1 z v (chF hi c)) δ (pR τ0) 0 := by
          intro c
          have hl : (τ ++ [((msg, ⟨i, c⟩) : EntK (F := F) (L := L) ℓ κ)]).length = 1 := by
            simp [hlen, hi0]
          simp only [DK, hl, one_ne_zero, if_false, show 1 ≤ ℓ + 1 by omega, if_true, not_not,
            Nat.sub_self]
          have hWA : pWA (τ ++ [((msg, ⟨i, c⟩) : EntK (F := F) (L := L) ℓ κ)]) = msg.1 := by
            simp [pWA, show (0 : ℕ) = i by omega, hcur]
          have hB : pBeta (τ ++ [((msg, ⟨i, c⟩) : EntK (F := F) (L := L) ℓ κ)]) = chF hi c := by
            simp [pBeta, show (0 : ℕ) = i by omega, hcur, hentR]
          simp only [pW0, hWA, hB]
          rfl
        have hprob : prob (fun c : ChK (F := F) (L := L) ℓ κ i =>
            ¬ DK m δ (w, z, v) (τ ++ [((msg, ⟨i, c⟩) : EntK (F := F) (L := L) ℓ κ)])) =
            prob (fun β : F => NotDoomedFT (pFT τ0) m ℓ (wbat w msg.1 z v β) δ (pR τ0) 0) := by
          rw [← prob_equiv' (chF (F := F) (L := L) (κ := κ) hi)]
          congr 1; funext c; exact propext (hpar c)
        rw [hprob] at hε
        have hcnt := rbr_item1 hL hR hδ0 hδ w msg.1 z v hnw' (fun _ => pFT τ0) (fun _ => pR τ0)
        have : prob (fun β : F => NotDoomedFT (pFT τ0) m ℓ (wbat w msg.1 z v β) δ (pR τ0) 0) ≤
            2 * (Nat.card L : ℚ) / Fintype.card F := by
          rw [prob_def, card_filter_eq_ncard]
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          exact_mod_cast hcnt
        linarith
      · -- rounds `2, …, ℓ + 1` of the paper (item 2), level `k = i - 1`
        exfalso
        simp only [εK, if_neg hi0, if_pos hi] at hε
        obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨i - 1, by omega⟩
        have hkℓ : k < ℓ := by omega
        -- the reference data
        set P0 := pFT τ0
        set w00 := pW0 τ0 m (w, z, v)
        set r0 := pR τ0
        have hC0 : P0.Causal := fun _ _ _ _ => rfl
        -- `τ` is doomed at level `k`
        have hdoom : ¬ NotDoomedFT P0 m ℓ w00 δ r0 k := by
          have hD' : ¬ NotDoomedFT (pFT τ) m ℓ (pW0 τ m (w, z, v)) δ (pR τ) k := by
            have h := hD
            simp only [DK, hlen, hk, Nat.add_sub_cancel] at h
            rw [if_neg (by omega), if_pos (by omega)] at h
            exact h
          obtain ⟨e1, e2, e3, e4⟩ := parse_congr (τ := τ) (τ' := τ0) (t := k) (fun s hs => by
            rw [getElem?_append_lt' _ _ (by omega)])
          have hw0 : pW0 τ m (w, z, v) = w00 := by simp only [pW0, w00, e1, e2]
          rw [hw0] at hD'
          rwa [NotDoomedFT_congr (m := m) (δ := δ) (P' := P0) (r' := r0) (by omega) (fun t ht =>
            ⟨pFT_W_congr _ _ _ (by omega) (fun _ => e3 t (by omega)), e4 t (by omega)⟩)] at hD'
        have hcnt := rbr_item2 hL hδ0 hδ P0 hC0 w00 r0 hkℓ hdoom
        -- `¬ D` after round `i` is "not doomed" at level `k + 1` with `r_{k+1} = c`
        have hpar : ∀ c : ChK (F := F) (L := L) ℓ κ i,
            ¬ DK m δ (w, z, v) (τ ++ [((msg, ⟨i, c⟩) : EntK (F := F) (L := L) ℓ κ)]) ↔
              NotDoomedFT P0 m ℓ w00 δ (Function.update r0 k (chF hi c)) (k + 1) := by
          intro c
          set τc := τ ++ [((msg, ⟨i, c⟩) : EntK (F := F) (L := L) ℓ κ)]
          have hl : τc.length = k + 2 := by simp [τc, hlen, hk]
          simp only [DK, hl, show k + 2 ≠ 0 by omega, if_false, show k + 2 ≤ ℓ + 1 by omega,
            if_true, not_not, show k + 2 - 1 = k + 1 by omega]
          obtain ⟨e1, e2, e3, e4⟩ := parse_congr (τ := τc) (τ' := τ0) (t := k) (fun s hs => by
            simp only [τc, τ0]
            rw [getElem?_append_lt' _ _ (by omega), getElem?_append_lt' _ _ (by omega)])
          have hw0 : pW0 τc m (w, z, v) = w00 := by simp only [pW0, w00, e1, e2]
          -- the oracle of round `i` and the challenge `r_{k+1}`
          have horc : pOrc τc k = pOrc τ0 k := by
            simp only [pOrc, ← hk, τc, τ0, hcur]
            rfl
          have hrk : pR τc k = chF hi c := by
            simp only [pR, ← hk, τc, hcur, Option.map_some, Option.getD_some, hentR]
          rw [hw0]
          apply NotDoomedFT_congr (by omega)
          intro t ht
          rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
          · exact ⟨pFT_W_congr _ _ _ (by omega) (fun _ => e3 t (by omega)),
              by rw [Function.update_of_ne (by omega)]; exact e4 t (by omega)⟩
          · exact ⟨pFT_W_congr _ _ _ (by omega) (fun _ => horc),
              by rw [Function.update_self]; exact hrk⟩
        have hprob : prob (fun c : ChK (F := F) (L := L) ℓ κ i =>
            ¬ DK m δ (w, z, v) (τ ++ [((msg, ⟨i, c⟩) : EntK (F := F) (L := L) ℓ κ)])) =
            prob (fun a : F => NotDoomedFT P0 m ℓ w00 δ (Function.update r0 k a) (k + 1)) := by
          rw [← prob_equiv' (chF (F := F) (L := L) (κ := κ) hi)]
          congr 1; funext c; exact propext (hpar c)
        rw [hprob] at hε
        have : prob (fun a : F => NotDoomedFT P0 m ℓ w00 δ (Function.update r0 k a) (k + 1)) ≤
            (Nat.card (lv L i) : ℚ) / Fintype.card F := by
          rw [prob_def, card_filter_eq_ncard, hk]
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          exact_mod_cast hcnt
        linarith
    · -- round `ℓ + 1` (item 3)
      exfalso
      have hiℓ : (i : ℕ) = ℓ + 1 := by omega
      simp only [εK, show (i : ℕ) ≠ 0 by omega, if_false, if_neg hi] at hε
      let c0 : ChK (F := F) (L := L) ℓ κ i := (chQ (F := F) (L := L) (κ := κ) hi).symm (fun _ => 1)
      let τ0 := τ ++ [((msg, ⟨i, c0⟩) : EntK (F := F) (L := L) ℓ κ)]
      set P0 := pFT τ0
      set w00 := pW0 τ0 m (w, z, v)
      set r0 := pR τ0
      have hD' : ¬ NotDoomedFT (pFT τ) m ℓ (pW0 τ m (w, z, v)) δ (pR τ) ℓ := by
        simp only [DK, hlen, hiℓ, show ℓ + 1 ≠ 0 by omega, if_false, le_refl, if_true,
          Nat.add_sub_cancel] at hD
        exact hD
      obtain ⟨e1, e2, e3, e4⟩ := parse_congr (τ := τ) (τ' := τ0) (t := ℓ) (fun s hs => by
        rw [getElem?_append_lt' _ _ (by omega)])
      have hw0 : pW0 τ m (w, z, v) = w00 := by simp only [pW0, w00, e1, e2]
      have hdoom : ¬ NotDoomedFT P0 m ℓ w00 δ r0 ℓ := by
        rw [hw0] at hD'
        rwa [NotDoomedFT_congr (m := m) (δ := δ) (P' := P0) (r' := r0) le_rfl (fun t ht =>
          ⟨pFT_W_congr _ _ _ ht (fun _ => e3 t (by omega)), e4 t (by omega)⟩)] at hD'
      have hcur : ∀ c : ChK (F := F) (L := L) ℓ κ i,
          (τ ++ [((msg, ⟨i, c⟩) : EntK (F := F) (L := L) ℓ κ)])[ℓ + 1]? = some (msg, ⟨i, c⟩) := by
        intro c; rw [show ℓ + 1 = τ.length by omega]; exact getElem?_append_len' _ _
      -- the full transcript `τ ++ [(msg, c)]` has the data of `τ0` and the query points `c`
      have hpar : ∀ c : ChK (F := F) (L := L) ℓ κ i,
          ¬ DK m δ (w, z, v) (τ ++ [((msg, ⟨i, c⟩) : EntK (F := F) (L := L) ℓ κ)]) ↔
            msg.2.2 ∈ degreeLT F (2 ^ m) ∧ P0.Accepts ℓ w00 r0 (chQ hi c) := by
        intro c
        set τc := τ ++ [((msg, ⟨i, c⟩) : EntK (F := F) (L := L) ℓ κ)]
        have hl : τc.length = ℓ + 2 := by simp [τc, hlen, hiℓ]
        simp only [DK, hl, show ℓ + 2 ≠ 0 by omega, if_false, show ¬ (ℓ + 2 ≤ ℓ + 1) by omega,
          not_not, VK]
        obtain ⟨f1, f2, f3, f4⟩ := parse_congr (τ := τc) (τ' := τ0) (t := ℓ) (fun s hs => by
          simp only [τc, τ0]
          rw [getElem?_append_lt' _ _ (by omega), getElem?_append_lt' _ _ (by omega)])
        have hfin : pFin τc = msg.2.2 := by simp [pFin, τc, hcur]
        have hfin0 : pFin τ0 = msg.2.2 := by simp [pFin, τ0, hcur]
        have hxi : pXi τc = chQ hi c := by simp [pXi, τc, hcur, entQ, hi]
        have horcℓ : pOrc τc ℓ = pOrc τ0 ℓ := by simp [pOrc, τc, τ0, hcur]
        have hrℓ : pR τc ℓ = pR τ0 ℓ := by
          simp [pR, τc, τ0, hcur, entR, hi]
        have hFT : pFT τc = P0 := by
          simp only [pFT, P0]
          congr 1
          · funext j _
            rcases Nat.lt_or_ge j ℓ with hj | hj
            · exact f3 j (by omega)
            · rcases Nat.eq_or_lt_of_le hj with rfl | hj'
              · exact horcℓ
              · have h1 : τc[j + 1]? = none :=
                  List.getElem?_eq_none (by simp [τc, hlen, hiℓ]; omega)
                have h2 : τ0[j + 1]? = none :=
                  List.getElem?_eq_none (by simp [τ0, hlen, hiℓ]; omega)
                simp [pOrc, h1, h2]
          · funext _; rw [hfin, hfin0]
        have hr : pR τc = r0 := by
          funext t
          rcases Nat.lt_or_ge t ℓ with ht | ht
          · exact f4 t (by omega)
          · rcases Nat.eq_or_lt_of_le ht with rfl | ht'
            · exact hrℓ
            · have h1 : τc[t + 1]? = none :=
                List.getElem?_eq_none (by simp [τc, hlen, hiℓ]; omega)
              have h2 : τ0[t + 1]? = none :=
                List.getElem?_eq_none (by simp [τ0, hlen, hiℓ]; omega)
              simp [pR, r0, h1, h2]
        have hw0c : pW0 τc m (w, z, v) = w00 := by simp only [pW0, w00, f1, f2]
        rw [hfin, hFT, hw0c, hr, hxi]
      have hprob : prob (fun c : ChK (F := F) (L := L) ℓ κ i =>
          ¬ DK m δ (w, z, v) (τ ++ [((msg, ⟨i, c⟩) : EntK (F := F) (L := L) ℓ κ)])) =
          prob (fun ξ : Fin κ → L => msg.2.2 ∈ degreeLT F (2 ^ m) ∧ P0.Accepts ℓ w00 r0 ξ) := by
        rw [← prob_equiv' (chQ (F := F) (L := L) (κ := κ) hi)]
        congr 1; funext c; exact propext (hpar c)
      rw [hprob] at hε
      by_cases hdeg : msg.2.2 ∈ degreeLT F (2 ^ m)
      · have hdegP : P0.DegOK m := by
          intro r
          show pFin τ0 ∈ _
          simpa [pFin, τ0, show ℓ + 1 = τ.length by omega] using hdeg
        have := rbr_item3 hℓ P0 hdegP w00 r0 hdoom κ
        simp only [hdeg, true_and] at hε
        linarith
      · simp only [hdeg, false_and, prob_false] at hε
        have hR' : (0 : ℚ) < 1 / 2 ^ R := by positivity
        have : (0 : ℚ) ≤ (1 - δ) ^ κ := pow_nonneg (by linarith) κ
        linarith
  · -- condition 3
    rintro x τ hτ hD
    have hlen := length_of_isPartial' hτ
    simp only [DK, hlen, show ℓ + 2 ≠ 0 by omega, if_false, show ¬ (ℓ + 2 ≤ ℓ + 1) by omega]
      at hD
    exact hD

/-- **Theorem 7.11**, in the form of Definition 3.7 (`RBRKnowledge`). -/
theorem rbr_knowledge' (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ)
    (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) :
    RBRKnowledge (VK (F := F) (L := L) (ℓ := ℓ) (κ := κ) m) (RK m δ) (εK (L := L) ℓ κ δ) :=
  ⟨_, _, rbr_knowledge κ hL hR hℓ hδ0 hδ⟩

omit [Fintype F] [DecidableEq F] [Fintype L] in
/-- The uniqueness property `eq:dist-unique` for `dist = Δ^fib₀` (Lemma 6.3(2)). -/
theorem uniqueWithin_fib (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 1 ≤ R)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) :
    UniqueWithin (encode L (n := m + ℓ) (F := F)) fibDist δ := by
  intro w f f' h1 h1'
  haveI := hL.finite
  have hNM : 2 ^ (m + ℓ) ≤ Nat.card L := by
    rw [show Nat.card L = 2 ^ (m + ℓ + R) from hL]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrate : rate L (2 ^ (m + ℓ)) = 1 / 2 ^ R := by
    rw [rate, show Nat.card L = 2 ^ (m + ℓ + R) from hL]; push_cast
    rw [pow_add (2 : ℚ) (m + ℓ) R]
    have : (2 : ℚ) ^ (m + ℓ) ≠ 0 := by positivity
    field_simp
  have hδ' : δ ≤ (1 - rate L (2 ^ (m + ℓ))) / 2 := by rw [hrate]; exact hδ
  exact encode_fib_unique hNM (hL.neg_one_mem (by omega)) (two_ne_zero_of_smooth hL (by omega))
    hδ' w h1 h1'

/-- **Corollary 7.12(3) in the generic framework** (Lemma 3.11): `Π_KF` is
`∑ ε_i`-evaluation binding (Definition 3.10). -/
theorem rbr_binding (hL : IsSmoothDomain L (m + ℓ + R)) (hR : 2 ≤ R) (hℓ : 1 ≤ ℓ)
    (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) :
    EvalBinding (VK (F := F) (L := L) (ℓ := ℓ) (κ := κ) m) (∑ i, εK (L := L) ℓ κ δ i) := by
  have hR' : (0 : ℚ) < 1 / 2 ^ R := by positivity
  refine rbr_knowledge_binding (encode L) fibDist δ _ _ (εK (L := L) ℓ κ δ) ?_
    (rbr_knowledge' κ hL hR hℓ hδ0 hδ) (uniqueWithin_fib hL (by omega) hδ)
  intro i
  simp only [εK]
  split_ifs
  · positivity
  · positivity
  · exact pow_nonneg (by linarith) κ

end Main

end KroneckerFRI
