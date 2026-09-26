/-
KBFold/BCIKS.lean  (Kronecker-FRI version)
The correlated-agreement theorem of Ben-Sasson, Carmon, Ishai, Kopparty and Saraf for
parameterised curves, in the unique-decoding regime (Theorem 2.16 of the Kronecker-FRI paper,
`thm:curves`), stated as the single axiom of the project.

The version for lines (`t = 1`), which is the axiom of the KBFold formalisation, is derived
from it below as the theorem `bciks_unique`, so that the modules shared with KBFold
(`KBFold/Fibre.lean`) use it unchanged.

Statement (paper, Theorem 2.16; [BCIKS23, Theorem 1.5 with Theorem 1.2]):
* `F` is a finite field and `L ≤ Fˣ` a smooth domain of order `M = 2^μ`;
* `𝒞 = RS_F[L,d]` with `1 ≤ d ≤ M`, rate `ρ = d/M`, and `0 < δ ≤ (1-ρ)/2`;
* `t ≥ 1` and `u_0, …, u_t ∈ F^L`, with the curve `u_β = ∑_{i ≤ t} β^i u_i`;
* `Z = {β ∈ F : Δ(u_β, 𝒞) ≤ δ}`;
* if `|Z| > t M`, there are `L' ⊆ L` with `|L'| ≥ (1-δ)M` and codewords `ĉ_0, …, ĉ_t ∈ 𝒞`
  such that `u_i = ĉ_i` on `L'` for every `i`.
-/
import KBFold.Domain

open Finset

namespace KBFold

/-- **Theorem 2.16 of the Kronecker-FRI paper** ([BCIKS23, Theorem 1.5 with Theorem 1.2],
correlated agreement for curves of degree `t` in the unique-decoding regime).
This is the only axiom of the formalisation. -/
axiom bciks_curves {F : Type*} [Field F] [Fintype F] (L : Subgroup Fˣ) (μ : ℕ)
    (hL : IsSmoothDomain L μ) (d : ℕ) (hd : 1 ≤ d) (hdM : d ≤ Nat.card L)
    (δ : ℚ) (hδ0 : 0 < δ) (hδ : δ ≤ (1 - rate L d) / 2) (t : ℕ) (ht : 1 ≤ t)
    (u : Fin (t + 1) → L → F)
    (hZ : t * Nat.card L <
      {β : F | DistLE (∑ i : Fin (t + 1), β ^ (i : ℕ) • u i) (RS L d : Set (L → F)) δ}.ncard) :
    ∃ L' : Set L, (1 - δ) * Nat.card L ≤ L'.ncard ∧
      ∃ c : Fin (t + 1) → L → F, (∀ i, c i ∈ RS L d) ∧ ∀ ξ ∈ L', ∀ i, u i ξ = c i ξ

/-- Correlated agreement for lines (`t = 1`): Theorem 2.23 of the KBFold paper, the axiom of the
KBFold formalisation, here a consequence of `bciks_curves`. -/
theorem bciks_unique {F : Type*} [Field F] [Fintype F] (L : Subgroup Fˣ) (μ : ℕ)
    (hL : IsSmoothDomain L μ) (d : ℕ) (hd : 1 ≤ d) (hdM : d ≤ Nat.card L)
    (δ : ℚ) (hδ0 : 0 < δ) (hδ : δ ≤ (1 - rate L d) / 2) (u0 u1 : L → F)
    (hS : Nat.card L < {r : F | DistLE (u0 + r • u1) (RS L d : Set (L → F)) δ}.ncard) :
    ∃ L' : Set L, (1 - δ) * Nat.card L ≤ L'.ncard ∧
      ∃ c0 ∈ RS L d, ∃ c1 ∈ RS L d, ∀ ξ ∈ L', u0 ξ = c0 ξ ∧ u1 ξ = c1 ξ := by
  let u : Fin 2 → L → F := ![u0, u1]
  have hcurve : ∀ β : F, (∑ i : Fin 2, β ^ (i : ℕ) • u i) = u0 + β • u1 := by
    intro β; simp [u]
  have hZ : 1 * Nat.card L <
      {β : F | DistLE (∑ i : Fin (1 + 1), β ^ (i : ℕ) • u i) (RS L d : Set (L → F)) δ}.ncard := by
    simp_rw [hcurve, one_mul]; exact hS
  obtain ⟨L', hL', c, hc, hagree⟩ := bciks_curves L μ hL d hd hdM δ hδ0 hδ 1 le_rfl u hZ
  exact ⟨L', hL', c 0, hc 0, c 1, hc 1, fun ξ hξ => ⟨hagree ξ hξ 0, hagree ξ hξ 1⟩⟩

end KBFold
