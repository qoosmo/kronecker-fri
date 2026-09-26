/-
KroneckerFRI/Audit.lean
Prints the axioms used by the main theorems.  The expected output for every theorem is a subset
of `[propext, Classical.choice, Quot.sound, KBFold.bciks_curves]`: the three standard axioms of
Lean and Mathlib, and correlated agreement for curves (Theorem 2.16 of the paper), the single
axiom of the project.
-/
import KroneckerFRI.Generic
import KroneckerFRI.Batch

open KroneckerFRI

-- §4
#print axioms KroneckerFRI.extraction
#print axioms KroneckerFRI.split_iff
#print axioms KroneckerFRI.identity_lemma
#print axioms KroneckerFRI.bilinear
#print axioms KroneckerFRI.kernel_reflect
#print axioms KroneckerFRI.cube_sum_half
-- §5
#print axioms KroneckerFRI.coeff_pfoldUp
#print axioms KroneckerFRI.chain_final
#print axioms KroneckerFRI.fpt_sound
#print axioms KroneckerFRI.acceptsC_iff
#print axioms KroneckerFRI.fptC_sound
#print axioms KroneckerFRI.sum_arity_lengths_lt
#print axioms KroneckerFRI.orcC_virtual_local
#print axioms KroneckerFRI.acceptsC_congr
-- §6
#print axioms KroneckerFRI.virt_honest
#print axioms KroneckerFRI.honestKF_prob_one
#print axioms KroneckerFRI.inv_agree_le
-- §7
#print axioms KroneckerFRI.batching_witness
#print axioms KroneckerFRI.soundness
#print axioms KroneckerFRI.soundnessC
#print axioms KroneckerFRI.rbr_knowledge
#print axioms KroneckerFRI.knowledge
#print axioms KroneckerFRI.binding
#print axioms KroneckerFRI.rbr_binding
-- §11
#print axioms KroneckerFRI.batch_soundness
#print axioms KroneckerFRI.batch_knowledge
#print axioms KroneckerFRI.batch_binding
