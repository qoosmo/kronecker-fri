/-
KroneckerFRI/Audit.lean
Prints the axioms used by the main theorems.  The expected output for every theorem is a subset
of `[propext, Classical.choice, Quot.sound, KBFold.bciks_curves]`: the three standard axioms of
Lean and Mathlib, and correlated agreement for curves (Theorem 2.16 of the paper), which is the
only project-specific assumption.
-/
import KroneckerFRI.Generic
import KroneckerFRI.Batch
import KroneckerFRI.R1CS

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
-- Research note: sumcheck-free inner products (table form)
#print axioms KroneckerFRI.eval_table
#print axioms KroneckerFRI.inner_product
#print axioms KroneckerFRI.eval_revP
#print axioms KroneckerFRI.splitG_iff
#print axioms KroneckerFRI.identityG
#print axioms KroneckerFRI.wrev_ev
#print axioms KroneckerFRI.curve_agreement
#print axioms KroneckerFRI.honestIP_prob_one
#print axioms KroneckerFRI.batching_IP
#print axioms KroneckerFRI.soundness_IP
#print axioms KroneckerFRI.soundnessC_IP
#print axioms KroneckerFRI.knowledge_IP
#print axioms KroneckerFRI.binding_IP
#print axioms KroneckerFRI.deep_step
#print axioms KroneckerFRI.deep_honest
#print axioms KroneckerFRI.ft_family_bound
#print axioms KroneckerFRI.batching_Had
#print axioms KroneckerFRI.prob_bad_le
#print axioms KroneckerFRI.soundness_Had
#print axioms KroneckerFRI.soundnessC_Had
#print axioms KroneckerFRI.knowledge_Had
#print axioms KroneckerFRI.honestHad_accepts
#print axioms KroneckerFRI.honestHad_prob
#print axioms KroneckerFRI.curve_agreement_idx
#print axioms KroneckerFRI.virtG_value
#print axioms KroneckerFRI.batching_B
#print axioms KroneckerFRI.prob_bad_had
#print axioms KroneckerFRI.prob_bad_B
#print axioms KroneckerFRI.soundness_B
#print axioms KroneckerFRI.soundnessC_B
#print axioms KroneckerFRI.knowledge_B
#print axioms KroneckerFRI.bwords_honest
#print axioms KroneckerFRI.honestB_accepts
#print axioms KroneckerFRI.honestB_prob
#print axioms KroneckerFRI.logup_prob
#print axioms KroneckerFRI.weighted_matVec
#print axioms KroneckerFRI.prob_lookupFail
#print axioms KroneckerFRI.lincheck_reduction
#print axioms KroneckerFRI.prob_two_phase
#print axioms KroneckerFRI.lincheck_sound
#print axioms KroneckerFRI.r1cs_sound
#print axioms KroneckerFRI.batching_A
#print axioms KroneckerFRI.prob_bad_A
#print axioms KroneckerFRI.soundness_A
#print axioms KroneckerFRI.knowledge_A
#print axioms KroneckerFRI.awords_honest
#print axioms KroneckerFRI.honestA_accepts
#print axioms KroneckerFRI.honestA_prob
#print axioms KroneckerFRI.r1_bridge
#print axioms KroneckerFRI.tA_r1stmts
#print axioms KroneckerFRI.r1cs_soundness
