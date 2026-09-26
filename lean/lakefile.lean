import Lake
open Lake DSL

package KroneckerFRI where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.23.0"

/-- Modules shared with the KBFold formalisation (github.com/qoosmo/kbfold), with the axiom
replaced by correlated agreement for curves (`KBFold/BCIKS.lean`). -/
lean_lib KBFold where

@[default_target]
lean_lib KroneckerFRI where
