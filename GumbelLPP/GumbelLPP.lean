import Mathlib.Analysis.SpecialFunctions.Log.Basic                   -- For aesop

-- Unused scopes in this specific snippet (Uncomment if needed)
-- import Mathlib.Algebra.BigOperators.Group.Finset -- For open scoped BigOperators
-- import Mathlib.Data.Set.Pointwise.Basic          -- For open scoped Pointwise

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Definition of the function h_N(x) used in the coupling.
-/
noncomputable def h (N : ℝ) (x : ℝ) : ℝ :=
  - Real.log (N * (1 - Real.exp (-Real.exp (-x) / N))) - x
