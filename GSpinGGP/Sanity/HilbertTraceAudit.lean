/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.HilbertTrace

/-!
# Sanity checks for `hilbertTrace`

Values of `GSpinGGP.hilbertTrace` in small cases: the identity of `ℂⁿ` has trace `n`, the operator
`2 • id` on `ℂ³` has trace `6`, the zero operator has trace `0`, a rank-one operator has trace
`⟪x, y⟫`, and the identity of `ℓ²(ℕ, ℂ)`, which is not trace class, gets the junk value `0`.
-/

open scoped InnerProductSpace lp

namespace GSpinGGP.HilbertTraceAudit

/-- The identity of `ℂⁿ` has trace `n`. -/
example (n : ℕ) :
    hilbertTrace (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n))) = n := by
  rw [hilbertTrace_eq_trace]
  simp

/-- The operator `2 • id` on `ℂ³` has trace `6`. -/
example : hilbertTrace ((2 : ℂ) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 3))) = 6 := by
  rw [hilbertTrace_smul, hilbertTrace_eq_trace]
  norm_num

/-- The zero operator has trace `0`. -/
example : hilbertTrace (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) = 0 :=
  hilbertTrace_zero

/-- The rank-one operator `v ↦ ⟪x, v⟫ • y` has trace `⟪x, y⟫`, also on an infinite-dimensional
space. -/
example (x y : ℓ²(ℕ, ℂ)) : hilbertTrace ((innerSL ℂ x).smulRight y) = ⟪x, y⟫_ℂ :=
  hilbertTrace_innerSL_smulRight x y

/-- `ℓ²(ℕ, ℂ)` is infinite-dimensional: its standard Hilbert basis is an infinite orthonormal,
hence linearly independent, family. -/
theorem not_finiteDimensional_l2 : ¬ FiniteDimensional ℂ ℓ²(ℕ, ℂ) := by
  intro h
  have hli := (default : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ)).orthonormal.linearIndependent
  have := hli.finite
  exact not_finite ℕ

/-- The identity of `ℓ²(ℕ, ℂ)` is not trace class, so its trace is the junk value `0`. -/
example : hilbertTrace (ContinuousLinearMap.id ℂ ℓ²(ℕ, ℂ)) = 0 :=
  hilbertTrace_id_of_not_finiteDimensional not_finiteDimensional_l2

/-- The trace through any Hilbert basis agrees with `hilbertTrace` for a rank-one operator on
`ℓ²(ℕ, ℂ)`. -/
example (x y : ℓ²(ℕ, ℂ)) :
    HasSum (fun i ↦ ⟪(default : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ)) i,
      (innerSL ℂ x).smulRight y ((default : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ)) i)⟫_ℂ) ⟪x, y⟫_ℂ := by
  rw [← hilbertTrace_innerSL_smulRight]
  exact hasSum_hilbertTrace _ (TauCeti.smulRight_mem_nuclearOperators _ _)

end GSpinGGP.HilbertTraceAudit
