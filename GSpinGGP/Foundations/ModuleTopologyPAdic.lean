/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalGroups
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Finite-dimensional vector spaces over a `p`-adic field

A finite-dimensional `F`-vector space `V` with the module topology, `F` a `p`-adic field, is
homeomorphic to `F^n` through basis coordinates (Tau Ceti's
`TauCeti.ModuleTopology.equivFunHomeomorph`). Hence it is second countable (and locally compact,
`TauCeti.ModuleTopology.locallyCompactSpace`), so Haar measures on it are unique up to a positive
scalar, and it carries test functions (locally constant, compactly supported) not vanishing at `0`.
-/

noncomputable section

open Module

namespace GSpinGGP

variable (F : Type*) [NontriviallyNormedField F] [PAdicField F]
variable (V : Type*) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V]
  [IsModuleTopology F V]

include F

/-- `V` is second countable. -/
theorem secondCountableTopology_of_finiteDimensional : SecondCountableTopology V := by
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  exact (TauCeti.ModuleTopology.equivFunHomeomorph (finBasis F V)).isEmbedding
    |>.secondCountableTopology

/-- `V` carries a test function (locally constant, compactly supported) not vanishing at `0`:
the indicator of the preimage of the unit ball of `F^n`, a compact open subgroup. -/
theorem exists_isTestFn_ne_zero : ∃ f : V → ℂ, IsTestFn f ∧ f 0 ≠ 0 := by
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  set e := TauCeti.ModuleTopology.equivFunHomeomorph (finBasis F V)
  set S : Set (Fin (finrank F V) → F) := Metric.closedBall 0 1
  have hS : IsClopen S := IsUltrametricDist.isClopen_closedBall (x := 0) one_ne_zero
  have hSc : IsCompact S := isCompact_closedBall 0 1
  refine ⟨S.indicator 1 ∘ e, ⟨?_, ?_⟩, ?_⟩
  · rw [← LocallyConstant.coe_charFn ℂ hS]
    exact (LocallyConstant.charFn ℂ hS).isLocallyConstant.comp_continuous e.continuous
  · exact (HasCompactSupport.intro' hSc hS.isClosed
      fun x hx => Set.indicator_of_notMem hx _).comp_homeomorph e
  · simp [S, e]

end GSpinGGP
