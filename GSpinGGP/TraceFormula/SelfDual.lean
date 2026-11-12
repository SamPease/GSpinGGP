/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.GSpin
import GSpinGGP.Foundations.LocalGroups

/-!
# Self-dual measures on Lie subalgebras: shared lemmas

* `selfDualMeasure_isAddHaar`: `selfDualMeasure B ψ` is a Haar measure as soon as some self-dual
  measure exists (otherwise it is the junk value `0`).
* `measurableSingletonClass_lie`, `locallyCompactSpace_lie`: topological facts about a Lie
  subalgebra of a finite-dimensional algebra with its module topology.
* `ggp_bilin_symm`: the trace form of a GGP datum is symmetric.
-/

open MeasureTheory

set_option linter.style.haveILetI false

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

section SelfDual

variable {F : Type*} [NontriviallyNormedField F]
variable {V : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V] [MeasurableSpace V]

/-- In general, `selfDualMeasure B ψ` is a genuine (nonzero) Haar measure as soon as some self-dual
measure exists. -/
theorem selfDualMeasure_isAddHaar {B : LinearMap.BilinForm F V} {ψ : NontrivialAddChar F}
    (h : ∃ μ, IsSelfDual μ B ψ) : (selfDualMeasure B ψ).IsAddHaarMeasure := by
  unfold selfDualMeasure
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec.1

end SelfDual

section Lie

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
variable {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A]
  [IsModuleTopology F A]

lemma measurableSingletonClass_lie (𝔤 : LieSubalgebra F A) : MeasurableSingletonClass ↥𝔤 := by
  haveI := t2Space_of_moduleTopology F A
  infer_instance

/-- A Lie subalgebra of `A` is locally compact (finite-dimensional subspaces of a Hausdorff TVS
over a complete field are closed). -/
lemma locallyCompactSpace_lie (𝔤 : LieSubalgebra F A) : LocallyCompactSpace ↥𝔤 := by
  haveI := t2Space_of_moduleTopology F A
  haveI := isTopologicalRing_of_moduleTopology F A
  haveI := locallyCompactSpace_of_moduleTopology F A
  haveI : ContinuousSMul F A := IsModuleTopology.toContinuousSMul F A
  have hcl : IsClosed (𝔤.toSubmodule : Set A) := Submodule.closed_of_finiteDimensional _
  exact hcl.locallyCompactSpace

/-- The trace form `b(X,Y) = tr(L_{XY})` of a GGP datum is symmetric
(`tr(L_X L_Y) = tr(L_Y L_X)`). -/
theorem ggp_bilin_symm (d : GGPData F) (X Y : d.ambient) : d.bilin X Y = d.bilin Y X := by
  rw [GGPData.bilin_apply, GGPData.bilin_apply, LinearMap.mulLeft_mul, ← Module.End.mul_eq_comp,
    LinearMap.trace_mul_comm, Module.End.mul_eq_comp, ← LinearMap.mulLeft_mul]

end Lie

end GSpinGGP
