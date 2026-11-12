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
* `exists_mem_skewAdjoint_trace_mul_ne_zero`: the trace form `(X, Y) ↦ tr(XY)` separates the
  skew-adjoint endomorphisms of a nondegenerate symmetric bilinear form (char `≠ 2`).
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

section SkewTrace

variable {K U : Type*} [Field K] [Invertible (2 : K)] [AddCommGroup U] [Module K U]
  [Module.Finite K U]

/-- **The trace form separates skew-adjoint maps**: for a nondegenerate symmetric bilinear form `B`
(characteristic `≠ 2`) and a nonzero `B`-skew `X`, some `B`-skew `Y` has `tr(XY) ≠ 0`.  Take `u` with
`Xu ≠ 0`, `w` with `B(Xu, w) ≠ 0` and the rank-one skew map `Y = u ∧ w : x ↦ B(w, x) u − B(u, x) w`;
then `tr(XY) = B(w, Xu) − B(u, Xw) = 2 B(Xu, w)`. -/
theorem exists_mem_skewAdjoint_trace_mul_ne_zero {B : LinearMap.BilinForm K U} (hs : B.IsSymm)
    (hB : B.Nondegenerate) {X : Module.End K U} (hX : X ∈ B.skewAdjointSubmodule) (h0 : X ≠ 0) :
    ∃ Y ∈ B.skewAdjointSubmodule, LinearMap.trace K U (X * Y) ≠ 0 := by
  have hsk : ∀ x y, B (X x) y = -B x (X y) := fun x y => by
    have := (LinearMap.mem_skewAdjointSubmodule (B := B) X).mp hX x y
    simpa using this
  obtain ⟨u, hu⟩ : ∃ u, X u ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (LinearMap.ext h)
  obtain ⟨w, hw⟩ : ∃ w, B (X u) w ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (hB.1 _ h)
  refine ⟨(B w).smulRight u - (B u).smulRight w, ?_, ?_⟩
  · rw [LinearMap.mem_skewAdjointSubmodule]
    intro x y
    simp only [LinearMap.sub_apply, LinearMap.smulRight_apply, Pi.neg_apply, map_sub,
      map_smul, LinearMap.smul_apply, smul_eq_mul, map_neg]
    rw [hs.eq x u, hs.eq x w]
    ring
  · have hc : X * ((B w).smulRight u - (B u).smulRight w) =
        (B w).smulRight (X u) - (B u).smulRight (X w) := by
      ext x
      simp
    rw [hc, map_sub, LinearMap.trace_smulRight, LinearMap.trace_smulRight, hs.eq u (X w),
      hsk w u, hs.eq w (X u)]
    rw [show B (X u) w - -B (X u) w = 2 * B (X u) w by ring]
    exact mul_ne_zero (Invertible.ne_zero 2) hw

end SkewTrace

end GSpinGGP
