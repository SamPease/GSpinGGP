/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.RealLieGroup
import GSpinGGP.Foundations.RealLieStructureOfClosed
import GSpinGGP.Sanity.RealEmbeddingAudit
import TauCeti.Geometry.Lie.AutomaticSmoothness

/-!
# Sanity checks for the Lie group structure on closed subgroups of units

`RealEmbedding.realLieStructure` applies to concrete closed subgroups over `ℝ` and `ℂ`: `ℝˣ`,
`ℂˣ`, the trivial subgroup and the unit circle in `ℂˣ`. For `G = ℝˣ` (as the subgroup `⊤ ≤ ℝˣ`)
the identity between the constructed structure and Mathlib's Lie group of units of `ℝ` is smooth
in both directions, so the two have the same smooth functions. This holds for any two Lie
structures on the same topological group (Tau Ceti's automatic smoothness), so it is a
consistency check, not a test specific to this construction.
-/

namespace GSpinGGP.Sanity.RealLieGroupAudit

open GSpinGGP GSpinGGP.Sanity.RealEmbeddingAudit
open scoped ContDiff Manifold

/-- The packaged structure for `ℝˣ` (over `F = A = ℝ`) and for `ℂˣ` (over `F = A = ℂ`). -/
noncomputable def realUnits : RealLieStructure (⊤ : Subgroup ℝˣ) :=
  realId.realLieStructure ⊤ (by simp)

noncomputable example : RealLieStructure (⊤ : Subgroup ℂˣ) :=
  complexOfReal.realLieStructure ⊤ (by simp)

/-- The trivial subgroup of `ℝˣ` (a zero-dimensional Lie group). -/
noncomputable example : RealLieStructure (⊥ : Subgroup ℝˣ) :=
  realId.realLieStructure ⊥ (by simp)

/-- The unit circle `{u : |u| = 1}`, a closed proper subgroup of `ℂˣ` of positive dimension. -/
def circle : Subgroup ℂˣ where
  carrier := {u | ‖(u : ℂ)‖ = 1}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by simp_all
  inv_mem' {a} ha := by simp_all [norm_inv]

theorem isClosed_circle : IsClosed (circle : Set ℂˣ) :=
  isClosed_eq (continuous_norm.comp Units.continuous_val) continuous_const

noncomputable example : RealLieStructure circle :=
  complexOfReal.realLieStructure circle isClosed_circle

section Units

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
  RealLieStructure.normedAddCommGroup RealLieStructure.normedSpace
  RealLieStructure.finiteDimensional RealLieStructure.chartedSpace RealLieStructure.lieGroup

/-- For `ℝˣ`, the inclusion of the constructed Lie group into Mathlib's Lie group `ℝˣ` is
smooth. -/
theorem contMDiff_val :
    ContMDiff 𝓘(ℝ, realUnits.E) 𝓘(ℝ, ℝ) ∞ (fun g : (⊤ : Subgroup ℝˣ) => (g : ℝˣ)) :=
  TauCeti.Lie.contMDiff_of_continuous_monoidHom (⊤ : Subgroup ℝˣ).subtype continuous_subtypeVal

/-- For `ℝˣ`, the inverse map from Mathlib's Lie group `ℝˣ` to the constructed one is smooth. -/
theorem contMDiff_topEquiv_symm :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, realUnits.E) ∞ (Subgroup.topEquiv (G := ℝˣ)).symm :=
  TauCeti.Lie.contMDiff_of_continuous_monoidHom (Subgroup.topEquiv (G := ℝˣ)).symm
    (continuous_id.subtype_mk _)

/-- Hence a function on `ℝˣ` is smooth for Mathlib's structure iff it is smooth for the
constructed one. -/
theorem contMDiff_iff (f : ℝˣ → ℂ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ f ↔
      ContMDiff 𝓘(ℝ, realUnits.E) 𝓘(ℝ, ℂ) ∞ (fun g : (⊤ : Subgroup ℝˣ) => f g) :=
  ⟨fun h => h.comp contMDiff_val, fun h => h.comp contMDiff_topEquiv_symm⟩

section LeftRegular

open scoped Matrix.Norms.Operator

attribute [local instance] Matrix.linftyOpTopologicalSpace

/-- `RealLieGroup.contMDiff_leftRegular` for `ℝˣ` over `A = ℝ`: `g ↦ ρ(g) ∈ M₁(ℝ)` is smooth. -/
example :
    letI := RealLieGroup.chartedSpace (G := (⊤ : Subgroup ℝˣ)) (by simp)
    ContMDiff 𝓘(ℝ, RealLieGroup.model (⊤ : Subgroup ℝˣ))
      𝓘(ℝ, Matrix (Fin (RealLieGroup.dim ℝ)) (Fin (RealLieGroup.dim ℝ)) ℝ) ∞
      (fun g : (⊤ : Subgroup ℝˣ) => RealLieGroup.leftRegular ℝ (g : ℝˣ)) :=
  RealLieGroup.contMDiff_leftRegular (G := ⊤) (by simp)

end LeftRegular

end Units

end GSpinGGP.Sanity.RealLieGroupAudit
