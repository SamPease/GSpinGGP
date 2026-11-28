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

The construction of `GSpinGGP/Foundations/RealLieGroup.lean` applies to concrete closed subgroups
over `ℝ` and `ℂ`. For `G = ℝˣ` (as the subgroup `⊤ ≤ ℝˣ`) it gives the same smooth structure as
Mathlib's Lie group of units of the normed algebra `ℝ`: the identity is smooth in both directions
(by Tau Ceti's automatic smoothness of continuous homomorphisms of Lie groups), so the two
structures have the same smooth functions.
-/

namespace GSpinGGP.Sanity.RealLieGroupAudit

open GSpinGGP GSpinGGP.Sanity.RealEmbeddingAudit
open scoped ContDiff Manifold

/-- `ℝˣ` is a real Lie group by the construction, over `F = A = ℝ`. -/
example : ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E)
    (_ : FiniteDimensional ℝ E) (_ : ChartedSpace E (⊤ : Subgroup ℝˣ)),
    LieGroup 𝓘(ℝ, E) ∞ (⊤ : Subgroup ℝˣ) :=
  realId.exists_lieGroup ⊤ isClosed_univ

/-- `ℂˣ` is a real Lie group by the construction, over `F = A = ℂ`. -/
example : ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E)
    (_ : FiniteDimensional ℝ E) (_ : ChartedSpace E (⊤ : Subgroup ℂˣ)),
    LieGroup 𝓘(ℝ, E) ∞ (⊤ : Subgroup ℂˣ) :=
  complexOfReal.exists_lieGroup ⊤ isClosed_univ

/-- The positive reals, a closed subgroup of `ℝˣ`. -/
example : ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E)
    (_ : FiniteDimensional ℝ E) (_ : ChartedSpace E (⊥ : Subgroup ℝˣ)),
    LieGroup 𝓘(ℝ, E) ∞ (⊥ : Subgroup ℝˣ) :=
  realId.exists_lieGroup ⊥ (by simp)

/-- The packaged structure for `ℝˣ` and for `ℂˣ`. -/
noncomputable example : RealLieStructure (⊤ : Subgroup ℝˣ) := realId.realLieStructure ⊤ (by simp)

noncomputable example : RealLieStructure (⊤ : Subgroup ℂˣ) :=
  complexOfReal.realLieStructure ⊤ (by simp)

section Units

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

noncomputable local instance :
    ChartedSpace (RealLieGroup.model (⊤ : Subgroup ℝˣ)) (⊤ : Subgroup ℝˣ) :=
  RealLieGroup.chartedSpace (G := ⊤) (by simp)

local instance :
    LieGroup 𝓘(ℝ, RealLieGroup.model (⊤ : Subgroup ℝˣ)) ∞ (⊤ : Subgroup ℝˣ) :=
  RealLieGroup.lieGroup (G := ⊤) (by simp)

/-- For `ℝˣ`, the inclusion of the constructed Lie group into Mathlib's Lie group `ℝˣ` is
smooth. -/
theorem contMDiff_val :
    ContMDiff 𝓘(ℝ, RealLieGroup.model (⊤ : Subgroup ℝˣ)) 𝓘(ℝ, ℝ) ∞
      (fun g : (⊤ : Subgroup ℝˣ) => (g : ℝˣ)) :=
  TauCeti.Lie.contMDiff_of_continuous_monoidHom (⊤ : Subgroup ℝˣ).subtype continuous_subtypeVal

/-- For `ℝˣ`, the inverse map from Mathlib's Lie group `ℝˣ` to the constructed one is smooth. -/
theorem contMDiff_topEquiv_symm :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, RealLieGroup.model (⊤ : Subgroup ℝˣ)) ∞
      (Subgroup.topEquiv (G := ℝˣ)).symm :=
  TauCeti.Lie.contMDiff_of_continuous_monoidHom (Subgroup.topEquiv (G := ℝˣ)).symm
    (continuous_id.subtype_mk _)

/-- Hence a function on `ℝˣ` is smooth for Mathlib's structure iff it is smooth for the
constructed one. -/
theorem contMDiff_iff (f : ℝˣ → ℂ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ f ↔
      ContMDiff 𝓘(ℝ, RealLieGroup.model (⊤ : Subgroup ℝˣ)) 𝓘(ℝ, ℂ) ∞
        (fun g : (⊤ : Subgroup ℝˣ) => f g) :=
  ⟨fun h => h.comp contMDiff_val, fun h => h.comp contMDiff_topEquiv_symm⟩

end Units

end GSpinGGP.Sanity.RealLieGroupAudit
