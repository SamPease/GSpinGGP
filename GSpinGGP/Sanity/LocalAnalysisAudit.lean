/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalAnalysis
import GSpinGGP.Sanity.LieRepresentationsAudit
import GSpinGGP.Sanity.RealEmbeddingAudit

/-!
# Sanity checks for the analytic notions by case on the field

The selectors of `GSpinGGP/Foundations/LocalAnalysis.lean` evaluated on the trivial
one-dimensional representation `1_G` of `G = Fˣ` (the subgroup `⊤ ≤ Fˣ`, with `A = F`):

* over `F = ℝ` and `F = ℂ`, through the whole archimedean chain: the classification gives the real
  embedding (`nonempty_realEmbedding_of_not_isUltrametricDist`, the default argument of the
  reduction lemmas), `realLieStructure` the Lie structure on `G`, and the selector is the `LieRep`
  notion there; the multiplicity of the trivial character is `1` (not the junk value `0`), of the
  sign character of `ℝˣ` it is `0`, and the constant `1` is the character of `1_G`;
* over a non-archimedean local field (for instance `ℚ_p`), the selector is the `p`-adic notion and
  the multiplicity of the trivial character is again `1`.
-/

namespace GSpinGGP.Sanity.LocalAnalysisAudit

open GSpinGGP GSpinGGP.LieRep.Audit GSpinGGP.Sanity.RealEmbeddingAudit

/-! ### `F = ℝ` -/

/-- The Lie structure of `ℝˣ` exists (it is not the junk value `none`). -/
example : (archLieStructure? ℝ (⊤ : Subgroup ℝˣ)).isSome :=
  (isSome_archLieStructure?_iff ℝ isClosed_univ).2 not_isUltrametricDist_real

example : localMultiplicity ℝ (trivialRep ↥(⊤ : Subgroup ℝˣ)) ⊤ (fun _ => 1) = 1 := by
  rw [localMultiplicity_of_not_isUltrametricDist not_isUltrametricDist_real isClosed_univ]
  exact multiplicity_trivialRep_one _ _

/-- The sign character of `ℝˣ`, on the subgroup `⊤` of `G = ⊤ ≤ ℝˣ`. -/
noncomputable def sign (s : ↥(⊤ : Subgroup ↥(⊤ : Subgroup ℝˣ))) : ℂ :=
  if 0 < (((s : ↥(⊤ : Subgroup ℝˣ)) : ℝˣ) : ℝ) then 1 else -1

example : localMultiplicity ℝ (trivialRep ↥(⊤ : Subgroup ℝˣ)) ⊤ sign = 0 := by
  rw [localMultiplicity_of_not_isUltrametricDist not_isUltrametricDist_real isClosed_univ]
  exact multiplicity_trivialRep_eq_zero (s := ⟨⟨-1, Subgroup.mem_top _⟩, Subgroup.mem_top _⟩) _
    (by norm_num [sign])

example : LocalHasModel ℝ (trivialRep ↥(⊤ : Subgroup ℝˣ)) ⊤ (fun _ => 1) := by
  rw [localHasModel_iff_localMultiplicity_ne_zero,
    localMultiplicity_of_not_isUltrametricDist not_isUltrametricDist_real isClosed_univ,
    multiplicity_trivialRep_one]
  exact one_ne_zero

section Character

/-- `ℝˣ` is locally compact (a closed subgroup of the units of a finite-dimensional algebra). -/
local instance : LocallyCompactSpace ↥(⊤ : Subgroup ℝˣ) :=
  subgroup_locallyCompactSpace_of_isClosed ℝ ℝ ⊤ isClosed_univ

theorem localIsCharacterOf_real_one :
    LocalIsCharacterOf ℝ (trivialRep ↥(⊤ : Subgroup ℝˣ)) (fun _ => 1) := by
  rw [localIsCharacterOf_of_not_isUltrametricDist not_isUltrametricDist_real isClosed_univ]
  exact isCharacterOf_trivialRep_one _

/-- The character of `1_G` exists, so `localCharacterOn` is a character of `1_G` continuous on `S`
(not the junk value of the epsilon pattern). -/
example (S : Set ↥(⊤ : Subgroup ℝˣ)) :
    LocalIsCharacterOf ℝ (trivialRep ↥(⊤ : Subgroup ℝˣ))
        (localCharacterOn ℝ (trivialRep ↥(⊤ : Subgroup ℝˣ)) S) ∧
      ContinuousOn (localCharacterOn ℝ (trivialRep ↥(⊤ : Subgroup ℝˣ)) S) S :=
  localCharacterOn_spec _ S ⟨fun _ => 1, localIsCharacterOf_real_one, continuousOn_const⟩

/-- The trace is the Hilbert-space trace of `π(f)` (no Lie structure involved). -/
example (f : ↥(⊤ : Subgroup ℝˣ) → ℂ) :
    localTraceOf ℝ (trivialRep ↥(⊤ : Subgroup ℝˣ)) f = LieRep.traceOf (trivialRep _) f :=
  localTraceOf_of_not_isUltrametricDist not_isUltrametricDist_real _ f

end Character

/-- The test functions are the smooth compactly supported functions for the Lie structure built
from the real embedding `ℝ → ℝ`. -/
example : localTestFunctions ℝ (⊤ : Subgroup ℝˣ) =
    LieRep.testFunctions (realId.realLieStructure ⊤ isClosed_univ) :=
  localTestFunctions_of_not_isUltrametricDist not_isUltrametricDist_real isClosed_univ realId

/-! ### `F = ℂ` -/

example : localMultiplicity ℂ (trivialRep ↥(⊤ : Subgroup ℂˣ)) ⊤ (fun _ => 1) = 1 := by
  rw [localMultiplicity_of_not_isUltrametricDist not_isUltrametricDist_complex isClosed_univ]
  exact multiplicity_trivialRep_one _ _

example : LocalHasModel ℂ (trivialRep ↥(⊤ : Subgroup ℂˣ)) ⊤ (fun _ => 1) := by
  rw [localHasModel_iff_localMultiplicity_ne_zero,
    localMultiplicity_of_not_isUltrametricDist not_isUltrametricDist_complex isClosed_univ,
    multiplicity_trivialRep_one]
  exact one_ne_zero

section CharacterC

/-- `ℂˣ` is locally compact. -/
local instance : LocallyCompactSpace ↥(⊤ : Subgroup ℂˣ) :=
  subgroup_locallyCompactSpace_of_isClosed ℂ ℂ ⊤ isClosed_univ

example : LocalIsCharacterOf ℂ (trivialRep ↥(⊤ : Subgroup ℂˣ)) (fun _ => 1) := by
  rw [localIsCharacterOf_of_not_isUltrametricDist not_isUltrametricDist_complex isClosed_univ]
  exact isCharacterOf_trivialRep_one _

end CharacterC

/-- With the real embedding given explicitly (the inclusion `ℝ → ℂ`) instead of by the
classification. -/
example : localMultiplicity ℂ (trivialRep ↥(⊤ : Subgroup ℂˣ)) ⊤ (fun _ => 1) =
    LieRep.multiplicity (complexOfReal.realLieStructure ⊤ isClosed_univ)
      (trivialRep ↥(⊤ : Subgroup ℂˣ)) ⊤ (fun _ => 1) :=
  localMultiplicity_of_not_isUltrametricDist not_isUltrametricDist_complex isClosed_univ _ _ _
    complexOfReal

/-! ### A non-archimedean local field -/

section NonArchimedean

variable {F : Type} [NontriviallyNormedField F] [LocalField F] [IsUltrametricDist F]

omit [LocalField F] in
/-- Every vector of `1_G` is smooth in the `p`-adic sense (fixed by the open subgroup `G`). -/
theorem smoothVectors_trivialRep_top :
    smoothVectors (trivialRep ↥(⊤ : Subgroup Fˣ)) = ⊤ :=
  eq_top_iff.2 fun _ _ => (mem_smoothVectors_iff _).2 ⟨⊤, isOpen_univ, fun _ _ => rfl⟩

omit [LocalField F] in
/-- For the trivial character, every linear form on `1_G^∞` is equivariant. -/
theorem equivariantForms_trivialRep_top :
    equivariantForms (trivialRep ↥(⊤ : Subgroup Fˣ)) ⊤ (fun _ => 1) = ⊤ :=
  eq_top_iff.2 fun ℓ _ s v => by rw [one_mul]; rfl

theorem localMultiplicity_trivialRep_top :
    localMultiplicity F (trivialRep ↥(⊤ : Subgroup Fˣ)) ⊤ (fun _ => 1) = 1 := by
  rw [localMultiplicity_of_isUltrametricDist]
  have e : ↥(smoothVectors (trivialRep ↥(⊤ : Subgroup Fˣ))) ≃ₗ[ℂ] ℂ :=
    LinearEquiv.ofTop _ smoothVectors_trivialRep_top
  have : Module.Finite ℂ ↥(smoothVectors (trivialRep ↥(⊤ : Subgroup Fˣ))) :=
    Module.Finite.equiv e.symm
  rw [multiplicity, equivariantForms_trivialRep_top, rank_top, Module.dual_rank_eq,
    Cardinal.lift_id, e.rank_eq, Module.rank_self, map_one]

example : LocalHasModel F (trivialRep ↥(⊤ : Subgroup Fˣ)) ⊤ (fun _ => 1) := by
  rw [localHasModel_iff_localMultiplicity_ne_zero, localMultiplicity_trivialRep_top]
  exact one_ne_zero

example : localTestFunctions F (⊤ : Subgroup Fˣ) = testFunctions ↥(⊤ : Subgroup Fˣ) :=
  localTestFunctions_of_isUltrametricDist

section Trace

/-- `Fˣ` is locally compact. -/
local instance : LocallyCompactSpace ↥(⊤ : Subgroup Fˣ) :=
  subgroup_locallyCompactSpace_of_isClosed F F ⊤ isClosed_univ

example (f : ↥(⊤ : Subgroup Fˣ) → ℂ) :
    localTraceOf F (trivialRep ↥(⊤ : Subgroup Fˣ)) f = traceOf (trivialRep _) f :=
  localTraceOf_of_isUltrametricDist _ f

end Trace

/-- There is no archimedean Lie structure in the non-archimedean case. -/
example : archLieStructure? F (⊤ : Subgroup Fˣ) = none := archLieStructure?_eq_none F ⊤

end NonArchimedean

example (p : ℕ) [Fact p.Prime] :
    localMultiplicity ℚ_[p] (trivialRep ↥(⊤ : Subgroup ℚ_[p]ˣ)) ⊤ (fun _ => 1) = 1 :=
  localMultiplicity_trivialRep_top

end GSpinGGP.Sanity.LocalAnalysisAudit
