/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalGroups
import GSpinGGP.Foundations.RealLieGroup
import GSpinGGP.Foundations.LieRepresentations
import TauCeti.Geometry.Lie.AutomaticSmoothness

/-!
# The real Lie structure of a closed subgroup over an archimedean local field

For a local field `F` with a real embedding `φ` (so `F = ℝ` or `ℂ`) and a closed subgroup `G` of
the units of a finite-dimensional `F`-algebra `A` with its module topology,
`RealEmbedding.realLieStructure φ G hG : RealLieStructure G` packages the Lie group structure of
`GSpinGGP/Foundations/RealLieGroup.lean` (closed-subgroup theorem in `GLₙ(ℝ)` through the left
regular representation of `A` as a real algebra through `φ`). Its charts are charts for the
topology `G` has as a subspace of `Aˣ`.

The structure involves choices (a basis of `A`, the slice charts of the closed-subgroup theorem).
For any two `RealLieStructure`s on the same topological group the identity is smooth in both
directions (Tau Ceti's automatic smoothness of continuous homomorphisms of Lie groups), so the test
functions and the smooth vectors of a unitary representation do not depend on the chosen structure
(`testFunctions_eq`, `smoothVectors_eq`), nor do the character (`isCharacterOf_iff`,
`characterOn_eq`, which see `L` only through the test functions) and the trace (which does not
involve `L`). For the seminorms, the continuous and equivariant forms, the multiplicity and
`HasModel` this is not yet proved: the spaces of smooth vectors are equal only propositionally, so
forms on them must be transported.

## Main results

* `RealEmbedding.realLieStructure φ G hG`: the real Lie structure on a closed subgroup `G ≤ Aˣ`.
* `RealLieStructure.contMDiff_id`: the identity is smooth from one Lie structure to another.
* `RealLieStructure.isCharacterOf_iff`, `RealLieStructure.characterOn_eq`: nor does the character.
* `RealLieStructure.testFunctions_eq`, `RealLieStructure.smoothVectors_eq`: `C_c^∞(G)` and `π^∞`
  do not depend on the Lie structure.
-/

open scoped ContDiff Manifold

namespace GSpinGGP

namespace RealEmbedding

variable {F : Type*} [NontriviallyNormedField F] [LocalField F] (φ : RealEmbedding F)
  {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A] [IsModuleTopology F A]

/-- The real Lie group structure on a closed subgroup `G` of `Aˣ`, for `F` with a real embedding
`φ`: `A` is a finite-dimensional real algebra through `φ`, and `G` gets the charts of
`RealLieGroup.chartedSpace`, modelled on `RealLieGroup.model G`. -/
noncomputable def realLieStructure (G : Subgroup Aˣ) (hG : IsClosed (G : Set Aˣ)) :
    RealLieStructure G :=
  letI := φ.algebraOf A
  haveI := φ.finiteDimensional_algebraOf A
  haveI := φ.continuousSMul_algebraOf A
  haveI := isTopologicalRing_of_moduleTopology F A
  haveI := t2Space_of_moduleTopology F A
  letI := RealLieGroup.chartedSpace hG
  haveI := RealLieGroup.lieGroup hG
  { E := RealLieGroup.model G }

end RealEmbedding

namespace RealLieStructure

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
  RealLieStructure.normedAddCommGroup RealLieStructure.normedSpace
  RealLieStructure.finiteDimensional RealLieStructure.chartedSpace RealLieStructure.lieGroup

variable {G : Type*} [Group G] [TopologicalSpace G] (L L' : RealLieStructure G)

/-- For two real Lie structures on the same topological group, the identity is smooth: it is a
continuous homomorphism of Lie groups (`TauCeti.Lie.contMDiff_of_continuous_monoidHom`). -/
theorem contMDiff_id : ContMDiff 𝓘(ℝ, L.E) 𝓘(ℝ, L'.E) ∞ (id : G → G) :=
  TauCeti.Lie.contMDiff_of_continuous_monoidHom (MonoidHom.id G) continuous_id

/-- The test functions `C_c^∞(G)` do not depend on the Lie structure. -/
theorem testFunctions_eq : LieRep.testFunctions L = LieRep.testFunctions L' := by
  have key : ∀ L L' : RealLieStructure G,
      LieRep.testFunctions L ≤ LieRep.testFunctions L' := by
    intro L L' f hf
    rw [LieRep.mem_testFunctions] at hf ⊢
    exact ⟨hf.1.comp (contMDiff_id L' L), hf.2⟩
  exact le_antisymm (key L L') (key L' L)

/-- The smooth vectors of a unitary representation do not depend on the Lie structure. -/
theorem smoothVectors_eq (π : UnitaryRep G) :
    LieRep.smoothVectors L π = LieRep.smoothVectors L' π := by
  have key : ∀ L L' : RealLieStructure G,
      LieRep.smoothVectors L π ≤ LieRep.smoothVectors L' π := by
    intro L L' v hv
    rw [LieRep.mem_smoothVectors_iff] at hv ⊢
    exact hv.comp (contMDiff_id L' L)
  exact le_antisymm (key L L') (key L' L)

section Characters

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Being the character of `π` does not depend on the Lie structure: it sees `L` only through
`C_c^∞(G)` (`testFunctions_eq`). -/
theorem isCharacterOf_iff (π : UnitaryRep G) (θ : G → ℂ) :
    LieRep.IsCharacterOf L π θ ↔ LieRep.IsCharacterOf L' π θ := by
  rw [LieRep.IsCharacterOf, LieRep.IsCharacterOf, testFunctions_eq L L']

/-- The character `θ_π` normalised on `S` does not depend on the Lie structure. -/
theorem characterOn_eq (π : UnitaryRep G) (S : Set G) :
    LieRep.characterOn L π S = LieRep.characterOn L' π S := by
  have h : LieRep.IsCharacterOf L π = LieRep.IsCharacterOf L' π :=
    funext fun θ => propext (isCharacterOf_iff L L' π θ)
  unfold LieRep.characterOn
  rw [h]

end Characters

end RealLieStructure

end GSpinGGP
