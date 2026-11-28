/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.RealEmbeddingClassification
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Topology.Algebra.Group.Units
import TauCeti.Analysis.Matrix.Normed
import TauCeti.Geometry.Lie.Subgroup.Embedded
import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.PullbackGroupoid

/-!
# Closed subgroups of the units of a finite-dimensional real algebra are Lie groups

Let `A` be a finite-dimensional real algebra with a Hausdorff topology for which it is a
topological vector space over `ℝ`, and let `G ≤ Aˣ` be a closed subgroup, where `Aˣ` carries
Mathlib's topology on units (induced by `u ↦ (u, u⁻¹)`). Then `G`, with its subspace topology, is
a real Lie group. The construction: the left regular representation `ρ : A → Mₙ(ℝ)`,
`x ↦ (y ↦ x y)` in a basis of `A`, is an injective algebra map, hence a closed embedding; it
induces a closed embedding of topological groups `Aˣ → GLₙ(ℝ)`, so `G` is homeomorphic, as a
group, to a closed subgroup `K` of `GLₙ(ℝ)`. Cartan's closed-subgroup theorem (Tau Ceti's
`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`) makes `K` a Lie group modelled on its Lie
algebra, and the charts are pulled back to `G` along the isomorphism of topological groups
(`Homeomorph.pullbackChartedSpace`, `ContinuousMulEquiv.lieGroup_pullbackChartedSpace`).

No norm is put on `A`: the only norm used is the `L∞` operator norm on `Mₙ(ℝ)`, whose topology is
the entrywise one. The charts on `G` are charts for the topology `G` already has (the type
`ChartedSpace E ↥G` refers to that topology), so the content of the compatibility is that
`G → K` is a homeomorphism for Mathlib's topology on `Aˣ`, which is proved below.

For a local field `F` with a real embedding `φ` (so `F = ℝ` or `ℂ`), a finite-dimensional
`F`-algebra `A` with its module topology is such a real algebra through `φ`
(`RealEmbedding.algebraOf`); `RealEmbedding.realLieStructure` applies the construction to the
closed subgroups of `Aˣ`.

The structure depends on the choice of a basis of `A` and on the choice of slice charts made by
the closed-subgroup theorem. For any two real Lie structures on the same topological group the
identity is smooth (`RealLieStructure.contMDiff_id`), so the test functions and the smooth vectors
do not depend on these choices (`RealLieStructure.testFunctions_eq`,
`RealLieStructure.smoothVectors_eq`, in `GSpinGGP/Foundations/RealLieStructureOfClosed.lean`).

## Main definitions

* `GSpinGGP.RealLieGroup.unitsMatrix A`: the closed embedding of topological groups
  `Aˣ → GLₙ(ℝ)` given by the left regular representation.
* `GSpinGGP.RealLieGroup.model G`: the model space of the Lie group structure on a closed
  subgroup `G ≤ Aˣ` (the Lie algebra of its image in `GLₙ(ℝ)`), a finite-dimensional real normed
  space in `Type`.
* `GSpinGGP.RealLieGroup.chartedSpace hG`, `GSpinGGP.RealLieGroup.lieGroup hG`: the charts on
  `G` and the smoothness of its group operations.
* `GSpinGGP.RealEmbedding.algebraOf φ`: the real algebra structure on an `F`-algebra given by a
  real embedding `φ` of `F`; `RealEmbedding.finiteDimensional_algebraOf`,
  `RealEmbedding.continuousSMul_algebraOf` check the hypotheses of the construction.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12 (the
  closed-subgroup theorem).
-/

open scoped ContDiff Manifold Matrix.Norms.Operator

namespace GSpinGGP

namespace RealLieGroup

-- The topology on matrices underlying the `L∞` operator norm (equal to the entrywise one), so
-- that `GLₙ(ℝ)` is Mathlib's Lie group of units of a complete normed algebra.
attribute [local instance] Matrix.linftyOpTopologicalSpace

variable (A : Type*) [Ring A] [Algebra ℝ A] [FiniteDimensional ℝ A]

/-- The dimension of `A` over `ℝ`, the size of the matrices of the left regular
representation. -/
noncomputable abbrev dim : ℕ := Module.finrank ℝ A

/-- The left regular representation `A → Mₙ(ℝ)`, `x ↦` the matrix of `y ↦ x y` in the basis
`Module.finBasis ℝ A`. -/
noncomputable abbrev leftRegular : A →ₐ[ℝ] Matrix (Fin (dim A)) (Fin (dim A)) ℝ :=
  Algebra.leftMulMatrix (Module.finBasis ℝ A)

theorem leftRegular_injective : Function.Injective (leftRegular A) :=
  Algebra.leftMulMatrix_injective _

/-- The embedding `Aˣ → GLₙ(ℝ)` induced by the left regular representation. -/
noncomputable def unitsMatrix : Aˣ →* (Matrix (Fin (dim A)) (Fin (dim A)) ℝ)ˣ :=
  Units.map (leftRegular A).toMonoidHom

@[simp] theorem val_unitsMatrix (u : Aˣ) : (unitsMatrix A u : Matrix _ _ ℝ) = leftRegular A u :=
  rfl

theorem unitsMatrix_injective : Function.Injective (unitsMatrix A) := fun _ _ h =>
  Units.ext (leftRegular_injective A (congrArg Units.val h))

variable [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A] [T2Space A]

/-- The left regular representation is a closed embedding (an injective linear map out of a
finite-dimensional Hausdorff topological vector space). -/
theorem isClosedEmbedding_leftRegular : Topology.IsClosedEmbedding (leftRegular A) :=
  LinearMap.isClosedEmbedding_of_injective (f := (leftRegular A).toLinearMap)
    (LinearMap.ker_eq_bot.2 (leftRegular_injective A))

/-- `Aˣ → GLₙ(ℝ)` is a closed embedding of topological groups (Mathlib's
`Topology.IsClosedEmbedding.units_map` applied to the left regular representation). -/
theorem isClosedEmbedding_unitsMatrix : Topology.IsClosedEmbedding (unitsMatrix A) := by
  have h := isClosedEmbedding_leftRegular A
  have : ContinuousMul A := h.isInducing.continuousMul (leftRegular A)
  exact Topology.IsClosedEmbedding.units_map (f := (leftRegular A).toMonoidHom) h

theorem isEmbedding_unitsMatrix : Topology.IsEmbedding (unitsMatrix A) :=
  (isClosedEmbedding_unitsMatrix A).isEmbedding

variable {A} (G : Subgroup Aˣ)

/-- The image of `G` in `GLₙ(ℝ)`. -/
noncomputable abbrev image : Subgroup (Matrix (Fin (dim A)) (Fin (dim A)) ℝ)ˣ :=
  G.map (unitsMatrix A)

theorem isClosed_image {G : Subgroup Aˣ} (hG : IsClosed (G : Set Aˣ)) :
    IsClosed (image G : Set (Matrix (Fin (dim A)) (Fin (dim A)) ℝ)ˣ) := by
  rw [Subgroup.coe_map]
  exact (isClosedEmbedding_unitsMatrix A).isClosedMap _ hG

/-- `G` is isomorphic, as a topological group, to its image in `GLₙ(ℝ)`. -/
noncomputable def homeomorphImage : G ≃ₜ* image G :=
  let e := G.equivMapOfInjective (unitsMatrix A) (unitsMatrix_injective A)
  ContinuousMulEquiv.mk' (e.toEquiv.toHomeomorphOfIsInducing
    (Topology.IsInducing.subtypeVal.of_comp_iff.1
      ((isEmbedding_unitsMatrix A).comp Topology.IsEmbedding.subtypeVal).isInducing)) e.map_mul

/-- The model space of the Lie group structure on a closed subgroup `G ≤ Aˣ`: the Lie algebra of
its image in `GLₙ(ℝ)`, a finite-dimensional real normed space. -/
noncomputable def model : Type :=
  (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, Matrix (Fin (dim A)) (Fin (dim A)) ℝ)) (image G)).toSubmodule

noncomputable instance : NormedAddCommGroup (model G) :=
  inferInstanceAs (NormedAddCommGroup (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, Matrix (Fin (dim A)) (Fin (dim A)) ℝ)) (image G)).toSubmodule)

noncomputable instance : NormedSpace ℝ (model G) :=
  inferInstanceAs (NormedSpace ℝ (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, Matrix (Fin (dim A)) (Fin (dim A)) ℝ)) (image G)).toSubmodule)

instance : FiniteDimensional ℝ (model G) :=
  inferInstanceAs (FiniteDimensional ℝ (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, Matrix (Fin (dim A)) (Fin (dim A)) ℝ)) (image G)).toSubmodule)

variable {G} (hG : IsClosed (G : Set Aˣ))

/-- The Lie group structure on the image of `G` in `GLₙ(ℝ)` given by Cartan's closed-subgroup
theorem, modelled on the Lie algebra of the image. -/
noncomputable def imageData :
    TauCeti.Lie.EmbeddedLieSubgroupData 𝓘(ℝ, Matrix (Fin (dim A)) (Fin (dim A)) ℝ) (image G)
      (model G) :=
  TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed (isClosed_image hG)

/-- The charts of the Lie group structure on a closed subgroup `G ≤ Aˣ`, for the topology `G`
has as a subspace of `Aˣ`: those of its image in `GLₙ(ℝ)` given by the closed-subgroup theorem,
pulled back along `homeomorphImage G`. -/
@[instance_reducible]
noncomputable def chartedSpace : ChartedSpace (model G) G :=
  letI := (imageData hG).chartedSpace
  (homeomorphImage G).toHomeomorph.pullbackChartedSpace

/-- A closed subgroup `G ≤ Aˣ` is a real Lie group for `chartedSpace hG`. -/
theorem lieGroup :
    letI := chartedSpace hG
    LieGroup 𝓘(ℝ, model G) ∞ G :=
  letI := (imageData hG).chartedSpace
  haveI := (imageData hG).lieGroup
  (homeomorphImage G).lieGroup_pullbackChartedSpace

/-- For the Lie group structure on `G`, the left regular representation `g ↦ ρ(g) ∈ Mₙ(ℝ)` is
smooth. (API for later use, e.g. smoothness of matrix coefficients; exercised in
`GSpinGGP/Sanity/RealLieGroupAudit.lean`.) -/
theorem contMDiff_leftRegular :
    letI := chartedSpace hG
    ContMDiff 𝓘(ℝ, model G) 𝓘(ℝ, Matrix (Fin (dim A)) (Fin (dim A)) ℝ) ∞
      (fun g : G => leftRegular A (g : Aˣ)) := by
  let := (imageData hG).chartedSpace
  let := chartedSpace hG
  have hD := ((homeomorphImage G).toHomeomorph.pullbackDiffeomorph 𝓘(ℝ, model G) ∞).contMDiff
  have h := (Units.contMDiff_val (𝕜 := ℝ)).comp ((imageData hG).contMDiff_subtypeVal.comp hD)
  exact h

end RealLieGroup

/-! ### Algebras over an archimedean local field as real algebras -/

namespace RealEmbedding

section Algebra

variable {F : Type*} [Field F] [TopologicalSpace F] (φ : RealEmbedding F)
  (A : Type*) [Ring A] [Algebra F A]

/-- The real algebra structure on an `F`-algebra `A` given by a real embedding `φ` of `F`:
`r • x = φ r • x`. Not an instance. -/
abbrev algebraOf : Algebra ℝ A := Algebra.compHom A φ.toRingHom

theorem algebraOf_smul_def (r : ℝ) (x : A) :
    letI := φ.algebraOf A
    r • x = φ r • x :=
  rfl

/-- Through `φ`, the real structure of `A` is the restriction of its `F`-structure. -/
theorem isScalarTower_algebraOf :
    letI := φ.toAlgebra
    letI := φ.algebraOf A
    IsScalarTower ℝ F A :=
  letI := φ.toAlgebra
  letI := φ.algebraOf A
  ⟨fun r x a => by
    change (φ r * x) • a = φ r • x • a
    rw [mul_smul]⟩

/-- A finite-dimensional algebra over a locally compact Hausdorff topological field `F` with a
real embedding `φ` is finite-dimensional over `ℝ` through `φ` (`F` is finite-dimensional over `ℝ`,
`RealEmbedding.finiteDimensional`). -/
theorem finiteDimensional_algebraOf [IsTopologicalRing F] [T2Space F] [LocallyCompactSpace F]
    [Module.Finite F A] :
    letI := φ.algebraOf A
    FiniteDimensional ℝ A :=
  letI := φ.toAlgebra
  letI := φ.algebraOf A
  haveI := φ.finiteDimensional
  haveI := φ.isScalarTower_algebraOf A
  Module.Finite.trans F A

/-- Real scalar multiplication through `φ` is continuous on a topological `F`-module. -/
theorem continuousSMul_algebraOf [TopologicalSpace A] [ContinuousSMul F A] :
    letI := φ.algebraOf A
    ContinuousSMul ℝ A :=
  letI := φ.algebraOf A
  ⟨(continuous_smul (M := F) (X := A)).comp (φ.continuous.prodMap continuous_id)⟩

end Algebra

end RealEmbedding

end GSpinGGP
