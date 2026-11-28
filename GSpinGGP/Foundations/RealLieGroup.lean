/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalGroups
import GSpinGGP.Foundations.RealEmbeddingClassification
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import TauCeti.Analysis.Matrix.Normed
import TauCeti.Geometry.Lie.Subgroup.Embedded
import TauCeti.Geometry.Lie.Subgroup.Units
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
algebra, and the charts are pulled back to `G` along the homeomorphism
(`Homeomorph.pullbackChartedSpace`).

No norm is put on `A`: the only norm used is the `L∞` operator norm on `Mₙ(ℝ)`, whose topology is
the entrywise one. The charts on `G` are charts for the topology `G` already has (the type
`ChartedSpace E ↥G` refers to that topology), so the content of the compatibility is that
`G → K` is a homeomorphism for Mathlib's topology on `Aˣ`, which is proved below.

For a local field `F` with a real embedding `φ` (so `F = ℝ` or `ℂ`), a finite-dimensional
`F`-algebra `A` with its module topology is such a real algebra through `φ`
(`RealEmbedding.algebraOf`), which applies the construction to the closed subgroups of `Aˣ`.

The structure depends on the choice of a basis of `A` and on the choice of slice charts made by
the closed-subgroup theorem. Any two Lie group structures on the same topological group have the
same smooth functions (a continuous homomorphism of Lie groups is smooth); this is not formalized
here.

## Main definitions

* `Homeomorph.pullback_lieGroup`: a homeomorphism `e : N ≃ₜ M` onto a Lie group that is a group
  homomorphism makes `N` a Lie group for the pulled-back charts.
* `GSpinGGP.RealLieGroup.unitsMatrix A`: the closed embedding of topological groups
  `Aˣ → GLₙ(ℝ)` given by the left regular representation.
* `GSpinGGP.RealLieGroup.model G hG`: the model space of the Lie group structure on a closed
  subgroup `G ≤ Aˣ` (the Lie algebra of its image in `GLₙ(ℝ)`), a finite-dimensional real normed
  space in `Type`.
* `GSpinGGP.RealLieGroup.chartedSpace G hG`, `GSpinGGP.RealLieGroup.lieGroup G hG`: the charts on
  `G` and the smoothness of its group operations.
* `GSpinGGP.RealEmbedding.algebraOf φ`: the real algebra structure on an `F`-algebra given by a
  real embedding `φ` of `F`; `RealEmbedding.finiteDimensional_algebraOf`,
  `RealEmbedding.continuousSMul_algebraOf` check the hypotheses of the construction.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12 (the
  closed-subgroup theorem).
-/

open scoped ContDiff Manifold Matrix.Norms.Operator

/-! ### Transport of a Lie group structure along a homeomorphic group isomorphism -/

section Pullback

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [Group M] [LieGroup I n M]
  {N : Type*} [TopologicalSpace N] [Group N]

/-- A homeomorphism `e : N ≃ₜ M` onto a Lie group which is a group homomorphism makes `N` a Lie
group for the charts pulled back along `e`: the group operations of `N` are those of `M` read
through the diffeomorphism `e`. -/
theorem Homeomorph.pullback_lieGroup (e : N ≃ₜ M) (he : ∀ x y, e (x * y) = e x * e y) :
    letI := e.pullbackChartedSpace (H := H)
    LieGroup I n N := by
  let := e.pullbackChartedSpace (H := H)
  have := e.pullback_isManifold I n
  let D := e.pullbackDiffeomorph I n
  let f : N ≃* M := MulEquiv.mk' e.toEquiv he
  have hmul : (fun p : N × N => p.1 * p.2) =
      D.symm ∘ (fun p : M × M => p.1 * p.2) ∘ Prod.map D D := by
    funext p
    change p.1 * p.2 = e.symm (e p.1 * e p.2)
    rw [← he, e.symm_apply_apply]
  have hinv : (fun x : N => x⁻¹) = D.symm ∘ (fun x : M => x⁻¹) ∘ D := by
    funext x
    change x⁻¹ = e.symm (e x)⁻¹
    have h : e x⁻¹ = (e x)⁻¹ := map_inv f x
    rw [← h, e.symm_apply_apply]
  exact
    { contMDiff_mul := by
        rw [hmul]
        exact D.symm.contMDiff.comp
          (contMDiff_mul I n |>.comp (D.contMDiff.prodMap D.contMDiff))
      contMDiff_inv := by
        rw [hinv]
        exact D.symm.contMDiff.comp ((contMDiff_inv I n).comp D.contMDiff) }

end Pullback

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

theorem isEmbedding_unitsMatrix : Topology.IsEmbedding (unitsMatrix A) :=
  (isClosedEmbedding_leftRegular A).isEmbedding.units_map (f := (leftRegular A).toMonoidHom)

/-- The image of `Aˣ` in `GLₙ(ℝ)` is closed: it consists of the invertible matrices `u` with `u`
and `u⁻¹` in the (closed) image of `A`, since `ρ(x) ρ(y) = 1` forces `x y = 1` by injectivity. -/
theorem isClosed_range_unitsMatrix : IsClosed (Set.range (unitsMatrix A)) := by
  have hR := (isClosedEmbedding_leftRegular A).isClosed_range
  have heq : Set.range (unitsMatrix A) =
      {u : (Matrix (Fin (dim A)) (Fin (dim A)) ℝ)ˣ |
          (u : Matrix _ _ ℝ) ∈ Set.range (leftRegular A)} ∩
        {u : (Matrix (Fin (dim A)) (Fin (dim A)) ℝ)ˣ |
          ((u⁻¹ : (Matrix _ _ ℝ)ˣ) : Matrix _ _ ℝ) ∈ Set.range (leftRegular A)} := by
    ext u
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨⟨v, rfl⟩, ⟨(v⁻¹ : Aˣ), by simp [unitsMatrix]⟩⟩
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      have hxy : x * y = 1 := leftRegular_injective A (by simp [map_mul, hx, hy])
      have hyx : y * x = 1 := leftRegular_injective A (by simp [map_mul, hx, hy])
      exact ⟨⟨x, y, hxy, hyx⟩, Units.ext hx⟩
  rw [heq]
  exact (hR.preimage Units.continuous_val).inter (hR.preimage Units.continuous_coe_inv)

theorem isClosedEmbedding_unitsMatrix : Topology.IsClosedEmbedding (unitsMatrix A) :=
  ⟨isEmbedding_unitsMatrix A, isClosed_range_unitsMatrix A⟩

variable {A} (G : Subgroup Aˣ)

/-- The image of `G` in `GLₙ(ℝ)`. -/
noncomputable abbrev image : Subgroup (Matrix (Fin (dim A)) (Fin (dim A)) ℝ)ˣ :=
  G.map (unitsMatrix A)

theorem isClosed_image {G : Subgroup Aˣ} (hG : IsClosed (G : Set Aˣ)) :
    IsClosed (image G : Set (Matrix (Fin (dim A)) (Fin (dim A)) ℝ)ˣ) := by
  rw [Subgroup.coe_map]
  exact (isClosedEmbedding_unitsMatrix A).isClosedMap _ hG

/-- `G` is homeomorphic to its image in `GLₙ(ℝ)`, by a group isomorphism. -/
noncomputable def homeomorphImage : G ≃ₜ image G where
  toEquiv := (G.equivMapOfInjective (unitsMatrix A) (unitsMatrix_injective A)).toEquiv
  continuous_toFun :=
    ((isEmbedding_unitsMatrix A).continuous.comp continuous_subtypeVal).subtype_mk _
  continuous_invFun := by
    have hemb : Topology.IsEmbedding (fun x : G => unitsMatrix A x) :=
      (isEmbedding_unitsMatrix A).comp Topology.IsEmbedding.subtypeVal
    refine hemb.continuous_iff.2 (continuous_subtypeVal.congr fun y => ?_)
    have := congrArg Subtype.val
      ((G.equivMapOfInjective (unitsMatrix A) (unitsMatrix_injective A)).apply_symm_apply y)
    rw [Subgroup.coe_equivMapOfInjective_apply] at this
    exact this.symm

theorem homeomorphImage_mul (x y : G) :
    homeomorphImage G (x * y) = homeomorphImage G x * homeomorphImage G y :=
  map_mul (G.equivMapOfInjective (unitsMatrix A) (unitsMatrix_injective A)) x y

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
  (homeomorphImage G).pullbackChartedSpace

/-- A closed subgroup `G ≤ Aˣ` is a real Lie group for `chartedSpace hG`. -/
theorem lieGroup :
    letI := chartedSpace hG
    LieGroup 𝓘(ℝ, model G) ∞ G :=
  letI := (imageData hG).chartedSpace
  haveI := (imageData hG).lieGroup
  (homeomorphImage G).pullback_lieGroup _ _ (homeomorphImage_mul G)

/-- For the Lie group structure on `G`, the left regular representation `g ↦ ρ(g) ∈ Mₙ(ℝ)` is
smooth. -/
theorem contMDiff_leftRegular :
    letI := chartedSpace hG
    ContMDiff 𝓘(ℝ, model G) 𝓘(ℝ, Matrix (Fin (dim A)) (Fin (dim A)) ℝ) ∞
      (fun g : G => leftRegular A (g : Aˣ)) := by
  let := (imageData hG).chartedSpace
  let := chartedSpace hG
  have hD := ((homeomorphImage G).pullbackDiffeomorph 𝓘(ℝ, model G) ∞).contMDiff
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

section LieGroup

variable {F : Type*} [NontriviallyNormedField F] [LocalField F] (φ : RealEmbedding F)
  {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A] [IsModuleTopology F A]

include φ in
/-- Over a local field `F` with a real embedding (that is, `F = ℝ` or `ℂ`), every closed subgroup
`G` of the units of a finite-dimensional `F`-algebra `A` with its module topology is a real Lie
group for the topology it has as a subspace of `Aˣ`: `RealLieGroup.lieGroup` for `A` as a real
algebra through `φ`. -/
theorem exists_lieGroup (G : Subgroup Aˣ) (hG : IsClosed (G : Set Aˣ)) :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E) (_ : FiniteDimensional ℝ E)
      (_ : ChartedSpace E G), LieGroup 𝓘(ℝ, E) ∞ G := by
  let := φ.algebraOf A
  have := φ.finiteDimensional_algebraOf A
  have := φ.continuousSMul_algebraOf A
  have := isTopologicalRing_of_moduleTopology F A
  have := t2Space_of_moduleTopology F A
  exact ⟨RealLieGroup.model G, inferInstance, inferInstance, inferInstance,
    RealLieGroup.chartedSpace hG, RealLieGroup.lieGroup hG⟩

end LieGroup

end RealEmbedding

end GSpinGGP
