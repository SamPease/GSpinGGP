/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import TauCeti.LinearAlgebra.BilinearForm.Isometry

/-!
# Skew-adjoint and orthogonal endomorphisms: unfolding and extension of scalars

* `LinearMap.isSkewAdjoint_iff`: `B.IsSkewAdjoint f ↔ ∀ u v, B (f u) v = -B u (f v)`.
* `LinearMap.IsOrthogonal.isAdjointPair`, `LinearMap.IsOrthogonal.isAdjointPair_inv`,
  `LinearMap.IsSkewAdjoint.conj_units`: an orthogonal unit is adjoint to its inverse, and
  conjugation by it preserves skew-adjointness.
* `LinearMap.IsAdjointPair.baseChange`, `LinearMap.IsSkewAdjoint.baseChange`,
  `LinearMap.IsOrthogonal.baseChange`: these notions survive extension of scalars to any
  commutative algebra.
-/

namespace LinearMap

section Unfold

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {B : M →ₗ[R] M →ₗ[R] N} {f : Module.End R M}

/-- Skew-adjointness, unfolded: `B (f u) v = - B u (f v)`. -/
theorem isSkewAdjoint_iff : B.IsSkewAdjoint f ↔ ∀ u v, B (f u) v = -B u (f v) := by
  simp only [IsSkewAdjoint, IsAdjointPair, Pi.neg_apply, map_neg]

theorem IsSkewAdjoint.eq (h : B.IsSkewAdjoint f) (u v : M) : B (f u) v = -B u (f v) :=
  isSkewAdjoint_iff.1 h u v

end Unfold

section BaseChange

variable {R M M₁ : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁]
  {B : LinearMap.BilinForm R M} {B₁ : LinearMap.BilinForm R M₁}

/-- An adjoint pair stays an adjoint pair after extension of scalars. -/
theorem IsAdjointPair.baseChange (A : Type*) [CommRing A] [Algebra R A] {f : M →ₗ[R] M₁}
    {g : M₁ →ₗ[R] M} (h : IsAdjointPair B B₁ f g) :
    IsAdjointPair (B.baseChange A) (B₁.baseChange A) (f.baseChange A) (g.baseChange A) := by
  intro u v
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul b y => simp [LinearMap.BilinForm.baseChange_tmul, h x y]
    | add v w hv hw => simp only [map_add] at hv hw ⊢; rw [hv, hw]
  | add u w hu hw => simp only [map_add, LinearMap.add_apply] at hu hw ⊢; rw [hu, hw]

/-- A skew-adjoint endomorphism stays skew-adjoint after extension of scalars. -/
theorem IsSkewAdjoint.baseChange (A : Type*) [CommRing A] [Algebra R A] {f : M →ₗ[R] M}
    (h : B.IsSkewAdjoint f) : (B.baseChange A).IsSkewAdjoint (f.baseChange A) := by
  have := IsAdjointPair.baseChange A (f := f) (g := -f) h
  rw [LinearMap.baseChange_neg] at this
  exact this

/-- An orthogonal endomorphism stays orthogonal after extension of scalars. -/
theorem IsOrthogonal.baseChange (A : Type*) [CommRing A] [Algebra R A] {f : M →ₗ[R] M}
    (h : B.IsOrthogonal f) : (B.baseChange A).IsOrthogonal (f.baseChange A) :=
  TauCeti.BilinForm.IsIsometry.baseChange A h

end BaseChange


section Units

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : LinearMap.BilinForm R M}
  {u : (Module.End R M)ˣ}

/-- The inverse of an orthogonal unit is its adjoint: `B (u⁻¹ x) y = B x (u y)`. -/
theorem IsOrthogonal.isAdjointPair_inv (h : B.IsOrthogonal (u : Module.End R M)) :
    IsAdjointPair B B ((u⁻¹ : (Module.End R M)ˣ) : Module.End R M) (u : Module.End R M) :=
  fun x y => by
    rw [← h, ← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]

/-- An orthogonal unit is adjoint to its inverse: `B (u x) y = B x (u⁻¹ y)`. -/
theorem IsOrthogonal.isAdjointPair (h : B.IsOrthogonal (u : Module.End R M)) :
    IsAdjointPair B B (u : Module.End R M) ((u⁻¹ : (Module.End R M)ˣ) : Module.End R M) :=
  fun x y => by
    rw [← h x, ← Module.End.mul_apply (u : Module.End R M), Units.mul_inv, Module.End.one_apply]

/-- Conjugation by an orthogonal unit preserves skew-adjointness. -/
theorem IsSkewAdjoint.conj_units (h : B.IsOrthogonal (u : Module.End R M)) {f : Module.End R M}
    (hf : B.IsSkewAdjoint f) :
    B.IsSkewAdjoint (((u⁻¹ : (Module.End R M)ˣ) : Module.End R M) * f * (u : Module.End R M)) := by
  have := (h.isAdjointPair.comp hf).comp h.isAdjointPair_inv
  intro x y
  simpa using this x y

end Units

end LinearMap
