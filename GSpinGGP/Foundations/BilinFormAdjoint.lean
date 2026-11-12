/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import TauCeti.LinearAlgebra.BilinearForm.BaseChange

/-!
# Skew-adjoint and orthogonal endomorphisms: unfolding and extension of scalars

* `LinearMap.isSkewAdjoint_iff`: `B.IsSkewAdjoint f ↔ ∀ u v, B (f u) v = -B u (f v)`.
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
    (h : B.IsOrthogonal f) : (B.baseChange A).IsOrthogonal (f.baseChange A) := by
  intro u v
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul b y => simp [LinearMap.BilinForm.baseChange_tmul, h x y]
    | add v w hv hw => simp only [map_add, LinearMap.add_apply] at hv hw ⊢; rw [hv, hw]
  | add u w hu hw => simp only [map_add, LinearMap.add_apply] at hu hw ⊢; rw [hu, hw]

end BaseChange

end LinearMap
