/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import TauCeti.Topology.Instances.Matrix

/-!
# Continuity of the coefficients of a characteristic polynomial

`continuous_charpoly_coeff_of_continuous`: for a family `N_x` of endomorphisms of a
finite-dimensional space `E` that embeds linearly into a finite-dimensional space `A` with its
module topology, if `x ↦ ι (N_x v)` is continuous for each `v`, then every coefficient of the
characteristic polynomial of `N_x` is continuous in `x` (Tau Ceti's
`Matrix.continuous_charpoly_coeff` and the matrix of `N_x` in a basis).  The matrix entries are
continuous by `continuous_repr_of_continuous`, shared with the determinant version
`continuous_det_restrict_of_continuous` (`Foundations/Determinant.lean`).
-/

namespace GSpinGGP

/-- **Continuous matrix entries**: if `E` embeds linearly into a finite-dimensional space `A` with
its module topology and `x ↦ ι (N_x v)` is continuous for each `v`, then every coordinate
`x ↦ b.repr (N_x v) i` in a basis `b` of `E` is continuous (a linear form on `A` restricting to
`b.coord i` through a left inverse of `ι`). -/
theorem continuous_repr_of_continuous {K : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] {X : Type*} [TopologicalSpace X] {E A : Type*} [AddCommGroup E]
    [Module K E] [AddCommGroup A] [Module K A] [TopologicalSpace A]
    [IsModuleTopology K A] (ι : E →ₗ[K] A) (hι : Function.Injective ι) (N : X → Module.End K E)
    (hN : ∀ v, Continuous fun x => ι (N x v)) {n : Type*} (b : Module.Basis n K E) (v : E)
    (i : n) : Continuous fun x => b.repr (N x v) i := by
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.mpr hι)
  have h : ∀ x, b.repr (N x v) i = (b.coord i ∘ₗ ψ) (ι (N x v)) := fun x => by
    rw [LinearMap.comp_apply, ← LinearMap.comp_apply ψ ι, hψ, LinearMap.id_apply]
    rfl
  simp_rw [h]
  exact (IsModuleTopology.continuous_of_linearMap (b.coord i ∘ₗ ψ)).comp (hN v)

/-- **The coefficients of `charpoly N_x` are continuous in `x`**, when `E` embeds linearly into a
finite-dimensional space `A` with its module topology and `x ↦ ι (N_x v)` is continuous for each
`v`. -/
theorem continuous_charpoly_coeff_of_continuous {K : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] {X : Type*} [TopologicalSpace X] {E A : Type*} [AddCommGroup E]
    [Module K E] [FiniteDimensional K E] [AddCommGroup A] [Module K A] [TopologicalSpace A]
    [IsModuleTopology K A] (ι : E →ₗ[K] A) (hι : Function.Injective ι) (N : X → Module.End K E)
    (hN : ∀ v, Continuous fun x => ι (N x v)) (k : ℕ) :
    Continuous fun x => (N x).charpoly.coeff k := by
  classical
  let b := Module.Free.chooseBasis K E
  simp_rw [← LinearMap.charpoly_toMatrix _ b]
  refine (Matrix.continuous_charpoly_coeff k).comp (continuous_matrix fun i j => ?_)
  simp only [LinearMap.toMatrix_apply]
  exact continuous_repr_of_continuous ι hι N hN b (b j) i

end GSpinGGP
