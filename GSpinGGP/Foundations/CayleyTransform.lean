/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import TauCeti.RingTheory.Adjoin.Unit
import GSpinGGP.Foundations.BilinFormAdjoint

/-!
# The Cayley transform of a skew endomorphism

Let `B` be a bilinear form on a finite-dimensional space `V` over a field in which `2` is
invertible, and `X` a `B`-skew endomorphism.  For `μ ≠ 0` with `μ − X` invertible, the Cayley
transform `s = (μ + X)(μ − X)⁻¹` is a `B`-isometry lying in `K[X]`; it fixes exactly `ker X`, and
has no eigenvector with eigenvalue `−1`.

* `LinearMap.BilinForm.cayley_spec`: these properties, for a given `μ`.
* `LinearMap.BilinForm.exists_cayley`: over an infinite field such a `μ` exists (`X` has finitely
  many eigenvalues).
-/

namespace GSpinGGP

open Module

variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]

/-- **The Cayley transform of a skew endomorphism.**  For a `B`-skew endomorphism `X`, `μ ≠ 0` with
`μ − X` invertible, and `s = (μ + X)(μ − X)⁻¹`: `s` is a `B`-isometry in `K[X]`,
`s v = v ↔ X v = 0`, and `s v = −v → v = 0`. -/
theorem _root_.LinearMap.BilinForm.cayley_spec [FiniteDimensional K V]
    {B : LinearMap.BilinForm K V} {X : Module.End K V} (hX : B.IsSkewAdjoint X) {μ : K}
    (hμ0 : μ ≠ 0) (hu : IsUnit (algebraMap K (Module.End K V) μ - X)) :
    B.IsOrthogonal ((algebraMap K (Module.End K V) μ + X) *
        Ring.inverse (algebraMap K (Module.End K V) μ - X)) ∧
      (algebraMap K (Module.End K V) μ + X) *
          Ring.inverse (algebraMap K (Module.End K V) μ - X) ∈ Algebra.adjoin K {X} ∧
      (∀ v, ((algebraMap K (Module.End K V) μ + X) *
          Ring.inverse (algebraMap K (Module.End K V) μ - X)) v = v ↔ X v = 0) ∧
      ∀ v, ((algebraMap K (Module.End K V) μ + X) *
          Ring.inverse (algebraMap K (Module.End K V) μ - X)) v = -v → v = 0 := by
  have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  set u : Module.End K V := algebraMap K (Module.End K V) μ - X with hu_def
  set p : Module.End K V := algebraMap K (Module.End K V) μ + X with hp_def
  set ui : Module.End K V := Ring.inverse u with hui
  have hu_apply : ∀ v, u v = μ • v - X v := fun v => by simp [hu_def]
  have hp_apply : ∀ v, p v = μ • v + X v := fun v => by simp [hp_def]
  have huX : Commute u X := Commute.sub_left (Algebra.commutes μ X) (Commute.refl X)
  have hpu : Commute p u :=
    Commute.add_left (Algebra.commute_algebraMap_left μ _)
      (Commute.sub_right (Algebra.commute_algebraMap_left μ X).symm (Commute.refl X))
  have hU : (hu.unit : Module.End K V) = u := rfl
  have hui' : ui = ((hu.unit⁻¹ : (Module.End K V)ˣ) : Module.End K V) :=
    Ring.inverse_unit hu.unit
  have hpui : Commute p ui := by
    rw [hui']
    exact (Commute.units_inv_left (u := hu.unit) hpu.symm).symm
  have hu_ui : ∀ v, u (ui v) = v := fun v => by
    rw [← Module.End.mul_apply, hui, Ring.mul_inverse_cancel u hu, Module.End.one_apply]
  have hui_u : ∀ v, ui (u v) = v := fun v => by
    rw [← Module.End.mul_apply, hui, Ring.inverse_mul_cancel u hu, Module.End.one_apply]
  -- `u (s v) = p v`
  have hus : ∀ v, u ((p * ui) v) = p v := fun v => by
    rw [hpui.eq, Module.End.mul_apply, hu_ui]
  refine ⟨?_, ?_, fun v => ⟨fun h => ?_, fun h => ?_⟩, fun v h => ?_⟩
  · -- `B((μ + X)a, (μ + X)b) = B((μ − X)a, (μ − X)b)`
    intro a b
    rw [Module.End.mul_apply, Module.End.mul_apply, hp_apply, hp_apply]
    conv_rhs => rw [← hu_ui a, ← hu_ui b, hu_apply (ui a), hu_apply (ui b)]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [hX.eq (ui a) (ui b)]
    ring
  · have hXm : X ∈ Algebra.adjoin K {X} := Algebra.subset_adjoin (Set.mem_singleton X)
    have hum : u ∈ Algebra.adjoin K {X} :=
      Subalgebra.sub_mem _ (Subalgebra.algebraMap_mem _ μ) hXm
    have hpm : p ∈ Algebra.adjoin K {X} :=
      Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ μ) hXm
    have huim : ui ∈ Algebra.adjoin K {X} := by
      have h := TauCeti.Units.coe_inv_mem_adjoin (K := K) hu.unit (IsIntegral.of_finite K _)
      rw [hU, ← hui'] at h
      exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hum) h
    exact Subalgebra.mul_mem _ hpm huim
  · have h1 := hus v
    rw [h, hu_apply, hp_apply] at h1
    have h3 : (2 : K) • X v = 0 :=
      calc (2 : K) • X v = (μ • v + X v) - (μ • v - X v) := by rw [two_smul]; abel
        _ = 0 := sub_eq_zero.mpr h1.symm
    exact (smul_eq_zero.mp h3).resolve_left h2
  · have hpv : p v = u v := by rw [hp_apply, hu_apply, h, add_zero, sub_zero]
    rw [hpui.eq, Module.End.mul_apply, hpv, hui_u]
  · have h1 := hus v
    rw [h, map_neg, hu_apply, hp_apply] at h1
    have h3 : (2 * μ) • v = 0 :=
      calc (2 * μ) • v = (μ • v + X v) - -(μ • v - X v) := by rw [mul_smul, two_smul]; abel
        _ = 0 := sub_eq_zero.mpr h1.symm
    exact (smul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 hμ0)

/-- **A Cayley transform exists** over an infinite field: for a `B`-skew endomorphism `X` there is
a `B`-isometry `s ∈ K[X]` with `s v = v ↔ X v = 0` and `s v = −v → v = 0` (`cayley_spec`, for
`μ ≠ 0` outside the finite set of eigenvalues of `X`). -/
theorem _root_.LinearMap.BilinForm.exists_cayley [Infinite K] [FiniteDimensional K V]
    {B : LinearMap.BilinForm K V} {X : Module.End K V} (hX : B.IsSkewAdjoint X) :
    ∃ s : Module.End K V, B.IsOrthogonal s ∧ s ∈ Algebra.adjoin K {X} ∧
      (∀ v, s v = v ↔ X v = 0) ∧ ∀ v, s v = -v → v = 0 := by
  obtain ⟨μ, hμ⟩ := ((Module.End.finite_hasEigenvalue X).union
    (Set.finite_singleton (0 : K))).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    not_or] at hμ
  have hu : IsUnit (algebraMap K (Module.End K V) μ - X) :=
    spectrum.notMem_iff.mp fun h => hμ.1 (Module.End.hasEigenvalue_iff_mem_spectrum.mpr h)
  exact ⟨_, LinearMap.BilinForm.cayley_spec hX hμ.2 hu⟩

end GSpinGGP
