/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import TauCeti.RingTheory.Adjoin.Unit

/-!
# The Cayley transform of a skew endomorphism

Let `B` be a bilinear form on a finite-dimensional space `V` over a field of characteristic `0`
and `X` a `B`-skew endomorphism.  For `μ ≠ 0` not an eigenvalue of `X`, the Cayley transform
`s = (μ + X)(μ − X)⁻¹` is a `B`-isometry lying in `K[X]`; it fixes exactly `ker X`, and has no
eigenvector with eigenvalue `−1`.

* `LinearMap.BilinForm.exists_cayley`: such an `s` exists (`K` is infinite, and `X` has finitely
  many eigenvalues).
-/

namespace GSpinGGP

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- **The Cayley transform of a skew endomorphism.**  For a `B`-skew endomorphism `X` of a
finite-dimensional space over a field of characteristic `0` there is a `B`-isometry `s ∈ K[X]`
(namely `(μ + X)(μ − X)⁻¹` for `μ ≠ 0` not an eigenvalue of `X`) with `s v = v ↔ X v = 0` and
`s v = −v → v = 0`. -/
theorem _root_.LinearMap.BilinForm.exists_cayley [CharZero K] [FiniteDimensional K V]
    {B : LinearMap.BilinForm K V} {X : Module.End K V} (hX : B.IsSkewAdjoint X) :
    ∃ s : Module.End K V, B.IsOrthogonal s ∧ s ∈ Algebra.adjoin K {X} ∧ Commute s X ∧
      (∀ v, s v = v ↔ X v = 0) ∧ ∀ v, s v = -v → v = 0 := by
  classical
  have hskew : ∀ a b, B (X a) b = -B a (X b) := fun a b => by
    have := hX a b
    rw [Pi.neg_apply, map_neg] at this
    exact this
  -- a parameter `μ ≠ 0` that is not an eigenvalue of `X`
  obtain ⟨μ, hμ0, hμ⟩ : ∃ μ : K, μ ≠ 0 ∧ ¬ X.HasEigenvalue μ := by
    have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
    obtain ⟨μ, hμ⟩ := ((Module.End.finite_hasEigenvalue X).union
      (Set.finite_singleton (0 : K))).infinite_compl.nonempty
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff,
      not_or] at hμ
    exact ⟨μ, hμ.2, hμ.1⟩
  set u : Module.End K V := algebraMap K (Module.End K V) μ - X with hu_def
  set p : Module.End K V := algebraMap K (Module.End K V) μ + X with hp_def
  have hu_apply : ∀ v, u v = μ • v - X v := fun v => by simp [hu_def]
  have hp_apply : ∀ v, p v = μ • v + X v := fun v => by simp [hp_def]
  have huinj : Function.Injective u := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    rw [hu_apply, sub_eq_zero] at hv
    by_contra hne
    exact hμ (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hv.symm, hne⟩)
  have hu : IsUnit u := (LinearMap.isUnit_iff_ker_eq_bot u).mpr (LinearMap.ker_eq_bot.mpr huinj)
  set U := hu.unit with hU
  set ui : Module.End K V := ((U⁻¹ : (Module.End K V)ˣ) : Module.End K V) with hui
  have huX : Commute u X := (Commute.sub_left (Algebra.commutes μ X) (Commute.refl X))
  have hpu : Commute p u := by
    rw [hp_def, hu_def]
    exact (Commute.add_left (Algebra.commute_algebraMap_left μ _) (Commute.sub_right
      (Commute.symm (Algebra.commute_algebraMap_left μ X)) (Commute.refl X)))
  have hpX : Commute p X := Commute.add_left (Algebra.commutes μ X) (Commute.refl X)
  have hUcoe : (U : Module.End K V) = u := rfl
  have huiX : Commute ui X := Commute.units_inv_left (hUcoe ▸ huX)
  have hpui : Commute p ui := (Commute.units_inv_left (hUcoe ▸ hpu.symm)).symm
  have hu_ui : ∀ v, u (ui v) = v := fun v => by
    rw [← Module.End.mul_apply, ← hUcoe, hui, Units.mul_inv, Module.End.one_apply]
  have hui_u : ∀ v, ui (u v) = v := fun v => by
    rw [← Module.End.mul_apply, ← hUcoe, hui, Units.inv_mul, Module.End.one_apply]
  set s : Module.End K V := p * ui with hs_def
  -- `u (s v) = p v`
  have hus : ∀ v, u (s v) = p v := fun v => by
    rw [hs_def, hpui.eq, Module.End.mul_apply, hu_ui]
  have hus' : ∀ v, s v = p (ui v) := fun v => rfl
  refine ⟨s, ?_, ?_, ?_, ?_, ?_⟩
  · -- `s` is an isometry: `B((μ + X)a, (μ + X)b) = B((μ − X)a, (μ − X)b)`
    intro a b
    rw [hus', hus', hp_apply, hp_apply]
    conv_rhs => rw [← hu_ui a, ← hu_ui b, hu_apply (ui a), hu_apply (ui b)]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [hskew (ui a) (ui b)]
    ring
  · -- `s ∈ K[X]`
    have hXm : X ∈ Algebra.adjoin K {X} := Algebra.subset_adjoin (Set.mem_singleton X)
    have hum : u ∈ Algebra.adjoin K {X} :=
      Subalgebra.sub_mem _ (Subalgebra.algebraMap_mem _ μ) hXm
    have hpm : p ∈ Algebra.adjoin K {X} :=
      Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ μ) hXm
    have huim : ui ∈ Algebra.adjoin K {X} := by
      have h := TauCeti.Units.coe_inv_mem_adjoin (K := K) U (IsIntegral.of_finite K _)
      rw [hUcoe] at h
      exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hum) h
    exact Subalgebra.mul_mem _ hpm huim
  · exact Commute.mul_left hpX huiX
  · intro v
    constructor
    · intro h
      have h1 := hus v
      rw [h, hu_apply, hp_apply] at h1
      have h2 : (2 : K) • X v = 0 :=
        calc (2 : K) • X v = (μ • v + X v) - (μ • v - X v) := by rw [two_smul]; abel
          _ = 0 := sub_eq_zero.mpr h1.symm
      exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
    · intro h
      have hpv : p v = u v := by rw [hp_apply, hu_apply, h, add_zero, sub_zero]
      rw [hus', ← Module.End.mul_apply, hpui.eq, Module.End.mul_apply, hpv, hui_u]
  · intro v h
    have h1 := hus v
    rw [h, map_neg, hu_apply, hp_apply] at h1
    have h2 : (2 * μ) • v = 0 :=
      calc (2 * μ) • v = (μ • v + X v) - -(μ • v - X v) := by rw [mul_smul, two_smul]; abel
        _ = 0 := sub_eq_zero.mpr h1.symm
    exact (smul_eq_zero.mp h2).resolve_left (mul_ne_zero two_ne_zero hμ0)

end GSpinGGP
