/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Determinants of families of endomorphisms

* `continuous_det_of_continuous_repr`, `continuous_det_restrict_of_continuous`: continuity of
  `x ↦ det (f x)` and `x ↦ det (f x|_C)`;
* `trailingCoeff_charpoly_of_isCompl`: for `E = ker f ⊕ C` with `C` stable, the trailing
  coefficient of the characteristic polynomial of `f` is `± det (f|_C)`, and `det (f|_C) ≠ 0`;
* `disjoint_ker_range_of_isSemisimple`, `isCompl_ker_range_of_isSemisimple`: `E = ker f ⊕ im f` for
  semisimple `f`.
-/

open Filter Topology

namespace GSpinGGP

/-- The determinant of a family of endomorphisms whose matrix coefficients in a basis are
continuous is continuous. -/
theorem continuous_det_of_continuous_repr {K : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] {X : Type*} [TopologicalSpace X] {U : Type*} [AddCommGroup U]
    [Module K U] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K U)
    (f : X → U →ₗ[K] U) (hf : ∀ v i, Continuous fun x => b.repr (f x v) i) :
    Continuous fun x => LinearMap.det (f x) := by
  simp_rw [← LinearMap.det_toMatrix b]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  simp only [LinearMap.toMatrix_apply]
  exact hf (b j) i

/-- If `E = L ⊕ C` with `L = ker f` and `C` stable under `f`, then `f|_C` is invertible and the
trailing coefficient of the characteristic polynomial of `f` is `± det (f|_C)`. -/
theorem trailingCoeff_charpoly_of_isCompl {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] {f : Module.End K E} {L C : Submodule K E} (hcompl : IsCompl L C)
    (hker : LinearMap.ker f = L) (hC : ∀ x ∈ C, f x ∈ C) :
    LinearMap.det (f.restrict hC) ≠ 0 ∧ (LinearMap.charpoly f).trailingCoeff =
      (-1) ^ Module.finrank K C * LinearMap.det (f.restrict hC) := by
  have hL : ∀ x ∈ L, f x ∈ L := fun x hx => by
    rw [← hker, LinearMap.mem_ker] at hx ⊢
    rw [hx, map_zero]
  have hdet0 : LinearMap.det (f.restrict hC) ≠ 0 := by
    rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, eq_bot_iff]
    intro Y hY
    rw [LinearMap.mem_ker] at hY
    have hY' : (Y : E) ∈ L := by
      rw [← hker, LinearMap.mem_ker]
      have := congrArg Subtype.val hY
      simpa using this
    have : (Y : E) ∈ L ⊓ C := ⟨hY', Y.2⟩
    rw [hcompl.disjoint.eq_bot, Submodule.mem_bot] at this
    exact (Submodule.mem_bot K).mpr (Subtype.ext this)
  refine ⟨hdet0, ?_⟩
  obtain ⟨e, he⟩ : ∃ e : (L × C) ≃ₗ[K] E, ∀ q : L × C, e q = (q.1 : E) + (q.2 : E) :=
    ⟨Submodule.prodEquivOfIsCompl L C hcompl, Submodule.coe_prodEquivOfIsCompl' L C hcompl⟩
  have hφ : e.symm.conj f = (f.restrict hL).prodMap (f.restrict hC) := by
    refine LinearMap.ext fun q => e.injective ?_
    show e (e.symm (f (e q))) = _
    rw [LinearEquiv.apply_symm_apply, he, he, map_add]
    simp [LinearMap.coe_restrict_apply]
  have hzL : f.restrict hL = 0 := by
    refine LinearMap.ext fun X => Subtype.ext ?_
    have hX : (X : E) ∈ LinearMap.ker f := hker ▸ X.2
    rw [LinearMap.mem_ker] at hX
    simpa [LinearMap.coe_restrict_apply] using hX
  have hc0 : (LinearMap.charpoly (f.restrict hC)).coeff 0 ≠ 0 := by
    intro h
    have := LinearMap.det_eq_sign_charpoly_coeff (f.restrict hC)
    rw [h, mul_zero] at this
    exact hdet0 this
  have htc := Polynomial.trailingCoeff_eq_coeff_zero hc0
  have hXr : ((Polynomial.X : Polynomial K) ^ Module.finrank K L).trailingCoeff = 1 := by
    rw [Polynomial.trailingCoeff, Polynomial.natTrailingDegree_X_pow, Polynomial.coeff_X_pow_self]
  rw [← LinearEquiv.charpoly_conj e.symm f, hφ, LinearMap.charpoly_prodMap, hzL,
    LinearMap.charpoly_zero, Polynomial.trailingCoeff_mul, hXr, one_mul, htc,
    LinearMap.det_eq_sign_charpoly_coeff, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
    one_pow, one_mul]

/-- Continuity of `x ↦ det (N_x|_C)` for a family `N_x` of endomorphisms of `E` stabilizing `C`,
when `E` embeds linearly into a finite-dimensional space `A` with its module topology and
`x ↦ ι (N_x v)` is continuous for each `v`. -/
theorem continuous_det_restrict_of_continuous {K : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] {X : Type*} [TopologicalSpace X] {E A : Type*} [AddCommGroup E]
    [Module K E] [FiniteDimensional K E] [AddCommGroup A] [Module K A] [TopologicalSpace A]
    [IsModuleTopology K A] (ι : E →ₗ[K] A) (hι : Function.Injective ι) (N : X → Module.End K E)
    (hN : ∀ v, Continuous fun x => ι (N x v)) (C : Submodule K E)
    (hC : ∀ x, ∀ v ∈ C, N x v ∈ C) :
    Continuous fun x => LinearMap.det ((N x).restrict (hC x)) := by
  classical
  let b := Module.Free.chooseBasis K C
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective (ι ∘ₗ C.subtype)
    (LinearMap.ker_eq_bot.mpr (hι.comp C.injective_subtype))
  refine continuous_det_of_continuous_repr b _ fun c i => ?_
  have h : ∀ x, b.repr ((N x).restrict (hC x) c) i = (b.coord i ∘ₗ ψ) (ι (N x c)) := by
    intro x
    have : ι (N x c) = (ι ∘ₗ C.subtype) ((N x).restrict (hC x) c) := by
      simp [LinearMap.coe_restrict_apply]
    rw [this, LinearMap.comp_apply, ← LinearMap.comp_apply ψ (ι ∘ₗ C.subtype), hψ,
      LinearMap.id_apply]
    rfl
  simp_rw [h]
  exact (IsModuleTopology.continuous_of_linearMap (b.coord i ∘ₗ ψ)).comp (hN c)

/-- A semisimple endomorphism has `ker f ∩ Im f = 0`. -/
theorem disjoint_ker_range_of_isSemisimple {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {f : Module.End K V} (hf : f.IsSemisimple) : Disjoint (LinearMap.ker f) (LinearMap.range f) := by
  obtain ⟨q, hq, hc⟩ := Module.End.isSemisimple_iff.mp hf (LinearMap.ker f)
    ((Module.End.mem_invtSubmodule f).mpr fun v hv => by
      simp only [Submodule.mem_comap, LinearMap.mem_ker] at hv ⊢; simp [hv])
  have hrange : LinearMap.range f ≤ q := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨k, hk, c, hc', rfl⟩ := Submodule.mem_sup.mp (hc.codisjoint.eq_top ▸ Submodule.mem_top :
      v ∈ LinearMap.ker f ⊔ q)
    rw [map_add, LinearMap.mem_ker.mp hk, zero_add]
    exact (Module.End.mem_invtSubmodule f).mp hq hc'
  exact hc.disjoint.mono_right hrange


/-- A semisimple endomorphism of a finite-dimensional space has `E = ker f ⊕ im f`. -/
theorem isCompl_ker_range_of_isSemisimple {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {f : Module.End K V} (hf : f.IsSemisimple) :
    IsCompl (LinearMap.ker f) (LinearMap.range f) := by
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).2 (disjoint_ker_range_of_isSemisimple hf)
  have := LinearMap.finrank_range_add_finrank_ker f
  omega

end GSpinGGP
