/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TorusFrame

/-!
# Counting elements of `Γ(G,H)` torus by torus

Ingredients of the torus-class count (`torusClass_count`, Thesis (6.7.2)–(6.7.5)).

* `commute_torusOf_of_commute`: for `x ∈ Γ(G,H)`, an element of `GSpin(W)(F)` commuting with `x`
  commutes with all of `T_x(F)` (by base change, from `Steinberg.commute_of_fixes_eigenspace_one`).
  Consequently (not formalized here) `N(T_x)` acts freely, through `W(T_x) = N(T_x)/Z(T_x)`, on the
  elements `t` with `T_t = T_x`.
-/

noncomputable section

open QuadraticMap
open scoped TensorProduct

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **A conjugate of a unit by a scalar multiple**: in a finite-dimensional algebra, if
`g u g⁻¹ = c • u` for a unit `u`, then `c ^ dim A = 1` (compare the determinants of left
multiplication). -/
theorem pow_finrank_eq_one_of_conj_eq_smul {K A : Type*} [Field K] [Ring A] [Algebra K A]
    [FiniteDimensional K A] {u g : Aˣ} {c : K}
    (h : ((g * u * g⁻¹ : Aˣ) : A) = c • (u : A)) : c ^ Module.finrank K A = 1 := by
  have hdet : ∀ v : Aˣ, LinearMap.det (LinearMap.mulLeft K (v : A)) *
      LinearMap.det (LinearMap.mulLeft K ((v⁻¹ : Aˣ) : A)) = 1 := fun v => by
    rw [← LinearMap.det_comp, ← LinearMap.mulLeft_mul, Units.mul_inv, LinearMap.mulLeft_one,
      LinearMap.det_id]
  have h1 : LinearMap.det (LinearMap.mulLeft K ((g * u * g⁻¹ : Aˣ) : A)) =
      LinearMap.det (LinearMap.mulLeft K (u : A)) := by
    rw [Units.val_mul, Units.val_mul, LinearMap.mulLeft_mul, LinearMap.mulLeft_mul,
      LinearMap.det_comp, LinearMap.det_comp]
    linear_combination LinearMap.det (LinearMap.mulLeft K (u : A)) * hdet g
  have h2 : LinearMap.det (LinearMap.mulLeft K (c • (u : A))) =
      c ^ Module.finrank K A * LinearMap.det (LinearMap.mulLeft K (u : A)) := by
    rw [show LinearMap.mulLeft K (c • (u : A)) = c • LinearMap.mulLeft K (u : A) by
      ext; simp [smul_mul_assoc], LinearMap.det_smul]
  rw [h, h2] at h1
  have hu : LinearMap.det (LinearMap.mulLeft K (u : A)) ≠ 0 := fun h0 => by
    have := hdet u; rw [h0, zero_mul] at this; exact zero_ne_one this
  exact (mul_eq_right₀ hu).1 h1

namespace GGPData

variable {d : GGPData F}

/-- Base change maps `T_x(F)` into `T_x(F̄)`. -/
theorem bcGSpin_mem_torusFbar {x t : ↥(GSpin d.QW)} (ht : t ∈ d.torusOf x) :
    bcGSpin d.QW t ∈ d.torusFbar x := by
  refine ⟨?_, fun w hw => ?_⟩
  · have h := congrArg (fun g : ↥(GSpin d.QW) => bcUnits d.QW (g : (CliffordAlgebra d.QW)ˣ))
      (Subgroup.mem_centralizer_singleton_iff.1 ht.1)
    simp only [Subgroup.coe_mul, map_mul] at h
    exact h
  · change (specP _ (bcGSpin d.QW t) : _ →ₗ[AlgebraicClosure F] _) w = w
    rw [specP_bcGSpin]
    obtain ⟨u, rfl⟩ := Submodule.toBaseChange_surjective' (AlgebraicClosure F) _ hw
    clear hw
    induction u using TensorProduct.inductionOn with
    | tmul k v =>
      rw [Submodule.coe_toBaseChange_tmul, LinearMap.baseChange_tmul]
      congr 1
      exact ht.2 v v.2
    | add u v hu hv => rw [map_add, Submodule.coe_add, map_add, hu, hv]

/-- **Centralizers of elements of `Γ(G,H)` centralize their torus**: for `x ∈ Γ(G,H)`, an element
`z` of `GSpin(W)(F)` commuting with `x` commutes with every `t ∈ T_x(F)`. -/
theorem commute_torusOf_of_commute {x z t : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    (hzx : Commute z x) (ht : t ∈ d.torusOf x) : Commute z t := by
  have h := Steinberg.commute_of_fixes_eigenspace_one (x := bcGSpin d.QW x)
    (isNondeg_baseChange _ d.nondeg)
    (by rw [specP_bcGSpin]; exact isSemisimple_specP_baseChange x hx.1)
    (by rw [specP_bcGSpin]; exact lieAbelian_specP_baseChange x hx)
    (t := bcGSpin d.QW t) (z := bcGSpin d.QW z)
    (Subtype.ext (bcGSpin_mem_torusFbar ht).1.eq)
    (fun w hw => (bcGSpin_mem_torusFbar ht).2 w (by rwa [GGPData.eigenspace_bc_one] at hw))
    (hzx.map (bcGSpin d.QW))
  exact bcGSpin_injective d.QW (by rw [map_mul, map_mul, h.eq])

/-- **Finitely many conjugates of `x` in `T_x(F)`**: for `x ∈ Γ(G,H)`, only finitely many
`t ∈ T_x(F)` are `GSpin(W)(F̄)`-conjugate to `x`. Over `F̄`, `P(t)` acts on an eigen-frame of
`P(x)` by eigenvalues of `P(x)` (roots of its minimal polynomial), so takes finitely many values;
and two such `t` with the same `P(t)` differ by a scalar `c` with `c ^ N = 1`
(`pow_finrank_eq_one_of_conj_eq_smul`). -/
theorem finite_conj_torusOf {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) :
    {t : ↥(GSpin d.QW) | t ∈ d.torusOf x ∧ ∃ g : ↥(GSpin (d.QW.baseChange (AlgebraicClosure F))),
      g * bcGSpin d.QW x * g⁻¹ = bcGSpin d.QW t}.Finite := by
  classical
  set S := {t : ↥(GSpin d.QW) | t ∈ d.torusOf x ∧ ∃ g : ↥(GSpin (d.QW.baseChange (AlgebraicClosure F))),
      g * bcGSpin d.QW x * g⁻¹ = bcGSpin d.QW t}
  obtain ⟨n, e, f, hF, heq⟩ := exists_hypFrame_torusFbar x hx
  set X : Module.End (AlgebraicClosure F) (AlgebraicClosure F ⊗[F] (Fin d.m → F)) :=
    (specP _ (bcGSpin d.QW x) : AlgebraicClosure F ⊗[F] (Fin d.m → F) →ₗ[AlgebraicClosure F]
      AlgebraicClosure F ⊗[F] (Fin d.m → F))
  set R : Set (AlgebraicClosure F)ˣ := {c | (minpoly (AlgebraicClosure F) X).IsRoot (c : (AlgebraicClosure F))}
  have hR : R.Finite := ((Polynomial.finite_setOfPred_isRoot
    (minpoly.ne_zero (Algebra.IsIntegral.isIntegral X))).preimage Units.val_injective.injOn)
  have : Finite R := hR.to_subtype
  -- the frame scalars of `P(t)` are eigenvalues of `X`
  have hscal : ∀ t ∈ S, ∃ τ : Fin n → R, (∀ w ∈ Module.End.eigenspace X 1,
      specP _ (bcGSpin d.QW t) w = w) ∧ ∀ i, specP _ (bcGSpin d.QW t) (e i) = ((τ i : (AlgebraicClosure F)ˣ) : (AlgebraicClosure F)) • e i ∧
        specP _ (bcGSpin d.QW t) (f i) = ((((τ i : (AlgebraicClosure F)ˣ))⁻¹ : (AlgebraicClosure F)ˣ) : (AlgebraicClosure F)) • f i := by
    rintro t ⟨ht, g, hg⟩
    obtain ⟨hW, τ, hτ⟩ : specP _ (bcGSpin d.QW t) ∈ hypTorus (Module.End.eigenspace X 1) e f :=
      heq ▸ Subgroup.mem_map_of_mem _ (bcGSpin_mem_torusFbar ht)
    have hmem : ∀ i, τ i ∈ R := fun i => by
      have he : e i ≠ 0 := fun h0 => by
        have := hF.polar_ef_self i; rw [h0, polar_zero_left] at this; exact zero_ne_one this
      set v := specP _ g⁻¹ (e i)
      have hv : v ≠ 0 := fun h0 => he (by
        have := congrArg (specP _ g) h0
        rw [map_zero, ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at this
        exact this)
      have hXv : X v = ((τ i : (AlgebraicClosure F)ˣ) : (AlgebraicClosure F)) • v := by
        have h1 : specP _ g⁻¹ * specP _ (bcGSpin d.QW t) = specP _ (bcGSpin d.QW x) * specP _ g⁻¹ := by
          rw [← map_mul, ← map_mul, ← hg]; congr 1; group
        have h2 := congrArg (fun φ => φ (e i)) h1
        simp only [LinearEquiv.mul_apply, (hτ i).1, map_smul] at h2
        exact h2.symm
      exact (Module.End.hasEigenvalue_iff_isRoot).1
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hXv, hv⟩)
    exact ⟨fun i => ⟨τ i, hmem i⟩, hW, hτ⟩
  sorry

end GGPData

end GSpinGGP
