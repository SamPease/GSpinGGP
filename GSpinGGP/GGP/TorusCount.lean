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

end GGPData

end GSpinGGP
