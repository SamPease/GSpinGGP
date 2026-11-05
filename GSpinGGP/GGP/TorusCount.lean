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
