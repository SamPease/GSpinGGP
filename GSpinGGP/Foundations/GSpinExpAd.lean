/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.GSpinExp
import GSpinGGP.Foundations.JordanAlgebra

/-!
# `P(e^X) = e^{ad X}` near the identity

For `X ∈ gspin(V)` near `0` and `g = e^X ∈ GSpin(V)(F)`, the image `P(g) ∈ SO(V)` of `g` is the
exponential of `ad X = adV X ∈ so(V)` (`eventually_specP_eq_expA_adV`): conjugation by `e^X` on
`C(V)` is `e^{ad X}` (`expA_ad_eq`), and `e^{ad X}` restricts to `ι(V)` as `e^{ad X|_V}`, since
`ad X` preserves `ι(V)`.

* `eventually_specP_eq_expA_adV`: `P(e^X) = e^{ad X}`.
-/

noncomputable section

open Filter Topology Module CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

section Clifford

variable {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] (Q : QuadraticForm F V)

/-- **`P(e^X) = e^{ad X}`** for `X ∈ gspin(V)` near `0` (Thesis §5.1.3: `ad : gspin(V) → so(V)` is
the differential of `P : GSpin(V) → SO(V)`): if `g ∈ GSpin(V)(F)` has `g = e^X` in `C(V)`, then
`P(g) = e^{adV X}` in `End(V)`.  Conjugation by `e^X` on `C(V)` is `e^{ad X}` (`expA_ad_eq`), and
`T ↦ ι⁻¹ ∘ T ∘ ι` maps the powers of `ad X` to those of `adV X` (`ι_adV_pow`). -/
theorem eventually_specP_eq_expA_adV [TopologicalSpace (Module.End F V)]
    [IsModuleTopology F (Module.End F V)] :
    ∀ᶠ X in 𝓝 (0 : CliffordAlgebra Q), X ∈ gspin Q → ∀ g : ↥(GSpin Q),
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = expA F X →
        ((specP Q g : V ≃ₗ[F] V) : Module.End F V) = expA F (adV Q X) := by
  letI : TopologicalSpace (Module.End F (CliffordAlgebra Q)) :=
    moduleTopology F (Module.End F (CliffordAlgebra Q))
  haveI : IsModuleTopology F (Module.End F (CliffordAlgebra Q)) := ⟨rfl⟩
  let ρ : Module.End F (CliffordAlgebra Q) →ₗ[F] Module.End F V :=
    { toFun := fun T => ιInv Q ∘ₗ T ∘ₗ ι Q
      map_add' := fun S T => by ext v; simp
      map_smul' := fun c T => by ext v; simp }
  set ad : CliffordAlgebra Q →ₗ[F] Module.End F (CliffordAlgebra Q) :=
    (Algebra.lmul F (CliffordAlgebra Q)).toLinearMap - mulRightₗ with had
  have hadc : Continuous ad := IsModuleTopology.continuous_of_linearMap ad
  have h1 := (hadc.tendsto' 0 0 (map_zero ad)).eventually (eventually_map_expA_of_pow (F := F) ρ)
  obtain ⟨U₂, hU₂, hneg⟩ := expA_mul_expA_neg F (A := CliffordAlgebra Q)
  filter_upwards [h1, expA_ad_eq F (B := CliffordAlgebra Q), hU₂] with X hX1 hX2 hX3 hX g hg
  have hadX : ad X = LinearMap.mulLeft F X - LinearMap.mulRight F X := rfl
  have hginv : (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      expA F (-X) := Units.inv_eq_of_mul_eq_one_right (by rw [hg]; exact hneg X hX3)
  have hpow : ∀ n : ℕ, ρ (ad X ^ n) = ρ (ad X) ^ n := by
    intro n
    ext v
    change ιInv Q ((ad X ^ n) (ι Q v)) = (ρ (ad X) ^ n) v
    have hρ : ρ (ad X) = adV Q X := rfl
    have hadf : LinearMap.mulLeft F X - LinearMap.mulRight F X =
        LieAlgebra.ad F (CliffordAlgebra Q) X := by
      rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]; rfl
    rw [hρ, hadX, hadf, ← ι_adV_pow hX, ιInv_ι]
  have key := hX1 hpow
  rw [hadX, hX2] at key
  change _ = expA F (ρ (ad X))
  rw [hadX, ← key]
  ext v
  change specP Q g v = ιInv Q (expA F X * (ι Q v * expA F (-X)))
  rw [specP_apply_eq, hg, hginv]

end Clifford

end GSpinGGP
