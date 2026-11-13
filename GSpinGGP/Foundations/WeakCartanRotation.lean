/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.WeakCartanSO

/-!
# The split torus of a hyperbolic pair, and the rotation lemma

Continuing `GSpinGGP.Foundations.WeakCartanSO`: `b` is an orthogonal basis of anisotropic vectors,
`Q (b i₀) = ν`, `Q (b i₁) = -ν`, `u = b i₀ + b i₁`, `u' = b i₀ - b i₁`.

* `pairTorus`: the split torus `a(t)` of the plane `⟨b i₀, b i₁⟩`, `u ↦ t u`, `u' ↦ t⁻¹ u'`
  (Tau Ceti's `hyperbolicPairTorus`), with its matrix entries and the bound
  `‖a(t)‖ ≤ ‖2‖⁻¹ max(‖t‖, ‖t‖⁻¹)`.
* `pairTorus_inv_apply`: `a(t)⁻¹ (b i₀) = (2t)⁻¹ u + (t/2) u'`, the normal form of the orbit
  lemma.
* `rotation_lemma` (the orthogonal analogue of Beuzart-Plessis's Lemme 11.0.3, used for Thesis
  Prop. 8.3.1): for every isometry `h` fixing `b i₀` and every `t` with `‖t‖ ≤ 1` there is a
  rotation `γ` of a plane `⟨b i₁, b k⟩` (a product of two reflections) such that
  `a(t)⁻¹ γ a(t)` is bounded independently of `h` and `t`, `‖hγ‖ ≤ ‖h‖`, and
  `ε ‖t‖ ‖hγ‖ ≤ ‖hγ (b i₁)‖`. The rotation is parametrized rationally (a Cayley-type
  parametrization `γ = r_{b i₁ + μ b k} r_{b i₁}`), so no square roots are needed.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Module QuadraticMap

namespace GSpinGGP

namespace WeakCartan

variable {F : Type*} [NontriviallyNormedField F] [CharZero F]
variable {V : Type*} [AddCommGroup V] [Module F V] {n : ℕ} {b : Module.Basis (Fin n) F V}
  {Q : QuadraticForm F V}

/-! ## The split torus of the pair -/

section Torus

variable (hb : IsOrthoBasis Q b) {i₀ i₁ : Fin n} (hne : i₀ ≠ i₁) {ν : F} (h₀ : Q (b i₀) = ν)
  (h₁ : Q (b i₁) = -ν)

include hb hne h₀ h₁

theorem pairV_scaled_isotropic : Q ((4 * ν)⁻¹ • (b i₀ - b i₁)) = 0 := by
  rw [QuadraticMap.map_smul, pairV_isotropic hb hne h₀ h₁, smul_zero]

theorem polar_pairU_pairV_scaled :
    polar Q (b i₀ + b i₁) ((4 * ν)⁻¹ • (b i₀ - b i₁)) = 1 := by
  have hν : ν ≠ 0 := fun h => hb.apply_ne_zero i₀ (h₀.trans h)
  rw [polar_smul_right, polar_pairU_pairV hb hne h₀ h₁, smul_eq_mul,
    inv_mul_cancel₀ (mul_ne_zero (by norm_num) hν)]

/-- The split torus `a(t)` of the plane `⟨b i₀, b i₁⟩`: `u ↦ t u`, `u' ↦ t⁻¹ u'`, the identity on
the orthogonal complement. -/
def pairTorus (t : Fˣ) : V ≃ₗ[F] V :=
  (TauCeti.QuadraticMap.hyperbolicPairTorus Q (pairU_isotropic hb hne h₀ h₁)
    (pairV_scaled_isotropic hb hne h₀ h₁) (polar_pairU_pairV_scaled hb hne h₀ h₁) t :
      V ≃ₗ[F] V)

theorem pairTorus_mem_orthogonalGroup (t : Fˣ) :
    pairTorus hb hne h₀ h₁ t ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  (TauCeti.QuadraticMap.hyperbolicPairTorus Q _ _ _ t).2

theorem pairTorus_mem_specialOrthogonalGroup [FiniteDimensional F V] (t : Fˣ) :
    pairTorus hb hne h₀ h₁ t ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q :=
  TauCeti.QuadraticMap.hyperbolicPairTorus_mem_specialOrthogonalGroup _ _ _ t

theorem pairTorus_mul (s t : Fˣ) :
    pairTorus hb hne h₀ h₁ (s * t) = pairTorus hb hne h₀ h₁ s * pairTorus hb hne h₀ h₁ t := by
  simp [pairTorus, map_mul]

theorem pairTorus_one : pairTorus hb hne h₀ h₁ 1 = 1 := by
  simp [pairTorus]

theorem pairTorus_inv (t : Fˣ) :
    pairTorus hb hne h₀ h₁ t⁻¹ = (pairTorus hb hne h₀ h₁ t)⁻¹ := by
  simp [pairTorus, map_inv]

theorem pairTorus_apply (t : Fˣ) (x : V) :
    pairTorus hb hne h₀ h₁ t x = x + (((t : F) - 1) * polar Q x ((4 * ν)⁻¹ • (b i₀ - b i₁))) •
      (b i₀ + b i₁) + ((((t⁻¹ : Fˣ) : F) - 1) * polar Q x (b i₀ + b i₁)) •
        ((4 * ν)⁻¹ • (b i₀ - b i₁)) :=
  TauCeti.QuadraticMap.hyperbolicPairTorus_apply _ _ _ t x

theorem pairTorus_apply_basis_of_ne (t : Fˣ) {k : Fin n} (hk₀ : k ≠ i₀) (hk₁ : k ≠ i₁) :
    pairTorus hb hne h₀ h₁ t (b k) = b k := by
  rw [pairTorus_apply, polar_smul_right, polar_comm Q (b k), polar_comm Q (b k)]
  have e1 : polar Q (b i₀ - b i₁) (b k) = 0 := by
    rw [polar_sub_left, hb.polar_eq_zero i₀ k (Ne.symm hk₀), hb.polar_eq_zero i₁ k (Ne.symm hk₁),
      sub_zero]
  have e2 : polar Q (b i₀ + b i₁) (b k) = 0 := by
    rw [polar_add_left, hb.polar_eq_zero i₀ k (Ne.symm hk₀), hb.polar_eq_zero i₁ k (Ne.symm hk₁),
      add_zero]
  simp [e1, e2]

theorem pairTorus_apply_left (t : Fˣ) :
    pairTorus hb hne h₀ h₁ t (b i₀) =
      (((t : F) + (t : F)⁻¹) / 2) • b i₀ + (((t : F) - (t : F)⁻¹) / 2) • b i₁ := by
  have hν : ν ≠ 0 := fun h => hb.apply_ne_zero i₀ (h₀.trans h)
  rw [pairTorus_apply]
  simp only [polar_smul_right, polar_add_right, polar_sub_right, polar_basis_self, h₀,
    hb.polar_eq_zero i₀ i₁ hne, smul_eq_mul, Units.val_inv_eq_inv_val]
  have ht : (t : F) ≠ 0 := t.ne_zero
  rw [show (4 * ν)⁻¹ * (2 * ν - 0) = (1 : F) / 2 by field_simp; ring,
    show (2 * ν + 0) = 2 * ν by ring]
  rw [smul_smul]
  have : (((t : F)⁻¹ - 1) * (2 * ν) * (4 * ν)⁻¹) = ((t : F)⁻¹ - 1) / 2 := by field_simp; ring
  rw [this]
  module

theorem pairTorus_apply_right (t : Fˣ) :
    pairTorus hb hne h₀ h₁ t (b i₁) =
      (((t : F) - (t : F)⁻¹) / 2) • b i₀ + (((t : F) + (t : F)⁻¹) / 2) • b i₁ := by
  have hν : ν ≠ 0 := fun h => hb.apply_ne_zero i₀ (h₀.trans h)
  rw [pairTorus_apply]
  simp only [polar_smul_right, polar_add_right, polar_sub_right, polar_basis_self, h₁,
    hb.polar_eq_zero i₁ i₀ hne.symm, smul_eq_mul, Units.val_inv_eq_inv_val]
  rw [smul_smul]
  have h1 : (4 * ν)⁻¹ * (0 - 2 * -ν) = (1 : F) / 2 := by field_simp; ring
  have h2 : ((t : F)⁻¹ - 1) * (0 + 2 * -ν) * (4 * ν)⁻¹ = -(((t : F)⁻¹ - 1) / 2) := by
    field_simp; ring
  rw [h1, h2]
  module

/-- `a(t)⁻¹ (b i₀) = (2t)⁻¹ u + (t/2) u'`: the normal form reached by the orbit lemma. -/
theorem pairTorus_inv_apply_left (t : Fˣ) :
    (pairTorus hb hne h₀ h₁ t)⁻¹ (b i₀) =
      (2 * (t : F))⁻¹ • (b i₀ + b i₁) + ((t : F) / 2) • (b i₀ - b i₁) := by
  rw [← pairTorus_inv, pairTorus_apply_left]
  simp only [Units.val_inv_eq_inv_val, inv_inv]
  have ht : (t : F) ≠ 0 := t.ne_zero
  rw [mul_inv]
  module

end Torus

end WeakCartan

end GSpinGGP
