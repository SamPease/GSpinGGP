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

section TorusBound

variable [IsUltrametricDist F] (hb : IsOrthoBasis Q b) {i₀ i₁ : Fin n} (hne : i₀ ≠ i₁) {ν : F}
  (h₀ : Q (b i₀) = ν) (h₁ : Q (b i₁) = -ν)

theorem one_le_norm_two_inv : 1 ≤ ‖(2 : F)‖⁻¹ :=
  one_le_inv₀ (norm_pos_iff.2 two_ne_zero) |>.2 norm_two_le_one

omit [CharZero F] in
theorem norm_add_inv_div_two_le (t : Fˣ) (σ : F) (hσ : ‖σ‖ = 1) :
    ‖((t : F) + σ * (t : F)⁻¹) / 2‖ ≤ ‖(2 : F)‖⁻¹ * max ‖(t : F)‖ ‖(t : F)‖⁻¹ := by
  rw [norm_div, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ((IsUltrametricDist.norm_add_le_max _ _).trans ?_)
    (inv_nonneg.2 (norm_nonneg _))
  rw [norm_mul, hσ, one_mul, norm_inv]

include hb hne h₀ h₁

/-- The torus is bounded: `‖a(t)‖ ≤ ‖2‖⁻¹ max(‖t‖, ‖t‖⁻¹)`. -/
theorem basisOpNorm_pairTorus_le (t : Fˣ) :
    basisOpNorm b (pairTorus hb hne h₀ h₁ t : V →ₗ[F] V) ≤
      ‖(2 : F)‖⁻¹ * max ‖(t : F)‖ ‖(t : F)‖⁻¹ := by
  have h1 : 1 ≤ ‖(2 : F)‖⁻¹ * max ‖(t : F)‖ ‖(t : F)‖⁻¹ := by
    have : 1 ≤ max ‖(t : F)‖ ‖(t : F)‖⁻¹ := by
      rcases le_total ‖(t : F)‖ 1 with h | h
      · exact le_max_of_le_right (one_le_inv₀ (norm_pos_iff.2 t.ne_zero) |>.2 h)
      · exact le_max_of_le_left h
    nlinarith [one_le_norm_two_inv (F := F)]
  have hc1 := norm_add_inv_div_two_le t 1 norm_one
  have hc2 := norm_add_inv_div_two_le t (-1) (by simp)
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at hc1 hc2
  refine (basisOpNorm_le_iff (by positivity)).2 fun m => ?_
  rw [LinearEquiv.coe_coe]
  by_cases hm₀ : m = i₀
  · subst hm₀
    rw [pairTorus_apply_left]
    refine (basisNorm_add_le _ _).trans (max_le ?_ ?_) <;>
      rw [basisNorm_smul, basisNorm_basis, mul_one] <;> assumption
  by_cases hm₁ : m = i₁
  · subst hm₁
    rw [pairTorus_apply_right]
    refine (basisNorm_add_le _ _).trans (max_le ?_ ?_) <;>
      rw [basisNorm_smul, basisNorm_basis, mul_one] <;> assumption
  rw [pairTorus_apply_basis_of_ne hb hne h₀ h₁ t hm₀ hm₁, basisNorm_basis]
  exact h1

/-- For `‖t‖ ≤ 1` the bound is `‖2‖⁻¹ ‖t‖⁻¹`, for `a(t)` and for `a(t)⁻¹`. -/
theorem basisOpNorm_pairTorus_le_of_le_one (t : Fˣ) (ht : ‖(t : F)‖ ≤ 1) :
    basisOpNorm b (pairTorus hb hne h₀ h₁ t : V →ₗ[F] V) ≤ ‖(2 : F)‖⁻¹ * ‖(t : F)‖⁻¹ ∧
      basisOpNorm b (((pairTorus hb hne h₀ h₁ t)⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) ≤
        ‖(2 : F)‖⁻¹ * ‖(t : F)‖⁻¹ := by
  have ht0 : 0 < ‖(t : F)‖ := norm_pos_iff.2 t.ne_zero
  have hmax : max ‖(t : F)‖ ‖(t : F)‖⁻¹ = ‖(t : F)‖⁻¹ :=
    max_eq_right (ht.trans (one_le_inv₀ ht0 |>.2 ht))
  refine ⟨(basisOpNorm_pairTorus_le hb hne h₀ h₁ t).trans_eq (by rw [hmax]), ?_⟩
  rw [← pairTorus_inv]
  refine (basisOpNorm_pairTorus_le hb hne h₀ h₁ t⁻¹).trans_eq ?_
  rw [Units.val_inv_eq_inv_val, norm_inv, inv_inv, max_comm, hmax]

end TorusBound

/-! ## Rotations of a plane `⟨b i₁, b k⟩` -/

section PlaneRotation

variable (hb : IsOrthoBasis Q b) {i₁ k : Fin n} (hk : i₁ ≠ k)

include hb hk

theorem apply_basis_add_smul (μ : F) :
    Q (b i₁ + μ • b k) = Q (b i₁) + μ ^ 2 * Q (b k) := by
  rw [QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul, polar_smul_right,
    hb.polar_eq_zero i₁ k hk, smul_zero, add_zero, smul_eq_mul, _root_.sq]

/-- The rotation `r_{b i₁ + μ b k} r_{b i₁}` of the plane `⟨b i₁, b k⟩`. With
`s = Q (b k) / Q (b i₁)` it sends `b i₁ ↦ ((1 - sμ²) b i₁ + 2μ b k)/(1 + sμ²)`; this is the
rational parametrization of the rotations of the plane. -/
def planeRot (μ : F) (hD : Q (b i₁) + μ ^ 2 * Q (b k) ≠ 0) : V ≃ₗ[F] V :=
  letI := invertibleOfNonzero (show Q (b i₁ + μ • b k) ≠ 0 by
    rwa [apply_basis_add_smul hb hk])
  letI := invertibleOfNonzero (hb.apply_ne_zero i₁)
  TauCeti.QuadraticMap.reflection Q (b i₁ + μ • b k) * TauCeti.QuadraticMap.reflection Q (b i₁)

theorem planeRot_mem_specialOrthogonalGroup [FiniteDimensional F V] (μ : F)
    (hD : Q (b i₁) + μ ^ 2 * Q (b k) ≠ 0) :
    planeRot hb hk μ hD ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q := by
  let := invertibleOfNonzero (show Q (b i₁ + μ • b k) ≠ 0 by
    rwa [apply_basis_add_smul hb hk])
  let := invertibleOfNonzero (hb.apply_ne_zero i₁)
  refine TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff.2
    ⟨mul_mem (TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q _)
      (TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q _), ?_⟩
  rw [planeRot, map_mul, TauCeti.QuadraticMap.det_reflection,
    TauCeti.QuadraticMap.det_reflection]
  simp

/-- The rotation moves only the coordinates `i₁`, `k`:
`γ z = z + z_{i₁} X + z_k Y` with `X = γ b i₁ - b i₁`, `Y = γ b k - b k`. -/
theorem planeRot_apply (μ : F) (hD : Q (b i₁) + μ ^ 2 * Q (b k) ≠ 0) (z : V) :
    planeRot hb hk μ hD z = z +
      b.repr z i₁ • ((-(2 * μ ^ 2 * Q (b k)) / (Q (b i₁) + μ ^ 2 * Q (b k))) • b i₁ +
        (2 * μ * Q (b i₁) / (Q (b i₁) + μ ^ 2 * Q (b k))) • b k) +
      b.repr z k • ((-(2 * μ * Q (b k)) / (Q (b i₁) + μ ^ 2 * Q (b k))) • b i₁ +
        (-(2 * μ ^ 2 * Q (b k)) / (Q (b i₁) + μ ^ 2 * Q (b k))) • b k) := by
  let := invertibleOfNonzero (show Q (b i₁ + μ • b k) ≠ 0 by
    rwa [apply_basis_add_smul hb hk])
  let := invertibleOfNonzero (hb.apply_ne_zero i₁)
  have hq₁ := hb.apply_ne_zero i₁
  set q₁ := Q (b i₁)
  set qe := Q (b k)
  set D := q₁ + μ ^ 2 * qe with hDdef
  set c₁ := b.repr z i₁
  set ce := b.repr z k
  have p1 : polar Q (b i₁) z = c₁ * (2 * q₁) := by
    rw [polar_comm, hb.polar_basis_right, polar_basis_self]
  have p2 : polar Q (b k) z = ce * (2 * qe) := by
    rw [polar_comm, hb.polar_basis_right, polar_basis_self]
  have p3 : polar Q (b i₁) (b i₁) = 2 * q₁ := polar_basis_self _
  have p4 : polar Q (b k) (b i₁) = 0 := hb.polar_eq_zero k i₁ hk.symm
  simp only [planeRot, LinearEquiv.mul_apply, TauCeti.QuadraticMap.reflection_apply, invOf_eq_inv,
    apply_basis_add_smul hb hk, polar_add_left, polar_smul_left, polar_sub_right,
    polar_smul_right, p1, p2, p3, p4, smul_eq_mul]
  rw [← hDdef]
  have e1 : -(q₁⁻¹ * (c₁ * (2 * q₁))) - D⁻¹ * (c₁ * (2 * q₁) + μ * (ce * (2 * qe)) -
      q₁⁻¹ * (c₁ * (2 * q₁)) * (2 * q₁ + μ * 0)) =
      c₁ * (-(2 * μ ^ 2 * qe) / D) + ce * (-(2 * μ * qe) / D) := by
    field_simp
    rw [hDdef]; ring
  have e2 : -(D⁻¹ * (c₁ * (2 * q₁) + μ * (ce * (2 * qe)) -
      q₁⁻¹ * (c₁ * (2 * q₁)) * (2 * q₁ + μ * 0))) * μ =
      c₁ * (2 * μ * q₁ / D) + ce * (-(2 * μ ^ 2 * qe) / D) := by
    field_simp
    ring
  calc z - (q₁⁻¹ * (c₁ * (2 * q₁))) • b i₁ -
        (D⁻¹ * (c₁ * (2 * q₁) + μ * (ce * (2 * qe)) - q₁⁻¹ * (c₁ * (2 * q₁)) *
          (2 * q₁ + μ * 0))) • (b i₁ + μ • b k)
      = z + (-(q₁⁻¹ * (c₁ * (2 * q₁))) - D⁻¹ * (c₁ * (2 * q₁) + μ * (ce * (2 * qe)) -
          q₁⁻¹ * (c₁ * (2 * q₁)) * (2 * q₁ + μ * 0))) • b i₁ +
          (-(D⁻¹ * (c₁ * (2 * q₁) + μ * (ce * (2 * qe)) -
            q₁⁻¹ * (c₁ * (2 * q₁)) * (2 * q₁ + μ * 0))) * μ) • b k := by module
    _ = _ := by rw [e1, e2]; module

end PlaneRotation

end WeakCartan

end GSpinGGP
