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


section PlaneRotationFacts

variable (hb : IsOrthoBasis Q b) {i₁ k : Fin n} (hk : i₁ ≠ k)
include hb hk

theorem planeRot_apply_of_ne (μ : F) (hD : Q (b i₁) + μ ^ 2 * Q (b k) ≠ 0) {m : Fin n}
    (hm₁ : m ≠ i₁) (hmk : m ≠ k) : planeRot hb hk μ hD (b m) = b m := by
  rw [planeRot_apply]
  simp [hm₁, hmk]

theorem planeRot_apply_left (μ : F) (hD : Q (b i₁) + μ ^ 2 * Q (b k) ≠ 0) :
    planeRot hb hk μ hD (b i₁) =
      (1 - 2 * μ ^ 2 * Q (b k) / (Q (b i₁) + μ ^ 2 * Q (b k))) • b i₁ +
        (2 * μ * Q (b i₁) / (Q (b i₁) + μ ^ 2 * Q (b k))) • b k := by
  rw [planeRot_apply]
  simp [hk.symm]
  module

theorem planeRot_apply_right (μ : F) (hD : Q (b i₁) + μ ^ 2 * Q (b k) ≠ 0) :
    planeRot hb hk μ hD (b k) =
      (-(2 * μ * Q (b k)) / (Q (b i₁) + μ ^ 2 * Q (b k))) • b i₁ +
        (1 - 2 * μ ^ 2 * Q (b k) / (Q (b i₁) + μ ^ 2 * Q (b k))) • b k := by
  rw [planeRot_apply]
  simp [hk]
  module

end PlaneRotationFacts

omit [CharZero F] in
theorem exists_basisOpNorm_eq (hn : 0 < n) (f : V →ₗ[F] V) :
    ∃ m, basisNorm b (f (b m)) = basisOpNorm b f := by
  have : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun m => basisNorm b (f (b m))) this
  exact ⟨m, le_antisymm (basisNorm_apply_basis_le_basisOpNorm f m)
    ((basisOpNorm_le_iff (basisNorm_nonneg _)).2 fun k => hm k (Finset.mem_univ k))⟩

/-- A vector with `Q x = c ≠ 0` is not too short: `min 1 (‖c‖ / c_Q) ≤ ‖x‖`. -/
theorem min_le_basisNorm_of_apply [IsUltrametricDist F] (hb : IsOrthoBasis Q b) {x : V} {c : F}
    (hx : Q x = c) (hc : c ≠ 0) : min 1 (‖c‖ / formBound Q b) ≤ basisNorm b x := by
  have hfB := hb.norm_apply_le x
  rw [hx] at hfB
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hfB0 : 0 < formBound Q b := by
    by_contra h
    have : formBound Q b = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
    rw [this, zero_mul] at hfB
    linarith
  rcases le_total 1 (basisNorm b x) with h | h
  · exact (min_le_left _ _).trans h
  · refine (min_le_right _ _).trans ?_
    rw [div_le_iff₀ hfB0]
    have hN := basisNorm_nonneg (b := b) x
    have h2 : basisNorm b x ^ 2 ≤ basisNorm b x := by nlinarith
    calc ‖c‖ ≤ formBound Q b * basisNorm b x ^ 2 := hfB
      _ ≤ formBound Q b * basisNorm b x := mul_le_mul_of_nonneg_left h2 hfB0.le
      _ = _ := mul_comm _ _


section RotationLemma

variable [IsUltrametricDist F]

theorem repr_pairTorus_apply_of_ne (hb : IsOrthoBasis Q b) {i₀ i₁ : Fin n} (hne : i₀ ≠ i₁)
    {ν : F} (h₀ : Q (b i₀) = ν) (h₁ : Q (b i₁) = -ν) (t : Fˣ) (x : V) {k : Fin n}
    (hk₀ : k ≠ i₀) (hk₁ : k ≠ i₁) :
    b.repr (pairTorus hb hne h₀ h₁ t x) k = b.repr x k := by
  rw [pairTorus_apply]
  simp [Ne.symm hk₀, Ne.symm hk₁]

/-- The bounds on the rotation `γ = planeRot` with parameter `μ = κ t`: `‖γ‖ ≤ 1`,
`γ b i₁ = a b i₁ + B b k` with `‖a‖ ≤ 1`, `‖B‖ = ‖2κt‖`, and `‖a(t)⁻¹ γ a(t)‖ ≤ ‖2‖⁻¹`. -/
theorem planeRot_bounds (hb : IsOrthoBasis Q b) {i₀ i₁ : Fin n} (hne : i₀ ≠ i₁) {ν : F}
    (h₀ : Q (b i₀) = ν) (h₁ : Q (b i₁) = -ν) {k : Fin n} (hk : i₁ ≠ k) (hk₀ : k ≠ i₀)
    {κ : F} (hκ1 : ‖κ‖ < 1) (hκs : ‖κ‖ * (formBound Q b * ‖(Q (b i₁))⁻¹‖) ≤ 1)
    (t : Fˣ) (ht : ‖(t : F)‖ ≤ 1) :
    ∃ hD : Q (b i₁) + (κ * t) ^ 2 * Q (b k) ≠ 0,
      basisOpNorm b (planeRot hb hk (κ * t) hD : V →ₗ[F] V) ≤ 1 ∧
      (∃ a B : F, ‖a‖ ≤ 1 ∧ ‖B‖ = ‖(2 : F)‖ * ‖κ‖ * ‖(t : F)‖ ∧
        planeRot hb hk (κ * t) hD (b i₁) = a • b i₁ + B • b k) ∧
      basisOpNorm b (((pairTorus hb hne h₀ h₁ t)⁻¹ * planeRot hb hk (κ * t) hD *
        pairTorus hb hne h₀ h₁ t : V ≃ₗ[F] V) : V →ₗ[F] V) ≤ ‖(2 : F)‖⁻¹ := by
  set q₁ := Q (b i₁) with hq₁def
  set qk := Q (b k) with hqkdef
  set μ : F := κ * t with hμ
  set r := ‖κ‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hq₁ : q₁ ≠ 0 := hb.apply_ne_zero i₁
  have hq₁n : 0 < ‖q₁‖ := norm_pos_iff.2 hq₁
  have ht0 : 0 < ‖(t : F)‖ := norm_pos_iff.2 t.ne_zero
  have h2 : 0 < ‖(2 : F)‖ := norm_pos_iff.2 two_ne_zero
  have h21 : ‖(2 : F)‖ ≤ 1 := norm_two_le_one
  have hqk : ‖qk‖ ≤ (formBound Q b * ‖q₁⁻¹‖) * ‖q₁‖ := by
    rw [mul_assoc, ← norm_mul, inv_mul_cancel₀ hq₁, norm_one, mul_one]
    exact norm_apply_basis_le k
  have hμn : ‖μ‖ = r * ‖(t : F)‖ := by rw [hμ, norm_mul]
  -- `‖μ² qk‖ ≤ r ‖t‖² ‖q₁‖ < ‖q₁‖`
  have hμqk : ‖μ ^ 2 * qk‖ ≤ r * ‖(t : F)‖ ^ 2 * ‖q₁‖ := by
    rw [norm_mul, norm_pow, hμn]
    calc (r * ‖(t : F)‖) ^ 2 * ‖qk‖ ≤ (r * ‖(t : F)‖) ^ 2 *
          ((formBound Q b * ‖q₁⁻¹‖) * ‖q₁‖) := by gcongr
      _ = r * ‖(t : F)‖ ^ 2 * ‖q₁‖ * (r * (formBound Q b * ‖q₁⁻¹‖)) := by ring
      _ ≤ r * ‖(t : F)‖ ^ 2 * ‖q₁‖ * 1 := by gcongr
      _ = _ := mul_one _
  have hμqk' : ‖μ ^ 2 * qk‖ < ‖q₁‖ := hμqk.trans_lt (by
    have : r * ‖(t : F)‖ ^ 2 < 1 := by
      calc r * ‖(t : F)‖ ^ 2 ≤ r * 1 := by gcongr; exact pow_le_one₀ ht0.le ht
        _ < 1 := by rw [mul_one]; exact hκ1
    nlinarith)
  have hDn : ‖q₁ + μ ^ 2 * qk‖ = ‖q₁‖ := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hμqk'.ne', max_eq_left hμqk'.le]
  have hD : q₁ + μ ^ 2 * qk ≠ 0 := by
    intro h; rw [h, norm_zero] at hDn; exact hq₁n.ne' hDn.symm
  set D := q₁ + μ ^ 2 * qk with hDdef
  -- the coefficients
  have hcX : ‖-(2 * μ ^ 2 * qk) / D‖ ≤ ‖(2 : F)‖ * r * ‖(t : F)‖ ^ 2 := by
    rw [norm_div, hDn, norm_neg, mul_assoc, norm_mul, div_le_iff₀ hq₁n]
    calc ‖(2 : F)‖ * ‖μ ^ 2 * qk‖ ≤ ‖(2 : F)‖ * (r * ‖(t : F)‖ ^ 2 * ‖q₁‖) := by gcongr
      _ = _ := by ring
  have hB : ‖2 * μ * q₁ / D‖ = ‖(2 : F)‖ * r * ‖(t : F)‖ := by
    rw [norm_div, hDn, norm_mul, norm_mul, hμn]; field_simp
  have hcY : ‖-(2 * μ * qk) / D‖ ≤ ‖(2 : F)‖ * ‖(t : F)‖ := by
    rw [norm_div, hDn, norm_neg, norm_mul, norm_mul, hμn, div_le_iff₀ hq₁n]
    calc ‖(2 : F)‖ * (r * ‖(t : F)‖) * ‖qk‖ ≤ ‖(2 : F)‖ * (r * ‖(t : F)‖) *
          ((formBound Q b * ‖q₁⁻¹‖) * ‖q₁‖) := by gcongr
      _ = ‖(2 : F)‖ * ‖(t : F)‖ * ‖q₁‖ * (r * (formBound Q b * ‖q₁⁻¹‖)) := by ring
      _ ≤ ‖(2 : F)‖ * ‖(t : F)‖ * ‖q₁‖ * 1 := by gcongr
      _ = _ := by ring
  have ht2 : ‖(t : F)‖ ^ 2 ≤ 1 := pow_le_one₀ ht0.le ht
  have hcX1 : ‖-(2 * μ ^ 2 * qk) / D‖ ≤ 1 := hcX.trans (by
    calc ‖(2 : F)‖ * r * ‖(t : F)‖ ^ 2 ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring)
  have ha : ‖1 - 2 * μ ^ 2 * qk / D‖ ≤ 1 := by
    rw [sub_eq_add_neg, ← neg_div]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le norm_one.le hcX1)
  have hB1 : ‖2 * μ * q₁ / D‖ ≤ 1 := by
    rw [hB]
    calc ‖(2 : F)‖ * r * ‖(t : F)‖ ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  have hcY1 : ‖-(2 * μ * qk) / D‖ ≤ 1 := hcY.trans (by
    calc ‖(2 : F)‖ * ‖(t : F)‖ ≤ 1 * 1 := by gcongr
      _ = 1 := by ring)
  refine ⟨hD, ?_, ⟨_, _, ha, hB, planeRot_apply_left hb hk μ hD⟩, ?_⟩
  · -- `‖γ‖ ≤ 1`
    refine (basisOpNorm_le_iff zero_le_one).2 fun m => ?_
    rw [LinearEquiv.coe_coe]
    by_cases hm₁ : m = i₁
    · subst hm₁
      rw [planeRot_apply_left]
      refine (basisNorm_add_le _ _).trans (max_le ?_ ?_) <;>
        rw [basisNorm_smul, basisNorm_basis, mul_one] <;> assumption
    by_cases hmk : m = k
    · subst hmk
      rw [planeRot_apply_right]
      refine (basisNorm_add_le _ _).trans (max_le ?_ ?_) <;>
        rw [basisNorm_smul, basisNorm_basis, mul_one] <;> assumption
    rw [planeRot_apply_of_ne hb hk μ hD hm₁ hmk, basisNorm_basis]
  · -- `‖a(t)⁻¹ γ a(t)‖ ≤ ‖2‖⁻¹`
    set T := pairTorus hb hne h₀ h₁ t
    obtain ⟨hT, hTi⟩ := basisOpNorm_pairTorus_le_of_le_one hb hne h₀ h₁ t ht
    have h2i : 1 ≤ ‖(2 : F)‖⁻¹ := one_le_norm_two_inv
    have hTk : T⁻¹ (b k) = b k := by
      rw [← pairTorus_inv]; exact pairTorus_apply_basis_of_ne hb hne h₀ h₁ _ hk₀ hk.symm
    have hTb₁ : basisNorm b (T⁻¹ (b i₁)) ≤ ‖(2 : F)‖⁻¹ * ‖(t : F)‖⁻¹ := by
      have := basisNorm_apply_basis_le_basisOpNorm (b := b) (((T⁻¹ : V ≃ₗ[F] V)) : V →ₗ[F] V) i₁
      exact this.trans hTi
    refine (basisOpNorm_le_iff (by positivity)).2 fun m => ?_
    set x := T (b m) with hx
    have hxn : basisNorm b x ≤ ‖(2 : F)‖⁻¹ * ‖(t : F)‖⁻¹ :=
      (basisNorm_apply_basis_le_basisOpNorm (b := b) (T : V →ₗ[F] V) m).trans hT
    have hxk : ‖b.repr x k‖ ≤ 1 := by
      rw [hx, repr_pairTorus_apply_of_ne hb hne h₀ h₁ t _ hk₀ hk.symm]
      exact (norm_repr_le_basisNorm _ _).trans (basisNorm_basis m).le
    have hCm : (((T⁻¹ * planeRot hb hk μ hD * T : V ≃ₗ[F] V)) : V →ₗ[F] V) (b m) =
        b m + b.repr x i₁ • ((-(2 * μ ^ 2 * qk) / D) • T⁻¹ (b i₁) + (2 * μ * q₁ / D) • b k) +
          b.repr x k • ((-(2 * μ * qk) / D) • T⁻¹ (b i₁) +
            (-(2 * μ ^ 2 * qk) / D) • b k) := by
      rw [LinearEquiv.coe_coe, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hx,
        planeRot_apply]
      simp only [map_add, map_smul, hTk]
      rw [hx, ← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
    rw [hCm]
    refine (basisNorm_add_le _ _).trans (max_le ((basisNorm_add_le _ _).trans
      (max_le (by rw [basisNorm_basis]; exact h2i) ?_)) ?_)
    · rw [basisNorm_smul]
      have hX : basisNorm b ((-(2 * μ ^ 2 * qk) / D) • T⁻¹ (b i₁) + (2 * μ * q₁ / D) • b k) ≤
          ‖(t : F)‖ := by
        refine (basisNorm_add_le _ _).trans (max_le ?_ ?_)
        · rw [basisNorm_smul]
          calc ‖-(2 * μ ^ 2 * qk) / D‖ * basisNorm b (T⁻¹ (b i₁))
              ≤ (‖(2 : F)‖ * r * ‖(t : F)‖ ^ 2) * (‖(2 : F)‖⁻¹ * ‖(t : F)‖⁻¹) :=
                mul_le_mul hcX hTb₁ (basisNorm_nonneg _) (by positivity)
            _ = r * ‖(t : F)‖ := by field_simp
            _ ≤ 1 * ‖(t : F)‖ := by gcongr
            _ = _ := one_mul _
        · rw [basisNorm_smul, basisNorm_basis, mul_one, hB]
          calc ‖(2 : F)‖ * r * ‖(t : F)‖ ≤ 1 * 1 * ‖(t : F)‖ := by gcongr
            _ = _ := by ring
      calc ‖b.repr x i₁‖ * basisNorm b ((-(2 * μ ^ 2 * qk) / D) • T⁻¹ (b i₁) +
            (2 * μ * q₁ / D) • b k)
          ≤ (‖(2 : F)‖⁻¹ * ‖(t : F)‖⁻¹) * ‖(t : F)‖ :=
            mul_le_mul ((norm_repr_le_basisNorm _ _).trans hxn) hX (basisNorm_nonneg _)
              (by positivity)
        _ = ‖(2 : F)‖⁻¹ := by field_simp
    · rw [basisNorm_smul]
      have hY : basisNorm b ((-(2 * μ * qk) / D) • T⁻¹ (b i₁) +
          (-(2 * μ ^ 2 * qk) / D) • b k) ≤ 1 := by
        refine (basisNorm_add_le _ _).trans (max_le ?_ ?_)
        · rw [basisNorm_smul]
          calc ‖-(2 * μ * qk) / D‖ * basisNorm b (T⁻¹ (b i₁))
              ≤ (‖(2 : F)‖ * ‖(t : F)‖) * (‖(2 : F)‖⁻¹ * ‖(t : F)‖⁻¹) :=
                mul_le_mul hcY hTb₁ (basisNorm_nonneg _) (by positivity)
            _ = 1 := by field_simp
        · rw [basisNorm_smul, basisNorm_basis, mul_one]; exact hcX1
      calc ‖b.repr x k‖ * basisNorm b ((-(2 * μ * qk) / D) • T⁻¹ (b i₁) +
            (-(2 * μ ^ 2 * qk) / D) • b k) ≤ 1 * 1 :=
            mul_le_mul hxk hY (basisNorm_nonneg _) zero_le_one
        _ ≤ _ := by rw [mul_one]; exact h2i


/-- **The rotation lemma** (Thesis Prop. 8.3.1, second step; the orthogonal analogue of
Beuzart-Plessis's Lemme 11.0.3). Let `a(t)` be the torus of the pair `(b i₀, b i₁)` and `S'` a set
of further indices. There is `ε > 0` such that for every isometry `h` fixing the basis vectors
outside `{i₁} ∪ S'` and every unit `t` with `‖t‖ ≤ 1` there is `γ ∈ SO(Q)` fixing the same basis
vectors (so `γ` fixes `b i₀`) with `‖a(t)⁻¹ γ a(t)‖ ≤ ‖2‖⁻¹`, `‖hγ‖ ≤ ‖h‖` and
`ε ‖t‖ ‖hγ‖ ≤ ‖hγ (b i₁)‖`. -/
theorem rotation_lemma [FiniteDimensional F V] (hb : IsOrthoBasis Q b) {i₀ i₁ : Fin n}
    (hne : i₀ ≠ i₁) {ν : F} (h₀ : Q (b i₀) = ν) (h₁ : Q (b i₁) = -ν) {S' : Finset (Fin n)}
    (h₀S : i₀ ∉ S') :
    ∃ ε > 0, ∀ h : V ≃ₗ[F] V, h ∈ TauCeti.QuadraticMap.orthogonalGroup Q →
      (∀ m, m ≠ i₁ → m ∉ S' → h (b m) = b m) → ∀ t : Fˣ, ‖(t : F)‖ ≤ 1 →
      ∃ γ ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q,
        (∀ m, m ≠ i₁ → m ∉ S' → γ (b m) = b m) ∧
        basisOpNorm b (((pairTorus hb hne h₀ h₁ t)⁻¹ * γ * pairTorus hb hne h₀ h₁ t :
          V ≃ₗ[F] V) : V →ₗ[F] V) ≤ ‖(2 : F)‖⁻¹ ∧
        basisOpNorm b ((h * γ : V ≃ₗ[F] V) : V →ₗ[F] V) ≤ basisOpNorm b (h : V →ₗ[F] V) ∧
        ε * ‖(t : F)‖ * basisOpNorm b ((h * γ : V ≃ₗ[F] V) : V →ₗ[F] V) ≤
          basisNorm b ((h * γ) (b i₁)) := by
  have hν : ν ≠ 0 := fun h => hb.apply_ne_zero i₀ (h₀.trans h)
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) i₀.2
  set smax := formBound Q b * ‖(Q (b i₁))⁻¹‖ with hsmax
  have hsmax0 : 0 ≤ smax := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hfB0 : 0 < formBound Q b :=
    (norm_pos_iff.2 (hb.apply_ne_zero i₁)).trans_le (norm_apply_basis_le i₁)
  obtain ⟨κ, hκ0, hκ⟩ := NormedField.exists_norm_lt F (inv_pos.2 (by linarith : 0 < smax + 1))
  have hκ1 : ‖κ‖ < 1 := hκ.trans_le (inv_le_one_of_one_le₀ (by linarith))
  have hκs : ‖κ‖ * smax ≤ 1 := by
    have hpos : 0 < smax + 1 := by linarith
    have h' := mul_lt_mul_of_pos_right hκ hpos
    rw [inv_mul_cancel₀ hpos.ne'] at h'
    nlinarith [norm_nonneg κ]
  set m₀ := min 1 (‖-ν‖ / formBound Q b) with hm₀
  have hm₀0 : 0 < m₀ := lt_min one_pos (div_pos (norm_pos_iff.2 (neg_ne_zero.2 hν)) hfB0)
  have h2 : 0 < ‖(2 : F)‖ := norm_pos_iff.2 two_ne_zero
  refine ⟨min m₀ (‖(2 : F)‖ * ‖κ‖), lt_min hm₀0 (mul_pos h2 hκ0), fun h hO hfix t ht => ?_⟩
  set ε := min m₀ (‖(2 : F)‖ * ‖κ‖)
  have hε1 : ε ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hε0 : 0 ≤ ε := (lt_min hm₀0 (mul_pos h2 hκ0)).le
  have ht0 : 0 ≤ ‖(t : F)‖ := norm_nonneg _
  have hh0 := basisOpNorm_nonneg (b := b) (h : V →ₗ[F] V)
  by_cases hc : ε * ‖(t : F)‖ * basisOpNorm b (h : V →ₗ[F] V) ≤ basisNorm b (h (b i₁))
  · refine ⟨1, one_mem _, fun _ _ _ => rfl, ?_, by simp, by simpa using hc⟩
    simp only [mul_one, inv_mul_cancel]
    exact basisOpNorm_id_le.trans one_le_norm_two_inv
  rw [not_le] at hc
  obtain ⟨k, hk⟩ := exists_basisOpNorm_eq (b := b) hn (h : V →ₗ[F] V)
  rw [LinearEquiv.coe_coe] at hk
  have hk₁ : i₁ ≠ k := by
    rintro rfl
    have : ε * ‖(t : F)‖ * basisOpNorm b (h : V →ₗ[F] V) ≤ basisOpNorm b (h : V →ₗ[F] V) := by
      calc ε * ‖(t : F)‖ * basisOpNorm b (h : V →ₗ[F] V) ≤ 1 * 1 *
            basisOpNorm b (h : V →ₗ[F] V) := by gcongr
        _ = _ := by ring
    linarith
  have hkS : k ∈ S' := by
    by_contra hkS
    rw [hfix k (Ne.symm hk₁) hkS, basisNorm_basis] at hk
    have hlow := min_le_basisNorm_of_apply hb
      (show Q (h (b i₁)) = -ν by rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hO, h₁])
      (neg_ne_zero.2 hν)
    rw [← hk, mul_one] at hc
    have : ε * ‖(t : F)‖ ≤ m₀ := by
      calc ε * ‖(t : F)‖ ≤ m₀ * 1 := mul_le_mul (min_le_left _ _) ht ht0 hm₀0.le
        _ = m₀ := mul_one _
    linarith
  have hk₀ : k ≠ i₀ := fun hk => h₀S (hk ▸ hkS)
  obtain ⟨hD, hγ1, ⟨a, B, ha, hB, hγb⟩, hconj⟩ :=
    planeRot_bounds hb hne h₀ h₁ hk₁ hk₀ hκ1 (by rw [← hsmax]; exact hκs) t ht
  set γ := planeRot hb hk₁ (κ * t) hD
  have hhγ : basisOpNorm b ((h * γ : V ≃ₗ[F] V) : V →ₗ[F] V) ≤ basisOpNorm b (h : V →ₗ[F] V) :=
    (basisOpNorm_mul_le h γ).trans (by nlinarith [basisOpNorm_nonneg (b := b) (γ : V →ₗ[F] V)])
  refine ⟨γ, planeRot_mem_specialOrthogonalGroup hb hk₁ _ hD,
    fun m hm₁ hmS => planeRot_apply_of_ne hb hk₁ _ hD hm₁ (fun hmk => hmS (hmk ▸ hkS)),
    hconj, hhγ, ?_⟩
  -- the dominant term `B h (b k)`
  have hdom : basisNorm b (a • h (b i₁)) < basisNorm b (B • h (b k)) := by
    rw [basisNorm_smul, basisNorm_smul, hB, hk]
    calc ‖a‖ * basisNorm b (h (b i₁)) ≤ 1 * basisNorm b (h (b i₁)) :=
          mul_le_mul_of_nonneg_right ha (basisNorm_nonneg _)
      _ < ε * ‖(t : F)‖ * basisOpNorm b (h : V →ₗ[F] V) := by rw [one_mul]; exact hc
      _ ≤ ‖(2 : F)‖ * ‖κ‖ * ‖(t : F)‖ * basisOpNorm b (h : V →ₗ[F] V) := by
          gcongr; exact min_le_right _ _
  have heq : basisNorm b ((h * γ) (b i₁)) =
      ‖(2 : F)‖ * ‖κ‖ * ‖(t : F)‖ * basisOpNorm b (h : V →ₗ[F] V) := by
    rw [LinearEquiv.mul_apply, hγb, map_add, map_smul, map_smul, add_comm,
      basisNorm_add_eq_left hdom, basisNorm_smul, hB, hk]
  rw [heq]
  calc ε * ‖(t : F)‖ * basisOpNorm b ((h * γ : V ≃ₗ[F] V) : V →ₗ[F] V)
      ≤ ε * ‖(t : F)‖ * basisOpNorm b (h : V →ₗ[F] V) := by gcongr
    _ ≤ ‖(2 : F)‖ * ‖κ‖ * ‖(t : F)‖ * basisOpNorm b (h : V →ₗ[F] V) := by
        gcongr; exact min_le_right _ _

end RotationLemma

end WeakCartan

end GSpinGGP
