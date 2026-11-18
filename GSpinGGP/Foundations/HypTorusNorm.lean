/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.HypFrame
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Eigenvalues and norms on the split torus of a hyperbolic frame

Let `eᵢ, fᵢ` be a hyperbolic frame of a quadratic space `(V, Q)` with complement `W`
(`IsHypFrame`), and `hypTorus W e f` its split torus: `y eᵢ = tᵢ eᵢ`, `y fᵢ = tᵢ⁻¹ fᵢ`,
`y = 1` on `W`. This file records the parameters `tᵢ` as functions of `y`, and shows that on a
normed space the operator norm of `y` is comparable to `max_i max(‖tᵢ‖, ‖tᵢ‖⁻¹)`:

* `hypParam Q e f y i = polar(y eᵢ, fᵢ)`, the eigenvalue of `y` on `eᵢ`
  (`IsHypFrame.apply_e_of_mem_hypTorus`); it is multiplicative on the torus
  (`IsHypFrame.hypParam_mul`, `IsHypFrame.hypParam_inv`).
* `IsHypFrame.norm_hypParam_le`, `IsHypFrame.norm_inv_hypParam_le`: `‖tᵢ‖, ‖tᵢ⁻¹‖ ≤ ‖y‖`
  (`eᵢ`, `fᵢ` are eigenvectors).
* `IsHypFrame.exists_norm_le_of_mem_hypTorus`: `‖y‖ ≤ C (1 + B)` when all `‖tᵢ^{±1}‖ ≤ B`.

These are the estimates behind the standard fact that on a split torus the log-norm (BP §1.2) is
equivalent to `1 + max_i |log ‖tᵢ‖|`; they are used for the polynomial growth of `A_min`
(BP (6.7.12)).
-/

noncomputable section

open QuadraticMap

namespace GSpinGGP

section Param

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {W : Submodule K V} {n : ℕ} {e f : Fin n → V}

/-- The eigenvalue `polar(y eᵢ, fᵢ)` of `y` on `eᵢ`, for `y` in the torus of a hyperbolic frame
(`IsHypFrame.apply_e_of_mem_hypTorus`). -/
def hypParam (Q : QuadraticForm K V) (e f : Fin n → V) (y : V ≃ₗ[K] V) (i : Fin n) : K :=
  polar Q (y (e i)) (f i)

namespace IsHypFrame

/-- An element `y` of the frame torus scales `eᵢ` and `fᵢ` by `tᵢ = hypParam Q e f y i ≠ 0` and
`tᵢ⁻¹`. -/
theorem apply_e_of_mem_hypTorus (hF : IsHypFrame Q W e f) {y : V ≃ₗ[K] V}
    (hy : y ∈ hypTorus W e f) (i : Fin n) :
    y (e i) = hypParam Q e f y i • e i ∧ y (f i) = (hypParam Q e f y i)⁻¹ • f i ∧
      hypParam Q e f y i ≠ 0 := by
  obtain ⟨-, t, ht⟩ := hy
  have hp : hypParam Q e f y i = t i := by
    rw [hypParam, (ht i).1, polar_smul_left, hF.polar_ef_self, smul_eq_mul, mul_one]
  rw [hp, (ht i).1, (ht i).2]
  exact ⟨rfl, by rw [Units.val_inv_eq_inv_val], (t i).ne_zero⟩

/-- `hypParam` is multiplicative on the frame torus. -/
theorem hypParam_mul (hF : IsHypFrame Q W e f) {y y' : V ≃ₗ[K] V} (hy : y ∈ hypTorus W e f)
    (hy' : y' ∈ hypTorus W e f) (i : Fin n) :
    hypParam Q e f (y * y') i = hypParam Q e f y i * hypParam Q e f y' i := by
  have h := (hF.apply_e_of_mem_hypTorus hy i).1
  have h' := (hF.apply_e_of_mem_hypTorus hy' i).1
  rw [hypParam, LinearEquiv.mul_apply, h', map_smul, h, smul_smul, polar_smul_left,
    hF.polar_ef_self, smul_eq_mul, mul_one, mul_comm]

/-- `hypParam (y⁻¹) = (hypParam y)⁻¹` on the frame torus. -/
theorem hypParam_inv (hF : IsHypFrame Q W e f) {y : V ≃ₗ[K] V} (hy : y ∈ hypTorus W e f)
    (i : Fin n) : hypParam Q e f y⁻¹ i = (hypParam Q e f y i)⁻¹ := by
  have h := hF.hypParam_mul ((hypTorus W e f).inv_mem hy) hy i
  rw [inv_mul_cancel] at h
  have h1 : hypParam Q e f 1 i = 1 := hF.polar_ef_self i
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem e_ne_zero (hF : IsHypFrame Q W e f) (i : Fin n) : e i ≠ 0 :=
  hF.linearIndependent.ne_zero (Sum.inl i)

theorem f_ne_zero (hF : IsHypFrame Q W e f) (i : Fin n) : f i ≠ 0 :=
  hF.linearIndependent.ne_zero (Sum.inr i)

end IsHypFrame

end Param

section Norm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {Q : QuadraticForm 𝕜 E} {W : Submodule 𝕜 E} {n : ℕ} {e f : Fin n → E}

namespace IsHypFrame

/-- `‖tᵢ‖ ≤ ‖y‖` for `y` in the frame torus (`eᵢ` is an eigenvector). -/
theorem norm_hypParam_le (hF : IsHypFrame Q W e f) {y : E ≃ₗ[𝕜] E} (hy : y ∈ hypTorus W e f)
    (i : Fin n) :
    ‖hypParam Q e f y i‖ ≤ ‖LinearMap.toContinuousLinearMap (y : E →ₗ[𝕜] E)‖ := by
  have h := (LinearMap.toContinuousLinearMap (y : E →ₗ[𝕜] E)).le_opNorm (e i)
  rw [LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe,
    (hF.apply_e_of_mem_hypTorus hy i).1, norm_smul] at h
  exact le_of_mul_le_mul_right h (norm_pos_iff.2 (hF.e_ne_zero i))

/-- `‖tᵢ⁻¹‖ ≤ ‖y‖` for `y` in the frame torus (`fᵢ` is an eigenvector). -/
theorem norm_inv_hypParam_le (hF : IsHypFrame Q W e f) {y : E ≃ₗ[𝕜] E}
    (hy : y ∈ hypTorus W e f) (i : Fin n) :
    ‖(hypParam Q e f y i)⁻¹‖ ≤ ‖LinearMap.toContinuousLinearMap (y : E →ₗ[𝕜] E)‖ := by
  have h := (LinearMap.toContinuousLinearMap (y : E →ₗ[𝕜] E)).le_opNorm (f i)
  rw [LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe,
    (hF.apply_e_of_mem_hypTorus hy i).2.1, norm_smul] at h
  exact le_of_mul_le_mul_right h (norm_pos_iff.2 (hF.f_ne_zero i))

/-- **`‖y‖ ≪ 1 + max ‖tᵢ^{±1}‖` on the frame torus**: there is `C ≥ 0` such that
`‖y‖ ≤ C (1 + B)` whenever all `‖tᵢ‖, ‖tᵢ⁻¹‖ ≤ B` (`B ≥ 0`). By `apply_eq_of_diag`,
`y v = (v − Σ …) + Σ (tⱼ polar(v, fⱼ) eⱼ + tⱼ⁻¹ polar(v, eⱼ) fⱼ)`. -/
theorem exists_norm_le_of_mem_hypTorus (hF : IsHypFrame Q W e f) :
    ∃ C, 0 ≤ C ∧ ∀ y ∈ hypTorus W e f, ∀ B : ℝ, 0 ≤ B →
      (∀ i, ‖hypParam Q e f y i‖ ≤ B ∧ ‖(hypParam Q e f y i)⁻¹‖ ≤ B) →
      ‖LinearMap.toContinuousLinearMap (y : E →ₗ[𝕜] E)‖ ≤ C * (1 + B) := by
  -- the functionals `v ↦ polar(v, w)` are bounded
  set κ : E → ℝ := fun w => ‖LinearMap.toContinuousLinearMap ((polarBilin Q).flip w)‖
  have hκ : ∀ v w, ‖polar Q v w‖ ≤ κ w * ‖v‖ := fun v w => by
    have := (LinearMap.toContinuousLinearMap ((polarBilin Q).flip w)).le_opNorm v
    simpa [κ] using this
  have hκ0 : ∀ w, 0 ≤ κ w := fun w => norm_nonneg _
  set S : ℝ := ∑ j, (κ (f j) * ‖e j‖ + κ (e j) * ‖f j‖)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => by positivity
  refine ⟨1 + S, by positivity, fun y hy B hB hpB => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe]
  have hkW : ∀ w ∈ W, (y : E →ₗ[𝕜] E) w = (1 : 𝕜) • w := fun w hw => by
    rw [one_smul]; exact hy.1 w hw
  have hdiag := hF.apply_eq_of_diag (k := (y : E →ₗ[𝕜] E)) (a := hypParam Q e f y)
    (b := fun i => (hypParam Q e f y i)⁻¹) hkW (fun i => (hF.apply_e_of_mem_hypTorus hy i).1)
    (fun i => (hF.apply_e_of_mem_hypTorus hy i).2.1) v
  rw [LinearEquiv.coe_coe] at hdiag
  rw [hdiag, one_smul]
  have hfs : ‖frameSum Q e f v‖ ≤ S * ‖v‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul]
    calc ‖polar Q v (f j)‖ * ‖e j‖ + ‖polar Q v (e j)‖ * ‖f j‖
        ≤ κ (f j) * ‖v‖ * ‖e j‖ + κ (e j) * ‖v‖ * ‖f j‖ := by
          gcongr
          · exact hκ _ _
          · exact hκ _ _
      _ = (κ (f j) * ‖e j‖ + κ (e j) * ‖f j‖) * ‖v‖ := by ring
  have hsum : ‖∑ j, ((hypParam Q e f y j * polar Q v (f j)) • e j +
      ((hypParam Q e f y j)⁻¹ * polar Q v (e j)) • f j)‖ ≤ B * (S * ‖v‖) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, norm_mul, norm_mul]
    have h1 := (hpB j).1
    have h2 := (hpB j).2
    have h3 := hκ v (f j)
    have h4 := hκ v (e j)
    have hp1 : ‖hypParam Q e f y j‖ * ‖polar Q v (f j)‖ ≤ B * (κ (f j) * ‖v‖) :=
      mul_le_mul h1 h3 (norm_nonneg _) hB
    have hp2 : ‖(hypParam Q e f y j)⁻¹‖ * ‖polar Q v (e j)‖ ≤ B * (κ (e j) * ‖v‖) :=
      mul_le_mul h2 h4 (norm_nonneg _) hB
    calc ‖hypParam Q e f y j‖ * ‖polar Q v (f j)‖ * ‖e j‖ +
          ‖(hypParam Q e f y j)⁻¹‖ * ‖polar Q v (e j)‖ * ‖f j‖
        ≤ B * (κ (f j) * ‖v‖) * ‖e j‖ + B * (κ (e j) * ‖v‖) * ‖f j‖ :=
          add_le_add (mul_le_mul_of_nonneg_right hp1 (norm_nonneg _))
            (mul_le_mul_of_nonneg_right hp2 (norm_nonneg _))
      _ = B * ((κ (f j) * ‖e j‖ + κ (e j) * ‖f j‖) * ‖v‖) := by ring
  calc ‖v - frameSum Q e f v + ∑ j, ((hypParam Q e f y j * polar Q v (f j)) • e j +
        ((hypParam Q e f y j)⁻¹ * polar Q v (e j)) • f j)‖
      ≤ ‖v‖ + S * ‖v‖ + B * (S * ‖v‖) :=
        (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (by linarith)) hsum)
    _ ≤ (1 + S) * (1 + B) * ‖v‖ := by
        have := norm_nonneg v
        nlinarith [mul_nonneg hS0 this, mul_nonneg hB this]

end IsHypFrame

end Norm

end GSpinGGP
