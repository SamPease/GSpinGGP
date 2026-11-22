/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalGroups

/-!
# The value group of a `p`-adic field is cyclic

For a `PAdicField F` (complete, locally compact, ultrametric, nontrivially normed), the norms of
the nonzero elements form a cyclic subgroup `‖ϖ‖^ℤ` of `ℝ_{>0}`: the open unit ball is compact
(closed in the compact closed ball, the norm being ultrametric), so the norm attains a largest
value `‖ϖ‖ < 1` on it, and then every `‖x‖`, `x ≠ 0`, is a power of `‖ϖ‖` (Euclidean division of
`log ‖x‖` by `log ‖ϖ‖`).  Equivalently, `log ‖F^×‖ = ℤ · log ‖ϖ‖` is discrete in `ℝ`.

## Main results

* `exists_norm_lt_one_isGreatest`: some `ϖ` with `0 < ‖ϖ‖ < 1` has the largest norm `< 1`.
* `exists_norm_eq_zpow`: then `‖x‖ = ‖ϖ‖^n`, `n ∈ ℤ`, for every `x ≠ 0`.
* `exists_log_norm_mem_zmultiples`: some `ℓ > 0` has `log ‖x‖ ∈ ℤ ℓ` for every `x ≠ 0`.
-/

noncomputable section

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F]

/-- **A uniformizer**: some `ϖ` with `0 < ‖ϖ‖ < 1` has the largest norm `< 1`.  The open unit ball
is closed (the norm is ultrametric) in the compact closed unit ball, so the norm attains its
supremum on it. -/
theorem exists_norm_lt_one_isGreatest [PAdicField F] :
    ∃ ϖ : F, 0 < ‖ϖ‖ ∧ ‖ϖ‖ < 1 ∧ ∀ x : F, ‖x‖ < 1 → ‖x‖ ≤ ‖ϖ‖ := by
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have hc : IsCompact (Metric.ball (0 : F) 1) :=
    (isCompact_closedBall (0 : F) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball 0 1)
      Metric.ball_subset_closedBall
  obtain ⟨ϖ, hϖ, hmax⟩ := hc.exists_isMaxOn ⟨0, Metric.mem_ball_self one_pos⟩
    continuous_norm.continuousOn
  have hle : ∀ x : F, ‖x‖ < 1 → ‖x‖ ≤ ‖ϖ‖ := fun x hx =>
    hmax (show x ∈ Metric.ball (0 : F) 1 by simpa using hx)
  obtain ⟨τ, hτ0, hτ1⟩ := NormedField.exists_norm_lt_one F
  exact ⟨ϖ, hτ0.trans_le (hle τ hτ1), by simpa using hϖ, hle⟩

/-- **The value group is `‖ϖ‖^ℤ`**: if `‖ϖ‖` is the largest norm `< 1`, every nonzero `x` has
`‖x‖ = ‖ϖ‖^n` for some `n ∈ ℤ`. -/
theorem exists_norm_eq_zpow {ϖ : F} (h0 : 0 < ‖ϖ‖) (h1 : ‖ϖ‖ < 1)
    (hmax : ∀ x : F, ‖x‖ < 1 → ‖x‖ ≤ ‖ϖ‖) {x : F} (hx : x ≠ 0) : ∃ n : ℤ, ‖x‖ = ‖ϖ‖ ^ n := by
  set a := ‖ϖ‖
  obtain ⟨k, hk1, hk2⟩ := exists_mem_Ico_zpow (norm_pos_iff.2 hx) ((one_lt_inv₀ h0).2 h1)
  rw [inv_zpow', zpow_neg] at hk1 hk2
  have hak : 0 < a ^ k := zpow_pos h0 k
  -- `y = ‖ϖ^k x‖ = a^k ‖x‖` lies in `[1, a⁻¹)`
  set y := a ^ k * ‖x‖ with hy
  have hy1 : 1 ≤ y := by
    have := mul_le_mul_of_nonneg_left hk1 hak.le
    rwa [mul_inv_cancel₀ hak.ne'] at this
  have hy2 : y < a⁻¹ := by
    have := mul_lt_mul_of_pos_left hk2 hak
    rwa [zpow_add_one₀ h0.ne', mul_inv, ← mul_assoc, mul_inv_cancel₀ hak.ne', one_mul] at this
  have hyeq : y = 1 := by
    by_contra hne
    have hlt : 1 < y := lt_of_le_of_ne hy1 (Ne.symm hne)
    have hpos : 0 < y := one_pos.trans hlt
    have hz : ‖(ϖ ^ k * x)⁻¹‖ = y⁻¹ := by rw [norm_inv, norm_mul, norm_zpow]
    have := hmax _ (by rw [hz]; exact inv_lt_one_of_one_lt₀ hlt)
    rw [hz] at this
    have : a⁻¹ ≤ y := (inv_le_comm₀ hpos h0).1 this
    exact absurd hy2 (not_lt.2 this)
  refine ⟨-k, ?_⟩
  rw [zpow_neg]
  exact eq_inv_of_mul_eq_one_right hyeq

/-- **`log ‖F^×‖` is discrete**: there is `ℓ > 0` with `log ‖x‖ ∈ ℤ ℓ` for every `x ≠ 0`
(`ℓ = −log ‖ϖ‖`). -/
theorem exists_log_norm_mem_zmultiples [PAdicField F] :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ x : F, x ≠ 0 → Real.log ‖x‖ ∈ AddSubgroup.zmultiples ℓ := by
  obtain ⟨ϖ, h0, h1, hmax⟩ := exists_norm_lt_one_isGreatest (F := F)
  refine ⟨-Real.log ‖ϖ‖, neg_pos.2 (Real.log_neg h0 h1), fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := exists_norm_eq_zpow h0 h1 hmax hx
  refine ⟨-n, ?_⟩
  change (-n) • (-Real.log ‖ϖ‖) = Real.log ‖x‖
  rw [hn, Real.log_zpow, zsmul_eq_mul]
  push_cast
  ring

end GSpinGGP
