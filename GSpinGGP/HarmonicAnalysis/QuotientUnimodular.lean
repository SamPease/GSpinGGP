/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Unimodularity of a quotient by a closed central subgroup

`isMulRightInvariant_haar_quotient_of_le_center`: if Haar measure on a locally compact, second
countable group `B` is right invariant and `A ≤ Z(B)` is closed, then Haar measure on `B/A` is
right invariant (used for `G(F)/A_G(F)`, Thesis §7.1).
`eq_smul_haar_of_isMulRightInvariant`: on a group whose Haar measure is right invariant, a right
invariant measure finite on compact sets is a multiple of `Measure.haar`.
-/

open MeasureTheory Topology Filter

noncomputable section

namespace GSpinGGP

section RightInvariance

variable {B : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B]
  [T2Space B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

/-- **Unimodularity passes to the quotient by a closed central subgroup** (used for
`G(F)/A_G(F)`, Thesis §7.1).  Let `B` be a locally compact, second countable group whose
Haar measure is right invariant, and `A ≤ Z(B)` closed.  Then Haar measure on `B/A` is right
invariant.

Proof: Mathlib's induced Haar measure on the extension `1 → A → B → B/A → 1` gives
`∫_B f = ∫_{B/A} ∫_A f(ḃ a) da dḃ` for `f ∈ C_c(B)`.  For `b ∈ B` the fibre integral of `f(· b)` at
`ḃ'` equals that of `f` at `ḃ' ḃ`, *because `A` is central* (`b' a b = b' b a`).  Right invariance on
`B` then gives `∫_{B/A} F(c ḃ) dc = ∫_{B/A} F(c) dc` for the fibre integral `F` of a nonnegative `f`
with `f(1) > 0`, so the modular character of `B/A` is `1`.  Centrality is essential: in general
`Δ_{B/A}(ḃ)` differs from `Δ_B(b)` by the modulus of conjugation by `b` on `A`. -/
theorem isMulRightInvariant_haar_quotient_of_le_center (A : Subgroup B) [A.Normal]
    (hA : IsClosed (A : Set B)) (hcent : A ≤ Subgroup.center B)
    [MeasurableSpace (B ⧸ A)] [BorelSpace (B ⧸ A)]
    [hB : (Measure.haar : Measure B).IsMulRightInvariant] :
    (Measure.haar : Measure (B ⧸ A)).IsMulRightInvariant := by
  have H := TopologicalGroup.IsSES.ofClosedSubgroup A hA
  have : LocallyCompactSpace A := hA.locallyCompactSpace
  set μA : Measure A := Measure.haar
  set μC : Measure (B ⧸ A) := Measure.haar
  set ν : Measure B := H.inducedMeasure μA μC
  have hν : ν = Measure.haarScalarFactor ν Measure.haar • (Measure.haar : Measure B) :=
    Measure.isMulLeftInvariant_eq_smul ν Measure.haar
  have hνR : ∀ (f : B → ℝ) (b : B), ∫ x, f (x * b) ∂ν = ∫ x, f x ∂ν := by
    intro f b
    rw [hν, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
      integral_mul_right_eq_self f b]
  -- a nonnegative test function with positive integral
  obtain ⟨f₀, f₀_comp, f₀_nonneg, f₀_one⟩ :
      ∃ f : C(B, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 1 ≠ 0 := exists_continuous_nonneg_pos 1
  let f : CompactlySupportedContinuousMap B ℝ := ⟨f₀, f₀_comp⟩
  set F := H.pushforward μA f with hF
  have hFint : ∫ c, F c ∂μC = ∫ x, f x ∂ν := by
    rw [TopologicalGroup.IsSES.integral_inducedMeasure]; rfl
  have hpos : 0 < ∫ x, f x ∂ν :=
    f₀.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero f₀_comp f₀_nonneg f₀_one
  refine ⟨fun g => ?_⟩
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g
  -- the right translate of `f` by `b`
  let fb : CompactlySupportedContinuousMap B ℝ :=
    ⟨⟨fun x => f₀ (x * b), f₀.continuous.comp (continuous_id.mul continuous_const)⟩,
      f₀_comp.comp_homeomorph (Homeomorph.mulRight b)⟩
  have hshift : ∀ c : B ⧸ A, H.pushforward μA fb c = F (c * (b : B ⧸ A)) := by
    intro c
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective c
    have e1 := TopologicalGroup.IsSES.pushforward_apply_apply H μA fb b'
    have e2 := TopologicalGroup.IsSES.pushforward_apply_apply H μA f (b' * b)
    change H.pushforward μA fb (QuotientGroup.mk' A b') = _
    rw [e1]
    have : ((b' : B ⧸ A) * (b : B ⧸ A)) = QuotientGroup.mk' A (b' * b) := rfl
    rw [this, e2]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp only [TopologicalGroup.IsSES.pullback_def]
    change f₀ (b' * (a : B) * b) = f₀ (b' * b * (a : B))
    have hc := Subgroup.mem_center_iff.mp (hcent a.2) b
    rw [mul_assoc, ← hc, mul_assoc]
  have hmapint : ∫ c, F c ∂(Measure.map (· * (b : B ⧸ A)) μC) = ∫ c, F c ∂μC := by
    rw [integral_map (f := fun c => F c) (measurable_mul_const _).aemeasurable
      F.continuous.aestronglyMeasurable]
    simp_rw [← hshift]
    rw [show ∫ c, H.pushforward μA fb c ∂μC = ∫ x, fb x ∂ν by
      rw [TopologicalGroup.IsSES.integral_inducedMeasure]; rfl]
    rw [hFint]
    exact hνR f₀ b
  have hfac := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * (b : B ⧸ A)) μC) μC
  have hne : ∫ c, F c ∂μC ≠ 0 := by rw [hFint]; exact hpos.ne'
  have hone : Measure.haarScalarFactor (Measure.map (· * (b : B ⧸ A)) μC) μC = 1 := by
    apply NNReal.coe_injective
    rw [Measure.haarScalarFactor_eq_integral_div _ _ F.continuous F.hasCompactSupport hne]
    change (∫ c, F c ∂(Measure.map (· * (b : B ⧸ A)) μC)) / (∫ c, F c ∂μC) = _
    rw [hmapint, div_self hne, NNReal.coe_one]
  rw [hfac, hone, one_smul]

end RightInvariance

open scoped NNReal ENNReal in
/-- A right invariant measure, finite on compact sets, on a unimodular group is a multiple of
`Measure.haar` (uniqueness of Haar measures, applied to the inverse measures). -/
theorem eq_smul_haar_of_isMulRightInvariant {Q : Type*} [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [LocallyCompactSpace Q] [SecondCountableTopology Q] [MeasurableSpace Q]
    [BorelSpace Q] (m : Measure Q) [m.IsMulRightInvariant] [IsFiniteMeasureOnCompacts m]
    [(Measure.haar : Measure Q).IsMulRightInvariant] :
    ∃ c : ℝ≥0, m = (c : ℝ≥0∞) • (Measure.haar : Measure Q) := by
  obtain ⟨s, e1⟩ : ∃ s : ℝ≥0, m.inv = s • (Measure.haar : Measure Q) :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul m.inv (Measure.haar : Measure Q)⟩
  obtain ⟨t, e2⟩ : ∃ t : ℝ≥0, (Measure.haar : Measure Q).inv = t • (Measure.haar : Measure Q) :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul (Measure.haar : Measure Q).inv
      (Measure.haar : Measure Q)⟩
  refine ⟨s * t, ?_⟩
  calc m = m.inv.inv := (Measure.inv_inv m).symm
    _ = _ := by
      rw [e1]
      change Measure.map Inv.inv (s • (Measure.haar : Measure Q)) = _
      rw [Measure.map_smul]
      · change s • (Measure.haar : Measure Q).inv = _
        rw [e2, smul_smul, ENNReal.smul_def]
      · exact measurable_inv.aemeasurable


end GSpinGGP
