/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalGroups

/-!
# Local properties of the exponential `expA`

* `expA_add_of_commute`: `e^{X+Y} = e^X e^Y` for commuting `X, Y` near `0`;
* `exists_localInverse_exp`: in a complete normed algebra over a nontrivially normed field of
  characteristic `0` in which the exponential series has positive radius (any `p`-adic or real
  Banach algebra), `exp` has a continuous local inverse `L` at `1`, injective domain included;
* `exp_units_conj_of_mem_ball`: `exp(g x g⁻¹) = g exp(x) g⁻¹` without a `ℚ`-normed structure;
* `commute_of_commute_exp`: on an injectivity domain of `exp`, `Y` commutes with everything
  commuting with `exp Y` (so the local inverse `L(c)` commutes with the commutant of `c`).
-/

noncomputable section

open Topology Filter

namespace GSpinGGP

variable (F : Type*) [NontriviallyNormedField F] [PAdicField F] {A : Type*} [Ring A] [Algebra F A]
  [Module.Finite F A] [TopologicalSpace A] [IsModuleTopology F A]

/-- **`e^{X+Y} = e^X e^Y` for commuting `X, Y` near `0`** (Mathlib's
`exp_add_of_commute_of_mem_ball`, transported along `lmulPi`). -/
lemma expA_add_of_commute :
    ∃ U ∈ 𝓝 (0 : A), ∀ X ∈ U, ∀ Y ∈ U, Commute X Y →
      expA F (X + Y) = expA F X * expA F Y := by
  have := isTopologicalRing_of_moduleTopology F A
  obtain ⟨U, hU, -, h⟩ := expA_aux F (A := A)
  obtain ⟨V, hV, hVU⟩ := exists_nhds_zero_half hU
  refine ⟨V ∩ U, inter_mem hV hU, fun X hX Y hY hXY => ?_⟩
  obtain ⟨hbX, -, heX⟩ := h X hX.2
  obtain ⟨hbY, -, heY⟩ := h Y hY.2
  obtain ⟨-, -, heXY⟩ := h (X + Y) (hVU X hX.1 Y hY.1)
  have hc : Commute (lmulPi F X) (lmulPi F Y) := by
    show lmulPi F X * lmulPi F Y = lmulPi F Y * lmulPi F X
    rw [← lmulPi_mul, ← lmulPi_mul, hXY.eq]
  have hadd := NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := F) hc hbX hbY
  have hl : lmulPi F (X + Y) = lmulPi F X + lmulPi F Y := map_add (lmulPiₗ F) X Y
  have key : lmulPi F (expA F (X + Y)) = lmulPi F (expA F X * expA F Y) := by
    rw [heXY, hl, hadd, lmulPi_mul, heX, heY]
  calc expA F (X + Y) = lmulPiInv F (lmulPi F (expA F (X + Y))) := (lmulPiInv_lmulPi F _).symm
    _ = expA F X * expA F Y := by rw [key, lmulPiInv_lmulPi]

section LocalInverse

open NormedSpace

variable {𝕂 E : Type*} [NontriviallyNormedField 𝕂] [CharZero 𝕂] [NormedRing E] [NormedAlgebra 𝕂 E]
  [CompleteSpace E]

/-- `exp(g x g⁻¹) = g exp(x) g⁻¹` when the exponential series of `x` converges. -/
theorem exp_units_conj_of_mem_ball (g : Eˣ) {x : E}
    (hx : x ∈ Metric.eball (0 : E) (expSeries 𝕂 E).radius) :
    exp ((g : E) * x * ↑g⁻¹) = (g : E) * exp x * ↑g⁻¹ := by
  have h := expSeries_hasSum_exp_of_mem_ball' (𝕂 := 𝕂) x hx
  have hc : Continuous fun a : E => (g : E) * a * ↑g⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have h' := h.map ((AddMonoidHom.mulLeft (g : E)).comp (AddMonoidHom.mulRight (↑g⁻¹ : E))) (by
    simpa [Function.comp_def, mul_assoc] using hc)
  have e : ∀ n : ℕ, (AddMonoidHom.mulLeft (g : E)).comp (AddMonoidHom.mulRight (↑g⁻¹ : E))
      (((n.factorial : 𝕂)⁻¹) • x ^ n) = ((n.factorial : 𝕂)⁻¹) • ((g : E) * x * ↑g⁻¹) ^ n := by
    intro n
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
    rw [Units.conj_pow]
    simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
  simp only [Function.comp_def, e] at h'
  calc exp ((g : E) * x * ↑g⁻¹) = ∑' n : ℕ, ((n.factorial : 𝕂)⁻¹) • ((g : E) * x * ↑g⁻¹) ^ n :=
        congrFun (exp_eq_tsum 𝕂) _
    _ = _ := h'.tsum_eq
    _ = (g : E) * exp x * ↑g⁻¹ := by simp [mul_assoc]

/-- **Local inverse of `exp` at `1`** (inverse function theorem): there are open `s ∋ 0` (inside the
ball of convergence) and `t ∋ 1` and `L : E → E`, continuous at `1` with `L 1 = 0`, such that
`L(c) ∈ s` and `exp(L c) = c` for `c ∈ t`, and `exp` is injective on `s`. -/
theorem exists_localInverse_exp (hr : 0 < (expSeries 𝕂 E).radius) :
    ∃ s t : Set E, IsOpen s ∧ (0 : E) ∈ s ∧ s ⊆ Metric.eball (0 : E) (expSeries 𝕂 E).radius ∧
      IsOpen t ∧ (1 : E) ∈ t ∧ Set.InjOn exp s ∧ ∃ L : E → E, ContinuousAt L 1 ∧ L 1 = 0 ∧
        ∀ c ∈ t, L c ∈ s ∧ exp (L c) = c := by
  have h := hasStrictFDerivAt_exp_zero_of_radius_pos hr
  have h' : HasStrictFDerivAt (exp : E → E) ((ContinuousLinearEquiv.refl 𝕂 E : E ≃L[𝕂] E) :
      E →L[𝕂] E) 0 := by
    convert h using 1
    exact ContinuousLinearMap.ext fun x => rfl
  set φ := h'.toOpenPartialHomeomorph exp
  have h0 : (0 : E) ∈ φ.source := h'.mem_toOpenPartialHomeomorph_source
  have h1 : (1 : E) ∈ φ.target := by
    have := h'.image_mem_toOpenPartialHomeomorph_target
    rwa [exp_zero] at this
  have hφ0 : φ.symm 1 = 0 := by
    have := φ.left_inv h0
    rwa [show φ 0 = 1 from exp_zero] at this
  set s := φ.source ∩ Metric.eball (0 : E) (expSeries 𝕂 E).radius
  have hs : IsOpen s := φ.open_source.inter Metric.isOpen_eball
  set t := φ.target ∩ φ.symm ⁻¹' s
  refine ⟨s, t, hs, ⟨h0, Metric.mem_eball_self hr⟩, Set.inter_subset_right,
    φ.isOpen_inter_preimage_symm hs, ⟨h1, by
      show φ.symm 1 ∈ s
      rw [hφ0]
      exact ⟨h0, Metric.mem_eball_self hr⟩⟩, φ.injOn.mono Set.inter_subset_left, φ.symm,
    φ.continuousAt_symm h1, hφ0, fun c hc => ⟨hc.2, φ.right_inv hc.1⟩⟩

/-- **The local inverse of `exp` commutes with the commutant**: if `exp` is injective on the open
set `s` (inside the ball of convergence), `Y ∈ s` and `z` commutes with `exp Y`, then `z` commutes
with `Y`.  Conjugate by `1 + εz` for small `ε ≠ 0`: it fixes `exp Y` and keeps `Y` in `s`. -/
theorem commute_of_commute_exp {s : Set E} (hs : IsOpen s)
    (hsr : s ⊆ Metric.eball (0 : E) (expSeries 𝕂 E).radius) (hinj : Set.InjOn exp s) {Y : E}
    (hY : Y ∈ s) {z : E} (hz : Commute z (exp Y)) : Commute z Y := by
  -- `ε ↦ 1 + εz` is a unit near `0`, and conjugation by it is continuous at `0`
  have hlim : Tendsto (fun ε : 𝕂 => ε • z) (𝓝[≠] 0) (𝓝 0) := by
    have : Continuous fun ε : 𝕂 => ε • z := continuous_id.smul continuous_const
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ ε in 𝓝[≠] (0 : 𝕂), ‖-(ε • z)‖ < 1 := by
    have := hlim.eventually (Metric.ball_mem_nhds (0 : E) one_pos)
    filter_upwards [this] with ε hε
    simpa using hε
  -- the conjugate of `Y` tends to `Y`
  have hconj : Tendsto (fun ε : 𝕂 => (1 + ε • z) * Y * Ring.inverse (1 + ε • z)) (𝓝[≠] 0) (𝓝 Y) := by
    have h1 : Tendsto (fun ε : 𝕂 => 1 + ε • z) (𝓝[≠] 0) (𝓝 1) := by
      simpa using tendsto_const_nhds.add hlim
    have h2 : Tendsto (fun ε : 𝕂 => Ring.inverse (1 + ε • z)) (𝓝[≠] 0) (𝓝 1) := by
      have := (NormedRing.inverse_continuousAt (1 : Eˣ)).tendsto.comp h1
      simpa [Function.comp_def] using this
    simpa using (h1.mul tendsto_const_nhds).mul h2
  obtain ⟨ε, ⟨hε1, hεs⟩, hε0⟩ := ((hsmall.and (hconj.eventually (hs.mem_nhds hY))).and
    self_mem_nhdsWithin).exists
  set g : Eˣ := Units.oneSub (-(ε • z)) hε1 with hg
  have hgv : (g : E) = 1 + ε • z := by simp [hg, Units.oneSub, sub_neg_eq_add]
  have hginv : Ring.inverse (1 + ε • z) = ↑g⁻¹ := by rw [← hgv, Ring.inverse_unit]
  rw [hginv, ← hgv] at hεs
  have hgc : Commute (g : E) (exp Y) := by rw [hgv]; exact (Commute.one_left _).add_left (hz.smul_left ε)
  have hexp : exp ((g : E) * Y * ↑g⁻¹) = exp Y := by
    rw [exp_units_conj_of_mem_ball g (hsr hY), hgc.eq, mul_assoc, Units.mul_inv, mul_one]
  have hYeq := hinj hεs hY hexp
  have h3 : (g : E) * Y = Y * g := by
    calc (g : E) * Y = (g : E) * Y * ↑g⁻¹ * g := by rw [mul_assoc _ (↑g⁻¹ : E), Units.inv_mul, mul_one]
      _ = Y * g := by rw [hYeq]
  rw [hgv, add_mul, mul_add, one_mul, mul_one, add_right_inj, smul_mul_assoc, mul_smul_comm] at h3
  exact smul_right_injective _ hε0 h3

end LocalInverse

end GSpinGGP
