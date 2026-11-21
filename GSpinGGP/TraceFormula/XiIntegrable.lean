/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.WaldspurgerXi
import GSpinGGP.TraceFormula.Analytic

/-!
# `∫_G Ξ^G(g)² σ_G(g)^{-D} dg < ∞` for every Iwasawa datum

Waldspurger 2003, Lemme II.1.5, is stated for a special maximal compact subgroup `K_s` and the
log-norm of a `K_s`-integral embedding (`exists_iwasawaPair_xi_sq_integrable`). This file
transfers it to `Ξ^G = IW.xiHC` for any Iwasawa datum `IW` (any compact open `K`) and to the
log-norm `σ_G = logNormG` of the project:

* `Ξ_K ≤ C Ξ_{K_s}` for the same minimal parabolic `P₀` (`IwasawaPair.exists_xi_le_mul_xi`);
* `1 + log entryMaxNorm b ≤ C' σ_G` (`logNorm_equiv_entryMaxNorm`);
* domination (`Integrable.mono'`), with `Ξ` and `σ_G` continuous.

This is BP Prop 1.5.1(v) (Astérisque 418, §1.5) for `G = GSpin(W) × GSpin(V)`.
-/

noncomputable section

open MeasureTheory

namespace GSpinGGP

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] {d : GGPData F}

namespace IwasawaDatum

/-- **`Ξ^G(g)² σ_G(g)^{-D}` is integrable on `G(F)` for some `D`** (Waldspurger 2003, Lemme
II.1.5; BP Prop 1.5.1(v)), for every Iwasawa datum. -/
theorem exists_integrable_xiHC_sq_mul_logNormG_inv_pow (IW : d.IwasawaDatum) :
    ∃ D : ℕ, Integrable (fun g : ↥d.G => IW.xiHC g ^ 2 * (d.logNormG g ^ D)⁻¹)
      (Measure.haar : Measure ↥d.G) := by
  obtain ⟨I, hIP, b, D, hint⟩ :=
    exists_iwasawaPair_xi_sq_integrable d IW.FW IW.FV IW.fullW IW.fullV
  obtain ⟨C, hC, hle⟩ := IW.toIwasawaPair.exists_xi_le_mul_xi I hIP.symm
  obtain ⟨C', hC', hσ⟩ := logNorm_equiv_entryMaxNorm b d.G
  refine ⟨D, (hint.const_mul (C ^ 2 * C' ^ D)).mono' ?_ (Filter.Eventually.of_forall fun g => ?_)⟩
  · exact ((IW.toIwasawaPair.continuous_xi.pow 2).mul
      ((d.continuous_logNormG.pow D).inv₀ fun g =>
        (pow_pos (zero_lt_one.trans_le (d.one_le_logNormG g)) D).ne')).aestronglyMeasurable
  · have hx0 : 0 ≤ IW.xiHC g := IW.toIwasawaPair.xi_nonneg g
    have hσ1 : 1 ≤ d.logNormG g := d.one_le_logNormG g
    have hE1 : 1 ≤ 1 + Real.log (entryMaxNorm b d.G g) := by
      linarith [Real.log_nonneg (one_le_entryMaxNorm b d.G g)]
    have hxle : IW.xiHC g ^ 2 ≤ C ^ 2 * I.xi g ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hx0 (hle g) 2
    have hEle : (1 + Real.log (entryMaxNorm b d.G g)) ^ D ≤ C' ^ D * d.logNormG g ^ D := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (hσ g).2 D
    have hinv : (d.logNormG g ^ D)⁻¹ ≤ C' ^ D * ((1 + Real.log (entryMaxNorm b d.G g)) ^ D)⁻¹ := by
      have hp : 0 < (1 + Real.log (entryMaxNorm b d.G g)) ^ D := pow_pos (by linarith) D
      have hq : 0 < d.logNormG g ^ D := pow_pos (by linarith) D
      calc (d.logNormG g ^ D)⁻¹
          = (d.logNormG g ^ D)⁻¹ * ((1 + Real.log (entryMaxNorm b d.G g)) ^ D *
              ((1 + Real.log (entryMaxNorm b d.G g)) ^ D)⁻¹) := by
            rw [mul_inv_cancel₀ hp.ne', mul_one]
        _ ≤ (d.logNormG g ^ D)⁻¹ * (C' ^ D * d.logNormG g ^ D *
              ((1 + Real.log (entryMaxNorm b d.G g)) ^ D)⁻¹) := by gcongr
        _ = C' ^ D * ((1 + Real.log (entryMaxNorm b d.G g)) ^ D)⁻¹ := by
            field_simp
    have hpos : 0 ≤ IW.xiHC g ^ 2 * (d.logNormG g ^ D)⁻¹ := by positivity
    rw [Real.norm_of_nonneg hpos]
    calc IW.xiHC g ^ 2 * (d.logNormG g ^ D)⁻¹
        ≤ (C ^ 2 * I.xi g ^ 2) * (C' ^ D * ((1 + Real.log (entryMaxNorm b d.G g)) ^ D)⁻¹) :=
          mul_le_mul hxle hinv (by positivity) (by positivity)
      _ = C ^ 2 * C' ^ D * (I.xi g ^ 2 * ((1 + Real.log (entryMaxNorm b d.G g)) ^ D)⁻¹) := by
          ring

end IwasawaDatum

end GGPData

end GSpinGGP
