/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.BPThetaF

/-!
# The geometric expansion of `J^A` for every family of Haar measures on the tori

BP Thm 5.5.1(iv) (Astérisque 418, p. 116) is stated for BP's measures `dt` on the maximal tori;
the literature axiom `bp_thm_5_5_1_iv` (`Literature/BPThetaF.lean`) gives it, with absolute
convergence, for some family of Haar measures.  The right side, its integrability on each torus and
its absolute summability do not depend on that family (`TraceFormula/BPThetaF.lean`), so the
expansion holds for every family.

## Main statements

* `GGPData.jA_eq_gammaIntegral`.
-/

noncomputable section

open MeasureTheory

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

/-- **The geometric expansion of `J^A`** (BP Thm 5.5.1(iv), p. 116; stated without proof there):
for `f ∈ C_c^∞(G(F))` strongly cuspidal, `θ = θ_f` on `G_reg(F)` (`IsBPThetaF`),
`f' ∈ C_c^∞(G(F))` and every family `μ` of Haar measures on the maximal tori,
`J^A(f, f') = Σ_{T ∈ 𝒯(G)} |W(G,T)|⁻¹ ∫_{T(F)} D^G(t)^{1/2} θ(t) J_G(t, f') dμ_T(t)`, with
`J_G(t, ·)` for `dg/μ_T`, each torus integral and the sum absolutely convergent.  From the axiom
`bp_thm_5_5_1_iv` and the independence of the right side from the family
(`gammaIntegral_thetaWeylIntegrand_eq`, `integrable_thetaWeylIntegrand_iff`,
`summable_norm_thetaWeylIntegrand_iff`). -/
theorem jA_eq_gammaIntegral (μ : ∀ T : Subgroup ↥d.G, Measure ↥T)
    (hμ : ∀ T : d.MaxTorus, (μ T.1).IsHaarMeasure) {f : ↥d.G → ℂ} (hf : f ∈ testFunctions ↥d.G)
    (hcusp : IsStronglyCuspidalInline d f) {θ : ↥d.G → ℂ} (hθ : d.IsBPThetaF f θ) {f' : ↥d.G → ℂ}
    (hf' : f' ∈ testFunctions ↥d.G) :
    (∀ c : d.MaxTorusClass, Integrable
        (fun t : ↥(Quot.out c).1 => d.thetaWeylIntegrand μ θ f' (Quot.out c).1 t)
        (μ (Quot.out c).1)) ∧
    Summable (fun c : d.MaxTorusClass => ((weylCardG d (Quot.out c).1 : ℝ))⁻¹ *
        ∫ t, ‖d.thetaWeylIntegrand μ θ f' (Quot.out c).1 t‖ ∂μ (Quot.out c).1) ∧
    d.jA f f' = d.gammaIntegral μ (d.thetaWeylIntegrand μ θ f') := by
  obtain ⟨μ₀, hμ₀, hBP⟩ := bp_thm_5_5_1_iv d
  obtain ⟨hint, hsum, heq⟩ := hBP f hf hcusp θ hθ f' hf'
  refine ⟨fun c => ?_, (d.summable_norm_thetaWeylIntegrand_iff μ₀ μ hμ₀ hμ θ f').2 hsum, ?_⟩
  · have := hμ (Quot.out c)
    have := hμ₀ (Quot.out c)
    exact (integrable_thetaWeylIntegrand_iff μ₀ μ (Quot.out c) θ f').2 (hint c)
  · rw [heq, d.gammaIntegral_thetaWeylIntegrand_eq μ₀ μ hμ₀ hμ θ f']

end GGPData

end GSpinGGP
