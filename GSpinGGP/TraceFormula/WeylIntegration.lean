/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.WeylIntegration

/-!
# The Weyl integration formula for every family of Haar measures on the tori

BP §1.7 (p. 32) states the formula for its particular Haar measures `dt` on the maximal tori; the
literature axiom `weyl_integration_exists` (`Literature/WeylIntegration.lean`) gives it for some
family of Haar measures.  The right side does not depend on that family
(`gammaIntegral_weylIntegrand_eq`, `TraceFormula/GammaG.lean`: uniqueness of Haar measure on each
torus, and `dg/(c μ) = c⁻¹ (dg/μ)`), so the formula holds for every family.

## Main statements

* `GGPData.weyl_integration`.
-/

noncomputable section

open MeasureTheory

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

/-- **The Weyl integration formula** (BP §1.7, p. 32; Harish-Chandra): for `f ∈ C_c^∞(G(F))`,
`∫_{G(F)} f(g) dg = ∫_{Γ(G)} D^G(x)^{1/2} J_G(x, f) dx
  = Σ_{T ∈ 𝒯(G)} |W(G,T)|⁻¹ ∫_{T(F)} D^G(t)^{1/2} J_G(t, f) dt`,
for every family `μ` of Haar measures on the maximal tori (`J_G(t, ·)` taken for `dg / μ T`).
From the literature axiom `weyl_integration_exists` (the formula for some such family; BP states
it without proof) and the independence of the right side from the family
(`gammaIntegral_weylIntegrand_eq`). -/
theorem weyl_integration (μ : ∀ T : Subgroup ↥d.G, Measure ↥T)
    (hμ : ∀ T : d.MaxTorus, (μ T.1).IsHaarMeasure) (f : ↥d.G → ℂ)
    (hf : f ∈ testFunctions ↥d.G) :
    ∫ g, f g ∂Measure.haar = d.gammaIntegral μ (d.weylIntegrand μ f) := by
  obtain ⟨μ₀, hμ₀, hW, -⟩ := weyl_integration_exists d
  rw [hW f hf, d.gammaIntegral_weylIntegrand_eq μ₀ μ hμ₀ hμ f]

end GGPData

end GSpinGGP
