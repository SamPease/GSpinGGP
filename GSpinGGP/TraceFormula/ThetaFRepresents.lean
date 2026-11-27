/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.ThetaFGlobal

/-!
# The quasi-character of a strongly cuspidal function represents the orbital pairing

`bp_thetaF_represents` restates `isThetaF_thetaF_of_cusp` (`TraceFormula/ThetaFGlobal.lean`) for
`Measure.haar` on `G(F)/A_G(F)`, with witness `dcScaleAG⁻¹ · θ_f`; `bp_thetaF_exists` adds the
integrability of the kernel (BP Thm 5.5.1(ii), the literature axiom `bp_integrable_kernel_scusp`).
-/

open MeasureTheory Topology Filter

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

namespace LitTF

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **(b′) The quasi-character of a strongly cuspidal function represents the orbital pairing** (the
part of `bp_thetaF_exists` that is not the integrability of the kernel).
Let `f₀ ∈ C_c^∞(G(F))` be strongly cuspidal (as in `bp_integrable_kernel_scusp`). Then there is a
function `θ` on `G(F)` such that
* `θ` is locally integrable and continuous (= locally constant) on `G_reg(F)`;
* `θ` is a quasi-character (for every nontrivial `ψ`; the notion does not depend on `ψ`, which
  only normalizes the functions `ĵ(O,·)` in which the germs are expanded);
* for every `f' ∈ C_c^∞(G(F))`, `∫_{G(F)} θ f' dg = ∫_{G(F)/A_G(F)} K(x,x) dx`, where
  `K(x,x) = ∫_{G(F)} f₀(x⁻¹gx) f'(g) dg` and `G(F)/A_G(F)` carries `Measure.haar`.

The integrand `K(x,x)` is evaluated at the representative `Quotient.out x`; it does not depend on
the representative because `A_G` is central (`K(ax, ax) = K(x, x)`).

"Proper" is `GGPData.IsProperFlagPair`, i.e. `whittB FW FV ≠ ⊤` (the thesis's definition).

Proof: `θ = c⁻¹ θ_f` with `θ_f = thetaF d f₀` (Beuzart-Plessis' formula, BP §5.2) and
`c = dcScaleAG` (`measGmodAG = c · Measure.haar`): `θ_f` represents the orbital pairing for
`measGmodAG` and is a quasi-character (`isThetaF_thetaF_of_cusp`: BP Thm 5.5.1(iv), the Weyl
integration formula, Waldspurger 2010 §5.3 Lemme and §5.9 Corollaire), and a multiple of a
quasi-character is one. -/
theorem bp_thetaF_represents (d : GGPData F) (f₀ : ↥d.G → ℂ) (hf₀ : f₀ ∈ testFunctions ↥d.G)
    (hcusp : ∀ (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV), d.IsProperFlagPair FW FV →
      ∀ p ∈ d.whittB FW FV,
        ∫ u : ↥(d.whittU FW FV), f₀ (p * u) ∂Measure.haar = 0) :
    ∃ θ : ↥d.G → ℂ, LocallyIntegrable θ Measure.haar ∧
      ContinuousOn θ (regularSet d.G d.lie) ∧
      (∀ ψ : NontrivialAddChar F, IsQuasiCharacter d.G d.lie d.bilin ψ θ) ∧
      ∀ f' ∈ testFunctions ↥d.G,
        ∫ g : ↥d.G, θ g * f' g ∂Measure.haar =
          ∫ x : ↥d.G ⧸ d.AG,
            (∫ g : ↥d.G, f₀ ((Quotient.out x)⁻¹ * g * Quotient.out x) * f' g ∂Measure.haar)
            ∂Measure.haar := by
  obtain ⟨hθ, hqc⟩ := isThetaF_thetaF_of_cusp hf₀ hcusp
  refine ⟨(d.dcScaleAG.toReal : ℂ)⁻¹ • thetaF d f₀, hθ.1.smul _, hθ.2.1.const_smul _,
    fun ψ => isQuasiCharacter_smul d ψ _ (hqc ψ), fun f' hf' => ?_⟩
  exact haar_pairing_of_isThetaF d hθ f' hf'

/-- **(b) The quasi-character of a strongly cuspidal function represents the orbital pairing,
and the kernel is integrable.** For `f₀ ∈ C_c^∞(G(F))` strongly cuspidal there is a locally
integrable `θ`, continuous on `G_reg(F)` and a quasi-character, such that for every
`f' ∈ C_c^∞(G(F))` the function `x ↦ ∫_{G(F)} f₀(x⁻¹gx) f'(g) dg` is integrable on `G(F)/A_G(F)` and
`∫_{G(F)} θ f' dg = ∫_{G(F)/A_G(F)} ∫_{G(F)} f₀(x⁻¹gx) f'(g) dg dx` (BP Thm 5.5.1(ii),(iv), the Weyl
integration formula and Prop 5.6.1(ii); Thesis Thm 4.7.1, Prop 4.8.1).  Integrability is the
literature axiom `bp_integrable_kernel_scusp` (BP Thm 5.5.1(ii)); the rest is
`bp_thetaF_represents` (proved from `isThetaF_thetaF_of_cusp`).

The `χ`-equivariant form of this statement is proved in this development
(`TraceFormula/ThetaF.lean`) and is *not* assumed here. -/
theorem bp_thetaF_exists (d : GGPData F) (f₀ : ↥d.G → ℂ) (hf₀ : f₀ ∈ testFunctions ↥d.G)
    (hcusp : ∀ (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV), d.IsProperFlagPair FW FV →
      ∀ p ∈ d.whittB FW FV,
        ∫ u : ↥(d.whittU FW FV), f₀ (p * u) ∂Measure.haar = 0) :
    ∃ θ : ↥d.G → ℂ, LocallyIntegrable θ Measure.haar ∧
      ContinuousOn θ (regularSet d.G d.lie) ∧
      (∀ ψ : NontrivialAddChar F, IsQuasiCharacter d.G d.lie d.bilin ψ θ) ∧
      ∀ f' ∈ testFunctions ↥d.G,
        Integrable (fun x : ↥d.G ⧸ d.AG =>
            ∫ g : ↥d.G, f₀ ((Quotient.out x)⁻¹ * g * Quotient.out x) * f' g ∂Measure.haar)
          Measure.haar ∧
        ∫ g : ↥d.G, θ g * f' g ∂Measure.haar =
          ∫ x : ↥d.G ⧸ d.AG,
            (∫ g : ↥d.G, f₀ ((Quotient.out x)⁻¹ * g * Quotient.out x) * f' g ∂Measure.haar)
            ∂Measure.haar := by
  obtain ⟨θ, hli, hcont, hqc, hrep⟩ := bp_thetaF_represents d f₀ hf₀ hcusp
  exact ⟨θ, hli, hcont, hqc, fun f' hf' =>
    ⟨bp_integrable_kernel_scusp d f₀ hf₀ hcusp f' hf', hrep f' hf'⟩⟩

end LitTF

end GSpinGGP
