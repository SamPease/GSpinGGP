/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.StronglyCuspidal

/-!
# The quasi-character of a strongly cuspidal function represents the orbital pairing

`bp_thetaF_exists` composes Beuzart-Plessis, Astérisque 418, Thm 5.5.1(ii) (the literature axiom
`bp_integrable_kernel_scusp`) with Thm 5.5.1(iv), the Weyl integration formula and Prop 5.6.1(ii),
which are not statable verbatim here and form the `sorry` theorem `bp_thetaF_represents`.
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
  `K(x,x) = ∫_{G(F)} f₀(x⁻¹gx) f'(g) dg` (integrable by `bp_integrable_kernel_scusp`).

The integrand `K(x,x)` is evaluated at the representative `Quotient.out x`; it does not depend on
the representative because `A_G` is central (`K(ax, ax) = K(x, x)`).

"Proper" is `GGPData.IsProperFlagPair`, i.e. `whittB FW FV ≠ ⊤` (the thesis's definition). With a
nonempty-flag encoding a hyperbolic-plane factor would give a "proper" pair with `whittB = G` and
`whittU = 1`, making `hcusp` force `f₀ = 0` (the statement would then be trivially true).

Sources and derivation (`θ` is `θ_f` of BP / the Thesis, up to a positive constant):
* Geometric expansion `J^A(f₀,f') = ∫_{Γ(G)} D^G(x)^{1/2} θ_{f₀}(x) J_G(x,f') dx`: BP Thm 5.5.1(iv)
  = Thesis Thm 4.7.1(iv), stated in BP without proof (BP p. 116 defers it, with (ii), to
  its reference [18], in preparation; see `bp_integrable_kernel_scusp`).  For `p`-adic `F`,
  its equality with the spectral side (Thm 5.5.1(iv) = (v)) is proved in J. Arthur, *On
  elliptic tempered characters*, Acta Math. 171 (1993), Thm 4.2 (p. 102) and Cor 4.3 (pp. 104–105),
  for cuspidal test functions (strongly cuspidal implies Arthur's cuspidality `f_L = 0`).
* Weyl integration formula `∫_G φ dg = ∫_{Γ(G)} D^G(x)^{1/2} J_G(x,φ) dx`, with the measure on
  `Γ(G)` of BP §1.7 = Thesis §2.5 and `J_G` the normalized orbital integral of Thesis §2.6; it
  turns the right-hand side into `∫_G θ_{f₀} f' dg` with constant `1` (BP §1.7 states the formula
  as an exact identity; BP uses this step in the proof of Prop 5.6.1(ii), p. 121). It holds when
  `A_G(F)\G(F)` carries `dg/d_c a`, `d_c a` giving the maximal compact subgroup of `A_G(F)`
  volume 1. The constant is irrelevant here anyway, see below.
* `θ_{f₀}` is a quasi-character: BP Prop 5.6.1(ii) = Thesis Prop 4.8.1(ii); in particular it is
  locally constant on `G_reg(F)` and locally integrable (`(D^G)^{1/2} θ` is locally bounded, and
  `(D^G)^{-1/2}` is locally integrable by Thesis (2.5.1)).  For `p`-adic `F` these properties
  of `θ_f` are also proved in Waldspurger, *Une formule intégrale reliée à la conjecture locale
  de Gross–Prasad*, Compositio Math. 146 (2010), §5.3 (Lemme) and §5.9 (Corollaire).

Normalization-insensitivity: rescaling the Haar measure on `G(F)` by `a > 0` and that on
`G(F)/A_G(F)` by `b > 0` multiplies the right-hand side by `ab` and the left-hand side by `a`, so
the statement holds for `θ = b·θ_{f₀}`; a positive constant does not affect the quasi-character
property. Hence the statement does not depend on any measure normalization, and the existential `θ`
is BP's `θ_{f₀}` up to a positive constant fixed by `Measure.haar` on `G(F)/A_G(F)`.

**Status: `sorry`, not a literature axiom.** `θ_{f₀}` is defined in BP §5.2 (after Waldspurger
2010, §5.3) through the weighted orbital integrals `J_{M(x)}(x, f₀)`, which are not defined in
this development (nor are `Γ(G)` with its measure and `J_G`), so Thm 5.5.1(iv) and
Prop 5.6.1(ii) cannot be stated verbatim here; this existential composite is not itself a
statement of the source. -/
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
  sorry

/-- **(b) The quasi-character of a strongly cuspidal function represents the orbital pairing,
and the kernel is integrable.** For `f₀ ∈ C_c^∞(G(F))` strongly cuspidal there is a locally
integrable `θ`, continuous on `G_reg(F)` and a quasi-character, such that for every
`f' ∈ C_c^∞(G(F))` the function `x ↦ ∫_{G(F)} f₀(x⁻¹gx) f'(g) dg` is integrable on `G(F)/A_G(F)` and
`∫_{G(F)} θ f' dg = ∫_{G(F)/A_G(F)} ∫_{G(F)} f₀(x⁻¹gx) f'(g) dg dx` (BP Thm 5.5.1(ii),(iv), the Weyl
integration formula and Prop 5.6.1(ii); Thesis Thm 4.7.1, Prop 4.8.1).  Integrability is the
literature axiom `bp_integrable_kernel_scusp` (BP Thm 5.5.1(ii)); the rest is
`bp_thetaF_represents`.

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
