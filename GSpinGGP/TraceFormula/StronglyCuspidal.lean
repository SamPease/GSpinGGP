/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.TraceFormula
import GSpinGGP.TraceFormula.Basic

/-!
# The quasi-character of a strongly cuspidal function, and elliptic isolation

Two statements built from Beuzart-Plessis, Astérisque 418, Ch. 5. The first, `bp_thetaF_exists`,
composes Thm 5.5.1(ii) (the literature axiom `bp_integrable_kernel_scusp`) with Thm 5.5.1(iv), the
Weyl integration formula and Prop 5.6.1(ii), which are not statable verbatim here and form the
`sorry` theorem `bp_thetaF_represents`. The second, `bp_scusp_surj_ell`, adapts Cor 5.7.2(i), which
assumes a compact centre; it is a `sorry` theorem.
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
  = Thesis Thm 4.7.1(iv), stated in BP without proof (BP p. 116 defers it, with (ii), to a paper in
  preparation; see `bp_integrable_kernel_scusp`).  For `p`-adic `F`, its equality with the spectral
  side (Thm 5.5.1(iv) = (v)) is proved in J. Arthur, *On elliptic tempered characters*, Acta Math. 171
  (1993), Thm 4.2 and Cor 4.3, pp. 104–105, for cuspidal test functions (strongly cuspidal implies
  Arthur's cuspidality `f_L = 0`).
* Weyl integration formula `∫_G φ dg = ∫_{Γ(G)} D^G(x)^{1/2} J_G(x,φ) dx`, with the measure on
  `Γ(G)` of BP §1.7 = Thesis §2.5 and `J_G` the normalized orbital integral of Thesis §2.6; it
  turns the right-hand side into `∫_G θ_{f₀} f' dg` with constant `1` (BP §1.7 states the formula
  as an exact identity; BP uses this step in the proof of Prop 5.6.1(ii), p. 121). It holds when
  `A_G(F)\G(F)` carries `dg/d_c a`, `d_c a` giving the maximal compact subgroup of `A_G(F)` volume 1.
  The constant is irrelevant here anyway, see below.
* `θ_{f₀}` is a quasi-character: BP Prop 5.6.1(ii) = Thesis Prop 4.8.1(ii); in particular it is
  locally constant on `G_reg(F)` and locally integrable (`(D^G)^{1/2} θ` is locally bounded, and
  `(D^G)^{-1/2}` is locally integrable by Thesis (2.5.1)).  For `p`-adic `F` these properties of `θ_f`
  are also proved in Waldspurger, *Une formule intégrale reliée à la conjecture locale de
  Gross–Prasad*, Compositio Math. 146 (2010), §5.3 (Lemme) and §5.9 (Corollaire).

Normalization-insensitivity: rescaling the Haar measure on `G(F)` by `a > 0` and that on
`G(F)/A_G(F)` by `b > 0` multiplies the right-hand side by `ab` and the left-hand side by `a`, so
the statement holds for `θ = b·θ_{f₀}`; a positive constant does not affect the quasi-character
property. Hence the statement does not depend on any measure normalization, and the existential `θ`
is BP's `θ_{f₀}` up to a positive constant fixed by `Measure.haar` on `G(F)/A_G(F)`.

**Status: `sorry`, not a literature axiom.** `θ_{f₀}` is defined in BP §5.2 (after Waldspurger 2010,
§5.3) through the weighted orbital integrals `J_{M(x)}(x, f₀)`, which are not defined in this
development (nor are `Γ(G)` with its measure and `J_G`), so Thm 5.5.1(iv) and Prop 5.6.1(ii) cannot be
stated verbatim here; this existential composite is not itself a statement of the source. -/
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

/-- **(c) Elliptic isolation, untwisted, `p`-adic** (BP Astérisque 418, Cor 5.7.2(i) = Thesis
Cor 4.8.3(i), in the form given by its proof for a group whose split centre `A_G` need not be
trivial).  There is a subset `Ω ⊆ G(F)` which is open and closed, conjugation invariant and
`A_G(F)`-stable, contains the elliptic regular set, and is compact modulo conjugation and
`A_G(F)`, such that every quasi-character `θ₀` whose support (on `G_reg(F)`) is compact modulo
conjugation *inside* `Ω` (the space `QC_c(Ω)` of BP §4.1) is `θ_{f₀}` on `G_reg(F)` for a strongly
cuspidal `f₀ ∈ C_c^∞(G(F))` supported in `Ω` (`S_scusp(Ω)`; `S = C_c^∞` for `p`-adic `F`).
Here "`θ_{f₀}` on `G_reg(F)`" is written, as in `bp_thetaF_exists`, as: some locally integrable `θ`,
continuous on `G_reg(F)` and equal to `θ₀` there, represents the orbital pairing of `f₀`.

**Relation to the source; what is adapted (not literal).**
* BP Cor 5.7.2 assumes that the centre of `G(F)` is compact; here `A_G(F)` is a nontrivial split
  torus.  BP's proof of (i) is local: for an elliptic `x`, a `G`-good open neighbourhood `Ω_x`
  relatively compact modulo conjugation, `Ω = Ω_x^G`, it combines semisimple descent
  (BP Prop 4.1.1(ii),(iii) = Thesis Prop 4.1.1.1), density of `θ(S_scusp(ω_x))` in `QC_c(ω_x)` on
  `𝔤_x` (BP Prop 5.6.1(i) = Thesis Prop 4.8.1(i); `G_x` has an elliptic maximal torus since `x` is
  elliptic) and the lift `f ↦ f̃` of BP Prop 5.7.1 = Thesis Prop 4.8.2; none of these assumes a
  compact centre.  The compact-centre hypothesis is used only to cover `G(F)_ell` by finitely many
  `Ω_{x_i}^G`.  Here `G(F)_ell` is compact modulo conjugation *and `A_G(F)`*, so finitely many
  `Ω_{x_i}^G` cover it modulo `A_G(F)`, and `Ω = A_G(F) · ⋃ Ω_{x_i}^G` (an `A_G(F)`-translate of a
  `G`-good neighbourhood of an elliptic point is one of the translated point).  A `θ₀ ∈ QC_c(Ω)`
  (support compact modulo conjugation, *not* modulo `A_G`) meets finitely many translates
  `a Ω_{x_i}^G`; an invariant partition of unity (BP Prop 3.1.1(ii)) reduces to one of them.
* Surjectivity: in the `p`-adic case `QC_c(Ω)` carries its finest locally convex topology, in which
  every subspace is closed, so "dense image" is "onto" (BP's own parenthesis in Cor 5.7.2(i)).
* Open and closed: BP's `Ω` is open.  For `p`-adic `F` the `Ω_{x_i}` may be taken compact open,
  and then `Ω_{x_i}^G` is also closed (unverified detail: it is the union of finitely many of the
  sets `π⁻¹(π(Ω'))`, `π` the characteristic-polynomial map, separating the rational classes in a
  stable class near `x_i`).  Closedness is what makes `1_Ω θ` a quasi-character.
* Not the `G/A_G` form: BP applied literally to `Ḡ = G/A_G` (compact centre) only treats
  `A_G(F)`-invariant data, i.e. trivial central character.  A character `χ` of `A_G(F)` with
  `χ(-1) ≠ 1` does not extend to `G(F)` (`-1 ∈ Spin(F)`), so twisting by an extension is not
  available, and the `χ`-equivariant statement is derived instead from this untwisted one on `G(F)`
  (cutoff `κ` and `P_χ`, `TraceFormula/Scusp.lean`).

Normalization-insensitivity: the conclusion is linear in `f₀`; rescaling either Haar measure
rescales `θ_{f₀}` by a positive constant (see `bp_thetaF_exists`), which is absorbed into `f₀`.
`p`-adic case only (`PAdicField F`).

Consistent at `toyD`, `hypVData`, `hypWData`; adapted, not verified.  Unverified: (a) closedness of `Ω` (proposed route:
the preimage under the characteristic-polynomial map of a small compact open, `A_G(F)`-stable
neighbourhood of the image of `G(F)_ell`, refined so that every point lies in a `G`-good
neighbourhood of an elliptic point where BP Prop 5.6.1(i), 5.7.1 apply); (b) the splitting of
rational classes inside a stable neighbourhood; (c) the `A_G(F)`-translate partition-of-unity step
(BP Prop 3.1.1(ii), number unchecked).  The hypothesis quantifies the quasi-character condition
over every `ψ`, stronger than BP's single notion; this only weakens the axiom.

**Status: `sorry`, not a literature axiom** (the statement is not verbatim in a source). Adapted: BP
Cor 5.7.2 assumes that the centre of `G(F)` is compact. The ingredients (BP Prop 5.6.1(i), Prop
5.7.1, Prop 3.1.1(ii), Prop 4.1.1(vi)) do not, and the adapting argument is sketched above. -/
theorem bp_scusp_surj_ell (d : GGPData F) :
    ∃ Ω : Set ↥d.G, IsOpen Ω ∧ IsClosed Ω ∧ (∀ x g : ↥d.G, g ∈ Ω → x * g * x⁻¹ ∈ Ω) ∧
      (∀ (a : ↥d.AG) (g : ↥d.G), g ∈ Ω → (a : ↥d.G) * g ∈ Ω) ∧
      ellipticRegularSet d.G d.lie d.AG ⊆ Ω ∧
      (∃ C : Set ↥d.G, IsCompact C ∧
        ∀ g ∈ Ω, ∃ (a : ↥d.AG) (x c : ↥d.G), c ∈ C ∧ g = (a : ↥d.G) * (x * c * x⁻¹)) ∧
      ∀ θ₀ : ↥d.G → ℂ, (∀ ψ : NontrivialAddChar F, IsQuasiCharacter d.G d.lie d.bilin ψ θ₀) →
        (∃ C₀ : Set ↥d.G, IsCompact C₀ ∧ C₀ ⊆ Ω ∧
          ∀ g ∈ regularSet d.G d.lie, θ₀ g ≠ 0 → ∃ x c : ↥d.G, c ∈ C₀ ∧ g = x * c * x⁻¹) →
        ∃ f₀ : ↥d.G → ℂ, f₀ ∈ testFunctions ↥d.G ∧
          (∀ (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV), d.IsProperFlagPair FW FV →
            ∀ p ∈ d.whittB FW FV, ∫ u : ↥(d.whittU FW FV), f₀ (p * u) ∂Measure.haar = 0) ∧
          Function.support f₀ ⊆ Ω ∧
          ∃ θ : ↥d.G → ℂ, LocallyIntegrable θ Measure.haar ∧
            ContinuousOn θ (regularSet d.G d.lie) ∧ Set.EqOn θ θ₀ (regularSet d.G d.lie) ∧
            ∀ f' ∈ testFunctions ↥d.G,
              ∫ g : ↥d.G, θ g * f' g ∂Measure.haar =
                ∫ x : ↥d.G ⧸ d.AG,
                  (∫ g : ↥d.G, f₀ ((Quotient.out x)⁻¹ * g * Quotient.out x) * f' g ∂Measure.haar)
                  ∂Measure.haar := by
  sorry

end LitTF

end GSpinGGP
