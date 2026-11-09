/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.TraceFormula
import GSpinGGP.TraceFormula.Basic

/-!
# The quasi-character of a strongly cuspidal function, and elliptic isolation

Two statements built from Beuzart-Plessis, Astérisque 418, Ch. 5. They are not verbatim there:
the first composes Thm 5.5.1(ii),(iv), the Weyl integration formula and Prop 5.6.1(ii); the
second adapts Cor 5.7.2(i), which assumes a compact centre. Both are `sorry` theorems.
-/

open MeasureTheory Topology Filter

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

namespace LitTF

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **(b) The quasi-character of a strongly cuspidal function represents the orbital pairing.**
Let `f₀ ∈ C_c^∞(G(F))` be strongly cuspidal: for every proper parabolic subgroup
`P = P_{F_W} × P_{F_V}` with unipotent radical `U = N_{F_W} × N_{F_V}` (`d.whittB`, `d.whittU` for a
proper flag pair; Thesis §5.1.2: every parabolic subgroup of `G` is of this form) and every
`p ∈ P(F)`, `∫_{U(F)} f₀(pu) du = 0` (Thesis §4.5, `f^P = 0`; quantifying over `p ∈ P` rather
than `m ∈ M` is equivalent by left invariance of `du`, and the factor `δ_P(m)^{1/2}` does not
affect vanishing). Then there is a function `θ` on `G(F)` such that
* `θ` is locally integrable and continuous (= locally constant) on `G_reg(F)`;
* `θ` is a quasi-character (for every nontrivial `ψ`; the notion does not depend on `ψ`, which
  only normalizes the functions `ĵ(O,·)` in which the germs are expanded);
* for every `f' ∈ C_c^∞(G(F))`, the function `x ↦ K(x,x) = ∫_{G(F)} f₀(x⁻¹gx) f'(g) dg` on
  `G(F)/A_G(F)` is integrable and `∫_{G(F)} θ f' dg = ∫_{G(F)/A_G(F)} K(x,x) dx`.

The integrand `K(x,x)` is evaluated at the representative `Quotient.out x`; it does not depend on
the representative because `A_G` is central (`K(ax, ax) = K(x, x)`).

"Proper" is `GGPData.IsProperFlagPair`, i.e. `whittB FW FV ≠ ⊤` (the thesis's definition). With a
nonempty-flag encoding a hyperbolic-plane factor would give a "proper" pair with `whittB = G` and
`whittU = 1`, making `hcusp` force `f₀ = 0` (the axiom would then be trivially true).

The `χ`-equivariant form of this statement is proved in this development
(`TraceFormula/ThetaF.lean`) and is *not* assumed here.

Sources and derivation (`θ` is `θ_f` of BP / the Thesis, up to a positive constant):
* Integrability of `x ↦ K^A_{f₀,f'}(x,x)` on `A_G(F)\G(F)`: BP Astérisque 418, Thm 5.5.1(ii) =
  Thesis Thm 4.7.1(ii), applied to `C_c^∞ ⊂ 𝒞(G(F))`. This is BP's *untwisted* statement:
  `f₀` has compact support on `G(F)` itself (not only modulo `A_G(F)`), so the inner integral is
  over a compact set.
* Geometric expansion `J^A(f₀,f') = ∫_{Γ(G)} D^G(x)^{1/2} θ_{f₀}(x) J_G(x,f') dx`: BP Thm 5.5.1(iv)
  = Thesis Thm 4.7.1(iv) (Arthur, Publ. IHÉS 73 (1991); Waldspurger, Crelle 465 (1995)).
* Weyl integration formula `∫_G φ dg = ∫_{Γ(G)} D^G(x)^{1/2} J_G(x,φ) dx`, with the measure on
  `Γ(G)` of BP §1.7 = Thesis §2.5 and `J_G` the normalized orbital integral of Thesis §2.6; it
  turns the right-hand side into `∫_G θ_{f₀} f' dg` with constant `1` (BP §1.7 states the formula
  as an exact identity; BP uses this step in the proof of Prop 5.6.1(ii); checked by hand). It holds when `A_G(F)\G(F)` carries `dg/d_c a`, `d_c a` giving the maximal compact
  subgroup of `A_G(F)` volume 1 — the only reading under which Thm 5.5.1(iv) holds. The constant is
  irrelevant here anyway, see below.
* `θ_{f₀}` is a quasi-character: BP Prop 5.6.1(ii) = Thesis Prop 4.8.1(ii); in particular it is
  locally constant on `G_reg(F)` and locally integrable (`(D^G)^{1/2} θ` is locally bounded, and
  `(D^G)^{-1/2}` is locally integrable by Thesis (2.5.1)).

Normalization-insensitivity: rescaling the Haar measure on `G(F)` by `a > 0` and that on
`G(F)/A_G(F)` by `b > 0` multiplies the right-hand side by `ab` and the left-hand side by `a`, so
the statement holds for `θ = b·θ_{f₀}`; a positive constant does not affect the quasi-character
property. Hence the axiom does not depend on any measure normalization ,
and the existential `θ` is BP's `θ_{f₀}` up to a positive constant fixed by `Measure.haar` on
`G(F)/A_G(F)`.

**Status: `sorry`, not a literature axiom** (the statement is not verbatim in a source). A composite
of BP Thm 5.5.1(ii),(iv), the Weyl integration formula (BP §1.7) and BP Prop 5.6.1(ii), all stated
for any connected reductive group. For `p`-adic `F` the properties of `θ_f` are also Waldspurger
2010, §5.3 (Lemme) and §5.9 (Corollaire). -/
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
  sorry

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
* `p`-adic ingredients without a centre hypothesis, which can replace BP's density statements:
  Waldspurger, *Une formule intégrale reliée à la conjecture locale de Gross–Prasad*, Compositio
  Math. 146 (2010), Prop. 6.4 (arXiv:0902.1875v1, p. 31: every quasi-character on `𝔤(F)` compactly
  supported modulo conjugation is `θ_f` for a strongly cuspidal `f ∈ C_c^∞(𝔤(F))`) and Lemme 6.2 (p. 28:
  lift from `𝔤_x` to `G` at an elliptic `x`, assuming `Z_G(x)(F)`-invariance, automatic here since
  `Z_G(x) = G_x` for `GSpin`, whose derived group is simply connected).
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
