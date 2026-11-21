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
assumes a compact centre; it is proved in `TraceFormula/Scusp.lean` (covering and gluing) from the
two `sorry` theorems here: `exists_isCompact_ellRegSet_modConjAG` (relative compactness of the
elliptic regular set modulo conjugation and `A_G(F)`) and `exists_scuspSurjOn_nhd_ell` (local
surjectivity of `f ↦ θ_f` near an elliptic point; Waldspurger 2010, Prop. 6.4 and Lemme 6.2,
adapted).
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

/-- **Surjectivity of `f ↦ θ_f` onto `QC_c(Ω)`** (BP §4.1, §5.7; `p`-adic, untwisted on `G(F)`):
every quasi-character `θ₀` (for every `ψ`) whose support on `G_reg(F)` is contained in `C₀^{G(F)}`
for a compact `C₀ ⊆ Ω` is `θ_{f₀}` on `G_reg(F)` for a strongly cuspidal `f₀ ∈ C_c^∞(G(F))`
supported in `Ω`.  "`θ_{f₀}` on `G_reg(F)`" is written as in `bp_thetaF_exists`: some locally
integrable `θ`, continuous on `G_reg(F)` and equal to `θ₀` there, represents the orbital pairing of
`f₀`.  This is the last clause of `bp_scusp_surj_ell` (`TraceFormula/Scusp.lean`) for a given `Ω`. -/
def ScuspSurjOn (d : GGPData F) (Ω : Set ↥d.G) : Prop :=
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
              ∂Measure.haar

/-- **The elliptic regular set is relatively compact modulo conjugation and `A_G(F)`**
(`p`-adic; standard, no exact reference located): there is a compact `K` contained in the closure
of `G(F)_{ell,reg}` such that every elliptic regular `g` is `a · x c x⁻¹` with `a ∈ A_G(F)`,
`x ∈ G(F)`, `c ∈ K`.

Proof sketch (not formalized): there are finitely many `G(F)`-conjugacy classes of maximal
`F`-tori of `G` (`F` `p`-adic of characteristic `0`); for an elliptic maximal torus `T`,
`T(F)/A_G(F)` is compact, so `T(F) ⊆ A_G(F) K_T` with `K_T` compact; every elliptic regular `g` is
conjugate into `T(F)` for one of the finitely many representatives `T`.  Then
`K = (⋃_T K_T) ∩ cl(G_ell,reg(F))` works: `G_ell,reg(F)` is stable under conjugation and under
`A_G(F)` (`conj_mem_ellRegSet`, `mul_mem_ellRegSet_of_mem_AG`), so the `c = x⁻¹ a⁻¹ g x ∈ K_T`
obtained is again elliptic regular.

**Status: `sorry`.**  Used, with `exists_scuspSurjOn_nhd_ell`, to prove `bp_scusp_surj_ell`
(`TraceFormula/Scusp.lean`), where only the covering argument is done. -/
theorem exists_isCompact_ellRegSet_modConjAG (d : GGPData F) :
    ∃ K : Set ↥d.G, IsCompact K ∧ K ⊆ closure (ellipticRegularSet d.G d.lie d.AG) ∧
      ∀ g ∈ ellipticRegularSet d.G d.lie d.AG,
        ∃ (a : ↥d.AG) (x c : ↥d.G), c ∈ K ∧ g = (a : ↥d.G) * (x * c * x⁻¹) := by
  sorry

/-- **Local surjectivity near an elliptic point** (`p`-adic): every `g` in the closure of
`G(F)_{ell,reg}` lies in a set `U` that is open and closed, conjugation invariant and
`A_G(F)`-stable, compact modulo conjugation and `A_G(F)`, and on which `f ↦ θ_f` is onto the
quasi-characters with support compact modulo conjugation inside `U` (`ScuspSurjOn`).

**Literature (Waldspurger, *Une formule intégrale reliée à la conjecture locale de Gross–Prasad*,
Compositio Math. 146 (2010); page numbers of arXiv:0902.1875v1).**  Sections 1–6 there are written
for an arbitrary connected reductive group `G` over a `p`-adic field of characteristic `0` (§1.1,
p. 5), so they apply to `G = GSpin(W) × GSpin(V)` and to its centralizers `G_x`:
* §3.1 (pp. 13–14): good neighbourhoods `ω` of `0` in `𝔤_x(F)` (`waldspurger_goodNbhd`);
* Prop. 6.4 (p. 31): every quasi-character on `𝔤(F)` with support compact modulo conjugation is
  `θ_f` for a very cuspidal `f ∈ C_c^∞(𝔤(F))` (applied to `𝔤_x`);
* Lemme 6.2 (p. 28): for `x` semisimple *elliptic* (`A_{G_x} = A_G`), a good `ω`, and a very
  cuspidal `φ ∈ C_c^∞(𝔤_x(F))` supported in `ω` with `θ_φ` invariant under `Z_G(x)(F)`, there is a
  very cuspidal `f ∈ C_c^∞(G(F))` with `θ_{f,x,ω} = θ_φ` (the proof gives `c·θ_φ`, `c > 0`, absorbed
  into `f`).  `Z_G(x) = G_x` for `GSpin` (simply connected derived group), so the invariance holds.

**Adapting argument (own; not formalized).**  Let `x` be the semisimple part of `g`.  It is elliptic:
an elliptic regular `y` near `g` is conjugate into `x exp(ω)`, its centralizer torus `T` lies in
`G_x`, so `A_{G_x} ⊆ T` and `T/A_G` anisotropic give `A_{G_x} = A_G`.  Take a compact open good `ω`
and `U = A_G(F) · (x exp ω)^{G(F)}` (it contains `g`, since `ω` is open, `G_x`-invariant and contains
`0`, so contains the nilpotent part of `log(x⁻¹ g)`).  The set `(x exp ω)^{G(F)}` is a `G`-domain (open, closed and
invariant, W1 p. 6), compact modulo conjugation (W1 §3.1, p. 14; the axiom `waldspurger_goodNbhd`).
`U` is closed because the translates `a (x exp ω)^{G(F)}` form a locally finite family (via the
Harish-Chandra map `H_G`, as for the `A_G`-cutoff of `TraceFormula/ThetaF.lean`); overlapping
translates are handled by taking differences of invariant clopen sets.  A `θ₀` as in `ScuspSurjOn d U` meets finitely many translates; on each, its descent
to `𝔤_x(F)` (W1 §4.1) is a quasi-character with compact support modulo conjugation, which is `θ_φ`
(Prop. 6.4); `φ` is cut down to `1_ω φ` (very cuspidal, `ω` being a `G_x`-domain) so that it is
supported in `ω`, lifted to `f` (Lemme 6.2) and translated by `a`; summing gives `f₀`.  Finally W1's
`θ_f` (defined by weighted orbital integrals, W1 §5.3) represents the orbital pairing (BP Thm
5.5.1(iv) with the Weyl integration formula, as in `bp_thetaF_represents`).

**Why not axioms.**  W1's `θ_f`, `θ_{f,x,ω}` and very cuspidal functions on `𝔤_x(F)` (with the
parabolic subgroups of `G_x`) are not defined in this development, so W1 Prop. 6.4 and Lemme 6.2
cannot be stated verbatim; written with the orbital-pairing characterization of `θ_f` they would be
derived statements (W1 + BP Thm 5.5.1(iv)/5.5.2(ii) + Weyl formula).

**Status: `sorry`.**  With `exists_isCompact_ellRegSet_modConjAG` it gives `bp_scusp_surj_ell`
(`TraceFormula/Scusp.lean`: finite subcover and gluing). -/
theorem exists_scuspSurjOn_nhd_ell (d : GGPData F) {g : ↥d.G}
    (hg : g ∈ closure (ellipticRegularSet d.G d.lie d.AG)) :
    ∃ U : Set ↥d.G, IsOpen U ∧ IsClosed U ∧ (∀ x y : ↥d.G, y ∈ U → x * y * x⁻¹ ∈ U) ∧
      (∀ (a : ↥d.AG) (y : ↥d.G), y ∈ U → (a : ↥d.G) * y ∈ U) ∧ g ∈ U ∧
      (∃ C : Set ↥d.G, IsCompact C ∧
        ∀ y ∈ U, ∃ (a : ↥d.AG) (x c : ↥d.G), c ∈ C ∧ y = (a : ↥d.G) * (x * c * x⁻¹)) ∧
      ScuspSurjOn d U := by
  sorry


end LitTF

end GSpinGGP
