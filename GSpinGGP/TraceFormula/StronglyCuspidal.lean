/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.TraceFormula
import GSpinGGP.TraceFormula.Basic

/-!
# Strongly cuspidal functions: elliptic isolation and the inline cuspidality condition

`bp_scusp_surj_ell` adapts Beuzart-Plessis, Astérisque 418, Cor 5.7.2(i), which assumes a compact
centre; it is proved in `TraceFormula/Scusp.lean` (covering and gluing) from the two `sorry`
theorems here: `exists_isCompact_ellRegSet_modConjAG` (relative compactness of the elliptic regular
set modulo conjugation and `A_G(F)`) and `exists_scuspSurjOn_nhd_ell` (local surjectivity of
`f ↦ θ_f` near an elliptic point; Waldspurger 2010, Prop. 6.4 and Lemme 6.2, adapted).

`IsStronglyCuspidalInline` is strong cuspidality in the form used by `bp_thetaF_exists`
(`TraceFormula/ThetaFRepresents.lean`), and `isStronglyCuspidal_iff_inline` identifies it with
`IsStronglyCuspidal` on `C_c^∞(G(F))`.
-/

open MeasureTheory Topology Filter

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

namespace LitTF

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **Surjectivity of `f ↦ θ_f` onto `QC_c(Ω)`** (BP §4.1, §5.7; `p`-adic, untwisted on `G(F)`):
every quasi-character `θ₀` (for every `ψ`) whose support on `G_reg(F)` is contained in `C₀^{G(F)}`
for a compact `C₀ ⊆ Ω` is `θ_{f₀}` on `G_reg(F)` for a strongly cuspidal `f₀ ∈ C_c^∞(G(F))`
supported in `Ω`.  "`θ_{f₀}` on `G_reg(F)`" is written as in `bp_thetaF_exists`: some locally
integrable `θ`, continuous on `G_reg(F)` and equal to `θ₀` there, represents the orbital pairing of
`f₀`.  This is the last clause of `bp_scusp_surj_ell` (`TraceFormula/Scusp.lean`) for a given
`Ω`. -/
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

**Adapting argument (own; not formalized).**  Let `x` be the semisimple part of `g`.  It is
elliptic: an elliptic regular `y` near `g` is conjugate into `x exp(ω)`, its centralizer torus `T`
lies in `G_x`, so `A_{G_x} ⊆ T` and `T/A_G` anisotropic give `A_{G_x} = A_G`.  Take a compact open
good `ω` and `U = A_G(F) · (x exp ω)^{G(F)}` (it contains `g`, since `ω` is open, `G_x`-invariant
and contains `0`, so contains the nilpotent part of `log(x⁻¹ g)`).  The set `Ω₀ = (x exp ω)^{G(F)}`
is a `G`-domain, compact modulo conjugation (W1 §3.1, p. 14; the axiom `waldspurger_goodNbhd`); a
`G`-domain is open, closed and invariant (definition, W1 p. 6).  `U` is closed: the Harish-Chandra
map `H_G` is locally constant and conjugation invariant, so it takes finitely many values on `Ω₀`;
writing `A_G(F)` as
the compact group `A_c = A_G(F) ∩ ker H_G` times a lattice of representatives `a_λ`,
`U = ⋃_λ a_λ (A_c · Ω₀)`, where each `A_c · Ω₀` is closed (`A_c` compact, `Ω₀` closed) and the
family is locally finite (`H_G` separates the pieces up to a finite overlap).  Overlapping
translates are handled by taking differences of invariant clopen sets.  A `θ₀` as in
`ScuspSurjOn d U` meets finitely many translates; on each, its descent to `𝔤_x(F)` (W1 §4.1) is a
quasi-character with compact support modulo conjugation, which is `θ_φ` (Prop. 6.4); `φ` is cut
down to `1_ω φ` (very cuspidal: `ω` is a `G_x`-domain, W1 §5.1 and §6.1) so that it is supported
in `ω`, lifted to `f` (Lemme 6.2) and translated by `a`; summing gives `f₀`.  Finally W1's `θ_f`
(defined by weighted orbital integrals, W1 §5.3) represents the orbital pairing (BP Thm
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

/-! ## Strong cuspidality in inline form -/

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

/-- Strong cuspidality in the form used by `bp_thetaF_exists` (Thesis §4.5; BP §5.1): for every proper
flag pair and `p ∈ P(F)`, `∫_{U(F)} f(p u) du = 0` (no integrability clause). -/
def IsStronglyCuspidalInline (f : ↥d.G → ℂ) : Prop :=
  ∀ (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV), d.IsProperFlagPair FW FV →
    ∀ p ∈ d.whittB FW FV, ∫ u : ↥(d.whittU FW FV), f (p * u) ∂Measure.haar = 0

/-- `IsStronglyCuspidal` implies the inline form of `bp_thetaF_exists` (drop integrability). -/
theorem IsStronglyCuspidal.inline {f : ↥d.G → ℂ} (hf : IsStronglyCuspidal d f) :
    IsStronglyCuspidalInline d f :=
  fun FW FV h p hp => (hf FW FV h p hp).2

/-- For `f ∈ C_c^∞(G(F))`, `u ↦ f(p u)` is integrable on `U(F)` (it is continuous with compact
support, `U(F)` being closed). -/
theorem integrable_parabolicU_of_testFunctions {f : ↥d.G → ℂ} (hf : f ∈ testFunctions ↥d.G)
    (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) (p : ↥d.G) :
    Integrable (fun u : ↥(d.whittU FW FV) => f (p * u)) Measure.haar := by
  have hemb : IsClosedEmbedding (fun u : ↥(d.whittU FW FV) => p * (u : ↥d.G)) :=
    (Homeomorph.mulLeft p).isClosedEmbedding.comp
      (d.isClosed_whittU FW FV).isClosedEmbedding_subtypeVal
  exact (hf.1.continuous.comp hemb.continuous).integrable_of_hasCompactSupport
    (hf.2.comp_isClosedEmbedding hemb)

/-- **Bridge to `bp_thetaF_exists`**: on `C_c^∞(G(F))` the two forms of
strong cuspidality (Thesis §4.5) agree. -/
theorem isStronglyCuspidal_iff_inline {f : ↥d.G → ℂ} (hf : f ∈ testFunctions ↥d.G) :
    IsStronglyCuspidal d f ↔ IsStronglyCuspidalInline d f :=
  ⟨IsStronglyCuspidal.inline d, fun h FW FV hFV p hp =>
    ⟨integrable_parabolicU_of_testFunctions d hf FW FV p, h FW FV hFV p hp⟩⟩

end GSpinGGP
