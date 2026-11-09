/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalGroups
import GSpinGGP.Foundations.Representations
import GSpinGGP.Foundations.GSpin

/-!
# Cited inputs of the local trace formula: the strongly cuspidal kernel

A result from the literature that the trace-formula part of the proof (Thesis Ch. 7–12) uses as a
black box, stated as an `axiom` about the concrete groups `d.G = GSpin(W) × GSpin(V)` of a
`d : GGPData F` over a `p`-adic field `F`. It quantifies over *all* `d`, so it applies to the inner
forms `d.twist τ` as well, and does not assume quasi-splitness. (The unimodularity of `G(F)` is
proved: `GGPData.isMulRightInvariant_haar_G`, `TraceFormula/Basic.lean`.)

* (a) `bp_integrable_kernel_scusp` — for `f₀, f' ∈ C_c^∞(G(F))` with `f₀` strongly cuspidal, the
  function `x ↦ ∫_{G(F)} f₀(x⁻¹gx) f'(g) dg` is integrable on `G(F)/A_G(F)` (BP Thm 5.5.1(ii), in
  the form stated after it on p. 116; Thesis Thm 4.7.1(ii)).  BP states it without proof.

The composite statements built on it live in `TraceFormula/StronglyCuspidal.lean`:
`bp_thetaF_exists` (the quasi-character `θ_f`; proved from this axiom and the `sorry` theorem
`bp_thetaF_represents`) and `bp_scusp_surj_ell` (BP Cor 5.7.2(i), adapted to a non-compact centre;
a `sorry` theorem).

Since `TraceFormula/Basic.lean` and `Literature/HarishChandra.lean` are in the same layer and not
visible here, the kernel and strong cuspidality are written out inline with the L1 names
(`whittB`, `whittU`, `IsProperFlagPair`, `↥d.G ⧸ d.AG`, `testFunctions`), and the topological
instances on `↥d.G` are redeclared (under names in the namespace `GSpinGGP.LitTF`, so they do not
clash with `HarishChandra`'s).

Not axiomatized, on purpose: Luo Lemma 7.2.2 and the `χ`-equivariant forms of `bp_thetaF_exists`
and `bp_scusp_surj_ell`, which are proved in this development (`TraceFormula/ThetaF.lean`,
`TraceFormula/Scusp.lean`).
-/

open MeasureTheory Topology Filter

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

namespace LitTF

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-! ## Topological and measurable instances -/

/-- `G(F)` is Hausdorff (LocalGroups `subgroup_t2Space`). Same as `HarishChandra.t2Space_G`,
redeclared because that file is in the same layer. -/
instance t2Space_G (d : GGPData F) : T2Space ↥d.G :=
  subgroup_t2Space F d.ambient d.G

/-- `G(F)` is locally compact (`d.G` is closed in `(C(W) × C(V))ˣ`, `GGPData.isClosed_G`). -/
instance locallyCompactSpace_G (d : GGPData F) : LocallyCompactSpace ↥d.G :=
  subgroup_locallyCompactSpace_of_isClosed F d.ambient d.G d.isClosed_G

/-- The same for an inner form `d.twist τ` (`GGPData.twist` is an `abbrev`, so the generic
instance is not found by discrimination; cf. `HarishChandra.t2Space_twist_G`). -/
instance t2Space_twist_G (d : GGPData F) (τ : InnerTwist d.QW) : T2Space ↥(d.twist τ).G :=
  t2Space_G (d.twist τ)

/-- `G_α(F)` is locally compact (see `t2Space_twist_G`). -/
instance locallyCompactSpace_twist_G (d : GGPData F) (τ : InnerTwist d.QW) :
    LocallyCompactSpace ↥(d.twist τ).G :=
  locallyCompactSpace_G (d.twist τ)

/-- The unipotent radical `U(F) = N_{F_W} × N_{F_V}` of a parabolic subgroup is locally compact
(it is closed in `G(F)`, `GGPData.isClosed_whittU`), so it carries a Haar measure. -/
instance locallyCompactSpace_whittU (d : GGPData F) (FW : IsotropicFlag d.QW)
    (FV : IsotropicFlag d.QV) : LocallyCompactSpace ↥(d.whittU FW FV) :=
  (d.isClosed_whittU FW FV).locallyCompactSpace

/-- The Borel σ-algebra on the quotient group `G(F)/A_G(F)` (`A_G` is central, hence normal,
`GGPData.AG_normal`). The topological group structure and local compactness come from Mathlib.
Meant to agree with `TraceFormula/Basic.lean`'s `GmodAG` (an `abbrev` for the same type with the
same `borel _` instance). -/
instance instMeasurableSpaceGmodAG (d : GGPData F) : MeasurableSpace (↥d.G ⧸ d.AG) := borel _

instance instBorelSpaceGmodAG (d : GGPData F) : BorelSpace (↥d.G ⧸ d.AG) := ⟨rfl⟩

/-! ## (a) Integrability of the kernel on the diagonal (BP Thm 5.5.1(ii)) -/

/-- **Integrability of `K^A_{f,f'}(x,x)` for strongly cuspidal `f`** (Beuzart-Plessis, *A local
trace formula for the Gan–Gross–Prasad conjecture for unitary groups: the archimedean case*,
Astérisque 418 (2020), §5.5, p. 116; Thesis Thm 4.7.1(ii)). BP fixes "until the end of Chapter 5, a
connected reductive group `G` over `F`" (§1.1, `F` "either p-adic (i.e., a finite extension of ℚ_p)
or ℝ"), sets `K^A_{f,f'}(g₁,g₂) = ∫_{G(F)} f(g₁⁻¹ g g₂) f'(g) dg` and states, after Thm 5.5.1(iii):
"By the point (ii), the function `x ∈ A_G(F)\G(F) ↦ K^A_{f,f'}(x,x)` is integrable as soon as `f`
is strongly cuspidal", for `f ∈ 𝒞_scusp(G(F))` and `f' ∈ 𝒞(G(F))`.

Specialized to the connected reductive group `G = GSpin(W) × GSpin(V)` over `p`-adic `F`, with `f,
f' ∈ C_c^∞(G(F)) ⊂ 𝒞(G(F))` (for `p`-adic `F`, `𝒞(G(F))` is the union over compact open `K'` of the
bi-`K'`-invariant `f` with `sup |f| Ξ^{-1} σ^d < ∞` for all `d`, BP §1.5, p. 25; a locally constant
compactly supported `f` is bi-`K'`-invariant for some compact open `K'`, and has this property
since `Ξ` is continuous and positive). Strong cuspidality is BP §5.1, p. 108: `f^P = 0` for every
proper parabolic `P = MU`, where `f^P(m) = δ_P(m)^{1/2} ∫_{U(F)} f(mu) du`; it is written here as
`∫_{U(F)} f(pu) du = 0` for `p ∈ P(F)` (equivalent: `p = mu'` and `du` is invariant), over the
proper parabolic subgroups `P = P_{F_W} × P_{F_V}` given by proper pairs of isotropic flags (Thesis
§5.1.2: every parabolic subgroup of `GSpin(V)` is a flag stabilizer, and the parabolic subgroups of
a product are the products of parabolic subgroups; `IsProperFlagPair` is `whittB FW FV ≠ ⊤`). The
kernel is evaluated at the representative `Quotient.out x`; it does not depend on it because `A_G`
is central. Integrability does not depend on the normalization of either Haar measure.

**Stated without proof in the source.** BP p. 116: "The proof of these two theorems will appear
elsewhere [18]", with [18] = R. Beuzart-Plessis, *A slight variation of Arthur local trace
formula*, in preparation; no published version is known. For `p`-adic `F` an equivalent form of the
identity of the geometric and spectral sides of the local trace formula for a cuspidal test
function (Thm 5.5.1(iv) = (v)), written with Arthur's invariant weighted orbital integrals and
elliptic characters, is proved in J. Arthur, *On elliptic tempered characters*, Acta Math. 171
(1993), Thm 4.2 (p. 102) and Cor 4.3 (pp. 104–105); the integrability statement here is not part
of that. -/
axiom bp_integrable_kernel_scusp (d : GGPData F) (f₀ : ↥d.G → ℂ) (hf₀ : f₀ ∈ testFunctions ↥d.G)
    (hcusp : ∀ (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV), d.IsProperFlagPair FW FV →
      ∀ p ∈ d.whittB FW FV,
        ∫ u : ↥(d.whittU FW FV), f₀ (p * u) ∂Measure.haar = 0)
    (f' : ↥d.G → ℂ) (hf' : f' ∈ testFunctions ↥d.G) :
    Integrable (fun x : ↥d.G ⧸ d.AG =>
        ∫ g : ↥d.G, f₀ ((Quotient.out x)⁻¹ * g * Quotient.out x) * f' g ∂Measure.haar)
      Measure.haar

end LitTF

end GSpinGGP
