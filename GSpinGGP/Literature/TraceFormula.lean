/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalGroups
import GSpinGGP.Foundations.Representations
import GSpinGGP.Foundations.GSpin

/-!
# Cited inputs of the local trace formula: the quasi-character `θ_f`

Results from the literature that the trace-formula part of the proof (Thesis Ch. 7–12) uses as
black boxes, stated about the concrete groups `d.G = GSpin(W) × GSpin(V)` of a `d : GGPData F` over
a `p`-adic field `F` (as `axiom`s, or as `sorry` theorems where the statement is adapted). They
quantify over *all* `d`, so they apply to the inner forms `d.twist τ` as well; none assumes
quasi-splitness. (The unimodularity of `G(F)` is proved: `GGPData.isMulRightInvariant_haar_G`,
`TraceFormula/Basic.lean`.)

* (b) `bp_thetaF_exists` — for `f₀ ∈ C_c^∞(G(F))` strongly cuspidal, the invariant distribution
  `f' ↦ ∫_{G(F)/A_G(F)} ∫_{G(F)} f₀(x⁻¹gx) f'(g) dg dx` is represented by a locally integrable
  function `θ` which is locally constant on `G_reg(F)` and is a quasi-character
  (BP Thm 5.5.1(ii),(iv) + Weyl integration, Prop 5.6.1(ii); Thesis Thm 4.7.1, Prop 4.8.1).

Since `TraceFormula/Basic.lean` and `Literature/HarishChandra.lean` are in the same layer and not
visible here, the orbital pairing and strong cuspidality are written out inline with the L1 names
(`whittB`, `whittU`, `IsProperFlagPair`, `↥d.G ⧸ d.AG`, `testFunctions`, `regularSet`,
`IsQuasiCharacter`), and the topological instances on `↥d.G` are redeclared (under names in the
namespace `GSpinGGP.LitTF`, so they do not clash with `HarishChandra`'s).

* (c) `bp_scusp_surj_ell` — BP Cor 5.7.2(i) (`p`-adic surjectivity of
  `S_scusp(Ω) → QC_c(Ω)` near the elliptic set), *untwisted* on `G(F)`, in the form its proof
  gives when `A_G` is nontrivial (the adaptation is explained in its docstring).

Not axiomatized here, on purpose: Luo Lemma 7.2.2 and the `χ`-equivariant forms of (b) and (c),
which are proved in this development (`TraceFormula/ThetaF.lean`, `TraceFormula/Scusp.lean`).
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

end LitTF

end GSpinGGP
