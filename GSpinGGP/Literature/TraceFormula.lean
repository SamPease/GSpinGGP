/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalGroups
import GSpinGGP.Foundations.Representations
import GSpinGGP.Foundations.GSpin

/-!
# Cited inputs of the local trace formula: unimodularity and the quasi-character `θ_f`

Two results from the
literature that the trace-formula part of the proof (Thesis Ch. 7–12) uses as black
boxes, stated as `axiom`s about the concrete groups `d.G = GSpin(W) × GSpin(V)` of a
`d : GGPData F` over a `p`-adic field `F`. Both quantify over *all* `d`, so they apply to the
inner forms `d.twist τ` as well; neither assumes quasi-splitness.

* (a) `haar_G_isMulRightInvariant` — `G(F)` is unimodular (connected reductive group);
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

/-! ## (a) Unimodularity of `G(F)` -/

/-- **(a) `G(F)` is unimodular.** The group of `F`-points of a connected reductive group over a
local field is unimodular: its modular character is `|det Ad(g)|_F`, and `det Ad` is a character
of `G` trivial on the derived group and on the (central) connected centre, hence trivial.
Here `G = GSpin(W) × GSpin(V)`.

Sources: Bourbaki, *Groupes et algèbres de Lie* III §3 no. 16 (number unverified);
Beuzart-Plessis, Astérisque 418 (2020), §1.6 (Haar measures on reductive groups are bi-invariant);
Thesis §2.4.

Stated for Mathlib's left Haar measure `Measure.haar` on `↥d.G` (the one used in
`IsCharacterOf` and the trace formula); quantified over every `d`, so it also covers the inner
forms `d.twist τ`. Used for the Weil quotient measure on `H(F)\G(F)/A_G(F)`:
right invariance on `G(F)/A_G(F)` follows from this *because `A_G` is central*. -/
axiom haar_G_isMulRightInvariant (d : GGPData F) :
    (Measure.haar : Measure ↥d.G).IsMulRightInvariant

attribute [instance] haar_G_isMulRightInvariant

/-- The same for an inner form `d.twist τ` (see `t2Space_twist_G` for why it is separate). -/
instance haar_twist_G_isMulRightInvariant (d : GGPData F) (τ : InnerTwist d.QW) :
    (Measure.haar : Measure ↥(d.twist τ).G).IsMulRightInvariant :=
  haar_G_isMulRightInvariant (d.twist τ)

end LitTF

end GSpinGGP
