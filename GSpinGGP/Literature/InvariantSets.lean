/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Interface

/-!
# Invariant open and closed subsets of `G(F)` (cited, `p`-adic)

Two standard facts about conjugation-invariant subsets of a `p`-adic reductive group, used by the
localization arguments of Thesis Ch. 12 (`TraceFormula/Scusp.lean`, `TraceFormula/Geometric.lean`).
Both are stated for `d.G = GSpin(W) × GSpin(V)` modulo its split centre `A_G(F)`, and both quantify
over *all* `d : GGPData F`.

* `hc_exists_invariantClopen_superset`: every compact subset of `G(F)` lies in an open and closed,
  invariant, `A_G(F)`-stable subset that is compact modulo conjugation and `A_G(F)` (Harish-Chandra's
  compactness lemma in its `p`-adic, characteristic-polynomial form).
* `hc_exists_invariantClopen_nearCentral`: the elements whose semisimple part lies in `A_G(F)` have
  arbitrarily small open and closed invariant `A_G(F)`-stable neighbourhoods (small in the sense:
  every element is conjugate, modulo `A_G(F)`, into a given neighbourhood of `1`).

**Why they hold (both).**  Write `Ḡ = G/A_G`; since `A_G` is a split torus, `G(F)/A_G(F) = Ḡ(F)`
(Hilbert 90) and the topologies agree.  Embed `Ḡ ⊆ GL_N` and let `c : Ḡ(F) → F^N` be the
characteristic-polynomial map; it is continuous and conjugation invariant, so `c⁻¹(K)` is open, closed
and invariant for every compact open `K ⊆ F^N`, and its preimage in `G(F)` is moreover
`A_G(F)`-stable.  Over a `p`-adic field of characteristic `0`: (i) there are finitely many
`Ḡ(F)`-conjugacy classes of maximal tori, and a semisimple element of a torus `T(F)` whose eigenvalues
lie in a compact subset of `F̄^×` lies in a compact subset of `T(F)`; (ii) for each of the finitely
many centralizers `M = Ḡ_s^0` (`s` in a fixed torus), `M(F)` has finitely many unipotent classes, each
containing `1` in its closure (a cocharacter of `M` centralizes `s`, which is central in `Ḡ_s`).
By Jordan decomposition `g = s u`, `u ∈ Ḡ_s^0`, (i) and (ii) give: `c⁻¹(K)` is compact modulo
conjugation (first axiom, `K ⊇ c(C̄)`), and for `K` a small neighbourhood of `(X − 1)^N` every element
of `c⁻¹(K)` is conjugate into a given neighbourhood of `1` (second axiom).  Compact subsets of
`Ḡ(F)` lift to compact subsets of `G(F)` (`G(F)` is locally compact).

Two precisions (both axioms are *adapted*).  For the first
axiom, choose `K` with its constant-term coordinate in a compact subset of `F^×` (possible since
`c(C̄)` is compact and `det ≠ 0` on `Ḡ(F)`); otherwise eigenvalues could tend to `0` and (i) would
not apply (in `GL_N`, `diag(t, 1, …, 1)` with `t → 0` has bounded coefficients).  For the second
axiom, the cocharacter in (ii) is an `F`-rational cocharacter of `M = Ḡ_s^0` contracting the
unipotent part to `1`, which exists by Jacobson–Morozov over `F` (characteristic `0`).

**Sources.**  Harish-Chandra, *Harmonic analysis on reductive `p`-adic groups*, Lecture Notes in
Math. 162 (1970), Part I (the compactness lemma and the finiteness of unipotent classes; numbers
unverified); BP Astérisque 418 (2020) §3.1, Prop 3.1.1(i) = Thesis Prop 3.5.1(i) (exhaustion of a
completely invariant open set by completely invariant open sets whose closures are compact modulo
conjugation; the `p`-adic open-and-closed refinement is the characteristic-polynomial argument
above, not literally in BP); BP §3.3 = Thesis §3.5.2 (`G`-excellent neighbourhoods `ω` of `0`, with
`exp(ω)` an open completely invariant neighbourhood of the unipotent set).  BP/Thesis Prop 3.5.1(i)
gives only *open* sets with closures compact modulo conjugation, and §3.3 is a Lie-algebra statement
used here only as motivation: closedness, `A_G(F)`-stability and the group-side form come from the
characteristic-polynomial argument above.  A numbered source for "the preimage of a compact set
under the characteristic-polynomial (Steinberg) map is compact modulo conjugation" is still wanted
(HC LNM 162 Part I, or Kottwitz's Clay notes, are likely places).  Status: adapted, not verified
against a single numbered statement.

**Degenerate checks** (`Sanity/InvariantSetsAudit.lean`): at `toyD` (`A_G = G`) both conclusions hold
with `Ω = G(F)` without the axioms.  For `G` a split torus (hyperbolic planes), `Ω = A_G(F)·K` with
`K` a compact open subgroup (inside `U` for the second axiom) works: it is open, and closed as the
product of a closed subgroup and a compact set.
-/

open Topology

noncomputable section

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **Harish-Chandra's compactness lemma, `p`-adic open-and-closed form** (see the module docstring
for the argument and sources: HC LNM 162 Part I; BP Astérisque 418 Prop 3.1.1(i) = Thesis
Prop 3.5.1(i), adapted).  Every compact `C ⊆ G(F)` is contained in a subset `Ω` that is open and
closed, conjugation invariant and `A_G(F)`-stable (`IsInvariantClopen`), and compact modulo
conjugation and `A_G(F)`: `Ω ⊆ A_G(F) · C'^{G(F)}` for a compact `C'`.  (In
`TraceFormula/Geometric.lean` terms: `C` lies in a set of the projective system `IsQCCutoff`.) -/
axiom hc_exists_invariantClopen_superset (d : GGPData F) {C : Set ↥d.G} (hC : IsCompact C) :
    ∃ Ω : Set ↥d.G, IsInvariantClopen d Ω ∧ C ⊆ Ω ∧
      ∃ C' : Set ↥d.G, IsCompact C' ∧
        ∀ g ∈ Ω, ∃ (a : ↥d.AG) (x c : ↥d.G), c ∈ C' ∧ g = (a : ↥d.G) * (x * c * x⁻¹)

/-- **Small invariant open-and-closed neighbourhoods of the near-central set** (see the module
docstring: HC LNM 162 Part I; BP Astérisque 418 §3.3 = Thesis §3.5.2, `G`-excellent sets, adapted).
For every neighbourhood `U` of `1` in `G(F)` there is an open and closed, invariant,
`A_G(F)`-stable `Ω` that contains every near-central `c` (`1` lies in the closure of
`A_G(F) · c^{G(F)}`; Lean: `IsNearCentral`, `TraceFormula/Geometric.lean`, written out here), and
every element of which is conjugate into `U` modulo `A_G(F)`. -/
axiom hc_exists_invariantClopen_nearCentral (d : GGPData F) {U : Set ↥d.G}
    (hU : U ∈ 𝓝 (1 : ↥d.G)) :
    ∃ Ω : Set ↥d.G, IsInvariantClopen d Ω ∧
      (∀ c : ↥d.G, (∀ V ∈ 𝓝 (1 : ↥d.G), ∃ (a : ↥d.AG) (x : ↥d.G),
          ((a : ↥d.G))⁻¹ * (x * c * x⁻¹) ∈ V) → c ∈ Ω) ∧
      ∀ g ∈ Ω, ∃ (a : ↥d.AG) (x : ↥d.G), ((a : ↥d.G))⁻¹ * (x * g * x⁻¹) ∈ U

end GSpinGGP
