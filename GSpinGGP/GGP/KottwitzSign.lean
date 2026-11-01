/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.Kottwitz

/-!
# Multiplicativity of the Kottwitz sign on `H¹(F, S_x)`

A `sorry` theorem. Its exact ingredients (BP Astérisque 418, (12.1.6), for
`SO(W) × SO(V)`; Kottwitz 1983) are listed in the docstring.
-/

noncomputable section

open scoped Classical TensorProduct

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

set_option linter.unusedSectionVars false

/-- **The Kottwitz sign is multiplicative on `H¹(F, S_x)`**.
For `G` quasi-split and `x ∈ Γ(G,H)`, if the cocycle `c` is the pointwise product of the cocycles
`a`, `b` (with values in `S_x`), then `e(G_{q_x[c]}) = e(G_{q_x[a]}) e(G_{q_x[b]})`.

Sources, combined as follows:
* Kottwitz, *Sign changes in harmonic analysis on reductive groups*, Trans. Amer. Math. Soc. 278
  (1983), 289–297: the sign `e(G')` of an inner form of a quasi-split group, equal to
  `(-1)^{rk_F G - rk_F G'}` for `F` `p`-adic (the formula `kottwitzSign`).  **The theorem number
  in Kottwitz 1983 is not verified**; the statement used is the one
  recalled in BP, *Astérisque* 418 (2020), §12.1.
* Beuzart-Plessis, loc. cit., §12.1: for pure inner forms of a quasi-split group `Ḡ`, `e(Ḡ')`
  is the image of the class of `Ḡ'` under the connecting map `H¹(F, Ḡ) → H²(F, {±1})` of the
  canonical central extension `Ḡ~ → Ḡ`; and (12.1.6): for a subtorus `S ⊆ Ḡ`, the composite
  `H¹(F, S) → H¹(F, Ḡ) → H²(F, {±1})` is a group homomorphism.
* The setup here: `Ḡ = SO(W) × SO(V)`, the inner form
  `G_α` has `e(G_α) = e(Ḡ_α)` (same adjoint group, same split central rank), the cocycles of the
  inner forms of the triple are `(a, a ⊕ 1_Z)` with `a` valued in `SO(W)`, and `S_x ⊆ Ḡ`
  diagonally.  So `e(G_{q_x(β)})` is the image of `β` under the homomorphism of (12.1.6).

The cohomology classes are compared through `TwistIdx` (`q_x`), so the axiom needs no group
structure on `H1`.  Degenerate cases: for `x` central, `S_x(F̄) = 1` and only `a = b = c = 1`
occur, with `q_x = 1` and `e = 1`.

**Status: `sorry`, not a literature axiom** (the statement is not verbatim in a source). Exact
ingredients:
* BP Astérisque 418, (12.1.6), for the quasi-split group `SO(W) × SO(V)`, the subtorus `S_x` and its
  pure inner forms. The sign is defined there through the connecting map to `H²(F, {±1})`.
* Kottwitz 1983: that sign is `(−1)^{rk_F G − rk_F G'}`.
* An inner form of `GSpin(W) × GSpin(V)` has the sign of the corresponding inner form of `SO(W) ×
  SO(V)` (same adjoint group). -/
theorem kottwitzSign_twistIdx_mul {d : GGPData F} (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (x : ↥(GSpin d.QW)) (hx : d.IsGammaElt x)
    (a b c : GalCocycle (d.torusBarFbar x)) (hc : ∀ σ, c.toFun σ = a.toFun σ * b.toFun σ)
    (α β γ : IF.Idx) (ha : TwistIdx IF x (H1.mk a) α) (hb : TwistIdx IF x (H1.mk b) β)
    (hγ : TwistIdx IF x (H1.mk c) γ) :
    kottwitzSign d (IF.twist γ) = kottwitzSign d (IF.twist α) * kottwitzSign d (IF.twist β) := by
  sorry

end GSpinGGP
