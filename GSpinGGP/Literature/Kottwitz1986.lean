/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.Kottwitz

/-!
# Fundamental tori: `H¹(F, T) → H¹(F, G)` is surjective (cited)

## Definitions (real definitions, no axioms)

* `fixerFbar d x`: the elements of `GSpin(W)(F̄)` acting trivially on `W'_x ⊗ F̄`, and
  `fixerBar d x = P(fixerFbar d x) ⊆ SO(W)(F̄)`, as matrices in the rational basis.  This is the
  group of `F̄`-points of `SO(W)_{W'_x}`, the pointwise stabilizer of `W'_x` in `SO(W)`, which is
  `SO(W''_x)` extended by `1` on `W'_x` (`P : GSpin(W)(F̄) → SO(W)(F̄)` is onto).
* `torusBarFbar_le_fixerBar`: `S_x(F̄) ⊆ (SO(W)_{W'_x})(F̄)`.

## Cited result (axiom)

* `exists_rel_torusBar_of_fixerBar` (Kottwitz, Math. Ann. 275 (1986), Lemma 10.2): for
  `x ∈ Γ(G,H)`, every class in `H¹(F, SO(W)_{W'_x})` comes from `H¹(F, S_x)`.
-/

noncomputable section

open CliffordAlgebra
open scoped TensorProduct

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

/-- The elements of `GSpin(W)(F̄)` acting trivially on `W'_x ⊗ F̄`. -/
def fixerFbar (x : ↥(GSpin d.QW)) :
    Subgroup ↥(GSpin (d.QW.baseChange (AlgebraicClosure F))) where
  carrier := {g | ∀ w ∈ (fixedSub x).baseChange (AlgebraicClosure F),
    specP (d.QW.baseChange (AlgebraicClosure F)) g w = w}
  one_mem' := fun w _ => by simp
  mul_mem' := fun {g h} hg hh w hw => by
    rw [map_mul, LinearEquiv.mul_apply, hh w hw, hg w hw]
  inv_mem' := fun {g} hg w hw => by
    have h1 : specP _ g⁻¹ (specP _ g w) = w := by
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [hg w hw] at h1
    exact h1

/-- `(SO(W)_{W'_x})(F̄) = P(fixerFbar d x) ⊆ SO(W)(F̄) ⊆ GL_m(F̄)`: the `F̄`-points of the pointwise
stabilizer of `W'_x` in `SO(W)` (`≅ SO(W''_x)`). -/
def fixerBar (x : ↥(GSpin d.QW)) : Subgroup (GL (Fin d.m) (AlgebraicClosure F)) :=
  (d.fixerFbar x).map (specMatFbar d.QW)

theorem torusFbar_le_fixerFbar (x : ↥(GSpin d.QW)) : d.torusFbar x ≤ d.fixerFbar x :=
  fun _ hg => hg.2

theorem torusBarFbar_le_fixerBar (x : ↥(GSpin d.QW)) : d.torusBarFbar x ≤ d.fixerBar x :=
  Subgroup.map_mono (d.torusFbar_le_fixerFbar x)

end GGPData

/-- **Fundamental tori** (Kottwitz, *Stable trace formula: elliptic singular terms*, Math. Ann. 275
(1986), §10, Lemma 10.2, p. 397: for `F` `p`-adic or real and `G` a connected reductive group over
`F`, "Let `T` be a fundamental torus of `G`. Then `H¹(F,T) → H¹(F,G)` is surjective"; a maximal
`F`-torus is *fundamental* if the dimension of its split component is as small as possible; "in
the `p`-adic case fundamental tori are elliptic").

Applied to `G = SO(W)_{W'_x} ≅ SO(W''_x)` (connected reductive), with `F̄`-points
`fixerBar d x`, and `T = S_x`, with `F̄`-points `torusBarFbar d x ⊆ fixerBar d x`
(`torusBarFbar_le_fixerBar`), for `x ∈ Γ(G,H)`:
* `S_x` is a maximal torus of `SO(W)_{W'_x}`: it is `Z_{SO(W''_x)}(x̄'')`, the centralizer of the
  semisimple element `x̄'' = P(x)|_{W''_x}` (connected, `SO(E₋₁) × ∏ GL(E_λ)` since `x̄''` has no
  eigenvalue `1`; equal to `P(T_x(F̄))` since `P(g)` commuting with `x̄` gives `g x g⁻¹ = ±x`, with
  sign `+1` on the connected group; abelian for `x ∈ Γ(G,H)`), and the centralizer of a semisimple
  element contains a maximal torus;
* `S_x` is anisotropic (`S_x(F) = T_x(F)/A_{G,H}(F)` is compact, `IsGammaElt`), so its split
  component is trivial, of the smallest possible dimension `0`: `S_x` is fundamental.
The statement is written in cocycles: every continuous cocycle `c` with values in
`(SO(W)_{W'_x})(F̄)` is cohomologous in `(SO(W)_{W'_x})(F̄)` to a cocycle with values in `S_x(F̄)`.
That `fixerBar d x` and `torusBarFbar d x` are the `F̄`-points of these `F`-groups (with the
entrywise Galois action) is not formalized; the facts above about them are used only here. -/
axiom exists_rel_torusBar_of_fixerBar (d : GGPData F) (x : ↥(GSpin d.QW))
    (hx : d.IsGammaElt x) (c : GalCocycle (d.fixerBar x)) :
    ∃ a : GalCocycle (d.torusBarFbar x), ∃ h ∈ d.fixerBar x,
      ∀ σ : GalF F, a.toFun σ = h⁻¹ * c.toFun σ * galGL d.m σ h

end GSpinGGP
