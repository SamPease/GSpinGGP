/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Interface

/-!
# Literature inputs for `m_geom` (Thesis Prop 12.1.1)

Content: BP Astérisque 418, Lemma B.1.2 (convergence
of the integrals defining `m_geom`), and any other cited input of Thesis Prop 12.1.1, each as an
`axiom` with its source, `#check`ed for its binders and instantiated at `toyData` with no `False`.

**What is not an axiom, and why.**  BP Lemma B.1.2(i) says: for a torus `T` over `F` and linearly
independent characters `χ_1, …, χ_n ∈ X^*(T)` (over `F̄`), `t ↦ ∏ |χ_i(t) − 1|^{s−1}` is locally
integrable on `T(F)` for `Re s > 0`.  This development has no algebraic tori or character
lattices, and the statement with continuous homomorphisms in place of algebraic characters is
false (on `F^×`, `χ_1(t) = t` and `χ_2(t) = t^a` on `1 + pℤ_p` with `a ∈ ℤ_p` irrational are
ℤ-independent, but `|t − 1|^{2s−2}` is not locally integrable near `1` for `s ≤ 1/2`).  So
B.1.2(i) itself is not stated.

**What is an axiom.**  Its GSpin consequence, the one Thesis Prop 12.1.1(i) uses:
* `bp_integrable_deltaGGP_rpow`: for `x ∈ Γ(G,H)` and `s > 0`,
  `∫_{T_x(F)/A_{G,H}(F)} 1_{T_♮}(t) Δ(t)^{s−1/2} dt < ∞`.
It is an *adapted* citation (BP Lemma B.1.2(i) plus the thesis's eigenvalue computation), not a
verbatim one; see its docstring.  Consistency check: at `x = 1` (a point of `Γ(G,H)` for every
`d`) the conclusion is proved outright, without the axiom (`TraceFormula/MGeom.lean`,
`integrable_delta_rpow_torusOf_one`).  For `toyData` (`W = 0`) and for `W` of dimension `1` or a
hyperbolic plane, every torus `T_x` of `Γ(G,H)` is `T_1` (by hand: `W''_x` is even-dimensional,
and `W''_x = W` split makes `T_x(F)/A_{G,H}(F) ≅ F^×` non-compact), so this covers them.  These
instances test consistency only: the content of the axiom is `dim W''_x ≥ 2`.
-/

open MeasureTheory

noncomputable section

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **Integrability of `Δ^{s−1/2}` on `T_x(F)/A_{G,H}(F)`** (BP Astérisque 418, Lemma B.1.2(i),
applied as in Thesis Prop 12.1.1(i), proof of (12.1.2): "a straightforward application of
Lemma B.1.2(i)"; the same step in BP's proof of their Prop 11.2.1).

For `x ∈ Γ(G,H)` with torus `T = T_x`, `T_♮ = {t ∈ T | t ∈ Γ(G,H), T_t = T}` and `s > 0`, the
function `t ↦ 1_{T_♮}(t) Δ(t)^{s−1/2}` on `T(F)` (it is `A_{G,H}(F)`-invariant: `P(ct) = P(t)`),
evaluated on coset representatives, is integrable on the compact group `T(F)/A_{G,H}(F)` for its
probability Haar measure.

Derivation from B.1.2(i) (the thesis's step, not BP's statement): on `T_♮` the eigenvalues of
`P(t)` on `W'' = W''_x` are `λ_i(t)^{±1}`, `1 ≤ i ≤ n = dim W''/2`, with `λ_1, …, λ_n` linearly
independent algebraic characters of `T`, all of absolute value `1` (`T(F)/A_{G,H}(F)` is compact);
so `Δ(t) = |det(P(t) − 1)|_{W''}| = ∏ |λ_i(t) − 1|²` and `Δ^{s−1/2} = ∏ |λ_i − 1|^{2s−1}`, locally
integrable on `T(F)` by B.1.2(i) at `2s`, hence integrable on the compact quotient.
Three points of this derivation, spelled out:
(a) `λ_1, …, λ_n` are linearly independent because `T_x` is the identity component of a centralizer
in `GSpin(W''_x)`, hence a maximal torus, so `λ_1, …, λ_n` form a basis of `X^*(S)`,
`S = P(T_x)`; (b) `deltaGGP d t` is computed on `movedSub t`, and on `T_♮` this is `W''_x`: `t ∈ T_x`
fixes `W'_x`, so `W''_t ⊆ W''_x`, and `x ∈ T_x = T_t` fixes `W'_t`, so `W''_x ⊆ W''_t`; (c) real
`s > 0` is the restriction of BP's `Re s > 0`.  Exact source: arXiv:1506.01452 (BP), App. B.1,
Lemma B.1.2(i), for `F` any local field of characteristic `0` other than `ℂ`.

Stated for `Γ`-tori only (`T = T_x`, `x ∈ Γ(G,H)`); for any other subgroup the integrand is `0`
(`TraceFormula/MGeom.lean`, `integrable_delta_rpow`). -/
axiom bp_integrable_deltaGGP_rpow (d : GGPData F) {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    {s : ℝ} (hs : 0 < s) :
    letI : MeasurableSpace (d.TorusQuot (d.torusOf x)) := borel _
    haveI : BorelSpace (d.TorusQuot (d.torusOf x)) := ⟨rfl⟩
    Integrable (fun q : d.TorusQuot (d.torusOf x) =>
      Set.indicator {t : ↥(GSpin d.QW) | d.IsGammaElt t ∧ d.torusOf t = d.torusOf x}
        (fun t => deltaGGP d t ^ (s - 1 / 2))
        ((Quotient.out q : ↥(d.torusOf x)) : ↥(GSpin d.QW)))
      (probHaar (d.TorusQuot (d.torusOf x)))

end GSpinGGP
