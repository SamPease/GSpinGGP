/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.GSpin
import GSpinGGP.Foundations.LocalGroups

/-!
# Good neighbourhoods of `0` (cited: Waldspurger 2010, §3.1)

J.-L. Waldspurger, *Une formule intégrale reliée à la conjecture locale de Gross–Prasad*, Compos. Math.
146 (2010) (arXiv:0902.1875; printed pages of the arXiv version). Setting: `F` non-archimedean of
characteristic `0` (§1.1, p. 5) and "un groupe réductif connexe `G`" fixed for §§2–6 (§2.1, p. 7); here
`G = GSpin(W) × GSpin(V)` (`d.G`), which is connected reductive. A *`G`-domaine* of `G(F)` or `𝔤(F)` is an
open, closed, conjugation-invariant subset (§1.2, p. 6); "compact modulo conjugaison" means contained
in `Γ^G` for a compact `Γ` (§1.1, p. 6, stated on `G(F)`; on `𝔤(F)` it is the same definition for the
adjoint action). We use §3.1 at `x = 1`, where `G_x = Z_G(x) = G` and `𝔤_x = 𝔤(F)`. Here `𝔤(F)` is
`d.lie = gspin(W) × gspin(V)`, with `gspin(U) = {X ∈ C⁰(U) : [X, U] ⊆ U} = F ⊕ ∧²U` the Lie algebra of
`GSpin(U)` (Thesis §5.1.3).

**Modelling step (not in the source).** Waldspurger's exponential ("On sait que l'on peut définir une
application exponentielle", §1.2, p. 6) is not defined there. We identify it with the exponential
series `expA` of the ambient algebra `C(W) × C(V)`, through which `G ⊆ (C(W) × C(V))^×` is a faithful
linear representation: near `0` the exponential of a linear algebraic group is the exponential series of
a faithful representation (Bourbaki, *Lie groups and Lie algebras*, Ch. III), say on a neighbourhood
`U` of `0`. Apply the source to `ω₀ ∩ U ∩ 𝔤(F)`: every `X ∈ ω` is `g Y g⁻¹` with `Y ∈ ω₀ ∩ U`, and both
exponentials are `G(F)`-equivariant (`expA_units_conj`), so they agree at `X`.
-/

open Topology

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **Waldspurger 2010, §3.1 "Bons voisinages" (pp. 13–14), at `x = 1`**, for `G = GSpin(W) × GSpin(V)`.
"De bons voisinages de 0 existent, aussi petits que l'on veut en ce sens que, si `ω₀` est un voisinage
de 0 dans `𝔤_x(F)`, il existe un bon voisinage `ω` de 0 tel que `ω ⊂ ω₀^{G_x}`" (p. 14, stated without
proof), together with conditions (1) and (2) of a good neighbourhood (p. 13): (1) `ω` is a `G`-domain of
`𝔤(F)`, compact modulo conjugation, containing `0`; (2) the exponential is defined on `ω` and is a
homeomorphism of `ω` onto a `G`-domain `exp(ω)` of `G(F)` (equivariant; here `expA_units_conj`).
Conditions (3)–(7) are not stated. Here `ω₀` is a neighbourhood of `0` in the ambient algebra (apply the
source to `ω₀ ∩ U ∩ 𝔤(F)`, `U` as in the module docstring), and `exp` is `expA` (see the module
docstring for this identification). -/
axiom waldspurger_goodNbhd_one (d : GGPData F) {ω₀ : Set d.ambient}
    (hω₀ : ω₀ ∈ 𝓝 (0 : d.ambient)) :
    ∃ (ω : Set d.ambient) (Ω : Set ↥d.G),
      ω ⊆ d.lie ∧ (0 : d.ambient) ∈ ω ∧
      IsOpen (Subtype.val ⁻¹' ω : Set ↥d.lie) ∧ IsClosed (Subtype.val ⁻¹' ω : Set ↥d.lie) ∧
      (∀ g : ↥d.G, ∀ X ∈ ω,
        ((g : d.ambientˣ) : d.ambient) * X * ((g⁻¹ : d.ambientˣ) : d.ambient) ∈ ω) ∧
      (∃ Γ : Set d.ambient, Γ ⊆ d.lie ∧ IsCompact Γ ∧ ∀ X ∈ ω, ∃ g : ↥d.G, ∃ Y ∈ Γ,
        X = ((g : d.ambientˣ) : d.ambient) * Y * ((g⁻¹ : d.ambientˣ) : d.ambient)) ∧
      IsOpen Ω ∧ IsClosed Ω ∧ (∀ x g : ↥d.G, g ∈ Ω → x * g * x⁻¹ ∈ Ω) ∧
      (∃ e : ↥ω ≃ₜ ↥Ω, ∀ X : ↥ω,
        ((((e X : ↥Ω) : ↥d.G) : d.ambientˣ) : d.ambient) = expA F (X : d.ambient)) ∧
      (∀ X ∈ ω, ∃ g : ↥d.G, ∃ Y ∈ ω₀,
        X = ((g : d.ambientˣ) : d.ambient) * Y * ((g⁻¹ : d.ambientˣ) : d.ambient))

end GSpinGGP
