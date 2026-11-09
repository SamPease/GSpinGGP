/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.GSpin
import GSpinGGP.Foundations.LocalGroups

/-!
# Good neighbourhoods of semisimple elements (cited: Waldspurger 2010, §3.1)

J.-L. Waldspurger, *Une formule intégrale reliée à la conjecture locale de Gross–Prasad*, Compos. Math.
146 (2010) (arXiv:0902.1875; printed pages of the arXiv version). Setting: `F` non-archimedean of
characteristic `0` (§1.1, p. 5) and "un groupe réductif connexe `G`" fixed for §§2–6 (§2.1, p. 7); here
`G = GSpin(W) × GSpin(V)` (`d.G`), which is connected reductive. A *`G`-domaine* of `G(F)` or `𝔤(F)` is an
open, closed, conjugation-invariant subset (§1.2, p. 6); "compact modulo conjugaison" means contained
in `Γ^G` for a compact `Γ` (§1.1, p. 6, stated on `G(F)`; on `𝔤(F)` it is the same definition for the
adjoint action). Here `𝔤(F)` is `d.lie = gspin(W) × gspin(V)`, with `gspin(U) = {X ∈ C⁰(U) : [X, U] ⊆ U}
= F ⊕ ∧²U` the Lie algebra of `GSpin(U)` (Thesis §5.1.3).

For `x ∈ G_ss(F)`, Waldspurger writes `G_x = Z_G(x)⁰` (§1.1, p. 5) and `𝔤_x` for its Lie algebra. Here
`𝔤_x(F)` is `lieCentralizer d.lie x = {X ∈ 𝔤(F) : xX = Xx}`: for semisimple `x` the Lie algebra of
`Z_G(x)` is the fixed space of `Ad x` (Humphreys, *Conjugacy classes in semisimple algebraic groups*,
1995, §1.10, Proposition), and `Z_G(x)⁰` has the same Lie algebra. The group `G_x(F)` is not formalized;
it occurs only in conclusions of the form "conjugate by an element of `G_x(F)`" and in "`exp(ω) ⊆ G_x(F)`",
which we weaken to `Z_G(x)(F)`, the elements of `G(F)` commuting with `x`.

**Modelling step (not in the source).** Waldspurger's exponential ("On sait que l'on peut définir une
application exponentielle", §1.2, p. 6) is not defined there. We identify it with the exponential
series `expA` of the ambient algebra `C(W) × C(V)`, through which `G ⊆ (C(W) × C(V))^×` is a faithful
linear representation: near `0` the exponential of a linear algebraic group is the exponential series of
a faithful representation (Bourbaki, *Lie groups and Lie algebras*, Ch. III), say on a neighbourhood
`U` of `0`. Apply the source to `ω₀ ∩ U ∩ 𝔤_x(F)`: every `X ∈ ω` is `g Y g⁻¹` with `Y ∈ ω₀ ∩ U` and
`g ∈ G_x(F)`, and both exponentials are `G(F)`-equivariant (`expA_units_conj`), so they agree at `X`.
-/

open Topology

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **Waldspurger 2010, §3.1 "Bons voisinages" (pp. 13–14)**, for `G = GSpin(W) × GSpin(V)` and
`x ∈ G_ss(F)`. "De bons voisinages de 0 existent, aussi petits que l'on veut en ce sens que, si `ω₀` est un
voisinage de 0 dans `𝔤_x(F)`, il existe un bon voisinage `ω` de 0 tel que `ω ⊂ ω₀^{G_x}`" (p. 14, stated
without proof), with conditions (1) and (2) of a good neighbourhood (p. 13):
(1) `ω` is a `G_x`-domain of `𝔤_x(F)`, compact modulo conjugation, invariant under `Z_G(x)(F)`, containing
`0`; (2) the exponential is defined on `ω` and is a homeomorphism, equivariant for `Z_G(x)(F)`, of `ω`
onto a `G_x`-domain `exp(ω)` of `G_x(F)`; and the consequence stated after them (p. 14): "Les
conditions (1) et (2) entraînent que l'ensemble `Ω = (x exp(ω))^G` est un `G`-domaine dans `G(F)`,
compact modulo conjugaison." Conditions (3)–(7) are not stated.

Weakenings and identifications (see the module docstring): `𝔤_x(F)` is `lieCentralizer d.lie x`;
conjugation by `G_x(F)` in "compact modulo conjugation" and in `ω ⊂ ω₀^{G_x}` is weakened to conjugation
by elements of `G(F)` commuting with `x`; of "`exp(ω)` a `G_x`-domain of `G_x(F)`" only
`exp(ω) ⊆ Z_G(x)(F)` is kept; `ω₀` is a neighbourhood of `0` in the ambient algebra (apply the source
to `ω₀ ∩ U ∩ 𝔤_x(F)`); `exp` is `expA`. Semisimple is `IsSS` in the faithful representation. -/
axiom waldspurger_goodNbhd (d : GGPData F) (x : ↥d.G) (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    {ω₀ : Set d.ambient} (hω₀ : ω₀ ∈ 𝓝 (0 : d.ambient)) :
    ∃ (ω : Set d.ambient) (E Ω : Set ↥d.G),
      ω ⊆ lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient) ∧ (0 : d.ambient) ∈ ω ∧
      IsOpen (Subtype.val ⁻¹' ω : Set ↥(lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))) ∧
      IsClosed (Subtype.val ⁻¹' ω : Set ↥(lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))) ∧
      (∀ g : ↥d.G, g * x = x * g → ∀ X ∈ ω,
        ((g : d.ambientˣ) : d.ambient) * X * ((g⁻¹ : d.ambientˣ) : d.ambient) ∈ ω) ∧
      (∃ Γ : Set d.ambient, Γ ⊆ lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient) ∧ IsCompact Γ ∧
        ∀ X ∈ ω, ∃ g : ↥d.G, g * x = x * g ∧ ∃ Y ∈ Γ,
          X = ((g : d.ambientˣ) : d.ambient) * Y * ((g⁻¹ : d.ambientˣ) : d.ambient)) ∧
      (∀ y ∈ E, y * x = x * y) ∧
      (∃ e : ↥ω ≃ₜ ↥E, ∀ X : ↥ω,
        ((((e X : ↥E) : ↥d.G) : d.ambientˣ) : d.ambient) = expA F (X : d.ambient)) ∧
      IsOpen Ω ∧ IsClosed Ω ∧ (∀ y g : ↥d.G, g ∈ Ω → y * g * y⁻¹ ∈ Ω) ∧
      Ω = {g | ∃ y z : ↥d.G, z ∈ E ∧ g = y * (x * z) * y⁻¹} ∧
      (∃ K : Set ↥d.G, IsCompact K ∧ ∀ g ∈ Ω, ∃ (y k : ↥d.G), k ∈ K ∧ g = y * k * y⁻¹) ∧
      (∀ X ∈ ω, ∃ g : ↥d.G, g * x = x * g ∧ ∃ Y ∈ ω₀,
        X = ((g : d.ambientˣ) : d.ambient) * Y * ((g⁻¹ : d.ambientˣ) : d.ambient))

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra in
/-- **Waldspurger 2010, §3.1 "Bons voisinages" (pp. 13–14), at `x = 1`**: the case `x = 1` of
`waldspurger_goodNbhd`, where `G_x = Z_G(x) = G` and `𝔤_x = 𝔤`. A good neighbourhood `ω ⊆ ω₀^{G(F)}` of
`0` in `𝔤(F)` is a `G`-domain, compact modulo conjugation, and `exp` is a homeomorphism of `ω` onto the
`G`-domain `Ω = exp(ω)` (`exp(ω)` is already invariant, as `ω` is and `exp` is equivariant). -/
theorem waldspurger_goodNbhd_one (d : GGPData F) {ω₀ : Set d.ambient}
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
 := by
  have hss : IsSS F (((1 : ↥d.G) : d.ambientˣ) : d.ambient) := by
    unfold IsSS
    simp only [OneMemClass.coe_one, Units.val_one, LinearMap.mulLeft_one]
    exact Module.End.isSemisimple_id
  obtain ⟨ω, E, Ω, hωlie, h0, hωo, hωc, hωinv, ⟨Γ, hΓlie, hΓ, hωΓ⟩, -, ⟨e, he⟩, hΩo, hΩc,
    hΩinv, hΩeq, -, hsmall⟩ := waldspurger_goodNbhd d 1 hss hω₀
  have hL : lieCentralizer d.lie (((1 : ↥d.G) : d.ambientˣ) : d.ambient) = d.lie := by
    refine LieSubalgebra.ext _ _ fun X => ?_
    simp [mem_lieCentralizer]
  rw [hL] at hωlie hωo hωc hΓlie
  have hval : ∀ g h : ↥d.G, ((g : d.ambientˣ) : d.ambient) = ((h : d.ambientˣ) : d.ambient) →
      g = h := fun g h hgh => Subtype.ext (Units.ext hgh)
  have hEΩ : E = Ω := by
    rw [hΩeq]
    ext g
    constructor
    · intro hg; exact ⟨1, g, hg, by simp⟩
    · rintro ⟨y, z, hz, rfl⟩
      obtain ⟨X, hX⟩ := e.surjective ⟨z, hz⟩
      have hX' := hωinv y (by simp) X X.2
      convert (e ⟨_, hX'⟩).2 using 1
      apply hval
      rw [he, expA_units_conj F ((y : d.ambientˣ)) (X : d.ambient), ← he X, hX]
      simp [mul_assoc]
  refine ⟨ω, Ω, hωlie, h0, hωo, hωc, fun g X hX => hωinv g (by simp) X hX,
    ⟨Γ, hΓlie, hΓ, fun X hX => ?_⟩, hΩo, hΩc, hΩinv,
    ⟨e.trans (Homeomorph.setCongr hEΩ), fun X => he X⟩, fun X hX => ?_⟩
  · obtain ⟨g, -, Y, hY, h⟩ := hωΓ X hX
    exact ⟨g, Y, hY, h⟩
  · obtain ⟨g, -, Y, hY, h⟩ := hsmall X hX
    exact ⟨g, Y, hY, h⟩

end GSpinGGP
