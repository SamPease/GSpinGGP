/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.GSpin
import GSpinGGP.Foundations.LocalGroups

/-!
# Nilpotent orbits are stable under squares (cited: Kottwitz, Clay Proc. 4, §17.5)

R. E. Kottwitz, *Harmonic analysis on reductive `p`-adic groups and Lie algebras*, in: Harmonic
Analysis, the Trace Formula, and Shimura Varieties, Clay Math. Proc. 4 (2005), 393–522. Setting of §17
(p. 459): "`F` is a `p`-adic field and `G` is a connected reductive `F`-group", with `G` also denoting
`G(F)`; nilpotent orbits in `𝔤` are `G(F)`-orbits (§17.2, p. 459).

**Application to a centralizer.** We apply §17.5 to the group `H = Z_G(s)⁰` for a semisimple
`s ∈ G(F)`, `G = GSpin(W) × GSpin(V)`, not to `G` itself. Its hypotheses: `H` is a connected reductive
`F`-group (Humphreys, *Conjugacy classes in semisimple algebraic groups*, 1995, §2.2, Theorem:
`Z_G(s)` is reductive, so its identity component is connected reductive; also Arthur, *An introduction
to the trace formula*, same volume, §16, p. 91), with Lie algebra
`Lie(H) = Lie Z_G(s) = {X ∈ 𝔤 : Ad(s)X = X}` (Humphreys 1995, §1.10, Proposition: equality for
semisimple `s`), i.e. `lieCentralizer d.lie s`. An element of `Lie(H)(F)` is nilpotent in `Lie(H)` iff it
is nilpotent in the faithful representation `H ⊆ G ⊆ (C(W) × C(V))^×` (the Jordan decomposition in the
Lie algebra of a linear algebraic group is preserved by representations). The element `h ∈ H(F)`
given by the source is weakened to an element of `G(F)` commuting with `s`.
-/

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **Kottwitz 2005, §17.5 "Homogeneity of nilpotent orbital integrals" (p. 461)**: "Let `O` be a
nilpotent orbit in `𝔤`. Then for any `α ∈ F^×` multiplication by `α²` preserves `O`" (proved there
via Jacobson–Morozov and `SL₂`). Applied to the connected reductive group `Z_G(s)⁰`, `s ∈ G(F)`
semisimple, whose Lie algebra is `𝔤_s = lieCentralizer d.lie s` (see the module docstring): for `N ∈ 𝔤_s`
nilpotent, `α²N = Ad(h)N` for some `h ∈ Z_G(s)⁰(F)`, in particular for some `h ∈ G(F)` commuting with
`s`. -/
axiom kottwitz_nilpotent_sq_smul (d : GGPData F) (s : ↥d.G)
    (hs : IsSS F ((s : d.ambientˣ) : d.ambient)) {N : d.ambient}
    (hN : N ∈ lieCentralizer d.lie ((s : d.ambientˣ) : d.ambient)) (hNnil : IsNilpotent N)
    {α : F} (hα : α ≠ 0) :
    ∃ h : ↥d.G, h * s = s * h ∧
      ((h : d.ambientˣ) : d.ambient) * N * ((h⁻¹ : d.ambientˣ) : d.ambient) = (α ^ 2) • N

end GSpinGGP
