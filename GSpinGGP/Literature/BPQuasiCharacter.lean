/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.HarishChandra

/-!
# Local boundedness of quasi-characters (cited: Beuzart-Plessis, Astérisque 418, Prop 4.1.1(ii))

R. Beuzart-Plessis, *A local trace formula for the Gan–Gross–Prasad conjecture for unitary groups:
the Archimedean case*, Astérisque 418 (2020) (arXiv:1506.01452). Setting: `F` a local field of
characteristic `0`, `G` a connected reductive group over `F` (Chapter 1); §4.1 is the `p`-adic case.
We apply it to `G = GSpin(W) × GSpin(V)` (and its inner forms `d.twist τ`, which are again of this
form), `G(F) = d.G`, `𝔤 = d.lie`.

**BP's definition (§4.1, Astérisque p. 73–74; arXiv p. 80–81).** For `Ω ⊆ G(F)` completely
`G(F)`-invariant and open, a quasi-character on `Ω` is a `G(F)`-invariant smooth function
`θ : Ω_reg → ℂ` such that for all `x ∈ Ω_ss` there are a `G_x`-excellent open neighbourhood `ω_x`
of `0` in `𝔤_x(F)` and coefficients `c_{θ,O}(x)`, `O ∈ Nil(𝔤_x)`, with
`θ(x e^Y) = ∑_{O ∈ Nil(𝔤_x)} c_{θ,O}(x) ĵ(O, Y)` for all `Y ∈ ω_{x,reg}`.

**Lean's `IsQuasiCharacter d.G d.lie d.bilin ψ θ` (with `Ω = G(F)`) gives such a `θ|_{G_reg}`.**
* Invariance: required on `G_reg(F)` in both. Only the values on `G_reg(F)` enter the conclusion
  below, so the values of the Lean `θ` off `G_reg(F)` play no role.
* Expansion: Lean asks for it at every semisimple `x` (`IsSS`, semisimplicity in the faithful
  representation on `C(W) × C(V)`), for `Y` in some neighbourhood `ω` of `0`, `Y ∈ 𝔤_x`, `Y` regular
  in `𝔤_x`, with finitely many nonzero coefficients (BP's `Nil(𝔤_x)` is finite). BP's condition
  follows. Let `V ⊆ 𝔤_x(F)` be the set of `Y` whose semisimple part is `G_x(F)`-conjugate to a
  semisimple element of `ω ∩ 𝔤_x`. The `G_x(F)`-saturation of `ω ∩ 𝔤_{x,ss}` is open in
  `𝔤_{x,ss}` (a union of conjugates of an open set), so `V` is the preimage of an open subset of
  `Γ(𝔤_x)`, i.e. open for the invariant topology (BP §1.7, arXiv p. 37), and it contains `0`. The
  `G_x`-excellent open sets containing `0` form a basis of neighbourhoods of `0` for that topology
  (BP §3.3, arXiv p. 74), so there is one, `ω_x ⊆ V`, which may also be taken inside the
  neighbourhood of `0` where `x e^Y` is regular iff `Y` is regular in `𝔤_x`. A regular
  `Y ∈ ω_x` is semisimple, so `Y = g Y' g⁻¹` with `g ∈ G_x(F)`, `Y' ∈ ω ∩ 𝔤_x` regular; as
  `θ` is invariant and `ĵ(O, ·)` is `G_x(F)`-invariant, `θ(x e^Y) = θ(x e^{Y'}) =
  ∑ c_O ĵ(O, Y') = ∑ c_O ĵ(O, Y)`. The orbits `Nil(𝔤_x)` are those of `Z_G(x)(F)` in Lean and of
  `G_x(F)` in BP; they agree, `Z_G(x)` being connected for `GSpin` (Steinberg: the derived group
  is simply connected).
* Smoothness: at regular `x`, `Nil(𝔤_x) = {0}` and `ĵ(0, ·) = 1`, so the Lean expansion and
  invariance make `θ` locally constant on `G_reg(F)`.
* `ĵ`: on `𝔤_{x,reg}` the Lean `jHat` is BP's `ĵ(O, ·)` when the measure `orbitMeasure` exists
  (then it is the Kirillov-normalized measure on `O`), and `0` otherwise: the self-dual measure on
  `𝔤_x(F)` exists (`exists_isSelfDual`; `b` is nondegenerate on `𝔤_x` by
  `restrictForm_lieCentralizer_nondegenerate`, GGP/Germs), so a representative continuous on the
  open set `𝔤_{x,reg}` is determined there. A zero `jHat` only removes terms from the expansion, so
  the Lean class is contained in BP's in either case. The normalization of `ĵ` (choice of `b`, `ψ`)
  rescales the `ĵ(O, ·)` and does not affect the class.
-/

open Topology

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **BP Astérisque 418, Proposition 4.1.1(ii)** (p. 74; arXiv:1506.01452, p. 81): "For all
`θ ∈ QC(G(F))` (resp. `θ ∈ QC(𝔤(F))`) the function `(D^G)^{1/2} θ` is locally bounded."
Only the group half is assumed. Here `F` is `p`-adic and `G = GSpin(W) × GSpin(V)` is connected
reductive; a Lean quasi-character is one of BP's (module docstring), and `D^G = weylDisc d.lie`
(`|det(1 − Ad z)|_{𝔤/𝔤_z}|_F` at semisimple `z`; the normalization of `|·|_F` does not affect
local boundedness). "Locally bounded on `G(F)`" for a function on `G_reg(F)`: every point of `G(F)`
has a neighbourhood on whose regular points the function is bounded. (BP's proof: the functions
`(D^G)^{1/2} ĵ(O, ·)` are locally bounded, Harish-Chandra, *Admissible invariant distributions on
reductive p-adic groups*, Thm 6.1, quoted in BP §1.8.) -/
axiom bp_sqrt_weylDisc_mul_locallyBounded (d : GGPData F) (ψ : NontrivialAddChar F)
    {θ : ↥d.G → ℂ} (hθ : IsQuasiCharacter d.G d.lie d.bilin ψ θ) (y : ↥d.G) :
    ∃ U ∈ 𝓝 y, ∃ C : ℝ, ∀ z ∈ U, z ∈ regularSet d.G d.lie →
      Real.sqrt (weylDisc d.lie (z : d.ambientˣ)) * ‖θ z‖ ≤ C

end GSpinGGP
