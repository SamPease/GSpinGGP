/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.W1Lie

/-!
# Waldspurger 2010, Théorème 7.9: the integral formula on the Lie algebra

One literature axiom, `waldspurger2010_thm_7_9`, verbatim: Waldspurger's Lie-algebra integral
formula for the pair `(SO(V), SO(W))`, with his truncated integrals `I_N(θ, f)`.  The objects are
those of `TraceFormula/W1Lie.lean`, defined on the quadratic spaces of a `LuoDatum`.
-/

open MeasureTheory Topology Filter

noncomputable section

namespace GSpinGGP

open LuoDatum

/-- **Waldspurger 2010, Théorème 7.9: `lim_{N→∞} I_N(θ, f) = I(θ, f)`.**

Source: J.-L. Waldspurger, *Une formule intégrale reliée à la conjecture locale de Gross–Prasad*,
Compositio Math. 146 (2010) 1180–1290; arXiv:0902.1875v1, §7.9, p. 43 (page numbers of the arXiv
version): "Pour tout quasi-caractère `θ` sur `h(F)` et toute fonction très cuspidale
`f ∈ C_c^∞(g(F))`, on a l'égalité `lim_{N→∞} I_N(θ, f) = I(θ, f)`."  Proved in §12.3 (via
Lemme 12.1 and the induction of §12.1–§12.3; §11.5 treats `d` odd with `d_W ≤ 2` and `d_W ≥ 4`
separately).  The absolute convergence of `I(θ, f)` is asserted in §7.9 ("Une analogue de la
proposition 7.3 entraîne l'absolue convergence de cette expression").

**Setting (W1 §1.1, §7.1, §7.2, verbatim).**  `F` is a non-archimedean local field of
characteristic `0` (`PAdicField`; W1 §1.1 makes no assumption on the residue characteristic).
`V` is a nondegenerate quadratic space of dimension `d`, `V = W ⊕ D ⊕ Z` orthogonal with `D` a
line and `Z` hyperbolic of dimension `2r` (`LuoDatum`: `D = F z₀`, `(z_i)_{1 ≤ |i| ≤ r}` a
maximal hyperbolic system of `Z`, W1's `v_i`), `G = SO(V)`, `H = SO(W)` acting trivially on
`D ⊕ Z`, `U` and `ξ` as in §7.2 with arbitrary `ξ_i ∈ F^×`, `K` the stabilizer of a special lattice
`R = R₀ ⊕ R_Z` and `κ_N` as in §7.2, the form `⟨X, Y⟩ = ½ trace(XY)` (§7.1) and `ψ`.
Every dimension `d_W = dim W ≥ 0` is allowed (in particular `W` a hyperbolic plane).

**Objects (W1 §7.3, §7.9).**  `I_N(θ, f) = ∫_{U(F)H(F)\G(F)} I(θ, f, g) κ_N(g) dg` with
`I(θ, f, g) = ∫_{𝔥(F)} θ(Y) ∫_{𝔲(F)} f(g⁻¹(Y + N)g) ξ(N) dN dY` (`W1Input.IN`), and
`I(θ, f) = Σ_{T ∈ 𝒯} |W(H, T)|⁻¹ ν(T) ∫_{𝔱(F)} c_θ(Y) c_f(Y) D^H(Y) Δ(Y)^r dY` (`W1Input.Igeom`),
with `c_f = c_{θ_f}` (§7.9), `θ_f` the quasi-character of §6.1.

**How the statement is encoded.**
* `θ_f`: W1 defines `θ_f(X) = (−1)^{a_{M(X)} − a_G} ν(G_X)^{-1} D^G(X)^{-1/2} J_{M(X)}(X, f)` on
  `𝔤_reg(F)` (§6.1); weighted orbital integrals are not formalized.  The statement is made for any
  `τ` satisfying `IsThetaFW1` (a continuous, locally integrable quasi-character on `𝔤_reg(F)`
  representing the orbital pairing of `f`).  W1 §6.1 (2) gives `J(φ̂, f) = ∫ φ̂ θ_f` for the
  geometric side `J` of the local trace formula on `𝔤`; with `J` written as the kernel integral
  `∫_{G(F)} ∫_{𝔤(F)} φ(X) f(g⁻¹Xg) dX dg` this says that `θ_f` has the property, and a continuous
  function on `𝔤_reg(F)` with it agrees with `θ_f` there (the germs `c_f` only see
  `𝔤_reg(F)`).  This
  identification is the step used in conjunct (b) of `luo_lie_geomExpansion_SO`; it is **not
  printed in this form**.  It enters only as a hypothesis on `τ`: for the true `θ_f` the statement
  is W1's.
* `θ_f`, `ĵ` and the germs use `germLie`/`jHat` of this project for `(SO(V), so(V))` and
  `(SO(W), so(W))` with W1's form.  The orbit recipes for `c_θ`, `c_f` are W1 §7.3 at
  `Y ∈ 𝔱_♮(F)` (Lie version, §7.9); `O_{±ν₀}` are `IsInOrbitNu … (±nu0)` (W1's `ν₀ = ½ Q(z₀)`, and
  `IsInOrbitNu` measures the anisotropic line by `Q`, so the factor `½` cancels).
* `𝒯` (§7.3 conditions (1)–(4)): parameterized by `Y ∈ 𝔥(F)` semisimple with `T_Y` commutative
  with compact `F`-points (`A_T = 1`) and condition (4) (`IsW1Elt`), as for Luo's `GammaTorus`.
* Measures: W1 fixes all measures (§1.2).  Here `μG` is an arbitrary Haar measure on `G(F)`, and
  `θ_f` is the representative for `μG`; replacing `μG` by `c μG` multiplies both sides by `c`
  (on the left through the quotient measure, on the right through `θ_f`), so the statement for
  arbitrary `μG` is equivalent to W1's.  The measures on `𝔥(F)` and `𝔲(F)` are deduced through
  `exp` from those on `H(F)` and `U(F)` (§1.2), and `U(F)H(F)` carries `du dh`; only their ratios
  enter.  `ν(T) dY` is deduced through `exp` from `d_c t = ν(T) dt`, of total mass `1` on `T(F)`
  when `A_T = 1` (§1.2).
* `I_N` integrates over representatives of `U(F)H(F)\G(F)`; `I(θ, f, ·)` and `κ_N` are left
  `U(F)H(F)`-invariant (W1 §7.2 for `κ_N`).
* `IsNondeg L.QV`: W1's `V` is nondegenerate; `W` is (`LuoDatum.nondeg`).
* `¬ IsHypPlane L.QV`: the case `V = V₀` a hyperbolic plane (`d = 2`, `r = 0`, `d_W = 1`) is
  excluded.  W1 flags it (§7.2: "`A_M = A`, sauf dans le cas où `V₀` est hyperbolique de dimension
  2, auquel cas `A_M = M`"): there `G = SO(V) ≅ G_m` is a split torus, `H = U = 1`, every `f` is
  very cuspidal, `I(θ, f, g) = θ(0) f(0)` for all `g`, and `I_N(θ, f)` is `θ(0) f(0)` times the
  volume of `{κ_N = 1}`, which grows with `N`; so the limit is not finite unless
  `θ(0) f(0) = 0`.  The statement is only used with `dim V ≥ 3`.

**Hypotheses checked.**  `F` `p`-adic of characteristic `0`: `PAdicField`.  `2r + 1 ≤ d`: by
construction.  `θ` a quasi-character on `𝔥(F)` (`IsLieQuasiCharacter` for `(SO(W), so(W))`, W1
§4.1/§6 sense: local expansions in the `ĵ(O, ·)` at every semisimple point).  `f` very cuspidal
in `C_c^∞(𝔤(F))` (`IsVeryCuspidal`, W1 §6.1 (1)). -/
axiom waldspurger2010_thm_7_9 {F : Type} [NontriviallyNormedField F] [PAdicField F]
    (L : LuoDatum F) (hV : IsNondeg L.QV) (hV2 : ¬ IsHypPlane L.QV) (ψ : NontrivialAddChar F)
    (I : L.W1Input ψ)
    (θ : ↥L.soW → ℂ) (hθ : IsLieQuasiCharacter L.SOW L.soW L.bW ψ θ)
    (f : ↥L.soV → ℂ) (hf : L.IsVeryCuspidal f)
    (τ : ↥L.soV → ℂ) (hτ : L.IsThetaFW1 ψ I.μG f τ) :
    Tendsto (I.IN θ f) atTop (𝓝 (I.Igeom θ τ))

end GSpinGGP
