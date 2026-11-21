/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.W1Lie

/-!
# Waldspurger 2010, Théorème 7.9: the integral formula on the Lie algebra

One literature axiom, `waldspurger2010_thm_7_9` (derived: a composite of Waldspurger's theorem with
Beuzart-Plessis Thm 5.5.2(ii) and the Weyl integration formula, which pin down his `θ_f`):
Waldspurger's Lie-algebra integral formula for the pair `(SO(V), SO(W))`, with his truncated
integrals `I_N(θ, f)`.  The objects are
those of `TraceFormula/W1Lie.lean`, defined on the quadratic spaces of a `LuoDatum`.
-/

open MeasureTheory Topology Filter

noncomputable section

namespace GSpinGGP

open LuoDatum

/-- **Waldspurger 2010, Théorème 7.9: `lim_{N→∞} I_N(θ, f) = I(θ, f)`** (composite axiom: W1
Thm 7.9, with `θ_f` pinned down through Beuzart-Plessis Thm 5.5.2(ii) and the Weyl integration
formula; the steps are written out under "Composite" below).

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

**Composite (derived axiom; listed in `scripts/derived-axioms.txt`).**  W1's `θ_f` is defined on
`𝔤_reg(F)` by weighted orbital integrals,
`θ_f(X) = (−1)^{a_{M(X)} − a_G} ν(G_X)^{-1} D^G(X)^{-1/2} J_{M(X)}(X, f)` (§6.1, p. 27), which are
not formalized.  The axiom is stated for every `τ` with `IsThetaFW1` (a locally integrable
quasi-character, continuous on `𝔤_reg(F)`, with `∫ τ f' dX = ∫_{G(F)} ∫_{𝔤(F)} f(g⁻¹Xg) f'(X) dX dg`
for every test function `f'`).  From W1 Thm 7.9 for W1's `θ_f` to this statement:
1. **W1 Thm 7.9** (quoted above) for `θ`, `f` and W1's measures.
2. **Beuzart-Plessis, Astérisque 418 (2020), Thm 5.5.2(ii)** (p. 117; arXiv:1506.01452 p. 127),
   for the connected reductive group `G = SO(V)` (here `A_G = 1`, as `V` is not a hyperbolic
   plane): "`J^A(f, f') = ∫_{Γ(𝔤)} D^G(X)^{1/2} θ_f(X) J_G(X, f') dX`", absolutely convergent, with
   `J^A(f, f') = ∫_{G(F)} ∫_{𝔤(F)} f(g⁻¹Xg) f'(X) dX dg`.  **Announced without proof in its
   source** ("The proof of these two theorems will appear elsewhere", BP p. 116).  BP's `θ_f`
   (§5.2) is given by the same formula as W1's (BP follows W1).
3. **Weyl integration formula** on `𝔤` (BP §1.7, arXiv p. 38): `θ_f` is conjugation-invariant, so
   `J_G(X, θ_f f') = θ_f(X) J_G(X, f')` and 2 becomes `∫ θ_f f' dX = J^A(f, f')`: W1's `θ_f` has
   the property `IsThetaFW1`.
4. **`τ = θ_f` on `𝔤_reg(F)`**: two locally integrable functions with the same integrals against
   all test functions agree almost everywhere; both are continuous on the open set `𝔤_reg(F)`,
   which has full measure, so they agree there.
5. **Equal germs**: `c_f(Y) = c_{θ_f, O}(Y)` depends only on the values on regular elements near
   `Y`, by the uniqueness of the regular coefficients of local expansions on `(SO(V), so(V))`
   (W1 §4.1–4.2; Harish-Chandra 1999 Cor 5.10), so `I(θ, τ) = I(θ, θ_f)`.
6. **Rescaling `μG`**: W1 fixes all measures (§1.2); replacing `μG` by `c μG` multiplies both
   sides by `c` (on the left through the quotient measure, on the right through `τ`), so the
   statement for an arbitrary Haar measure is equivalent to W1's.
Steps 4–6 are identifications.  Once `θ_f` is defined in this project, the axiom splits into W1
Thm 7.9 for `θ_f` (verbatim) and BP Thm 5.5.2(ii) (verbatim, flagged), and this statement becomes
a theorem.

**How the statement is encoded.**
* `θ_f`, `ĵ` and the germs use `germLie`/`jHat` of this project for `(SO(V), so(V))` and
  `(SO(W), so(W))` with W1's form.  The orbit recipes for `c_θ`, `c_f` are W1 §7.3 at
  `Y ∈ 𝔱_♮(F)` (Lie version, §7.9); `O_{±ν₀}` are `IsInOrbitNu … (±nu0)` (W1's `ν₀ = ½ Q(z₀)`, and
  `IsInOrbitNu` measures the anisotropic line by `Q`, so the factor `½` cancels).
* `𝒯` (§7.3 conditions (1)–(4)): parameterized by `Y ∈ 𝔥(F)` semisimple with `T_Y` commutative
  with compact `F`-points (`A_T = 1`) and condition (4) (`IsW1Elt`), as for Luo's `GammaTorus`.
* Measures: `μG` is an arbitrary Haar measure on `G(F)` (step 6).  The measures on `𝔥(F)` and `𝔲(F)` are deduced through
  `exp` from those on `H(F)` and `U(F)` (§1.2), and `U(F)H(F)` carries `du dh`; only their ratios
  enter.  `ν(T) dY` is deduced through `exp` from `d_c t = ν(T) dt`, of total mass `1` on `T(F)`
  when `A_T = 1` (§1.2).
* `I_N` integrates over representatives of `U(F)H(F)\G(F)`; `I(θ, f, ·)` and `κ_N` are left
  `U(F)H(F)`-invariant (W1 §7.2 for `κ_N`).
* `IsNondeg L.QV`: W1's `V` is nondegenerate; `W` is (`LuoDatum.nondeg`).
* `¬ IsHypPlane L.QV`: the case `V = V₀` a hyperbolic plane (`d = 2`, `r = 0`, `d_W = 1`) is
  excluded, because W1's printed statement fails there (our computation, not stated in W1):
  `G = SO(V) ≅ G_m` is a split torus, `H = U = 1`, every `f` is very cuspidal,
  `I(θ, f, g) = θ(0) f(0)` for all `g`, and `I_N(θ, f)` is `θ(0) f(0)` times the volume of
  `{κ_N = 1}`, which grows linearly in `N`; so the limit is not finite unless `θ(0) f(0) = 0`.
  The statement is only used with `dim V ≥ 3`.

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
