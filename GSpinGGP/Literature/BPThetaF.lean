/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.BPThetaF
import GSpinGGP.Literature.HarishChandra

/-!
# Cited properties of `θ_f` for a strongly cuspidal `f` (Waldspurger 2010, Beuzart-Plessis)

Sources.
* **W1**: J.-L. Waldspurger, *Une formule intégrale reliée à la conjecture locale de
  Gross–Prasad*, Compositio Math. 146 (2010) 1180–1290.  Cited with the page numbers of
  arXiv:0902.1875v1 ("arXiv p."); the Compositio page numbers have not been checked.  Setting
  (§1.1, arXiv p. 5): `F` non-archimedean of characteristic `0` (no condition on the residue
  characteristic), `G` a connected reductive group over `F`.
* **BP**: R. Beuzart-Plessis, *A local trace formula for the Gan–Gross–Prasad conjecture for
  unitary groups: the archimedean case*, Astérisque 418 (2020), printed page numbers.  Setting
  (§1.1): `F` `p`-adic or `ℝ`, `G` a connected reductive group over `F`.

Both define, for `f ∈ C_c^∞(G(F))` strongly cuspidal ("très cuspidale", W1 §5.1, arXiv p. 17;
BP §5.1, pp. 107–108) and `x ∈ G_reg(F)`,
`θ_f(x) = (−1)^{a_G − a_{M(x)}} ν(G_x)⁻¹ D^G(x)^{−1/2} J_{M(x)}(x, f)`
(W1 §5.3, arXiv p. 18, with the sign written `(−1)^{a_{M(x)} − a_G}`, the same number; BP §5.2,
p. 109).  The Lean form is `ReducedLeviDatum.thetaFBP`, and `GGPData.IsBPThetaF f θ` says `θ = θ_f`
on `G_reg(F)` for every special presentation (`TraceFormula/BPThetaF.lean`).

## Identification steps shared by the three axioms

These are identifications (our objects satisfy the sources' hypotheses, or are the sources' objects
in other notation).  Each axiom's docstring lists which it uses.

* **(I1) Group, field, function class.**  `G = GSpin(W) × GSpin(V)` (`d.G`) is connected
  reductive over the `p`-adic field `F`: a specialization of W1's and BP's `G`, not an adaptation.
  `f ∈ testFunctions ↥d.G` is `f ∈ C_c^∞(G(F))`; for `p`-adic `F`, `C_c^∞(G(F)) ⊆ 𝒞(G(F))`
  (BP §1.5, p. 25) and `C_c^∞(G(F)) ∩ 𝒞_scusp(G(F))` is the strongly cuspidal `C_c^∞` functions.
  `IsStronglyCuspidalInline d f` is W1 §5.1 / BP §5.1 strong cuspidality: `∫_{U(F)} f(pu) du = 0`
  for every proper parabolic `P = MU` and `p ∈ P(F)` (equivalently `x ∈ M(F)`, writing `p = mu'`),
  over the proper parabolics `whittB FW FV` given by pairs of isotropic flags (every parabolic of a
  product of `GSpin`s is of this form, Thesis §5.1.2); the same identification as in the docstring
  of `LitTF.bp_integrable_kernel_scusp`.
* **(I2) `dg` (homogeneity).**  W1 (§1.2, arXiv p. 7) and BP (§1.6, p. 30) fix `dg` through the
  exponential map; `Measure.haar = c · dg` for some `0 < c < ∞`.  `θ_f` has degree `1` in `dg`:
  `J_{M(x)}(x, f)` integrates over `G_x(F)\G(F)` for `dg/dt`, and `ν(G_x)⁻¹ (dg/dt) = dg/d_c t`
  with `d_c t` canonical (W1 §1.2, arXiv p. 7; BP §1.6), which is the measure `thetaFBP` uses
  (`dcMeasure`).  So `thetaFBP` (for `Measure.haar`) is `c · θ_f`.  Each statement below is
  invariant under this rescaling (stated case by case).
* **(I3) Special `K` in good position.**  `GoodK.IsSpecial K` for `K : d.GoodK L.toFlagLeviDatum`
  implies that `K` is a special maximal compact subgroup of `G(F)` in good position relative to
  `L.M` in the sense of W1 §1.1 (arXiv p. 5): W1 §7.1 (arXiv p. 34) and §7.2 (arXiv pp. 34–35),
  both **stated without proof in the source**, with the Bruhat–Tits identification written out in
  the module docstring of `GGP/SpecialK.lean`.  Only this direction is used.  (BP §1.10, p. 36 and
  §5.2, p. 109 only say "special"; BP Lemma 5.2.1 refers its proof to W1 for `p`-adic `F`, so the
  class used is W1's, special in good position.)  The positivity of `(H_P(g))_P` for such `K`
  (W1 §2.3, arXiv p. 9) makes `vM` Arthur's `v_M`; the measure on `a_M^G` is W1's (§1.2, arXiv
  p. 7: `A_M^G/proj_M(H_M(A_M(F)))` of volume `1`), which is the normalization of `vM`
  (`latticeMG`; see the docstring of `vM`).
* **(I4) `M(x)`.**  If `IsMx L x` then `L.M = M(x)`, the centralizer of `A_{G_x}` (W1 §5.3, BP
  §5.2): `x ∈ L.M` and `x` regular give `G_x ⊆ L.M` (`IsMx.centG_le`), so `A_M ⊆ A_{G_x}` (`A_M` is
  central in `M ⊇ G_x` and split); `A_{G_x}(F)/A_M(F)` is a closed subgroup of `G_x(F)/A_M(F)`,
  which is compact by `IsMx.compact`, and `A_{G_x}(F)/A_M(F) = (A_{G_x}/A_M)(F)` (Hilbert 90 for the
  split torus `A_M`), a split torus with compact group of `F`-points, hence trivial; so
  `A_{G_x} = A_M` and `M(x) = Z_G(A_M) = M`.  (The converse, existence of such `L`, is not used:
  each axiom quantifies over the presentations that exist.)
* **(I5) Presentation.**  `thetaFBP L K f x` reads `L` only through objects attached to `M = L.M`
  in the sources: the sign `(−1)^{dim a_M^G}` (`aMG`, `dim a_M^G = a_M − a_G`), `d_c t` on
  `G_x(F)` (through `A_M(F)`, `AMF`), and `J_M(x, f)` (`weightedOrbitalIntegral`, with Arthur's
  `v_M` for `K` by (I3); `vM` is the hull volume for the measure on `a_M^G` giving
  `a_M^G/proj_M(H_M(A_M(F)))` volume `1`, W1 §1.2, arXiv p. 7; BP §1.6, pp. 29–30, normalizes
  `a_M` and `a_G` instead, and the quotient measure is the same because `X_*(A_G)` is saturated in
  `X_*(A_M)`, as recorded in the docstring of `vM`).  The weight basis of `L` only constructs
  them.  So for `IsMx L x` and
  special `K`, `L.thetaFBP K f x` is W1's/BP's `θ_f(x)` computed with `K` (up to `c`, (I2)).
* **(I6) Regular set.**  `regularSet d.G d.lie` is `G_reg(F)` (`hcDisc_ne_zero_iff_mem_regularSet`);
  it is open and its complement is null (`hc_regular_open_dense_conull`), so a statement about
  `θ_f`, which is defined on `G_reg(F)` only, is a statement about any `θ` agreeing with it there.
-/

open MeasureTheory

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **W1 Lemme 5.2 (i), (ii) and Lemme 5.3** (Waldspurger, Compositio Math. 146 (2010); §5.2,
arXiv p. 17, and §5.3, arXiv p. 18; printed with proofs).

W1 §5.2 (arXiv p. 17), for `M` a Levi subgroup and `K` "un sous-groupe compact spécial de `G(F)` en
bonne position relativement à `M`": "Lemme. Soient `f ∈ C_c^∞(G(F))` et `x ∈ M(F) ∩ G_reg(F)`. On
suppose `f` très cuspidale. (i) L'intégrale orbitale pondérée `J_M(x, f)` ne dépend pas de `K`.
(ii) Pour tout `y ∈ G(F)`, on a l'égalité `J_M(x, ^y f) = J_M(x, f)`."  W1 §5.3 (arXiv p. 18)
defines `θ_f` (see the module docstring) and states: "Lemme. La fonction `θ_f` est invariante par
conjugaison, à support compact modulo conjugaison, localement intégrable sur `G(F)` et localement
constante sur `G_reg(F)`."

The statement, for `f ∈ C_c^∞(G(F))` strongly cuspidal:
1. for regular `x`, `y ∈ G(F)`, presentations `L` of `M(x)` and `L'` of `M(y x y⁻¹)` and special
   `K`, `K'` in good position relative to them, `θ_f` computed with `(L', K')` at `y x y⁻¹` equals
   `θ_f` computed with `(L, K)` at `x`;
2. every `θ` agreeing with `θ_f` on `G_reg(F)` (`IsBPThetaF f θ`) is locally integrable on `G(F)`
   and continuous on `G_reg(F)`.

Derivation (identification steps, module docstring):
* (I1) for `G` and `f`; (I3) for `K`, `K'`; (I4) for `L.M = M(x)`, `L'.M = M(y x y⁻¹)`; (I5).
* Conjunct 1 with `y = 1`: by (I4), `L.M = L'.M = M(x)`, and by (I5) both sides are `θ_f(x)`
  computed with `K` and `K'`, equal by Lemme 5.2(i) (this is W1's remark "Cette définition est
  loisible d'après le (i) du lemme précédent").  General `y`: W1 5.3 "invariante par conjugaison"
  (its proof: `M(yxy⁻¹) = yM(x)y⁻¹`, transport of structure, and 5.2(ii)).
* (I2): conjunct 1 is an equality of two values of `c · θ_f`; conjunct 2 is unchanged when `θ` is
  multiplied by `c > 0`.
* Conjunct 2: (I6) moves W1's statements about `θ_f` to any `θ` equal to it on `G_reg(F)`
  (local integrability only sees `θ` almost everywhere; continuity on the open set `G_reg(F)`
  only sees `θ` there).  `ContinuousOn` is weaker than W1's local constancy, and the support
  clause is dropped: the statement is weaker than print.

**Guard.**  Conjunct 2 has the hypothesis `IsBPThetaF`, which is unsatisfiable if `IsSpecial` were
too strict or too loose (`not_isBPThetaF_of_not_exists`, `not_isBPThetaF_of_ne`).  Conjunct 1 is a
bare `∀` over special presentations: it relies on (I3), i.e. on `IsSpecial` admitting only
special `K` in good position.  That is the soundness direction of the definition of `IsSpecial`
(W1 §7.1–7.2 with the Bruhat–Tits identification); it is tested on `gl2Data`, where a `GoodK` that
is not special and lattices that are not special are excluded (`Sanity/GL2SpecialK.lean`). -/
axiom waldspurger2010_lemme_5_3 (d : GGPData F) {f : ↥d.G → ℂ} (hf : f ∈ testFunctions ↥d.G)
    (hcusp : IsStronglyCuspidalInline d f) :
    (∀ (x y : ↥d.G) (L L' : d.ReducedLeviDatum) (K : d.GoodK L.toFlagLeviDatum)
        (K' : d.GoodK L'.toFlagLeviDatum), L.IsMx x → L'.IsMx (y * x * y⁻¹) →
        K.IsSpecial → K'.IsSpecial → L'.thetaFBP K' f (y * x * y⁻¹) = L.thetaFBP K f x) ∧
    ∀ θ : ↥d.G → ℂ, d.IsBPThetaF f θ →
      LocallyIntegrable θ (Measure.haar : Measure ↥d.G) ∧ ContinuousOn θ (regularSet d.G d.lie)

/-- **W1 Corollaire 5.9** (Waldspurger, Compositio Math. 146 (2010), §5.9, arXiv p. 26; printed
with proof): "Corollaire. Soit `f ∈ C_c^∞(G(F))`. Supposons `f` très cuspidale. Alors la fonction
`θ_f` est un quasi-caractère."

W1's definition (§4.1, arXiv pp. 15–16): a function `θ` defined almost everywhere on `G(F)` and
invariant by conjugation is a quasi-character if for every `x ∈ G_ss(F)` there are a good
neighbourhood `ω` of `0` in `𝔤_x(F)` (§3.1, arXiv p. 13) and `c_{θ,O}(x) ∈ ℂ`, `O ∈ Nil(𝔤_x)`, with
`θ(x exp X) = Σ_O c_{θ,O}(x) ĵ(O, X)` for almost every `X ∈ ω`; then `θ` is locally constant on
`G_reg(F)` (§4.1, arXiv p. 16).

The statement: every `θ` with `IsBPThetaF f θ` satisfies `IsQuasiCharacter d.G d.lie d.bilin ψ θ`
for every nontrivial `ψ`.  Derivation:
* (I1), (I3), (I4), (I5): `θ = c · θ_f` on `G_reg(F)` (I2), and `c · θ_f` is a quasi-character
  (W1's definition is linear).
* Invariance clause of `IsQuasiCharacter` (for regular `y`): `θ_f` is invariant (W1 §5.3 Lemme)
  and `G_reg(F)` is stable under conjugation (`conj_mem_regularSet`).
* Expansion clause at semisimple `x` (`HasGermExpansion`):
  - the coefficients are indexed by `NilOrbit (grpCentralizer d.G x) …`, the nilpotent orbits of
    `Z_G(x)(F)` in `𝔤_x(F)`; `Z_G(x) = G_x` because the derived group `Spin(W) × Spin(V)` is
    simply connected (Steinberg, Mem. AMS 80 (1968), Thm 8.1; `steinberg_centralizer_connected`),
    and `Nil(𝔤_x)` is finite (W1 sums over it), so `c` has finite support;
  - from almost every `X ∈ ω` to every `X ∈ ω` regular in `𝔤_x`: by W1 §3.1 (good neighbourhoods)
    `x exp X ∈ G_reg(F)` for such small `X` (here `exists_nhds_mul_expA_mem_regularSet`), where
    `θ` is locally constant (W1 §4.1, arXiv p. 16) and `ĵ(O, ·)` is a smooth, i.e. locally
    constant, function on the regular set (BP §1.8, p. 34, after Harish-Chandra; `IsJHat` asks
    continuity there); both sides are continuous on an open set
    on which they agree almost everywhere, and Haar measure charges every nonempty open set, so they
    agree there;
  - `ω` is a neighbourhood of `0` in `𝔤_x(F)`, hence the trace of a neighbourhood of `0` in the
    ambient algebra;
  - normalization of `ĵ`: `jHat` is normalized by `d.bilin` and `ψ`; another invariant form,
    character or measure rescales and permutes the `ĵ(O, ·)` (as recorded for
    `hc_character_isQuasiCharacter_admissible`), which is absorbed into the coefficients, so the
    statement holds for every `ψ`.
* (I6): `IsQuasiCharacter` only reads `θ` on `G_reg(F)` (its invariance clause is for regular `y`,
  and its expansion is evaluated at `x exp X ∈ G_reg(F)`), so it holds for any `θ` agreeing with
  `c · θ_f` there.

The same conclusion is printed in BP Prop 5.6.1(ii) (p. 117: "Let `f ∈ 𝒞_scusp(G(F))`. Then, the
function `θ_f` is a quasi-character on `G(F)`"), with BP's pointwise definition (§4.1, p. 74:
the expansion holds "for all `Y ∈ ω_{x,reg}`"); BP's proof of (ii) uses Thm 5.5.1(iv)–(v), so W1's
proved corollary is the anchor here.

As for `hc_character_isQuasiCharacter_admissible`, the statement presupposes that `ĵ(O, ·)` exists
(`jHat` is defined by choice, `0` otherwise); Harish-Chandra proves it. -/
axiom waldspurger2010_cor_5_9 (d : GGPData F) {f : ↥d.G → ℂ} (hf : f ∈ testFunctions ↥d.G)
    (hcusp : IsStronglyCuspidalInline d f) :
    ∀ θ : ↥d.G → ℂ, d.IsBPThetaF f θ → ∀ ψ : NontrivialAddChar F,
      IsQuasiCharacter d.G d.lie d.bilin ψ θ

/-- **BP Thm 5.5.1(iv)** (Beuzart-Plessis, Astérisque 418, §5.5, p. 116).  BP p. 116: "(iv) We have
the geometric expansion `J^A(f, f') = ∫_{Γ(G)} D^G(x)^{1/2} θ_f(x) J_G(x, f') dx` for all
`f ∈ 𝒞_scusp(G(F))` and all `f' ∈ 𝒞(G(F))`, the integral above being absolutely convergent", with
(p. 115–116) `K^A_{f,f'}(g₁, g₂) = ∫_{G(F)} f(g₁⁻¹ g g₂) f'(g) dg` and
`J^A(f, f') = ∫_{A_G(F)\G(F)} K^A_{f,f'}(x, x) dx`.  **Stated without proof in the source**: "The
proof of these two theorems will appear elsewhere [18]" (p. 116), [18] being R. Beuzart-Plessis,
*A slight variation of Arthur local trace formula*, in preparation.

The statement: there is a family `μ` of Haar measures on the maximal tori such that for
`f ∈ C_c^∞(G(F))` strongly cuspidal, every `θ` with `IsBPThetaF f θ` and every `f' ∈ C_c^∞(G(F))`,
the torus integrals of `D^{1/2} θ J_G(·, f')` converge absolutely, their sum over `𝒯(G)` converges
absolutely, and `jA f f' = gammaIntegral μ (thetaWeylIntegrand μ θ f')`.

Derivation (identification steps):
* (I1) for `G`, `f`, `f'` (`C_c^∞ ⊆ 𝒞`); (I3)–(I5) for `θ = c · θ_f` on `G_reg(F)` (BP §5.2, p. 109;
  BP's `θ_f` does not depend on `K`, Lemma 5.2.1(ii)).
* **`J^A`.**  `kernelA` is `K^A` for `dg = Measure.haar`; `jA` integrates it over
  `A_G(F)\G(F) = G(F)/A_G(F)` (`A_G` central) for `measGmodAG = dg/d_c a`.  BP does not state the
  measure on `A_G(F)`; we read it with Arthur's convention, `d_c a` giving the maximal compact
  subgroup of `A_G(F)` measure `1` (J. Arthur, Publ. Math. IHÉS 73 (1991), §1, p. 11; also
  Waldspurger, J. reine angew. Math. 465 (1995), §1.4): **flagged, BP leaves it unstated.**  It is
  the only Haar measure on `A_G(F)` for which (iv) can hold (both sides scale differently under it),
  and it is the one tested at the toy datum (`toyD_jA_geom`).  `measGmodAG` is
  `dcScaleAG • Measure.haar` with `dcScaleAG` chosen by choice; its specification is proved
  (`isDcQuotientAG_measGmodAG`, from `weil_quotient_radon` only), so no existence is hidden.
* **(I2), `dg` homogeneity.**  With `Measure.haar = c · dg`: `kernelA` is `c` times BP's,
  `measGmodAG = (c · dg)/d_c a` is `c` times BP's, so `jA` is `c²` times BP's `J^A`; on the right,
  `J_G(t, f')` (`orbitalIntegralOn`, for `dg/μ_T`) is `c` times BP's and `θ = c · θ_f`, so the
  right side is `c²` times BP's.  The equality is equivalent to BP's.
* **`Γ(G)` and `dx`** (BP §1.7, p. 32: `∫_{Γ(G)} φ(x) dx = Σ_{T ∈ 𝒯(G)} |W(G,T)|⁻¹ ∫_{T(F)} φ(t) dt`):
  the identifications 3, 5, 6 and 7 of the docstring of `weyl_integration_exists` (unfolding `dx`
  for integrable `φ`; `MaxTorus`/`MaxTorusClass` as BP's maximal tori up to `G(F)`-conjugacy;
  `weylCardG = |W(G,T)|`, `weylDisc = D^G`, `orbitalIntegralOn = J_G` (BP §1.8, p. 33); the
  singular set of each torus is null and `thetaWeylIntegrand` is `0` there).
* **Torus measures (the `∃`).**  BP's `dt` (§1.6, p. 30) is a Haar measure on each `T(F)`; it is
  the witness.  The left side, `IsBPThetaF` and `thetaFBP` (which uses `d_c t`) do not involve
  `μ`, and the right side is independent of the Haar family
  (`gammaIntegral_thetaWeylIntegrand_eq`), so the form for every family is a theorem
  (`jA_eq_gammaIntegral`).
* **"Absolutely convergent".**  For BP's integrand on `Γ(G)`, absolute convergence means
  `∫_{T(F)} |D^{1/2} θ_f J_G(·, f')| dt < ∞` for each `T ∈ 𝒯(G)` and summability of the weighted
  sum over the finitely many `T`; the inner integral of `J_G(t, f')` over `G_t(F)\G(F)` is
  absolutely convergent for `t ∈ G_reg(F)` (BP §1.8, p. 33: "the integral being absolutely
  convergent for all `f ∈ 𝒞(G(F))`"), so `orbitalIntegralOn` is not a junk value either;
  measurability: `θ_f` is locally constant on `G_reg(F)` (W1 §5.3)
  and `t ↦ D^{1/2} J_G(t, f')` is locally constant on `T_reg(F)` (Harish-Chandra).  These are the
  `Integrable` and `Summable` conjuncts; with them Lean's Bochner integrals and `tsum` are BP's
  integrals and sum, not junk values.

The statement is no stronger than BP's: BP's (iv), for its `dg`, `dt` and `θ_f`, implies it with
`μ = dt`.  `IsBPThetaF` has an existence and a universal half, so that a wrong `IsSpecial` makes the
hypothesis unsatisfiable rather than the statement false. -/
axiom bp_thm_5_5_1_iv (d : GGPData F) :
    ∃ μ : ∀ T : Subgroup ↥d.G, Measure ↥T, (∀ T : d.MaxTorus, (μ T.1).IsHaarMeasure) ∧
      ∀ f ∈ testFunctions ↥d.G, IsStronglyCuspidalInline d f →
      ∀ θ : ↥d.G → ℂ, d.IsBPThetaF f θ →
      ∀ f' ∈ testFunctions ↥d.G,
        (∀ c : d.MaxTorusClass, Integrable
            (fun t : ↥(Quot.out c).1 => d.thetaWeylIntegrand μ θ f' (Quot.out c).1 t)
            (μ (Quot.out c).1)) ∧
        Summable (fun c : d.MaxTorusClass => ((weylCardG d (Quot.out c).1 : ℝ))⁻¹ *
            ∫ t, ‖d.thetaWeylIntegrand μ θ f' (Quot.out c).1 t‖ ∂μ (Quot.out c).1) ∧
        d.jA f f' = d.gammaIntegral μ (d.thetaWeylIntegrand μ θ f')

end GSpinGGP
