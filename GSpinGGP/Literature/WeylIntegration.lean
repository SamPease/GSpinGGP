/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.GammaG

/-!
# The Weyl integration formula (cited: Beuzart-Plessis, Astérisque 418, §1.7, p. 32)

R. Beuzart-Plessis, *A local trace formula for the Gan–Gross–Prasad conjecture for unitary groups:
the Archimedean case*, Astérisque 418 (2020). Setting (Chapter 1): `F` a local field of
characteristic `0`, `G` a connected reductive group over `F`. BP states the formula without proof,
as a standard result (Harish-Chandra).

The axiom is stated with the Lean objects of `TraceFormula/GammaG.lean` (`MaxTorus`,
`MaxTorusClass`, `gammaIntegral`, `weylIntegrand`); its docstring lists the identifications with
BP's objects. The form for every family of Haar measures on the tori is a theorem,
`GGPData.weyl_integration` (`TraceFormula/WeylIntegration.lean`).
-/

open MeasureTheory

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **The Weyl integration formula** (Beuzart-Plessis, Astérisque 418, §1.7, p. 32; Harish-Chandra).
BP p. 32, after defining the measure `dx` on `Γ(G)`: "We have the Weyl integration formula
`∫_{G(F)} f(g) dg = ∫_{Γ(G)} D^G(x)^{1/2} J_G(x, f) dx` for all `f ∈ S(G(F))`", where (same page)
`∫_{Γ(G)} φ(x) dx = Σ_{T ∈ 𝒯(G)} |W(G,T)|⁻¹ ∫_{T(F)} φ(t) dt` for `φ ∈ C_c(Γ(G))`, `𝒯(G)` a set of
representatives of the conjugacy classes of maximal tori, and (§1.8, p. 33)
`J_G(x, f) = D^G(x)^{1/2} ∫_{G_x(F)\G(F)} f(g⁻¹ x g) dg` for `x ∈ G_reg(F)`.
**Stated without proof in the source** (a standard result of Harish-Chandra).

A *derived* axiom: BP's printed statement, for the connected reductive group
`G = GSpin(W) × GSpin(V)` over the `p`-adic field `F` (`d.G`), with the following identification
steps, each an equivalence except (4), which weakens the statement.

1. **Group and test functions.** BP's `G` is any connected reductive group over a local field of
   characteristic `0`, so this is a specialization, not an adaptation. For `p`-adic `F`,
   `S(G(F)) = C_c^∞(G(F))` (BP §1.4, p. 23), which is `testFunctions ↥d.G` (locally constant,
   compactly supported).
2. **`dg` (homogeneity).** BP fixes `dg` in §1.6 (p. 30); here `Measure.haar = c · dg` for some
   `0 < c < ∞`. The left side has degree `1` in `dg`. On the right, `dx` involves only the measures
   `dt` on the tori, and `J_G(x, f)` integrates over `G_x(F)\G(F)` for the quotient measure `dg/dt`,
   which has degree `1` in `dg`. So both sides are multiplied by `c`, and the formula for `dg` is
   equivalent to the formula for `Measure.haar`.
3. **Unfolding `dx`.** BP defines `dx` by the torus sum on `C_c(Γ(G))`. Both `dx` and
   `Σ_T |W(G,T)|⁻¹ (image of dt)` are regular Borel measures on `Γ(G)` (`T(F) → Γ(G)` is continuous
   and proper, BP §1.7, p. 31), so they are equal, and the torus sum computes `∫_{Γ(G)} φ dx` for
   every `dx`-integrable `φ`, in particular for `φ = (D^G)^{1/2} J_G(·, f)` (see 8).
4. **Torus measures (the `∃`).** BP's `dt` on `T(F)` (§1.6, p. 30: the autodual measure of
   `𝔱(F)`, lifted by the exponential) is a Haar measure. The witness is `μ (T(F)) = dt` on the
   tori of `𝒯(G)` and anything on other subgroups (`gammaIntegral` and `weylIntegrand` only read
   `μ` on the representatives `Quot.out c`). The axiom does not say which Haar measure.
5. **`𝒯(G)` (maximal tori as centralizers).** `MaxTorus` is the set of `T(F) = G_x(F)` (`centG x`)
   for `x ∈ G_reg(F)`. For regular semisimple `x`, `Z_G(x)` is a maximal torus `T`, connected by
   Steinberg's theorem (the derived group `Spin(W) × Spin(V)` is simply connected), so
   `centG x = Z_G(x)(F) = T(F)`. Conversely, for a maximal torus `T`, `T(F)` is Zariski dense in `T`
   (`F` of characteristic `0`) and `T_reg` is open dense in `T`, so `T(F)` contains some regular
   `x`, and `T = Z_G(x)`; `G_t(F) = T(F)` for every regular `t ∈ T(F)`
   (`centG_eq_of_mem_regularSet`). By density `T ↦ T(F)` is injective and respects
   `G(F)`-conjugacy, so `MaxTorusClass` is BP's set of conjugacy classes of maximal tori, and the
   representatives `Quot.out c` are one choice of `𝒯(G)`.
6. **`|W(G,T)|`, `D^G`, `J_G`.** `weylCardG d T = |N_{G(F)}(T(F))/T(F)|` is BP's
   `|Norm_{G(F)}(T)/T(F)|` (the normalizers agree by density); it is finite, so not the junk value
   `0`. `weylDisc` is `D^G`. For regular `t ∈ T(F)`, `orbitalIntegralOn T (μ T) t f` is
   `J_G(t, f)` for `dg/μ_T` (BP §1.8, p. 33; `G_t(F) = T(F)` by 5, and `quotMeasureOn` is the Weil
   quotient `dg/μ_T`, `MaxTorus.quotMeasureOn_spec`).
7. **The regular set.** BP's `J_G` is defined on `G_reg(F)`; `weylIntegrand` is `0` off it. The
   singular elements of `T(F)` are the zeros of the nonzero analytic function `D^G` on `T(F)`, a
   `dt`-null set.
8. **Lean's integrals and sum are BP's.** BP's integrals converge absolutely: the inner integral
   by BP §1.8 (p. 33), and the outer ones because `|J_G(x, f)| ≤ J_G(x, |f|)` and
   `|f| ∈ C_c^∞(G(F))` (`F` is `p`-adic), so BP's formula for `|f|` bounds
   `∫_{Γ(G)} D^{1/2} |J_G(·, f)| dx` by `∫ |f| dg < ∞`. Hence the integrand is integrable on each
   `T(F)` and the terms of the sum over `𝒯(G)` are absolutely summable, so Lean's Bochner integrals
   and `tsum` (which give `0` on non-integrable or non-summable input) agree with BP's.

The statement is therefore no stronger than BP's: BP's formula for its `dg` and `dt` implies it,
with BP's `dt` as the witness. -/
axiom weyl_integration_exists (d : GGPData F) :
    ∃ μ : ∀ T : Subgroup ↥d.G, Measure ↥T, (∀ T : d.MaxTorus, (μ T.1).IsHaarMeasure) ∧
      ∀ f ∈ testFunctions ↥d.G,
        ∫ g, f g ∂Measure.haar = d.gammaIntegral μ (d.weylIntegrand μ f)

end GSpinGGP
