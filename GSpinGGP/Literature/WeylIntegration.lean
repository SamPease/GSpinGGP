/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.GammaG

/-!
# The Weyl integration formula (cited: Beuzart-Plessis, Astérisque 418, §1.7, p. 32)

R. Beuzart-Plessis, *A local trace formula for the Gan–Gross–Prasad conjecture for unitary groups:
the Archimedean case*, Astérisque 418 (2020). Setting (Chapter 1): `F` a local field of
characteristic `0`, `G` a connected reductive group over `F`. BP states the formula without proof
or reference, as a standard result (it is due to Harish-Chandra; the attribution is ours).

The axiom is stated with the Lean objects of `TraceFormula/GammaG.lean` (`MaxTorus`,
`MaxTorusClass`, `gammaIntegral`, `weylIntegrand`); its docstring lists the identifications with
BP's objects. The form for every family of Haar measures on the tori is a theorem,
`GGPData.weyl_integration` (`TraceFormula/WeylIntegration.lean`).
-/

open MeasureTheory

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **The Weyl integration formula** (Beuzart-Plessis, Astérisque 418, §1.7, p. 32).
BP p. 32, after defining the measure `dx` on `Γ(G)`: "We have the Weyl integration formula
`∫_{G(F)} f(g) dg = ∫_{Γ(G)} D^G(x)^{1/2} J_G(x, f) dx` (…) for all `f ∈ S(G(F))` (…)" (the
omitted clauses are the Lie algebra version), where (same page)
`∫_{Γ(G)} φ(x) dx = Σ_{T ∈ 𝒯(G)} |W(G,T)|⁻¹ ∫_{T(F)} φ(t) dt` for `φ ∈ C_c(Γ(G))`, `𝒯(G)` a set of
representatives of the conjugacy classes of maximal tori, and (§1.8, p. 33)
`J_G(x, f) = D^G(x)^{1/2} ∫_{G_x(F)\G(F)} f(g⁻¹ x g) dg` for `x ∈ G_reg(F)`.
**Stated without proof in the source.** (The attribution to Harish-Chandra is ours: BP gives no
reference.)

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
4. **Torus measures (the `∃`).** BP fixes a Haar measure `dt` on `T(F)` for every maximal subtorus
   `T` (§1.6, p. 30: the autodual measure of `𝔱(F)`, lifted by the exponential). The witness is
   `μ (T(F)) = dt` for every maximal torus `T`, and anything on subgroups that are not of this form.
   The axiom does not say which Haar measure.
5. **`𝒯(G)` (maximal tori as centralizers).** `MaxTorus` is the set of `centG x` for
   `x ∈ G_reg(F)`, where `centG x` is the full centralizer `Z_G(x)(F)`; BP's `G_x` is `Z_G(x)⁰`
   (§1.1, p. 13), so the two agree because `Z_G(x)` is connected for semisimple `x` (Steinberg,
   *Endomorphisms of linear algebraic groups*, Mem. AMS 80 (1968), Thm 8.1: the derived group
   `Spin(W) × Spin(V)` is simply connected; proved here as `steinberg_centralizer_connected`,
   `GGP/Centralizers.lean`). For regular semisimple `x`, `Z_G(x)⁰` is a maximal torus `T`, so
   `centG x = T(F)`. Conversely, for a maximal torus `T`, `T(F)` is Zariski dense in `T` (Borel,
   *Linear algebraic groups*, 18.3; `F` of characteristic `0`) and `T_reg` is open dense in `T`, so
   `T(F)` contains some regular `x`, and `T = Z_G(x)`; `G_t(F) = T(F)` for every regular
   `t ∈ T(F)` (`centG_eq_of_mem_regularSet`). By density `T ↦ T(F)` is injective and carries
   `G(F)`-conjugacy of tori to conjugacy of subgroups of `G(F)`. Reading BP's "conjugacy classes
   of maximal tori in `G`" as `G(F)`-conjugacy classes (as `W(G,T) = Norm_{G(F)}(T)/T(F)` and the
   integral over `T(F)` require) is our reading. So `MaxTorusClass` is BP's set of classes, and
   the representatives `Quot.out c` are one choice of `𝒯(G)`.
6. **`|W(G,T)|`, `D^G`, `J_G`.** `weylCardG d T = |N_{G(F)}(T(F))/T(F)|` is BP's
   `|W(G,T)| = |Norm_{G(F)}(T)/T(F)|` (§1.1, p. 13; the normalizers agree by density). `weylDisc`
   is BP's `D^G(x) = |det(1 − Ad x)|_{𝔤/𝔤_x}|` (§1.1, p. 13). For regular `t ∈ T(F)`,
   `orbitalIntegralOn T (μ T) t f` is `J_G(t, f)` for `dg/μ_T` (BP §1.8, p. 33; `G_t(F) = T(F)` by
   5, and `quotMeasureOn` is the Weil quotient `dg/μ_T`, `MaxTorus.quotMeasureOn_spec`).
7. **The regular set.** BP's `J_G` is defined on `G_reg(F)`; `weylIntegrand` is `0` off it. On
   `T(F)` the singular set is the zero set of `t ↦ det(1 − Ad t)|_{𝔤/𝔱} = ∏_α (1 − α(t))`, a
   nonzero regular function on `T` (not `D^G` itself, which is nonzero at every semisimple
   element); it is the set where the Lean condition `IsRegularSS` (`regularSet`) fails, and it is
   a `dt`-null set.
8. **Absolute convergence, and Lean's integrals and sum are BP's.**
   * Measurability: for `t ∈ T(F)` the inner integrand `g ↦ f(g⁻¹ t g)` is left `T(F)`-invariant
     (`MaxTorus.conj_mul_left`), hence a continuous function on `T(F)\G(F)`; and
     `t ↦ D^G(t)^{1/2} J_G(t, f)` is locally constant on `T_reg(F)` (Harish-Chandra), which is
     open and conull in `T(F)`.
   * The third conjunct (convergence in `[0, ∞]`). BP reads the formula as an identity of
     integrals in `[0, ∞]` of nonnegative functions: right after it (p. 32) "We deduce from this
     and the local boundedness of normalized orbital integrals the following fact (1.7.1) The
     function `x ↦ D^G(x)^{-1/2}` (…) is locally integrable on `G(F)`", which applies the formula to
     `1_K (D^G)^{-1/2}` for compact `K`, a nonnegative function that is not in `S(G(F))`; so BP's
     formula is read in `[0, ∞]`. The conjunct needs less than this, only the formula for `|f|`
     with `f ∈ C_c^∞(G(F))`. For `f ∈ C_c^∞(G(F))` (`F` is `p`-adic), `|f| ∈ C_c^∞(G(F))` too, and
     for `|f|` every term on the right is a nonnegative integral:
     `D^G(t)^{1/2} J_G(t, |f|) = 1_{G_reg}(t) D^G(t) ∫_{T(F)\G(F)} |f(g⁻¹ t g)| dġ`
     (one `D^{1/2}` is inside `J_G`, BP p. 33). So BP's formula for `|f|` gives, for each
     `T ∈ 𝒯(G)`, `|W(G,T)|⁻¹ ∫_{T(F)} 1_{G_reg}(t) D^G(t) ∫_{T(F)\G(F)} |f(g⁻¹ t g)| dġ dt
     ≤ ∫_{G(F)} |f| dg < ∞`, and `|W(G,T)|` is finite (below; BP's printed `|W(G,T)|⁻¹`
     presupposes it). BP's `𝒯(G)` is any set of
     representatives (p. 32, "Let `𝒯(G)` be a set of representatives"), so every maximal torus
     `T` lies in some choice of it, and the witness of 4 is BP's `dt` on every maximal torus;
     hence the bound holds for every `T : d.MaxTorus`. This is the third conjunct, with
     `‖f(·)‖ₑ = |f(·)|` and the inner integral over the representatives `CosetSpace.out`.
     `quotMeasureOn T (μ T)` is the quotient of Lean's `Measure.haar = c · dg` (step 2) by `dt`,
     so it is `c · (dg/dt)`; rescaling by `0 < c < ∞` preserves `< ∞`.
   * Consequently the Bochner integrals of the second conjunct converge absolutely: the inner one
     (also BP §1.8, p. 33), and the outer ones because `|J_G(x, f)| ≤ J_G(x, |f|)`. Hence the
     integrand is integrable on each `T(F)` and the terms of the sum over `𝒯(G)` are absolutely
     summable (`∫ |f| dg < ∞` bounds their sum).
   * Finiteness: `𝒯(G)` is finite for `p`-adic `F` and each `N_{G(F)}(T)/T(F)` is finite (it
     embeds in the Weyl group of `T` over `F̄`; BP's printed `|W(G,T)|⁻¹` presupposes it), so
     neither the `tsum` nor the `Nat.card` in `weylCardG` takes a junk value.
   So Lean's Bochner integrals and `tsum` (which give `0` on non-integrable or non-summable input)
   agree with BP's.

The statement is therefore no stronger than BP's: BP's formula for its `dg` and `dt` implies it,
with BP's `dt` as the witness.

**Change to the statement (reviewed, deliberate).** The third conjunct (the `[0, ∞]` convergence
of item 8) was added after the axiom was first stated with the first two conjuncts only. Reason:
Lean's Bochner integrals and `tsum` are `0` on divergent input, so the identity alone cannot force
a torus term to be finite: the identities for all `1_U` do not exclude a torus term, as a measure
on `G(F)`, with an infinite atom. Integrability or summability conjuncts in the Bochner sense
would not exclude this either, since the inner orbital integral can itself be a junk `0`; the
`lintegral` conjunct does. It adds no hypothesis beyond the print: it is BP's formula for `|f|`,
read in `[0, ∞]` as BP does for (1.7.1). -/
axiom weyl_integration_exists (d : GGPData F) :
    ∃ μ : ∀ T : Subgroup ↥d.G, Measure ↥T, (∀ T : d.MaxTorus, (μ T.1).IsHaarMeasure) ∧
      (∀ f ∈ testFunctions ↥d.G,
        ∫ g, f g ∂Measure.haar = d.gammaIntegral μ (d.weylIntegrand μ f)) ∧
      ∀ f ∈ testFunctions ↥d.G, ∀ T : d.MaxTorus,
        ∫⁻ t : ↥T.1, (regularSet d.G d.lie).indicator
            (fun x => ENNReal.ofReal (weylDisc d.lie (x : d.ambientˣ))) (t : ↥d.G) *
          ∫⁻ q, ‖f ((CosetSpace.out _ q)⁻¹ * (t : ↥d.G) * CosetSpace.out _ q)‖ₑ
            ∂d.quotMeasureOn T.1 (μ T.1) ∂μ T.1 < ⊤

end GSpinGGP
