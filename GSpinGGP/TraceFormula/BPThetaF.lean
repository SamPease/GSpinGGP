/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.GammaG
import GSpinGGP.TraceFormula.ThetaFBP
import GSpinGGP.GGP.SpecialK

/-!
# Beuzart-Plessis' `θ_f` as a predicate, and the integrand of the geometric expansion

For `f ∈ C_c^∞(G(F))` strongly cuspidal, Beuzart-Plessis (Astérisque 418, §5.2, p. 109) and
Waldspurger (Compositio Math. 146 (2010), §5.3) define, for `x ∈ G_reg(F)`,
`θ_f(x) = (−1)^{a_G − a_{M(x)}} ν(G_x)⁻¹ D^G(x)^{−1/2} J_{M(x)}(x, f)`, the weighted orbital
integral being taken with a special maximal compact subgroup in good position relative to `M(x)`.
`ReducedLeviDatum.thetaFBP L K f x` is that formula for a presentation `L` of `M(x)` (`IsMx L x`)
and a compact subgroup `K`.

* `IsBPThetaF f θ` says that `θ` is `θ_f` on `G_reg(F)`: at every regular `x` **some** presentation
  `(L, K)` with `IsMx L x` and `K` special (`GoodK.IsSpecial`) exists, and **every** such
  presentation gives `θ x`.  Off `G_reg(F)` nothing is said.

  Why both halves.  With only the second half, a predicate `IsSpecial` that no `K` satisfies would
  make the hypothesis hold for every `θ`; with only the first, a predicate that some non-special
  `K` satisfies would make statements about `θ` assert independence of `K` beyond the special
  ones.  With both, either mistake only makes `IsBPThetaF f θ` unsatisfiable, so a statement with
  this hypothesis becomes vacuous rather than false (`not_isBPThetaF_of_not_exists`,
  `not_isBPThetaF_of_ne`).
* `thetaWeylIntegrand μ θ f' T t = θ(t) · D^G(t)^{1/2} J_G(t, f')` on `T(F)` (for `t ∈ G_reg(F)`,
  `0` otherwise), the integrand of BP Thm 5.5.1(iv); `J_G(t, ·)` is taken for `dg / μ T`.  It is
  written as `θ t * weylIntegrand μ f' T t`.
* The right side of BP Thm 5.5.1(iv) does not depend on the Haar measures of the tori
  (`gammaIntegral_thetaWeylIntegrand_eq`), nor do its integrability and summability
  (`integrable_thetaWeylIntegrand_iff`, `summable_norm_thetaWeylIntegrand_iff`).

The literature axioms about `θ_f` are in `Literature/BPThetaF.lean`.
-/

noncomputable section

open MeasureTheory

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

/-! ## `IsBPThetaF` -/

/-- **`θ` is Beuzart-Plessis' `θ_f` on `G_reg(F)`** (BP §5.2, p. 109; Waldspurger 2010, §5.3):
for every `x ∈ G_reg(F)`, some presentation `(L, K)` of `M(x)` with `K` special in good position
relative to `L.M` exists, and every such presentation gives `θ x = L.thetaFBP K f x`.  The
measure on `G(F)` is `Measure.haar`, so this is `θ_f` for `dg = Measure.haar` (`thetaFBP` is
linear in `dg`).  The values of `θ` off `G_reg(F)` are not constrained.  See the module docstring
for why the predicate has both an existence and a universal half. -/
def IsBPThetaF (f θ : ↥d.G → ℂ) : Prop :=
  ∀ x ∈ regularSet d.G d.lie,
    (∃ (L : d.ReducedLeviDatum) (K : d.GoodK L.toFlagLeviDatum), L.IsMx x ∧ K.IsSpecial) ∧
    ∀ (L : d.ReducedLeviDatum) (K : d.GoodK L.toFlagLeviDatum), L.IsMx x → K.IsSpecial →
      θ x = L.thetaFBP K f x

variable {d}

/-- **A wrong `IsSpecial` that is too strict makes the hypothesis unsatisfiable**: if at some
regular `x` no special presentation exists, no `θ` satisfies `IsBPThetaF f θ`. -/
theorem not_isBPThetaF_of_not_exists {f θ : ↥d.G → ℂ} {x : ↥d.G}
    (hx : x ∈ regularSet d.G d.lie)
    (h : ¬ ∃ (L : d.ReducedLeviDatum) (K : d.GoodK L.toFlagLeviDatum), L.IsMx x ∧ K.IsSpecial) :
    ¬ d.IsBPThetaF f θ :=
  fun hθ => h (hθ x hx).1

/-- **A wrong `IsSpecial` that is too loose makes the hypothesis unsatisfiable** as soon as two
presentations it admits give different values. -/
theorem not_isBPThetaF_of_ne {f θ : ↥d.G → ℂ} {x : ↥d.G} (hx : x ∈ regularSet d.G d.lie)
    {L L' : d.ReducedLeviDatum} {K : d.GoodK L.toFlagLeviDatum} {K' : d.GoodK L'.toFlagLeviDatum}
    (hL : L.IsMx x) (hL' : L'.IsMx x) (hK : K.IsSpecial) (hK' : K'.IsSpecial)
    (hne : L.thetaFBP K f x ≠ L'.thetaFBP K' f x) : ¬ d.IsBPThetaF f θ := fun hθ =>
  hne (((hθ x hx).2 L K hL hK).symm.trans ((hθ x hx).2 L' K' hL' hK'))

/-- `IsBPThetaF` only reads `θ` on `G_reg(F)`. -/
theorem IsBPThetaF.congr {f θ θ' : ↥d.G → ℂ} (hθ : d.IsBPThetaF f θ)
    (h : ∀ x ∈ regularSet d.G d.lie, θ' x = θ x) : d.IsBPThetaF f θ' := fun x hx =>
  ⟨(hθ x hx).1, fun L K hL hK => (h x hx).trans ((hθ x hx).2 L K hL hK)⟩

/-- Two functions with `IsBPThetaF f` agree on `G_reg(F)`. -/
theorem IsBPThetaF.eq {f θ θ' : ↥d.G → ℂ} (hθ : d.IsBPThetaF f θ) (hθ' : d.IsBPThetaF f θ')
    {x : ↥d.G} (hx : x ∈ regularSet d.G d.lie) : θ x = θ' x := by
  obtain ⟨L, K, hL, hK⟩ := (hθ x hx).1
  exact ((hθ x hx).2 L K hL hK).trans ((hθ' x hx).2 L K hL hK).symm

/-! ## The integrand of BP Thm 5.5.1(iv) -/

variable (d)

/-- **The integrand `D^G(t)^{1/2} θ(t) J_G(t, f')` of BP Thm 5.5.1(iv)** on `T(F)`, with
`J_G(t, f')` for `dg / μ T` (`orbitalIntegralOn`, which contains a factor `D^G(t)^{1/2}`), and `0`
off `G_reg(F)` (`thetaWeylIntegrand_of_mem_regularSet`, `thetaWeylIntegrand_of_not_mem`).  So the
values of `θ` off `G_reg(F)` do not enter. -/
def thetaWeylIntegrand (μ : ∀ T : Subgroup ↥d.G, Measure ↥T) (θ f' : ↥d.G → ℂ)
    (T : Subgroup ↥d.G) (t : ↥d.G) : ℂ :=
  θ t * d.weylIntegrand μ f' T t

variable {d}

theorem thetaWeylIntegrand_of_mem_regularSet (μ : ∀ T : Subgroup ↥d.G, Measure ↥T)
    (θ f' : ↥d.G → ℂ) (T : Subgroup ↥d.G) {t : ↥d.G} (ht : t ∈ regularSet d.G d.lie) :
    d.thetaWeylIntegrand μ θ f' T t =
      (Real.sqrt (weylDisc d.lie (t : d.ambientˣ)) : ℂ) * θ t *
        d.orbitalIntegralOn T (μ T) t f' := by
  simp only [thetaWeylIntegrand, weylIntegrand, ht, ↓reduceIte]
  ring

theorem thetaWeylIntegrand_of_not_mem (μ : ∀ T : Subgroup ↥d.G, Measure ↥T)
    (θ f' : ↥d.G → ℂ) (T : Subgroup ↥d.G) {t : ↥d.G} (ht : t ∉ regularSet d.G d.lie) :
    d.thetaWeylIntegrand μ θ f' T t = 0 := by
  simp [thetaWeylIntegrand, weylIntegrand, ht]

/-- The integrand only reads `θ` on `G_reg(F)`. -/
theorem thetaWeylIntegrand_congr (μ : ∀ T : Subgroup ↥d.G, Measure ↥T) {θ θ' : ↥d.G → ℂ}
    (h : ∀ x ∈ regularSet d.G d.lie, θ x = θ' x) (f' : ↥d.G → ℂ) :
    d.thetaWeylIntegrand μ θ f' = d.thetaWeylIntegrand μ θ' f' := by
  funext T t
  by_cases ht : t ∈ regularSet d.G d.lie
  · simp only [thetaWeylIntegrand, h t ht]
  · rw [thetaWeylIntegrand_of_not_mem μ θ f' T ht, thetaWeylIntegrand_of_not_mem μ θ' f' T ht]

/-- On a maximal torus `T`, two Haar measures differ by a factor `0 < k < ∞`. -/
theorem MaxTorus.exists_eq_smul (T : d.MaxTorus) (μ μ' : Measure ↥T.1) [μ.IsHaarMeasure]
    [μ'.IsHaarMeasure] : ∃ k : ENNReal, k ≠ 0 ∧ k ≠ ⊤ ∧ μ' = k • μ := by
  have : LocallyCompactSpace ↥T.1 := T.isClosed.locallyCompactSpace
  have : SecondCountableTopology ↥T.1 := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  refine ⟨(Measure.haarScalarFactor μ' μ : ENNReal),
    ENNReal.coe_ne_zero.2 (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne',
    ENNReal.coe_ne_top, Measure.isMulLeftInvariant_eq_smul μ' μ⟩

/-- The integrand under rescaling of one torus measure: if `μ' T = k • μ T`, `0 < k < ∞`, it is
divided by `k` on `T(F)` (`weylIntegrand_of_eq_smul`). -/
theorem thetaWeylIntegrand_of_eq_smul {μ μ' : ∀ T : Subgroup ↥d.G, Measure ↥T} (T : d.MaxTorus)
    [(μ T.1).IsHaarMeasure] {k : ENNReal} (hk0 : k ≠ 0) (hk : k ≠ ⊤) (h : μ' T.1 = k • μ T.1)
    (θ f' : ↥d.G → ℂ) (t : ↥d.G) :
    d.thetaWeylIntegrand μ' θ f' T.1 t =
      ((k⁻¹).toReal : ℂ) * d.thetaWeylIntegrand μ θ f' T.1 t := by
  unfold thetaWeylIntegrand
  rw [d.weylIntegrand_of_eq_smul T hk0 hk h]
  ring

/-- **The torus integral of the integrand does not depend on the Haar measure of the torus**. -/
theorem integral_thetaWeylIntegrand_eq (μ μ' : ∀ T : Subgroup ↥d.G, Measure ↥T) (T : d.MaxTorus)
    [(μ T.1).IsHaarMeasure] [(μ' T.1).IsHaarMeasure] (θ f' : ↥d.G → ℂ) :
    ∫ t : ↥T.1, d.thetaWeylIntegrand μ' θ f' T.1 t ∂μ' T.1 =
      ∫ t : ↥T.1, d.thetaWeylIntegrand μ θ f' T.1 t ∂μ T.1 := by
  obtain ⟨k, hk0, hk, hμk⟩ := T.exists_eq_smul (μ T.1) (μ' T.1)
  simp_rw [thetaWeylIntegrand_of_eq_smul T hk0 hk hμk θ f']
  rw [hμk, integral_smul_measure, integral_const_mul, Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul, ← ENNReal.toReal_mul, ENNReal.mul_inv_cancel hk0 hk,
    ENNReal.toReal_one, Complex.ofReal_one, one_mul]

/-- **The torus integral of the norm of the integrand does not depend on the Haar measure of the
torus**. -/
theorem integral_norm_thetaWeylIntegrand_eq (μ μ' : ∀ T : Subgroup ↥d.G, Measure ↥T)
    (T : d.MaxTorus) [(μ T.1).IsHaarMeasure] [(μ' T.1).IsHaarMeasure] (θ f' : ↥d.G → ℂ) :
    ∫ t : ↥T.1, ‖d.thetaWeylIntegrand μ' θ f' T.1 t‖ ∂μ' T.1 =
      ∫ t : ↥T.1, ‖d.thetaWeylIntegrand μ θ f' T.1 t‖ ∂μ T.1 := by
  obtain ⟨k, hk0, hk, hμk⟩ := T.exists_eq_smul (μ T.1) (μ' T.1)
  simp_rw [thetaWeylIntegrand_of_eq_smul T hk0 hk hμk θ f', norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  rw [hμk, integral_smul_measure, integral_const_mul, smul_eq_mul, ← mul_assoc,
    ← ENNReal.toReal_mul, ENNReal.mul_inv_cancel hk0 hk, ENNReal.toReal_one, one_mul]

/-- **Integrability of the integrand on a torus does not depend on the Haar measure.** -/
theorem integrable_thetaWeylIntegrand_iff (μ μ' : ∀ T : Subgroup ↥d.G, Measure ↥T)
    (T : d.MaxTorus) [(μ T.1).IsHaarMeasure] [(μ' T.1).IsHaarMeasure] (θ f' : ↥d.G → ℂ) :
    Integrable (fun t : ↥T.1 => d.thetaWeylIntegrand μ' θ f' T.1 t) (μ' T.1) ↔
      Integrable (fun t : ↥T.1 => d.thetaWeylIntegrand μ θ f' T.1 t) (μ T.1) := by
  obtain ⟨k, hk0, hk, hμk⟩ := T.exists_eq_smul (μ T.1) (μ' T.1)
  simp_rw [thetaWeylIntegrand_of_eq_smul T hk0 hk hμk θ f']
  rw [hμk, integrable_smul_measure hk0 hk]
  have hc : ((k⁻¹).toReal : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 hk)
      (ENNReal.inv_ne_top.2 hk0)).ne'
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.2 hc) _

variable (d) in
/-- **The right side of BP Thm 5.5.1(iv) does not depend on the Haar measures of the tori**:
term by term, as for `gammaIntegral_weylIntegrand_eq`; no integrability is needed. -/
theorem gammaIntegral_thetaWeylIntegrand_eq (μ μ' : ∀ T : Subgroup ↥d.G, Measure ↥T)
    (hμ : ∀ T : d.MaxTorus, (μ T.1).IsHaarMeasure) (hμ' : ∀ T : d.MaxTorus, (μ' T.1).IsHaarMeasure)
    (θ f' : ↥d.G → ℂ) :
    d.gammaIntegral μ' (d.thetaWeylIntegrand μ' θ f') =
      d.gammaIntegral μ (d.thetaWeylIntegrand μ θ f') := by
  unfold gammaIntegral
  refine tsum_congr fun c => ?_
  have := hμ (Quot.out c)
  have := hμ' (Quot.out c)
  rw [integral_thetaWeylIntegrand_eq μ μ' (Quot.out c) θ f']

variable (d) in
/-- **Absolute summability over `𝒯(G)` does not depend on the Haar measures of the tori.** -/
theorem summable_norm_thetaWeylIntegrand_iff (μ μ' : ∀ T : Subgroup ↥d.G, Measure ↥T)
    (hμ : ∀ T : d.MaxTorus, (μ T.1).IsHaarMeasure) (hμ' : ∀ T : d.MaxTorus, (μ' T.1).IsHaarMeasure)
    (θ f' : ↥d.G → ℂ) :
    Summable (fun c : d.MaxTorusClass => ((weylCardG d (Quot.out c).1 : ℝ))⁻¹ *
        ∫ t, ‖d.thetaWeylIntegrand μ' θ f' (Quot.out c).1 t‖ ∂μ' (Quot.out c).1) ↔
      Summable (fun c : d.MaxTorusClass => ((weylCardG d (Quot.out c).1 : ℝ))⁻¹ *
        ∫ t, ‖d.thetaWeylIntegrand μ θ f' (Quot.out c).1 t‖ ∂μ (Quot.out c).1) := by
  have h : (fun c : d.MaxTorusClass => ((weylCardG d (Quot.out c).1 : ℝ))⁻¹ *
        ∫ t, ‖d.thetaWeylIntegrand μ' θ f' (Quot.out c).1 t‖ ∂μ' (Quot.out c).1) =
      (fun c : d.MaxTorusClass => ((weylCardG d (Quot.out c).1 : ℝ))⁻¹ *
        ∫ t, ‖d.thetaWeylIntegrand μ θ f' (Quot.out c).1 t‖ ∂μ (Quot.out c).1) := by
    funext c
    have := hμ (Quot.out c)
    have := hμ' (Quot.out c)
    rw [integral_norm_thetaWeylIntegrand_eq μ μ' (Quot.out c) θ f']
  rw [h]

end GGPData

end GSpinGGP
