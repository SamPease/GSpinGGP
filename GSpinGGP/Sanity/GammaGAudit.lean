/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.GammaG
import GSpinGGP.Sanity.WeightedOrbitalAudit
import GSpinGGP.Sanity.DcQuotientAudit

/-!
# Sanity checks for `Γ(G)`, the Weyl integration formula and `J^A`

At the toy datum `toyD` (`G = GL₁ × GL₁`, commutative, `G_reg(F) = G(F)`, `D^G = 1`):

* `G(F)` is the only maximal torus (`toyD_maxTorus_eq_top`), so `𝒯(G)` is a point
  (`toyD_subsingleton_maxTorusClass`) and `|W(G,G)| = 1` (`toyD_ellWeylCard_top`);
* for every Haar measure `μ` on `T(F) = G(F)`, `J_G(t, f) = m(T\G) f(t)`, `m = dg/μ` on the point
  `T(F)\G(F)` (`toyD_orbitalIntegralOn`);
* **the Weyl integration formula holds** for every continuous compactly supported `f` and every
  family of Haar measures on the tori (`toyD_weyl_integration`): it is Weil's formula
  `∫_G f dg = m(T\G) ∫_T f dμ`.  This tests the normalizations of `gammaIntegral` and
  `weylIntegrand` (the weight `|W|⁻¹`, the factor `D^{1/2}` on top of the one inside `J_G`, and the
  quotient measure `dg/μ`); `D^G = 1` here, so the power of `D` is not tested;
* `J^A(f, f') = c ∫_G f f'` with `c = dcScaleAG` the mass of the point `G(F)/A_G(F)`
  (`toyD_jA`), and **BP Thm 5.5.1(iv) holds** with `θ_f = thetaF f`:
  `J^A(f, f') = ∫_{Γ(G)} D^G(x)^{1/2} θ_f(x) J_G(x, f') dx` (`toyD_jA_geom`).

No axioms beyond those of the imported modules (`weil_quotient_radon`, through the Weil measure).
-/

noncomputable section

open MeasureTheory GSpinGGP.Sanity GSpinGGP.AxiomRedTeam

namespace GSpinGGP.GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝕋" => (toyD (F := F))

/-- At `toyD` every maximal torus is `G(F)`. -/
theorem toyD_maxTorus_eq_top (T : (𝕋).MaxTorus) : T.1 = ⊤ := by
  obtain ⟨x, -, hT⟩ := T.2
  rw [hT, toyD_centG_eq_top]

/-- `G(F)` is a maximal torus of `toyD` (`G_1(F) = G(F)`, `1` regular). -/
def toyD_maxTorusTop : (𝕋).MaxTorus :=
  ⟨⊤, 1, by rw [toy_regularSet_eq_univ]; trivial, (toyD_centG_eq_top 1).symm⟩

instance toyD_subsingleton_maxTorus : Subsingleton (𝕋).MaxTorus :=
  ⟨fun T T' => Subtype.ext (by rw [toyD_maxTorus_eq_top T, toyD_maxTorus_eq_top T'])⟩

/-- **`𝒯(toyD)` is a point.** -/
instance toyD_subsingleton_maxTorusClass : Subsingleton (𝕋).MaxTorusClass :=
  ⟨fun a b => by
    induction a using Quot.ind
    induction b using Quot.ind
    rename_i T T'
    rw [Subsingleton.elim T T']⟩

/-- **`|W(G,G)| = 1`** at `toyD`. -/
theorem toyD_ellWeylCard_top : ellWeylCard (𝕋) ⊤ = 1 := by
  unfold ellWeylCard
  rw [Subgroup.top_subgroupOf]
  exact Subgroup.index_top

/-- `T(F)\G(F)` is a point for `T = G(F)`. -/
theorem subsingleton_cosetSpace_of_eq_top {T : Subgroup ↥(𝕋).G} (hT : T = ⊤) :
    Subsingleton (CosetSpace T.subtype) := by
  refine ⟨fun a b => ?_⟩
  induction a using CosetSpace.ind with | h a => ?_
  induction b using CosetSpace.ind with | h b => ?_
  rw [CosetSpace.mk_eq_mk_iff, CosetSpace.rel_iff]
  exact ⟨⟨b * a⁻¹, by rw [hT]; trivial⟩, by simp⟩

/-- **`J_G(t, f) = m(T\G) f(t)` at `toyD`** for a maximal torus `T` (`= G(F)`), any Haar measure `μ`
on it and any `t`, `m = dg/μ` (`D^G = 1`, `g⁻¹ t g = t`). -/
theorem toyD_orbitalIntegralOn (T : (𝕋).MaxTorus) (μ : Measure ↥T.1) (t : ↥(𝕋).G)
    (f : ↥(𝕋).G → ℂ) :
    (𝕋).orbitalIntegralOn T.1 μ t f = ((𝕋).quotMeasureOn T.1 μ).real Set.univ * f t := by
  have hpt : ∀ q : CosetSpace T.1.subtype,
      f ((CosetSpace.out _ q)⁻¹ * t * CosetSpace.out _ q) = f t := fun q => by
    rw [mul_assoc, toyD_G_comm t, inv_mul_cancel_left]
  unfold orbitalIntegralOn
  rw [toyD_weylDisc, Real.sqrt_one, Complex.ofReal_one, one_mul]
  simp_rw [hpt]
  rw [integral_const, Complex.real_smul]

/-- The Weyl integrand at `toyD`: `D^{1/2} J_G(t, f) = m(T\G) f(t)`. -/
theorem toyD_weylIntegrand (μ : ∀ T : Subgroup ↥(𝕋).G, Measure ↥T) (f : ↥(𝕋).G → ℂ)
    (T : (𝕋).MaxTorus) (t : ↥(𝕋).G) :
    (𝕋).weylIntegrand μ f T.1 t = ((𝕋).quotMeasureOn T.1 (μ T.1)).real Set.univ * f t := by
  have hreg : t ∈ regularSet (𝕋).G (𝕋).lie := by rw [toy_regularSet_eq_univ]; trivial
  simp only [weylIntegrand, hreg, ↓reduceIte]
  rw [toyD_weylDisc, Real.sqrt_one, Complex.ofReal_one, one_mul,
    toyD_orbitalIntegralOn]

/-- `∫_{Γ(G)}` at `toyD` is the integral over the one torus `G(F)`, with weight `1`. -/
theorem toyD_gammaIntegral (μ : ∀ T : Subgroup ↥(𝕋).G, Measure ↥T)
    (φ : Subgroup ↥(𝕋).G → ↥(𝕋).G → ℂ) :
    ∃ T : (𝕋).MaxTorus, (𝕋).gammaIntegral μ φ = ∫ t : ↥T.1, φ T.1 t ∂μ T.1 := by
  set c0 : (𝕋).MaxTorusClass := Quot.mk _ toyD_maxTorusTop
  refine ⟨Quot.out c0, ?_⟩
  unfold gammaIntegral
  rw [tsum_eq_single c0 fun b hb => (hb (Subsingleton.elim _ _)).elim,
    toyD_maxTorus_eq_top (Quot.out c0), toyD_ellWeylCard_top, Nat.cast_one, inv_one, one_mul]

/-- **Weil's formula at a maximal torus of `toyD`**: `∫_G f dg = m(T\G) ∫_T f dμ` for continuous
compactly supported `f`, any Haar measure `μ` on `T(F) = G(F)`, `m = dg/μ`. -/
theorem toyD_integral_eq_torus (T : (𝕋).MaxTorus) (μ : Measure ↥T.1) [μ.IsHaarMeasure]
    {f : ↥(𝕋).G → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫ g, f g ∂Measure.haar =
      ((𝕋).quotMeasureOn T.1 μ).real Set.univ * ∫ t : ↥T.1, f t ∂μ := by
  have hT := toyD_maxTorus_eq_top T
  have := T.isMulRightInvariant μ
  have hW := T.quotMeasureOn_spec μ
  set m := (𝕋).quotMeasureOn T.1 μ
  have hemb : Topology.IsClosedEmbedding T.1.subtype := T.isClosed.isClosedEmbedding_subtypeVal
  have : IsFiniteMeasureOnCompacts m := hW.isFiniteMeasureOnCompacts continuous_subtypeVal hemb
  have := subsingleton_cosetSpace_of_eq_top hT
  have : CompactSpace (CosetSpace T.1.subtype) := ⟨Set.Subsingleton.isCompact fun a _ b _ =>
    Subsingleton.elim a b⟩
  have : IsFiniteMeasure m := ⟨isCompact_univ.measure_lt_top⟩
  have hfT : Integrable (fun s : ↥T.1 => f s) μ :=
    (hf.comp continuous_subtypeVal).integrable_of_hasCompactSupport
      (hfc.comp_isClosedEmbedding hemb)
  -- the fibre integral is `∫_T f dμ` at every point (right invariance of `μ`)
  have hfib : ∀ q : CosetSpace T.1.subtype,
      (fun s : ↥T.1 => f (T.1.subtype s * CosetSpace.out _ q)) =
        fun s => (fun s' : ↥T.1 => f s') (s * ⟨CosetSpace.out _ q, (Subgroup.eq_top_iff' _).1 hT _⟩) :=
    fun q => rfl
  have hfibI : ∀ q : CosetSpace T.1.subtype,
      ∫ s, f (T.1.subtype s * CosetSpace.out _ q) ∂μ = ∫ t : ↥T.1, f t ∂μ := fun q => by
    rw [hfib q, integral_mul_right_eq_self (fun s' : ↥T.1 => f s')]
  rw [hW.integral_complex f hf hfc (fun q => by rw [hfib q]; exact hfT.comp_mul_right _)
    (by simp_rw [hfibI]; exact integrable_const _)]
  simp_rw [hfibI]
  rw [integral_const, Complex.real_smul]

/-- **The Weyl integration formula at `toyD`** (BP §1.7, p. 32), for every continuous compactly
supported `f` and every family of Haar measures on the maximal tori: proved, from Weil's formula
(the general statement is the `sorry` theorem `weyl_integration`). -/
theorem toyD_weyl_integration (μ : ∀ T : Subgroup ↥(𝕋).G, Measure ↥T)
    (hμ : ∀ T : (𝕋).MaxTorus, (μ T.1).IsHaarMeasure) {f : ↥(𝕋).G → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    ∫ g, f g ∂Measure.haar = (𝕋).gammaIntegral μ ((𝕋).weylIntegrand μ f) := by
  obtain ⟨T, hT⟩ := toyD_gammaIntegral μ ((𝕋).weylIntegrand μ f)
  have := hμ T
  rw [hT, toyD_integral_eq_torus T (μ T.1) hf hfc]
  simp_rw [toyD_weylIntegrand μ f T]
  rw [integral_const_mul]

/-- **`J^A(f, f') = c ∫_G f f'` at `toyD`**, `c = dcScaleAG` (`= haar_G(A_G(𝒪))`,
`toyD_dcScaleAG`), the mass of the point `G(F)/A_G(F)` for `dg / d_c a`. -/
theorem toyD_jA {f f' : ↥(𝕋).G → ℂ} (hf : Continuous f) (hf' : f' ∈ testFunctions ↥(𝕋).G) :
    (𝕋).jA f f' = ((𝕋).dcScaleAG.toReal : ℂ) * ∫ g, f g * f' g ∂Measure.haar := by
  rw [jA_eq_orbitalPairing, ← (toyD_isThetaF hf).2.2 f' hf', ← integral_const_mul]
  congr 1
  funext g
  simp [mul_assoc]

open scoped Classical in
/-- **BP Thm 5.5.1(iv) at `toyD`**: `J^A(f, f') = ∫_{Γ(G)} D^G(x)^{1/2} θ_f(x) J_G(x, f') dx` for
continuous compactly supported `f`, `f' ∈ C_c^∞(G(F))`, `θ_f = thetaF f`, and every family of Haar
measures on the tori (`J_G(x, ·)` for `dg / μ T`).  With `θ_f = c f` (`toyD_thetaF_eq`) both sides
are `c ∫ f f'` (`toyD_jA`, `toyD_weyl_integration`).  So the measure `dg / d_c a` on
`A_G(F)\G(F)` in `jA` is the one for which (iv) holds here. -/
theorem toyD_jA_geom (μ : ∀ T : Subgroup ↥(𝕋).G, Measure ↥T)
    (hμ : ∀ T : (𝕋).MaxTorus, (μ T.1).IsHaarMeasure) {f f' : ↥(𝕋).G → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hf' : f' ∈ testFunctions ↥(𝕋).G) :
    (𝕋).jA f f' = (𝕋).gammaIntegral μ (fun T t =>
      if t ∈ regularSet (𝕋).G (𝕋).lie then
        (Real.sqrt (weylDisc (𝕋).lie (t : (𝕋).ambientˣ)) : ℂ) * thetaF (𝕋) f t *
          (𝕋).orbitalIntegralOn T (μ T) t f'
      else 0) := by
  set c : ℂ := ((𝕋).dcScaleAG.toReal : ℂ)
  have hcont' : Continuous f' := hf'.1.continuous
  have hh : Continuous (fun g => c * (f g * f' g)) := continuous_const.mul (hf.mul hcont')
  have hhc : HasCompactSupport (fun g => c * (f g * f' g)) :=
    (hfc.mul_right).mul_left
  rw [toyD_jA hf hf', ← integral_const_mul, toyD_weyl_integration μ hμ hh hhc]
  refine gammaIntegral_congr _ μ fun T t _ => ?_
  have hreg : t ∈ regularSet (𝕋).G (𝕋).lie := by rw [toy_regularSet_eq_univ]; trivial
  simp only [hreg, ↓reduceIte]
  rw [toyD_weylIntegrand, toyD_weylDisc, Real.sqrt_one, Complex.ofReal_one, one_mul,
    toyD_thetaF_eq hf, toyD_orbitalIntegralOn, Pi.smul_apply, smul_eq_mul]
  ring

end GSpinGGP.GGPData
