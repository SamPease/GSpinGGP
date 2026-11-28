/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.WeylIntegration
import GSpinGGP.Foundations.CompactOpenExt
import GSpinGGP.Foundations.TorusIntegrability

/-!
# The Weyl integration formula for integrable functions

BP §1.7 (p. 32) states the Weyl integration formula for `f ∈ S(G(F)) = C_c^∞(G(F))`
(`weyl_integration`).  Here it is extended to every `f ∈ L¹(G(F))`, with absolute convergence of
the right side.

## The measure on `G(F)` defined by the right side

For a maximal torus `T` with Haar measure `μ_T`, push the measure `D^G(t) dμ_T(t) ⊗ dġ` on
`T(F) × T(F)\G(F)` (`dġ = dg/μ_T`, the density `D^G` cut off to `G_reg(F)`) forward along
`(t, ġ) ↦ g⁻¹ t g` (`weylConj`; well defined because `T(F)` is commutative); this is
`weylMeasureOn`.  The sum over the classes `c ∈ 𝒯(G)`, weighted by `|W(G,T_c)|⁻¹`, is
`weylMeasure`.  By Fubini–Tonelli `∫ φ d(weylMeasure) = ∫_{Γ(G)} D^{1/2} J_G(·, φ)` whenever the
left side converges (`MaxTorus.integral_weylMeasureOn` for one torus, `weyl_integration_integrable`
for the sum).

## From `C_c^∞` to `L¹`

For a compact open `U ⊆ G(F)`, `1_U ∈ C_c^∞(G(F))`, so the Weyl integration formula for `1_U`
gives `weylMeasure U = haar U`, *provided* each torus term is finite (Lean's Bochner integral and
`tsum` are `0` on divergent input, so the formula for `1_U` alone does not exclude an infinite
torus term).  That finiteness is `MaxTorus.isFiniteMeasureOnCompacts_weylMeasureOn`, from the
`[0, ∞]` convergence conjunct of `weyl_integration_exists` (BP §1.7, p. 32), Tonelli
(`MaxTorus.lintegral_weylMeasureOn`) and the independence of a torus term from the Haar measure
of the torus (`MaxTorus.weylMeasureOn_eq`).  Compact open sets form a π-system generating the
Borel sets (`measure_ext_of_isCompact_isOpen`), so `weylMeasure = haar` (`weylMeasure_eq_haar`),
and the formula holds for every integrable `φ` (`weyl_integration_integrable`).

## Main statements

* `GGPData.weylMeasure_eq_haar`.
* `GGPData.weyl_integration_integrable`: the formula for `φ ∈ L¹(G(F))`, with integrability on
  each torus and summability over `𝒯(G)`.
* `GGPData.integral_mul_invariant`: for `θ` invariant under conjugation on `G_reg(F)` and
  `θ f ∈ L¹`, `∫ θ f = ∫_{Γ(G)} θ(x) D^{1/2}(x) J_G(x, f) dx`.
-/

noncomputable section

open MeasureTheory Topology
open scoped ENNReal

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

/-! ## The measure defined by the right side -/

/-- `(t, ġ) ↦ g⁻¹ t g` on `T(F) × T(F)\G(F)`, at the representatives `CosetSpace.out`.  For a
maximal torus it does not depend on the representatives (`MaxTorus.weylConj_mk`). -/
def weylConj (T : Subgroup ↥d.G) (p : ↥T × CosetSpace T.subtype) : ↥d.G :=
  (CosetSpace.out _ p.2)⁻¹ * (p.1 : ↥d.G) * CosetSpace.out _ p.2

variable {d}

/-- On a maximal torus, `weylConj` at the coset of `g` is `g⁻¹ t g`. -/
theorem MaxTorus.weylConj_mk (T : d.MaxTorus) (t : ↥T.1) (g : ↥d.G) :
    d.weylConj T.1 (t, CosetSpace.mk T.1.subtype g) = g⁻¹ * (t : ↥d.G) * g := by
  obtain ⟨s, hs⟩ := CosetSpace.exists_out_mk T.1.subtype g
  unfold weylConj
  set o := CosetSpace.out T.1.subtype (CosetSpace.mk T.1.subtype g)
  have hst : Commute (s : ↥d.G) (t : ↥d.G) := T.commute s.prop t.prop
  rw [hs]
  simp only [Subgroup.subtype_apply]
  have e : ((s : ↥d.G) * o)⁻¹ * (t : ↥d.G) * ((s : ↥d.G) * o) =
      o⁻¹ * ((s : ↥d.G)⁻¹ * ((s : ↥d.G) * t)) * o := by
    rw [hst.eq]; group
  rw [e]
  group

/-- `weylConj` is continuous on `T(F) × T(F)\G(F)` for a maximal torus `T`: composed with the open
quotient map `id × mk` it is `(t, g) ↦ g⁻¹ t g`. -/
theorem MaxTorus.continuous_weylConj (T : d.MaxTorus) : Continuous (d.weylConj T.1) := by
  have hq : IsOpenQuotientMap (Prod.map (id : ↥T.1 → ↥T.1) (CosetSpace.mk T.1.subtype)) :=
    IsOpenQuotientMap.id.prodMap (CosetSpace.isOpenQuotientMap_mk _)
  refine hq.isQuotientMap.continuous_iff.2 ?_
  have e : d.weylConj T.1 ∘ Prod.map id (CosetSpace.mk T.1.subtype) =
      fun p : ↥T.1 × ↥d.G => p.2⁻¹ * (p.1 : ↥d.G) * p.2 :=
    funext fun p => T.weylConj_mk p.1 p.2
  rw [e]
  fun_prop

variable (d)

/-- The density `D^G(t)` on `T(F)`, cut off to `G_reg(F)`. -/
def weylDensity (T : Subgroup ↥d.G) (t : ↥T) : ℝ≥0∞ :=
  (regularSet d.G d.lie).indicator (fun x => ENNReal.ofReal (weylDisc d.lie (x : d.ambientˣ)))
    (t : ↥d.G)

theorem measurable_weylDensity (T : Subgroup ↥d.G) : Measurable (d.weylDensity T) := by
  have e : d.weylDensity T = fun t : ↥T => (regularSet d.G d.lie).indicator
      (fun x => ENNReal.ofReal (absF (hcDisc d x))) (t : ↥d.G) := funext fun t => by
    unfold weylDensity
    by_cases ht : (t : ↥d.G) ∈ regularSet d.G d.lie
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, weylDisc_eq_absF_hcDisc d ht]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
  have hm : Measurable fun x : ↥d.G => (regularSet d.G d.lie).indicator
      (fun x => ENNReal.ofReal (absF (hcDisc d x))) x :=
    (ENNReal.continuous_ofReal.comp (continuous_absF.comp (continuous_hcDisc d))).measurable
      |>.indicator (hc_regularSet_open_conull d).1.measurableSet
  rw [e]
  exact hm.comp measurable_subtypeVal

theorem weylDensity_lt_top (T : Subgroup ↥d.G) (t : ↥T) : d.weylDensity T t < ∞ := by
  unfold weylDensity
  by_cases ht : (t : ↥d.G) ∈ regularSet d.G d.lie
  · rw [Set.indicator_of_mem ht]; exact ENNReal.ofReal_lt_top
  · rw [Set.indicator_of_notMem ht]; exact ENNReal.zero_lt_top

/-- **The torus term of the right side of the Weyl integration formula, as a measure on `G(F)`**:
the push-forward of `D^G(t) dμ_T(t) ⊗ dg/μ_T` on `T(F) × T(F)\G(F)` along `(t, ġ) ↦ g⁻¹ t g`. -/
def weylMeasureOn (μ : ∀ T : Subgroup ↥d.G, Measure ↥T) (T : Subgroup ↥d.G) : Measure ↥d.G :=
  (((μ T).withDensity (d.weylDensity T)).prod (d.quotMeasureOn T (μ T))).map (d.weylConj T)

/-- `|W(G,T)|⁻¹` as a weight in `[0, ∞)` (`0` if the Lean `Nat.card` is `0`, matching the
complex `(0 : ℂ)⁻¹ = 0` of `gammaIntegral`). -/
def weylWeight (T : Subgroup ↥d.G) : ℝ≥0∞ := ENNReal.ofReal ((weylCardG d T : ℝ)⁻¹)

/-- **The right side of the Weyl integration formula, as a measure on `G(F)`**:
`Σ_{c ∈ 𝒯(G)} |W(G,T_c)|⁻¹ · weylMeasureOn μ T_c`. -/
def weylMeasure (μ : ∀ T : Subgroup ↥d.G, Measure ↥T) : Measure ↥d.G :=
  Measure.sum fun c : d.MaxTorusClass =>
    d.weylWeight (Quot.out c).1 • d.weylMeasureOn μ (Quot.out c).1

variable {d}

theorem weylWeight_ne_top (T : Subgroup ↥d.G) : d.weylWeight T ≠ ∞ := ENNReal.ofReal_ne_top

theorem weylWeight_eq_zero_iff (T : Subgroup ↥d.G) : d.weylWeight T = 0 ↔ weylCardG d T = 0 := by
  rw [weylWeight, ENNReal.ofReal_eq_zero, inv_nonpos, Nat.cast_nonpos]

theorem weylWeight_toReal (T : Subgroup ↥d.G) :
    ((d.weylWeight T).toReal : ℂ) = ((weylCardG d T : ℂ))⁻¹ := by
  rw [weylWeight, ENNReal.toReal_ofReal (inv_nonneg.2 (Nat.cast_nonneg _)), Complex.ofReal_inv,
    Complex.ofReal_natCast]

/-- **Tonelli for a torus term**: for measurable `φ : G(F) → [0, ∞]`,
`∫⁻ φ d(weylMeasureOn μ T) = ∫⁻_{T(F)} D^G(t) ∫⁻_{T(F)\G(F)} φ(g⁻¹ t g) dġ dμ_T(t)`
(`D^G` cut off to `G_reg(F)`). -/
theorem MaxTorus.lintegral_weylMeasureOn (T : d.MaxTorus) (μ : ∀ T : Subgroup ↥d.G, Measure ↥T)
    [(μ T.1).IsHaarMeasure] {φ : ↥d.G → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ g, φ g ∂d.weylMeasureOn μ T.1 = ∫⁻ t, d.weylDensity T.1 t *
      ∫⁻ q, φ (d.weylConj T.1 (t, q)) ∂d.quotMeasureOn T.1 (μ T.1) ∂μ T.1 := by
  have : LocallyCompactSpace ↥T.1 := T.isClosed.locallyCompactSpace
  have : SecondCountableTopology ↥T.1 := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have : IsFiniteMeasureOnCompacts (d.quotMeasureOn T.1 (μ T.1)) := by
    have := T.isMulRightInvariant (μ T.1)
    exact (T.quotMeasureOn_spec (μ T.1)).isFiniteMeasureOnCompacts continuous_subtypeVal
      T.isClosed.isClosedEmbedding_subtypeVal
  -- supplied by hand: found by instance search, but the `SigmaFinite` term built from it
  -- exceeds the default `synthInstance.maxSize`
  have : SigmaCompactSpace (CosetSpace T.1.subtype) := inferInstance
  have hΦ : Measurable (d.weylConj T.1) := T.continuous_weylConj.measurable
  have hm : Measurable fun t : ↥T.1 =>
      ∫⁻ q, φ (d.weylConj T.1 (t, q)) ∂d.quotMeasureOn T.1 (μ T.1) :=
    (hφ.comp hΦ).lintegral_prod_right'
  unfold weylMeasureOn
  rw [lintegral_map hφ hΦ,
    lintegral_prod (fun z => φ (d.weylConj T.1 z)) (hφ.comp hΦ).aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ (d.measurable_weylDensity T.1) hm]
  rfl

/-- **A torus term does not depend on the Haar measure of the torus**: for Haar measures `μ T`,
`μ' T` on `T(F)`, `weylMeasureOn μ T = weylMeasureOn μ' T`.  If `μ' T = c μ T`, the outer
measure is multiplied by `c` and `dg/μ' T = c⁻¹ dg/μ T` (`quotMeasureOn_smul`). -/
theorem MaxTorus.weylMeasureOn_eq (T : d.MaxTorus) (μ μ' : ∀ T : Subgroup ↥d.G, Measure ↥T)
    [(μ T.1).IsHaarMeasure] [(μ' T.1).IsHaarMeasure] :
    d.weylMeasureOn μ' T.1 = d.weylMeasureOn μ T.1 := by
  have : LocallyCompactSpace ↥T.1 := T.isClosed.locallyCompactSpace
  have : SecondCountableTopology ↥T.1 := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have := T.isMulRightInvariant (μ T.1)
  set k := Measure.haarScalarFactor (μ' T.1) (μ T.1)
  have hk : μ' T.1 = (k : ℝ≥0∞) • μ T.1 := by
    rw [Measure.isMulLeftInvariant_eq_smul (μ' T.1) (μ T.1)]
    rfl
  have hk0 : (k : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  ext s hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs,
    T.lintegral_weylMeasureOn μ' (measurable_one.indicator hs),
    T.lintegral_weylMeasureOn μ (measurable_one.indicator hs), hk,
    d.quotMeasureOn_smul T.1 T.isClosed (μ T.1) hk0 ENNReal.coe_ne_top, lintegral_smul_measure]
  simp_rw [lintegral_smul_measure, smul_eq_mul, mul_left_comm _ (k : ℝ≥0∞)⁻¹]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hk0), ← mul_assoc,
    ENNReal.mul_inv_cancel hk0 ENNReal.coe_ne_top, one_mul]

/-- **Finiteness of a torus term on compact sets**: for a maximal torus `T`, a Haar measure `μ_T`
on `T(F)` and compact `K ⊆ G(F)`, `∫_{T(F)} D^G(t) ∫_{T(F)\G(F)} 1_K(g⁻¹ t g) dġ dt < ∞`.

This is the absolute convergence of the right side of the Weyl integration formula, the third
conjunct of `weyl_integration_exists` (BP §1.7, p. 32, read in `[0, ∞]`).  Take a compact open
`U ⊇ K`, so `1_U ∈ C_c^∞(G(F))`; the conjunct for `1_U` is `weylMeasureOn μ₀ T (U) < ∞` for the
witness family `μ₀` (`MaxTorus.lintegral_weylMeasureOn`), and `weylMeasureOn` does not depend on
the Haar measure of `T(F)` (`MaxTorus.weylMeasureOn_eq`). -/
theorem MaxTorus.isFiniteMeasureOnCompacts_weylMeasureOn (T : d.MaxTorus)
    (μ : ∀ T : Subgroup ↥d.G, Measure ↥T) [(μ T.1).IsHaarMeasure] :
    IsFiniteMeasureOnCompacts (d.weylMeasureOn μ T.1) := by
  obtain ⟨μ₀, hμ₀, -, hfin⟩ := weyl_integration_exists d
  have := hμ₀ T
  rw [T.weylMeasureOn_eq μ₀ μ]
  have : TotallyDisconnectedSpace ↥d.G := totallyDisconnectedSpace_subgroup F d.ambient d.G
  refine ⟨fun K hK => ?_⟩
  obtain ⟨U, hUc, hUo, hKU, -⟩ :=
    exists_isCompact_isClopen_between hK isOpen_univ (Set.subset_univ K)
  refine (measure_mono hKU).trans_lt ?_
  have h := hfin _ (indicator_mem_testFunctions hUc hUo) T
  rw [← lintegral_indicator_one hUo.isOpen.measurableSet,
    T.lintegral_weylMeasureOn μ₀ (measurable_one.indicator hUo.isOpen.measurableSet)]
  refine lt_of_eq_of_lt (lintegral_congr fun t => ?_) h
  congr 1
  refine lintegral_congr fun q => ?_
  rw [eNorm_indicator_eq_indicator_eNorm]
  simp only [Pi.one_apply, eNorm_one]
  rfl

/-! ## The integral against a torus term -/

/-- `D^G(t) · ∫_{T(F)\G(F)} φ(g⁻¹ t g) dġ` is the Weyl integrand `D^G(t)^{1/2} J_G(t, φ)`. -/
theorem weylDensity_smul_integral (μ : ∀ T : Subgroup ↥d.G, Measure ↥T) (T : Subgroup ↥d.G)
    (φ : ↥d.G → ℂ) (t : ↥T) :
    (d.weylDensity T t).toReal • ∫ q, φ (d.weylConj T (t, q)) ∂d.quotMeasureOn T (μ T) =
      d.weylIntegrand μ φ T t := by
  unfold weylDensity weylIntegrand orbitalIntegralOn weylConj
  by_cases ht : (t : ↥d.G) ∈ regularSet d.G d.lie
  · have hD : 0 ≤ weylDisc d.lie ((t : ↥d.G) : d.ambientˣ) := (weylDisc_pos d t).le
    rw [Set.indicator_of_mem ht]
    simp only [ht, ↓reduceIte, ENNReal.toReal_ofReal hD]
    rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt hD]
  · rw [Set.indicator_of_notMem ht]
    simp only [ht, ↓reduceIte, ENNReal.toReal_zero, zero_smul]

/-- **The torus term computes the Weyl integrand** (Fubini–Tonelli): for `φ` integrable against
`weylMeasureOn μ T`, the Weyl integrand `D^G(t)^{1/2} J_G(t, φ)` is `μ_T`-integrable and
`∫ φ d(weylMeasureOn μ T) = ∫_{T(F)} D^G(t)^{1/2} J_G(t, φ) dμ_T(t)`. -/
theorem MaxTorus.integral_weylMeasureOn (T : d.MaxTorus) (μ : ∀ T : Subgroup ↥d.G, Measure ↥T)
    [(μ T.1).IsHaarMeasure] {φ : ↥d.G → ℂ} (hφ : Integrable φ (d.weylMeasureOn μ T.1)) :
    Integrable (fun t : ↥T.1 => d.weylIntegrand μ φ T.1 t) (μ T.1) ∧
      ∫ g, φ g ∂d.weylMeasureOn μ T.1 = ∫ t : ↥T.1, d.weylIntegrand μ φ T.1 t ∂μ T.1 := by
  have : LocallyCompactSpace ↥T.1 := T.isClosed.locallyCompactSpace
  have : SecondCountableTopology ↥T.1 := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have : IsFiniteMeasureOnCompacts (d.quotMeasureOn T.1 (μ T.1)) := by
    have := T.isMulRightInvariant (μ T.1)
    exact (T.quotMeasureOn_spec (μ T.1)).isFiniteMeasureOnCompacts continuous_subtypeVal
      T.isClosed.isClosedEmbedding_subtypeVal
  -- supplied by hand: found by instance search, but the `SigmaFinite` term built from it
  -- exceeds the default `synthInstance.maxSize`
  have : SigmaCompactSpace (CosetSpace T.1.subtype) := inferInstance
  have hΦ : Measurable (d.weylConj T.1) := T.continuous_weylConj.measurable
  have hρ := d.measurable_weylDensity T.1
  have hρt : ∀ᵐ t ∂μ T.1, d.weylDensity T.1 t < ∞ :=
    Filter.Eventually.of_forall (d.weylDensity_lt_top T.1)
  have hφ' : Integrable (φ ∘ d.weylConj T.1)
      (((μ T.1).withDensity (d.weylDensity T.1)).prod (d.quotMeasureOn T.1 (μ T.1))) :=
    hφ.comp_aemeasurable hΦ.aemeasurable
  have hpt : ∀ t : ↥T.1, (d.weylDensity T.1 t).toReal •
      ∫ q, (φ ∘ d.weylConj T.1) (t, q) ∂d.quotMeasureOn T.1 (μ T.1) =
        d.weylIntegrand μ φ T.1 t := d.weylDensity_smul_integral μ T.1 φ
  refine ⟨?_, ?_⟩
  · have h := (integrable_withDensity_iff_integrable_smul' hρ hρt).1 hφ'.integral_prod_left
    simp_rw [hpt] at h
    exact h
  · unfold weylMeasureOn
    rw [integral_map hΦ.aemeasurable hφ.aestronglyMeasurable, ← Function.comp_def φ,
      integral_prod _ hφ', integral_withDensity_eq_integral_toReal_smul hρ hρt]
    simp_rw [hpt]

/-! ## `weylMeasure = haar` -/

/-- **The Weyl integration formula for `1_U`**, `U` compact open, in measure form: each torus term
is finite (`isFiniteMeasureOnCompacts_weylMeasureOn`), so the formula for `1_U ∈ C_c^∞(G(F))`
(`weyl_integration`) reads `Σ_c |W|⁻¹ weylMeasureOn μ T_c (U) = haar U`. -/
theorem weylMeasure_apply_eq_haar (μ : ∀ T : Subgroup ↥d.G, Measure ↥T)
    (hμ : ∀ T : d.MaxTorus, (μ T.1).IsHaarMeasure) {U : Set ↥d.G} (hUc : IsCompact U)
    (hUo : IsOpen U) : d.weylMeasure μ U = Measure.haar U := by
  have hUm : MeasurableSet U := hUo.measurableSet
  set f : ↥d.G → ℂ := U.indicator fun _ => 1
  have hf : f ∈ testFunctions ↥d.G := indicator_mem_testFunctions hUc ⟨hUc.isClosed, hUo⟩
  have hW := d.weyl_integration μ hμ f hf
  -- each torus term is `|W|⁻¹ weylMeasureOn μ T (U)`, a finite number
  set a : d.MaxTorusClass → ℝ≥0∞ := fun c =>
    (d.weylWeight (Quot.out c).1 • d.weylMeasureOn μ (Quot.out c).1) U
  have ha : ∀ c, a c ≠ ∞ := fun c => by
    have := hμ (Quot.out c)
    have := (Quot.out c).isFiniteMeasureOnCompacts_weylMeasureOn μ
    exact ENNReal.mul_ne_top (weylWeight_ne_top _) (hUc.measure_lt_top).ne
  have hterm : ∀ c : d.MaxTorusClass, ((weylCardG d (Quot.out c).1 : ℂ))⁻¹ *
      ∫ t : ↥(Quot.out c).1, d.weylIntegrand μ f (Quot.out c).1 t ∂μ (Quot.out c).1 =
        ((a c).toReal : ℂ) := fun c => by
    have := hμ (Quot.out c)
    have := (Quot.out c).isFiniteMeasureOnCompacts_weylMeasureOn μ
    have hint : Integrable f (d.weylMeasureOn μ (Quot.out c).1) :=
      (integrableOn_const hUc.measure_lt_top.ne).integrable_indicator hUm
    rw [← ((Quot.out c).integral_weylMeasureOn μ hint).2, integral_indicator_const _ hUm,
      ← weylWeight_toReal, Measure.real, Complex.real_smul, mul_one, ← Complex.ofReal_mul,
      ← ENNReal.toReal_mul]
    rfl
  have hsum : ((Measure.haar U).toReal : ℂ) = ∑' c, ((a c).toReal : ℂ) := by
    rw [← tsum_congr hterm]
    have : ∫ g, f g ∂Measure.haar = ((Measure.haar U).toReal : ℂ) := by
      rw [integral_indicator_const _ hUm, Measure.real, Complex.real_smul, mul_one]
    rw [← this, hW]
    rfl
  rw [← Complex.ofReal_tsum] at hsum
  have hsum' : (Measure.haar U).toReal = ∑' c, (a c).toReal := Complex.ofReal_injective hsum
  rw [weylMeasure, Measure.sum_apply _ hUm]
  rcases U.eq_empty_or_nonempty with rfl | hne
  · simp
  have hpos : 0 < (Measure.haar U).toReal :=
    ENNReal.toReal_pos (hUo.measure_ne_zero _ hne) hUc.measure_lt_top.ne
  have hsumm : Summable fun c => (a c).toReal := by
    by_contra h
    rw [tsum_eq_zero_of_not_summable h] at hsum'
    exact hpos.ne' hsum'
  change ∑' c, a c = _
  rw [← ENNReal.ofReal_toReal hUc.measure_lt_top.ne, hsum',
    ENNReal.ofReal_tsum_of_nonneg (fun c => ENNReal.toReal_nonneg) hsumm]
  exact tsum_congr fun c => (ENNReal.ofReal_toReal (ha c)).symm

/-- **The right side of the Weyl integration formula is Haar measure**: `weylMeasure μ = dg` for
every family `μ` of Haar measures on the maximal tori.  The two agree on compact open sets
(`weylMeasure_apply_eq_haar`), which form a π-system generating the Borel σ-algebra of `G(F)`
(`measure_ext_of_isCompact_isOpen`). -/
theorem weylMeasure_eq_haar (μ : ∀ T : Subgroup ↥d.G, Measure ↥T)
    (hμ : ∀ T : d.MaxTorus, (μ T.1).IsHaarMeasure) : d.weylMeasure μ = Measure.haar := by
  have : TotallyDisconnectedSpace ↥d.G := totallyDisconnectedSpace_subgroup F d.ambient d.G
  refine (measure_ext_of_isCompact_isOpen (fun U hUc _ => hUc.measure_lt_top.ne)
    fun U hUc hUo => (weylMeasure_apply_eq_haar μ hμ hUc hUo).symm).symm

/-! ## The formula for integrable functions -/

/-- **The Weyl integration formula for integrable functions**: for `φ ∈ L¹(G(F))` and every
family `μ` of Haar measures on the maximal tori,
`∫_{G(F)} φ(g) dg = Σ_{T ∈ 𝒯(G)} |W(G,T)|⁻¹ ∫_{T(F)} D^G(t)^{1/2} J_G(t, φ) dt`,
with the right side absolutely convergent: the Weyl integrand is integrable on each torus (with
`|W(G,T)| ≠ 0`; for `|W(G,T)| = 0` the Lean term is `0`) and the sum over `𝒯(G)` converges.
BP §1.7 (p. 32) states the formula for `f ∈ C_c^∞(G(F))` (`weyl_integration`); the extension is by
`weylMeasure_eq_haar` and Fubini (`MaxTorus.integral_weylMeasureOn`). -/
theorem weyl_integration_integrable (μ : ∀ T : Subgroup ↥d.G, Measure ↥T)
    (hμ : ∀ T : d.MaxTorus, (μ T.1).IsHaarMeasure) {φ : ↥d.G → ℂ}
    (hφ : Integrable φ Measure.haar) :
    (∀ c : d.MaxTorusClass, weylCardG d (Quot.out c).1 ≠ 0 →
        Integrable (fun t : ↥(Quot.out c).1 => d.weylIntegrand μ φ (Quot.out c).1 t)
          (μ (Quot.out c).1)) ∧
      Summable (fun c : d.MaxTorusClass => ((weylCardG d (Quot.out c).1 : ℂ))⁻¹ *
        ∫ t : ↥(Quot.out c).1, d.weylIntegrand μ φ (Quot.out c).1 t ∂μ (Quot.out c).1) ∧
      ∫ g, φ g ∂Measure.haar = d.gammaIntegral μ (d.weylIntegrand μ φ) := by
  rw [← weylMeasure_eq_haar μ hμ] at hφ ⊢
  unfold weylMeasure at hφ ⊢
  have hc : ∀ c : d.MaxTorusClass, weylCardG d (Quot.out c).1 ≠ 0 →
      Integrable φ (d.weylMeasureOn μ (Quot.out c).1) := fun c hn =>
    (integrable_smul_measure (mt (weylWeight_eq_zero_iff _).1 hn) (weylWeight_ne_top _)).1
      (hφ.mono_measure (Measure.le_sum (fun c : d.MaxTorusClass =>
        d.weylWeight (Quot.out c).1 • d.weylMeasureOn μ (Quot.out c).1) c))
  have hterm : ∀ c : d.MaxTorusClass,
      ∫ g, φ g ∂(d.weylWeight (Quot.out c).1 • d.weylMeasureOn μ (Quot.out c).1) =
        ((weylCardG d (Quot.out c).1 : ℂ))⁻¹ *
          ∫ t : ↥(Quot.out c).1, d.weylIntegrand μ φ (Quot.out c).1 t ∂μ (Quot.out c).1 :=
    fun c => by
      rw [integral_smul_measure, Complex.real_smul, weylWeight_toReal]
      by_cases hn : weylCardG d (Quot.out c).1 = 0
      · rw [hn, Nat.cast_zero, inv_zero, zero_mul, zero_mul]
      · have := hμ (Quot.out c)
        rw [((Quot.out c).integral_weylMeasureOn μ (hc c hn)).2]
  have hs := hasSum_integral_measure hφ
  simp_rw [hterm] at hs
  refine ⟨fun c hn => ?_, hs.summable, hs.tsum_eq.symm⟩
  have := hμ (Quot.out c)
  exact ((Quot.out c).integral_weylMeasureOn μ (hc c hn)).1

/-- **Weyl integration against an invariant function**: if `θ(g⁻¹ t g) = θ(t)` for `t ∈ G_reg(F)`
and `θ f ∈ L¹(G(F))`, then `∫_{G(F)} θ f dg = ∫_{Γ(G)} θ(x) D^G(x)^{1/2} J_G(x, f) dx`
(`J_G(t, θ f) = θ(t) J_G(t, f)` for regular `t`, and `weyl_integration_integrable`). -/
theorem integral_mul_invariant (μ : ∀ T : Subgroup ↥d.G, Measure ↥T)
    (hμ : ∀ T : d.MaxTorus, (μ T.1).IsHaarMeasure) {θ f : ↥d.G → ℂ}
    (hθ : ∀ t ∈ regularSet d.G d.lie, ∀ g : ↥d.G, θ (g⁻¹ * t * g) = θ t)
    (hint : Integrable (fun g => θ g * f g) Measure.haar) :
    ∫ g, θ g * f g ∂Measure.haar =
      d.gammaIntegral μ (fun T t => θ t * d.weylIntegrand μ f T t) := by
  rw [(weyl_integration_integrable μ hμ hint).2.2]
  congr 1
  funext T t
  unfold weylIntegrand orbitalIntegralOn
  split_ifs with ht
  · simp_rw [hθ t ht, integral_const_mul]
    ring
  · rw [mul_zero]

end GGPData

end GSpinGGP
