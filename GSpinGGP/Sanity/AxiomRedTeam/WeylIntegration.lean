/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Sanity.GammaGAudit
import GSpinGGP.Sanity.WeylIntegrationL1Audit
import GSpinGGP.TraceFormula.WeylIntegration
import GSpinGGP.TraceFormula.WeylIntegrationL1
import GSpinGGP.Literature.HarishChandra

/-!
# Check of `weyl_integration_exists` (BP §1.7, the Weyl integration formula)

* **V at `toyD`** (`toyD_weyl_integration_exists_check`): the full statement of the axiom, all three
  conjuncts, proved without it, from Weil's formula (`toyD_weyl_integration`), the Haar family
  `haarFamily`, and for the `[0, ∞]` convergence conjunct the axiom-free
  `toyD_isFiniteMeasureOnCompacts_weylMeasureOn` with
  `lintegral_conjunct_of_isFiniteMeasureOnCompacts`
  (finiteness of a torus term on compacts implies the conjunct, for any datum, without the axiom).
  At `toyD` the right side is a genuine sum and integral, not a junk value: the class sum is finite
  (`toyD_summable_gammaIntegral`) and the integrand is integrable on the torus
  (`toyD_integrable_weylIntegrand`).
* **Non-vacuity of the `∀`-form, any datum** (`isHaarMeasure_haarFamily`): every datum has a family
  of Haar measures on its maximal tori, so `weyl_integration` is not vacuous, and the `∃` of the axiom
  asserts no existence beyond Haar measures on closed subgroups.
* **Junk values.**
  - The zero family makes the right side `0` (`gammaIntegral_zero_family`), while some test function
    has nonzero integral (`exists_testFunction_integral_ne_zero`), so the Haar conjunct is needed
    (`not_formula_zero_family`).
  - An empty set of classes would make the `tsum` `0` (`gammaIntegral_of_isEmpty`); the axiom
    therefore implies that maximal tori exist (`nonempty_maxTorusClass_of_axiom`). **C**: the same
    follows from Harish-Chandra's density of `G_reg(F)` (`hc_regular_open_dense_conull`), without
    the new axiom (`nonempty_maxTorusClass`; it uses `hc_regular_open_dense_conull` and, through
    `mem_regularSet_of_hcDisc_ne_zero`, `jantzen_finrank_soCentMat_ge`), so no conflict arises.
  - The `tsum` over classes is the finite sum when there are finitely many classes
    (`gammaIntegral_eq_sum`), as in BP. Independence of the torus measures holds term by term,
    with no integrability or summability hypothesis (`gammaIntegral_weylIntegrand_eq`), so the
    `∃`-form and the `∀`-form agree whatever the junk conventions.

* **The counter-model `ν₁ = ∞ · δ_x`** (why the third conjunct was added). The real-valued
  identity cannot see an infinite atom in a torus term (`toReal_top_smul_dirac`,
  `counterModel_toReal`: `haar`, `∞ · δ_x` satisfy `ν₀(U).toReal + ν₁(U).toReal = haar(U).toReal`
  for every `U`), while the `[0, ∞]` form does (`counterModel_lintegral`). With the third conjunct
  every torus term is finite on compacts for every Haar family, so it has no infinite atom
  (`weylMeasureOn_singleton_lt_top_of_axiom`, `weylMeasureOn_ne_top_smul_dirac_of_axiom`).
* **No new conflict**: the strengthened statement still holds at `toyD` without the axiom (above),
  and its only consequence beyond the first two conjuncts, finiteness of the torus terms on
  compacts, is what `weylMeasure_eq_haar` needs; at `toyD` it is the axiom-free
  `toyD_isFiniteMeasureOnCompacts_weylMeasureOn`.

* **Implicit consequence**: the axiom forces some class of tori with a finite Weyl group
  (`weylCardG ≠ 0`) and a nonzero torus integral (`exists_class_weylCardG_ne_zero_of_axiom`).
  True for `GSpin`; not proved independently here.

Not covered (accepted gap): nonabelian `G`, `|W(G,T)| > 1`, `D^G ≠ 1`, several classes of tori.
All nonabelian content of the formula (the power of `D^G`, the Weyl weights, the sum over
classes) is untested; even `weylDisc` at a regular element of the nonabelian datum `gl2Data` is
not computed (it is the trailing coefficient of a characteristic polynomial on the Lie algebra
inside a Clifford algebra, not a cheap computation).
-/

open MeasureTheory GSpinGGP GSpinGGP.Sanity GSpinGGP.GGPData
open scoped ENNReal

noncomputable section

namespace GSpinGGP.AxiomRedTeam

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

open scoped Classical in
/-- A family of Haar measures on the closed subgroups of `G(F)` (`0` on the others). -/
def haarFamily (d : GGPData F) : ∀ T : Subgroup ↥d.G, Measure ↥T := fun T =>
  if h : IsClosed (T : Set ↥d.G) then
    haveI : LocallyCompactSpace ↥T := h.locallyCompactSpace
    Measure.haar
  else 0

/-- **Every datum has a family of Haar measures on its maximal tori.** -/
theorem isHaarMeasure_haarFamily (d : GGPData F) (T : d.MaxTorus) :
    (haarFamily d T.1).IsHaarMeasure := by
  have h := T.isClosed
  have : LocallyCompactSpace ↥T.1 := h.locallyCompactSpace
  simp only [haarFamily, dite_eq_left h]
  infer_instance

/-- **The convergence conjunct from finiteness on compacts** (no axiom): if a torus term
`weylMeasureOn μ T` is finite on compact sets, the third conjunct of `weyl_integration_exists`
holds for `μ` and `T` (Tonelli, `MaxTorus.lintegral_weylMeasureOn`; a test function is bounded with
compact support). -/
theorem lintegral_conjunct_of_isFiniteMeasureOnCompacts (d : GGPData F)
    (μ : ∀ T : Subgroup ↥d.G, Measure ↥T) (T : d.MaxTorus) [(μ T.1).IsHaarMeasure]
    [IsFiniteMeasureOnCompacts (d.weylMeasureOn μ T.1)] {f : ↥d.G → ℂ}
    (hf : f ∈ testFunctions ↥d.G) :
    ∫⁻ t : ↥T.1, (regularSet d.G d.lie).indicator
        (fun x => ENNReal.ofReal (weylDisc d.lie (x : d.ambientˣ))) (t : ↥d.G) *
      ∫⁻ q, ‖f ((CosetSpace.out _ q)⁻¹ * (t : ↥d.G) * CosetSpace.out _ q)‖ₑ
        ∂d.quotMeasureOn T.1 (μ T.1) ∂μ T.1 < ⊤ := by
  have hint := hf.1.continuous.integrable_of_hasCompactSupport hf.2
    (μ := d.weylMeasureOn μ T.1)
  have h2 := hint.2
  unfold HasFiniteIntegral at h2
  rw [T.lintegral_weylMeasureOn μ hf.1.continuous.measurable.eNorm] at h2
  exact h2

/-- **The axiom at `toyD`, proved without it**, all three conjuncts; the third from
`toyD_isFiniteMeasureOnCompacts_weylMeasureOn` (`Sanity/WeylIntegrationL1Audit.lean`,
axiom-free). -/
theorem toyD_weyl_integration_exists_check :
    ∃ μ : ∀ T : Subgroup ↥(toyD (F := F)).G, Measure ↥T,
      (∀ T : (toyD (F := F)).MaxTorus, (μ T.1).IsHaarMeasure) ∧
      (∀ f ∈ testFunctions ↥(toyD (F := F)).G,
        ∫ g, f g ∂Measure.haar = (toyD (F := F)).gammaIntegral μ
          ((toyD (F := F)).weylIntegrand μ f)) ∧
      ∀ f ∈ testFunctions ↥(toyD (F := F)).G, ∀ T : (toyD (F := F)).MaxTorus,
        ∫⁻ t : ↥T.1, (regularSet (toyD (F := F)).G (toyD (F := F)).lie).indicator
            (fun x => ENNReal.ofReal (weylDisc (toyD (F := F)).lie
              (x : (toyD (F := F)).ambientˣ))) (t : ↥(toyD (F := F)).G) *
          ∫⁻ q, ‖f ((CosetSpace.out _ q)⁻¹ * (t : ↥(toyD (F := F)).G) * CosetSpace.out _ q)‖ₑ
            ∂(toyD (F := F)).quotMeasureOn T.1 (μ T.1) ∂μ T.1 < ⊤ := by
  refine ⟨haarFamily _, isHaarMeasure_haarFamily _, fun _ hf =>
    toyD_weyl_integration _ (isHaarMeasure_haarFamily _) hf.1.continuous hf.2, fun f hf T => ?_⟩
  have := isHaarMeasure_haarFamily _ T
  have := toyD_isFiniteMeasureOnCompacts_weylMeasureOn T (haarFamily _)
  exact lintegral_conjunct_of_isFiniteMeasureOnCompacts _ _ T hf

/-! ### The counter-model `ν₁ = ∞ · δ_x` -/

/-- **The real-valued identity does not see an infinite atom**: `(∞ · δ_x)(U)` has real part `0`
for every `U`, so adding `∞ · δ_x` as a torus term leaves every identity
`Σ_c w_c · ν_c(U).toReal = haar(U).toReal` (the formula of the first two conjuncts for `f = 1_U`)
unchanged. -/
theorem toReal_top_smul_dirac {X : Type*} [MeasurableSpace X] (x : X) (U : Set X) :
    (((⊤ : ℝ≥0∞) • Measure.dirac x) U).toReal = 0 := by
  rw [smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_top, zero_mul]

/-- With `ν₀ = haar`, `ν₁ = ∞ · δ_x`: `ν₀(U).toReal + ν₁(U).toReal = haar(U).toReal` for every `U`
(the formal counter-model to finiteness under the first two conjuncts alone). -/
theorem counterModel_toReal (d : GGPData F) (x : ↥d.G) (U : Set ↥d.G) :
    ((Measure.haar : Measure ↥d.G) U).toReal + (((⊤ : ℝ≥0∞) • Measure.dirac x) U).toReal =
      ((Measure.haar : Measure ↥d.G) U).toReal := by
  rw [toReal_top_smul_dirac, add_zero]

/-- **The `[0, ∞]` form sees it**: `∫⁻ ‖1_U‖ₑ d(∞ · δ_x) = ∞` for `x ∈ U`, so the shape of the third
conjunct rejects an infinite atom in a torus term. -/
theorem counterModel_lintegral (d : GGPData F) {x : ↥d.G} {U : Set ↥d.G} (hU : MeasurableSet U)
    (hx : x ∈ U) :
    ∫⁻ g, ‖U.indicator (1 : ↥d.G → ℂ) g‖ₑ ∂((⊤ : ℝ≥0∞) • Measure.dirac x) = ⊤ := by
  rw [lintegral_smul_measure,
    lintegral_dirac' x (measurable_one.indicator hU).eNorm, Set.indicator_of_mem hx]
  simp

/-- **The axiom excludes the counter-model**: no torus term has an infinite atom, for any Haar
family (`isFiniteMeasureOnCompacts_weylMeasureOn`, from the third conjunct). -/
theorem weylMeasureOn_singleton_lt_top_of_axiom (d : GGPData F)
    (μ : ∀ T : Subgroup ↥d.G, Measure ↥T) (T : d.MaxTorus) [(μ T.1).IsHaarMeasure] (x : ↥d.G) :
    d.weylMeasureOn μ T.1 {x} < ⊤ := by
  have := T.isFiniteMeasureOnCompacts_weylMeasureOn μ
  exact isCompact_singleton.measure_lt_top

/-- In particular no torus term is `∞ · δ_x`. -/
theorem weylMeasureOn_ne_top_smul_dirac_of_axiom (d : GGPData F)
    (μ : ∀ T : Subgroup ↥d.G, Measure ↥T) (T : d.MaxTorus) [(μ T.1).IsHaarMeasure] (x : ↥d.G) :
    d.weylMeasureOn μ T.1 ≠ (⊤ : ℝ≥0∞) • Measure.dirac x := by
  intro h
  have h1 := weylMeasureOn_singleton_lt_top_of_axiom d μ T x
  rw [h, smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton x), smul_eq_mul,
    mul_one] at h1
  exact lt_irrefl _ h1

/-- At `toyD` the sum over classes of tori is a finite sum (one class), hence summable. -/
theorem toyD_summable_gammaIntegral (μ : ∀ T : Subgroup ↥(toyD (F := F)).G, Measure ↥T)
    (φ : Subgroup ↥(toyD (F := F)).G → ↥(toyD (F := F)).G → ℂ) :
    Summable fun c : (toyD (F := F)).MaxTorusClass =>
      ((weylCardG (toyD (F := F)) (Quot.out c).1 : ℂ))⁻¹ *
        ∫ t : ↥(Quot.out c).1, φ (Quot.out c).1 t ∂μ (Quot.out c).1 := by
  have : Finite (toyD (F := F)).MaxTorusClass := Finite.of_subsingleton
  exact Summable.of_finite

/-- At `toyD` the Weyl integrand is integrable on the torus, for every Haar measure and every
continuous compactly supported `f`: the right side of the axiom is not a junk `0`. -/
theorem toyD_integrable_weylIntegrand (μ : ∀ T : Subgroup ↥(toyD (F := F)).G, Measure ↥T)
    (T : (toyD (F := F)).MaxTorus) [(μ T.1).IsHaarMeasure] {f : ↥(toyD (F := F)).G → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun t : ↥T.1 => (toyD (F := F)).weylIntegrand μ f T.1 t) (μ T.1) := by
  simp_rw [toyD_weylIntegrand μ f T]
  have hemb : Topology.IsClosedEmbedding T.1.subtype := T.isClosed.isClosedEmbedding_subtypeVal
  have : LocallyCompactSpace ↥T.1 := T.isClosed.locallyCompactSpace
  exact ((hf.comp continuous_subtypeVal).integrable_of_hasCompactSupport
    (hfc.comp_isClosedEmbedding hemb)).const_mul _

/-- With the zero family of measures the right side vanishes. -/
theorem gammaIntegral_zero_family (d : GGPData F) (φ : Subgroup ↥d.G → ↥d.G → ℂ) :
    d.gammaIntegral (fun _ => 0) φ = 0 := by
  simp [gammaIntegral]

/-- With no classes of maximal tori the right side vanishes. -/
theorem gammaIntegral_of_isEmpty (d : GGPData F) [IsEmpty d.MaxTorusClass]
    (μ : ∀ T : Subgroup ↥d.G, Measure ↥T) (φ : Subgroup ↥d.G → ↥d.G → ℂ) :
    d.gammaIntegral μ φ = 0 := by
  simp [gammaIntegral]

/-- With finitely many classes the `tsum` is BP's finite sum. -/
theorem gammaIntegral_eq_sum (d : GGPData F) [Fintype d.MaxTorusClass]
    (μ : ∀ T : Subgroup ↥d.G, Measure ↥T) (φ : Subgroup ↥d.G → ↥d.G → ℂ) :
    d.gammaIntegral μ φ = ∑ c : d.MaxTorusClass, ((weylCardG d (Quot.out c).1 : ℂ))⁻¹ *
      ∫ t : ↥(Quot.out c).1, φ (Quot.out c).1 t ∂μ (Quot.out c).1 :=
  tsum_fintype _

/-- **Some test function has nonzero integral** (separation by test functions applied to `1`). -/
theorem exists_testFunction_integral_ne_zero (d : GGPData F) :
    ∃ f ∈ testFunctions ↥d.G, ∫ g, f g ∂(Measure.haar : Measure ↥d.G) ≠ 0 := by
  by_contra h
  push Not at h
  have h1 := ae_eq_zero_of_integral_testFunctions (G := ↥d.G) (θ := fun _ => (1 : ℂ))
    (locallyIntegrable_const 1) fun f hf => by simpa using h f hf
  have h0 : (Measure.haar : Measure ↥d.G) Set.univ = 0 := by
    simpa using ae_iff.1 h1
  exact isOpen_univ.measure_ne_zero Measure.haar Set.univ_nonempty h0

/-- **The Haar conjunct is needed**: the formula fails for the zero family. -/
theorem not_formula_zero_family (d : GGPData F) :
    ¬ ∀ f ∈ testFunctions ↥d.G,
      ∫ g, f g ∂Measure.haar = d.gammaIntegral (fun _ => 0) (d.weylIntegrand (fun _ => 0) f) := by
  intro h
  obtain ⟨f, hf, hne⟩ := exists_testFunction_integral_ne_zero d
  exact hne ((h f hf).trans (gammaIntegral_zero_family d _))

/-- **The axiom forces maximal tori to exist** (otherwise its right side is `0`). -/
theorem nonempty_maxTorusClass_of_axiom (d : GGPData F) : Nonempty d.MaxTorusClass := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  obtain ⟨μ, -, hW, -⟩ := weyl_integration_exists d
  obtain ⟨f, hf, hne'⟩ := exists_testFunction_integral_ne_zero d
  exact hne' ((hW f hf).trans (gammaIntegral_of_isEmpty d μ _))

/-- **C: maximal tori exist, without the Weyl axiom**, from Harish-Chandra's density of the
regular set (`hc_regular_open_dense_conull`). -/
theorem nonempty_maxTorusClass (d : GGPData F) : Nonempty d.MaxTorusClass := by
  obtain ⟨x, hx⟩ := (hc_regular_open_dense_conull d).2.1.nonempty
  exact ⟨Quot.mk _ ⟨d.centG x, x, mem_regularSet_of_hcDisc_ne_zero d hx, rfl⟩⟩

/-- **Implicit consequence of the axiom**: some class of maximal tori has a finite Weyl group
(`weylCardG ≠ 0`, i.e. not the junk value of `Nat.card`) and a nonzero torus integral, i.e. a
nonzero, non-junk term in the `tsum`.  True for `GSpin` (`N_{G(F)}(T)/T(F)` is finite). -/
theorem exists_class_weylCardG_ne_zero_of_axiom (d : GGPData F) :
    ∃ μ : ∀ T : Subgroup ↥d.G, Measure ↥T, (∀ T : d.MaxTorus, (μ T.1).IsHaarMeasure) ∧
      ∃ (f : ↥d.G → ℂ) (c : d.MaxTorusClass), f ∈ testFunctions ↥d.G ∧
        weylCardG d (Quot.out c).1 ≠ 0 ∧
        ∫ t : ↥(Quot.out c).1, d.weylIntegrand μ f (Quot.out c).1 t ∂μ (Quot.out c).1 ≠ 0 := by
  obtain ⟨μ, hμ, hW, -⟩ := weyl_integration_exists d
  obtain ⟨f, hf, hne⟩ := exists_testFunction_integral_ne_zero d
  refine ⟨μ, hμ, f, ?_⟩
  by_contra h
  push Not at h
  apply hne
  rw [hW f hf, gammaIntegral]
  refine (tsum_congr fun c => ?_).trans tsum_zero
  by_cases hc : weylCardG d (Quot.out c).1 = 0
  · simp [hc]
  · rw [h c hf hc, mul_zero]

end GSpinGGP.AxiomRedTeam
