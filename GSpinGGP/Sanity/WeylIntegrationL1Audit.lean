/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.WeylIntegrationL1
import GSpinGGP.Sanity.GammaGAudit
import GSpinGGP.Sanity.AxiomRedTeam.HarishChandra

/-!
# Check of `MaxTorus.isFiniteMeasureOnCompacts_weylMeasureOn` at the toy datum

At `toyD` (`G = GL₁ × GL₁`, commutative, `D^G = 1`) the only maximal torus is `T(F) = G(F)`,
`T(F)\G(F)` is a point and `(t, ġ) ↦ g⁻¹ t g` is `t ↦ t`, so `weylMeasureOn μ T` is
`m(T\G) · μ_T` transported to `G(F)`, which is finite on compact sets
(`toyD_isFiniteMeasureOnCompacts_weylMeasureOn`, proved without the axiom
`weyl_integration_exists`, from which the general statement is derived).  So the statement holds
in this degenerate instance independently of the axiom (used in
`Sanity/AxiomRedTeam/WeylIntegration.lean` to verify the axiom's convergence conjunct at `toyD`).
-/

noncomputable section

open MeasureTheory GSpinGGP.Sanity GSpinGGP.AxiomRedTeam

namespace GSpinGGP.GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝕋" => (toyD (F := F))

/-- **The torus term of the Weyl measure is finite on compact sets at `toyD`.** -/
theorem toyD_isFiniteMeasureOnCompacts_weylMeasureOn (T : (𝕋).MaxTorus)
    (μ : ∀ T : Subgroup ↥(𝕋).G, Measure ↥T) [(μ T.1).IsHaarMeasure] :
    IsFiniteMeasureOnCompacts ((𝕋).weylMeasureOn μ T.1) := by
  have : LocallyCompactSpace ↥T.1 := T.isClosed.locallyCompactSpace
  have : SecondCountableTopology ↥T.1 := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have : IsFiniteMeasureOnCompacts ((𝕋).quotMeasureOn T.1 (μ T.1)) := by
    have := T.isMulRightInvariant (μ T.1)
    exact (T.quotMeasureOn_spec (μ T.1)).isFiniteMeasureOnCompacts continuous_subtypeVal
      T.isClosed.isClosedEmbedding_subtypeVal
  have hT := toyD_maxTorus_eq_top T
  have := subsingleton_cosetSpace_of_eq_top hT
  -- `(t, ġ) ↦ g⁻¹ t g` is `t ↦ t`
  have hΦ : ∀ p, (𝕋).weylConj T.1 p = (p.1 : ↥(𝕋).G) := fun p => by
    unfold weylConj
    rw [toyD_G_comm _ (p.1 : ↥(𝕋).G), inv_mul_cancel_right]
  refine ⟨fun K hK => ?_⟩
  set S : Set ↥T.1 := Subtype.val ⁻¹' K
  have hS : IsCompact S := T.isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hpre : (𝕋).weylConj T.1 ⁻¹' K = S ×ˢ Set.univ := by
    ext p; simp [hΦ, S]
  unfold weylMeasureOn
  rw [Measure.map_apply T.continuous_weylConj.measurable hK.measurableSet, hpre,
    Measure.prod_prod]
  refine ENNReal.mul_lt_top ?_ (Set.subsingleton_univ.isCompact.measure_lt_top)
  rw [withDensity_apply _ hS.measurableSet]
  have hρ : ∀ t, (𝕋).weylDensity T.1 t ≤ 1 := fun t => by
    unfold weylDensity
    by_cases ht : (t : ↥(𝕋).G) ∈ regularSet (𝕋).G (𝕋).lie
    · rw [Set.indicator_of_mem ht, weylDisc_eq_absF_hcDisc _ ht, toyD_hcDisc, absF_one,
        ENNReal.ofReal_one]
    · rw [Set.indicator_of_notMem ht]; exact zero_le_one
  calc ∫⁻ t in S, (𝕋).weylDensity T.1 t ∂μ T.1 ≤ ∫⁻ _ in S, 1 ∂μ T.1 := lintegral_mono hρ
    _ = μ T.1 S := by rw [setLIntegral_one]
    _ < ⊤ := hS.measure_lt_top

end GSpinGGP.GGPData
