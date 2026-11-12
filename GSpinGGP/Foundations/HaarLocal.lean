/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Haar measures are determined near the identity

* `Measure.eq_of_isHaarMeasure_of_eqOn_nhds`: two Haar measures on a second countable locally
  compact group that agree on the measurable subsets of a neighbourhood of `1` are equal.
* `Measure.eq_of_isHaarMeasure_of_eq_near_one`: the same, when both agree near `1` with a common
  reference set function (e.g. the `exp`-image measure of a torus).
-/

open MeasureTheory Topology Filter

namespace MeasureTheory.Measure

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- **Two Haar measures that agree near `1` are equal**: `ν = c • μ`
(`isMulLeftInvariant_eq_smul`), and the interior of a compact neighbourhood `K ⊆ U` of `1` has
`0 < μ (interior K) < ∞`, so `c = 1`. -/
@[to_additive /-- **Two additive Haar measures that agree near `0` are equal**: `ν = c • μ`
(`isAddLeftInvariant_eq_smul`), and the interior of a compact neighbourhood `K ⊆ U` of `0` has
`0 < μ (interior K) < ∞`, so `c = 1`. -/]
theorem eq_of_isHaarMeasure_of_eqOn_nhds (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    {U : Set G} (hU : U ∈ 𝓝 1) (h : ∀ S, MeasurableSet S → S ⊆ U → μ S = ν S) : μ = ν := by
  have hc : ν = Measure.haarScalarFactor ν μ • μ := Measure.isMulLeftInvariant_eq_smul ν μ
  obtain ⟨K, hK, hKU, hKc⟩ := local_compact_nhds hU
  have hI : interior K ∈ 𝓝 1 := interior_mem_nhds.2 hK
  have h0 : μ (interior K) ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hI).ne'
  have htop : μ (interior K) ≠ ⊤ :=
    (measure_mono interior_subset |>.trans_lt hKc.measure_lt_top).ne
  have hK' := h _ isOpen_interior.measurableSet (interior_subset.trans hKU)
  rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hK'
  have h1 := (ENNReal.mul_eq_right h0 htop).mp hK'.symm
  rw [hc, ENNReal.coe_eq_one.mp h1, one_smul]

/-- Two Haar measures that both agree near `1` with a set function `m` are equal
(`eq_of_isHaarMeasure_of_eqOn_nhds` on the intersection of the two neighbourhoods). -/
@[to_additive /-- Two additive Haar measures that both agree near `0` with a set function `m` are
equal (`eq_of_isAddHaarMeasure_of_eqOn_nhds` on the intersection of the two neighbourhoods). -/]
theorem eq_of_isHaarMeasure_of_eq_near_one {μ ν : Measure G} [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    (m : Set G → ENNReal) (hμ : ∃ U ∈ 𝓝 (1 : G), ∀ S, MeasurableSet S → S ⊆ U → μ S = m S)
    (hν : ∃ U ∈ 𝓝 (1 : G), ∀ S, MeasurableSet S → S ⊆ U → ν S = m S) : μ = ν := by
  obtain ⟨U, hU, hμU⟩ := hμ
  obtain ⟨U', hU', hνU⟩ := hν
  exact eq_of_isHaarMeasure_of_eqOn_nhds μ ν (inter_mem hU hU') fun S hS hSU =>
    (hμU S hS (hSU.trans Set.inter_subset_left)).trans
      (hνU S hS (hSU.trans Set.inter_subset_right)).symm

end MeasureTheory.Measure
