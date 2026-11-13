/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.ExpIntertwine
import GSpinGGP.Foundations.ExpHaar

/-!
# The `exp`-compatible measure on `𝔥⁰(F)`

`exists_isExpCompatH`: an additive Haar measure on `𝔥⁰(F)` compatible through `exp` with
`Measure.haar` on `H(F)/A_{G,H}(F)` (`IsExpCompatH`, defined in `TraceFormula/LieAlgebra.lean`), so
that `measH0` is `exp`-compatible (`isExpCompatH_measH0`).
-/

noncomputable section

open MeasureTheory Topology Filter

set_option linter.style.haveILetI false

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

/-- **An `exp`-compatible Haar measure on `𝔥⁰(F)` exists** (BP §1.6, Thesis §10.1, §12.4): near
`0`, `X ↦ e^X` is a homeomorphism from a neighbourhood of `0` in `𝔥⁰(F)` onto a neighbourhood of
`1` in `H(F)/A_{G,H}(F)` (`𝔥 = Lie(A_{G,H}) ⊕ 𝔥⁰`), and on a small enough lattice it carries an
additive Haar measure to a Haar measure (the Jacobian `j^H` is `1` near `0` in the `p`-adic case).
Proved via the isometry chart (`exists_isAddHaarMeasure_eq_expA_image`, with
`j : H(F) → (C(W) × C(V))ˣ`, the scalars `A_{G,H}(F) ⊆ H(F)`, `exp` into `H(F)` by
`eventually_exists_mem_H_eq_expA` and the logarithm by
`eventually_exists_sub_algebraMap_mem_lieH0`). -/
theorem exists_isExpCompatH : ∃ μ, d.IsExpCompatH μ := by
  haveI := submodule_isTopologicalAddGroup d.lieH0
  obtain ⟨_, _, _, _, _⟩ := submodule_topology d.lieH0
  let j : ↥d.H →* d.ambientˣ := d.G.subtype.comp d.H.subtype
  have hj : Topology.IsEmbedding fun h : ↥d.H => ((j h : d.ambientˣ) : d.ambient) :=
    (isEmbedding_units_val F).comp
      (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal)
  have hZ : ∀ h : ↥d.H, h ∈ d.AGHinH ↔
      ((j h : d.ambientˣ) : d.ambient) ∈ Set.range (algebraMap F d.ambient) := by
    intro h
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨(c : F), ?_⟩
      rw [← GGPData.coe_diag_scalarGSpin c]
      exact congrArg (fun g : ↥d.G => ((g : d.ambientˣ) : d.ambient)) hc
    · rintro ⟨c, hc⟩
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [map_zero] at hc
        exact Units.ne_zero _ hc.symm
      refine ⟨Units.mk0 c hc0, Subtype.ext (Units.ext ?_)⟩
      change (((d.diag (scalarGSpin d.QW (Units.mk0 c hc0)) : ↥d.G) : d.ambientˣ) :
        d.ambient) = _
      rw [GGPData.coe_diag_scalarGSpin]; exact hc
  have hscal : ∀ c : F, c ≠ 0 → ∃ h : ↥d.H,
      ((j h : d.ambientˣ) : d.ambient) = algebraMap F d.ambient c :=
    fun c hc => ⟨⟨d.diag (scalarGSpin d.QW (Units.mk0 c hc)), d.AGH_le_H ⟨_, rfl⟩⟩,
      GGPData.coe_diag_scalarGSpin (Units.mk0 c hc)⟩
  obtain ⟨μ, hμ, U, hU, hUS⟩ := exists_isAddHaarMeasure_eq_expA_image j hj d.AGHinH hZ hscal
    d.lieH0 (fun t ht => eq_zero_of_algebraMap_mem_soSub (Q := d.QW) ht.1.1)
    d.eventually_exists_mem_H_eq_expA d.eventually_exists_sub_algebraMap_mem_lieH0
    (Measure.haar : Measure d.HmodAGH)
  exact ⟨μ, hμ, U, hU, hUS⟩

/-- `measH0` is `exp`-compatible (`exists_isExpCompatH`). -/
theorem isExpCompatH_measH0 : d.IsExpCompatH d.measH0 := by
  have h := d.exists_isExpCompatH
  unfold measH0
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

end GGPData

end GSpinGGP
