/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.ThetaFBP
import GSpinGGP.GGP.LeviOpp

/-!
# `θ_f` does not depend on the choice `L` versus `L.opp` of presentation

`L.opp` (opposite flags, same bases, negated weights) has the same Levi subgroup `M`
(`FlagLeviDatum.opp_M`), and the same `K` is good and special for it (`ReducedLeviDatum.oppK`,
`oppK_isSpecial`).  Beuzart-Plessis' `θ_f(x)` (`thetaFBP`) is built from `M`, `A_M(F)`, `d_c t`
and Arthur's weight `v_M`; all of them agree for the two presentations:

* `IsMx.opp`: `IsMx` is the same (same `M`, same `A_M(F)`, `opp_AMF`);
* `opp_AGx`, `opp_AGxOne`, `opp_dcMeasure`: `A_{G_x}(F)`, its maximal compact subgroup, and `d_c t`;
* `opp_thetaFBP`: **`θ_f` is the same**, from these, `opp_finrank_aMG` (the sign) and `opp_vM`
  (the weight, `GGP/LeviOpp.lean`).
-/

noncomputable section

open MeasureTheory Module

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable {d : GGPData F}

namespace ReducedLeviDatum

variable (L : d.ReducedLeviDatum)

/-- `A_{G_x}(F)` is the same for `L` and `L.opp` (`opp_AMF`). -/
theorem opp_AGx (x : ↥d.G) : L.opp.AGx x = L.AGx x := by
  simp only [ReducedLeviDatum.AGx, opp_AMF]

/-- **`A_{G_x}(F)^1` is the same for `L` and `L.opp`**: both are `A_{G_x}(F) ∩ latticeK` of the same
bases (`AGxOne_eq_preimage`). -/
theorem opp_AGxOne (x : ↥d.G) (a : ↥(d.centG x)) (ha : a ∈ L.AGx x) (ha' : a ∈ L.opp.AGx x) :
    (⟨a, ha'⟩ : ↥(L.opp.AGx x)) ∈ L.opp.AGxOne x ↔ (⟨a, ha⟩ : ↥(L.AGx x)) ∈ L.AGxOne x := by
  rw [← SetLike.mem_coe, ← SetLike.mem_coe, ReducedLeviDatum.AGxOne_eq_preimage,
    ReducedLeviDatum.AGxOne_eq_preimage]
  rfl

/-- `IsDcMeasure` with `A_{G_x}(F)^1` written as `A_{G_x}(F) ∩ latticeK` (`AGxOne_eq_preimage`). -/
theorem isDcMeasure_iff_preimage (x : ↥d.G) (μ : Measure ↥(d.centG x)) :
    L.IsDcMeasure x μ ↔ μ.IsHaarMeasure ∧ ∃ (μA : Measure ↥(L.AGx x))
      (m : Measure (CosetSpace (L.AGx x).subtype)), μA.IsHaarMeasure ∧
        μA ((fun a : ↥(L.AGx x) => ((a : ↥(d.centG x)) : ↥d.G)) ⁻¹'
          d.latticeK L.bWFin L.bVFin) = 1 ∧
        IsWeilMeasure (L.AGx x).subtype μ μA m ∧ m Set.univ = 1 := by
  rw [ReducedLeviDatum.IsDcMeasure, ReducedLeviDatum.AGxOne_eq_preimage]

/-- **The normalization of `d_c t` is the same for `L` and `L.opp`.** -/
theorem opp_isDcMeasure (x : ↥d.G) : L.opp.IsDcMeasure x = L.IsDcMeasure x := by
  funext μ
  apply propext
  rw [isDcMeasure_iff_preimage, isDcMeasure_iff_preimage, opp_AGx]
  rfl

/-- **`d_c t` is the same for `L` and `L.opp`.** -/
theorem opp_dcMeasure (x : ↥d.G) : L.opp.dcMeasure x = L.dcMeasure x := by
  unfold ReducedLeviDatum.dcMeasure
  rw [opp_isDcMeasure]

variable {L} in
/-- **`IsMx` is the same for `L` and `L.opp`**: same `M`, same `A_M(F)`. -/
theorem IsMx.opp {x : ↥d.G} (h : L.IsMx x) : L.opp.IsMx x where
  regular := h.regular
  mem := by
    change x ∈ L.toFlagLeviDatum.opp.M
    rw [FlagLeviDatum.opp_M]; exact h.mem
  compact := by
    rw [L.opp_AGx x]; exact h.compact

/-- **`θ_f` is the same for `(L, K)` and `(L.opp, K)`**, for every `f` and `x`: the sign
(`opp_finrank_aMG`), `d_c t` (`opp_dcMeasure`) and `v_M` (`opp_vM`) agree. -/
theorem opp_thetaFBP (K : d.GoodK L.toFlagLeviDatum) (f : ↥d.G → ℂ) (x : ↥d.G) :
    L.opp.thetaFBP (L.oppK K) f x = L.thetaFBP K f x := by
  simp only [ReducedLeviDatum.thetaFBP, weightedOrbitalIntegral, weightedIntegrand,
    opp_finrank_aMG, opp_dcMeasure, opp_vM]

end ReducedLeviDatum

end GGPData

end GSpinGGP
