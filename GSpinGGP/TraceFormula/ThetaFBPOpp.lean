/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.ThetaFBPPresentation
import GSpinGGP.GGP.LeviOpp

/-!
# `θ_f` does not depend on the choice `L` versus `L.opp` of presentation

`L.opp` (opposite flags, same bases, negated weights) has the same Levi subgroup `M`
(`FlagLeviDatum.opp_M`), its weight spaces are those of `L` relabelled by `w ↦ −w`
(`sameWtSpaces_opp`), and the same `K` is good and special for it (`ReducedLeviDatum.oppK`,
`oppK_isSpecial`).  So, as instances of `TraceFormula/ThetaFBPPresentation.lean`:

* `IsMx.opp`: `IsMx` is the same;
* `opp_dcMeasure`: `d_c t` is the same;
* `opp_thetaFBP`: **`θ_f` is the same**, for every `f` and `x`.
-/

noncomputable section

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable {d : GGPData F}

namespace ReducedLeviDatum

variable (L : d.ReducedLeviDatum)

/-- **`d_c t` is the same for `L` and `L.opp`.** -/
theorem opp_dcMeasure (x : ↥d.G) : L.opp.dcMeasure x = L.dcMeasure x :=
  dcMeasure_eq_of_sameWtSpaces L.sameWtSpaces_opp.1 L.sameWtSpaces_opp.2 x

variable {L} in
/-- **`IsMx` is the same for `L` and `L.opp`**: same `M`, same `A_M(F)`. -/
theorem IsMx.opp {x : ↥d.G} (h : L.IsMx x) : L.opp.IsMx x :=
  h.of_sameWtSpaces L.sameWtSpaces_opp.1 L.sameWtSpaces_opp.2

/-- **`θ_f` is the same for `(L, K)` and `(L.opp, K)`**, for every `f` and `x`
(`thetaFBP_eq_of_sameWtSpaces`). -/
theorem opp_thetaFBP (K : d.GoodK L.toFlagLeviDatum) (f : ↥d.G → ℂ) (x : ↥d.G) :
    L.opp.thetaFBP (L.oppK K) f x = L.thetaFBP K f x :=
  thetaFBP_eq_of_sameWtSpaces L.sameWtSpaces_opp.1 L.sameWtSpaces_opp.2 K (L.oppK K) rfl f x

end ReducedLeviDatum

end GGPData

end GSpinGGP
