/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.SpecialK
import GSpinGGP.GGP.LeviPresentation

/-!
# The opposite presentation `L ↦ L.opp` of a Levi subgroup

`L.opp` (`ReducedLeviDatum.opp`) has the opposite flags, the same bases and the negated weights;
its Levi subgroup is the same (`FlagLeviDatum.opp_M`), and its weight spaces are those of `L`
relabelled by `w ↦ −w` (`sameWtSpaces_opp`, `GGP/LeviPresentation.lean`).

* `GoodK.opp`, `GoodK.IsSpecial.opp`: the same subgroup `K` is good (special) for `L.opp`.
* `ReducedLeviDatum.opp_AMF`, `opp_finrank_aMG`: same `A_M(F)`, `dim a_M^G`.
* `ReducedLeviDatum.opp_vM`: **`v_M` is the same for `L` and `L.opp`**.

The last three are instances of the presentation independence of `GGP/LeviPresentation.lean`
(`AMF_eq_of_sameWtSpaces`, `finrank_aMG_eq_of_sameWtSpaces`, `vM_eq_of_sameWtSpaces`), whose
sign `−` on the `GL`-coordinates comes from determinant duality (`det_wtBlock_neg_mul`,
`GGP/WtSpan.lean`).
-/

noncomputable section

open Module MeasureTheory

namespace GSpinGGP

section SpecialOpp

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
  {V : Type*} [AddCommGroup V] [Module F V] {ι : Type*}

omit [PAdicField F] in
/-- Adaptedness of a special lattice does not see the sign of the weights. -/
theorem SpecialLattice.IsAdapted.neg [FiniteDimensional F V] {Q : QuadraticForm F V}
    {S : SpecialLattice Q} {b : Basis ι F V} {wt : ι → ℤ} (h : S.IsAdapted b wt) :
    S.IsAdapted b (-wt) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i => exists_mem_wtSpan_neg (h1 i), fun i => exists_mem_wtSpan_neg (h2 i), ?_⟩
  rwa [wtSpan_neg]

end SpecialOpp

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] {d : GGPData F}

/-- Good position does not see the sign of the weights. -/
theorem StabilizesSplitLattice.neg {V ι : Type*} [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {b : Basis ι F V} {wt : ι → ℤ} {S : Set (GSpin Q)}
    (h : StabilizesSplitLattice Q b wt S) : StabilizesSplitLattice Q b (-wt) S :=
  h.of_wtSpan_eq fun w => ⟨-w, by rw [wtSpan_neg_wt, neg_neg]⟩

/-- **A good `K` for `L` is good for `L.opp`**: the same subgroup (`𝒫(M)` is the same, and the
weight spaces are the same up to sign). -/
def GoodK.opp {L : d.FlagLeviDatum} (K : d.GoodK L) : d.GoodK L.opp where
  K := K.K
  isOpen := K.isOpen
  isCompact := K.isCompact
  mul_eq P hP := K.mul_eq P (L.opp_M ▸ hP)
  goodPositionW := K.goodPositionW.neg
  goodPositionV := K.goodPositionV.neg

@[simp] theorem GoodK.opp_K {L : d.FlagLeviDatum} (K : d.GoodK L) : K.opp.K = K.K := rfl

/-- **`K` special for `L` is special for `L.opp`.** -/
theorem GoodK.IsSpecial.opp {L : d.FlagLeviDatum} {K : d.GoodK L} (h : K.IsSpecial) :
    K.opp.IsSpecial := by
  obtain ⟨SW, SV, hW, hV, hK⟩ := h
  exact ⟨SW, SV, hW.neg, hV.neg, hK⟩

namespace ReducedLeviDatum

variable (L : d.ReducedLeviDatum)

/-- `GoodK.opp`, typed for the reduced datum `L.opp`. -/
def oppK (K : d.GoodK L.toFlagLeviDatum) : d.GoodK L.opp.toFlagLeviDatum := K.opp

@[simp] theorem oppK_K (K : d.GoodK L.toFlagLeviDatum) : (L.oppK K).K = K.K := rfl

theorem oppK_isSpecial {K : d.GoodK L.toFlagLeviDatum} (h : K.IsSpecial) : (L.oppK K).IsSpecial :=
  h.opp

/-- **`A_M(F)` is the same for `L` and `L.opp`.** -/
theorem opp_AMF : L.opp.AMF = L.AMF :=
  AMF_eq_of_sameWtSpaces L.sameWtSpaces_opp.1 L.sameWtSpaces_opp.2

/-- **`dim a_M^G` is the same for `L` and `L.opp`.** -/
theorem opp_finrank_aMG : finrank ℝ L.opp.aMG = finrank ℝ L.aMG :=
  finrank_aMG_eq_of_sameWtSpaces L.sameWtSpaces_opp.1 L.sameWtSpaces_opp.2

/-- **`v_M` is the same for `L` and `L.opp`** (with the same `K`). -/
theorem opp_vM (K : d.GoodK L.toFlagLeviDatum) (g : ↥d.G) : L.opp.vM (L.oppK K) g = L.vM K g :=
  vM_eq_of_sameWtSpaces L.sameWtSpaces_opp.1 L.sameWtSpaces_opp.2 K (L.oppK K) rfl g

end ReducedLeviDatum

end GGPData

end GSpinGGP
