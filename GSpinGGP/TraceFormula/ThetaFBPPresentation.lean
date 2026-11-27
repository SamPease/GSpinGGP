/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.ThetaFBP
import GSpinGGP.GGP.LeviPresentation

/-!
# `θ_f` depends on the presentation only through the weight spaces

Beuzart-Plessis' `θ_f(x)` (`thetaFBP`, Astérisque 418, §5.2) is built from `M`, `A_M(F)`, `d_c t`
and Arthur's weight `v_M`.  For two reduced Levi data `L`, `L'` with the same `M` and the same
`A_M(F)`, and a linear isomorphism `ψ : a_M^L ≃ a_M^{L'}` carrying `H_M^L` to `H_M^{L'}`, all of
them agree (`thetaFBP_eq_of_equiv`): `d_c t` because the maximal compact subgroup
`A_M(F) ∩ ker H_M` is the same (`kerHMSet_eq`, `dcMeasure_eq_of_equiv`), and `v_M` and the sign
`(−1)^{dim a_M^G}` by `GGP/LeviPresentation.lean`.

Such a `ψ` exists when the families of weight spaces of `L` and `L'` have the same members
(`exists_aMEquiv_of_sameWtSpaces`), so **`θ_f` computed with `(L', K')` equals `θ_f` computed with
`(L, K)` for any good `K`, `K'` with the same underlying subgroup, every `f` and every `x`**
(`thetaFBP_eq_of_sameWtSpaces`).  This covers reindexing and rescaling the bases, the opposite
datum `L.opp` (`opp_thetaFBP`, `TraceFormula/ThetaFBPOpp.lean`, a corollary) and every
relabelling of the weight spaces by a signed permutation of the weights.

**What is not proved here.**  That two reduced data with the same Levi subgroup `M` have the same
weight spaces up to relabelling (the weight spaces are the isotypic components of `A_M`):
`sameWtSpaces_of_M_eq` is a `sorry` with a proof sketch (`GGP/LeviPresentation.lean`), off the path
of the main theorem.  With it, `thetaFBP` depends on `L` only through `L.M`
(`thetaFBP_eq_of_M_eq`).  The independence of `K` (for special `K`) and
the conjugation invariance are not touched: they come from `waldspurger2010_lemme_5_3`
(`Literature/BPThetaF.lean`).

## Main results

* `IsMx.of_AMF_eq`, `dcMeasure_eq_of_equiv` (and `IsMx.of_sameWtSpaces`,
  `dcMeasure_eq_of_sameWtSpaces`): `IsMx` and `d_c t` agree.
* `thetaFBP_eq_of_equiv`: `θ_f` agrees, given `ψ`.
* `thetaFBP_eq_of_sameWtSpaces`: `θ_f` agrees for the same weight spaces up to relabelling;
  `rebase_thetaFBP`: reindexed and rescaled bases.
* `thetaFBP_eq_of_M_eq`: `θ_f` agrees for the same `M` (from the `sorry` `sameWtSpaces_of_M_eq`).
-/

noncomputable section

open MeasureTheory Module

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable {d : GGPData F}

namespace ReducedLeviDatum

variable (L : d.ReducedLeviDatum)

/-- The elements of `M(F)` on which `H_M` vanishes (all of `G(F) \ M(F)` is included, which does
not matter below). -/
def kerHMSet : Set ↥d.G := {g | ∀ h : g ∈ L.M, L.HM ⟨g, h⟩ = 0}

/-- `A_M(F) ∩ T ∩ ker H_M` as a preimage of `kerHMSet`. -/
theorem coe_AGxOneOn (T : Subgroup ↥d.G) :
    (L.AGxOneOn T : Set ↥(L.AGxOn T)) =
      (fun a : ↥(L.AGxOn T) => ((a : ↥T) : ↥d.G)) ⁻¹' L.kerHMSet := by
  ext a
  change a ∈ L.AGxOneOn T ↔ ∀ h, _
  rw [AGxOneOn, MonoidHom.mem_ker]
  exact ⟨fun h _ => h, fun h => h _⟩

/-- `IsDcMeasureOn` with `A_M(F) ∩ T ∩ ker H_M` written as a preimage of `kerHMSet`. -/
theorem isDcMeasureOn_iff_kerHMSet (T : Subgroup ↥d.G) (μ : Measure ↥T) :
    L.IsDcMeasureOn T μ ↔ μ.IsHaarMeasure ∧ ∃ (μA : Measure ↥(L.AGxOn T))
      (m : Measure (CosetSpace (L.AGxOn T).subtype)), μA.IsHaarMeasure ∧
        μA ((fun a : ↥(L.AGxOn T) => ((a : ↥T) : ↥d.G)) ⁻¹' L.kerHMSet) = 1 ∧
        IsWeilMeasure (L.AGxOn T).subtype μ μA m ∧ m Set.univ = 1 := by
  unfold IsDcMeasureOn
  rw [coe_AGxOneOn]

variable {L} {L' : d.ReducedLeviDatum}

theorem AGxOn_eq_of_AMF_eq (hA : L'.AMF = L.AMF) (T : Subgroup ↥d.G) :
    L'.AGxOn T = L.AGxOn T := by
  unfold AGxOn; rw [hA]

theorem kerHMSet_eq (ψ : L.aM ≃ₗ[ℝ] L'.aM) (hM : L'.M = L.M)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m)) :
    L'.kerHMSet = L.kerHMSet := by
  ext g
  constructor
  · intro h hm
    have := h (hM.ge hm)
    rw [hψ ⟨g, hm⟩ ⟨g, hM.ge hm⟩ rfl] at this
    exact ψ.map_eq_zero_iff.1 this
  · intro h hm'
    rw [hψ ⟨g, hM.le hm'⟩ ⟨g, hm'⟩ rfl, h (hM.le hm'), map_zero]

theorem isDcMeasureOn_eq_of_equiv (ψ : L.aM ≃ₗ[ℝ] L'.aM) (hM : L'.M = L.M)
    (hA : L'.AMF = L.AMF)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m))
    (T : Subgroup ↥d.G) : L'.IsDcMeasureOn T = L.IsDcMeasureOn T := by
  funext μ
  apply propext
  rw [isDcMeasureOn_iff_kerHMSet, isDcMeasureOn_iff_kerHMSet, AGxOn_eq_of_AMF_eq hA,
    kerHMSet_eq ψ hM hψ]

/-- **`IsMx` agrees** for data with the same `M` and `A_M(F)`. -/
theorem IsMx.of_AMF_eq (hM : L'.M = L.M) (hA : L'.AMF = L.AMF) {x : ↥d.G} (h : L.IsMx x) :
    L'.IsMx x where
  regular := h.regular
  mem := hM.ge h.mem
  compact := by
    rw [show L'.AGx x = L.AGx x from AGxOn_eq_of_AMF_eq hA _]
    exact h.compact

/-- **`d_c t` agrees** for `L` and `L'`. -/
theorem dcMeasure_eq_of_equiv (ψ : L.aM ≃ₗ[ℝ] L'.aM) (hM : L'.M = L.M) (hA : L'.AMF = L.AMF)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m)) (x : ↥d.G) :
    L'.dcMeasure x = L.dcMeasure x := by
  unfold ReducedLeviDatum.dcMeasure ReducedLeviDatum.dcMeasureOn
  rw [isDcMeasureOn_eq_of_equiv ψ hM hA hψ]

/-- **`θ_f` is carried by an isomorphism of `a_M` compatible with `H_M`**: for `L`, `L'` with the
same `M` and `A_M(F)`, `ψ : a_M^L ≃ a_M^{L'}` with `ψ ∘ H_M^L = H_M^{L'}`, and good subgroups with
the same underlying `K`, `θ_f` is the same for every `f` and `x`. -/
theorem thetaFBP_eq_of_equiv (ψ : L.aM ≃ₗ[ℝ] L'.aM) (hM : L'.M = L.M) (hA : L'.AMF = L.AMF)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m))
    (K : d.GoodK L.toFlagLeviDatum) (K' : d.GoodK L'.toFlagLeviDatum) (hK : K'.K = K.K)
    (f : ↥d.G → ℂ) (x : ↥d.G) : L'.thetaFBP K' f x = L.thetaFBP K f x := by
  simp only [ReducedLeviDatum.thetaFBP, weightedOrbitalIntegral, weightedIntegrand,
    finrank_aMG_eq ψ hM hψ, dcMeasure_eq_of_equiv ψ hM hA hψ, vM_eq_of_equiv ψ hM hA hψ K K' hK]

/-- **`IsMx` agrees** for the same weight spaces up to relabelling. -/
theorem IsMx.of_sameWtSpaces (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L') {x : ↥d.G}
    (h : L.IsMx x) : L'.IsMx x :=
  h.of_AMF_eq (M_eq_of_sameWtSpaces hW hV) (AMF_eq_of_sameWtSpaces hW hV)

/-- **`d_c t` agrees** for the same weight spaces up to relabelling. -/
theorem dcMeasure_eq_of_sameWtSpaces (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L')
    (x : ↥d.G) : L'.dcMeasure x = L.dcMeasure x := by
  obtain ⟨ψ, hψ⟩ := exists_aMEquiv_of_sameWtSpaces hW hV
  exact dcMeasure_eq_of_equiv ψ (M_eq_of_sameWtSpaces hW hV) (AMF_eq_of_sameWtSpaces hW hV) hψ x

/-- **`θ_f` depends on the presentation only through the weight spaces**: for reduced data `L`,
`L'` whose families of weight spaces have the same members (for `W` and for `V`; e.g. reindexed or
rescaled bases, `L.opp`, or weight spaces relabelled by a signed permutation of the weights) and
good subgroups `K`, `K'` with the same underlying subgroup, `θ_f` computed with `(L', K')` equals
`θ_f` computed with `(L, K)`, for every `f` and `x`. -/
theorem thetaFBP_eq_of_sameWtSpaces (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L')
    (K : d.GoodK L.toFlagLeviDatum) (K' : d.GoodK L'.toFlagLeviDatum) (hK : K'.K = K.K)
    (f : ↥d.G → ℂ) (x : ↥d.G) : L'.thetaFBP K' f x = L.thetaFBP K f x := by
  obtain ⟨ψ, hψ⟩ := exists_aMEquiv_of_sameWtSpaces hW hV
  exact thetaFBP_eq_of_equiv ψ (M_eq_of_sameWtSpaces hW hV) (AMF_eq_of_sameWtSpaces hW hV) hψ
    K K' hK f x

/-- **The rebased datum** (reindexed, rescaled bases; `rebase`) gives the same `θ_f`, with the same
`K`. -/
theorem rebase_thetaFBP {κW κV : Type} [Fintype κW] [Fintype κV] (eW : L.ιW ≃ κW)
    (uW : κW → Fˣ) (eV : L.ιV ≃ κV) (uV : κV → Fˣ) (K : d.GoodK L.toFlagLeviDatum)
    (f : ↥d.G → ℂ) (x : ↥d.G) :
    (L.rebase eW uW eV uV).thetaFBP (goodKOfSameWtSpaces (L.sameWtSpaces_rebase eW uW eV uV).1
      (L.sameWtSpaces_rebase eW uW eV uV).2 K) f x = L.thetaFBP K f x :=
  thetaFBP_eq_of_sameWtSpaces (L.sameWtSpaces_rebase eW uW eV uV).1
    (L.sameWtSpaces_rebase eW uW eV uV).2 K _ rfl f x

/-- **`θ_f` depends on the presentation `L` only through `L.M`**, for good subgroups with the same
underlying `K`.  Proved from `sameWtSpaces_of_M_eq` (the weight spaces are intrinsic to `M`), which
is a `sorry`; everything else is proved (`thetaFBP_eq_of_sameWtSpaces`).  Not on the path of the
main theorem. -/
theorem thetaFBP_eq_of_M_eq (hM : L'.M = L.M) (K : d.GoodK L.toFlagLeviDatum)
    (K' : d.GoodK L'.toFlagLeviDatum) (hK : K'.K = K.K) (f : ↥d.G → ℂ) (x : ↥d.G) :
    L'.thetaFBP K' f x = L.thetaFBP K f x :=
  thetaFBP_eq_of_sameWtSpaces (sameWtSpaces_of_M_eq hM).1 (sameWtSpaces_of_M_eq hM).2 K K' hK f x

end ReducedLeviDatum

end GGPData

end GSpinGGP
