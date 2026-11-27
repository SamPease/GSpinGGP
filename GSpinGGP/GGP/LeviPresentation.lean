/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.WeightVM
import GSpinGGP.GGP.WtSpan

/-!
# Arthur's weight `v_M` depends on the presentation only through the weight spaces

A reduced Levi datum `L` presents its Levi subgroup `M` by bases with weights `(b_W, wt_W)`,
`(b_V, wt_V)`; `a_M` is written in the coordinates of the characters `char L c` (determinants on
the weight spaces of weights `1, …, len`, and the `GSpin`-norms).  This file shows that `v_M`
does not see the presentation beyond the family of weight spaces, up to relabelling the weights.

**Transport along a linear isomorphism of `a_M`.**  If `L.M = L'.M`, `A_M(F)` is the same and a
linear isomorphism `ψ : a_M^L ≃ a_M^{L'}` carries `H_M^L` to `H_M^{L'}` (exactly, not modulo
`a_G`), then `ψ` carries `a_G` (`aG_eq_map`), the lattice `proj_M^G(H_M(A_M(F)))`
(`latticeMG_eq_map`) and the points `H_P(g)` (`mkQ_hPar_eq`) of `L` to those of `L'`, so
`v_M` is the same for any two `IwasawaK` with the same underlying `K` (`vM_eq_of_equiv`).
The inverse of `ψ` need not be given: linear maps both ways compatible with `H_M` are inverse to
each other because `H_M(A_M(F))` spans `a_M` (`aMEquivOfHM`).

**Same weight spaces up to relabelling** (`SameWtSpacesW`, `SameWtSpacesV`).  If the families
`w ↦ wtSpan b wt w` of `L` and `L'` have the same members (`Set.range`), for `W` and for `V` (this
covers reindexing and rescaling the bases, `L ↦ L.opp`, and permuting the weight spaces with
independent signs), then:
* the weight projections agree up to relabelling (`wtProj_eq_of_wtSpan_eq`), so `L.M = L'.M`
  (`M_eq_of_sameWtSpaces`);
* the weight-`0` spaces agree (`wtSpan_zero_eq_of_wtSpan_eq`: the other weight spaces are totally
  isotropic, a nonzero weight-`0` space is not), so `A_M(F)` agrees (`AMF_eq_of_sameWtSpaces`);
* every coordinate of `H_M^{L'}` is `0`, or `±` a coordinate of `H_M^{L}`
  (`exists_HM_coord_eq`; the sign `−` by determinant duality `det_wtBlock_neg_mul`), which gives
  the isomorphism `ψ` (`exists_aMEquiv_of_sameWtSpaces`);
* hence `v_M^{L'} = v_M^{L}` (`vM_eq_of_sameWtSpaces`).

A good `K` for `L` is good for `L'` (`goodKOfSameWtSpaces`).  Examples: `rebase` (reindexed and
rescaled bases, `sameWtSpaces_rebase`) and `L.opp` (`sameWtSpaces_opp`).

**Not proved here** (`sameWtSpaces_of_M_eq`, a `sorry` with a proof sketch, off the path of the
main theorem): two reduced data with the same Levi subgroup have the same weight spaces up to
relabelling.
-/

noncomputable section

open Module MeasureTheory

namespace GSpinGGP

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] {d : GGPData F}

/-- The projection `P → M` does not depend on how `M` is written. -/
theorem IsLevi.coe_proj_congr {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV}
    {M M' : Subgroup ↥d.G} (h : M = M') (hL : d.IsLevi FW FV M) (hL' : d.IsLevi FW FV M')
    (p : ↥(d.whittB FW FV)) : ((hL.proj p : ↥M) : ↥d.G) = ((hL'.proj p : ↥M') : ↥d.G) := by
  subst h; rfl

namespace ReducedLeviDatum

/-! ## 2. Transport of `v_M` along an isomorphism of `a_M` -/

variable {L L' : d.ReducedLeviDatum}

/-- **Linear maps both ways compatible with `H_M` are inverse isomorphisms**: `H_M(A_M(F))` spans
`a_M` (`span_HMAMF_eq_top`). -/
def aMEquivOfHM (hM : L'.M = L.M) (Φ : L.aM →ₗ[ℝ] L'.aM)
    (Ψ : L'.aM →ₗ[ℝ] L.aM)
    (hΦ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = Φ (L.HM m))
    (hΨ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L.HM m = Ψ (L'.HM m')) :
    L.aM ≃ₗ[ℝ] L'.aM :=
  LinearEquiv.ofLinearMap Φ Ψ
    (LinearMap.ext_on L'.span_HMAMF_eq_top (by
      rintro _ ⟨⟨m', hm'⟩, rfl⟩
      let m : ↥L.M := ⟨m', hM.le m'.2⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [← hΨ m m' rfl, ← hΦ m m' rfl]))
    (LinearMap.ext_on L.span_HMAMF_eq_top (by
      rintro _ ⟨⟨m, hm⟩, rfl⟩
      let m' : ↥L'.M := ⟨m, hM.ge m.2⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [← hΦ m m' rfl, ← hΨ m m' rfl]))

@[simp] theorem aMEquivOfHM_apply (hM : L'.M = L.M)
    (Φ : L.aM →ₗ[ℝ] L'.aM) (Ψ : L'.aM →ₗ[ℝ] L.aM) (hΦ hΨ) (H : L.aM) :
    aMEquivOfHM hM Φ Ψ hΦ hΨ H = Φ H := rfl

variable (ψ : L.aM ≃ₗ[ℝ] L'.aM)

/-- **`a_G` is carried by `ψ`** (it is spanned by `H_M(A_G(F))`). -/
theorem aG_eq_map (hM : L'.M = L.M)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m)) :
    L'.aG = L.aG.map (ψ : L.aM →ₗ[ℝ] L'.aM) := by
  rw [ReducedLeviDatum.aG, ReducedLeviDatum.aG, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨⟨m', hm'⟩, rfl⟩
    exact ⟨_, ⟨⟨⟨m', hM.le m'.2⟩, hm'⟩, rfl⟩, (hψ _ m' rfl).symm⟩
  · rintro ⟨_, ⟨⟨m, hm⟩, rfl⟩, rfl⟩
    exact ⟨⟨⟨m, hM.ge m.2⟩, hm⟩, hψ m _ rfl⟩

/-- `ψ` on `a_M^G = a_M / a_G`. -/
def aMGEquiv (hM : L'.M = L.M)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m)) :
    L.aMG ≃L[ℝ] L'.aMG :=
  (Submodule.Quotient.equiv L.aG L'.aG ψ (aG_eq_map ψ hM hψ).symm).toContinuousLinearEquiv

theorem aMGEquiv_mkQ (hM : L'.M = L.M)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m)) (H : L.aM) :
    aMGEquiv ψ hM hψ (L.aG.mkQ H) = L'.aG.mkQ (ψ H) := rfl

theorem finrank_aMG_eq (hM : L'.M = L.M)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m)) :
    finrank ℝ L'.aMG = finrank ℝ L.aMG :=
  (aMGEquiv ψ hM hψ).toLinearEquiv.finrank_eq.symm

theorem mkQ_HM_eq (hM : L'.M = L.M)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m))
    (m : ↥L.M) (m' : ↥L'.M) (hmm : (m' : ↥d.G) = m) :
    L'.aG.mkQ (L'.HM m') = aMGEquiv ψ hM hψ (L.aG.mkQ (L.HM m)) := by
  rw [aMGEquiv_mkQ, hψ m m' hmm]

/-- **The lattice `proj_M^G(H_M(A_M(F)))` is carried by `ψ`.** -/
theorem latticeMG_eq_map (hM : L'.M = L.M) (hA : L'.AMF = L.AMF)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m)) :
    L'.latticeMG = L.latticeMG.map (aMGEquiv ψ hM hψ : L.aMG →+ L'.aMG) := by
  rw [ReducedLeviDatum.latticeMG, ReducedLeviDatum.latticeMG, AddMonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨⟨m', hm'⟩, rfl⟩
    exact ⟨_, ⟨⟨⟨m', hM.le m'.2⟩, hA ▸ hm'⟩, rfl⟩,
      (mkQ_HM_eq ψ hM hψ ⟨m', hM.le m'.2⟩ m' rfl).symm⟩
  · rintro ⟨_, ⟨⟨m, hm⟩, rfl⟩, rfl⟩
    exact ⟨⟨⟨m, hM.ge m.2⟩, hA.symm ▸ hm⟩, mkQ_HM_eq ψ hM hψ m ⟨m, hM.ge m.2⟩ rfl⟩

/-- **The points `H_P(g)` are carried by `ψ`**, for subgroups `K`, `K'` of `L`, `L'` with the
same underlying subgroup and the same parabolic `P ∈ 𝒫(M)`. -/
theorem mkQ_hPar_eq (hM : L'.M = L.M)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m))
    (K : d.IwasawaK L.toFlagLeviDatum) (K' : d.IwasawaK L'.toFlagLeviDatum) (hK : K'.K = K.K)
    {P : Subgroup ↥d.G} (hP' : P ∈ d.parabolics L'.M) (hP : P ∈ d.parabolics L.M) (g : ↥d.G) :
    L'.aG.mkQ (L'.hPar K' ⟨P, hP'⟩ g) = aMGEquiv ψ hM hψ (L.aG.mkQ (L.hPar K ⟨P, hP⟩ g)) := by
  obtain ⟨FW, FV, hPeq, hL'⟩ := id hP'
  have hL : d.IsLevi FW FV L.M := hM ▸ hL'
  obtain ⟨p, hp, k, hk, rfl⟩ := K.mul_eq P hP g
  have hp' : p ∈ d.whittB FW FV := hPeq ▸ hp
  have hk' : k ∈ K'.K := hK ▸ hk
  rw [L'.hPar_eq K' ⟨P, hP'⟩ hPeq hL', L.hPar_eq K ⟨P, hP⟩ hPeq hL]
  have e3 := L'.hP_eq hL' K'.isCompact (hPeq ▸ K'.mul_eq P hP') ⟨p, hp'⟩ hk'
  have e4 := L.hP_eq hL K.isCompact (hPeq ▸ K.mul_eq P hP) ⟨p, hp'⟩ hk
  rw [e3, e4]
  exact mkQ_HM_eq ψ hM hψ _ _ (IsLevi.coe_proj_congr hM hL' hL _)

/-- **`v_M` is carried by `ψ`**: `v_M^{L'}(g) = v_M^{L}(g)` for subgroups with the same
underlying `K` (the hull and the lattice are carried by the linear isomorphism `aMGEquiv ψ`,
`Measure.hullVolume_map`). -/
theorem vM_eq_of_equiv (hM : L'.M = L.M) (hA : L'.AMF = L.AMF)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m))
    (K : d.IwasawaK L.toFlagLeviDatum) (K' : d.IwasawaK L'.toFlagLeviDatum) (hK : K'.K = K.K)
    (g : ↥d.G) : L'.vM K' g = L.vM K g := by
  have hS :
      (Set.range fun P : ↥(d.parabolics L'.M) => L'.aG.mkQ (L'.hPar K' P g)) =
      aMGEquiv ψ hM hψ '' Set.range fun P : ↥(d.parabolics L.M) => L.aG.mkQ (L.hPar K P g) := by
    ext v
    constructor
    · rintro ⟨⟨P, hP'⟩, rfl⟩
      have hP : P ∈ d.parabolics L.M := hM ▸ hP'
      exact ⟨_, ⟨⟨P, hP⟩, rfl⟩, (mkQ_hPar_eq ψ hM hψ K K' hK hP' hP g).symm⟩
    · rintro ⟨_, ⟨⟨P, hP⟩, rfl⟩, rfl⟩
      have hP' : P ∈ d.parabolics L'.M := hM.symm ▸ hP
      exact ⟨⟨P, hP'⟩, mkQ_hPar_eq ψ hM hψ K K' hK hP' hP g⟩
  obtain ⟨D, hD, -⟩ := L'.exists_isAddFundamentalDomain_latticeHaar_eq_one
  have hcount : Countable ↥(L'.latticeMG.toIntSubmodule) := by
    obtain ⟨h1, h2⟩ := L'.latticeMG_isLattice
    have : IsZLattice ℝ L'.latticeMG.toIntSubmodule := ⟨h2⟩
    infer_instance
  simp only [ReducedLeviDatum.vM]
  rw [hS]
  have : Countable ↥(L.latticeMG.map (aMGEquiv ψ hM hψ : L.aMG →+ L'.aMG)) := by
    rw [← latticeMG_eq_map ψ hM hA hψ]; exact hcount
  rw [latticeMG_eq_map ψ hM hA hψ] at hD
  rw [latticeMG_eq_map ψ hM hA hψ]
  exact Measure.hullVolume_map (aMGEquiv ψ hM hψ) hD _

/-! ## 3. Same weight spaces up to relabelling -/

variable (L L')

/-- The family of weight spaces of `W` of `L'` has the same members as that of `L`. -/
def SameWtSpacesW : Prop :=
  Set.range (wtSpan L'.bW L'.wtW) = Set.range (wtSpan L.bW L.wtW)

/-- The family of weight spaces of `V` of `L'` has the same members as that of `L`. -/
def SameWtSpacesV : Prop :=
  Set.range (wtSpan L'.bV L'.wtV) = Set.range (wtSpan L.bV L.wtV)

variable {L L'}

theorem SameWtSpacesW.exists (h : SameWtSpacesW L L') (u' : ℤ) :
    ∃ u, wtSpan L'.bW L'.wtW u' = wtSpan L.bW L.wtW u := by
  obtain ⟨u, hu⟩ : wtSpan L'.bW L'.wtW u' ∈ Set.range (wtSpan L.bW L.wtW) := h ▸ ⟨u', rfl⟩
  exact ⟨u, hu.symm⟩

theorem SameWtSpacesW.exists' (h : SameWtSpacesW L L') (u : ℤ) :
    ∃ u', wtSpan L.bW L.wtW u = wtSpan L'.bW L'.wtW u' := by
  obtain ⟨u', hu'⟩ : wtSpan L.bW L.wtW u ∈ Set.range (wtSpan L'.bW L'.wtW) := h.symm ▸ ⟨u, rfl⟩
  exact ⟨u', hu'.symm⟩

theorem SameWtSpacesV.exists (h : SameWtSpacesV L L') (u' : ℤ) :
    ∃ u, wtSpan L'.bV L'.wtV u' = wtSpan L.bV L.wtV u := by
  obtain ⟨u, hu⟩ : wtSpan L'.bV L'.wtV u' ∈ Set.range (wtSpan L.bV L.wtV) := h ▸ ⟨u', rfl⟩
  exact ⟨u, hu.symm⟩

theorem SameWtSpacesV.exists' (h : SameWtSpacesV L L') (u : ℤ) :
    ∃ u', wtSpan L.bV L.wtV u = wtSpan L'.bV L'.wtV u' := by
  obtain ⟨u', hu'⟩ : wtSpan L.bV L.wtV u ∈ Set.range (wtSpan L'.bV L'.wtV) := h.symm ▸ ⟨u, rfl⟩
  exact ⟨u', hu'.symm⟩

theorem SameWtSpacesW.symm (h : SameWtSpacesW L L') : SameWtSpacesW L' L := Eq.symm h

theorem SameWtSpacesV.symm (h : SameWtSpacesV L L') : SameWtSpacesV L' L := Eq.symm h

/-- **The Levi subgroup is the same.** -/
theorem M_eq_of_sameWtSpaces (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L') :
    L'.M = L.M := by
  change d.flagLeviG L'.bW L'.wtW L'.bV L'.wtV = d.flagLeviG L.bW L.wtW L.bV L.wtV
  unfold GGPData.flagLeviG
  rw [flagLevi_eq_of_wtSpan_eq hW.exists' hW.exists, flagLevi_eq_of_wtSpan_eq hV.exists' hV.exists]

theorem wtSpanW_zero_eq (hW : SameWtSpacesW L L') :
    wtSpan L'.bW L'.wtW 0 = wtSpan L.bW L.wtW 0 :=
  wtSpan_zero_eq_of_wtSpan_eq d.nondeg L.hsW.orth L'.hsW.orth hW.exists' hW.exists

theorem wtSpanV_zero_eq (hV : SameWtSpacesV L L') :
    wtSpan L'.bV L'.wtV 0 = wtSpan L.bV L.wtV 0 :=
  wtSpan_zero_eq_of_wtSpan_eq d.nondeg_QV L.hsV.orth L'.hsV.orth hV.exists' hV.exists

/-- **`A_M(F)` is the same.** -/
theorem AMF_eq_of_sameWtSpaces (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L') :
    L'.AMF = L.AMF := by
  have eW : wtScalar d.QW L'.bW L'.wtW = wtScalar d.QW L.bW L.wtW :=
    le_antisymm (wtScalar_le_of_wtSpan_eq hW.exists' (wtSpanW_zero_eq hW).symm)
      (wtScalar_le_of_wtSpan_eq hW.exists (wtSpanW_zero_eq hW))
  have eV : wtScalar d.QV L'.bV L'.wtV = wtScalar d.QV L.bV L.wtV :=
    le_antisymm (wtScalar_le_of_wtSpan_eq hV.exists' (wtSpanV_zero_eq hV).symm)
      (wtScalar_le_of_wtSpan_eq hV.exists (wtSpanV_zero_eq hV))
  ext g
  rw [L'.mem_AMF_iff, L.mem_AMF_iff, eW, eV]

/-- **Each coordinate of `H_M^{L'}` is a real multiple of one coordinate of `H_M^{L}`**, uniformly
in `m`, when the weight spaces are the same up to relabelling.  (The proof gives the multiplier
`0` or `±1`; the statement only records some real `s`.) -/
theorem exists_HM_coord_eq (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L') (c' : L'.Coord) :
    ∃ (s : ℝ) (c : L.Coord), ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m →
      L'.HM m' c' = s * L.HM m c := by
  rcases c' with (i' | _) | (i' | _)
  · obtain ⟨w, hw⟩ := hW.exists ((i' : ℤ) + 1)
    have hw0 : w = 0 → ∀ j, L.wtW j ≠ 0 := by
      rintro rfl j hj
      have h1 : L.bW j ∈ wtSpan L'.bW L'.wtW ((i' : ℤ) + 1) := by
        rw [hw, ← hj]; exact basis_mem_wtSpan j
      have h2 : L.bW j ∈ wtSpan L'.bW L'.wtW 0 := by
        rw [wtSpanW_zero_eq hW, ← hj]; exact basis_mem_wtSpan j
      exact L.bW.ne_zero j (Submodule.disjoint_def.1 (disjoint_wtSpan (by omega)) _ h1 h2)
    rcases L.hsW.log_det_wtBlock_cases d.nondeg w hw0 with h0 | ⟨s, i, h⟩
    · refine ⟨0, Sum.inl (Sum.inr ()), fun m m' hmm => ?_⟩
      change Real.log ‖LinearMap.det (wtBlock L'.bW L'.wtW ((i' : ℤ) + 1)
        (specP d.QW (d.fst (m' : ↥d.G)) : _ →ₗ[F] _))‖ = _
      rw [wtBlock_eq_of_wtSpan_eq hW.exists' hw, hmm, h0 _ m.2.1, zero_mul]
    · refine ⟨s, Sum.inl (Sum.inl i), fun m m' hmm => ?_⟩
      change Real.log ‖LinearMap.det (wtBlock L'.bW L'.wtW ((i' : ℤ) + 1)
        (specP d.QW (d.fst (m' : ↥d.G)) : _ →ₗ[F] _))‖ = s * Real.log ‖LinearMap.det
          (wtBlock L.bW L.wtW ((i : ℤ) + 1) (specP d.QW (d.fst (m : ↥d.G)) : _ →ₗ[F] _))‖
      rw [wtBlock_eq_of_wtSpan_eq hW.exists' hw, hmm, h _ m.2.1]
  · refine ⟨1, Sum.inl (Sum.inr ()), fun m m' hmm => ?_⟩
    change Real.log ‖((detChar d.QW (d.fst (m' : ↥d.G)) : Fˣ) : F)‖ =
      1 * Real.log ‖((detChar d.QW (d.fst (m : ↥d.G)) : Fˣ) : F)‖
    rw [hmm, one_mul]
  · obtain ⟨w, hw⟩ := hV.exists ((i' : ℤ) + 1)
    have hw0 : w = 0 → ∀ j, L.wtV j ≠ 0 := by
      rintro rfl j hj
      have h1 : L.bV j ∈ wtSpan L'.bV L'.wtV ((i' : ℤ) + 1) := by
        rw [hw, ← hj]; exact basis_mem_wtSpan j
      have h2 : L.bV j ∈ wtSpan L'.bV L'.wtV 0 := by
        rw [wtSpanV_zero_eq hV, ← hj]; exact basis_mem_wtSpan j
      exact L.bV.ne_zero j (Submodule.disjoint_def.1 (disjoint_wtSpan (by omega)) _ h1 h2)
    rcases L.hsV.log_det_wtBlock_cases d.nondeg_QV w hw0 with h0 | ⟨s, i, h⟩
    · refine ⟨0, Sum.inl (Sum.inr ()), fun m m' hmm => ?_⟩
      change Real.log ‖LinearMap.det (wtBlock L'.bV L'.wtV ((i' : ℤ) + 1)
        (specP d.QV (d.snd (m' : ↥d.G)) : _ →ₗ[F] _))‖ = _
      rw [wtBlock_eq_of_wtSpan_eq hV.exists' hw, hmm, h0 _ m.2.2, zero_mul]
    · refine ⟨s, Sum.inr (Sum.inl i), fun m m' hmm => ?_⟩
      change Real.log ‖LinearMap.det (wtBlock L'.bV L'.wtV ((i' : ℤ) + 1)
        (specP d.QV (d.snd (m' : ↥d.G)) : _ →ₗ[F] _))‖ = s * Real.log ‖LinearMap.det
          (wtBlock L.bV L.wtV ((i : ℤ) + 1) (specP d.QV (d.snd (m : ↥d.G)) : _ →ₗ[F] _))‖
      rw [wtBlock_eq_of_wtSpan_eq hV.exists' hw, hmm, h _ m.2.2]
  · refine ⟨1, Sum.inr (Sum.inr ()), fun m m' hmm => ?_⟩
    change Real.log ‖((detChar d.QV (d.snd (m' : ↥d.G)) : Fˣ) : F)‖ =
      1 * Real.log ‖((detChar d.QV (d.snd (m : ↥d.G)) : Fˣ) : F)‖
    rw [hmm, one_mul]

/-- A linear map `a_M^L → a_M^{L'}` carrying `H_M^L` to `H_M^{L'}`, for the same weight spaces up to
relabelling (`exists_HM_coord_eq`). -/
theorem exists_linearMap_HM (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L') :
    ∃ Φ : L.aM →ₗ[ℝ] L'.aM, ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m →
      L'.HM m' = Φ (L.HM m) := by
  choose s c hsc using exists_HM_coord_eq hW hV
  refine ⟨LinearMap.pi fun c' => s c' • LinearMap.proj (c c'), fun m m' hmm => ?_⟩
  funext c'
  rw [hsc c' m m' hmm]
  simp [smul_eq_mul]

/-- **The isomorphism `a_M^L ≃ a_M^{L'}` carrying `H_M`**, for the same weight spaces up to
relabelling. -/
theorem exists_aMEquiv_of_sameWtSpaces (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L') :
    ∃ ψ : L.aM ≃ₗ[ℝ] L'.aM, ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m →
      L'.HM m' = ψ (L.HM m) := by
  have hM := M_eq_of_sameWtSpaces hW hV
  obtain ⟨Φ, hΦ⟩ := exists_linearMap_HM hW hV
  obtain ⟨Ψ, hΨ⟩ := exists_linearMap_HM hW.symm hV.symm
  exact ⟨aMEquivOfHM hM Φ Ψ hΦ (fun m m' hmm => hΨ m' m hmm.symm), fun m m' hmm => hΦ m m' hmm⟩

/-- **`v_M` depends on the presentation only through the weight spaces**: for reduced data `L`,
`L'` whose families of weight spaces have the same members (for `W` and for `V`), and
subgroups `K`, `K'` with the same underlying subgroup, `v_M^{L'}(g) = v_M^{L}(g)`. -/
theorem vM_eq_of_sameWtSpaces (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L')
    (K : d.IwasawaK L.toFlagLeviDatum) (K' : d.IwasawaK L'.toFlagLeviDatum) (hK : K'.K = K.K)
    (g : ↥d.G) : L'.vM K' g = L.vM K g := by
  obtain ⟨ψ, hψ⟩ := exists_aMEquiv_of_sameWtSpaces hW hV
  exact vM_eq_of_equiv ψ (M_eq_of_sameWtSpaces hW hV) (AMF_eq_of_sameWtSpaces hW hV) hψ K K' hK g

/-- **`dim a_M^G` is the same** for the same weight spaces up to relabelling. -/
theorem finrank_aMG_eq_of_sameWtSpaces (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L') :
    finrank ℝ L'.aMG = finrank ℝ L.aMG := by
  obtain ⟨ψ, hψ⟩ := exists_aMEquiv_of_sameWtSpaces hW hV
  exact finrank_aMG_eq ψ (M_eq_of_sameWtSpaces hW hV) hψ

/-! ## 4. Good subgroups, rebased data, the opposite datum -/

/-- **A good `K` for `L` is good for `L'`** with the same weight spaces up to relabelling (same
subgroup `K`). -/
def goodKOfSameWtSpaces (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L')
    (K : d.GoodK L.toFlagLeviDatum) : d.GoodK L'.toFlagLeviDatum where
  K := K.K
  isOpen := K.isOpen
  isCompact := K.isCompact
  mul_eq P hP := K.mul_eq P (M_eq_of_sameWtSpaces hW hV ▸ hP)
  goodPositionW := K.goodPositionW.of_wtSpan_eq hW.exists'
  goodPositionV := K.goodPositionV.of_wtSpan_eq hV.exists'

@[simp] theorem goodKOfSameWtSpaces_K (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L')
    (K : d.GoodK L.toFlagLeviDatum) : (goodKOfSameWtSpaces hW hV K).K = K.K := rfl

variable (L) in
/-- **The rebased datum**: the same flags, with the splitting bases reindexed by `eW`, `eV` and
rescaled by the units `uW`, `uV` (`IsFlagSplitting.reindexUnits`); the weights are carried along. -/
def rebase {κW κV : Type} [Fintype κW] [Fintype κV] (eW : L.ιW ≃ κW) (uW : κW → Fˣ)
    (eV : L.ιV ≃ κV) (uV : κV → Fˣ) : d.ReducedLeviDatum where
  FW := L.FW
  FV := L.FV
  ιW := κW
  ιV := κV
  bW := (L.bW.reindex eW).unitsSMul uW
  wtW := L.wtW ∘ eW.symm
  bV := (L.bV.reindex eV).unitsSMul uV
  wtV := L.wtV ∘ eV.symm
  hsW := L.hsW.reindexUnits eW uW
  hsV := L.hsV.reindexUnits eV uV
  reducedW := by rw [wtSpan_reindexUnits]; exact L.reducedW
  reducedV := by rw [wtSpan_reindexUnits]; exact L.reducedV

variable (L) in
theorem sameWtSpaces_rebase {κW κV : Type} [Fintype κW] [Fintype κV] (eW : L.ιW ≃ κW)
    (uW : κW → Fˣ) (eV : L.ιV ≃ κV) (uV : κV → Fˣ) :
    SameWtSpacesW L (L.rebase eW uW eV uV) ∧ SameWtSpacesV L (L.rebase eW uW eV uV) :=
  ⟨congrArg Set.range (funext fun w => wtSpan_reindexUnits (b := L.bW) eW uW w),
    congrArg Set.range (funext fun w => wtSpan_reindexUnits (b := L.bV) eV uV w)⟩

variable (L) in
/-- `L.opp` has the same weight spaces as `L`, relabelled by `w ↦ −w` (`wtSpan_neg_wt`). -/
theorem sameWtSpaces_opp : SameWtSpacesW L L.opp ∧ SameWtSpacesV L L.opp := by
  refine ⟨?_, ?_⟩
  · change Set.range (wtSpan L.bW (-L.wtW)) = Set.range (wtSpan L.bW L.wtW)
    rw [show wtSpan L.bW (-L.wtW) = wtSpan L.bW L.wtW ∘ Neg.neg from
      funext fun w => wtSpan_neg_wt w]
    exact neg_surjective.range_comp _
  · change Set.range (wtSpan L.bV (-L.wtV)) = Set.range (wtSpan L.bV L.wtV)
    rw [show wtSpan L.bV (-L.wtV) = wtSpan L.bV L.wtV ∘ Neg.neg from
      funext fun w => wtSpan_neg_wt w]
    exact neg_surjective.range_comp _

/-- **The weight spaces are intrinsic to `M`** (`sorry`): two reduced data with the same Levi
subgroup have the same weight spaces up to relabelling.  Not on the path of the main theorem.
Sketch (`G = GSpin(W) × GSpin(V)`, so `M` determines `flagLevi` of each factor; argue for `V`):
1. *Compatibility.*  For `w ≥ 1` the lift `T` of the one-weight cocharacter
   (`IsFlagSplitting.exists_oneWt_lift`, `‖τ‖ < 1`) lies in `M = M'`, so `P(T)` commutes with every
   `wtProj` of `L'`; `P(T)` is diagonal in `b` with eigenvalues `τ` on `V_w`, `τ⁻¹` on `V_{−w}`, `1`
   elsewhere, and `τ ≠ τ⁻¹`, `τ ≠ 1`.  So each `wtProj' u'` preserves the `τ^{±1}`-eigenspaces
   `V_{±w}` and the common `1`-eigenspace `V_0`: every `V_u = ⊕_{u'} (V_u ∩ V'_{u'})`, and
   symmetrically.
2. *`u ≠ 0`: one piece.*  If `x ∈ V_u ∩ V'_{u'}`, `x' ∈ V_u ∩ V'_{v'}` are nonzero with
   `u' ≠ v'`, choose `e ∈ V_{−u}` with `b(x, e) = 0`, `b(x', e) = 1` (`V_u × V_{−u}` is a perfect
   pairing).  The Eichler transformation `v ↦ v + b(v, e) x − b(v, x) e` preserves every `V_w`,
   lies in `SO(V)` with determinant `1` and lifts to `GSpin` (`exists_specP_eq_of_det_eq_one`),
   so it lies in `M = M'`; it sends `x'` to `x' + x ∉ V'_{v'}`, a contradiction.
3. *`u = 0`: reducedness.*  If `0 ≠ x ∈ V_0 ∩ V'_{u'}` with `u' ≠ 0`, `x` is isotropic, so
   `V_0` (nondegenerate, not a hyperbolic plane) has dimension `≥ 3`; take `e ∈ V_0` with
   `b(x, e) = 1`, `Q(e) = 0`, and `f ∈ V_0` anisotropic orthogonal to `x`, `e` (`b = bform Q`,
   so `b(v, v) = Q(v)`).  The Eichler transformation
   `v ↦ v + b(v, e) f − b(v, f) e − (Q(f)/2) b(v, e) e` acts on `V_0` only, so lies in `M = M'`,
   and sends `x` to `x' = x + f − (Q(f)/2) e` with `b(x, x') = −Q(f)/2 ≠ 0`; but `V'_{u'}` is
   totally isotropic and contains `x` and `x'`, a contradiction.
From 1–3 each nonzero `V_u` lies in one `V'_{u'}` and each nonzero `V'_{u'}` in one `V_v`, hence
`V_u = V'_{u'}` (`disjoint_wtSpan`). -/
theorem sameWtSpaces_of_M_eq (hM : L'.M = L.M) : SameWtSpacesW L L' ∧ SameWtSpacesV L L' := by
  sorry

end ReducedLeviDatum

end GGPData

end GSpinGGP
