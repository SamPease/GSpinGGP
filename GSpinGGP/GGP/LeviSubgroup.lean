/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.Levi
import GSpinGGP.TraceFormula.FlagLevi
import GSpinGGP.HarmonicAnalysis.LeviComplement
import GSpinGGP.TraceFormula.SpinorNorm

/-!
# Levi subgroups of `G` as subgroups, the set `𝒫(M)`, `a_M` and `H_P`

`parInd` (`GGP/Levi.lean`) induces from the quotient `P/U` (`LeviQuot`).  The weighted orbital
integrals and the spectral side need the Levi `M` as a *subgroup* of `G`, the finite set `𝒫(M)`
of parabolic subgroups with Levi component `M`, the real vector space `a_M` and the map `H_P`
(Thesis §2.1, §2.6, §5.1.2; Waldspurger 2003 §I.1; Beuzart-Plessis, Astérisque 418, §1.1, §1.10).
This file builds these objects for `G = GSpin(W) × GSpin(V)` and the Levi subgroups of its flag
stabilizers (M. Asgari, *Local L-functions for split spinor groups*, Canad. J. Math. 54 (2002),
§2: `M ≅ ∏ GL × GSpin`).

## Main definitions

* `GGPData.IsLevi FW FV M`: `M` is a closed subgroup of `P = P_{F_W} × P_{F_V}` complementary to
  the unipotent radical `U = N_{F_W} × N_{F_V}` (`P = M U`, `M ∩ U = 1`).  `P` and `U` are the
  genuine flag stabilizer and its unipotent radical, only `M` is free: so `U` cannot be replaced
  by a larger or smaller normal subgroup (a structure with `P`, `M`, `U` all free admits junk such
  as `M = 1`, `U = P`).
* `GGPData.parabolics M`: `𝒫(M)`, the parabolic subgroups `P_{F_W} × P_{F_V}` having `M` as a
  Levi component.
* `GGPData.FlagLeviDatum`: flags with splittings of their weight filtrations; its Levi
  `M = flagLeviG`, its opposite datum (`FlagLeviDatum.opp`, the opposite parabolic `P̄ = M Ū`),
  the space `a_M = Coord → ℝ` and `H_M : M → a_M`.
* `GGPData.hP`: `H_P(g) = H_M(m)` for `g = m u k`, any `P ∈ 𝒫(M)` and any compact open `K`
  with `G = P K`.

## Main results

* `IsFlagSplitting.flagLevi_inf_flagUnip`: `M_F ∩ N_F = 1`.
* `GGPData.FlagLeviDatum.isLevi`: `M = M_{F_W} × M_{F_V}` is a Levi of `P`;
  `IsLevi.leviQuotEquiv : M ≃* P/U` connects it with `LeviQuot`.
* `GGPData.FlagLeviDatum.mem_parabolics`, `opp_mem_parabolics`: `P, P̄ ∈ 𝒫(M)`.
* `GGPData.hP_mul`: `H_P(m u k) = H_M(m)` (well defined for any `K` with `G = P K`).
-/

noncomputable section

open Topology Filter Module

namespace GSpinGGP

/-! ## 1. `M_F ∩ N_F = 1`, closedness, and `M` of the opposite weights -/

section FlagLevi

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} {F : IsotropicFlag Q}
variable {ι : Type*} [Fintype ι] {b : Basis ι K V} {wt : ι → ℤ}

omit [Invertible (2 : K)] [Fintype ι] in
theorem wtProj_basis (w : ℤ) (j : ι) :
    wtProj b wt w (b j) = if wt j = w then b j else 0 := by
  simp [wtProj]

omit [Invertible (2 : K)] [Fintype ι] in
/-- `x` is homogeneous of weight `w` iff it is fixed by the weight projection `wtProj w`. -/
theorem isHomog_iff_wtProj (x : V) (w : ℤ) : IsHomog b wt x w ↔ wtProj b wt w x = x := by
  constructor
  · intro hx
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [repr_wtProj]
    split_ifs with h
    · rfl
    · exact (hx i h).symm
  · intro hx i hi
    rw [← hx, repr_wtProj]; simp [hi]

omit [Fintype ι] in
/-- `g ∈ M_F` iff `P(g)` maps each `bⱼ` to a vector of the same weight. -/
theorem mem_flagLevi_iff {g : GSpin Q} :
    g ∈ flagLevi (Q := Q) b wt ↔ ∀ j, IsHomog b wt (specP Q g (b j)) (wt j) := by
  refine ⟨fun hg j => ?_, fun h => wtProj_comp_of_isHomog h⟩
  rw [isHomog_iff_wtProj]
  have := congr($(hg (wt j)) (b j))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, wtProj_basis] at this
  exact this.symm

omit [Fintype ι] in
/-- The Levi subgroup depends only on the weight spaces: `M(b, −wt) = M(b, wt)`. -/
theorem flagLevi_neg : flagLevi (Q := Q) b (-wt) = flagLevi (Q := Q) b wt := by
  ext g
  simp only [mem_flagLevi_iff, IsHomog, Pi.neg_apply, ne_eq, neg_inj]

/-- **`M_F ∩ N_F = 1`**: an element of the Levi subgroup preserves every weight space, and an
element of `N_F` acts trivially on the graded pieces of the weight filtration, so `P(g) = 1`;
then `g` is a scalar `c` (`ker_specP`) with `c − 1` nilpotent, so `c = 1`. -/
theorem IsFlagSplitting.flagLevi_inf_flagUnip [FiniteDimensional K V] (hQ : IsNondeg Q)
    (hs : IsFlagSplitting F b wt) : flagLevi (Q := Q) b wt ⊓ flagUnip F = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hm, hu⟩
  have hA : ∀ j, specP Q g (b j) = b j := by
    intro j
    have hh := (isHomog_iff_wtProj _ _).1 (mem_flagLevi_iff.1 hm j)
    have hr := F.specP_sub_mem_flagWt (flagUnip_le_flagUnipSO F hu) (wt j) (b j) (hs.mem j)
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    by_cases hij : wt i = wt j
    · have := hs.repr_eq_zero _ _ hr i (by omega)
      rwa [map_sub, Finsupp.sub_apply, sub_eq_zero] at this
    · have hji : j ≠ i := fun h => hij (h ▸ rfl)
      rw [← hh, repr_wtProj]
      simp [hij, b.repr_self, hji]
  have hker : g ∈ (specP Q).ker := by
    rw [MonoidHom.mem_ker]
    refine LinearEquiv.toLinearMap_injective (b.ext fun j => ?_)
    simpa using hA j
  rw [ker_specP hQ] at hker
  obtain ⟨c, rfl⟩ := hker
  have hn := hu.2.2.2
  have hc : ((scalarGSpin Q c : GSpin Q) : (CliffordAlgebra Q)ˣ) =
      Units.map (algebraMap K (CliffordAlgebra Q)).toMonoidHom c := rfl
  rw [hc, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    ← map_one (algebraMap K (CliffordAlgebra Q)), ← map_sub] at hn
  have hc1 : (c : K) - 1 = 0 :=
    ((IsNilpotent.map_iff (algebraMap K (CliffordAlgebra Q)).injective).1 hn).eq_zero
  rw [Subgroup.mem_bot, show c = 1 from Units.ext (sub_eq_zero.1 hc1), map_one]

omit [Fintype ι] in
/-- `M_F` is closed in `GSpin(V)`. -/
theorem isClosed_flagLevi [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    [Module.Finite K V] : IsClosed (flagLevi (Q := Q) b wt : Set (GSpin Q)) := by
  have h : (flagLevi (Q := Q) b wt : Set (GSpin Q)) = ⋂ j, {g : GSpin Q |
      specP Q g (b j) - 0 ∈ LinearMap.ker (wtProj b wt (wt j) - LinearMap.id)} := by
    ext g
    simp only [SetLike.mem_coe, mem_flagLevi_iff, isHomog_iff_wtProj, Set.mem_iInter,
      Set.mem_ofPred_eq, sub_zero, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
  rw [h]
  exact isClosed_iInter fun j => isClosed_setOf_specP_sub_mem _ _ _

end FlagLevi

/-! ## 2. Levi subgroups of `P = P_{F_W} × P_{F_V}` -/

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

/-- **`M` is a Levi subgroup of `P = P_{F_W} × P_{F_V}`** (Thesis §5.1.2: `P = M N`;
Beuzart-Plessis §1.1): a closed subgroup of `P` complementary to the unipotent radical
`U = N_{F_W} × N_{F_V}`, i.e. `M ∩ U = 1` and `P = M U` (Mathlib's `Subgroup.IsComplement'`,
inside `P`).  `M` normalizes `U` because `U` is normal in `P` (`whittU_normal`).  The Levi
subgroups `flagLeviG` of splittings of the flags are examples (`FlagLeviDatum.isLevi`). -/
structure IsLevi (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) (M : Subgroup ↥d.G) :
    Prop where
  isClosed : IsClosed (M : Set ↥d.G)
  le : M ≤ d.whittB FW FV
  isComplement' : (M.subgroupOf (d.whittB FW FV)).IsComplement'
    ((d.whittU FW FV).subgroupOf (d.whittB FW FV))

variable {d}

namespace IsLevi

variable {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV} {M : Subgroup ↥d.G}

/-- `M ∩ U = 1`. -/
theorem inf_eq_bot (hL : d.IsLevi FW FV M) : M ⊓ d.whittU FW FV = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hm, hu⟩
  have := Subgroup.disjoint_def.1 hL.isComplement'.disjoint
    (x := ⟨g, hL.le hm⟩) hm hu
  simpa using congrArg Subtype.val this

/-- `P = M U`. -/
theorem exists_mul (hL : d.IsLevi FW FV M) {p : ↥d.G} (hp : p ∈ d.whittB FW FV) :
    ∃ m ∈ M, ∃ u ∈ d.whittU FW FV, p = m * u := by
  obtain ⟨⟨m, u⟩, he⟩ := hL.isComplement'.2 ⟨p, hp⟩
  exact ⟨m.1.1, m.2, u.1.1, u.2, by simpa using (congrArg Subtype.val he).symm⟩

/-- The projection `P → M`, `m u ↦ m`. -/
def proj (hL : d.IsLevi FW FV M) : ↥(d.whittB FW FV) →* ↥M :=
  (Subgroup.subgroupOfEquivOfLe hL.le).toMonoidHom.comp hL.isComplement'.proj

theorem proj_mul (hL : d.IsLevi FW FV M) (m : ↥M) {u : ↥d.G} (hu : u ∈ d.whittU FW FV) :
    hL.proj ⟨(m : ↥d.G) * u, (d.whittB FW FV).mul_mem (hL.le m.2) (d.whittU_le_whittB FW FV hu)⟩ =
      m := by
  have := hL.isComplement'.proj_mul ⟨⟨m, hL.le m.2⟩, m.2⟩
    (n := ⟨u, d.whittU_le_whittB FW FV hu⟩) hu
  simp only [proj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [show (⟨(m : ↥d.G) * u, _⟩ : ↥(d.whittB FW FV)) =
    ((⟨⟨m, hL.le m.2⟩, m.2⟩ : ↥(M.subgroupOf (d.whittB FW FV))) : ↥(d.whittB FW FV)) *
      ⟨u, d.whittU_le_whittB FW FV hu⟩ from rfl, this]
  rfl

/-- **`M ≅ P/U`**: a Levi subgroup is isomorphic to the Levi quotient `LeviQuot` used by `parInd`
(`Subgroup.IsComplement'.QuotientMulEquiv`). -/
def leviQuotEquiv (hL : d.IsLevi FW FV M) : ↥M ≃* d.LeviQuot FW FV :=
  (Subgroup.subgroupOfEquivOfLe hL.le).symm.trans hL.isComplement'.QuotientMulEquiv.symm

theorem leviQuotEquiv_apply (hL : d.IsLevi FW FV M) (m : ↥M) :
    hL.leviQuotEquiv m = QuotientGroup.mk ⟨(m : ↥d.G), hL.le m.2⟩ := rfl

/-- The projection `P → M` is continuous (open mapping theorem: `M` is σ-compact and `P/U` is
locally compact). -/
theorem continuous_proj (hL : d.IsLevi FW FV M) : Continuous hL.proj := by
  have hcl : IsClosed ((M.subgroupOf (d.whittB FW FV) : Subgroup ↥(d.whittB FW FV)) :
      Set ↥(d.whittB FW FV)) := hL.isClosed.preimage continuous_subtypeVal
  have : LocallyCompactSpace ↥(M.subgroupOf (d.whittB FW FV)) := hcl.locallyCompactSpace
  have : SecondCountableTopology ↥(d.whittB FW FV) := d.secondCountableTopology_whittB FW FV
  have : SecondCountableTopology ↥(M.subgroupOf (d.whittB FW FV)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : SigmaCompactSpace ↥(M.subgroupOf (d.whittB FW FV)) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have he : Continuous (Subgroup.subgroupOfEquivOfLe hL.le) :=
    (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
  have : T2Space (d.LeviQuot FW FV) := d.t2Space_leviQuot FW FV
  have : LocallyCompactSpace (d.LeviQuot FW FV) := inferInstance
  exact he.comp hL.isComplement'.continuous_proj

/-- Levi subgroups of the same parabolic are never properly nested. -/
theorem eq_of_le (hL : d.IsLevi FW FV M) {M' : Subgroup ↥d.G} (hL' : d.IsLevi FW FV M')
    (h : M ≤ M') : M = M' := by
  refine le_antisymm h fun x hx => ?_
  obtain ⟨m, hm, u, hu, rfl⟩ := hL.exists_mul (hL'.le hx)
  have hu' : u ∈ M' := by
    have := M'.mul_mem (M'.inv_mem (h hm)) hx
    rwa [inv_mul_cancel_left] at this
  have : u ∈ M' ⊓ d.whittU FW FV := ⟨hu', hu⟩
  rw [hL'.inf_eq_bot, Subgroup.mem_bot] at this
  rw [this, mul_one]; exact hm

end IsLevi

/-- **Elements of the unipotent radical generate relatively compact subgroups**: all powers of
`u ∈ U` lie in one compact set (`u − 1` is nilpotent in each Clifford factor,
`exists_isCompact_zpow_of_isNilpotent`). -/
theorem exists_isCompact_zpow_of_mem_whittU {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV}
    {u : ↥d.G} (hu : u ∈ d.whittU FW FV) : ∃ C : Set ↥d.G, IsCompact C ∧ ∀ k : ℤ, u ^ k ∈ C := by
  have := properSpace_F (F := F)
  have key : ∀ {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      [TopologicalSpace V] [IsModuleTopology F V] {Q : QuadraticForm F V} {g : GSpin Q},
      IsNilpotent (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1) →
      ∃ C : Set (GSpin Q), IsCompact C ∧ ∀ k : ℤ, g ^ k ∈ C := by
    intro V _ _ _ _ _ Q g hg
    have := t2Space_cliffordAlgebra Q
    obtain ⟨C, hC, hCu⟩ := exists_isCompact_zpow_of_isNilpotent (K := F) _ hg
    refine ⟨_, (isClosed_GSpin Q).isClosedEmbedding_subtypeVal.isCompact_preimage hC,
      fun k => ?_⟩
    show ((g ^ k : GSpin Q) : (CliffordAlgebra Q)ˣ) ∈ C
    rw [Subgroup.coe_zpow]; exact hCu k
  obtain ⟨CW, hCW, hW⟩ := key hu.1.2.2.2
  obtain ⟨CV, hCV, hV⟩ := key hu.2.2.2.2
  refine ⟨d.pair '' (CW ×ˢ CV), (hCW.prod hCV).image d.continuous_pair, fun k => ?_⟩
  refine ⟨(d.fst (u ^ k), d.snd (u ^ k)), ⟨?_, ?_⟩, d.pair_fst_snd _⟩
  · show d.fst (u ^ k) ∈ CW
    rw [map_zpow]; exact hW k
  · show d.snd (u ^ k) ∈ CV
    rw [map_zpow]; exact hV k

end GGPData

end GSpinGGP
