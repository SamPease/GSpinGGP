/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalGroups
import GSpinGGP.Foundations.Representations
import GSpinGGP.Foundations.GSpin
import GSpinGGP.Literature.Measure
import GSpinGGP.Literature.GSpin

/-!
# The local trace formula: basic objects (`J`, `θ_f`, test functions)

Contents:

* parabolic subgroups `parabolicP/U`, closedness of `H`, the central subgroup `A_{G,H}` of `H`
  and the quotient group `H(F)/A_{G,H}(F)` (`HmodAGH`);
* the quotient group `G(F)/A_G(F)` (`GmodAG`), the induced injection
  `toGmodAG : H(F)/A_{G,H}(F) → G(F)/A_G(F)` and the coset space
  `HGQuot = H(F)\G(F)/A_G(F)` (Thesis §7.1);
* the Weil quotient measure `weilMeasureHG` on `HGQuot`, fixed by the Haar
  measures on `G/A_G` and `H/A_{G,H}`;
* strongly cuspidal test functions `ScuspTestFn d χ` (Thesis §4.5, §7.1, with
  `C_c^∞` mod `A_G` in place of the Harish-Chandra Schwartz space);
* the kernel `K(f,x)` and the distribution `J(f)` (Thesis §7.1);
* the orbital pairing and the function `θ_f` (Thesis §4.8; BP §5.5), defined as
  *the* locally integrable function representing `f' ↦ ∫_{G/A_G} ∫_G f(x⁻¹gx) f'(g) dg dx`;
* the elliptic regular set `ellRegSet d` (Thesis §2.5).

## Normalization

`θ_f` and `J` are both tied to one measure, `Measure.haar` on the quotient group `G(F)/A_G(F)`:
`θ_f` through the orbital pairing, `J` through the Weil quotient measure.  The Haar measure on
`H(F)/A_{G,H}(F)` cancels in `J` (`IsWeilMeasure.smul_right`).  So `J(f) = m_geom(θ_f)` does not
depend on any normalization; the normalization of Thesis §2.4 is not
modelled.

## Measurable structures on quotient groups

Mathlib's global instance `QuotientGroup.measurableSpace` puts the *pushforward* σ-algebra on
`G ⧸ N`.  We want the Borel σ-algebra of the quotient topology (needed for `Measure.haar` to be a
Haar measure and for `weil_quotient`).  We declare `borel` instances on `GmodAG` and `HmodAGH`
with high priority, so instance search picks them (`borelSpace_GmodAG` etc. are then `⟨rfl⟩`).
-/

noncomputable section

open MeasureTheory Topology Filter
open scoped Pointwise

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-! ## 0. Topological instances on `G(F)`

`GGP/Triple.lean` and `Literature/HarishChandra.lean` declare the same instances; this file sits
in the same layer as those and cannot import them, so it redeclares them under
its own namespace (both are `Prop`-valued, so the copies do not conflict). -/

namespace TraceFormulaBasic

/-- `G(F)` is Hausdorff (LocalGroups `subgroup_t2Space`). -/
instance t2Space_G (d : GGPData F) : T2Space ↥d.G :=
  subgroup_t2Space F d.ambient d.G

/-- `G(F)` is locally compact (`d.G` is closed in `(C(W) × C(V))ˣ`, `GGPData.isClosed_G`). -/
instance locallyCompactSpace_G (d : GGPData F) : LocallyCompactSpace ↥d.G :=
  subgroup_locallyCompactSpace_of_isClosed F d.ambient d.G d.isClosed_G

/-- The ambient algebra `C(W) × C(V)` is second countable (`F` is proper, hence second
countable, and `C(W) × C(V) ≅ F^n` as topological vector spaces, LocalGroups `toPiCLE`). -/
theorem secondCountableTopology_ambient (d : GGPData F) : SecondCountableTopology d.ambient := by
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  exact (toPiCLE F d.ambient).toHomeomorph.secondCountableTopology

/-- `G(F)` is second countable (a subspace of `(C(W) × C(V))ˣ ⊆ (C(W) × C(V)) × (C(W) × C(V))ᵐᵒᵖ`).
Hence also σ-compact (`sigmaCompactSpace_of_locallyCompact_secondCountable`), and so are its
closed subgroups and quotients. -/
instance secondCountableTopology_G (d : GGPData F) : SecondCountableTopology ↥d.G := by
  have := secondCountableTopology_ambient d
  have : SecondCountableTopology d.ambientᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := d.ambient)).symm.secondCountableTopology
  have : SecondCountableTopology d.ambientˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

end TraceFormulaBasic

/-! ### Closedness of the split centre -/

section SplitCentre

variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]
  [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] [Module.Finite K V]

/-- The central scalars `K^× ⊆ GSpin(V)` form a closed subgroup: they are the elements of
`GSpin(V)` lying in the line `K · 1 ⊆ C(V)`, which is closed (LocalGroups/GSpin
`isClosed_submodule_of_moduleTopology`). -/
theorem isClosed_range_scalarGSpin (Q : QuadraticForm K V) :
    IsClosed ((scalarGSpin Q).range : Set (GSpin Q)) := by
  have hS := isClosed_submodule_of_moduleTopology (K := K)
    (LinearMap.range (Algebra.linearMap K (CliffordAlgebra Q)))
  have hc : Continuous (fun g : GSpin Q => ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) :=
    Units.continuous_val.comp continuous_subtype_val
  convert hS.preimage hc using 1
  ext g
  simp only [Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_range, MonoidHom.mem_range,
    Algebra.linearMap_apply]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, hc⟩
    by_cases h0 : c = 0
    · -- then `0` is a unit of `C(V)`, so `C(V)` is trivial and `g = 1`
      have h01 : (0 : CliffordAlgebra Q) = 1 := by
        have := (g : (CliffordAlgebra Q)ˣ).mul_inv
        rw [← hc, h0, map_zero, zero_mul] at this
        exact this
      have : Subsingleton (CliffordAlgebra Q) := subsingleton_of_zero_eq_one h01
      refine ⟨1, ?_⟩
      apply Subtype.ext
      apply Units.ext
      exact Subsingleton.elim _ _
    · refine ⟨Units.mk0 c h0, ?_⟩
      apply Subtype.ext
      apply Units.ext
      exact hc

/-- The split centre `A_{GSpin(V)}` is closed in `GSpin(V)` (it is all of `GSpin(V)` or the
scalars). -/
theorem isClosed_splitCentralGSpin (Q : QuadraticForm K V) :
    IsClosed (splitCentralGSpin Q : Set (GSpin Q)) := by
  classical
  unfold splitCentralGSpin
  split_ifs
  · exact isClosed_univ
  · exact isClosed_range_scalarGSpin Q

end SplitCentre

/-! ## 1. Closed subgroups, `A_{G,H}` and `H(F)/A_{G,H}(F)` -/

/-- **Closed embedding of quotient groups** (generic).  Let `G` be a locally
compact, second countable topological group, `A ⊴ G` closed, `H ≤ G` locally compact, and
`N = A ∩ H` (as a subgroup of `H`).  If `H · A` is closed in `G`, then the induced injection
`H/N → G/A` is a closed embedding.  Proof: its range `HA/A` is closed (quotient topology); the
corestriction `H/N → HA/A` is a continuous bijective homomorphism from a σ-compact group onto a
locally compact Hausdorff group, hence open (open mapping theorem,
`MonoidHom.isOpenMap_of_sigmaCompact`), hence a homeomorphism. -/
theorem _root_.QuotientGroup.isClosedEmbedding_map_of_isClosed_mul {G : Type*} [Group G]
    [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    {H A : Subgroup G} [A.Normal] [IsClosed (A : Set G)] [LocallyCompactSpace H]
    (N : Subgroup H) [N.Normal] (hN : N = A.subgroupOf H) (hle : N ≤ A.comap H.subtype)
    (hHA : IsClosed ((H : Set G) * (A : Set G))) :
    IsClosedEmbedding (QuotientGroup.map N A H.subtype hle) := by
  set f := QuotientGroup.map N A H.subtype hle with hf_def
  have hcont : Continuous f :=
    continuous_coinduced_dom.2 (QuotientGroup.continuous_mk.comp continuous_subtype_val)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H h =>
      have h1 : f (QuotientGroup.mk h) = QuotientGroup.mk (h : G) := rfl
      rw [h1, QuotientGroup.eq_one_iff] at hq
      rw [QuotientGroup.eq_one_iff, hN]
      exact hq
  have hrange : Set.range f = QuotientGroup.mk '' (H : Set G) := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H h => exact ⟨h, h.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨QuotientGroup.mk ⟨g, hg⟩, rfl⟩
  have hclosed : IsClosed (Set.range f) := by
    rw [hrange, ← (QuotientGroup.isQuotientMap_mk A).isClosed_preimage,
      QuotientGroup.preimage_image_mk_eq_mul]
    exact hHA
  have hRc : IsClosed (f.range : Set (G ⧸ A)) := by
    rw [MonoidHom.coe_range]; exact hclosed
  have : LocallyCompactSpace f.range := hRc.locallyCompactSpace
  have hf'c : Continuous f.rangeRestrict := continuous_induced_rng.2 hcont
  have : SecondCountableTopology H := IsEmbedding.subtypeVal.secondCountableTopology
  have hf'o : IsOpenMap f.rangeRestrict :=
    f.rangeRestrict.isOpenMap_of_sigmaCompact f.rangeRestrict_surjective hf'c
  have hbij : Function.Bijective f.rangeRestrict :=
    ⟨MonoidHom.rangeRestrict_injective_iff.2 hinj, f.rangeRestrict_surjective⟩
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap hcont hinj ?_
  intro C hC
  have himg : f '' C = Subtype.val '' (f.rangeRestrict '' C) := by
    rw [Set.image_image]; rfl
  have hC' : IsClosed (f.rangeRestrict '' C) := by
    rw [← compl_compl C, Set.image_compl_eq hbij]
    exact (hf'o _ hC.isOpen_compl).isClosed_compl
  rw [himg]
  exact hRc.isClosedMap_subtype_val _ hC'


/-- Conjugation in a quotient group, at a representative.  Stated for an abstract group: on the
concrete subgroup towers of `G(F)` the same `rw [QuotientGroup.mk_mul]` times out (instance
unification through the Clifford algebras), while instantiating this lemma is instant. -/
theorem _root_.QuotientGroup.mk_conj_out {S : Type*} [Group S] (N : Subgroup S) [N.Normal]
    (h : S) (q : S ⧸ N) :
    ((h⁻¹ * Quotient.out q * h : S) : S ⧸ N) = (h : S ⧸ N)⁻¹ * q * (h : S ⧸ N) := by
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq']

namespace GGPData

variable (d : GGPData F)

/-- The parabolic subgroup `P = P_{F_W} × P_{F_V}` of `G` attached to isotropic flags of `W` and
`V` (Thesis §5.1.2: every parabolic subgroup of `G = GSpin(W) × GSpin(V)` is of this form).
(This is `GGPData.whittB`, which despite its name is defined for arbitrary flags.) -/
abbrev parabolicP (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) : Subgroup ↥d.G :=
  d.whittB FW FV

/-- Its unipotent radical `U = N_{F_W} × N_{F_V}` (= `GGPData.whittU` for arbitrary flags). -/
abbrev parabolicU (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) : Subgroup ↥d.G :=
  d.whittU FW FV

/-- `U(F)` is closed in `G(F)` (it is the group of `F`-points of a closed subgroup). -/
theorem isClosed_parabolicU (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) :
    IsClosed (d.parabolicU FW FV : Set ↥d.G) :=
  d.isClosed_whittU FW FV

instance locallyCompactSpace_parabolicU (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) :
    LocallyCompactSpace ↥(d.parabolicU FW FV) :=
  (d.isClosed_parabolicU FW FV).locallyCompactSpace

/-- `H(F)` is closed in `G(F)` (from `GGPData.isClosed_H`, closedness in `(C(W) × C(V))ˣ`). -/
theorem isClosed_H_in_G : IsClosed (d.H : Set ↥d.G) := by
  have h := d.isClosed_H.preimage (continuous_subtype_val (p := fun x => x ∈ d.G))
  have he : (Subtype.val ⁻¹' ((d.H.map d.G.subtype : Subgroup d.ambientˣ) : Set d.ambientˣ) :
      Set ↥d.G) = (d.H : Set ↥d.G) := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rwa [he] at h

instance locallyCompactSpace_H : LocallyCompactSpace ↥d.H :=
  d.isClosed_H_in_G.locallyCompactSpace

/-- `H(F)` is second countable (a subspace of `G(F)`). -/
instance secondCountableTopology_H : SecondCountableTopology ↥d.H :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

/-- `A_{G,H}` is central in `G` (from `center_inf_H_eq_AGH`). -/
theorem AGH_le_center : d.AGH ≤ Subgroup.center ↥d.G := by
  rw [← d.center_inf_H_eq_AGH]
  exact inf_le_left

/-- `A_{G,H} ⊆ H` (from `AG_inf_H`). -/
theorem AGH_le_H' : d.AGH ≤ d.H := by
  rw [← d.AG_inf_H]
  exact inf_le_right

/-- `λ(1) = 0`. -/
theorem lam_one : d.lam 1 = 0 := by
  have h := d.lam_mul 1 1
  rw [mul_one] at h
  simpa using h

/-- `ξ(1) = 1`. -/
theorem xi_one (ψ : AddChar F Circle) : d.xi ψ 1 = 1 := by
  unfold xi
  rw [lam_one, AddChar.map_zero_eq_one]
  rfl

/-- `ξ` is invariant under conjugation in `H(F)` (`ξ` is a character with values in a commutative
group). -/
theorem xi_conj (ψ : AddChar F Circle) (h k : ↥d.H) : d.xi ψ (h⁻¹ * k * h) = d.xi ψ k := by
  rw [d.xi_mul, d.xi_mul, mul_comm (d.xi ψ h⁻¹), mul_assoc, ← d.xi_mul, inv_mul_cancel, xi_one,
    mul_one]

/-- `ξ` is trivial on `A_{G,H}(F)`: for `h = (c, c)` the unipotent part is `1`, and
`λ(1) = Σ b(z_{−i−1}, z_i) = 0`.  (Same statement as `GGPData.xi_eq_one_of_mem_AGH` of
`GGP/Triple.lean`, which this layer cannot import.) -/
theorem xi_eq_one_of_mem_AGH' (ψ : AddChar F Circle) (h : ↥d.H) (hh : (h : ↥d.G) ∈ d.AGH) :
    d.xi ψ h = 1 := by
  obtain ⟨c, hc⟩ := hh
  have hn : d.nPart (h : ↥d.G) = 1 := by
    rw [← hc]
    change (d.incl (d.fst (d.diag _)))⁻¹ * d.snd (d.diag _) = 1
    exact inv_mul_cancel _
  have hlam : d.lam h = 0 := by
    unfold lam
    rw [hn, map_one]
    refine Finset.sum_eq_zero fun i _ => ?_
    change bform d.QV (d.zV (-(i : ℤ) - 1)) (d.zV (i : ℕ)) = 0
    have hi := i.2
    rw [bform_QV_zV]
    · rw [bform_splitOddForm_zvec]
      · exact ite_eq_right_iff.mpr fun h => absurd h (by omega)
      · rw [abs_le]; constructor <;> omega
      · rw [abs_le]; constructor <;> omega
  unfold xi
  rw [hlam, AddChar.map_zero_eq_one]
  rfl

/-- `A_{G,H}(F)` as a (normal, central) subgroup of `H(F)`. -/
abbrev AGHinH : Subgroup ↥d.H := d.AGH.subgroupOf d.H

instance AGHinH_normal : d.AGHinH.Normal := by
  refine Subgroup.normal_of_le_center ?_
  intro a ha
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  have hc := Subgroup.mem_center_iff.mp (d.AGH_le_center (Subgroup.mem_subgroupOf.mp ha))
    (h : ↥d.G)
  simpa using hc

/-- The quotient group `H(F)/A_{G,H}(F)` (Thesis §7.1). -/
abbrev HmodAGH : Type _ := ↥d.H ⧸ d.AGHinH

/-- The Borel σ-algebra on `H(F)/A_{G,H}(F)` (high priority, to beat Mathlib's pushforward
σ-algebra `QuotientGroup.measurableSpace`; see the module docstring). -/
instance (priority := 1100) measurableSpace_HmodAGH : MeasurableSpace d.HmodAGH := borel _

instance borelSpace_HmodAGH : BorelSpace d.HmodAGH := ⟨rfl⟩

/-! ## 2. `A_G` and the quotient group `G(F)/A_G(F)` -/

/-- The quotient group `G(F)/A_G(F)` (Thesis §7.1).  `A_G` is central
(`AG_le_center`), so this is a group; the measure used on it is `Measure.haar`. -/
abbrev GmodAG : Type _ := ↥d.G ⧸ d.AG

/-- The Borel σ-algebra on `G(F)/A_G(F)` (high priority; see the module docstring). -/
instance (priority := 1100) measurableSpace_GmodAG : MeasurableSpace d.GmodAG := borel _

instance borelSpace_GmodAG : BorelSpace d.GmodAG := ⟨rfl⟩

/-- `A_G(F) = A_{GSpin(W)}(F) × A_{GSpin(V)}(F)` as a subset of `G(F)`. -/
theorem coe_AG : (d.AG : Set ↥d.G) =
    d.fst ⁻¹' (splitCentralGSpin d.QW : Set _) ∩ d.snd ⁻¹' (splitCentralGSpin d.QV : Set _) := by
  ext g
  simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨hp.1, hp.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(d.fst g, d.snd g), ⟨h1, h2⟩, d.G_ext rfl rfl⟩

/-- `A_G(F)` is closed in `G(F)` (an instance, for Mathlib's `T3Space (G ⧸ N)`). -/
instance isClosed_AG : IsClosed (d.AG : Set ↥d.G) := by
  rw [coe_AG]
  exact ((isClosed_splitCentralGSpin d.QW).preimage d.continuous_fst).inter
    ((isClosed_splitCentralGSpin d.QV).preimage d.continuous_snd)

/-- `A_{G,H}(F)` is closed in `H(F)`: it is `A_G(F) ∩ H(F)` (`AG_inf_H`), and `A_G(F)` is
closed (`isClosed_AG`).  An instance, so that `H(F)/A_{G,H}(F)` is Hausdorff. -/
instance isClosed_AGHinH : IsClosed (d.AGHinH : Set ↥d.H) := by
  have h : (d.AGHinH : Set ↥d.H) = Subtype.val ⁻¹' (d.AG : Set ↥d.G) := by
    ext h
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
    constructor
    · intro hh
      exact d.AGH_le_AG hh
    · intro hh
      rw [← d.AG_inf_H]
      exact ⟨hh, h.2⟩
  rw [h]
  exact d.isClosed_AG.preimage continuous_subtype_val

/-- `G(F)/A_G(F)` and `H(F)/A_{G,H}(F)` are Hausdorff (indeed regular), since `A_G(F)` and
`A_{G,H}(F)` are closed. -/
example : T2Space d.GmodAG ∧ T2Space d.HmodAGH := ⟨inferInstance, inferInstance⟩

/-- `G(F)/A_G(F)` and `H(F)/A_{G,H}(F)` are second countable and locally compact. -/
example : SecondCountableTopology d.GmodAG ∧ LocallyCompactSpace d.GmodAG ∧
    SecondCountableTopology d.HmodAGH ∧ LocallyCompactSpace d.HmodAGH :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- `A_{G,H}(F) ⊆ A_G(F)` is carried into `A_G(F)` by the inclusion `H(F) ⊆ G(F)`. -/
theorem AGHinH_le_comap_AG : d.AGHinH ≤ d.AG.comap d.H.subtype := by
  intro a ha
  exact d.AGH_le_AG (Subgroup.mem_subgroupOf.mp ha)

/-- The homomorphism `H(F)/A_{G,H}(F) → G(F)/A_G(F)` induced by `H ⊆ G` (Thesis §7.1). -/
def toGmodAG : d.HmodAGH →* d.GmodAG :=
  QuotientGroup.map d.AGHinH d.AG d.H.subtype d.AGHinH_le_comap_AG

@[simp] theorem toGmodAG_mk (h : ↥d.H) :
    d.toGmodAG (QuotientGroup.mk h) = QuotientGroup.mk (h : ↥d.G) := rfl

/-- `toGmodAG` is injective, because `A_G ∩ H = A_{G,H}` (`AG_inf_H`). -/
theorem toGmodAG_injective : Function.Injective d.toGmodAG := by
  rw [injective_iff_map_eq_one]
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H h =>
    rw [toGmodAG_mk, QuotientGroup.eq_one_iff] at hq
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, ← d.AG_inf_H]
    exact ⟨hq, h.2⟩

/-- `toGmodAG` is continuous (Thesis §7.1). -/
theorem continuous_toGmodAG : Continuous d.toGmodAG := by
  apply continuous_coinduced_dom.2
  exact (QuotientGroup.continuous_mk).comp continuous_subtype_val

end GGPData

/-! ### `H(F) · A_G(F)` is closed (`isClosed_H_mul_AG`) -/

/-- **Pinning the scalar of a unipotent element by a trace** (own work, for `isClosed_H_mul_AG`).
In a nontrivial finite-dimensional algebra `A` over a field of characteristic `0`, a unit `u` has
a scalar multiple `t • u` with `t • u − 1` nilpotent iff `(D • u − τ(u))^D = 0`, where
`D = dim A` and `τ(u) = tr(L_u)`.  (Nilpotent elements have trace `0`, so `t τ(u) = D`; this pins
`t = D/τ(u)` and turns the existential condition into a closed one.) -/
theorem exists_smul_sub_one_isNilpotent_iff {K A : Type*} [Field K] [CharZero K] [Ring A]
    [Algebra K A] [FiniteDimensional K A] [Nontrivial A] {u : A} (hu : IsUnit u) :
    (∃ t : K, IsNilpotent (t • u - 1)) ↔
      ((Module.finrank K A : K) • u - LinearMap.trace K A (Algebra.lmul K A u) • (1 : A)) ^
        Module.finrank K A = 0 := by
  set D : K := (Module.finrank K A : K)
  set τ : K := LinearMap.trace K A (Algebra.lmul K A u)
  have hD : D ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have htr : ∀ t : K, LinearMap.trace K A (Algebra.lmul K A (t • u - 1)) = t * τ - D := by
    intro t
    rw [map_sub, map_smul, map_one, map_sub, map_smul, LinearMap.trace_one, smul_eq_mul]
  constructor
  · rintro ⟨t, ht⟩
    have h0 : t * τ - D = 0 := by
      rw [← htr]
      exact (LinearMap.isNilpotent_trace_of_isNilpotent (ht.map (Algebra.lmul K A))).eq_zero
    have he : D • u - τ • (1 : A) = τ • (t • u - 1) := by
      rw [smul_sub, smul_smul, mul_comm τ t, show t * τ = D by linear_combination h0]
    rw [← isNilpotent_iff_pow_finrank (K := K), he]
    exact ht.smul τ
  · intro h
    have hnil : IsNilpotent (D • u - τ • (1 : A)) := ⟨_, h⟩
    have hτ : τ ≠ 0 := by
      intro h0
      rw [h0, zero_smul, sub_zero] at hnil
      have h' : IsUnit (D • u) := by
        rw [Algebra.smul_def]
        exact ((IsUnit.mk0 D hD).map (algebraMap K A)).mul hu
      exact h'.not_isNilpotent hnil
    refine ⟨τ⁻¹ * D, ?_⟩
    have he : (τ⁻¹ * D) • u - 1 = τ⁻¹ • (D • u - τ • (1 : A)) := by
      rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hτ, one_smul, mul_smul]
    rw [he]
    exact hnil.smul _


section ClosedHAG
variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]

/-- Right multiplication by a central scalar is scalar multiplication in `C(V)`. -/
theorem coe_mul_scalarGSpin {Q : QuadraticForm K V} (n : GSpin Q) (c : Kˣ) :
    (((n * scalarGSpin Q c : GSpin Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      (c : K) • (((n : GSpin Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  rw [Algebra.smul_def, Algebra.commutes]
  rfl

/-- The scalars lie in the preimage `K^× · N_F` of `N_F^{SO}`. -/
theorem scalarGSpin_mem_flagUnipSO [FiniteDimensional K V] {Q : QuadraticForm K V}
    (F : IsotropicFlag Q) (c : Kˣ) : scalarGSpin Q c ∈ flagUnipSO F := by
  refine ⟨mem_flagStab_iff.mpr fun i v hv => ?_, fun i v _ => ?_, fun v _ => ?_⟩
  · rw [specP_scalarGSpin_eq_one]; exact hv
  · rw [specP_scalarGSpin_eq_one]; simp
  · rw [specP_scalarGSpin_eq_one]; simp

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

/-- `K^× · N_F` is closed in `GSpin(V)` (as `isClosed_flagUnip`, without the nilpotency
condition). -/
theorem isClosed_flagUnipSO [FiniteDimensional K V] {Q : QuadraticForm K V}
    (F : IsotropicFlag Q) : IsClosed (flagUnipSO F : Set (GSpin Q)) := by
  have h : (flagUnipSO F : Set (GSpin Q)) = (flagStab F : Set (GSpin Q)) ∩
      ((⋂ i : Fin F.len, ⋂ v ∈ F.sub i.succ,
          {g : GSpin Q | specP Q g v - v ∈ F.sub i.castSucc}) ∩
      (⋂ v ∈ (bform Q).orthogonal F.top, {g : GSpin Q | specP Q g v - v ∈ F.top})) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [h]
  exact (isClosed_flagStab F).inter ((isClosed_iInter fun i => isClosed_biInter fun v _ =>
    isClosed_setOf_specP_sub_mem _ _ _).inter (isClosed_biInter fun v _ =>
    isClosed_setOf_specP_sub_mem _ _ _))

end ClosedHAG

/-- Group identity with a central element (stated abstractly: on the concrete towers `group`
and `rw`'s closing `rfl` time out). -/
theorem inv_mul_mul_of_central_aux {S : Type*} [Group S] {u : S} (hu : ∀ y, y * u = u * y)
    (x y v : S) : (x * u)⁻¹ * (y * v) = x⁻¹ * y * (u⁻¹ * v) := by
  have hu' : ∀ y, u⁻¹ * y = y * u⁻¹ := fun y => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hu, mul_assoc, mul_inv_cancel, mul_one]
  rw [mul_inv_rev, mul_assoc, hu', mul_assoc, mul_assoc, ← hu' v, ← mul_assoc]

/-- Group identity with a central element (abstract; see `inv_mul_mul_of_central_aux`). -/
theorem mul_mul_inv_mul_of_central_aux {S : Type*} [Group S] {u : S} (hu : ∀ y, y * u = u * y)
    (x y : S) : x * u * (x⁻¹ * y) = y * u := by
  rw [mul_assoc, ← hu, ← mul_assoc, mul_inv_cancel_left]

namespace GGPData

variable (d : GGPData F)

/-- `fst ∘ inr = 1` (`rfl`). -/
theorem fst_inr_eq_one (y : GSpin d.QV) : d.fst (d.inr y) = 1 := rfl

/-- `g ↦ n(g) = g_W⁻¹ g_V` is continuous (also `continuous_nPart` in `TraceFormula/Analytic`, which
this file cannot import). -/
theorem continuous_nPart_coe :
    Continuous fun g : ↥d.G => (((d.nPart g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ)) := by
  have hmap : Continuous (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)) :=
    IsModuleTopology.continuous_of_linearMap
      (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)).toLinearMap
  have hW : Continuous fun g : ↥d.G => ((d.fst g : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) :=
    continuous_subtype_val.comp d.continuous_fst
  have hV : Continuous fun g : ↥d.G => ((d.snd g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) :=
    continuous_subtype_val.comp d.continuous_snd
  have hi : Continuous fun g : ↥d.G =>
      (((d.incl (d.fst g))⁻¹ : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) := by
    rw [Units.continuous_iff]
    constructor
    · have e : ∀ g : ↥d.G, ((((d.incl (d.fst g))⁻¹ : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) :
          CliffordAlgebra d.QV) = CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
            ((((d.fst g : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) :
              CliffordAlgebra d.QW) := fun g => by
        rw [← map_inv]; rfl
      exact (continuous_congr e).mpr (hmap.comp (Units.continuous_coe_inv.comp hW))
    · have e : ∀ g : ↥d.G, (((((d.incl (d.fst g))⁻¹ : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ))⁻¹ :
          (CliffordAlgebra d.QV)ˣ) = CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
            (((d.fst g : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) :=
        fun g => by
          rw [← Subgroup.coe_inv, inv_inv]; rfl
      exact (continuous_congr e).mpr (hmap.comp (Units.continuous_val.comp hW))
  unfold nPart
  simp only [Subgroup.coe_mul]
  exact hi.mul hV


/-- `g ↦ n(g)` is continuous as a map to `GSpin(V)`. -/
theorem continuous_nPart_GSpin : Continuous d.nPart :=
  continuous_induced_rng.2 d.continuous_nPart_coe

/-- **Membership in `H·A_G` (all cases).**  If `n = n(g)` lies in `K^× · N` at the level of `SO(V)`
(`flagUnipSO`) and `t · n − 1` is nilpotent in `C(V)` for some `t ∈ K`, then `g ∈ H·A_G`:
`t ≠ 0`, and `g = (g · (1, t)) · (1, t)⁻¹` with `n(g · (1, t)) = t · n ∈ N`. -/
theorem mem_H_mul_AG_of {g : ↥d.G} (hSO : d.nPart g ∈ flagUnipSO d.flag) {t : F}
    (ht : IsNilpotent (t • (((d.nPart g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) :
      CliffordAlgebra d.QV) - 1)) :
    g ∈ (d.H : Set ↥d.G) * (d.AG : Set ↥d.G) := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_sub] at ht
    exact isUnit_one.neg.not_isNilpotent ht
  obtain ⟨c, rfl⟩ : ∃ c : Fˣ, (c : F) = t := ⟨Units.mk0 t ht0, rfl⟩
  have hh : g * d.inr (scalarGSpin d.QV c) ∈ d.H := by
    show d.nPart _ ∈ d.N
    have e : d.nPart (g * d.inr (scalarGSpin d.QV c)) = d.nPart g * scalarGSpin d.QV c := by
      simp only [nPart, map_mul, fst_inr_eq_one, snd_inr, mul_one, mul_assoc]
    rw [e]
    have hSO' := (flagUnipSO d.flag).mul_mem hSO (scalarGSpin_mem_flagUnipSO d.flag c)
    refine ⟨hSO'.1, hSO'.2.1, hSO'.2.2, ?_⟩
    rw [coe_mul_scalarGSpin]
    exact ht
  have ha : (d.inr (scalarGSpin d.QV c))⁻¹ ∈ d.AG :=
    d.AG.inv_mem ⟨(1, scalarGSpin d.QV c), ⟨(splitCentralGSpin d.QW).one_mem,
      scalarGSpin_mem_splitCentralGSpin _ _⟩, rfl⟩
  exact ⟨_, hh, _, ha, mul_inv_cancel_right _ _⟩

/-- **Membership in `H·A_G`, converse (generic case).**  If neither `W` nor `V` is a hyperbolic
plane, `A_G` is the pair of scalars, and `g = h · (c₁, c₂)` gives `n(g) = c₁⁻¹c₂ · n(h)`. -/
theorem of_mem_H_mul_AG (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) {g : ↥d.G}
    (hg : g ∈ (d.H : Set ↥d.G) * (d.AG : Set ↥d.G)) :
    d.nPart g ∈ flagUnipSO d.flag ∧ ∃ t : F, IsNilpotent (t •
      (((d.nPart g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) - 1) := by
  classical
  obtain ⟨h, hh, a, ha, rfl⟩ := hg
  obtain ⟨p, ⟨hp1, hp2⟩, rfl⟩ := ha
  have hp1' : p.1 ∈ (scalarGSpin d.QW).range := by
    unfold splitCentralGSpin at hp1; simp only [hW, ↓reduceIte] at hp1; exact hp1
  have hp2' : p.2 ∈ (scalarGSpin d.QV).range := by
    unfold splitCentralGSpin at hp2; simp only [hV, ↓reduceIte] at hp2; exact hp2
  obtain ⟨c1, hc1⟩ := hp1'
  obtain ⟨c2, hc2⟩ := hp2'
  have hz : ∀ y, y * scalarGSpin d.QV c1 = scalarGSpin d.QV c1 * y :=
    Subgroup.mem_center_iff.mp (scalarGSpin_mem_center d.QV c1)
  have e1 : d.nPart (h * d.pair p) = (d.incl (d.fst h) * scalarGSpin d.QV c1)⁻¹ *
      (d.snd h * scalarGSpin d.QV c2) := by
    simp only [nPart, map_mul, fst_pair, snd_pair, ← hc1, ← hc2, incl_scalarGSpin]
  have e : d.nPart (h * d.pair p) = d.nPart h * scalarGSpin d.QV (c1⁻¹ * c2) := by
    refine e1.trans ((inv_mul_mul_of_central_aux hz _ _ _).trans ?_)
    simp only [map_mul, map_inv]
    rfl
  have hhN : d.nPart h ∈ d.N := hh
  refine ⟨?_, ⟨(((c1⁻¹ * c2)⁻¹ : Fˣ) : F), ?_⟩⟩
  · rw [e]
    exact (flagUnipSO d.flag).mul_mem (flagUnip_le_flagUnipSO _ hhN)
      (scalarGSpin_mem_flagUnipSO _ _)
  · rw [e, coe_mul_scalarGSpin, smul_smul, Units.inv_mul, one_smul]
    exact hhN.2.2.2

end GGPData

/-! ### `GSpin(W) · N` is closed when `dim W = 2` (`isClosed_incl_range_mul_N_of_finrank_eq_two`)

Used by `isClosed_H_mul_AG` when `W` is a hyperbolic plane.  For `b = a n` (`a ∈ GSpin(W)`,
`n ∈ N`) the component `a = s + t ω ∈ C⁺(W) = K ⊕ K ω` is pinned by two traces, because
`tr(L_{x n}) = tr(L_x)` for `x ∈ C(W)`: `x (n − 1)` has positive weight for the weight filtration
of `C(V)` attached to the flag (Foundations/GSpin `sub_one_mem_wtFil_one`), hence is nilpotent. -/

section PlaneClifford

variable {K : Type*} [Field K] [Invertible (2 : K)] {W : Type*} [AddCommGroup W] [Module K W]

open CliffordAlgebra in
/-- In an orthogonal basis of a nondegenerate plane both basis vectors are anisotropic. -/
theorem ne_zero_of_orthogonal_basis_fin_two {Q : QuadraticForm K W} (hQ : IsNondeg Q)
    (e : Module.Basis (Fin 2) K W) (he : ∀ i j, i ≠ j → bform Q (e i) (e j) = 0) (i : Fin 2) :
    Q (e i) ≠ 0 := by
  intro h0
  have hz : bform Q (e i) = 0 := by
    refine e.ext fun j => ?_
    by_cases hij : i = j
    · subst hij
      rw [LinearMap.zero_apply, bform, QuadraticMap.associated_eq_self_apply, h0]
    · rw [LinearMap.zero_apply]; exact he i j hij
  exact e.ne_zero i ((isNondeg_iff Q).mp hQ (e i) fun y => by rw [hz]; rfl)

open CliffordAlgebra in
/-- `ι e₁ ι e₀ = − ι e₀ ι e₁` for orthogonal `e₀, e₁`. -/
theorem ι_mul_ι_swap_of_orthogonal {Q : QuadraticForm K W} {u w : W} (h : bform Q u w = 0) :
    ι Q w * ι Q u = -(ι Q u * ι Q w) := by
  have h1 := ι_mul_ι_add_swap (Q := Q) w u
  have hb : bform Q w u = 0 := by rw [bform_comm]; exact h
  rw [polar_eq_two_mul_bform, hb, mul_zero, (algebraMap K (CliffordAlgebra Q)).map_zero] at h1
  exact eq_neg_of_add_eq_zero_left h1

open CliffordAlgebra in
/-- In a plane, odd elements of the Clifford algebra are vectors. -/
theorem mem_range_ι_of_mem_evenOdd_one_of_fin_two {Q : QuadraticForm K W} (hQ : IsNondeg Q)
    (e : Module.Basis (Fin 2) K W) (he : ∀ i j, i ≠ j → bform Q (e i) (e j) = 0)
    {x : CliffordAlgebra Q} (hx : x ∈ evenOdd Q 1) : x ∈ LinearMap.range (ι Q) := by
  have h0 := ne_zero_of_orthogonal_basis_fin_two hQ e he 0
  have hev : ι Q (e 0) * x ∈ evenOdd Q 0 := by
    have := SetLike.mul_mem_graded (ι_mem_evenOdd_one Q (e 0)) hx
    rwa [show (1 : ZMod 2) + 1 = 0 from rfl] at this
  obtain ⟨p, q, hpq⟩ := exists_eq_smul_one_add_smul_of_even e he _ hev
  have hsq : ι Q (e 0) * ι Q (e 0) = Q (e 0) • (1 : CliffordAlgebra Q) := by
    rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one]
  have key : Q (e 0) • x = ι Q (p • e 0 + (q * Q (e 0)) • e 1) := by
    have : Q (e 0) • x = ι Q (e 0) * (ι Q (e 0) * x) := by
      rw [← mul_assoc, hsq, smul_mul_assoc, one_mul]
    rw [this, hpq, mul_add, mul_smul_comm, mul_smul_comm, mul_one, ← mul_assoc, hsq,
      smul_mul_assoc, one_mul, map_add, map_smul, map_smul, smul_smul, mul_comm q]
  refine ⟨(Q (e 0))⁻¹ • (p • e 0 + (q * Q (e 0)) • e 1), ?_⟩
  rw [map_smul, ← key, smul_smul, inv_mul_cancel₀ h0, one_smul]

open CliffordAlgebra in
/-- In a plane, every unit of the even Clifford algebra lies in `GSpin` (`dim W = 2`:
`C⁺(W)^× = GSpin(W)`). -/
theorem mem_GSpin_of_even_of_fin_two {Q : QuadraticForm K W} (hQ : IsNondeg Q)
    (e : Module.Basis (Fin 2) K W) (he : ∀ i j, i ≠ j → bform Q (e i) (e j) = 0)
    (g : (CliffordAlgebra Q)ˣ) (hg : (g : CliffordAlgebra Q) ∈ evenOdd Q 0)
    (hg' : ((g⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 0) : g ∈ GSpin Q := by
  have hodd : ∀ a b : CliffordAlgebra Q, a ∈ evenOdd Q 0 → b ∈ evenOdd Q 0 → ∀ v,
      a * ι Q v * b ∈ LinearMap.range (ι Q) := by
    intro a b ha hb v
    refine mem_range_ι_of_mem_evenOdd_one_of_fin_two hQ e he ?_
    have := SetLike.mul_mem_graded (SetLike.mul_mem_graded ha (ι_mem_evenOdd_one Q v)) hb
    rwa [show (0 : ZMod 2) + 1 + 0 = 1 from rfl] at this
  refine ⟨?_, hodd _ _ hg hg', hodd _ _ hg' hg⟩
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]; exact hg

end PlaneClifford

/-- `x ↦ tr(L_x)` as a linear functional. -/
theorem trace_mulLeft_eq_comp {K A : Type*} [Field K] [Ring A] [Algebra K A] (x : A) :
    LinearMap.trace K A (LinearMap.mulLeft K x) =
      ((LinearMap.trace K A).comp (LinearMap.mul K A)) x := rfl

namespace GGPData

variable (d : GGPData F)

section PlaneClosed

open CliffordAlgebra

/-- `W ⊆ V_{≥0} = Z_rᗮ` for the weight filtration of the flag `Z_•` (which lies in `Z = Wᗮ`). -/
theorem inl_mem_flagWt_zero (w : Fin d.m → F) :
    QuadraticMap.Isometry.inl d.QW d.QZ w ∈ flagWt d.flag 0 := by
  rw [d.flag.flagWt_of_nonpos le_rfl, LinearMap.BilinForm.mem_orthogonal_iff]
  intro v hv
  have h1 : v.1 = 0 := (d.span_flag_le _ hv).1
  show bform d.QV v _ = 0
  rw [bform_prod, h1]
  simp

/-- `C(W) ⊆ C(V)` has weight `≥ 0`. -/
theorem map_inl_mem_wtFil_zero (x : CliffordAlgebra d.QW) :
    CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ) x ∈
      wtFil d.QV (flagWt d.flag) 0 := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact algebraMap_mem_wtFil r le_rfl
  | ι w =>
    rw [CliffordAlgebra.map_apply_ι]
    have := ι_mul_mem_wtFil (Q := d.QV) (d.inl_mem_flagWt_zero w)
      (algebraMap_mem_wtFil (Q := d.QV) (Vf := flagWt d.flag) 1 le_rfl)
    simpa using this
  | mul x y hx hy => rw [map_mul]; simpa using mul_mem_wtFil hx hy
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- For `n ∈ N`, `n − 1` has positive weight (Foundations/GSpin `sub_one_mem_wtFil_one`). -/
theorem coe_sub_one_mem_wtFil_one {n : GSpin d.QV} (hn : n ∈ d.N) :
    ((n : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) - 1 ∈
      wtFil d.QV (flagWt d.flag) 1 := by
  have hx0 : ((n : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) ∈ evenOdd d.QV 0 := by
    have := n.2.1
    rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at this
    exact this
  refine sub_one_mem_wtFil_one d.nondeg_QV d.flag.isWtFil
    (d.flag.orthogonal_flagWt_le d.nondeg_QV) hx0 (P := (specP d.QV n : d.V →ₗ[F] d.V))
    (fun v => ?_) (d.flag.specP_sub_mem_flagWt (flagUnip_le_flagUnipSO _ hn)) hn.2.2.2
  rw [LinearEquiv.coe_coe, ι_specP, mul_assoc, Units.inv_mul, mul_one]

/-- **Traces do not see `N`**: for `x ∈ C(W)` and `n ∈ N`, `tr(L_{x n}) = tr(L_x)`, because
`x (n − 1)` has positive weight, hence is nilpotent. -/
theorem trace_map_inl_mul_N (x : CliffordAlgebra d.QW) {n : GSpin d.QV} (hn : n ∈ d.N) :
    LinearMap.trace F _ (LinearMap.mulLeft F
      (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ) x *
        ((n : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV))) =
    LinearMap.trace F _ (LinearMap.mulLeft F
      (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ) x)) := by
  set X := CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ) x
  set y := ((n : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)
  have hnil : IsNilpotent (X * (y - 1)) := isNilpotent_of_mem_wtFil_one d.flag.isWtFil
    (by simpa using mul_mem_wtFil (d.map_inl_mem_wtFil_zero x) (d.coe_sub_one_mem_wtFil_one hn))
  have hL : IsNilpotent (LinearMap.mulLeft F (X * (y - 1))) := by
    obtain ⟨k, hk⟩ := hnil
    exact ⟨k, by rw [LinearMap.pow_mulLeft, hk]; ext; simp⟩
  have h0 := (LinearMap.isNilpotent_trace_of_isNilpotent hL).eq_zero
  have e : X * y = X + X * (y - 1) := by noncomm_ring
  rw [e, trace_mulLeft_eq_comp, map_add, ← trace_mulLeft_eq_comp, ← trace_mulLeft_eq_comp, h0,
    add_zero]

/-- `tr(L_{n x}) = tr(L_x)` for `x ∈ C(W)`, `n ∈ N` (`trace_map_inl_mul_N` and `tr(L_{ab}) = tr(L_{ba})`). -/
theorem trace_N_mul_map_inl (x : CliffordAlgebra d.QW) {n : GSpin d.QV} (hn : n ∈ d.N) :
    LinearMap.trace F _ (LinearMap.mulLeft F
      (((n : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) *
        CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ) x)) =
    LinearMap.trace F _ (LinearMap.mulLeft F
      (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ) x)) := by
  rw [trace_mulLeft_comm, d.trace_map_inl_mul_N x hn]

/-- `tr(L_c) = c · dim C(V)` for a scalar `c`. -/
theorem trace_mulLeft_algebraMap (c : F) :
    LinearMap.trace F (CliffordAlgebra d.QV) (LinearMap.mulLeft F
      (algebraMap F (CliffordAlgebra d.QV) c)) =
      c * (Module.finrank F (CliffordAlgebra d.QV) : F) := by
  rw [Algebra.algebraMap_eq_smul_one, trace_mulLeft_eq_comp, map_smul, ← trace_mulLeft_eq_comp,
    LinearMap.mulLeft_one, ← Module.End.one_eq_id, LinearMap.trace_one, smul_eq_mul]

section Plane

variable {d}
variable (e : Module.Basis (Fin 2) F (Fin d.m → F))
  (he : ∀ i j, i ≠ j → bform d.QW (e i) (e j) = 0)

include he in
/-- `ω² = −q(e₀)q(e₁)` for `ω = e₀e₁`. -/
theorem planeω_sq :
    (ι d.QW (e 0) * ι d.QW (e 1)) * (ι d.QW (e 0) * ι d.QW (e 1)) =
      algebraMap F _ (-(d.QW (e 0) * d.QW (e 1))) := by
  have hsw := ι_mul_ι_swap_of_orthogonal (he 0 1 (by decide))
  calc (ι d.QW (e 0) * ι d.QW (e 1)) * (ι d.QW (e 0) * ι d.QW (e 1))
      = ι d.QW (e 0) * (ι d.QW (e 1) * ι d.QW (e 0)) * ι d.QW (e 1) := by simp only [mul_assoc]
    _ = -((ι d.QW (e 0) * ι d.QW (e 0)) * (ι d.QW (e 1) * ι d.QW (e 1))) := by
        rw [hsw]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = _ := by rw [ι_sq_scalar, ι_sq_scalar, ← map_mul, ← map_neg]

include he in
/-- `tr(L_ω) = 0` in `C(V)`: `e₀ ω e₀⁻¹ = −ω`. -/
theorem trace_map_inl_planeω :
    LinearMap.trace F (CliffordAlgebra d.QV) (LinearMap.mulLeft F
      (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
        (ι d.QW (e 0) * ι d.QW (e 1)))) = 0 := by
  have h0 := ne_zero_of_orthogonal_basis_fin_two d.nondeg e he 0
  have hsw := ι_mul_ι_swap_of_orthogonal (he 0 1 (by decide))
  set y0 := ι d.QW (e 0)
  set y1 := ι d.QW (e 1)
  set Cm := CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
  have e1 : y0 * (y0 * y1 * y0) = -(d.QW (e 0) • (y0 * y1)) := by
    calc y0 * (y0 * y1 * y0) = (y0 * y0) * (y1 * y0) := by simp only [mul_assoc]
      _ = _ := by rw [hsw, ι_sq_scalar, mul_neg, Algebra.smul_def]
  have e2 : (y0 * y1 * y0) * y0 = d.QW (e 0) • (y0 * y1) := by
    rw [mul_assoc, ι_sq_scalar, Algebra.smul_def, Algebra.commutes]
  have h := trace_mulLeft_comm d.QV (Cm y0) (Cm (y0 * y1 * y0))
  rw [← map_mul Cm, ← map_mul Cm, e1, e2, map_neg, map_smul, trace_mulLeft_eq_comp, map_neg,
    map_smul, ← trace_mulLeft_eq_comp, smul_eq_mul, trace_mulLeft_eq_comp (d.QW (e 0) • _),
    map_smul, ← trace_mulLeft_eq_comp, smul_eq_mul] at h
  have h2 : (2 * d.QW (e 0)) * LinearMap.trace F _ (LinearMap.mulLeft F (Cm (y0 * y1))) = 0 := by
    linear_combination -h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (mul_ne_zero (Invertible.ne_zero 2) h0)
  · exact h3

include he in
/-- The two traces that pin `a = s + t ω ∈ C⁺(W)`. -/
theorem trace_map_inl_planeElt (s t : F) :
    LinearMap.trace F (CliffordAlgebra d.QV) (LinearMap.mulLeft F
      (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
        (s • (1 : CliffordAlgebra d.QW) + t • (ι d.QW (e 0) * ι d.QW (e 1))))) =
      s * (Module.finrank F (CliffordAlgebra d.QV) : F) := by
  rw [map_add, map_smul, map_smul, map_one, trace_mulLeft_eq_comp, map_add, map_smul, map_smul,
    ← trace_mulLeft_eq_comp, ← trace_mulLeft_eq_comp, trace_map_inl_planeω e he,
    ← map_one (algebraMap F (CliffordAlgebra d.QV)), d.trace_mulLeft_algebraMap]
  simp

include he in
/-- `tr(L_{ω a}) = t · (−q(e₀)q(e₁)) · dim C(V)` for `a = s + t ω`. -/
theorem trace_map_inl_planeω_mul (s t : F) :
    LinearMap.trace F (CliffordAlgebra d.QV) (LinearMap.mulLeft F
      (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
        ((ι d.QW (e 0) * ι d.QW (e 1)) *
          (s • (1 : CliffordAlgebra d.QW) + t • (ι d.QW (e 0) * ι d.QW (e 1)))))) =
      t * (-(d.QW (e 0) * d.QW (e 1))) * (Module.finrank F (CliffordAlgebra d.QV) : F) := by
  rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one, planeω_sq e he, map_add, map_smul, map_smul,
    AlgHom.commutes, trace_mulLeft_eq_comp, map_add, map_smul, map_smul,
    ← trace_mulLeft_eq_comp, ← trace_mulLeft_eq_comp, trace_map_inl_planeω e he,
    d.trace_mulLeft_algebraMap]
  simp only [smul_eq_mul, mul_zero, zero_add]
  ring

/-- The element of `C⁺(W)` read off from `b ∈ C(V)` by two traces:
`α(b) = tr(L_b)/D + tr(L_{ω b})/(κ D) · ω`, `D = dim C(V)`, `κ = ω² = −q(e₀)q(e₁)`. -/
def planeCoord (b : CliffordAlgebra d.QV) : CliffordAlgebra d.QW :=
  (LinearMap.trace F (CliffordAlgebra d.QV) (LinearMap.mulLeft F b) /
      (Module.finrank F (CliffordAlgebra d.QV) : F)) • (1 : CliffordAlgebra d.QW) +
    (LinearMap.trace F (CliffordAlgebra d.QV) (LinearMap.mulLeft F
        (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
          (ι d.QW (e 0) * ι d.QW (e 1)) * b)) /
      ((-(d.QW (e 0) * d.QW (e 1))) * (Module.finrank F (CliffordAlgebra d.QV) : F))) •
      (ι d.QW (e 0) * ι d.QW (e 1))

theorem planeCoord_mem_evenOdd_zero (b : CliffordAlgebra d.QV) :
    planeCoord e b ∈ evenOdd d.QW 0 :=
  add_mem (Submodule.smul_mem _ _ (SetLike.one_mem_graded _))
    (Submodule.smul_mem _ _ (ι_mul_ι_mem_evenOdd_zero _ _ _))

include he in
/-- **The traces pin the `GSpin(W)`-component**: for `a ∈ C⁺(W)` and `n ∈ N`,
`α(a n) = a` and `α(n a) = a`. -/
theorem planeCoord_map_inl_mul {a : CliffordAlgebra d.QW} (ha : a ∈ evenOdd d.QW 0)
    {n : GSpin d.QV} (hn : n ∈ d.N) :
    planeCoord e (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ) a *
        ((n : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) = a ∧
    planeCoord e (((n : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) *
        CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ) a) = a := by
  obtain ⟨s, t, rfl⟩ := exists_eq_smul_one_add_smul_of_even e he _ ha
  have hD := cast_finrank_cliffordAlgebra_ne_zero d.QV
  have hκ : -(d.QW (e 0) * d.QW (e 1)) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero
    (ne_zero_of_orthogonal_basis_fin_two d.nondeg e he 0)
    (ne_zero_of_orthogonal_basis_fin_two d.nondeg e he 1))
  set Cm := CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
  set ω := ι d.QW (e 0) * ι d.QW (e 1)
  set y := ((n : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)
  have hcomm : (s • (1 : CliffordAlgebra d.QW) + t • ω) * ω = ω * (s • 1 + t • ω) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have h1 : LinearMap.trace F _ (LinearMap.mulLeft F (Cm (s • 1 + t • ω) * y)) =
      s * (Module.finrank F (CliffordAlgebra d.QV) : F) := by
    rw [d.trace_map_inl_mul_N _ hn, trace_map_inl_planeElt e he]
  have h2 : LinearMap.trace F _ (LinearMap.mulLeft F (Cm ω * (Cm (s • 1 + t • ω) * y))) =
      t * (-(d.QW (e 0) * d.QW (e 1))) * (Module.finrank F (CliffordAlgebra d.QV) : F) := by
    rw [← mul_assoc, ← map_mul Cm, d.trace_map_inl_mul_N _ hn, trace_map_inl_planeω_mul e he]
  have h3 : LinearMap.trace F _ (LinearMap.mulLeft F (y * Cm (s • 1 + t • ω))) =
      s * (Module.finrank F (CliffordAlgebra d.QV) : F) := by
    rw [d.trace_N_mul_map_inl _ hn, trace_map_inl_planeElt e he]
  have h4 : LinearMap.trace F _ (LinearMap.mulLeft F (Cm ω * (y * Cm (s • 1 + t • ω)))) =
      t * (-(d.QW (e 0) * d.QW (e 1))) * (Module.finrank F (CliffordAlgebra d.QV) : F) := by
    rw [← mul_assoc, trace_mulLeft_comm, ← mul_assoc, ← map_mul Cm, hcomm,
      d.trace_map_inl_mul_N _ hn, trace_map_inl_planeω_mul e he]
  constructor
  · simp only [planeCoord]
    rw [h1, h2, mul_div_cancel_right₀ _ hD, mul_assoc t, mul_div_cancel_right₀ _ (mul_ne_zero hκ hD)]
  · simp only [planeCoord]
    rw [h3, h4, mul_div_cancel_right₀ _ hD, mul_assoc t, mul_div_cancel_right₀ _ (mul_ne_zero hκ hD)]

end Plane

/-- The conditions defining `N`, written for a pair `(y, y')` of elements of `C(V)` standing for
`(g, g⁻¹)`: conjugation `v ↦ y v y'` stabilizes the flag, is trivial on its graded pieces and on
`Z_rᗮ/Z_r`, and `y − 1` is nilpotent (`mem_N_iff_NCond`). -/
def NCond (y y' : CliffordAlgebra d.QV) : Prop :=
  (∀ i, ∀ v ∈ d.flag.sub i, y * ι d.QV v * y' ∈ (d.flag.sub i).map (ι d.QV)) ∧
  (∀ i : Fin d.flag.len, ∀ v ∈ d.flag.sub i.succ,
    y * ι d.QV v * y' - ι d.QV v ∈ (d.flag.sub i.castSucc).map (ι d.QV)) ∧
  (∀ v ∈ (bform d.QV).orthogonal d.flag.top,
    y * ι d.QV v * y' - ι d.QV v ∈ d.flag.top.map (ι d.QV)) ∧
  (y - 1) ^ Module.finrank F (CliffordAlgebra d.QV) = 0

/-- `x ∈ S ↔ ι(x) ∈ ι(S)`. -/
theorem mem_iff_ι_mem_map (x : d.V) (S : Submodule F d.V) :
    x ∈ S ↔ ι d.QV x ∈ S.map (ι d.QV) :=
  ⟨fun h => ⟨x, h, rfl⟩, fun ⟨_, hy, he⟩ => ι_injective d.QV he ▸ hy⟩

theorem mem_N_iff_NCond (g : GSpin d.QV) :
    g ∈ d.N ↔ d.NCond ((g : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)
      (((g : (CliffordAlgebra d.QV)ˣ)⁻¹ : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) := by
  have e1 : ∀ (v : d.V) (S : Submodule F d.V), specP d.QV g v ∈ S ↔ ((g : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) *
      ι d.QV v * (((g : (CliffordAlgebra d.QV)ˣ)⁻¹ : (CliffordAlgebra d.QV)ˣ) :
        CliffordAlgebra d.QV) ∈ S.map (ι d.QV) := fun v S => by
    rw [d.mem_iff_ι_mem_map, ι_specP]
  have e2 : ∀ (v : d.V) (S : Submodule F d.V), specP d.QV g v - v ∈ S ↔ ((g : (CliffordAlgebra d.QV)ˣ) :
      CliffordAlgebra d.QV) * ι d.QV v * (((g : (CliffordAlgebra d.QV)ˣ)⁻¹ :
        (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) - ι d.QV v ∈ S.map (ι d.QV) :=
    fun v S => by rw [d.mem_iff_ι_mem_map, map_sub, ι_specP]
  show g ∈ flagUnip d.flag ↔ _
  simp only [flagUnip, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq,
    mem_flagStab_iff, NCond, e1, e2, isNilpotent_iff_pow_finrank (K := F)]

/-- The `N`-conditions cut out a closed set. -/
theorem isClosed_setOf_NCond {X : Type*} [TopologicalSpace X] {f f' : X → CliffordAlgebra d.QV}
    (hf : Continuous f) (hf' : Continuous f') : IsClosed {x | d.NCond (f x) (f' x)} := by
  have hc : ∀ v, Continuous fun x => f x * ι d.QV v * f' x :=
    fun v => (hf.mul continuous_const).mul hf'
  have hS : ∀ S : Submodule F d.V, IsClosed (S.map (ι d.QV) : Set (CliffordAlgebra d.QV)) :=
    fun S => isClosed_submodule_of_moduleTopology _
  have h0 : IsClosed ({0} : Set (CliffordAlgebra d.QV)) := by
    simpa using isClosed_submodule_of_moduleTopology (⊥ : Submodule F (CliffordAlgebra d.QV))
  simp only [NCond, Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_iInter fun i => isClosed_iInter fun v => isClosed_iInter fun _ =>
    (hS _).preimage (hc v)).inter ((isClosed_iInter fun i => isClosed_iInter fun v =>
    isClosed_iInter fun _ => (hS _).preimage ((hc v).sub continuous_const)).inter
    ((isClosed_iInter fun v => isClosed_iInter fun _ =>
    (hS _).preimage ((hc v).sub continuous_const)).inter ?_))
  exact h0.preimage ((hf.sub continuous_const).pow _)

/-- **`GSpin(W) · N` is closed in `GSpin(V)` when `dim W = 2`** (own work).  `GSpin(W) = C⁺(W)^×`
lies in `K ⊕ K ω`, and for `b = a n` the component `a = s + t ω` is pinned by two traces,
`α(b) = tr(L_b)/D + tr(L_{ω b})/(κD) · ω` (`planeCoord_map_inl_mul`: `tr(L_{x n}) = tr(L_x)` for
`x ∈ C(W)`, `n ∈ N`, by the weight filtration).  So `b ∈ GSpin(W)·N` iff `α(b) α(b⁻¹) = 1 = α(b⁻¹) α(b)`
and `α(b)⁻¹ b ∈ N`, and these conditions are closed. -/
theorem isClosed_incl_range_mul_N_of_finrank_eq_two
    (hW : Module.finrank F (Fin d.m → F) = 2) :
    IsClosed ((d.incl.range : Set (GSpin d.QV)) * (d.N : Set (GSpin d.QV))) := by
  obtain ⟨e, he⟩ := exists_orthogonal_basis_fin_two d.QW hW
  set Cm := CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
  set bv : GSpin d.QV → CliffordAlgebra d.QV := fun b => ((b : (CliffordAlgebra d.QV)ˣ) :
    CliffordAlgebra d.QV)
  set bi : GSpin d.QV → CliffordAlgebra d.QV := fun b => (((b : (CliffordAlgebra d.QV)ˣ)⁻¹ :
    (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)
  have key : ((d.incl.range : Set (GSpin d.QV)) * (d.N : Set (GSpin d.QV))) =
      {b | planeCoord e (bv b) * planeCoord e (bi b) = 1} ∩
      ({b | planeCoord e (bi b) * planeCoord e (bv b) = 1} ∩
      {b | d.NCond (Cm (planeCoord e (bi b)) * bv b) (bi b * Cm (planeCoord e (bv b)))}) := by
    ext b
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, n, hn, rfl⟩
      have ha0 : ((a : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) ∈ evenOdd d.QW 0 := by
        have := a.2.1; rwa [← Subalgebra.mem_toSubmodule, even_toSubmodule] at this
      have hai0 : (((a : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) :
          CliffordAlgebra d.QW) ∈ evenOdd d.QW 0 := by
        have := (a⁻¹ : GSpin d.QW).2.1; rwa [← Subalgebra.mem_toSubmodule, even_toSubmodule] at this
      have hv : bv (d.incl a * n) = Cm ((a : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) *
          ((n : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) := rfl
      have hi : bi (d.incl a * n) = (((n : (CliffordAlgebra d.QV)ˣ)⁻¹ : (CliffordAlgebra d.QV)ˣ) :
          CliffordAlgebra d.QV) * Cm (((a : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) :
            CliffordAlgebra d.QW) := by
        simp only [bi, Subgroup.coe_mul, mul_inv_rev, Units.val_mul]
        rfl
      have hni : (n⁻¹ : GSpin d.QV) ∈ d.N := d.N.inv_mem hn
      have h1 : planeCoord e (bv (d.incl a * n)) = ((a : (CliffordAlgebra d.QW)ˣ) :
          CliffordAlgebra d.QW) := by
        rw [hv]; exact (planeCoord_map_inl_mul e he ha0 hn).1
      have h2 : planeCoord e (bi (d.incl a * n)) = (((a : (CliffordAlgebra d.QW)ˣ)⁻¹ :
          (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) := by
        rw [hi]; exact (planeCoord_map_inl_mul e he hai0 hni).2
      refine ⟨?_, ?_, ?_⟩
      · show planeCoord e (bv _) * planeCoord e (bi _) = 1
        rw [h1, h2, Units.mul_inv]
      · show planeCoord e (bi _) * planeCoord e (bv _) = 1
        rw [h1, h2, Units.inv_mul]
      · show d.NCond _ _
        rw [h1, h2, hv, hi, ← mul_assoc, ← map_mul Cm, Units.inv_mul, map_one, one_mul, mul_assoc,
          ← map_mul Cm, Units.inv_mul, map_one, mul_one]
        exact (d.mem_N_iff_NCond n).mp hn
    · rintro ⟨h1, h2, h3⟩
      set u : (CliffordAlgebra d.QW)ˣ := ⟨planeCoord e (bv b), planeCoord e (bi b), h1, h2⟩
      have hu : u ∈ GSpin d.QW := mem_GSpin_of_even_of_fin_two d.nondeg e he u
        (planeCoord_mem_evenOdd_zero e _) (planeCoord_mem_evenOdd_zero e _)
      set a : GSpin d.QW := ⟨u, hu⟩
      have e1 : ((((d.incl a)⁻¹ * b : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) :
          CliffordAlgebra d.QV) = Cm (planeCoord e (bi b)) * bv b := rfl
      have e2 : (((((d.incl a)⁻¹ * b : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ)⁻¹ :
          (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) = bi b * Cm (planeCoord e (bv b)) := by
        simp only [mul_inv_rev, Units.val_mul, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        rfl
      have hy : (d.incl a)⁻¹ * b ∈ d.N := by
        rw [d.mem_N_iff_NCond, e1, e2]; exact h3
      exact ⟨d.incl a, ⟨a, rfl⟩, _, hy, mul_inv_cancel_left _ _⟩
  rw [key]
  have hbv : Continuous bv := Units.continuous_val.comp continuous_subtype_val
  have hbi : Continuous bi := Units.continuous_coe_inv.comp continuous_subtype_val
  have hτ : Continuous fun x : CliffordAlgebra d.QV =>
      LinearMap.trace F (CliffordAlgebra d.QV) (LinearMap.mulLeft F x) :=
    IsModuleTopology.continuous_of_linearMap
      ((LinearMap.trace F (CliffordAlgebra d.QV)).comp (LinearMap.mul F (CliffordAlgebra d.QV)))
  have hα : Continuous (planeCoord e) := by
    have : ContinuousSMul F (CliffordAlgebra d.QW) := inferInstance
    have h2 : Continuous fun b : CliffordAlgebra d.QV =>
        LinearMap.trace F (CliffordAlgebra d.QV) (LinearMap.mulLeft F
          (Cm (ι d.QW (e 0) * ι d.QW (e 1)) * b)) := hτ.comp (continuous_const.mul continuous_id)
    unfold planeCoord
    fun_prop
  have hCm : Continuous Cm := IsModuleTopology.continuous_of_linearMap Cm.toLinearMap
  have h1 : ∀ f : GSpin d.QV → CliffordAlgebra d.QW, Continuous f → IsClosed {b | f b = 1} := by
    intro f hf
    have : T2Space (CliffordAlgebra d.QW) := IsTopologicalAddGroup.t2Space_iff_zero_closed.mpr
      (by simpa using isClosed_submodule_of_moduleTopology (⊥ : Submodule F (CliffordAlgebra d.QW)))
    exact isClosed_eq hf continuous_const
  exact (h1 _ ((hα.comp hbv).mul (hα.comp hbi))).inter ((h1 _ ((hα.comp hbi).mul (hα.comp hbv))).inter
    (d.isClosed_setOf_NCond ((hCm.comp (hα.comp hbi)).mul hbv)
      (hbi.mul (hCm.comp (hα.comp hbv)))))

end PlaneClosed

/-- `H·A_G = G` when `V` is a hyperbolic plane. -/
theorem H_mul_AG_eq_univ_of_isHypPlane (hV : IsHypPlane d.QV) :
    (d.H : Set ↥d.G) * (d.AG : Set ↥d.G) = Set.univ := by
  classical
  refine Set.eq_univ_of_forall fun g => ⟨d.diag (d.fst g), ?_, d.inr (d.nPart g), ?_, ?_⟩
  · show d.nPart (d.diag _) ∈ d.N
    rw [show d.nPart (d.diag (d.fst g)) = 1 from inv_mul_cancel _]
    exact d.N.one_mem
  · refine ⟨(1, d.nPart g), ⟨(splitCentralGSpin d.QW).one_mem, ?_⟩, rfl⟩
    unfold splitCentralGSpin
    simp only [hV, ↓reduceIte]
    trivial
  · apply d.G_ext
    · exact (map_mul d.fst _ _).trans (mul_one _)
    · exact (map_mul d.snd _ _).trans (mul_inv_cancel_left (d.incl (d.fst g)) (d.snd g))

/-- `H·A_G = {g | g_V ∈ incl(GSpin(W)) · N}` when `W` is a hyperbolic plane (and `V` is not, which
is automatic): then `A_G = GSpin(W) × K^×`. -/
theorem H_mul_AG_eq_of_isHypPlane (hW : IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) :
    (d.H : Set ↥d.G) * (d.AG : Set ↥d.G) =
      d.snd ⁻¹' ((d.incl.range : Set (GSpin d.QV)) * (d.N : Set (GSpin d.QV))) := by
  classical
  ext g
  simp only [Set.mem_preimage]
  constructor
  · rintro ⟨h, hh, a, ⟨p, ⟨-, hp2⟩, rfl⟩, rfl⟩
    have hp2' : p.2 ∈ (scalarGSpin d.QV).range := by
      unfold splitCentralGSpin at hp2; simp only [hV, ↓reduceIte] at hp2; exact hp2
    obtain ⟨c, hc⟩ := hp2'
    have hz : ∀ y, y * scalarGSpin d.QV c = scalarGSpin d.QV c * y :=
      Subgroup.mem_center_iff.mp (scalarGSpin_mem_center d.QV c)
    refine ⟨d.incl (d.fst h * scalarGSpin d.QW c), ⟨_, rfl⟩, d.nPart h, hh, ?_⟩
    refine Eq.trans ?_ (map_mul d.snd h (d.pair p)).symm
    rw [map_mul, incl_scalarGSpin, snd_pair, ← hc]
    exact mul_mul_inv_mul_of_central_aux hz _ _
  · rintro ⟨_, ⟨a', rfl⟩, n, hn, hgn⟩
    refine ⟨d.diag a' * d.inr n, ?_, d.pair (a'⁻¹ * d.fst g, 1), ⟨_, ⟨?_, ?_⟩, rfl⟩, ?_⟩
    · show d.nPart _ ∈ d.N
      have : d.nPart (d.diag a' * d.inr n) = n := by
        simp only [nPart, map_mul, fst_inr_eq_one, snd_inr, mul_one]
        exact inv_mul_cancel_left (d.incl a') n
      rw [this]; exact hn
    · unfold splitCentralGSpin; simp only [hW, ↓reduceIte]; trivial
    · exact (splitCentralGSpin d.QV).one_mem
    · apply d.G_ext
      · refine (map_mul d.fst _ _).trans ?_
        simp only [map_mul, fst_inr_eq_one, fst_pair, mul_one]
        exact mul_inv_cancel_left a' (d.fst g)
      · refine (map_mul d.snd _ _).trans ?_
        simp only [map_mul, snd_inr, snd_pair, mul_one]
        exact hgn

/-- The generic case of `isClosed_H_mul_AG`: `g ∈ H·A_G` iff `n(g) ∈ K^×·N` at the level of
`SO(V)` and `(D · n(g) − tr(L_{n(g)}))^D = 0` in `C(V)`, `D = dim C(V)`. -/
theorem isClosed_H_mul_AG_of_not_isHypPlane (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) :
    IsClosed ((d.H : Set ↥d.G) * (d.AG : Set ↥d.G)) := by
  have e : (d.H : Set ↥d.G) * (d.AG : Set ↥d.G) =
      {g | d.nPart g ∈ flagUnipSO d.flag} ∩ {g | ((Module.finrank F (CliffordAlgebra d.QV) : F) •
        (((d.nPart g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) -
        LinearMap.trace F (CliffordAlgebra d.QV) (Algebra.lmul F (CliffordAlgebra d.QV)
          (((d.nPart g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) •
          (1 : CliffordAlgebra d.QV)) ^ Module.finrank F (CliffordAlgebra d.QV) = 0} := by
    ext g
    constructor
    · intro hg
      obtain ⟨h1, t, ht⟩ := d.of_mem_H_mul_AG hW hV hg
      exact ⟨h1, (exists_smul_sub_one_isNilpotent_iff (Units.isUnit _)).mp ⟨t, ht⟩⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨t, ht⟩ := (exists_smul_sub_one_isNilpotent_iff (Units.isUnit _)).mpr h2
      exact d.mem_H_mul_AG_of h1 ht
  rw [e]
  have hnh : Continuous fun g : ↥d.G =>
      (((d.nPart g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) :=
    Units.continuous_val.comp d.continuous_nPart_coe
  have htr : Continuous fun x : CliffordAlgebra d.QV =>
      LinearMap.trace F (CliffordAlgebra d.QV) (Algebra.lmul F (CliffordAlgebra d.QV) x) :=
    IsModuleTopology.continuous_of_linearMap
      ((LinearMap.trace F (CliffordAlgebra d.QV)).comp
        (Algebra.lmul F (CliffordAlgebra d.QV)).toLinearMap)
  have h0 : IsClosed ({0} : Set (CliffordAlgebra d.QV)) := by
    simpa using isClosed_submodule_of_moduleTopology (⊥ : Submodule F (CliffordAlgebra d.QV))
  refine ((isClosed_flagUnipSO d.flag).preimage d.continuous_nPart_GSpin).inter
    (h0.preimage ?_)
  exact (((continuous_const (y := ((Module.finrank F (CliffordAlgebra d.QV) : ℕ) : F))).smul hnh).sub
    ((htr.comp hnh).smul (continuous_const (y := (1 : CliffordAlgebra d.QV))))).pow _

/-- `H(F) · A_G(F)` is closed in `G(F)`.  Needed for `H(F)\G(F)/A_G(F)` to be a reasonable
(Hausdorff, locally compact) homogeneous space and for `toGmodAG` to be a closed embedding.
Not stated in the thesis (which works with `H(F)\G(F)/A_G(F)` directly).

Proof (own work), by cases on `A_G` (`splitCentralGSpin`):
* `V` a hyperbolic plane: `A_G ⊇ 1 × GSpin(V)`, so `H·A_G = G` (`H_mul_AG_eq_univ_of_isHypPlane`);
* `W` a hyperbolic plane: `H·A_G = {g | g_V ∈ incl(GSpin(W)) · N}` (`H_mul_AG_eq_of_isHypPlane`),
  closed because `dim W = 2` (`isClosed_incl_range_mul_N_of_finrank_eq_two`: the `GSpin(W)`-component
  is pinned by two traces);
* otherwise `A_G = F^× × F^×`, and `g ∈ H·A_G` iff `n(g) = g_W⁻¹g_V` lies in `F^× · N` at the level
  of `SO(V)` and `t · n(g) − 1` is nilpotent for some `t ∈ F`; unipotence pins `t` by a trace
  (`exists_smul_sub_one_isNilpotent_iff`), which makes both conditions closed
  (`isClosed_H_mul_AG_of_not_isHypPlane`). -/
theorem isClosed_H_mul_AG : IsClosed ((d.H : Set ↥d.G) * (d.AG : Set ↥d.G)) := by
  by_cases hV : IsHypPlane d.QV
  · rw [d.H_mul_AG_eq_univ_of_isHypPlane hV]
    exact isClosed_univ
  by_cases hW : IsHypPlane d.QW
  · rw [d.H_mul_AG_eq_of_isHypPlane hW hV]
    exact (d.isClosed_incl_range_mul_N_of_finrank_eq_two hW.1).preimage d.continuous_snd
  · exact d.isClosed_H_mul_AG_of_not_isHypPlane hW hV

/-- `toGmodAG : H(F)/A_{G,H}(F) → G(F)/A_G(F)` is a closed embedding, from
`AG_inf_H` (injectivity), `isClosed_H_mul_AG` (closed range) and the open mapping theorem
(`QuotientGroup.isClosedEmbedding_map_of_isClosed_mul`). -/
theorem isClosedEmbedding_toGmodAG : IsClosedEmbedding d.toGmodAG := by
  have hN : d.AGHinH = d.AG.subgroupOf d.H := by
    ext h
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hh
      exact d.AGH_le_AG hh
    · intro hh
      rw [← d.AG_inf_H]
      exact ⟨hh, h.2⟩
  exact QuotientGroup.isClosedEmbedding_map_of_isClosed_mul d.AGHinH hN d.AGHinH_le_comap_AG
    d.isClosed_H_mul_AG

/-- The coset space `H(F)\G(F)/A_G(F)` (Thesis §7.1), realised as the right cosets of
the image of `H(F)/A_{G,H}(F)` in `G(F)/A_G(F)`. -/
abbrev HGQuot : Type _ := CosetSpace d.toGmodAG

end GGPData

/-! ### Right invariance of Haar measure on `H(F)/A_{G,H}(F)` -/

section HaarRightInvariance

/-- **Binomial expansion of a unipotent power** (`X` nilpotent, so `X^D = 0` for `D = dim A`):
`(1 + X)^k = Σ_{j < D} C(k, j) X^j`. -/
theorem one_add_pow_eq_sum_fin {K A : Type*} [Field K] [Ring A] [Algebra K A]
    [FiniteDimensional K A] {X : A} (hX : IsNilpotent X) (k : ℕ) :
    (1 + X) ^ k = ∑ j : Fin (Module.finrank K A), ((k.choose j : ℕ) : K) • X ^ (j : ℕ) := by
  have hD : X ^ Module.finrank K A = 0 := (isNilpotent_iff_pow_finrank (K := K) X).mp hX
  set D := Module.finrank K A
  rw [add_comm, (Commute.one_right X).add_pow, Finset.sum_range (fun j => ((k.choose j : ℕ) : K) •
    X ^ j) |>.symm]
  have e1 : ∀ m, X ^ m * 1 ^ (k - m) * (k.choose m : A) = ((k.choose m : ℕ) : K) • X ^ m := by
    intro m
    rw [one_pow, mul_one, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, Nat.cast_comm]
  simp_rw [e1]
  have hsub1 : Finset.range (k + 1) ⊆ Finset.range (k + 1 + D) :=
    Finset.range_subset_range.mpr (by omega)
  have hsub2 : Finset.range D ⊆ Finset.range (k + 1 + D) :=
    Finset.range_subset_range.mpr (by omega)
  rw [Finset.sum_subset hsub1 ?_, Finset.sum_subset hsub2 ?_]
  · intro m _ hm
    rw [Finset.mem_range, not_lt] at hm
    rw [pow_eq_zero_of_le hm hD, smul_zero]
  · intro m _ hm
    rw [Finset.mem_range, not_lt] at hm
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_smul]

/-- **Powers of a unipotent element are bounded** (`p`-adic `K`).  If `u ∈ A^×` and `u − 1` is
nilpotent, all powers `u^k`, `k ∈ ℤ`, lie in one compact subset of `A^×`: by the binomial
expansion, `u^k` and `u^{-k}` (`k ≥ 0`) are `Σ_{j<D} c_j X^j` with `X = u − 1` resp. `u⁻¹ − 1` and
integer coefficients `c_j`, which have norm `≤ 1` (ultrametric). -/
theorem exists_isCompact_zpow_of_isNilpotent {K A : Type*} [NontriviallyNormedField K]
    [ProperSpace K] [IsUltrametricDist K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul K A] [T1Space A] (u : Aˣ)
    (hu : IsNilpotent ((u : A) - 1)) :
    ∃ C : Set Aˣ, IsCompact C ∧ ∀ k : ℤ, u ^ k ∈ C := by
  set D := Module.finrank K A
  let B : Set (Fin D → K) := Set.pi Set.univ fun _ => Metric.closedBall (0 : K) 1
  have hB : IsCompact B := isCompact_univ_pi fun _ => isCompact_closedBall _ _
  let Φ : A → (Fin D → K) → A := fun X c => ∑ j : Fin D, c j • X ^ (j : ℕ)
  have hΦ : ∀ X, Continuous (Φ X) := fun X =>
    continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const
  have hmem : ∀ X : A, IsNilpotent X → ∀ k : ℕ, (1 + X) ^ k ∈ Φ X '' B := by
    intro X hX k
    refine ⟨fun j => ((k.choose j : ℕ) : K), fun j _ => ?_, (one_add_pow_eq_sum_fin hX k).symm⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact IsUltrametricDist.norm_natCast_le_one K _
  have hu' : IsNilpotent (((u⁻¹ : Aˣ) : A) - 1) := by
    have e : ((u⁻¹ : Aˣ) : A) - 1 = -(((u⁻¹ : Aˣ) : A) * ((u : A) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [e]
    refine (Commute.isNilpotent_mul_left ?_ hu).neg
    show ((u⁻¹ : Aˣ) : A) * ((u : A) - 1) = ((u : A) - 1) * ((u⁻¹ : Aˣ) : A)
    rw [mul_sub, sub_mul, Units.inv_mul, Units.mul_inv, mul_one, one_mul]
  set S : Set A := Φ ((u : A) - 1) '' B ∪ Φ (((u⁻¹ : Aˣ) : A) - 1) '' B
  have hS : IsCompact S := (hB.image (hΦ _)).union (hB.image (hΦ _))
  have hpos : ∀ v : Aˣ, IsNilpotent ((v : A) - 1) → ∀ k : ℕ, ((v ^ k : Aˣ) : A) ∈
      Φ ((v : A) - 1) '' B := by
    intro v hv k
    have := hmem _ hv k
    rwa [add_sub_cancel] at this
  refine ⟨Units.embedProduct A ⁻¹' (S ×ˢ (MulOpposite.op '' S)),
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hS.prod (hS.image MulOpposite.continuous_op)), fun k => ?_⟩
  simp only [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image]
  rcases Int.eq_nat_or_neg k with ⟨k, rfl | rfl⟩
  · refine ⟨Or.inl (by simpa using hpos u hu k), ?_⟩
    refine ⟨_, Or.inr (by simpa [← inv_pow] using hpos u⁻¹ hu' k), rfl⟩
  · refine ⟨Or.inr (by simpa [← inv_pow] using hpos u⁻¹ hu' k), ?_⟩
    refine ⟨_, Or.inl (by simpa using hpos u hu k), ?_⟩
    simp

/-- **Right translation by an element of a compact subgroup preserves Haar measure** (the modular
character is trivial on compact subgroups).  Proof: `map (· * g) μ = c • μ`, and with `U` a compact
neighbourhood of `1`, the set `E = U·K` satisfies `E g⁻¹ = E` and `0 < μ E < ∞`, so `c = 1`. -/
theorem map_mul_right_haar_of_mem_compact {Q : Type*} [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q]
    [MeasurableSpace Q] [BorelSpace Q] (Kc : Subgroup Q) (hK : IsCompact (Kc : Set Q)) {g : Q}
    (hg : g ∈ Kc) : Measure.map (· * g) (Measure.haar : Measure Q) = Measure.haar := by
  set μ : Measure Q := Measure.haar
  have hfac := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ
  obtain ⟨U, hUc, hU1⟩ := exists_compact_mem_nhds (1 : Q)
  set E : Set Q := U * (Kc : Set Q)
  have hEc : IsCompact E := hUc.mul hK
  have hpre : (· * g) ⁻¹' E = E := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · rintro ⟨u, hu, k, hk, he⟩
      refine ⟨u, hu, k * g⁻¹, Kc.mul_mem hk (Kc.inv_mem hg), ?_⟩
      dsimp only at he ⊢
      rw [← mul_assoc, he, mul_inv_cancel_right]
    · rintro ⟨u, hu, k, hk, rfl⟩
      exact ⟨u, hu, k * g, Kc.mul_mem hk hg, (mul_assoc _ _ _).symm⟩
  have hpos : μ E ≠ 0 := (Measure.measure_pos_of_mem_nhds μ (Filter.mem_of_superset hU1
    (Set.subset_mul_left U Kc.one_mem))).ne'
  have hfin : μ E ≠ ⊤ := hEc.measure_lt_top.ne
  have h1 : Measure.map (· * g) μ E = μ E := by
    rw [Measure.map_apply (measurable_mul_const g) hEc.isClosed.measurableSet, hpre]
  have hc : Measure.haarScalarFactor (Measure.map (· * g) μ) μ = 1 := by
    rw [hfac, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    have h2 : ((Measure.haarScalarFactor (Measure.map (· * g) μ) μ : NNReal) : ENNReal) * μ E =
        1 * μ E := by rw [one_mul]; exact h1
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).mp h2
  rw [hfac, hc, one_smul]

/-- Variant of `map_mul_right_haar_of_mem_compact`: if all powers `q^k`, `k ∈ ℤ`, lie in a compact
set, right translation by `q` preserves Haar measure (the closure of `⟨q⟩` is a compact subgroup). -/
theorem map_mul_right_haar_of_zpow_mem_compact {Q : Type*} [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q]
    [MeasurableSpace Q] [BorelSpace Q] {q : Q} {C : Set Q} (hC : IsCompact C)
    (hq : ∀ k : ℤ, q ^ k ∈ C) : Measure.map (· * q) (Measure.haar : Measure Q) = Measure.haar := by
  refine map_mul_right_haar_of_mem_compact (Subgroup.zpowers q).topologicalClosure
    (hC.of_isClosed_subset isClosed_closure (closure_minimal ?_ hC.isClosed))
    (Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers q))
  rintro _ ⟨k, rfl⟩
  exact hq k

/-- Right translations preserving a measure are closed under products. -/
theorem map_mul_right_mul_eq {Q : Type*} [Group Q] [MeasurableSpace Q] [MeasurableMul Q]
    {μ : Measure Q} {a b : Q} (ha : Measure.map (· * a) μ = μ) (hb : Measure.map (· * b) μ = μ) :
    Measure.map (· * (a * b)) μ = μ := by
  have e : (fun x : Q => x * (a * b)) = (fun x => x * b) ∘ (fun x => x * a) := by
    funext x; simp [mul_assoc]
  rw [e, ← Measure.map_map (measurable_mul_const b) (measurable_mul_const a), ha, hb]


section ModularInvolution

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
  [T2Space Q] [SecondCountableTopology Q] [MeasurableSpace Q] [BorelSpace Q]

/-- Right translation by `q` preserves Haar measure iff `Δ(q) = 1`. -/
theorem map_mul_right_haar_eq_self_of_modularCharacter_eq_one {q : Q}
    (hq : Measure.modularCharacter q = 1) :
    Measure.map (· * q) (Measure.haar : Measure Q) = Measure.haar := by
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul, show Measure.modularCharacterFun q = 1 from hq,
    one_smul]

/-- The modular character is invariant under a continuous involutive automorphism `σ`
(`σ ∘ σ = id`): `σ` carries Haar measure to a Haar measure. -/
theorem modularCharacter_apply_of_involutive (σ : Q →* Q) (hσ : Continuous σ)
    (hinv : ∀ q, σ (σ q) = q) (q : Q) :
    Measure.modularCharacter (σ q) = Measure.modularCharacter q := by
  let e : Q ≃ₜ* Q :=
    { toFun := σ, invFun := σ, left_inv := hinv, right_inv := hinv, map_mul' := σ.map_mul,
      continuous_toFun := hσ, continuous_invFun := hσ }
  set μ : Measure Q := Measure.haar
  set ν : Measure Q := Measure.map e μ
  have : ν.IsHaarMeasure := e.isHaarMeasure_map μ
  have hmeas : Measurable e := e.continuous.measurable
  have h1 : Measure.map (· * σ q) ν = Measure.map e (Measure.map (· * q) μ) := by
    rw [Measure.map_map (measurable_mul_const _) hmeas,
      Measure.map_map hmeas (measurable_mul_const _)]
    congr 1
    funext x
    exact (σ.map_mul x q).symm
  have h2 : Measure.map (· * σ q) ν = Measure.modularCharacter q • ν := by
    rw [h1, Measure.map_right_mul_eq_modularCharacterFun_smul, Measure.map_smul _ hmeas.aemeasurable]
    rfl
  have h3 : Measure.haarScalarFactor (Measure.map (· * σ q) ν) ν =
      Measure.haarScalarFactor (Measure.modularCharacter q • ν) ν := by
    congr 1
  show Measure.modularCharacterFun (σ q) = Measure.modularCharacterFun q
  rw [Measure.modularCharacterFun_eq_haarScalarFactor ν, h3, Measure.haarScalarFactor_smul,
    Measure.haarScalarFactor_self, smul_eq_mul, mul_one]
  rfl

/-- If a continuous involutive automorphism maps `q` to `q⁻¹`, then `Δ(q) = 1`. -/
theorem modularCharacter_eq_one_of_involutive_inv (σ : Q →* Q) (hσ : Continuous σ)
    (hinv : ∀ q, σ (σ q) = q) {q : Q} (hq : σ q = q⁻¹) : Measure.modularCharacter q = 1 := by
  have h := modularCharacter_apply_of_involutive σ hσ hinv q
  rw [hq, map_inv] at h
  have h2 : Measure.modularCharacter q * Measure.modularCharacter q = 1 := by
    conv_lhs => arg 1; rw [← h]
    exact inv_mul_cancel₀ (Measure.modularCharacterFun_pos q).ne'
  have h3 : Measure.modularCharacter q ^ 2 = 1 := by rw [sq]; exact h2
  exact (pow_eq_one_iff_of_nonneg bot_le two_ne_zero).mp h3

end ModularInvolution

/-- `φ(s x⁻¹) = φ(x)⁻¹` when `φ(s) = 1` (abstract; avoids unfolding concrete quotient towers). -/
theorem map_mul_inv_of_map_eq_one {A B : Type*} [Group A] [Group B] (φ : A →* B) {s : A}
    (hs : φ s = 1) (x : A) : φ (s * x⁻¹) = (φ x)⁻¹ := by
  rw [map_mul, hs, one_mul, map_inv]

section ConjVector

variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]

open CliffordAlgebra

/-- An anisotropic vector `w` as a unit of `C(V)` (`w⁻¹ = q(w)⁻¹ w`). -/
def ιUnit (Q : QuadraticForm K V) {w : V} (hw : Q w ≠ 0) : (CliffordAlgebra Q)ˣ where
  val := ι Q w
  inv := (Q w)⁻¹ • ι Q w
  val_inv := by
    rw [mul_smul_comm, ι_sq_scalar, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hw, map_one]
  inv_val := by
    rw [smul_mul_assoc, ι_sq_scalar, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hw, map_one]

theorem coe_ιUnit (Q : QuadraticForm K V) {w : V} (hw : Q w ≠ 0) :
    ((ιUnit Q hw : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = ι Q w := rfl

theorem coe_ιUnit_inv (Q : QuadraticForm K V) {w : V} (hw : Q w ≠ 0) :
    (((ιUnit Q hw)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = (Q w)⁻¹ • ι Q w := rfl

/-- `w v w⁻¹` is a vector. -/
theorem ιUnit_conj_ι {Q : QuadraticForm K V} {w : V} (hw : Q w ≠ 0) (v : V) :
    ((ιUnit Q hw : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q v *
      (((ιUnit Q hw)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      ι Q ((Q w)⁻¹ • (QuadraticMap.polar Q w v • w - Q w • v)) := by
  rw [coe_ιUnit, coe_ιUnit_inv, mul_smul_comm, ι_mul_ι_mul_ι, map_smul]

/-- `w⁻¹ v w` is a vector. -/
theorem ιUnit_inv_conj_ι {Q : QuadraticForm K V} {w : V} (hw : Q w ≠ 0) (v : V) :
    (((ιUnit Q hw)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q v *
      ((ιUnit Q hw : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      ι Q ((Q w)⁻¹ • (QuadraticMap.polar Q w v • w - Q w • v)) := by
  rw [coe_ιUnit, coe_ιUnit_inv, smul_mul_assoc, smul_mul_assoc, ι_mul_ι_mul_ι, map_smul]

/-- For `v ⊥ w`: `w v w⁻¹ = −v`. -/
theorem ιUnit_conj_ι_of_polar_eq_zero {Q : QuadraticForm K V} {w : V} (hw : Q w ≠ 0) {v : V}
    (hv : QuadraticMap.polar Q w v = 0) :
    ((ιUnit Q hw : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q v *
      (((ιUnit Q hw)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = -ι Q v := by
  rw [ιUnit_conj_ι, hv, zero_smul, zero_sub, smul_neg, smul_smul, inv_mul_cancel₀ hw, one_smul,
    map_neg]

/-- Conjugation by an anisotropic vector preserves `GSpin(V)` (it acts on `V` by `−s_w`). -/
theorem conj_ιUnit_mem_GSpin {Q : QuadraticForm K V} {w : V} (hw : Q w ≠ 0)
    {g : (CliffordAlgebra Q)ˣ} (hg : g ∈ GSpin Q) :
    ιUnit Q hw * g * (ιUnit Q hw)⁻¹ ∈ GSpin Q := by
  obtain ⟨hg0, hg1, hg2⟩ := hg
  set c := ιUnit Q hw
  have hc1 : ∀ v, (c : CliffordAlgebra Q) * ι Q v * ((c⁻¹ : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q) ∈ LinearMap.range (ι Q) := fun v => ⟨_, (ιUnit_conj_ι hw v).symm⟩
  have hc2 : ∀ v, ((c⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q v *
      (c : CliffordAlgebra Q) ∈ LinearMap.range (ι Q) := fun v => ⟨_, (ιUnit_inv_conj_ι hw v).symm⟩
  -- conjugating a vector successively by `a`, `b`, `c`
  have three : ∀ a b : (CliffordAlgebra Q)ˣ,
      (∀ v, (a : CliffordAlgebra Q) * ι Q v * ((a⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
        LinearMap.range (ι Q)) →
      (∀ v, (b : CliffordAlgebra Q) * ι Q v * ((b⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
        LinearMap.range (ι Q)) →
      ∀ v, ((a * b : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q v *
        (((a * b)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ LinearMap.range (ι Q) := by
    intro a b ha hb v
    obtain ⟨v1, hv1⟩ := hb v
    rw [mul_inv_rev, Units.val_mul, Units.val_mul,
      show (a : CliffordAlgebra Q) * b * ι Q v * (((b⁻¹ : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q) * ((a⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) =
        a * (b * ι Q v * ((b⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) *
          ((a⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) by simp only [mul_assoc], ← hv1]
    exact ha v1
  have hgc1 : ∀ v, ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q v *
      ((g⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ LinearMap.range (ι Q) := hg1
  have hgc2 : ∀ v, ((g⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q v *
      (((g⁻¹)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ LinearMap.range (ι Q) := by
    simpa using hg2
  have hci : ∀ v, ((c⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q v *
      (((c⁻¹)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ LinearMap.range (ι Q) := by
    simpa using hc2
  refine ⟨?_, three _ _ (three _ _ hc1 hgc1) hci, ?_⟩
  · rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at hg0 ⊢
    have := SetLike.mul_mem_graded (SetLike.mul_mem_graded (ι_mem_evenOdd_one Q w) hg0)
      (Submodule.smul_mem _ (Q w)⁻¹ (ι_mem_evenOdd_one Q w))
    rw [show (1 : ZMod 2) + 0 + 1 = 0 from rfl] at this
    exact this
  · intro v
    have e : ((c * g * c⁻¹)⁻¹ : (CliffordAlgebra Q)ˣ) = c * g⁻¹ * c⁻¹ := by group
    rw [e, show ((c * g * c⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      (((c * g⁻¹ * c⁻¹)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) by congr 1; group]
    exact three _ _ (three _ _ hc1 hgc2) hci v

/-- Conjugation by an anisotropic vector, as an endomorphism of `GSpin(V)`. -/
def conjιGSpin (Q : QuadraticForm K V) {w : V} (hw : Q w ≠ 0) : GSpin Q →* GSpin Q :=
  ((MulAut.conj (ιUnit Q hw)).toMonoidHom.comp (GSpin Q).subtype).codRestrict (GSpin Q)
    fun g => conj_ιUnit_mem_GSpin hw g.2

theorem coe_conjιGSpin {Q : QuadraticForm K V} {w : V} (hw : Q w ≠ 0) (g : GSpin Q) :
    (((conjιGSpin Q hw g : GSpin Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      ι Q w * ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ((Q w)⁻¹ • ι Q w) := rfl

/-- `conjιGSpin` is an involution (`w² = q(w)` is central). -/
theorem conjιGSpin_conjιGSpin {Q : QuadraticForm K V} {w : V} (hw : Q w ≠ 0) (g : GSpin Q) :
    conjιGSpin Q hw (conjιGSpin Q hw g) = g := by
  apply Subtype.ext; apply Units.ext
  rw [coe_conjιGSpin, coe_conjιGSpin]
  have e : ι Q w * (ι Q w * ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ((Q w)⁻¹ • ι Q w)) *
      ((Q w)⁻¹ • ι Q w) = ((Q w)⁻¹ * (Q w)⁻¹) • ((ι Q w * ι Q w) *
        ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * (ι Q w * ι Q w)) := by
    simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
  rw [e, ι_sq_scalar, ← Algebra.commutes, ← mul_assoc,
    ← map_mul (algebraMap K (CliffordAlgebra Q)), ← Algebra.smul_def, smul_smul,
    show (Q w)⁻¹ * (Q w)⁻¹ * (Q w * Q w) = 1 by field_simp, one_smul]

/-- Scalars are fixed by `conjιGSpin`. -/
theorem conjιGSpin_scalarGSpin {Q : QuadraticForm K V} {w : V} (hw : Q w ≠ 0) (c : Kˣ) :
    conjιGSpin Q hw (scalarGSpin Q c) = scalarGSpin Q c := by
  apply Subtype.ext; apply Units.ext
  rw [coe_conjιGSpin]
  show ι Q w * algebraMap K _ (c : K) * ((Q w)⁻¹ • ι Q w) = algebraMap K _ (c : K)
  rw [← Algebra.commutes, mul_assoc, mul_smul_comm, ι_sq_scalar, Algebra.smul_def, ← map_mul,
    ← map_mul, inv_mul_cancel₀ hw, mul_one]

/-- **`w` inverts `uw` up to a scalar**: `w (u w) w⁻¹ = w u = q(u) q(w) (u w)⁻¹`. -/
theorem conjιGSpin_gspinPair {Q : QuadraticForm K V} {u w : V} (hu : Q u ≠ 0) (hw : Q w ≠ 0) :
    conjιGSpin Q hw (gspinPair Q hu hw) =
      scalarGSpin Q (Units.mk0 (Q u * Q w) (mul_ne_zero hu hw)) * (gspinPair Q hu hw)⁻¹ := by
  apply Subtype.ext; apply Units.ext
  rw [coe_conjιGSpin, coe_gspinPair]
  show _ = algebraMap K _ (Q u * Q w) * ((Q u * Q w)⁻¹ • (ι Q w * ι Q u))
  rw [mul_smul_comm, mul_smul_comm, ← Algebra.smul_def, smul_smul,
    inv_mul_cancel₀ (mul_ne_zero hu hw), one_smul, show ι Q w * (ι Q u * ι Q w) * ι Q w = ι Q w * ι Q u * (ι Q w * ι Q w) by
      simp only [mul_assoc], ι_sq_scalar, ← Algebra.commutes, ← Algebra.smul_def, smul_smul,
    inv_mul_cancel₀ hw, one_smul]

/-- **Cartan–Dieudonné for `GSpin`.**  For nondegenerate finite-dimensional `V`, `GSpin(V)` is
generated by the scalars and the products `u w` of two anisotropic vectors: `P(g) ∈ SO(V)` is a
product `∏ s_{uᵢ} s_{wᵢ}` of an even number of reflections (`cartan_dieudonne_even`, E. Artin,
*Geometric Algebra*, Thm. 3.20), `P(uᵢ wᵢ) = s_{uᵢ} s_{wᵢ}` (`specP_gspinPair`), so `g (∏ uᵢ wᵢ)⁻¹`
lies in `ker P = K^×` (`ker_specP`). -/
theorem closure_scalarGSpin_gspinPair [Module.Finite K V] {Q : QuadraticForm K V}
    (hQ : IsNondeg Q) :
    Subgroup.closure (Set.range (scalarGSpin Q) ∪
      {g | ∃ (u w : V) (hu : Q u ≠ 0) (hw : Q w ≠ 0), gspinPair Q hu hw = g}) = ⊤ := by
  set S := Set.range (scalarGSpin Q) ∪
      {g | ∃ (u w : V) (hu : Q u ≠ 0) (hw : Q w ≠ 0), gspinPair Q hu hw = g}
  rw [eq_top_iff]
  intro g _
  obtain ⟨l, hl, hgl⟩ := cartan_dieudonne_even Q hQ (specP Q g) (specP_isometry g)
    (det_specP g)
  have key : ∀ l : List (V × V), (∀ p ∈ l, Q p.1 ≠ 0 ∧ Q p.2 ≠ 0) →
      ∃ x ∈ Subgroup.closure S, (specP Q x : V →ₗ[K] V) =
        (l.map fun p => quadReflection Q p.1 * quadReflection Q p.2).prod := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨1, Subgroup.one_mem _, by simp; rfl⟩
    | cons p l ih =>
      intro h
      obtain ⟨x, hxS, hx⟩ := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
      obtain ⟨h1, h2⟩ := h p List.mem_cons_self
      refine ⟨gspinPair Q h1 h2 * x, Subgroup.mul_mem _
        (Subgroup.subset_closure (Or.inr ⟨p.1, p.2, h1, h2, rfl⟩)) hxS, ?_⟩
      rw [List.map_cons, List.prod_cons, ← hx, ← specP_gspinPair Q h1 h2, map_mul]
      rfl
  obtain ⟨x, hxS, hx⟩ := key l hl
  have hPx : specP Q x = specP Q g :=
    LinearEquiv.toLinearMap_injective (hx.trans hgl.symm)
  have hker : g * x⁻¹ ∈ (specP Q).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hPx, mul_inv_cancel]
  rw [ker_specP hQ] at hker
  obtain ⟨c, hc⟩ := hker
  have hg : g = scalarGSpin Q c * x := by rw [hc, inv_mul_cancel_right]
  rw [hg]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)) hxS

end ConjVector

end HaarRightInvariance

namespace GGPData

variable (d : GGPData F)

/-- `y ↦ (1, y)`, `GSpin(V) → G`, is continuous. -/
theorem continuous_inr : Continuous d.inr := by
  apply continuous_induced_rng.2
  rw [Units.continuous_iff]
  constructor
  · exact continuous_const.prodMk (Units.continuous_val.comp continuous_subtype_val)
  · exact continuous_const.prodMk (Units.continuous_coe_inv.comp continuous_subtype_val)

/-- `(1, n) ∈ H` for `n ∈ N`. -/
theorem inr_mem_H {n : GSpin d.QV} (hn : n ∈ d.N) : d.inr n ∈ d.H := by
  show d.nPart (d.inr n) ∈ d.N
  have e : d.nPart (d.inr n) = n := by
    show (d.incl 1)⁻¹ * n = n
    rw [map_one, inv_one, one_mul]
  rw [e]; exact hn

/-- `(a, a) ∈ H`. -/
theorem diag_mem_H (a : GSpin d.QW) : d.diag a ∈ d.H := by
  show d.nPart (d.diag a) ∈ d.N
  rw [show d.nPart (d.diag a) = 1 from inv_mul_cancel _]
  exact d.N.one_mem

/-- If all powers of `h ∈ H(F)` lie in a compact set, right translation by its image preserves the
Haar measure of `H(F)/A_{G,H}(F)`. -/
theorem map_mul_mk_haar_HmodAGH_of_zpow {h : ↥d.H} {C : Set ↥d.H} (hC : IsCompact C)
    (hk : ∀ k : ℤ, h ^ k ∈ C) :
    Measure.map (· * (QuotientGroup.mk h : d.HmodAGH)) Measure.haar = Measure.haar :=
  map_mul_right_haar_of_zpow_mem_compact (hC.image QuotientGroup.continuous_mk)
    fun k => ⟨_, hk k, (QuotientGroup.mk_zpow _ _ _).symm⟩

/-- **Unimodularity of `H(F)/A_{G,H}(F)`, the unipotent half**: right translation by (the image of) `(1, n)`, `n ∈ N`, preserves
the Haar measure of `H(F)/A_{G,H}(F)`.  The powers of `n` stay in a compact set
(`exists_isCompact_zpow_of_isNilpotent`: `n − 1` is nilpotent and `F` is non-archimedean), so the
closure of the cyclic group they generate in `H/A_{G,H}` is a compact subgroup
(`map_mul_right_haar_of_mem_compact`). -/
theorem map_mul_inr_haar_HmodAGH {n : GSpin d.QV} (hn : n ∈ d.N) :
    Measure.map (· * (QuotientGroup.mk ⟨d.inr n, d.inr_mem_H hn⟩ : d.HmodAGH)) Measure.haar =
      Measure.haar := by
  obtain ⟨C, hC, hCn⟩ : ∃ C : Set (CliffordAlgebra d.QV)ˣ, IsCompact C ∧
      ∀ k : ℤ, ((n : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) ^ k ∈ C := by
    have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
    have : T2Space (CliffordAlgebra d.QV) := IsTopologicalAddGroup.t2Space_iff_zero_closed.mpr
      (by simpa using isClosed_submodule_of_moduleTopology (⊥ : Submodule F (CliffordAlgebra d.QV)))
    exact exists_isCompact_zpow_of_isNilpotent (K := F) _ hn.2.2.2
  -- a compact subset of `H/A_{G,H}` containing all powers of the image of `(1, n)`
  have hCV : IsCompact (Subtype.val ⁻¹' C : Set (GSpin d.QV)) :=
    (isClosed_GSpin d.QV).isClosedEmbedding_subtypeVal.isCompact_preimage hC
  have hCH : IsCompact (Subtype.val ⁻¹' (d.inr '' (Subtype.val ⁻¹' C)) : Set ↥d.H) :=
    d.isClosed_H_in_G.isClosedEmbedding_subtypeVal.isCompact_preimage (hCV.image d.continuous_inr)
  refine d.map_mul_mk_haar_HmodAGH_of_zpow hCH fun k => ?_
  refine ⟨n ^ k, ?_, ?_⟩
  · show ((n ^ k : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) ∈ C
    rw [Subgroup.coe_zpow]; exact hCn k
  · exact (map_zpow d.inr n k).trans (Subgroup.coe_zpow d.H ⟨d.inr n, d.inr_mem_H hn⟩ k).symm

section LeviInvolution

open CliffordAlgebra

/-- `GSpin(W) × GSpin(V) → G` is continuous. -/
theorem continuous_pair : Continuous d.pair := by
  apply continuous_induced_rng.2
  rw [Units.continuous_iff]
  constructor
  · exact (Units.continuous_val.comp (continuous_subtype_val.comp _root_.continuous_fst)).prodMk
      (Units.continuous_val.comp (continuous_subtype_val.comp _root_.continuous_snd))
  · exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp _root_.continuous_fst)).prodMk
      (Units.continuous_coe_inv.comp (continuous_subtype_val.comp _root_.continuous_snd))

theorem continuous_conjιGSpin {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    {Q : QuadraticForm F V} {w : V} (hw : Q w ≠ 0) : Continuous (conjιGSpin Q hw) :=
  continuous_induced_rng.2 ((continuous_const.mul continuous_subtype_val).mul continuous_const)

/-- The diagonal `GSpin(W) → H`. -/
def diagToH : GSpin d.QW →* d.H := d.diag.codRestrict d.H d.diag_mem_H

variable {d}

theorem QV_inl_ne_zero {w : Fin d.m → F} (hw : d.QW w ≠ 0) :
    d.QV (QuadraticMap.Isometry.inl d.QW d.QZ w) ≠ 0 := by
  rw [(QuadraticMap.Isometry.inl d.QW d.QZ).map_app]; exact hw

/-- `incl ∘ (w · w⁻¹) = (w · w⁻¹) ∘ incl`. -/
theorem incl_conjιGSpin {w : Fin d.m → F} (hw : d.QW w ≠ 0) (a : GSpin d.QW) :
    d.incl (conjιGSpin d.QW hw a) = conjιGSpin d.QV (QV_inl_ne_zero hw) (d.incl a) := by
  apply Subtype.ext; apply Units.ext
  show CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ) (ι d.QW w *
      ((a : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * ((d.QW w)⁻¹ • ι d.QW w)) = _
  rw [coe_conjιGSpin, map_mul, map_mul, map_smul, CliffordAlgebra.map_apply_ι,
    (QuadraticMap.Isometry.inl d.QW d.QZ).map_app]
  rfl

/-- Vectors of the flag are orthogonal to `W`. -/
theorem polar_inl_eq_zero_of_mem_flag {w : Fin d.m → F} {i : Fin (d.flag.len + 1)} {v : d.V}
    (hv : v ∈ d.flag.sub i) : QuadraticMap.polar d.QV (QuadraticMap.Isometry.inl d.QW d.QZ w) v = 0 := by
  have h1 : v.1 = 0 := (d.span_flag_le _ hv).1
  rw [polar_eq_two_mul_bform, bform_prod, h1]
  simp

/-- **Conjugation by `w ∈ W` preserves `N`** (it acts on `V` by `−s_w`, which is `−1` on `Z ⊇` the
flag and preserves `Z_rᗮ`). -/
theorem conjιGSpin_mem_N {w : Fin d.m → F} (hw : d.QW w ≠ 0) {n : GSpin d.QV} (hn : n ∈ d.N) :
    conjιGSpin d.QV (QV_inl_ne_zero hw) n ∈ d.N := by
  set w' := QuadraticMap.Isometry.inl d.QW d.QZ w
  have hw' : d.QV w' ≠ 0 := QV_inl_ne_zero hw
  obtain ⟨hA, hB, hC, hD⟩ := (d.mem_N_iff_NCond n).mp hn
  set c := ((ιUnit d.QV hw' : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)
  set c' := (((ιUnit d.QV hw')⁻¹ : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)
  set nv := ((n : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)
  set ni := (((n : (CliffordAlgebra d.QV)ˣ)⁻¹ : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)
  have hcc : c * c' = 1 := Units.mul_inv _
  have hc'c : c' * c = 1 := Units.inv_mul _
  have hperp : ∀ v, QuadraticMap.polar d.QV w' v = 0 → c' * ι d.QV v * c = -ι d.QV v := by
    intro v hv
    rw [ιUnit_inv_conj_ι, hv, zero_smul, zero_sub, smul_neg, smul_smul, inv_mul_cancel₀ hw',
      one_smul, map_neg]
  have hperp2 : ∀ v, QuadraticMap.polar d.QV w' v = 0 → c * ι d.QV v * c' = -ι d.QV v :=
    fun v hv => ιUnit_conj_ι_of_polar_eq_zero hw' hv
  have hy : ((conjιGSpin d.QV hw' n : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) =
      ιUnit d.QV hw' * (n : (CliffordAlgebra d.QV)ˣ) * (ιUnit d.QV hw')⁻¹ := rfl
  rw [d.mem_N_iff_NCond, hy, mul_inv_rev, mul_inv_rev, inv_inv]
  show d.NCond (c * nv * c') (c * (ni * c'))
  -- `y X y' = c (n (c' X c) n⁻¹) c'`
  have hconj : ∀ X : CliffordAlgebra d.QV, c * nv * c' * X * (c * (ni * c')) =
      c * (nv * (c' * X * c) * ni) * c' := fun X => by simp only [mul_assoc]
  refine ⟨fun i v hv => ?_, fun i v hv => ?_, fun v hv => ?_, ?_⟩
  · rw [hconj, hperp v (polar_inl_eq_zero_of_mem_flag hv), mul_neg, neg_mul]
    obtain ⟨f, hf, hfe⟩ := hA i v hv
    rw [← hfe, mul_neg, neg_mul, hperp2 f (polar_inl_eq_zero_of_mem_flag hf), neg_neg]
    exact ⟨f, hf, rfl⟩
  · rw [hconj, hperp v (polar_inl_eq_zero_of_mem_flag hv), mul_neg, neg_mul]
    obtain ⟨f, hf, hfe⟩ := hB i v hv
    rw [eq_sub_iff_add_eq] at hfe
    rw [← hfe, ← map_add, mul_neg, neg_mul, hperp2 _ (by
      rw [QuadraticMap.polar_add_right, polar_inl_eq_zero_of_mem_flag hf,
        polar_inl_eq_zero_of_mem_flag hv, add_zero]),
      neg_neg, map_add, add_sub_cancel_right]
    exact ⟨f, hf, rfl⟩
  · set v1 := (d.QV w')⁻¹ • (QuadraticMap.polar d.QV w' v • w' - d.QV w' • v)
    have h1 : c' * ι d.QV v * c = ι d.QV v1 := ιUnit_inv_conj_ι hw' v
    have h2 : c * ι d.QV v1 * c' = ι d.QV v := by
      rw [← h1]
      calc c * (c' * ι d.QV v * c) * c' = (c * c') * ι d.QV v * (c * c') := by
            simp only [mul_assoc]
        _ = _ := by rw [hcc, one_mul, mul_one]
    have hv1 : v1 ∈ (bform d.QV).orthogonal d.flag.top := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro z hz
      have hzw : bform d.QV z w' = 0 := by
        have h1 : z.1 = 0 := (d.span_flag_le _ hz).1
        rw [bform_prod, h1]; simp [w']
      have hzv : bform d.QV z v = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hv) z hz
      show bform d.QV z v1 = 0
      simp only [v1, map_smul, map_sub, hzw, hzv, smul_zero, sub_zero]
    obtain ⟨f, hf, hfe⟩ := hC v1 hv1
    rw [eq_sub_iff_add_eq] at hfe
    rw [hconj, h1, ← hfe, mul_add, add_mul, h2,
      hperp2 f (polar_inl_eq_zero_of_mem_flag hf), add_sub_cancel_right, ← map_neg]
    exact ⟨-f, neg_mem hf, rfl⟩
  · have hpow : ∀ k : ℕ, (c * nv * c' - 1) ^ k = c * (nv - 1) ^ k * c' := by
      intro k
      induction k with
      | zero => simp [hcc]
      | succ k ih =>
        rw [pow_succ, ih, pow_succ]
        calc c * (nv - 1) ^ k * c' * (c * nv * c' - 1)
            = c * (nv - 1) ^ k * (c' * c) * nv * c' - c * (nv - 1) ^ k * c' := by
              simp only [mul_sub, mul_one, mul_assoc]
          _ = c * ((nv - 1) ^ k * (nv - 1)) * c' := by
              rw [hc'c, mul_one]; simp only [mul_sub, sub_mul, mul_one, mul_assoc]
    rw [hpow, hD, mul_zero, zero_mul]

/-- Conjugation by `w ∈ W` (anisotropic) on `G = GSpin(W) × GSpin(V)`, componentwise (in `C(V)`,
by the image `(w, 0)` of `w`).  An outer automorphism: `w` is odd. -/
def conjιG {w : Fin d.m → F} (hw : d.QW w ≠ 0) : d.G →* d.G :=
  d.pair.comp (((conjιGSpin d.QW hw).prodMap (conjιGSpin d.QV (QV_inl_ne_zero hw))).comp
    (d.fst.prod d.snd))

theorem continuous_conjιG {w : Fin d.m → F} (hw : d.QW w ≠ 0) : Continuous (conjιG hw) :=
  d.continuous_pair.comp (((continuous_conjιGSpin _).comp d.continuous_fst).prodMk
    ((continuous_conjιGSpin _).comp d.continuous_snd))

theorem conjιG_conjιG {w : Fin d.m → F} (hw : d.QW w ≠ 0) (g : d.G) :
    conjιG hw (conjιG hw g) = g :=
  d.G_ext (conjιGSpin_conjιGSpin _ _) (conjιGSpin_conjιGSpin _ _)

theorem conjιG_diag {w : Fin d.m → F} (hw : d.QW w ≠ 0) (a : GSpin d.QW) :
    conjιG hw (d.diag a) = d.diag (conjιGSpin d.QW hw a) :=
  d.G_ext rfl (incl_conjιGSpin hw a).symm

theorem nPart_conjιG {w : Fin d.m → F} (hw : d.QW w ≠ 0) (g : d.G) :
    d.nPart (conjιG hw g) = conjιGSpin d.QV (QV_inl_ne_zero hw) (d.nPart g) := by
  show (d.incl (conjιGSpin d.QW hw (d.fst g)))⁻¹ * conjιGSpin d.QV _ (d.snd g) = _
  rw [incl_conjιGSpin, ← map_inv, ← map_mul]
  rfl

/-- `conjιG` restricted to `H` (it preserves `N`, `conjιGSpin_mem_N`). -/
def conjιH {w : Fin d.m → F} (hw : d.QW w ≠ 0) : d.H →* d.H :=
  ((conjιG hw).comp d.H.subtype).codRestrict d.H fun h => by
    show d.nPart (conjιG hw (h : d.G)) ∈ d.N
    rw [nPart_conjιG]
    exact conjιGSpin_mem_N hw h.2

/-- `conjιH` fixes `A_{G,H}` (the diagonal scalars) pointwise. -/
theorem conjιH_eq_self_of_mem_AGHinH {w : Fin d.m → F} (hw : d.QW w ≠ 0) {h : d.H}
    (hh : h ∈ d.AGHinH) : conjιH hw h = h := by
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hh
  apply Subtype.ext
  show conjιG hw (h : d.G) = h
  rw [← hc, MonoidHom.comp_apply, conjιG_diag, conjιGSpin_scalarGSpin]

/-- The induced automorphism of `H(F)/A_{G,H}(F)`. -/
def conjιHmod {w : Fin d.m → F} (hw : d.QW w ≠ 0) : d.HmodAGH →* d.HmodAGH :=
  QuotientGroup.map d.AGHinH d.AGHinH (conjιH hw) fun h hh => by
    show conjιH hw h ∈ d.AGHinH
    rw [conjιH_eq_self_of_mem_AGHinH hw hh]; exact hh

theorem conjιHmod_mk {w : Fin d.m → F} (hw : d.QW w ≠ 0) (h : d.H) :
    conjιHmod hw (QuotientGroup.mk h) = QuotientGroup.mk (conjιH hw h) := rfl

theorem continuous_conjιHmod {w : Fin d.m → F} (hw : d.QW w ≠ 0) : Continuous (conjιHmod hw) :=
  continuous_coinduced_dom.2 (QuotientGroup.continuous_mk.comp
    (continuous_induced_rng.2 ((continuous_conjιG hw).comp continuous_subtype_val)))

theorem conjιHmod_conjιHmod {w : Fin d.m → F} (hw : d.QW w ≠ 0) (q : d.HmodAGH) :
    conjιHmod hw (conjιHmod hw q) = q := by
  induction q using QuotientGroup.induction_on with
  | H h =>
    rw [conjιHmod_mk, conjιHmod_mk]
    congr 1
    exact Subtype.ext (conjιG_conjιG hw h)

theorem mk'_diagToH_scalarGSpin (c : Fˣ) :
    QuotientGroup.mk' d.AGHinH (d.diagToH (scalarGSpin d.QW c)) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ⟨c, rfl⟩)

theorem mk_diagToH_scalarGSpin (c : Fˣ) :
    (QuotientGroup.mk (d.diagToH (scalarGSpin d.QW c)) : d.HmodAGH) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ⟨c, rfl⟩)

/-- **`Δ(u w) = 1`** for the modular character `Δ` of `H(F)/A_{G,H}(F)` and `u, w ∈ W`
anisotropic: conjugation by `w` is a continuous involutive automorphism mapping the image of
`(uw, uw)` to its inverse (`conjιGSpin_gspinPair`), so `Δ(uw) = Δ(uw)⁻¹`. -/
theorem modularCharacter_mk_diagToH_gspinPair {u w : Fin d.m → F} (hu : d.QW u ≠ 0)
    (hw : d.QW w ≠ 0) :
    Measure.modularCharacter (QuotientGroup.mk (d.diagToH (gspinPair d.QW hu hw)) : d.HmodAGH) =
      1 := by
  refine modularCharacter_eq_one_of_involutive_inv (conjιHmod hw) (continuous_conjιHmod hw)
    (conjιHmod_conjιHmod hw) ?_
  rw [conjιHmod_mk]
  have e : conjιH hw (d.diagToH (gspinPair d.QW hu hw)) =
      d.diagToH (conjιGSpin d.QW hw (gspinPair d.QW hu hw)) :=
    Subtype.ext (conjιG_diag hw _)
  rw [e, conjιGSpin_gspinPair]
  exact map_mul_inv_of_map_eq_one ((QuotientGroup.mk' d.AGHinH).comp d.diagToH)
    (mk'_diagToH_scalarGSpin _) _

/-- **Unimodularity of `H(F)/A_{G,H}(F)`, the Levi half** (from Cartan–Dieudonné): `Δ(a, a) = 1` for all `a ∈ GSpin(W)`.  `Δ ∘ diag`
is a homomorphism, trivial on the scalars (they lie in `A_{G,H}`) and on the products `u w` of
anisotropic vectors (`modularCharacter_mk_diagToH_gspinPair`), which generate `GSpin(W)` with the
scalars (`closure_scalarGSpin_gspinPair`). -/
theorem modularCharacter_mk_diagToH (a : GSpin d.QW) :
    Measure.modularCharacter (QuotientGroup.mk (d.diagToH a) : d.HmodAGH) = 1 := by
  let χ : GSpin d.QW →* NNReal :=
    Measure.modularCharacter.comp ((QuotientGroup.mk' d.AGHinH).comp d.diagToH)
  have hχ : χ = 1 := by
    refine MonoidHom.eq_of_eqOn_dense (closure_scalarGSpin_gspinPair d.nondeg) ?_
    rintro x (⟨c, rfl⟩ | ⟨u, w, hu, hw, rfl⟩)
    · show Measure.modularCharacter
        (QuotientGroup.mk (d.diagToH (scalarGSpin d.QW c)) : d.HmodAGH) = 1
      rw [mk_diagToH_scalarGSpin, map_one]
    · exact modularCharacter_mk_diagToH_gspinPair hu hw
  exact congr($hχ a)

end LeviInvolution

/-- **Unimodularity of `H(F)/A_{G,H}(F)`, the Levi half**: right translation by (the image of) `(a, a)`, `a ∈ GSpin(W)`, preserves
the Haar measure of `H(F)/A_{G,H}(F)`.  The thesis argues through `Δ_H(a) = Δ_{GSpin(W)}(a) ·
|det Ad(a)|_𝔫|` and `det = 1` (Thesis §5.2).  Proof here (own work), avoiding the
semidirect-product decomposition of Haar measure: the modular character `Δ` is a homomorphism to
`ℝ_{>0}`, invariant under continuous automorphisms; conjugation by an anisotropic `w ∈ W` is a
continuous involutive automorphism of `H/A_{G,H}` mapping `(uw, uw)` to its inverse modulo
`A_{G,H}`, so `Δ(uw, uw) = 1`; the scalars lie in `A_{G,H}`; and scalars and products `u w`
generate `GSpin(W)` (`closure_scalarGSpin_gspinPair`, proved from the Cartan–Dieudonné axiom
`cartan_dieudonne_even`). -/
theorem map_mul_diag_haar_HmodAGH (a : GSpin d.QW) :
    Measure.map (· * (QuotientGroup.mk ⟨d.diag a, d.diag_mem_H a⟩ : d.HmodAGH)) Measure.haar =
      Measure.haar :=
  map_mul_right_haar_eq_self_of_modularCharacter_eq_one (modularCharacter_mk_diagToH (d := d) a)

/-- `H(F)/A_{G,H}(F)` is unimodular, i.e. its Haar measure is also right
invariant.  (`H = GSpin(W) ⋉ N` with `N` unipotent: the modular character of `H` is
`|det Ad(·)|_𝔫|`, trivial since `GSpin(W)` acts on `𝔫 = Lie N` with determinant `1`; Thesis §5.2.)

Proof (own work): every `h ∈ H` is `(a, a) · (1, n)` with `a = h_W`, `n = n(h) ∈ N`, and the right
translations preserving Haar measure form a monoid (`map_mul_right_mul_eq`).  Translation by
`(1, n)` is proved (`map_mul_inr_haar_HmodAGH`: powers of a unipotent element are bounded, and the
modular character is trivial on compact subgroups); translation by `(a, a)` is
`map_mul_diag_haar_HmodAGH` (an outer involution inverts the generators `u w` of `GSpin(W)`; it
rests on `closure_scalarGSpin_gspinPair`, proved from the axiom `cartan_dieudonne_even`). -/
theorem isMulRightInvariant_haar_HmodAGH :
    (Measure.haar : Measure d.HmodAGH).IsMulRightInvariant := by
  refine ⟨fun q => ?_⟩
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  have hn : d.nPart h ∈ d.N := h.2
  have e : h = ⟨d.diag (d.fst h), d.diag_mem_H _⟩ * ⟨d.inr (d.nPart h), d.inr_mem_H hn⟩ := by
    apply Subtype.ext
    apply d.G_ext
    · exact ((map_mul d.fst _ _).trans (mul_one _)).symm
    · exact ((map_mul d.snd _ _).trans (mul_inv_cancel_left _ _)).symm
  have hq : (QuotientGroup.mk h : d.HmodAGH) =
      QuotientGroup.mk ⟨d.diag (d.fst h), d.diag_mem_H _⟩ *
        QuotientGroup.mk ⟨d.inr (d.nPart h), d.inr_mem_H hn⟩ :=
    (congrArg (QuotientGroup.mk (s := d.AGHinH)) e).trans (QuotientGroup.mk_mul _ _ _)
  have key := map_mul_right_mul_eq (d.map_mul_diag_haar_HmodAGH (d.fst h))
    (d.map_mul_inr_haar_HmodAGH hn)
  rw [hq]
  exact key


open scoped Classical in
/-- The Weil quotient measure `dx` on `H(F)\G(F)/A_G(F)` (Thesis §7.1): the
unique measure `m` with `∫_{G/A_G} φ = ∫_{H\G/A_G} ∫_{H/A_{G,H}} φ(h x) dh dm(x)` for
`φ ∈ C_c(G/A_G)`, for the Haar measures `Measure.haar` on `G/A_G` and on `H/A_{G,H}`
(chosen by the epsilon pattern; `0` if no such measure exists, which does not happen:
`weilMeasureHG_spec` in `TraceFormula/ThetaF.lean`, from `weil_quotient`). -/
def weilMeasureHG : Measure d.HGQuot :=
  if h : ∃ m, IsWeilMeasure d.toGmodAG (Measure.haar : Measure d.GmodAG)
      (Measure.haar : Measure d.HmodAGH) m then h.choose else 0

/-- If a Weil measure exists, `weilMeasureHG` is one. -/
theorem weilMeasureHG_spec_of_exists
    (h : ∃ m, IsWeilMeasure d.toGmodAG (Measure.haar : Measure d.GmodAG)
      (Measure.haar : Measure d.HmodAGH) m) :
    IsWeilMeasure d.toGmodAG Measure.haar Measure.haar d.weilMeasureHG := by
  classical
  unfold weilMeasureHG
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

/-- The elliptic regular set of `G(F)` (Thesis §2.5): regular semisimple elements whose
centralizer is compact modulo `A_G(F)`. -/
def ellRegSet : Set ↥d.G := ellipticRegularSet d.G d.lie d.AG

theorem ellRegSet_subset_regularSet : d.ellRegSet ⊆ regularSet d.G d.lie :=
  ellipticRegularSet_subset_regularSet _ _ _

/-- `weilMeasureHG` is the Weil measure, given right invariance of the Haar measure on
`G(F)/A_G(F)` (which follows from the unimodularity of `G(F)` because `A_G` is central; proved downstream).
From `weil_quotient` (Bourbaki), `isClosedEmbedding_toGmodAG` and the unimodularity of
`H(F)/A_{G,H}(F)` (`isMulRightInvariant_haar_HmodAGH`).  All topological hypotheses of `weil_quotient` are
instances in this file. -/
theorem weilMeasureHG_spec_of_isMulRightInvariant
    (hG : (Measure.haar : Measure d.GmodAG).IsMulRightInvariant) :
    IsWeilMeasure d.toGmodAG Measure.haar Measure.haar d.weilMeasureHG := by
  have := d.isMulRightInvariant_haar_HmodAGH
  exact d.weilMeasureHG_spec_of_exists
    (weil_quotient d.toGmodAG d.continuous_toGmodAG d.isClosedEmbedding_toGmodAG _ _).exists

end GGPData

/-! ## 3. Strongly cuspidal test functions (`C_c^∞` modulo `A_G`) -/

variable (d : GGPData F) (χ : CentralCharOn d)

/-- `f(a g) = χ(a)⁻¹ f(g)` for `a ∈ A_G(F)` (Thesis §2.3). -/
def IsChiEquivariant (f : ↥d.G → ℂ) : Prop :=
  ∀ (a : ↥d.AG) (g : ↥d.G), f ((a : ↥d.G) * g) = (((χ.toHom a)⁻¹ : Circle) : ℂ) * f g

/-- `f` is compactly supported modulo `A_G(F)`: `supp f ⊆ A_G(F) · C` for a compact `C`. -/
def HasCompactSupportModAG (f : ↥d.G → ℂ) : Prop :=
  ∃ C : Set ↥d.G, IsCompact C ∧ Function.support f ⊆ (d.AG : Set ↥d.G) * C

/-- Strong cuspidality (Thesis §4.5): for every proper parabolic
`P = MU` of `G`, `∫_{U(F)} f(m u) du = 0` for all `m`.  We quantify over `m ∈ P(F)` instead of
`m ∈ M(F)` (equivalent, by left-invariance of `du`, since `P = MU`), which avoids choosing Levi
factors.  Integrability of `u ↦ f(mu)` is included (automatic for the functions considered, since
`U(F)` embeds closedly in `G(F)/A_G(F)`). -/
def IsStronglyCuspidal (f : ↥d.G → ℂ) : Prop :=
  ∀ (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV), d.IsProperFlagPair FW FV →
    ∀ p ∈ d.parabolicP FW FV,
      Integrable (fun u : ↥(d.parabolicU FW FV) => f (p * u)) Measure.haar ∧
        ∫ u : ↥(d.parabolicU FW FV), f (p * u) ∂Measure.haar = 0

/-- **`𝒞_scusp(A_G(F)\G(F), χ⁻¹)`, `C_c^∞` version** (Thesis Ch. 1, §4.5, §7.1, with
`C_c^∞` test functions): locally constant functions `f` on `G(F)` with `f(ag) = χ(a)⁻¹ f(g)`
(`a ∈ A_G(F)`), compactly supported modulo `A_G(F)`, and strongly cuspidal.
`C_c^∞` modulo `A_G` replaces the Harish-Chandra Schwartz space `𝒞(A_G\G, χ⁻¹)`; every stated
theorem of the trace formula uses this space. -/
def ScuspTestFn : Set (↥d.G → ℂ) :=
  {f | IsLocallyConstant f ∧ IsChiEquivariant d χ f ∧ HasCompactSupportModAG d f ∧
    IsStronglyCuspidal d f}

theorem zero_mem_scuspTestFn : (0 : ↥d.G → ℂ) ∈ ScuspTestFn d χ := by
  refine ⟨IsLocallyConstant.const 0, fun _ _ => by simp, ⟨∅, isCompact_empty, by simp⟩,
    fun FW FV _ p _ => ⟨integrable_zero _ _ _, by simp⟩⟩

/-! ## 4. The kernel `K(f, x)` and the distribution `J(f)` -/

variable (ψ : NontrivialAddChar F)

/-- The integrand `h ↦ f(x⁻¹ h x) ξ(h)` of `K(f,x)` on `H(F)`. -/
def kernelIntegrand (f : ↥d.G → ℂ) (x : ↥d.G) (h : ↥d.H) : ℂ :=
  f (x⁻¹ * (h : ↥d.G) * x) * d.xi ψ.toAddChar h

/-- `K(f, x) = ∫_{H(F)/A_{G,H}(F)} f(x⁻¹ h x) ξ(h) dh` (Thesis §7.1), for the Haar
measure on the quotient group `H(F)/A_{G,H}(F)`, integrating over coset representatives
(the integrand is `A_{G,H}(F)`-invariant: `kernelIntegrand_mul_AGH`). -/
def kernelK (f : ↥d.G → ℂ) (x : ↥d.G) : ℂ :=
  ∫ q : d.HmodAGH, kernelIntegrand d ψ f x (Quotient.out q) ∂Measure.haar

/-- `J(f) = ∫_{H(F)\G(F)/A_G(F)} K(f, x) dx` (Thesis §7.1, §10.1), for the Weil
quotient measure `weilMeasureHG`, integrating over coset representatives (`K(f,·)` is left
`H(F)`- and right `A_G(F)`-invariant: `kernelK_mul_left_H`, `kernelK_mul_AG`). -/
def distribJ (f : ↥d.G → ℂ) : ℂ :=
  ∫ q : d.HGQuot, kernelK d ψ f (Quotient.out (CosetSpace.out d.toGmodAG q : d.GmodAG))
    ∂d.weilMeasureHG

/-! ### Well-definedness on the quotients -/

/-- The integrand of `K(f,x)` is `A_{G,H}(F)`-invariant, so it descends to `H(F)/A_{G,H}(F)`:
`f(x⁻¹ a h x) = f(a x⁻¹ h x) = χ(a)⁻¹ f(x⁻¹hx) = f(x⁻¹hx)` (χ trivial on `A_{G,H}`) and
`ξ(ah) = ξ(h)` (`xi_eq_one_of_mem_AGH'`). -/
theorem kernelIntegrand_mul_AGH (f : ↥d.G → ℂ) (hf : IsChiEquivariant d χ f) (x : ↥d.G)
    (a h : ↥d.H) (ha : a ∈ d.AGHinH) :
    kernelIntegrand d ψ f x (a * h) = kernelIntegrand d ψ f x h := by
  have ha' : (a : ↥d.G) ∈ d.AGH := Subgroup.mem_subgroupOf.mp ha
  have hcent := Subgroup.mem_center_iff.mp (d.AGH_le_center ha')
  have hconj : x⁻¹ * ((a * h : ↥d.H) : ↥d.G) * x = (a : ↥d.G) * (x⁻¹ * (h : ↥d.G) * x) := by
    rw [Subgroup.coe_mul, ← mul_assoc, hcent x⁻¹]
    simp only [mul_assoc]
  unfold kernelIntegrand
  rw [hconj, d.xi_mul, d.xi_eq_one_of_mem_AGH' ψ.toAddChar a ha',
    hf ⟨(a : ↥d.G), d.AGH_le_AG ha'⟩, χ.trivial_AGH _ ha']
  simp

/-- The integrand of `K(f,x)` only depends on the class in `H(F)/A_{G,H}(F)` (Thesis §7.1). -/
theorem kernelIntegrand_eq_of_mk_eq (f : ↥d.G → ℂ) (hf : IsChiEquivariant d χ f) (x : ↥d.G)
    {h k : ↥d.H} (hhk : (QuotientGroup.mk h : d.HmodAGH) = QuotientGroup.mk k) :
    kernelIntegrand d ψ f x h = kernelIntegrand d ψ f x k := by
  rw [QuotientGroup.eq] at hhk
  -- `k = h * a = a * h` with `a = h⁻¹ k ∈ A_{G,H}` central
  set a : ↥d.H := h⁻¹ * k
  have hk : k = a * h := by
    have hcent := Subgroup.mem_center_iff.mp (d.AGH_le_center (Subgroup.mem_subgroupOf.mp hhk))
      (h : ↥d.G)
    apply Subtype.ext
    have : ((h : ↥d.G) * (a : ↥d.G)) = (a : ↥d.G) * h := hcent
    simp only [Subgroup.coe_mul] at this ⊢
    rw [← this]
    simp [a]
  rw [hk, kernelIntegrand_mul_AGH d χ ψ f hf x a h hhk]

/-- `K(f, x a) = K(f, x)` for `a ∈ A_G(F)` (`a` is central: `(xa)⁻¹ h (xa) = x⁻¹ h x`). -/
theorem kernelK_mul_AG (f : ↥d.G → ℂ) (x : ↥d.G) (a : ↥d.G) (ha : a ∈ d.AG) :
    kernelK d ψ f (x * a) = kernelK d ψ f x := by
  have hcent := Subgroup.mem_center_iff.mp (d.AG_le_center ha)
  unfold kernelK kernelIntegrand
  congr 1
  funext q
  congr 2
  have e : (x * a)⁻¹ * ((Quotient.out q : ↥d.H) : ↥d.G) * (x * a) =
      a⁻¹ * ((x⁻¹ * ((Quotient.out q : ↥d.H) : ↥d.G) * x) * a) := by group
  rw [e, hcent, ← mul_assoc, inv_mul_cancel, one_mul]

/-- `K(f, h x) = K(f, x)` for `h ∈ H(F)` (substitute `h' ↦ h⁻¹ h' h` in `H(F)/A_{G,H}(F)`;
`ξ` is a character, and `H(F)/A_{G,H}(F)` is unimodular
(`isMulRightInvariant_haar_HmodAGH`); Thesis §7.1). -/
theorem kernelK_mul_left_H (f : ↥d.G → ℂ) (hf : IsChiEquivariant d χ f) (h : ↥d.H)
    (x : ↥d.G) : kernelK d ψ f ((h : ↥d.G) * x) = kernelK d ψ f x := by
  have hR := d.isMulRightInvariant_haar_HmodAGH
  let φ : d.HmodAGH → ℂ := fun q => kernelIntegrand d ψ f x (Quotient.out q)
  -- the integrand at `h x`, at the representative of `q`, equals the integrand at `x`
  -- at the representative of `h̄⁻¹ q h̄`
  have key : ∀ q : d.HmodAGH, kernelIntegrand d ψ f ((h : ↥d.G) * x) (Quotient.out q) =
      φ ((h : d.HmodAGH)⁻¹ * q * (h : d.HmodAGH)) := by
    intro q
    have e1 : kernelIntegrand d ψ f ((h : ↥d.G) * x) (Quotient.out q) =
        kernelIntegrand d ψ f x (h⁻¹ * Quotient.out q * h) := by
      unfold kernelIntegrand
      rw [d.xi_conj]
      congr 2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc]
    refine e1.trans ?_
    exact kernelIntegrand_eq_of_mk_eq d χ ψ f hf x
      ((QuotientGroup.mk_conj_out d.AGHinH h q).trans (QuotientGroup.out_eq' _).symm)
  have h1 : ∫ q, φ ((h : d.HmodAGH)⁻¹ * q * (h : d.HmodAGH)) ∂(Measure.haar : Measure d.HmodAGH) =
      ∫ q, φ (q * (h : d.HmodAGH)) ∂(Measure.haar : Measure d.HmodAGH) :=
    integral_mul_left_eq_self (fun q => φ (q * (h : d.HmodAGH))) (h : d.HmodAGH)⁻¹
  have h2 : ∫ q, φ (q * (h : d.HmodAGH)) ∂(Measure.haar : Measure d.HmodAGH) =
      ∫ q, φ q ∂(Measure.haar : Measure d.HmodAGH) :=
    integral_mul_right_eq_self φ (h : d.HmodAGH)
  unfold kernelK
  simp_rw [key]
  exact h1.trans h2

/-! ## 5. The orbital pairing and `θ_f` -/

/-- The inner integral `∫_G f(y⁻¹ g y) f'(g) dg` of the orbital pairing, at `y ∈ G(F)` (Thesis §4.8;
BP §5.5, number unverified). -/
def orbitalInner (f f' : ↥d.G → ℂ) (y : ↥d.G) : ℂ :=
  ∫ g : ↥d.G, f (y⁻¹ * g * y) * f' g ∂Measure.haar

/-- The orbital pairing `⟨f, f'⟩ = ∫_{G(F)/A_G(F)} ∫_{G(F)} f(x⁻¹ g x) f'(g) dg dx` (BP §5.5,
number unverified; Thesis §4.8), for `Measure.haar` on `G(F)` and on the quotient
group `G(F)/A_G(F)`, integrating over coset representatives (the inner integral does not depend
on the representative: `orbitalInner_mul_AG`). -/
def orbitalPairing (f f' : ↥d.G → ℂ) : ℂ :=
  ∫ x : d.GmodAG, (∫ g : ↥d.G, f ((Quotient.out x)⁻¹ * g * Quotient.out x) * f' g
    ∂Measure.haar) ∂Measure.haar

theorem orbitalPairing_eq (f f' : ↥d.G → ℂ) :
    orbitalPairing d f f' =
      ∫ x : d.GmodAG, orbitalInner d f f' (Quotient.out x) ∂Measure.haar := rfl

/-- The inner integral of the orbital pairing is invariant under `y ↦ y a`, `a ∈ A_G(F)`
(`a` central), so the orbital pairing does not depend on the choice of representatives. -/
theorem orbitalInner_mul_AG (f f' : ↥d.G → ℂ) (y a : ↥d.G) (ha : a ∈ d.AG) :
    orbitalInner d f f' (y * a) = orbitalInner d f f' y := by
  have hcent := Subgroup.mem_center_iff.mp (d.AG_le_center ha)
  unfold orbitalInner
  congr 1
  funext g
  congr 2
  have e : (y * a)⁻¹ * g * (y * a) = a⁻¹ * ((y⁻¹ * g * y) * a) := by group
  rw [e, hcent, ← mul_assoc, inv_mul_cancel, one_mul]

/-- Well-definedness of the orbital pairing: the inner integral at the chosen representative of
the class of `y` equals the inner integral at `y`. -/
theorem orbitalInner_out_mk (f f' : ↥d.G → ℂ) (y : ↥d.G) :
    orbitalInner d f f' (Quotient.out (QuotientGroup.mk y : d.GmodAG)) =
      orbitalInner d f f' y := by
  have h : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk y : d.GmodAG)) : d.GmodAG) =
      QuotientGroup.mk y := QuotientGroup.out_eq' _
  rw [QuotientGroup.eq] at h
  have e : y = Quotient.out (QuotientGroup.mk y : d.GmodAG) *
      ((Quotient.out (QuotientGroup.mk y : d.GmodAG))⁻¹ * y) := by group
  conv_rhs => rw [e]
  rw [orbitalInner_mul_AG d f f' _ _ h]

/-- `θ` represents the orbital pairing of `f`: `θ` is locally integrable,
continuous on the regular set, and `∫_G θ f' = ⟨f, f'⟩` for all `f' ∈ C_c^∞(G(F))`.
For strongly cuspidal `f`, BP Thm 5.5.1(iv) with the Weyl integration formula (BP §1.7,
numbers unverified) says that BP's `θ_f` (Thesis §4.8) has this property, up to the positive
constant relating the measures. -/
def IsThetaF (f θ : ↥d.G → ℂ) : Prop :=
  LocallyIntegrable θ (Measure.haar : Measure ↥d.G) ∧ ContinuousOn θ (regularSet d.G d.lie) ∧
    ∀ f' ∈ testFunctions ↥d.G, ∫ g, θ g * f' g ∂Measure.haar = orbitalPairing d f f'

open scoped Classical in
/-- **The quasi-character `θ_f` of a strongly cuspidal function** (Thesis §4.8; BP §5.5):
the function representing the orbital pairing of `f` (`IsThetaF`), chosen by the
epsilon pattern (as `characterOn`); `0` if there is none.  Its existence and the quasi-character
property for `f ∈ ScuspTestFn d χ` are `thetaF_spec` (`TraceFormula/ThetaF.lean`).  It is unique
on the regular set (`thetaF_unique`, ibid.).  Convention: `θ_f(ag) = χ(a)⁻¹ θ_f(g)`, so `θ_f` is
matched with characters of representations with central character `χ⁻¹`. -/
def thetaF (f : ↥d.G → ℂ) : ↥d.G → ℂ :=
  if h : ∃ θ, IsThetaF d f θ then h.choose else 0

/-- If some `θ` represents the orbital pairing of `f`, so does `thetaF d f`. -/
theorem isThetaF_thetaF_of_exists (f : ↥d.G → ℂ) (h : ∃ θ, IsThetaF d f θ) :
    IsThetaF d f (thetaF d f) := by
  classical
  unfold thetaF
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

/-- If no function represents the orbital pairing of `f`, then `thetaF d f = 0`. -/
theorem thetaF_of_not_exists (f : ↥d.G → ℂ) (h : ¬ ∃ θ, IsThetaF d f θ) :
    thetaF d f = 0 := by
  classical
  unfold thetaF
  rw [dite_eq_right_of_eq_false (eq_false h)]

end GSpinGGP
