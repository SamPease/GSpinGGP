/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import TauCeti.MeasureTheory.Group.Conjugation

/-!
# Haar measures are determined near the identity

* `Measure.eq_of_isHaarMeasure_of_eqOn_nhds`: two Haar measures on a second countable locally
  compact group that agree on the measurable subsets of a neighbourhood of `1` are equal.
* `Measure.eq_of_isHaarMeasure_of_eq_near_one`: the same, when both agree near `1` with a common
  reference set function (e.g. the `exp`-image measure of a torus).
* `Measure.measure_eq_card_mul_of_vadd`, `Measure.eq_of_forall_vadd_coset`: two finite measures
  carried by a compact open subgroup `L₀`, with the same mass on `L₀`, and each giving every coset
  inside `L₀` of a basis of open subgroups `Lₙ` the mass of `Lₙ`, are equal.
* `Measure.map_conj_map_mulEquiv`: the push-forward of a bi-invariant measure along a group
  isomorphism is conjugation invariant (Tau Ceti `measurePreserving_conj`).
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

section CosetMeasure

open Pointwise

/-! ## Measures that are uniform on the cosets of a basis of open subgroups -/

variable {V : Type*} [AddCommGroup V]

variable [MeasurableSpace V]

/-- A measure giving the same mass to all cosets of `L` inside `L₀` gives `L₀` the index times
that mass. -/
theorem measure_eq_card_mul_of_vadd [MeasurableAdd V] (μ : Measure V) {L₀ L : AddSubgroup V}
    (hL : L ≤ L₀) [Finite (L₀ ⧸ L.addSubgroupOf L₀)] (hLm : MeasurableSet (L : Set V))
    (h : ∀ x ∈ L₀, μ (x +ᵥ (L : Set V)) = μ L) :
    μ L₀ = Nat.card (L₀ ⧸ L.addSubgroupOf L₀) * μ L := by
  classical
  have : Fintype (L₀ ⧸ L.addSubgroupOf L₀) := Fintype.ofFinite _
  set o : (L₀ ⧸ L.addSubgroupOf L₀) → V := fun q => ((Quotient.out q : ↥L₀) : V) with ho
  have hcover : (L₀ : Set V) = ⋃ q, o q +ᵥ (L : Set V) := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_iUnion]
    constructor
    · intro hx
      refine ⟨QuotientAddGroup.mk ⟨x, hx⟩, ?_⟩
      rw [mem_leftAddCoset_iff]
      have := QuotientAddGroup.eq.mp
        (Quotient.out_eq (QuotientAddGroup.mk (s := L.addSubgroupOf L₀) ⟨x, hx⟩))
      exact AddSubgroup.mem_addSubgroupOf.mp this
    · rintro ⟨q, hq⟩
      rw [mem_leftAddCoset_iff] at hq
      have h1 := L₀.add_mem (Quotient.out q).2 (hL hq)
      rwa [add_neg_cancel_left] at h1
  have hdisj : Pairwise (Function.onFun Disjoint fun q => o q +ᵥ (L : Set V)) := by
    intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    intro w hw hw'
    rw [mem_leftAddCoset_iff] at hw hw'
    apply hqq'
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    apply QuotientAddGroup.eq.mpr
    rw [AddSubgroup.mem_addSubgroupOf]
    have := L.sub_mem hw hw'
    rw [show -o q + w - (-o q' + w) = -o q + o q' by abel] at this
    simpa [ho] using this
  rw [hcover, measure_iUnion hdisj fun q => hLm.const_vadd _, tsum_fintype]
  simp only [fun q => h (o q) (Quotient.out q).2, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.card_eq_fintype_card]

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [SecondCountableTopology V]
  [BorelSpace V]

/-- **Measures uniform on cosets are equal.** Let `L₀ ⊇ L₁ ⊇ …` be open subgroups forming a basis
of neighbourhoods of `0`, with `L₀` compact. Two finite measures carried by `L₀`, giving `L₀` the
same mass and giving each coset of `Lₙ` inside `L₀` the mass of `Lₙ`, are equal. (Counting cosets
gives them equal mass on every coset; the cosets form a π-system generating the Borel sets.) -/
theorem eq_of_forall_vadd_coset (L : ℕ → AddSubgroup V) (hanti : Antitone L)
    (hopen : ∀ n, IsOpen (L n : Set V)) (hcpt : IsCompact (L 0 : Set V))
    (hbasis : ∀ U ∈ 𝓝 (0 : V), ∃ n, (L n : Set V) ⊆ U) (μ ν : Measure V) [IsFiniteMeasure μ]
    (hμ0 : μ (L 0 : Set V)ᶜ = 0) (hν0 : ν (L 0 : Set V)ᶜ = 0)
    (hμ : ∀ n, ∀ x ∈ L 0, μ (x +ᵥ (L n : Set V)) = μ (L n))
    (hν : ∀ n, ∀ x ∈ L 0, ν (x +ᵥ (L n : Set V)) = ν (L n)) (h0 : μ (L 0) = ν (L 0)) :
    μ = ν := by
  -- equal mass on each `Lₙ`
  have hLn : ∀ n, μ (L n) = ν (L n) := by
    intro n
    have hle : L n ≤ L 0 := hanti (Nat.zero_le n)
    haveI : CompactSpace ↥(L 0) := isCompact_iff_compactSpace.mp hcpt
    haveI : Finite (↥(L 0) ⧸ (L n).addSubgroupOf (L 0)) :=
      AddSubgroup.quotient_finite_of_isOpen _ (AddSubgroup.addSubgroupOf_isOpen _ _ (hopen n))
    have hm := (hopen n).measurableSet
    have e1 := measure_eq_card_mul_of_vadd μ hle hm fun x hx => hμ n x hx
    have e2 := measure_eq_card_mul_of_vadd ν hle hm fun x hx => hν n x hx
    rw [h0, e2] at e1
    have hN0 : (Nat.card (↥(L 0) ⧸ (L n).addSubgroupOf (L 0)) : ENNReal) ≠ 0 := by
      have : Nonempty (↥(L 0) ⧸ (L n).addSubgroupOf (L 0)) := ⟨0⟩
      exact_mod_cast Nat.card_pos.ne'
    exact ((ENNReal.mul_right_inj hN0 (ENNReal.natCast_ne_top _)).mp e1).symm
  -- equal mass on every coset
  have hC : ∀ n, ∀ x : V, μ (x +ᵥ (L n : Set V)) = ν (x +ᵥ (L n : Set V)) := by
    intro n x
    by_cases hx : x ∈ L 0
    · rw [hμ n x hx, hν n x hx, hLn]
    · have hsub : x +ᵥ (L n : Set V) ⊆ (L 0 : Set V)ᶜ := by
        intro w hw hw0
        rw [mem_leftAddCoset_iff] at hw
        apply hx
        have := (L 0).sub_mem hw0 (hanti (Nat.zero_le n) hw)
        rwa [show w - (-x + w) = x by abel] at this
      rw [measure_mono_null hsub hμ0, measure_mono_null hsub hν0]
  -- the cosets form a π-system generating the Borel σ-algebra
  set C : Set (Set V) := {s | ∃ n, ∃ x : V, s = x +ᵥ (L n : Set V)} with hCdef
  have hbas : TopologicalSpace.IsTopologicalBasis C := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ ⟨n, x, rfl⟩
      exact (hopen n).vadd x
    · intro a u hau hu
      have : (fun y => a + y) ⁻¹' u ∈ 𝓝 (0 : V) :=
        (continuous_const_add a).continuousAt.preimage_mem_nhds (by simpa using hu.mem_nhds hau)
      obtain ⟨n, hn⟩ := hbasis _ this
      refine ⟨a +ᵥ (L n : Set V), ⟨n, a, rfl⟩, ?_, ?_⟩
      · rw [mem_leftAddCoset_iff, neg_add_cancel]; exact (L n).zero_mem
      · intro w hw
        rw [mem_leftAddCoset_iff] at hw
        have := hn hw
        simpa using this
  have hpi : IsPiSystem C := by
    rintro _ ⟨n, x, rfl⟩ _ ⟨m, y, rfl⟩ ⟨z, hzx, hzy⟩
    refine ⟨max n m, z, ?_⟩
    rw [(leftAddCoset_eq_iff _).mpr ((mem_leftAddCoset_iff _).mp hzx),
      (leftAddCoset_eq_iff _).mpr ((mem_leftAddCoset_iff _).mp hzy)]
    ext w
    simp only [Set.mem_inter_iff, mem_leftAddCoset_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rcases le_total n m with h | h
      · rwa [max_eq_right h]
      · rwa [max_eq_left h]
    · intro hw
      exact ⟨hanti (le_max_left n m) hw, hanti (le_max_right n m) hw⟩
  refine ext_of_generate_finite C (by rw [‹BorelSpace V›.measurable_eq,
    hbas.borel_eq_generateFrom]) hpi ?_ ?_
  · rintro _ ⟨n, x, rfl⟩; exact hC n x
  · have hm := (hopen 0).measurableSet
    rw [← measure_add_measure_compl hm, ← measure_add_measure_compl hm, hμ0, hν0, h0]

end CosetMeasure
/-- **The push-forward of a bi-invariant measure along a group isomorphism is conjugation
invariant** (Tau Ceti `measurePreserving_conj`). -/
theorem map_conj_map_mulEquiv {G P : Type*} [Group G] [Group P] [MeasurableSpace G]
    [MeasurableMul G] [MeasurableSpace P] [MeasurableMul P] (μ : Measure G)
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (e : G ≃* P) (he : Measurable e) (u : P) :
    (μ.map e).map (fun h => u⁻¹ * h * u) = μ.map e := by
  set h₀ := (e.symm u)⁻¹
  have hc : (fun h => u⁻¹ * h * u) ∘ e = e ∘ (fun q => h₀ * q * h₀⁻¹) := by
    funext q; simp [h₀, map_mul, map_inv]
  rw [Measure.map_map (by fun_prop) he, hc, ← Measure.map_map he (by fun_prop),
    (TauCeti.measurePreserving_conj μ h₀).map_eq]

end MeasureTheory.Measure
