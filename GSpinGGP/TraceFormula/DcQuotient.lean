/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.ThetaF

/-!
# The measure `dg / d_c a` on `G(F)/A_G(F)` exists and is unique

`measGmodAG` (`TraceFormula/Basic.lean`) is `dcScaleAG • Measure.haar`, where `dcScaleAG` is chosen
so that `measGmodAG` is the quotient of the Haar measure `dg` on `G(F)` by the Haar measure `d_c a`
on `A_G(F)` giving the maximal compact subgroup of `A_G(F)` measure `1` (Arthur, Publ. IHÉS 73
(1991), §1, p. 11).  This file proves that such a constant exists and is unique, so that the
epsilon choice in `dcScaleAG` is the intended one:

* `isMaxCompact_ker_hcA`: `A_G(F) ∩ ker H_G` contains every compact subgroup of `A_G(F)` (the
  values of `H_G` on a compact subgroup form a finite subgroup of a torsion-free group); it is
  compact and open (`isCompact_ker_hcA`, `isOpen_ker_hcA`), so it is the maximal compact subgroup
  `A_G(𝒪)`, and `d_c a` is the Haar measure normalized on it (`isDcMeasureAG_dcA`);
* `IsDcMeasureAG.unique`: `d_c a` is unique;
* `exists_isDcQuotientAG`: the Weil quotient of `dg` by `d_c a` (`weil_quotient`, for
  `A_G(F) → G(F)`), transported from `A_G(F)\G(F)` to `G(F)/A_G(F)` (`A_G` is central), is right
  invariant, hence a positive multiple of `Measure.haar`;
* `isDcQuotientAG_measGmodAG`, `dcScaleAG_eq`: `measGmodAG` is that quotient, and `dcScaleAG` is the
  only constant that makes `c • Measure.haar` one.
-/

noncomputable section

open MeasureTheory Topology Filter
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- A right invariant measure, finite on compact sets, on a unimodular group is a multiple of
`Measure.haar` (uniqueness of Haar measures, applied to the inverse measures). -/
theorem eq_smul_haar_of_isMulRightInvariant {Q : Type*} [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [LocallyCompactSpace Q] [SecondCountableTopology Q] [MeasurableSpace Q]
    [BorelSpace Q] (m : Measure Q) [m.IsMulRightInvariant] [IsFiniteMeasureOnCompacts m]
    [(Measure.haar : Measure Q).IsMulRightInvariant] :
    ∃ c : ℝ≥0, m = (c : ℝ≥0∞) • (Measure.haar : Measure Q) := by
  obtain ⟨s, e1⟩ : ∃ s : ℝ≥0, m.inv = s • (Measure.haar : Measure Q) :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul m.inv (Measure.haar : Measure Q)⟩
  obtain ⟨t, e2⟩ : ∃ t : ℝ≥0, (Measure.haar : Measure Q).inv = t • (Measure.haar : Measure Q) :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul (Measure.haar : Measure Q).inv
      (Measure.haar : Measure Q)⟩
  refine ⟨s * t, ?_⟩
  calc m = m.inv.inv := (Measure.inv_inv m).symm
    _ = _ := by
      rw [e1]
      change Measure.map Inv.inv (s • (Measure.haar : Measure Q)) = _
      rw [Measure.map_smul]
      · change s • (Measure.haar : Measure Q).inv = _
        rw [e2, smul_smul, ENNReal.smul_def]
      · exact measurable_inv.aemeasurable

namespace GGPData

variable (d : GGPData F)

/-! ## The maximal compact subgroup of `A_G(F)` and `d_c a` -/

/-- **`A_G(F) ∩ ker H_G` is the maximal compact subgroup of `A_G(F)`**: every compact subgroup
`K'` lies in it.  For `k ∈ K'` the values `H_G(k)^n = H_G(k^n)` lie in the finite set `H_G(K')`
(`finite_image_hcG`), so `H_G(k)` has finite order in the torsion-free group `ℝ⁴`. -/
theorem isMaxCompact_ker_hcA (K' : Subgroup ↥d.AG) (hK' : IsCompact (K' : Set ↥d.AG)) :
    K' ≤ d.hcA.ker := by
  intro k hk
  have hfin : (d.hcG '' ((Subtype.val : ↥d.AG → ↥d.G) '' (K' : Set ↥d.AG))).Finite :=
    d.finite_image_hcG (hK'.image continuous_subtypeVal)
  have hmem : ∀ n : ℕ, d.hcA k ^ n ∈ d.hcG '' ((Subtype.val : ↥d.AG → ↥d.G) '' (K' : Set ↥d.AG)) :=
    fun n => ⟨((k ^ n : ↥d.AG) : ↥d.G), ⟨k ^ n, K'.pow_mem hk n, rfl⟩, by
      rw [← hcA_apply, map_pow]⟩
  obtain ⟨m, n, hmn, he⟩ : ∃ m n : ℕ, m < n ∧ d.hcA k ^ m = d.hcA k ^ n := by
    by_contra hc
    push Not at hc
    have hinj : Function.Injective fun n : ℕ => d.hcA k ^ n := by
      intro a b hab
      rcases lt_trichotomy a b with h | h | h
      · exact absurd hab (hc a b h)
      · exact h
      · exact absurd hab.symm (hc b a h)
    exact Set.infinite_range_of_injective hinj (hfin.subset (Set.range_subset_iff.2 hmem))
  have hpow : d.hcA k ^ (n - m) = 1 := by
    have : d.hcA k ^ m * d.hcA k ^ (n - m) = d.hcA k ^ m * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hmn.le, mul_one, he]
    exact mul_left_cancel this
  have h0 : n - m ≠ 0 := Nat.sub_ne_zero_of_lt hmn
  simpa [h0] using (pow_eq_one_iff (a := d.hcA k) (n := n - m)).1 hpow

/-- `A_G(𝒪) = A_G(F) ∩ ker H_G` as a positive compact set (compact and open). -/
def kerHcAPC : TopologicalSpace.PositiveCompacts ↥d.AG :=
  ⟨⟨(d.hcA.ker : Set ↥d.AG), d.isCompact_ker_hcA⟩,
    ⟨1, d.isOpen_ker_hcA.mem_nhds d.hcA.ker.one_mem |> mem_interior_iff_mem_nhds.2⟩⟩

/-- **`d_c a`**: the Haar measure on `A_G(F)` giving `A_G(𝒪) = A_G(F) ∩ ker H_G` measure `1`. -/
def dcA : Measure ↥d.AG := Measure.haarMeasure d.kerHcAPC

instance isHaarMeasure_dcA : d.dcA.IsHaarMeasure := by unfold dcA; infer_instance

theorem dcA_ker : d.dcA (d.hcA.ker : Set ↥d.AG) = 1 := Measure.haarMeasure_self

theorem isDcMeasureAG_dcA : d.IsDcMeasureAG d.dcA :=
  ⟨inferInstance, d.hcA.ker, d.isCompact_ker_hcA, d.isMaxCompact_ker_hcA, d.dcA_ker⟩

/-- A Haar measure on `A_G(F)` is right invariant (`A_G(F)` is central in `G(F)`). -/
theorem isMulRightInvariant_AG (μ : Measure ↥d.AG) [μ.IsMulLeftInvariant] :
    μ.IsMulRightInvariant := by
  refine ⟨fun a => ?_⟩
  have e : (fun x : ↥d.AG => x * a) = fun x => a * x := by
    funext x
    exact Subtype.ext (Subgroup.mem_center_iff.mp (d.AG_le_center a.2) (x : ↥d.G))
  rw [e]
  exact map_mul_left_eq_self μ a

/-- **`d_c a` is unique**: the maximal compact subgroup is unique, and two Haar measures giving it
measure `1` are equal. -/
theorem IsDcMeasureAG.unique {μ μ' : Measure ↥d.AG} (h : d.IsDcMeasureAG μ)
    (h' : d.IsDcMeasureAG μ') : μ = μ' := by
  obtain ⟨hμ, K, hK, hKmax, hK1⟩ := h
  obtain ⟨hμ', K', hK', hKmax', hK1'⟩ := h'
  have eK : K = K' := le_antisymm (hKmax' K hK) (hKmax K' hK')
  subst eK
  have e := Measure.isMulLeftInvariant_eq_smul μ' μ
  rw [ENNReal.smul_def] at e
  have h1 := congrArg (fun ν : Measure ↥d.AG => ν (K : Set ↥d.AG)) e
  simp only [smul_apply, hK1, hK1', smul_eq_mul, mul_one] at h1
  rw [e, ← h1, one_smul]

/-! ## Existence of the quotient measure -/

/-- `A_G(F)\G(F) ≃ G(F)/A_G(F)` (the identity on representatives; `A_G` is normal). -/
def cosetEquivGmodAG : CosetSpace d.AG.subtype ≃ d.GmodAG where
  toFun := Quotient.map' id fun a b h => by
    rw [QuotientGroup.rightRel_apply, Subgroup.range_subtype] at h
    show QuotientGroup.leftRel d.AG a b
    rw [QuotientGroup.leftRel_apply]
    exact (Subgroup.Normal.mem_comm_iff inferInstance).1 h
  invFun := Quotient.map' id fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h
    show QuotientGroup.rightRel d.AG.subtype.range a b
    rw [QuotientGroup.rightRel_apply, Subgroup.range_subtype]
    exact (Subgroup.Normal.mem_comm_iff inferInstance).1 h
  left_inv q := by induction q using CosetSpace.ind with | h x => rfl
  right_inv q := by induction q using QuotientGroup.induction_on with | H x => rfl

theorem cosetEquivGmodAG_mk (x : ↥d.G) :
    d.cosetEquivGmodAG (CosetSpace.mk _ x) = (QuotientGroup.mk x : d.GmodAG) := rfl

/-- `cosetEquivGmodAG` as a homeomorphism (both sides carry the quotient topology). -/
def cosetHomeoGmodAG : CosetSpace d.AG.subtype ≃ₜ d.GmodAG where
  toEquiv := d.cosetEquivGmodAG
  continuous_toFun := CosetSpace.continuous_of_comp_mk _ QuotientGroup.continuous_mk
  continuous_invFun := continuous_coinduced_dom.2 (CosetSpace.continuous_mk _)

/-- **The quotient of `dg` by `d_c a` exists** and is a positive finite multiple of
`Measure.haar` on `G(F)/A_G(F)`.  Weil's quotient measure on `A_G(F)\G(F)` (`weil_quotient`),
transported to `G(F)/A_G(F)`, is right invariant (`IsWeilMeasure.map_mulRight` and uniqueness), so
it is `c • Measure.haar` (uniqueness of Haar measures, applied to its inverse), with `c ≠ 0` since a
Weil measure is nonzero and `c ≠ ∞` since it is finite on compacts. -/
theorem exists_isDcQuotientAG :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ d.IsDcQuotientAG (c • Measure.haar) := by
  set ι := d.AG.subtype
  have hemb : IsClosedEmbedding ι := d.isClosed_AG.isClosedEmbedding_subtypeVal
  have hι : Continuous ι := continuous_subtypeVal
  have := d.isMulRightInvariant_AG d.dcA
  obtain ⟨m0, hW, -⟩ := weil_quotient ι hι hemb (Measure.haar : Measure ↥d.G) d.dcA
  set e := d.cosetHomeoGmodAG
  set m : Measure d.GmodAG := m0.map e
  -- the Weil formula on `G(F)/A_G(F)`
  have hWm : ∀ φ : ↥d.G → ℝ, Continuous φ → HasCompactSupport φ →
      ∫ g, φ g ∂Measure.haar = ∫ x, ∫ a, φ (Quotient.out x * (a : ↥d.G)) ∂d.dcA ∂m := by
    intro φ hφ hφc
    rw [hW φ hφ hφc, e.isClosedEmbedding.measurableEmbedding.integral_map]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    -- `out (e q) = out q · a₀` with `a₀ ∈ A_G(F)`
    have hq : (QuotientGroup.mk (CosetSpace.out ι q) : d.GmodAG) = e q := by
      conv_rhs => rw [← CosetSpace.mk_out ι q]
      rfl
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ↥d.AG, Quotient.out (e q) = CosetSpace.out ι q * (a₀ : ↥d.G) := by
      have h := QuotientGroup.mk_out_eq_mul d.AG (CosetSpace.out ι q)
      obtain ⟨a₀, ha₀⟩ := h
      exact ⟨a₀, by rw [← hq]; exact ha₀⟩
    simp only
    rw [ha₀]
    have e1 : ∀ a : ↥d.AG, φ (CosetSpace.out ι q * (a₀ : ↥d.G) * (a : ↥d.G)) =
        (fun b : ↥d.AG => φ (CosetSpace.out ι q * (b : ↥d.G))) (a₀ * a) := by
      intro a; simp [mul_assoc]
    simp_rw [e1]
    rw [integral_mul_left_eq_self (fun b : ↥d.AG => φ (CosetSpace.out ι q * (b : ↥d.G))) a₀]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    show φ ((a : ↥d.G) * CosetSpace.out ι q) = φ (CosetSpace.out ι q * (a : ↥d.G))
    rw [Subgroup.mem_center_iff.mp (d.AG_le_center a.2) (CosetSpace.out ι q)]
  -- right invariance
  have hm0 : ∀ γ : ↥d.G, m0.map (CosetSpace.mulRight ι γ) = m0 := fun γ =>
    (IsWeilMeasure.unique hι hemb hW (hW.map_mulRight γ)).symm
  have hRI : m.IsMulRightInvariant := by
    refine ⟨fun q => ?_⟩
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
    have hcomm : (fun x : d.GmodAG => x * (QuotientGroup.mk γ : d.GmodAG)) ∘ e =
        e ∘ CosetSpace.mulRight ι γ := by
      funext q'
      induction q' using CosetSpace.ind with | h x => rfl
    show (m0.map e).map _ = m0.map e
    rw [Measure.map_map (measurable_mul_const _) e.continuous.measurable, hcomm,
      ← Measure.map_map e.continuous.measurable (CosetSpace.mulRight ι γ).continuous.measurable,
      hm0]
  have hfin0 := hW.isFiniteMeasureOnCompacts hι hemb
  have hfin : IsFiniteMeasureOnCompacts m := by
    refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply e.continuous.measurable hK.isClosed.measurableSet]
    rw [← congrFun e.image_symm K]
    exact (hK.image e.symm.continuous).measure_lt_top
  have hne : m ≠ 0 := by
    intro h0
    have h1 : (m0.map e).map e.symm = m0 := by
      rw [Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
      simp
    exact hW.ne_zero (by rw [← h1]; change m.map e.symm = 0; rw [h0, Measure.map_zero])
  -- `m = c • haar`
  obtain ⟨c, hm⟩ := eq_smul_haar_of_isMulRightInvariant m
  refine ⟨(c : ℝ≥0∞), fun h0 => hne ?_, ENNReal.coe_ne_top, d.dcA,
    d.isDcMeasureAG_dcA, ?_⟩
  · rw [hm, h0, zero_smul]
  · rw [← hm]; exact hWm

/-- **`measGmodAG` is the quotient of `dg` by `d_c a`** (Arthur 1991, §1, p. 11). -/
theorem isDcQuotientAG_measGmodAG : d.IsDcQuotientAG d.measGmodAG :=
  d.dcScaleAG_spec_of_exists d.exists_isDcQuotientAG

/-- **Uniqueness of the constant**: if `c • Measure.haar` (`c ≠ ∞`) is the quotient of `dg` by
`d_c a`, then `c = dcScaleAG`.  (`d_c a` is unique, and a test function `φ ≥ 0` with
`∫ φ dg > 0` pins the constant.) -/
theorem dcScaleAG_eq {c : ℝ≥0∞} (hc : c ≠ ⊤) (h : d.IsDcQuotientAG (c • Measure.haar)) :
    d.dcScaleAG = c := by
  obtain ⟨μ, hμ, hW⟩ := d.isDcQuotientAG_measGmodAG
  obtain ⟨μ', hμ', hW'⟩ := h
  obtain rfl := IsDcMeasureAG.unique d hμ hμ'
  obtain ⟨φ, hφ, hφc, hpos⟩ := exists_integral_pos_of_isOpenPosMeasure (Measure.haar : Measure ↥d.G)
  have h1 := hW φ hφ hφc
  have h2 := hW' φ hφ hφc
  rw [measGmodAG, integral_smul_measure] at h1
  rw [integral_smul_measure] at h2
  set I := ∫ x, ∫ a, φ (Quotient.out x * (a : ↥d.G)) ∂μ ∂(Measure.haar : Measure d.GmodAG)
  have hI : I ≠ 0 := by
    intro hI; rw [hI, smul_zero] at h1; exact hpos.ne' h1
  have e : d.dcScaleAG.toReal = c.toReal := by
    have := h1.symm.trans h2
    simp only [smul_eq_mul] at this
    exact mul_right_cancel₀ hI this
  exact (ENNReal.toReal_eq_toReal_iff' d.dcScaleAG_ne_top hc).1 e

end GGPData

end GSpinGGP
