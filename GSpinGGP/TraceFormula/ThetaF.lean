/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Basic
import GSpinGGP.TraceFormula.SpinorNorm
import GSpinGGP.Literature.TraceFormula
import GSpinGGP.Literature.HarishChandra
import GSpinGGP.Literature.Measure

/-!
# The quasi-character `θ_f` of a strongly cuspidal function

Theory of the function
`thetaF d f` defined in `TraceFormula/Basic.lean` (Thesis §4.8, §7.1; BP §5.5–5.6), and the Weil measure on `H(F)\G(F)/A_G(F)`.

* `isMulRightInvariant_haar_quotient_of_le_center` (generic) and
  `isMulRightInvariant_haar_GmodAG`: Haar measure on `G(F)/A_G(F)` is right invariant, from the
  unimodularity of `G(F)`, because `A_G` is central; hence `weilMeasureHG_spec` (Thesis §7.1).
* `isStronglyCuspidal_iff_inline`: bridge to the form of strong cuspidality in
  `bp_thetaF_exists`.
* `thetaF_unique`: functions representing the same orbital pairing agree on `G_reg(F)`.
* `isQuasiCharacter_congr_regularSet`: a quasi-character only depends on its values on
  `G_reg(F)` (needs `conj_mem_regularSet`, proved from `Ad(G)`-stability of `gspin`, and the
  Harish-Chandra regularity statement `exists_nhds_mul_expA_mem_regularSet`, proved from
  LocalGroups `exists_nhds_isRegularSS_mul_expA`).
* `isFiniteMeasureOnCompacts_weilMeasureHG` (from the defining formula, `Literature/Measure`).
* `chiProj` (`P_χ`, Thesis §7.1) with equivariance, support, local constancy, strong
  cuspidality (`chiProj_isStronglyCuspidal`, Fubini over `A_G × U`) and surjectivity onto
  `ScuspTestFn` (`chiProj_surjective`), all proved from the cutoff `agCutoff` along `A_G(F)`
  (`IsAGCutoff`, `exists_isAGCutoff`; built from the Harish-Chandra map `H_G` of `SpinorNorm.lean`).
* The `χ`-transfer `isThetaF_chiProj`, proved without Fubini: on each fibre of `H_G`,
  `θ_{P_χ f₀} = c χ(b) θ_{κ P_χ f₀}(b ·)` (`chiTransfer_fibre`, `hasGermExpansion_transfer`); and the
  averaging formula `isThetaF_chiProj_avg`, by Fubini on `A_G × G`
  (`integrable_AG_prod`, `orbitalInner_chiProj`) and a finite decomposition of the `A_G`-integrals
  (`integral_char_mul_eq_sum`).
* `thetaF_spec` (key deliverable), `thetaF_zero`, `thetaF_smul`, `thetaF_add`, `thetaF_conj`,
  `thetaF_mul_AG` (on `G_reg(F)`), using `mul_mem_regularSet_of_mem_AG` (`G_reg(F)` is stable
  under `A_G(F)`; proved via `splitCentralGSpin_spec`).  No `sorry` remains in this file.

All equalities for `thetaF` hold on `G_reg(F)` only: `thetaF` is chosen by the epsilon pattern
among functions determined up to null sets.
-/

noncomputable section

open MeasureTheory Topology Filter
open scoped Pointwise NNReal

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

section RightInvariance

variable {B : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B]
  [T2Space B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

/-- **Unimodularity passes to the quotient by a closed central subgroup** (used for
`G(F)/A_G(F)`, Thesis §7.1).  Let `B` be a locally compact, second countable group whose
Haar measure is right invariant, and `A ≤ Z(B)` closed.  Then Haar measure on `B/A` is right
invariant.

Proof: Mathlib's induced Haar measure on the extension `1 → A → B → B/A → 1` gives
`∫_B f = ∫_{B/A} ∫_A f(ḃ a) da dḃ` for `f ∈ C_c(B)`.  For `b ∈ B` the fibre integral of `f(· b)` at
`ḃ'` equals that of `f` at `ḃ' ḃ`, *because `A` is central* (`b' a b = b' b a`).  Right invariance on
`B` then gives `∫_{B/A} F(c ḃ) dc = ∫_{B/A} F(c) dc` for the fibre integral `F` of a nonnegative `f`
with `f(1) > 0`, so the modular character of `B/A` is `1`.  Centrality is essential: in general
`Δ_{B/A}(ḃ)` differs from `Δ_B(b)` by the modulus of conjugation by `b` on `A`. -/
theorem isMulRightInvariant_haar_quotient_of_le_center (A : Subgroup B) [A.Normal]
    (hA : IsClosed (A : Set B)) (hcent : A ≤ Subgroup.center B)
    [MeasurableSpace (B ⧸ A)] [BorelSpace (B ⧸ A)]
    [hB : (Measure.haar : Measure B).IsMulRightInvariant] :
    (Measure.haar : Measure (B ⧸ A)).IsMulRightInvariant := by
  have H := TopologicalGroup.IsSES.ofClosedSubgroup A hA
  have : LocallyCompactSpace A := hA.locallyCompactSpace
  set μA : Measure A := Measure.haar
  set μC : Measure (B ⧸ A) := Measure.haar
  set ν : Measure B := H.inducedMeasure μA μC
  have hν : ν = Measure.haarScalarFactor ν Measure.haar • (Measure.haar : Measure B) :=
    Measure.isMulLeftInvariant_eq_smul ν Measure.haar
  have hνR : ∀ (f : B → ℝ) (b : B), ∫ x, f (x * b) ∂ν = ∫ x, f x ∂ν := by
    intro f b
    rw [hν, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
      integral_mul_right_eq_self f b]
  -- a nonnegative test function with positive integral
  obtain ⟨f₀, f₀_comp, f₀_nonneg, f₀_one⟩ :
      ∃ f : C(B, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 1 ≠ 0 := exists_continuous_nonneg_pos 1
  let f : CompactlySupportedContinuousMap B ℝ := ⟨f₀, f₀_comp⟩
  set F := H.pushforward μA f with hF
  have hFint : ∫ c, F c ∂μC = ∫ x, f x ∂ν := by
    rw [TopologicalGroup.IsSES.integral_inducedMeasure]; rfl
  have hpos : 0 < ∫ x, f x ∂ν :=
    f₀.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero f₀_comp f₀_nonneg f₀_one
  refine ⟨fun g => ?_⟩
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g
  -- the right translate of `f` by `b`
  let fb : CompactlySupportedContinuousMap B ℝ :=
    ⟨⟨fun x => f₀ (x * b), f₀.continuous.comp (continuous_id.mul continuous_const)⟩,
      f₀_comp.comp_homeomorph (Homeomorph.mulRight b)⟩
  have hshift : ∀ c : B ⧸ A, H.pushforward μA fb c = F (c * (b : B ⧸ A)) := by
    intro c
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective c
    have e1 := TopologicalGroup.IsSES.pushforward_apply_apply H μA fb b'
    have e2 := TopologicalGroup.IsSES.pushforward_apply_apply H μA f (b' * b)
    change H.pushforward μA fb (QuotientGroup.mk' A b') = _
    rw [e1]
    have : ((b' : B ⧸ A) * (b : B ⧸ A)) = QuotientGroup.mk' A (b' * b) := rfl
    rw [this, e2]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp only [TopologicalGroup.IsSES.pullback_def]
    change f₀ (b' * (a : B) * b) = f₀ (b' * b * (a : B))
    have hc := Subgroup.mem_center_iff.mp (hcent a.2) b
    rw [mul_assoc, ← hc, mul_assoc]
  have hmapint : ∫ c, F c ∂(Measure.map (· * (b : B ⧸ A)) μC) = ∫ c, F c ∂μC := by
    rw [integral_map (f := fun c => F c) (measurable_mul_const _).aemeasurable
      F.continuous.aestronglyMeasurable]
    simp_rw [← hshift]
    rw [show ∫ c, H.pushforward μA fb c ∂μC = ∫ x, fb x ∂ν by
      rw [TopologicalGroup.IsSES.integral_inducedMeasure]; rfl]
    rw [hFint]
    exact hνR f₀ b
  have hfac := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * (b : B ⧸ A)) μC) μC
  have hne : ∫ c, F c ∂μC ≠ 0 := by rw [hFint]; exact hpos.ne'
  have hone : Measure.haarScalarFactor (Measure.map (· * (b : B ⧸ A)) μC) μC = 1 := by
    apply NNReal.coe_injective
    rw [Measure.haarScalarFactor_eq_integral_div _ _ F.continuous F.hasCompactSupport hne]
    change (∫ c, F c ∂(Measure.map (· * (b : B ⧸ A)) μC)) / (∫ c, F c ∂μC) = _
    rw [hmapint, div_self hne, NNReal.coe_one]
  rw [hfac, hone, one_smul]

end RightInvariance

/-- Abstract form of the `χ`-equivariance of the projection `f₀ ↦ ∫_A χ(a) f₀(a ·)`: for a
character `c` of a group `S` mapping into the centre of `B` (Thesis §7.1). -/
theorem integral_char_mul_central {S B : Type*} [Group S] [Group B] [MeasurableSpace S]
    [MeasurableMul S] (μ : Measure S) [μ.IsMulLeftInvariant] (ι : S →* B) {a' : S}
    (hc : ∀ a : S, ι a * ι a' = ι a' * ι a) (c : S → ℂ) (hcmul : ∀ a b, c (a * b) = c a * c b)
    (hc0 : ∀ a, c a ≠ 0) (f₀ : B → ℂ) (g : B) :
    ∫ a, c a * f₀ (ι a * (ι a' * g)) ∂μ = (c a')⁻¹ * ∫ a, c a * f₀ (ι a * g) ∂μ := by
  set φ : S → ℂ := fun b => c b * f₀ (ι b * g)
  have key : ∀ a : S, c a * f₀ (ι a * (ι a' * g)) = (c a')⁻¹ * φ (a' * a) := by
    intro a
    simp only [φ, hcmul, map_mul]
    rw [← mul_assoc (ι a), hc a, mul_assoc (ι a')]
    field_simp [hc0 a']
  simp_rw [key]
  rw [integral_const_mul, integral_mul_left_eq_self φ a']

/-- Conjugation commutes with multiplication by a central element (abstract group; on the
concrete subgroup towers `group` times out). -/
theorem conj_mul_of_commute {B : Type*} [Group B] {a : B} (ha : ∀ x, a * x = x * a) (y g : B) :
    y⁻¹ * (a * g) * y = a * (y⁻¹ * g * y) := by
  rw [← mul_assoc, ← ha y⁻¹, mul_assoc a, mul_assoc a, mul_assoc]

/-- A compactly supported locally constant function on a locally compact group is invariant under
left translation by a neighbourhood of `1` (uniform local constancy; Thesis §2.3). -/
theorem exists_nhds_one_mul_eq {B Y : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [LocallyCompactSpace B] [Zero Y] {f : B → Y} (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) : ∃ U ∈ 𝓝 (1 : B), ∀ t ∈ U, ∀ x, f (t * x) = f x := by
  obtain ⟨U₀, hU₀c, hU₀⟩ := exists_compact_mem_nhds (1 : B)
  set K' : Set B := U₀⁻¹ * tsupport f
  have hK' : IsCompact K' := hU₀c.inv.mul hc
  have hS : IsOpen {p : B × B | f (p.1 * p.2) = f p.2} := by
    have h1 : IsLocallyConstant (fun p : B × B => (f (p.1 * p.2), f p.2)) :=
      (hf.comp_continuous continuous_mul).prodMk (hf.comp_continuous continuous_snd)
    exact h1 {q | q.1 = q.2}
  have hmem : {p : B × B | f (p.1 * p.2) = f p.2} ∈ 𝓝ˢ (({1} : Set B) ×ˢ K') :=
    hS.mem_nhdsSet.2 fun p hp => by
      obtain ⟨h1, -⟩ := hp
      simp only [Set.mem_singleton_iff] at h1
      simp [h1]
  rw [isCompact_singleton.nhdsSet_prod_eq hK', nhdsSet_singleton, Filter.mem_prod_iff] at hmem
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := hmem
  refine ⟨t₁ ∩ U₀, inter_mem ht₁ hU₀, fun t ht x => ?_⟩
  by_cases hx : x ∈ K'
  · exact hsub (show (t, x) ∈ t₁ ×ˢ t₂ from ⟨ht.1, subset_of_mem_nhdsSet ht₂ hx⟩)
  · have hx1 : x ∉ tsupport f := fun h =>
      hx ⟨1, by simpa using mem_of_mem_nhds hU₀, x, h, one_mul x⟩
    have hx2 : t * x ∉ tsupport f := fun h =>
      hx ⟨t⁻¹, by simpa using ht.2, t * x, h, by simp⟩
    rw [image_eq_zero_of_notMem_tsupport hx1, image_eq_zero_of_notMem_tsupport hx2]

/-- Abstract form of the local constancy of `f₀ ↦ ∫_A c(a) f₀(a ·)` for `f₀ ∈ C_c^∞` and `A`
central. -/
theorem isLocallyConstant_integral_central {S B : Type*} [Group S] [Group B] [TopologicalSpace B]
    [IsTopologicalGroup B] [LocallyCompactSpace B] [MeasurableSpace S] (μ : Measure S)
    (ι : S →* B) (hc : ∀ (a : S) (x : B), ι a * x = x * ι a) (c : S → ℂ) {f₀ : B → ℂ}
    (hf : IsLocallyConstant f₀) (hfc : HasCompactSupport f₀) :
    IsLocallyConstant (fun g => ∫ a, c a * f₀ (ι a * g) ∂μ) := by
  obtain ⟨U, hU, hUf⟩ := exists_nhds_one_mul_eq hf hfc
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hcont : Continuous (fun y : B => y * g⁻¹) := continuous_id.mul continuous_const
  have : (fun y : B => y * g⁻¹) ⁻¹' U ∈ 𝓝 g :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using hU)
  filter_upwards [this] with y hy
  have hyg : y = (y * g⁻¹) * g := by simp
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  simp only
  congr 1
  rw [hyg, ← mul_assoc, hc a, mul_assoc, hUf _ hy]

/-! ## Concrete statements for `d : GGPData F` -/

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- The regular semisimple set is stable under conjugation by `G`, provided `𝔤` is
`Ad(G)`-stable (Thesis §2.1): `x ↦ g x g⁻¹` conjugates left multiplication (so preserves
semisimplicity) and carries `𝔤_x` isomorphically onto `𝔤_{g x g⁻¹}`. -/
theorem conj_mem_regularSet_of_ad {A : Type*} [Ring A] [Algebra F A] (G : Subgroup Aˣ)
    (𝔤 : LieSubalgebra F A)
    (hAd : ∀ g : ↥G, ∀ X ∈ 𝔤, ((g : Aˣ) : A) * X * ((g⁻¹ : Aˣ) : A) ∈ 𝔤)
    (g y : ↥G) (hy : y ∈ regularSet G 𝔤) : g * y * g⁻¹ ∈ regularSet G 𝔤 := by
  obtain ⟨hss, hab⟩ := hy
  set u : Aˣ := (g : Aˣ)
  set z : A := ((y : Aˣ) : A)
  have hc : (((g * y * g⁻¹ : ↥G) : Aˣ) : A) = (u : A) * z * ((u⁻¹ : Aˣ) : A) := rfl
  refine ⟨?_, ?_⟩
  · -- semisimplicity is invariant under conjugation by the linear equivalence `L_u`
    let e : A ≃ₗ[F] A := LinearEquiv.ofLinearMap (LinearMap.mulLeft F (u : A))
      (LinearMap.mulLeft F ((u⁻¹ : Aˣ) : A)) (by ext; simp [← mul_assoc]) (by ext; simp [← mul_assoc])
    change IsSS F (((g * y * g⁻¹ : ↥G) : Aˣ) : A)
    rw [hc]
    refine (LinearEquiv.isSemisimple_iff (f := LinearMap.mulLeft F z) _ e ?_).1 hss
    ext w
    simp [e, mul_assoc]
  · refine ⟨fun X Y => ?_⟩
    obtain ⟨X, hX⟩ := X
    obtain ⟨Y, hY⟩ := Y
    rw [mem_lieCentralizer, hc] at hX hY
    have hmem : ∀ W : A, W ∈ 𝔤 → (u : A) * z * ((u⁻¹ : Aˣ) : A) * W =
        W * ((u : A) * z * ((u⁻¹ : Aˣ) : A)) →
        ((u⁻¹ : Aˣ) : A) * W * (u : A) ∈ lieCentralizer 𝔤 z := by
      intro W hW hWc
      rw [mem_lieCentralizer]
      refine ⟨?_, ?_⟩
      · have := hAd g⁻¹ W hW
        simpa using this
      · have h2 := congrArg (fun T => ((u⁻¹ : Aˣ) : A) * T * (u : A)) hWc
        simp only [mul_assoc, Units.inv_mul, mul_one, Units.inv_mul_cancel_left] at h2
        simpa [mul_assoc] using h2
    have h0 := hab.trivial ⟨_, hmem X hX.1 hX.2⟩ ⟨_, hmem Y hY.1 hY.2⟩
    rw [Subtype.ext_iff, LieSubalgebra.coe_bracket] at h0
    apply Subtype.ext
    rw [LieSubalgebra.coe_bracket]
    simp only [Ring.lie_def, ZeroMemClass.coe_zero] at h0 ⊢
    have h3 := congrArg (fun T => (u : A) * T * ((u⁻¹ : Aˣ) : A)) h0
    simp only [mul_sub, sub_mul, mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one,
      mul_zero, zero_mul] at h3
    simpa [mul_assoc] using h3

namespace GGPData

variable (d : GGPData F)

/-- `G(F)` is totally disconnected (`p`-adic `F`; LocalGroups `totallyDisconnectedSpace_subgroup`,
Thesis §2.1). -/
instance totallyDisconnectedSpace_G : TotallyDisconnectedSpace ↥d.G :=
  totallyDisconnectedSpace_subgroup F d.ambient d.G

/-- `A_G(F)` is locally compact (it is closed in `G(F)`), so it carries a Haar measure
(Thesis §7.1). -/
instance locallyCompactSpace_AG : LocallyCompactSpace ↥d.AG :=
  d.isClosed_AG.locallyCompactSpace

/-! ### The Haar measure on `G(F)/A_G(F)` is right invariant; the Weil measure -/

/-- The Haar measure on `G(F)/A_G(F)` is right invariant: from the unimodularity of
`G(F)` (`haar_G_isMulRightInvariant`) because `A_G(F)` is closed and central
(`isMulRightInvariant_haar_quotient_of_le_center`; Thesis §2.4, §7.1). -/
instance isMulRightInvariant_haar_GmodAG :
    (Measure.haar : Measure d.GmodAG).IsMulRightInvariant :=
  isMulRightInvariant_haar_quotient_of_le_center d.AG d.isClosed_AG d.AG_le_center

/-- **The Weil measure on `H(F)\G(F)/A_G(F)`** (Thesis §7.1):
`weilMeasureHG d` satisfies the quotient-integral formula for the Haar measures on `G(F)/A_G(F)`
and `H(F)/A_{G,H}(F)`.  From `weil_quotient` (Bourbaki), `isClosedEmbedding_toGmodAG`, the
unimodularity of `G(F)` (via `isMulRightInvariant_haar_GmodAG`) and of `H(F)/A_{G,H}(F)`
(`isMulRightInvariant_haar_HmodAGH`). -/
theorem weilMeasureHG_spec :
    IsWeilMeasure d.toGmodAG Measure.haar Measure.haar d.weilMeasureHG :=
  d.weilMeasureHG_spec_of_isMulRightInvariant d.isMulRightInvariant_haar_GmodAG

/-- **The Weil measure on `H(F)\G(F)/A_G(F)` is finite on compact sets**, from its defining formula (`IsWeilMeasure.isFiniteMeasureOnCompacts`), so
`weil_quotient` did not need strengthening. -/
instance isFiniteMeasureOnCompacts_weilMeasureHG : IsFiniteMeasureOnCompacts d.weilMeasureHG := by
  have := d.isMulRightInvariant_haar_HmodAGH
  exact IsWeilMeasure.isFiniteMeasureOnCompacts d.continuous_toGmodAG
    d.isClosedEmbedding_toGmodAG d.weilMeasureHG_spec

end GGPData

/-! ### `Ad(G)`-stability of `𝔤` and conjugation stability of `G_reg` -/

section GSpinAd

variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]

open CliffordAlgebra in
/-- `gspin(V)` is stable under conjugation by `GSpin(V)` (Thesis Prop. 5.1.3.1: it is the Lie
algebra of `GSpin(V)`): for `g ∈ GSpin(V)` and `X ∈ gspin(V)`, `g X g⁻¹` is even and
`[g X g⁻¹, v] = g [X, g⁻¹ v g] g⁻¹ ∈ V`. -/
theorem conj_mem_gspin (Q : QuadraticForm K V) (g : GSpin Q) {X : CliffordAlgebra Q}
    (hX : X ∈ gspin Q) :
    ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * X *
      (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ gspin Q := by
  obtain ⟨hX0, hX⟩ := hX
  set u : (CliffordAlgebra Q)ˣ := (g : (CliffordAlgebra Q)ˣ)
  have hg := g.2
  refine ⟨?_, fun v => ?_⟩
  · exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hg.1 hX0) (g⁻¹ : GSpin Q).2.1
  · obtain ⟨w, hw⟩ := hg.2.2 v
    -- `ι v = u ι w u⁻¹`
    have hv : ι Q v = (u : CliffordAlgebra Q) * ι Q w * ((u⁻¹ : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q) := by
      rw [hw]
      simp [u, mul_assoc]
    obtain ⟨t, ht⟩ := hX w
    obtain ⟨r, hr⟩ := hg.2.1 t
    refine ⟨r, ?_⟩
    rw [hr, hv, Ring.lie_def]
    rw [Ring.lie_def] at ht
    rw [ht]
    simp only [mul_sub, sub_mul, mul_assoc, Units.inv_mul_cancel_left]
    rfl

end GSpinAd

namespace GGPData

variable (d : GGPData F)

/-- `𝔤 = gspin(W) × gspin(V)` is `Ad(G)`-stable. -/
theorem conj_mem_lie (g : ↥d.G) {X : d.ambient} (hX : X ∈ d.lie) :
    ((g : d.ambientˣ) : d.ambient) * X * ((g⁻¹ : d.ambientˣ) : d.ambient) ∈ d.lie :=
  ⟨conj_mem_gspin d.QW (d.fst g) hX.1, conj_mem_gspin d.QV (d.snd g) hX.2⟩

end GGPData

/-- `G_reg(F)` is stable under conjugation by `G(F)` (Thesis §2.1). -/
theorem conj_mem_regularSet (d : GGPData F) (g y : ↥d.G) (hy : y ∈ regularSet d.G d.lie) :
    g * y * g⁻¹ ∈ regularSet d.G d.lie :=
  conj_mem_regularSet_of_ad d.G d.lie (fun g _ hX => d.conj_mem_lie g hX) g y hy

/-! ### Strong cuspidality: bridge to the inline form of `bp_thetaF_exists` -/

variable (d : GGPData F) (χ : CentralCharOn d)

/-- Strong cuspidality in the form used by `bp_thetaF_exists` (Thesis §4.5; BP §5.1): for every proper
flag pair and `p ∈ P(F)`, `∫_{U(F)} f(p u) du = 0` (no integrability clause). -/
def IsStronglyCuspidalInline (f : ↥d.G → ℂ) : Prop :=
  ∀ (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV), d.IsProperFlagPair FW FV →
    ∀ p ∈ d.whittB FW FV, ∫ u : ↥(d.whittU FW FV), f (p * u) ∂Measure.haar = 0

/-- `IsStronglyCuspidal` implies the inline form of `bp_thetaF_exists` (drop integrability). -/
theorem IsStronglyCuspidal.inline {f : ↥d.G → ℂ} (hf : IsStronglyCuspidal d f) :
    IsStronglyCuspidalInline d f :=
  fun FW FV h p hp => (hf FW FV h p hp).2

/-- For `f ∈ C_c^∞(G(F))`, `u ↦ f(p u)` is integrable on `U(F)` (it is continuous with compact
support, `U(F)` being closed). -/
theorem integrable_parabolicU_of_testFunctions {f : ↥d.G → ℂ} (hf : f ∈ testFunctions ↥d.G)
    (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) (p : ↥d.G) :
    Integrable (fun u : ↥(d.whittU FW FV) => f (p * u)) Measure.haar := by
  have hemb : IsClosedEmbedding (fun u : ↥(d.whittU FW FV) => p * (u : ↥d.G)) :=
    (Homeomorph.mulLeft p).isClosedEmbedding.comp
      (d.isClosed_whittU FW FV).isClosedEmbedding_subtypeVal
  exact (hf.1.continuous.comp hemb.continuous).integrable_of_hasCompactSupport
    (hf.2.comp_isClosedEmbedding hemb)

/-- **Bridge to `bp_thetaF_exists`**: on `C_c^∞(G(F))` the two forms of
strong cuspidality (Thesis §4.5) agree. -/
theorem isStronglyCuspidal_iff_inline {f : ↥d.G → ℂ} (hf : f ∈ testFunctions ↥d.G) :
    IsStronglyCuspidal d f ↔ IsStronglyCuspidalInline d f :=
  ⟨IsStronglyCuspidal.inline d, fun h FW FV hFV p hp =>
    ⟨integrable_parabolicU_of_testFunctions d hf FW FV p, h FW FV hFV p hp⟩⟩

/-- `bp_thetaF_exists` (BP Thm 5.5.1) applied with the inline cuspidality predicate of this file (checks that
the bridge matches the axiom's hypothesis exactly). -/
theorem bp_thetaF_exists_of_inline {f₀ : ↥d.G → ℂ} (hf₀ : f₀ ∈ testFunctions ↥d.G)
    (h : IsStronglyCuspidalInline d f₀) :
    ∃ θ : ↥d.G → ℂ, LocallyIntegrable θ Measure.haar ∧
      ContinuousOn θ (regularSet d.G d.lie) ∧
      (∀ ψ : NontrivialAddChar F, IsQuasiCharacter d.G d.lie d.bilin ψ θ) ∧
      ∀ f' ∈ testFunctions ↥d.G,
        Integrable (fun x : d.GmodAG => orbitalInner d f₀ f' (Quotient.out x)) Measure.haar ∧
        ∫ g, θ g * f' g ∂Measure.haar = orbitalPairing d f₀ f' :=
  LitTF.bp_thetaF_exists d f₀ hf₀ h

/-! ### Uniqueness of `θ_f` on the regular set -/

/-- Two functions representing the same orbital pairing agree almost everywhere (separation by test
functions, Thesis Ch. 1; Representations `ae_eq_of_integral_testFunctions`). -/
theorem ae_eq_of_isThetaF {f θ₁ θ₂ : ↥d.G → ℂ} (h₁ : IsThetaF d f θ₁) (h₂ : IsThetaF d f θ₂) :
    θ₁ =ᵐ[(Measure.haar : Measure ↥d.G)] θ₂ :=
  ae_eq_of_integral_testFunctions h₁.1 h₂.1 fun f' hf' => by rw [h₁.2.2 f' hf', h₂.2.2 f' hf']

/-- **Uniqueness of `θ_f` on `G_reg(F)`** (Thesis §4.8): two functions representing the
orbital pairing of `f` agree on the regular set, since they agree almost everywhere and are
continuous on the open set `G_reg(F)` (`hc_regularSet_open_conull`), on which Haar measure is
positive on nonempty open sets. -/
theorem thetaF_unique {f θ₁ θ₂ : ↥d.G → ℂ} (h₁ : IsThetaF d f θ₁) (h₂ : IsThetaF d f θ₂) :
    Set.EqOn θ₁ θ₂ (regularSet d.G d.lie) :=
  Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae (ae_eq_of_isThetaF d h₁ h₂))
    (hc_regularSet_open_conull d).1 h₁.2.1 h₂.2.1

/-- `thetaF d f` agrees on `G_reg(F)` with any function representing the orbital pairing of `f`. -/
theorem eqOn_thetaF {f θ : ↥d.G → ℂ} (h : IsThetaF d f θ) :
    Set.EqOn (thetaF d f) θ (regularSet d.G d.lie) :=
  thetaF_unique d (isThetaF_thetaF_of_exists d f ⟨θ, h⟩) h

/-! ### Quasi-characters only see the regular set -/

/-- **Regularity near a semisimple point** (Harish-Chandra; Thesis §4.1.1, BP §4.1, the setting of
the local expansion of quasi-characters): if `x ∈ G(F)` is semisimple, then for `X ∈ 𝔤_x(F)` close to
`0` and regular semisimple in `𝔤_x`, the element `x·exp(X)` is regular semisimple in `G`.

This is the generic `exists_nhds_isRegularSS_mul_expA` (LocalGroups §4b): `exp X ∈ F[X]` is
semisimple and commutes with `x`, so `x exp X` is semisimple; and `𝔤_{x exp X} ⊆ (𝔤_x)_X`, which
is abelian (proved over `F` by a norm estimate for `ad x` on its range, without eigenvalues). -/
theorem exists_nhds_mul_expA_mem_regularSet (x : ↥d.G) (hx : IsSS F ((x : d.ambientˣ) : d.ambient)) :
    ∃ ω ∈ 𝓝 (0 : d.ambient), ∀ X ∈ ω, X ∈ lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient) →
      IsRegularSS (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) X →
      ∀ y : ↥d.G, ((y : d.ambientˣ) : d.ambient) = ((x : d.ambientˣ) : d.ambient) * expA F X →
        y ∈ regularSet d.G d.lie := by
  obtain ⟨ω, hω, h⟩ := exists_nhds_isRegularSS_mul_expA F d.lie hx (x : d.ambientˣ).isUnit
  refine ⟨ω, hω, fun X hX hXc hXr y hy => ?_⟩
  change IsRegularSS d.lie ((y : d.ambientˣ) : d.ambient)
  rw [hy]
  exact h X hX hXc hXr

/-- **A quasi-character only depends on its values on `G_reg(F)`** (as asserted in the docstring of
`IsQuasiCharacter`, Thesis §4.1.1): conjugation invariance is only required at regular points, and
the local expansions only evaluate at `x·exp(X)` with `X` regular in `𝔤_x` and small, which is
regular (`exists_nhds_mul_expA_mem_regularSet`). -/
theorem isQuasiCharacter_congr_regularSet (ψ : NontrivialAddChar F) {θ θ' : ↥d.G → ℂ}
    (h : IsQuasiCharacter d.G d.lie d.bilin ψ θ) (heq : Set.EqOn θ θ' (regularSet d.G d.lie)) :
    IsQuasiCharacter d.G d.lie d.bilin ψ θ' := by
  refine ⟨fun g y hy => ?_, fun x hx => ?_⟩
  · rw [← heq (conj_mem_regularSet d g y hy), ← heq hy, h.1 g y hy]
  · obtain ⟨c, hfin, ω, hω, hexp⟩ := h.2 x hx
    obtain ⟨ω', hω', hreg⟩ := exists_nhds_mul_expA_mem_regularSet d x hx
    refine ⟨c, hfin, ω ∩ ω', inter_mem hω hω', fun X hX hXc hXr y hy => ?_⟩
    rw [← heq (hreg X hX.2 hXc hXr y hy)]
    exact hexp X hX.1 hXc hXr y hy

/-! ### Projection to `χ`-equivariant functions -/

/-- **The projection `P_χ`** (Thesis §7.1):
`(P_χ f₀)(g) = ∫_{A_G(F)} χ(a) f₀(a g) da`, for the Haar measure on `A_G(F)`.  It maps
`C_c^∞(G(F))` to `χ⁻¹`-equivariant functions, compactly supported mod `A_G(F)`. -/
def chiProj (f₀ : ↥d.G → ℂ) (g : ↥d.G) : ℂ :=
  ∫ a : ↥d.AG, ((χ.toHom a : Circle) : ℂ) * f₀ ((a : ↥d.G) * g) ∂Measure.haar

/-- `P_χ f₀(a g) = χ(a)⁻¹ P_χ f₀(g)` (Thesis §7.1): substitute `a ↦ a a'⁻¹` in `A_G(F)`. -/
theorem chiProj_isChiEquivariant (f₀ : ↥d.G → ℂ) : IsChiEquivariant d χ (chiProj d χ f₀) := by
  intro a' g
  have hc : ∀ a : ↥d.AG, (a : ↥d.G) * (a' : ↥d.G) = (a' : ↥d.G) * a := fun a =>
    (Subgroup.mem_center_iff.mp (d.AG_le_center a'.2) a)
  have h := integral_char_mul_central Measure.haar d.AG.subtype hc
    (fun a => ((χ.toHom a : Circle) : ℂ)) (fun a b => by simp) (fun a => Circle.coe_ne_zero _)
    f₀ g
  unfold chiProj
  rw [Circle.coe_inv]
  exact h

/-- `P_χ f₀` is supported in `A_G(F) · supp f₀`. -/
theorem chiProj_hasCompactSupportModAG {f₀ : ↥d.G → ℂ} (hf₀ : HasCompactSupport f₀) :
    HasCompactSupportModAG d (chiProj d χ f₀) := by
  refine ⟨tsupport f₀, hf₀, fun g hg => ?_⟩
  by_contra hmem
  apply hg
  unfold chiProj
  refine integral_eq_zero_of_ae (Eventually.of_forall fun a => ?_)
  have : f₀ ((a : ↥d.G) * g) = 0 := by
    by_contra hne
    apply hmem
    refine ⟨(a : ↥d.G)⁻¹, d.AG.inv_mem a.2, (a : ↥d.G) * g,
      subset_tsupport f₀ hne, ?_⟩
    simp
  simp [this]

/-- `P_χ f₀` is locally constant for `f₀ ∈ C_c^∞(G(F))` (`f₀` is invariant under left translation by a
neighbourhood of `1`, and `A_G` is central). -/
theorem chiProj_isLocallyConstant {f₀ : ↥d.G → ℂ} (hf₀ : f₀ ∈ testFunctions ↥d.G) :
    IsLocallyConstant (chiProj d χ f₀) :=
  isLocallyConstant_integral_central Measure.haar d.AG.subtype
    (fun a x => (Subgroup.mem_center_iff.mp (d.AG_le_center a.2) x).symm)
    (fun a => ((χ.toHom a : Circle) : ℂ)) hf₀.1 hf₀.2

/-! ### The cutoff `κ` along `A_G(F)`

`κ = c⁻¹ · 1_{H_G⁻¹(D)}` for the Harish-Chandra map `H_G` (`SpinorNorm.lean`), a set `D` of
representatives of `H_G`-values modulo `H_G(A_G(F))` and `c = vol(A_G(F) ∩ ker H_G)`. -/

/-- `κ` is a **cutoff along `A_G(F)`** (used for the surjectivity of `P_χ`):
`κ = 1_D ∘ H_G` normalized, for the Harish-Chandra map `H_G` and a fundamental domain `D` of the
lattice `H_G(A_G(F))` in `H_G(G(F))`.  It is locally constant, its `A_G(F)`-average is `1`, it is
compactly supported on each `A_G(F)·C` with `C` compact, conjugation invariant and invariant under
right translation by unipotent radicals of parabolic subgroups (`H_G` is a homomorphism to an
abelian group, trivial on unipotent elements). -/
structure IsAGCutoff (κ : ↥d.G → ℂ) : Prop where
  isLocallyConstant : IsLocallyConstant κ
  integral_AG : ∀ g : ↥d.G, ∫ a : ↥d.AG, κ ((a : ↥d.G) * g) ∂Measure.haar = 1
  isCompact_inter : ∀ C : Set ↥d.G, IsCompact C →
    IsCompact (tsupport κ ∩ ((d.AG : Set ↥d.G) * C))
  conj : ∀ x g : ↥d.G, κ (x * g * x⁻¹) = κ g
  mul_whittU : ∀ (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) (p u : ↥d.G),
    u ∈ d.whittU FW FV → κ (p * u) = κ p

namespace GGPData

/-- `H_G` restricted to `A_G(F)`. -/
def hcA : ↥d.AG →* HCVal := d.hcG.comp d.AG.subtype

theorem hcA_apply (a : ↥d.AG) : d.hcA a = d.hcG (a : ↥d.G) := rfl

/-- A set of representatives of `HCVal / H_G(A_G(F))` (a "fundamental domain" of the lattice). -/
def hcDomain : Set HCVal := Set.range (fun q : HCVal ⧸ d.hcA.range => Quotient.out q)

/-- Each coset `t · H_G(A_G)` meets `D` in exactly one point: `H_G(a) t ∈ D` iff `H_G(a) = H_G(a₀)`
for one `a₀ ∈ A_G(F)`. -/
theorem exists_hcDomain (t : HCVal) :
    ∃ a₀ : ↥d.AG, ∀ a : ↥d.AG, d.hcA a * t ∈ d.hcDomain ↔ d.hcA a = d.hcA a₀ := by
  set q : HCVal ⧸ d.hcA.range := QuotientGroup.mk t
  have hq : (QuotientGroup.mk (Quotient.out q) : HCVal ⧸ d.hcA.range) = q := QuotientGroup.out_eq' q
  obtain ⟨a₀, ha₀⟩ : t⁻¹ * Quotient.out q ∈ d.hcA.range := QuotientGroup.eq.1 hq.symm
  have e1 : t * d.hcA a₀ = Quotient.out q := by rw [ha₀, mul_inv_cancel_left]
  refine ⟨a₀, fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨q', hq'⟩
    simp only at hq'
    have h1 : (QuotientGroup.mk (d.hcA a * t) : HCVal ⧸ d.hcA.range) = q := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (MonoidHom.mem_range.2 ⟨a, rfl⟩),
        one_mul]
    have h2 : q' = q := by
      rw [← h1, ← hq', QuotientGroup.out_eq']
    rw [h2] at hq'
    have h3 : d.hcA a * t = d.hcA a₀ * t :=
      calc d.hcA a * t = Quotient.out q := hq'.symm
        _ = t * d.hcA a₀ := e1.symm
        _ = d.hcA a₀ * t := mul_comm _ _
    exact mul_right_cancel h3
  · intro h
    refine ⟨q, ?_⟩
    change Quotient.out q = d.hcA a * t
    rw [h, ← e1, mul_comm]

/-- `A_G(F) ∩ ker H_G` is open in `A_G(F)` (`H_G` is locally constant). -/
theorem isOpen_ker_hcA : IsOpen (d.hcA.ker : Set ↥d.AG) :=
  (d.isLocallyConstant_hcG.comp_continuous continuous_subtype_val).isOpen_fiber 1

/-- `A_G(F) ∩ ker H_G` is compact (`isCompact_AG_inter_ker_hcG`). -/
theorem isCompact_ker_hcA : IsCompact (d.hcA.ker : Set ↥d.AG) := by
  have e : (d.hcA.ker : Set ↥d.AG) =
      Subtype.val ⁻¹' ((d.AG : Set ↥d.G) ∩ {g | d.hcG g = 1}) := by
    ext a
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_inter_iff,
      Set.mem_ofPred_eq, hcA_apply]
    exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
  rw [e]
  exact d.isClosed_AG.isClosedEmbedding_subtypeVal.isCompact_preimage d.isCompact_AG_inter_ker_hcG

/-- The normalizing constant `c = vol(A_G(F) ∩ ker H_G)`. -/
def hcVol : ℝ := (Measure.haar (d.hcA.ker : Set ↥d.AG)).toReal

theorem hcVol_pos : 0 < d.hcVol :=
  ENNReal.toReal_pos (d.isOpen_ker_hcA.measure_pos Measure.haar ⟨1, d.hcA.ker.one_mem⟩).ne'
    d.isCompact_ker_hcA.measure_lt_top.ne

/-- The preimage under `H_G|_{A_G}` of a finite set is compact (a finite union of cosets of the
compact group `A_G(F) ∩ ker H_G`). -/
theorem isCompact_preimage_hcA {S : Set HCVal} (hS : S.Finite) : IsCompact (d.hcA ⁻¹' S) := by
  rw [← Set.biUnion_preimage_singleton]
  refine hS.isCompact_biUnion fun s _ => ?_
  by_cases h : ∃ a, d.hcA a = s
  · obtain ⟨a, rfl⟩ := h
    have e : d.hcA ⁻¹' {d.hcA a} = (fun b => a * b) '' (d.hcA.ker : Set ↥d.AG) := by
      ext b
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image, SetLike.mem_coe,
        MonoidHom.mem_ker]
      constructor
      · intro hb
        refine ⟨a⁻¹ * b, by rw [map_mul, map_inv, hb, inv_mul_cancel], mul_inv_cancel_left _ _⟩
      · rintro ⟨c, hc, rfl⟩
        rw [map_mul, hc, mul_one]
    rw [e]
    exact d.isCompact_ker_hcA.image (Homeomorph.mulLeft a).continuous
  · push Not at h
    have : d.hcA ⁻¹' {s} = ∅ := Set.eq_empty_iff_forall_notMem.2 fun a ha => h a ha
    rw [this]; exact isCompact_empty

/-- `H_G` takes finitely many values on a compact set. -/
theorem finite_image_hcG {C : Set ↥d.G} (hC : IsCompact C) : (d.hcG '' C).Finite := by
  have : CompactSpace C := isCompact_iff_compactSpace.1 hC
  rw [Set.image_eq_range]
  exact (d.isLocallyConstant_hcG.comp_continuous continuous_subtype_val).range_finite

open scoped Classical in
/-- **The cutoff** `κ(g) = c⁻¹ · 1_D(H_G(g))`. -/
def agCutoff : ↥d.G → ℂ := fun g => if d.hcG g ∈ d.hcDomain then ((d.hcVol : ℂ))⁻¹ else 0

theorem isLocallyConstant_agCutoff : IsLocallyConstant d.agCutoff := by
  classical
  exact IsLocallyConstant.comp d.isLocallyConstant_hcG
    (fun t => if t ∈ d.hcDomain then ((d.hcVol : ℂ))⁻¹ else 0)

/-- Preimages under `H_G` are closed (and open). -/
theorem isClosed_preimage_hcG (S : Set HCVal) : IsClosed (d.hcG ⁻¹' S) :=
  isOpen_compl_iff.1 (by rw [← Set.preimage_compl]; exact d.isLocallyConstant_hcG _)

theorem tsupport_agCutoff_subset : tsupport d.agCutoff ⊆ d.hcG ⁻¹' d.hcDomain := by
  classical
  refine closure_minimal (fun g hg => ?_) (d.isClosed_preimage_hcG _)
  by_contra h
  exact hg (by simp only [agCutoff]; exact ite_eq_right h)

end GGPData

set_option maxHeartbeats 1000000 in
/-- `agCutoff` is a cutoff along `A_G(F)`. -/
theorem isAGCutoff_agCutoff : IsAGCutoff d d.agCutoff := by
  classical
  have hloc := d.isLocallyConstant_hcG
  refine ⟨d.isLocallyConstant_agCutoff, fun g => ?_, fun C hC => ?_,
    fun x g => ?_, fun FW FV p u hu => ?_⟩
  · -- `∫_{A_G} κ(a g) da = c⁻¹ vol(a₀ (A_G ∩ ker H_G)) = 1`
    obtain ⟨a₀, ha₀⟩ := d.exists_hcDomain (d.hcG g)
    set E : Set ↥d.AG := {a | d.hcA a * d.hcG g ∈ d.hcDomain}
    have hE : E = (fun a => a₀⁻¹ * a) ⁻¹' (d.hcA.ker : Set ↥d.AG) := by
      ext a
      simp only [E, Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker,
        map_mul, map_inv, ha₀ a]
      rw [inv_mul_eq_one, eq_comm]
    have hEo : IsOpen E := by
      have : E = (fun a : ↥d.AG => d.hcG ((a : ↥d.G) * g)) ⁻¹' d.hcDomain := by
        ext a; simp [E, GGPData.hcA_apply]
      rw [this]
      exact (hloc.comp_continuous (continuous_subtype_val.mul continuous_const)) _
    have hmemE : ∀ a : ↥d.AG, a ∈ E ↔ d.hcG ((a : ↥d.G) * g) ∈ d.hcDomain := fun a => by
      rw [map_mul]; exact Iff.rfl
    have hfun : (fun a : ↥d.AG => d.agCutoff ((a : ↥d.G) * g)) =
        E.indicator (fun _ => ((d.hcVol : ℂ))⁻¹) := by
      funext a
      by_cases h : a ∈ E
      · rw [Set.indicator_of_mem h]; exact ite_eq_left ((hmemE a).1 h)
      · rw [Set.indicator_of_notMem h]; exact ite_eq_right (mt (hmemE a).2 h)
    rw [hfun, integral_indicator_const _ hEo.measurableSet, hE, Measure.real,
      measure_preimage_mul]
    change d.hcVol • ((d.hcVol : ℂ))⁻¹ = 1
    rw [Complex.real_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 d.hcVol_pos.ne')]
  · -- `tsupport κ ∩ A_G C` lies in finitely many sets `a_t (A_G ∩ ker H_G) C`
    have hT : (d.hcG '' C).Finite := by
      have : CompactSpace C := isCompact_iff_compactSpace.1 hC
      rw [Set.image_eq_range]
      exact (hloc.comp_continuous continuous_subtype_val).range_finite
    choose a₀ ha₀ using fun t : HCVal => d.exists_hcDomain t
    have hpiece : ∀ t : HCVal, IsCompact ((Subtype.val : ↥d.AG → ↥d.G) ''
        ((fun a : ↥d.AG => a₀ t * a) '' (d.hcA.ker : Set ↥d.AG)) * C) := fun t =>
      d.isCompact_image_mul hC d.isCompact_ker_hcA (a₀ t)
    have hKc : IsCompact (⋃ t ∈ d.hcG '' C, (Subtype.val : ↥d.AG → ↥d.G) ''
        ((fun a : ↥d.AG => a₀ t * a) '' (d.hcA.ker : Set ↥d.AG)) * C) :=
      hT.isCompact_biUnion fun t _ => hpiece t
    refine hKc.of_isClosed_subset ((isClosed_tsupport _).inter (d.isClosed_AG_mul hC)) ?_
    rintro g ⟨hgs, a, ha, c, hc, rfl⟩
    have hD := d.tsupport_agCutoff_subset hgs
    simp only [Set.mem_preimage, map_mul] at hD
    set a' : ↥d.AG := ⟨a, ha⟩
    have hmem : d.hcA a' = d.hcA (a₀ (d.hcG c)) := (ha₀ (d.hcG c) a').1 hD
    have hk : (a₀ (d.hcG c))⁻¹ * a' ∈ d.hcA.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      exact inv_mul_eq_one.2 hmem.symm
    exact Set.mem_biUnion (x := d.hcG c) ⟨c, hc, rfl⟩
      ⟨a, ⟨_, ⟨(a₀ (d.hcG c))⁻¹ * a', hk, mul_inv_cancel_left _ _⟩, rfl⟩, c, hc, rfl⟩
  · simp only [GGPData.agCutoff, d.hcG_conj]
  · simp only [GGPData.agCutoff, d.hcG_mul_whittU p hu]

/-- **A cutoff along `A_G(F)` exists**: `agCutoff`, built from the Harish-Chandra
map `H_G` (`SpinorNorm.lean`). -/
theorem exists_isAGCutoff : ∃ κ : ↥d.G → ℂ, IsAGCutoff d κ := ⟨_, isAGCutoff_agCutoff d⟩

/-- The `A_G`-support of `a ↦ f₀(a x)` for `x ∈ p U` is compact, uniformly in `u ∈ U`: if
`f₀(a p u) ≠ 0` then `H_G(a) H_G(p) ∈ H_G(supp f₀)` (`H_G(u) = 1`), a finite set. -/
theorem exists_isCompact_AG_support {f₀ : ↥d.G → ℂ} (hf₀ : HasCompactSupport f₀)
    (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) (p : ↥d.G) :
    ∃ Ap : Set ↥d.AG, IsCompact Ap ∧ ∃ Up : Set ↥(d.whittU FW FV), IsCompact Up ∧
      ∀ (a : ↥d.AG) (u : ↥(d.whittU FW FV)), f₀ ((a : ↥d.G) * (p * u)) ≠ 0 → a ∈ Ap ∧ u ∈ Up := by
  set S := (fun s => s * (d.hcG p)⁻¹) '' (d.hcG '' tsupport f₀)
  have hS : S.Finite := (d.finite_image_hcG hf₀).image _
  refine ⟨d.hcA ⁻¹' S, d.isCompact_preimage_hcA hS, ?_⟩
  set L : Set ↥d.G := (Subtype.val '' (d.hcA ⁻¹' S))⁻¹ * tsupport f₀
  have hL : IsCompact L :=
    ((d.isCompact_preimage_hcA hS).image continuous_subtype_val).inv.mul hf₀
  have hemb : IsClosedEmbedding (fun u : ↥(d.whittU FW FV) => p * (u : ↥d.G)) :=
    (Homeomorph.mulLeft p).isClosedEmbedding.comp
      (d.isClosed_whittU FW FV).isClosedEmbedding_subtypeVal
  refine ⟨_, hemb.isCompact_preimage hL, fun a u h => ?_⟩
  have hmem : (a : ↥d.G) * (p * u) ∈ tsupport f₀ := subset_tsupport f₀ h
  have ha : a ∈ d.hcA ⁻¹' S := by
    refine ⟨d.hcG ((a : ↥d.G) * (p * u)), ⟨_, hmem, rfl⟩, ?_⟩
    simp only [map_mul, d.hcG_eq_one_of_mem_whittU u.2, mul_one, GGPData.hcA_apply,
      mul_inv_cancel_right]
  refine ⟨ha, ?_⟩
  show p * (u : ↥d.G) ∈ L
  refine ⟨(a : ↥d.G)⁻¹, ?_, _, hmem, by simp⟩
  show ((a : ↥d.G)⁻¹)⁻¹ ∈ Subtype.val '' (d.hcA ⁻¹' S)
  rw [inv_inv]
  exact ⟨a, ha, rfl⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
/-- `P_χ` preserves strong cuspidality (Thesis §7.1):
`∫_U P_χ f₀(p u) du = ∫_{A_G} χ(a) ∫_U f₀(a p u) du da = 0`, including integrability on `U(F)`.
The integrand is compactly supported on `A_G(F) × U(F)` (`exists_isCompact_AG_support`, via
`H_G`), so Fubini applies; `a p ∈ P` since `A_G ≤ P` (`AG_le_whittB`). -/
theorem chiProj_isStronglyCuspidal {f₀ : ↥d.G → ℂ} (hf₀ : f₀ ∈ testFunctions ↥d.G)
    (hcusp : IsStronglyCuspidalInline d f₀) : IsStronglyCuspidal d (chiProj d χ f₀) := by
  intro FW FV hFV p hp
  obtain ⟨Ap, hAp, Up, hUp, hsupp⟩ := exists_isCompact_AG_support d hf₀.2 FW FV p
  have hφc : Continuous (chiProj d χ f₀) := (chiProj_isLocallyConstant d χ hf₀).continuous
  have hcontU : Continuous (fun u : ↥(d.whittU FW FV) => p * (u : ↥d.G)) :=
    continuous_const.mul continuous_subtype_val
  refine ⟨?_, ?_⟩
  · -- integrability: continuous with compact support `Up`
    refine (hφc.comp hcontU).integrable_of_hasCompactSupport (HasCompactSupport.intro hUp ?_)
    intro u hu
    simp only [Function.comp_apply, chiProj]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun a => ?_)
    by_contra h
    have h' : f₀ ((a : ↥d.G) * (p * u)) ≠ 0 := fun h0 => h (by simp [h0])
    exact hu (hsupp a u h').2
  · -- Fubini over `A_G(F) × U(F)`
    set Φ : ↥d.AG → ↥(d.whittU FW FV) → ℂ :=
      fun a u => ((χ.toHom a : Circle) : ℂ) * f₀ ((a : ↥d.G) * (p * u))
    have hΦc : Continuous (Function.uncurry Φ) := by
      refine ((continuous_subtype_val.comp (χ.continuous.comp continuous_fst))).mul
        (hf₀.1.continuous.comp ?_)
      exact (continuous_subtype_val.comp continuous_fst).mul
        (continuous_const.mul (continuous_subtype_val.comp continuous_snd))
    have hΦs : HasCompactSupport (Function.uncurry Φ) := by
      refine HasCompactSupport.intro (hAp.prod hUp) fun x hx => ?_
      by_contra h
      have h' : f₀ ((x.1 : ↥d.G) * (p * x.2)) ≠ 0 := fun h0 =>
        h (show Φ x.1 x.2 = 0 by simp only [Φ, h0, mul_zero])
      exact hx ⟨(hsupp x.1 x.2 h').1, (hsupp x.1 x.2 h').2⟩
    have : SecondCountableTopology ↥d.AG :=
      Topology.IsEmbedding.subtypeVal.secondCountableTopology
    have : SecondCountableTopology ↥(d.whittU FW FV) :=
      Topology.IsEmbedding.subtypeVal.secondCountableTopology
    have hint : Integrable (Function.uncurry Φ) (Measure.haar.prod Measure.haar) :=
      hΦc.integrable_of_hasCompactSupport hΦs
    have h1 : (fun u : ↥(d.whittU FW FV) => chiProj d χ f₀ (p * u)) =
        fun u => ∫ a, Φ a u ∂Measure.haar := rfl
    rw [h1, ← integral_integral_swap hint]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun a => ?_)
    simp only [Φ]
    rw [integral_const_mul]
    have hap : (a : ↥d.G) * p ∈ d.whittB FW FV :=
      (d.whittB FW FV).mul_mem (d.AG_le_whittB FW FV a.2) hp
    have := hcusp FW FV hFV _ hap
    simp only [mul_assoc] at this
    rw [this, mul_zero]
    rfl

/-- `P_χ` maps strongly cuspidal `f₀ ∈ C_c^∞(G(F))` into `𝒞_scusp(G, χ⁻¹)` (`ScuspTestFn d χ`;
Thesis §7.1). -/
theorem chiProj_mem_scusp {f₀ : ↥d.G → ℂ} (hf₀ : f₀ ∈ testFunctions ↥d.G)
    (hcusp : IsStronglyCuspidalInline d f₀) : chiProj d χ f₀ ∈ ScuspTestFn d χ :=
  ⟨chiProj_isLocallyConstant d χ hf₀, chiProj_isChiEquivariant d χ f₀,
    chiProj_hasCompactSupportModAG d χ hf₀.2, chiProj_isStronglyCuspidal d χ hf₀ hcusp⟩

/-- For a cutoff `κ` along `A_G(F)` and `f ∈ 𝒞_scusp(G, χ⁻¹)`, `κ f` is a strongly cuspidal test
function with `P_χ(κ f) = f` (the proof of `chiProj_surjective`). -/
theorem cutoff_mul_spec {κ : ↥d.G → ℂ} (hκ : IsAGCutoff d κ) {f : ↥d.G → ℂ}
    (hf : f ∈ ScuspTestFn d χ) :
    κ * f ∈ testFunctions ↥d.G ∧ IsStronglyCuspidalInline d (κ * f) ∧ chiProj d χ (κ * f) = f := by
  obtain ⟨hloc, heq, ⟨C, hC, hsupp⟩, hcusp⟩ := hf
  refine ⟨⟨hκ.isLocallyConstant.mul hloc, ?_⟩, ?_, ?_⟩
  · -- compact support
    have hfC : tsupport f ⊆ (d.AG : Set ↥d.G) * C :=
      closure_minimal hsupp (d.isClosed_AG_mul hC)
    refine (hκ.isCompact_inter C hC).of_isClosed_subset (isClosed_tsupport _) ?_
    exact Set.subset_inter (tsupport_mul_subset_left (f := κ) (g := f))
      ((tsupport_mul_subset_right (f := κ) (g := f)).trans hfC)
  · -- strong cuspidality
    intro FW FV hFV p hp
    have e : (fun u : ↥(d.whittU FW FV) => (κ * f) (p * u)) =
        fun u : ↥(d.whittU FW FV) => κ p * f (p * u) := by
      funext u
      rw [Pi.mul_apply, hκ.mul_whittU FW FV p u u.2]
    rw [e, integral_const_mul, (hcusp FW FV hFV p hp).2, mul_zero]
  · -- `P_χ(κ f) = f`
    funext g
    unfold chiProj
    have e : ∀ a : ↥d.AG, ((χ.toHom a : Circle) : ℂ) * (κ * f) ((a : ↥d.G) * g) =
        κ ((a : ↥d.G) * g) * f g := by
      intro a
      rw [Pi.mul_apply, heq a g, Circle.coe_inv_eq_conj, ← Circle.coe_inv_eq_conj]
      have h1 : ((χ.toHom a : Circle) : ℂ) * (((χ.toHom a)⁻¹ : Circle) : ℂ) = 1 := by
        rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
      linear_combination (κ ((a : ↥d.G) * g) * f g) * h1
    simp_rw [e]
    rw [integral_mul_const, hκ.integral_AG g, one_mul]

/-- **`P_χ` is onto `𝒞_scusp`** (Thesis §7.1): every `f ∈ ScuspTestFn d χ` is
`P_χ f₀` for a strongly cuspidal `f₀ ∈ C_c^∞(G(F))`.

Proof: `f₀ = κ f` for a cutoff `κ` along `A_G(F)` (`exists_isAGCutoff`, built from the
Harish-Chandra map `H_G`).  It is locally constant; compactly supported, since
`supp f₀ ⊆ tsupport κ ∩ A_G C`; cuspidal, since `κ(p u) = κ(p)` for `u` in a unipotent radical; and
`P_χ f₀(g) = ∫ χ(a) κ(a g) χ(a)⁻¹ f(g) da = f(g)` because `∫_{A_G} κ(a g) da = 1`. -/
theorem chiProj_surjective {f : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d χ) :
    ∃ f₀ ∈ testFunctions ↥d.G, IsStronglyCuspidalInline d f₀ ∧ chiProj d χ f₀ = f := by
  obtain ⟨κ, hκ⟩ := exists_isAGCutoff d
  exact ⟨κ * f, cutoff_mul_spec d χ hκ hf⟩

/-! ### Helpers for the `χ`-transfer (moved up from the algebraic-properties section) -/

/-- The inner integrand `g ↦ f(y⁻¹gy) f'(g)` of the orbital pairing is integrable for continuous `f`
and `f' ∈ C_c^∞(G(F))`. -/
theorem integrable_orbitalInner_integrand {f f' : ↥d.G → ℂ} (hf : Continuous f)
    (hf' : f' ∈ testFunctions ↥d.G) (y : ↥d.G) :
    Integrable (fun g : ↥d.G => f (y⁻¹ * g * y) * f' g) Measure.haar := by
  refine Continuous.integrable_of_hasCompactSupport ?_ (hf'.2.mul_left)
  exact (hf.comp (by fun_prop)).mul hf'.1.continuous

/-- A locally integrable function times a test function is integrable. -/
theorem integrable_mul_testFunction {θ f' : ↥d.G → ℂ}
    (hθ : LocallyIntegrable θ (Measure.haar : Measure ↥d.G)) (hf' : f' ∈ testFunctions ↥d.G) :
    Integrable (fun g => θ g * f' g) (Measure.haar : Measure ↥d.G) := by
  simpa [mul_comm] using hθ.integrable_smul_left_of_hasCompactSupport hf'.1.continuous hf'.2

/-- `C_c^∞(G(F))` is stable under left translation. -/
theorem testFunctions_mul_left {f' : ↥d.G → ℂ} (hf' : f' ∈ testFunctions ↥d.G) (b : ↥d.G) :
    (fun g => f' (b * g)) ∈ testFunctions ↥d.G :=
  ⟨hf'.1.comp_continuous (continuous_const.mul continuous_id),
    hf'.2.comp_homeomorph (Homeomorph.mulLeft b)⟩

/-- Local integrability is preserved by left translation (Haar measure is left invariant). -/
theorem locallyIntegrable_comp_mul_left {θ : ↥d.G → ℂ}
    (hθ : LocallyIntegrable θ (Measure.haar : Measure ↥d.G)) (b : ↥d.G) :
    LocallyIntegrable (fun g => θ (b * g)) (Measure.haar : Measure ↥d.G) := by
  rw [locallyIntegrable_iff] at hθ ⊢
  intro K hK
  have he := measurePreserving_mul_left (Measure.haar : Measure ↥d.G) b
  have hemb : MeasurableEmbedding (fun g : ↥d.G => b * g) :=
    (MeasurableEquiv.mulLeft b).measurableEmbedding
  have hK' : IsCompact ((fun g : ↥d.G => b * g) '' K) := hK.image (continuous_const.mul continuous_id)
  have := (he.integrableOn_comp_preimage hemb (f := θ)).2 (hθ _ hK')
  rwa [Set.preimage_image_eq K (mul_right_injective b)] at this

/-- The inner orbital integral against a left translate `f'(a⁻¹ ·)`, `a ∈ A_G(F)`: substitute
`g ↦ a g` and use `f(x⁻¹ a g x) = f(a x⁻¹ g x) = χ(a)⁻¹ f(x⁻¹ g x)`. -/
theorem orbitalInner_translate_AG {f : ↥d.G → ℂ} (hf : IsChiEquivariant d χ f) (a : ↥d.AG)
    (f' : ↥d.G → ℂ) (y : ↥d.G) :
    orbitalInner d f (fun x => f' ((a : ↥d.G)⁻¹ * x)) y =
      (((χ.toHom a)⁻¹ : Circle) : ℂ) * orbitalInner d f f' y := by
  have hb : ∀ x : ↥d.G, (a : ↥d.G) * x = x * a := fun x =>
    (Subgroup.mem_center_iff.mp (d.AG_le_center a.2) x).symm
  unfold orbitalInner
  rw [← integral_mul_left_eq_self
      (fun x => f (y⁻¹ * x * y) * f' ((a : ↥d.G)⁻¹ * x)) (a : ↥d.G), ← integral_const_mul]
  congr 1; funext x
  have e2 : f (y⁻¹ * ((a : ↥d.G) * x) * y) =
      (((χ.toHom a)⁻¹ : Circle) : ℂ) * f (y⁻¹ * x * y) :=
    (congrArg f (conj_mul_of_commute hb y x)).trans (hf a _)
  have e3 : f' ((a : ↥d.G)⁻¹ * ((a : ↥d.G) * x)) = f' x :=
    congrArg f' (inv_mul_cancel_left _ x)
  exact (congrArg₂ (· * ·) e2 e3).trans (mul_assoc _ _ _)

/-- The orbital pairing against a left translate by `a ∈ A_G(F)` (`orbitalInner_translate_AG`). -/
theorem orbitalPairing_translate_AG {f : ↥d.G → ℂ} (hf : IsChiEquivariant d χ f) (a : ↥d.AG)
    (f' : ↥d.G → ℂ) :
    orbitalPairing d f (fun x => f' ((a : ↥d.G)⁻¹ * x)) =
      (((χ.toHom a)⁻¹ : Circle) : ℂ) * orbitalPairing d f f' := by
  rw [orbitalPairing_eq, orbitalPairing_eq, ← integral_const_mul]
  congr 1; funext x
  exact orbitalInner_translate_AG d χ hf a f' _

/-- If `θ` represents the orbital pairing of `f` (χ-equivariant), so does
`g ↦ χ(a) θ(a g)`, `a ∈ A_G(F)`. -/
theorem integral_translate_AG {f θ : ↥d.G → ℂ} (hf : IsChiEquivariant d χ f)
    (hθ : IsThetaF d f θ) (a : ↥d.AG) {f' : ↥d.G → ℂ} (hf' : f' ∈ testFunctions ↥d.G) :
    ∫ x, ((χ.toHom a : Circle) : ℂ) * θ ((a : ↥d.G) * x) * f' x ∂Measure.haar =
      ∫ x, θ x * f' x ∂Measure.haar := by
  have hca : ((χ.toHom a : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hf'b := testFunctions_mul_left d hf' (a : ↥d.G)⁻¹
  have h1 : ∫ x, ((χ.toHom a : Circle) : ℂ) * θ ((a : ↥d.G) * x) * f' x ∂Measure.haar =
      ((χ.toHom a : Circle) : ℂ) *
        ∫ x, θ x * f' ((a : ↥d.G)⁻¹ * x) ∂Measure.haar := by
    rw [← integral_mul_left_eq_self (fun x => θ x * f' ((a : ↥d.G)⁻¹ * x)) (a : ↥d.G),
      ← integral_const_mul]
    congr 1; funext x
    exact (mul_assoc _ _ _).trans (congrArg (fun z => ((χ.toHom a : Circle) : ℂ) *
      (θ ((a : ↥d.G) * x) * f' z)) (inv_mul_cancel_left _ x).symm)
  rw [h1, hθ.2.2 _ hf'b, orbitalPairing_translate_AG d χ hf a f', hθ.2.2 f' hf',
    Circle.coe_inv, ← mul_assoc, mul_inv_cancel₀ hca, one_mul]

open Classical Polynomial in
/-- An element annihilated by a product of distinct linear factors is semisimple. -/
theorem isSS_of_aeval_prod_eq_zero {A : Type*} [Ring A] [Algebra F A] {x : A} (s : Finset F)
    (h : aeval x (∏ μ ∈ s, (X - C μ)) = 0) : IsSS F x := by
  have hsep : (∏ μ ∈ s, (X - C μ)).Separable :=
    separable_prod_X_sub_C_iff' (f := fun μ : F => μ).mpr fun a _ b _ hab => hab
  unfold IsSS
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree ?_
  have h1 := Polynomial.aeval_algHom_apply (Algebra.lmul F A) x (∏ μ ∈ s, (X - C μ))
  have h2 : Algebra.lmul F A x = LinearMap.mulLeft F x := rfl
  rw [h2] at h1
  rw [h1, h, map_zero]

open Classical Polynomial in
/-- Enlarging the set of roots keeps the annihilation. -/
theorem aeval_prod_eq_zero_of_subset {A : Type*} [Ring A] [Algebra F A] {x : A} {s t : Finset F}
    (hst : s ⊆ t) (h : aeval x (∏ μ ∈ s, (X - C μ)) = 0) :
    aeval x (∏ μ ∈ t, (X - C μ)) = 0 := by
  rw [← Finset.prod_sdiff hst, map_mul, h, mul_zero]

open Classical CliffordAlgebra Polynomial in
/-- **Elements of the split centre `A_{GSpin(V)}` are split semisimple and commute with
`gspin(V)`**: scalars trivially; for a hyperbolic plane, `GSpin(V) ⊆ C⁺(V) = F ⊕ F ω` with
`ω² = r²`, `r ≠ 0`, so `a = α + βω` satisfies `(a - α - βr)(a - α + βr) = 0`, and `C⁺(V) ⊇ gspin(V)` is
commutative. -/
theorem splitCentralGSpin_spec {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (Q : QuadraticForm F V) {a : GSpin Q} (ha : a ∈ splitCentralGSpin Q) :
    (∃ s : Finset F,
      aeval ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) (∏ μ ∈ s, (X - C μ)) = 0) ∧
    ∀ Y ∈ gspin Q, ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * Y =
      Y * ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  unfold splitCentralGSpin at ha
  split_ifs at ha with hQ
  · obtain ⟨e, he⟩ := exists_orthogonal_basis_fin_two Q hQ.1
    obtain ⟨r, hr0, hr⟩ := exists_sq_eq_of_isHypPlane hQ e he
    set ω : CliffordAlgebra Q := ι Q (e 0) * ι Q (e 1) with hω
    have h10 : ι Q (e 1) * ι Q (e 0) = -ω := by
      have h1 := ι_mul_ι_add_swap (Q := Q) (e 1) (e 0)
      have hb : bform Q (e 1) (e 0) = 0 := he 1 0 (by decide)
      rw [polar_eq_two_mul_bform, hb, mul_zero, (algebraMap F (CliffordAlgebra Q)).map_zero] at h1
      exact eq_neg_of_add_eq_zero_left h1
    have hsq : ∀ i, ι Q (e i) * ι Q (e i) = Q (e i) • (1 : CliffordAlgebra Q) := fun i => by
      rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one]
    have hωω : ω * ω = (r ^ 2) • (1 : CliffordAlgebra Q) := by
      calc ω * ω = ι Q (e 0) * (ι Q (e 1) * ι Q (e 0)) * ι Q (e 1) := by
            simp only [ω, mul_assoc]
        _ = -((ι Q (e 0) * ι Q (e 0)) * (ι Q (e 1) * ι Q (e 1))) := by
            rw [h10]; simp only [ω, mul_neg, neg_mul, mul_assoc]
        _ = _ := by rw [hsq, hsq, smul_mul_smul_comm, one_mul, hr, neg_smul]
    have hev : ∀ Y : CliffordAlgebra Q, Y ∈ even Q → ∃ α β : F, Y = α • (1 : CliffordAlgebra Q) + β • ω :=
      fun Y hY => exists_eq_smul_one_add_smul_of_even e he Y (by rw [← even_toSubmodule]; exact hY)
    obtain ⟨α, β, hab⟩ := hev _ a.2.1
    refine ⟨?_, fun Y hY => ?_⟩
    · by_cases hβ : β = 0
      · refine ⟨{α}, ?_⟩
        rw [Finset.prod_singleton, map_sub, aeval_X, aeval_C, hab, hβ,
          Algebra.algebraMap_eq_smul_one]
        module
      · have hne : α + β * r ≠ α - β * r := by
          intro h
          have h2 : (2 : F) * (β * r) = 0 := by linear_combination h
          rcases mul_eq_zero.mp h2 with h2 | h2
          · exact two_ne_zero h2
          · exact mul_ne_zero hβ hr0 h2
        refine ⟨{α + β * r, α - β * r}, ?_⟩
        rw [Finset.prod_pair hne, map_mul, map_sub, map_sub, aeval_X, aeval_C, aeval_C, hab,
          Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        simp only [sub_mul, mul_sub, add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, hωω]
        module
    · obtain ⟨γ, η, hYe⟩ := hev Y hY.1
      rw [hab, hYe]
      simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one]
      module
  · obtain ⟨c, rfl⟩ := ha
    have hc : ((scalarGSpin Q c : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
        algebraMap F (CliffordAlgebra Q) (c : F) := rfl
    refine ⟨⟨{(c : F)}, ?_⟩, fun Y _ => ?_⟩
    · rw [Finset.prod_singleton, map_sub, aeval_X, aeval_C, hc, sub_self]
    · rw [hc]; exact Algebra.commutes _ _

open Classical Polynomial in
/-- `G_reg(F)` is stable under multiplication by `A_G(F)` (Thesis §2.1).

`a ∈ A_G(F)` is semisimple (annihilated by a product of distinct linear factors: scalars, or on a
hyperbolic-plane factor an element of `C⁺(W) ≅ F × F`, `splitCentralGSpin_spec`) and commutes with
`𝔤` (`C⁺(W) ⊇ gspin(W)` is commutative for a plane) and with `g` (`A_G` is central), so `a g` is
semisimple with `𝔤_{ag} = 𝔤_g`. -/
theorem mul_mem_regularSet_of_mem_AG (a : ↥d.AG) {g : ↥d.G} (hg : g ∈ regularSet d.G d.lie) :
    (a : ↥d.G) * g ∈ regularSet d.G d.lie := by
  obtain ⟨p, ⟨hp1, hp2⟩, hpa⟩ := a.2
  obtain ⟨⟨s₁, hs₁⟩, hc₁⟩ := splitCentralGSpin_spec d.QW hp1
  obtain ⟨⟨s₂, hs₂⟩, hc₂⟩ := splitCentralGSpin_spec d.QV hp2
  set A : d.ambient := (((a : ↥d.G) : d.ambientˣ) : d.ambient) with hAdef
  have hA : A = (((p.1 : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW),
      ((p.2 : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) := by
    rw [hAdef, ← hpa]; rfl
  have hAss : IsSS F A := by
    refine isSS_of_aeval_prod_eq_zero (s₁ ∪ s₂) ?_
    rw [hA]
    refine Prod.ext ?_ ?_
    · have := Polynomial.aeval_algHom_apply (AlgHom.fst F (CliffordAlgebra d.QW)
        (CliffordAlgebra d.QV)) (((p.1 : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW),
          ((p.2 : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) (∏ μ ∈ s₁ ∪ s₂, (X - C μ))
      change aeval ((p.1 : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) _ = (aeval (R := F) (A := d.ambient) _ _).1 at this
      rw [← this, Prod.fst_zero]
      exact aeval_prod_eq_zero_of_subset Finset.subset_union_left hs₁
    · have := Polynomial.aeval_algHom_apply (AlgHom.snd F (CliffordAlgebra d.QW)
        (CliffordAlgebra d.QV)) (((p.1 : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW),
          ((p.2 : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) (∏ μ ∈ s₁ ∪ s₂, (X - C μ))
      change aeval ((p.2 : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) _ = (aeval (R := F) (A := d.ambient) _ _).2 at this
      rw [← this, Prod.snd_zero]
      exact aeval_prod_eq_zero_of_subset Finset.subset_union_right hs₂
  have hAc : ∀ Y ∈ d.lie, A * Y = Y * A := fun Y hY => by
    rw [hA]
    exact Prod.ext (hc₁ Y.1 hY.1) (hc₂ Y.2 hY.2)
  have hAg : A * (((g : ↥d.G) : d.ambientˣ) : d.ambient) =
      (((g : ↥d.G) : d.ambientˣ) : d.ambient) * A := by
    have h := Subgroup.mem_center_iff.mp (d.AG_le_center a.2) g
    have h' := congrArg (fun u : ↥d.G => ((u : d.ambientˣ) : d.ambient)) h
    simpa [hAdef] using h'.symm
  show IsRegularSS d.lie ((((a : ↥d.G) * g : ↥d.G) : d.ambientˣ) : d.ambient)
  rw [Subgroup.coe_mul, Units.val_mul, ← hAdef]
  have hC : lieCentralizer d.lie (A * (((g : ↥d.G) : d.ambientˣ) : d.ambient)) =
      lieCentralizer d.lie (((g : ↥d.G) : d.ambientˣ) : d.ambient) := by
    ext Y
    rw [mem_lieCentralizer, mem_lieCentralizer]
    refine and_congr_right fun hY => ?_
    have hu : IsUnit A := ((a : ↥d.G) : d.ambientˣ).isUnit
    constructor
    · intro h
      refine hu.mul_left_cancel ?_
      rw [← mul_assoc, h, ← mul_assoc, ← hAc Y hY, mul_assoc]
    · intro h
      rw [mul_assoc, h, ← mul_assoc, hAc Y hY, mul_assoc]
  refine ⟨?_, hC ▸ hg.2⟩
  have hcomm : Commute (LinearMap.mulLeft F A)
      (LinearMap.mulLeft F (((g : ↥d.G) : d.ambientˣ) : d.ambient)) := by
    change LinearMap.mulLeft F A * LinearMap.mulLeft F _ = LinearMap.mulLeft F _ * LinearMap.mulLeft F A
    refine LinearMap.ext fun w => ?_
    simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, ← mul_assoc, hAg]
  have := Module.End.IsSemisimple.mul_of_commute hcomm hAss hg.1
  unfold IsSS
  rwa [LinearMap.mulLeft_mul]

open Classical Polynomial in
/-- An element of `A_G(F)` is semisimple in `C(W) × C(V)` and commutes with `𝔤` (the first half of
`mul_mem_regularSet_of_mem_AG`). -/
theorem coe_AG_spec (a : ↥d.AG) :
    IsSS F (((a : ↥d.G) : d.ambientˣ) : d.ambient) ∧
      ∀ Y ∈ d.lie, (((a : ↥d.G) : d.ambientˣ) : d.ambient) * Y =
        Y * (((a : ↥d.G) : d.ambientˣ) : d.ambient) := by
  obtain ⟨p, ⟨hp1, hp2⟩, hpa⟩ := a.2
  obtain ⟨⟨s₁, hs₁⟩, hc₁⟩ := splitCentralGSpin_spec d.QW hp1
  obtain ⟨⟨s₂, hs₂⟩, hc₂⟩ := splitCentralGSpin_spec d.QV hp2
  set A : d.ambient := (((a : ↥d.G) : d.ambientˣ) : d.ambient) with hAdef
  have hA : A = (((p.1 : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW),
      ((p.2 : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) := by
    rw [hAdef, ← hpa]; rfl
  refine ⟨?_, fun Y hY => ?_⟩
  · refine isSS_of_aeval_prod_eq_zero (s₁ ∪ s₂) ?_
    rw [hA]
    refine Prod.ext ?_ ?_
    · have := Polynomial.aeval_algHom_apply (AlgHom.fst F (CliffordAlgebra d.QW)
        (CliffordAlgebra d.QV)) (((p.1 : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW),
          ((p.2 : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) (∏ μ ∈ s₁ ∪ s₂, (X - C μ))
      change aeval ((p.1 : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) _ = (aeval (R := F) (A := d.ambient) _ _).1 at this
      rw [← this, Prod.fst_zero]
      exact aeval_prod_eq_zero_of_subset Finset.subset_union_left hs₁
    · have := Polynomial.aeval_algHom_apply (AlgHom.snd F (CliffordAlgebra d.QW)
        (CliffordAlgebra d.QV)) (((p.1 : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW),
          ((p.2 : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) (∏ μ ∈ s₁ ∪ s₂, (X - C μ))
      change aeval ((p.2 : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) _ = (aeval (R := F) (A := d.ambient) _ _).2 at this
      rw [← this, Prod.snd_zero]
      exact aeval_prod_eq_zero_of_subset Finset.subset_union_right hs₂
  · rw [hA]
    exact Prod.ext (hc₁ Y.1 hY.1) (hc₂ Y.2 hY.2)

/-- `a ∈ A_G(F)` commutes with every `g ∈ G(F)` in `C(W) × C(V)`. -/
theorem coe_AG_commute (a : ↥d.AG) (g : ↥d.G) :
    (((a : ↥d.G) : d.ambientˣ) : d.ambient) * ((g : d.ambientˣ) : d.ambient) =
      ((g : d.ambientˣ) : d.ambient) * (((a : ↥d.G) : d.ambientˣ) : d.ambient) := by
  have h := Subgroup.mem_center_iff.mp (d.AG_le_center a.2) g
  have h' := congrArg (fun u : ↥d.G => ((u : d.ambientˣ) : d.ambient)) h
  simpa using h'.symm

/-- `a x` is semisimple for `a ∈ A_G(F)` and semisimple `x`. -/
theorem isSS_mul_AG (a : ↥d.AG) {x : ↥d.G} (hx : IsSS F ((x : d.ambientˣ) : d.ambient)) :
    IsSS F ((((a : ↥d.G) * x : ↥d.G) : d.ambientˣ) : d.ambient) := by
  have hcomm : Commute (LinearMap.mulLeft F (((a : ↥d.G) : d.ambientˣ) : d.ambient))
      (LinearMap.mulLeft F ((x : d.ambientˣ) : d.ambient)) := by
    change LinearMap.mulLeft F _ * LinearMap.mulLeft F _ = LinearMap.mulLeft F _ * LinearMap.mulLeft F _
    refine LinearMap.ext fun w => ?_
    simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, ← mul_assoc, coe_AG_commute d a x]
  have := Module.End.IsSemisimple.mul_of_commute hcomm (coe_AG_spec d a).1 hx
  unfold IsSS
  rw [Subgroup.coe_mul, Units.val_mul, LinearMap.mulLeft_mul]
  exact this

/-- `𝔤_{a x} = 𝔤_x` for `a ∈ A_G(F)`. -/
theorem lieCentralizer_mul_AG (a : ↥d.AG) (x : ↥d.G) :
    lieCentralizer d.lie ((((a : ↥d.G) * x : ↥d.G) : d.ambientˣ) : d.ambient) =
      lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient) := by
  set A : d.ambient := (((a : ↥d.G) : d.ambientˣ) : d.ambient)
  have hAc := (coe_AG_spec d a).2
  have hu : IsUnit A := ((a : ↥d.G) : d.ambientˣ).isUnit
  rw [Subgroup.coe_mul, Units.val_mul]
  ext Y
  rw [mem_lieCentralizer, mem_lieCentralizer]
  refine and_congr_right fun hY => ?_
  constructor
  · intro h
    refine hu.mul_left_cancel ?_
    rw [← mul_assoc, h, ← mul_assoc, ← hAc Y hY, mul_assoc]
  · intro h
    rw [mul_assoc, h, ← mul_assoc, hAc Y hY, mul_assoc]

/-- `G_{a x} = G_x` for `a ∈ A_G(F)` (as subgroups of `(C(W) × C(V))^×`). -/
theorem grpCentralizer_mul_AG (a : ↥d.AG) (x : ↥d.G) :
    grpCentralizer d.G (((a : ↥d.G) * x : ↥d.G) : d.ambientˣ) =
      grpCentralizer d.G (x : d.ambientˣ) := by
  ext z
  simp only [grpCentralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun hz => ?_
  have hc : ((a : ↥d.G) : d.ambientˣ) * z = z * ((a : ↥d.G) : d.ambientˣ) := by
    have h := Subgroup.mem_center_iff.mp (d.AG_le_center a.2) ⟨z, hz⟩
    exact (congrArg Subtype.val h).symm
  set u : d.ambientˣ := ((a : ↥d.G) : d.ambientˣ)
  set v : d.ambientˣ := ((x : ↥d.G) : d.ambientˣ)
  change z * (u * v) = u * v * z ↔ z * v = v * z
  constructor
  · intro h
    refine mul_left_cancel (a := u) ?_
    calc u * (z * v) = z * (u * v) := by rw [← mul_assoc, hc, mul_assoc]
      _ = u * v * z := h
      _ = u * (v * z) := mul_assoc _ _ _
  · intro h
    calc z * (u * v) = u * (z * v) := by rw [← mul_assoc, ← hc, mul_assoc]
      _ = u * (v * z) := by rw [h]
      _ = u * v * z := (mul_assoc _ _ _).symm

/-- The inner orbital integral is linear in the second function (scalars). -/
theorem orbitalInner_smul_right (c : ℂ) (f h : ↥d.G → ℂ) (y : ↥d.G) :
    orbitalInner d f (c • h) y = c * orbitalInner d f h y := by
  unfold orbitalInner
  rw [← integral_const_mul]
  congr 1; funext g; simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- A conjugation-invariant factor moves from the first to the second function of the inner
orbital integral: `∫ κ(y⁻¹gy) f(y⁻¹gy) h(g) dg = ∫ f(y⁻¹gy) κ(g) h(g) dg`. -/
theorem orbitalInner_mul_conjInv {κ : ↥d.G → ℂ} (hκ : ∀ x g : ↥d.G, κ (x * g * x⁻¹) = κ g)
    (f h : ↥d.G → ℂ) (y : ↥d.G) :
    orbitalInner d (κ * f) h y = orbitalInner d f (κ * h) y := by
  unfold orbitalInner
  congr 1; funext g
  have e : κ (y⁻¹ * g * y) = κ g := by
    have := hκ y⁻¹ g
    rwa [inv_inv] at this
  simp only [Pi.mul_apply, e]; ring

/-- The indicator `g ↦ [H_G(g) = t]` of a fibre of `H_G`. -/
def fibInd (t : HCVal) : ↥d.G → ℂ := fun g => if d.hcG g = t then 1 else 0

theorem isLocallyConstant_fibInd (t : HCVal) : IsLocallyConstant (fibInd d t) := by
  classical
  exact IsLocallyConstant.comp d.isLocallyConstant_hcG (fun s => if s = t then (1 : ℂ) else 0)

/-- Cutting a test function along a fibre of `H_G` gives a test function. -/
theorem fibInd_mul_mem {f' : ↥d.G → ℂ} (hf' : f' ∈ testFunctions ↥d.G) (t : HCVal) :
    fibInd d t * f' ∈ testFunctions ↥d.G :=
  ⟨(isLocallyConstant_fibInd d t).mul hf'.1, hf'.2.mul_left⟩

/-- A test function is the finite sum of its cuts along the fibres of `H_G` (finitely many, since
`H_G` is locally constant and the support is compact). -/
theorem sum_fibInd_mul {f' : ↥d.G → ℂ} (hf' : f' ∈ testFunctions ↥d.G) :
    ∑ t ∈ (d.finite_image_hcG hf'.2).toFinset, fibInd d t * f' = f' := by
  classical
  funext g
  rw [Finset.sum_apply]
  simp only [Pi.mul_apply, fibInd]
  by_cases hg : g ∈ tsupport f'
  · rw [Finset.sum_eq_single (d.hcG g)]
    · simp
    · intro t _ ht; rw [ite_eq_right (Ne.symm ht), zero_mul]
    · intro h; exact absurd (((d.finite_image_hcG hf'.2).mem_toFinset).2 ⟨g, hg, rfl⟩) h
  · rw [image_eq_zero_of_notMem_tsupport hg]; simp

/-- **Points `x e^X` approach `x` in `G(F)`**: for an open `O ∋ x`, every `y ∈ G(F)` with
`y = x e^X` lies in `O` once `X` is small (`e^X → 1` and `e^X e^{-X} = 1` near `0`, so also
`y⁻¹ = e^{-X} x⁻¹ → x⁻¹`). -/
theorem eventually_mem_of_eq_mul_expA (x : ↥d.G) {O : Set ↥d.G} (hO : IsOpen O) (hx : x ∈ O) :
    ∀ᶠ X in 𝓝 (0 : d.ambient), ∀ y : ↥d.G,
      ((y : d.ambientˣ) : d.ambient) = ((x : d.ambientˣ) : d.ambient) * expA F X → y ∈ O := by
  obtain ⟨O', hO', rfl⟩ := isOpen_induced_iff.1 hO
  obtain ⟨O'', hO'', rfl⟩ := Units.isInducing_embedProduct.isOpen_iff.1 hO'
  set u : d.ambientˣ := (x : d.ambientˣ)
  let Φ : d.ambient → d.ambient × d.ambientᵐᵒᵖ := fun X =>
    ((u : d.ambient) * expA F X, MulOpposite.op (expA F (-X) * ((u⁻¹ : d.ambientˣ) : d.ambient)))
  have hΦ : ContinuousAt Φ 0 := by
    refine ContinuousAt.prodMk (continuousAt_const.mul (continuousAt_expA_at_zero F)) ?_
    refine MulOpposite.continuous_op.continuousAt.comp ?_
    refine ContinuousAt.mul ?_ continuousAt_const
    exact ContinuousAt.comp (g := expA F) (by simpa using continuousAt_expA_at_zero F)
      continuous_neg.continuousAt
  have hΦ0 : Φ 0 = Units.embedProduct d.ambient u := by
    simp [Φ, expA_zero_eq_one, Units.embedProduct_apply]
  have h1 : Φ ⁻¹' O'' ∈ 𝓝 (0 : d.ambient) :=
    hΦ.preimage_mem_nhds (hO''.mem_nhds (by rw [hΦ0]; exact hx))
  obtain ⟨U, hU, hUe⟩ := expA_mul_expA_neg F (A := d.ambient)
  filter_upwards [h1, hU] with X hX hXU y hy
  show Units.embedProduct d.ambient (y : d.ambientˣ) ∈ O''
  have hinv : (((y : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) =
      expA F (-X) * ((u⁻¹ : d.ambientˣ) : d.ambient) := by
    refine (Units.inv_eq_of_mul_eq_one_right ?_)
    rw [hy, mul_assoc, ← mul_assoc (expA F X), hUe X hXU, one_mul, Units.mul_inv]
  have : Units.embedProduct d.ambient (y : d.ambientˣ) = Φ X := by
    simp only [Units.embedProduct_apply, Φ, hy, hinv]
  rw [this]; exact hX

/-- Transport of germ coefficients along equal centralizer data. -/
theorem exists_germCoeff_transport (ψ : NontrivialAddChar F) {Gc Gc' : Subgroup d.ambientˣ}
    {Lc Lc' : LieSubalgebra F d.ambient} (hG : Gc = Gc') (hL : Lc = Lc') (c : NilOrbit Gc Lc → ℂ) :
    ∃ c' : NilOrbit Gc' Lc' → ℂ, ((Function.support c).Finite → (Function.support c').Finite) ∧
      ∀ X, ∑ᶠ O, c' O * jHat Gc' Lc' d.bilin ψ O X = ∑ᶠ O, c O * jHat Gc Lc d.bilin ψ O X := by
  subst hG; subst hL
  exact ⟨c, id, fun _ => rfl⟩

/-- **Germ expansions transfer along a local identity `θ(x e^X) = k θ₁(x₁ e^X)`** when `x` and `x₁`
have the same centralizers (used with `x₁ = a x`, `a ∈ A_G(F)`). -/
theorem hasGermExpansion_transfer (ψ : NontrivialAddChar F) {θ θ₁ : ↥d.G → ℂ} {x x₁ : ↥d.G}
    (k : ℂ) (hG : grpCentralizer d.G (x₁ : d.ambientˣ) = grpCentralizer d.G (x : d.ambientˣ))
    (hL : lieCentralizer d.lie ((x₁ : d.ambientˣ) : d.ambient) =
      lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))
    (hloc : ∀ᶠ X in 𝓝 (0 : d.ambient), ∀ y : ↥d.G,
      ((y : d.ambientˣ) : d.ambient) = ((x : d.ambientˣ) : d.ambient) * expA F X →
      ∃ y₁ : ↥d.G, ((y₁ : d.ambientˣ) : d.ambient) = ((x₁ : d.ambientˣ) : d.ambient) * expA F X ∧
        θ y = k * θ₁ y₁)
    (h : ∃ c, HasGermExpansion d.G d.lie d.bilin ψ θ₁ x₁ c) :
    ∃ c, HasGermExpansion d.G d.lie d.bilin ψ θ x c := by
  obtain ⟨c, hfin, ω, hω, hexp⟩ := h
  obtain ⟨c', hfin', hsum⟩ := exists_germCoeff_transport d ψ hG hL c
  refine ⟨k • c', (hfin' hfin).subset (Function.support_const_smul_subset k c'),
    ω ∩ {X | ∀ y : ↥d.G, ((y : d.ambientˣ) : d.ambient) = ((x : d.ambientˣ) : d.ambient) * expA F X →
      ∃ y₁ : ↥d.G, ((y₁ : d.ambientˣ) : d.ambient) = ((x₁ : d.ambientˣ) : d.ambient) * expA F X ∧
        θ y = k * θ₁ y₁}, inter_mem hω hloc, ?_⟩
  intro X hX hXc hXr y hy
  obtain ⟨y₁, hy₁, hθ⟩ := hX.2 y hy
  rw [← hL] at hXc hXr
  rw [hθ, hexp X hX.1 hXc hXr y₁ hy₁, ← hsum X]
  rw [mul_finsum]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

set_option maxHeartbeats 2000000 in
/-- **One fibre of the `χ`-transfer.**  Let `φ ∈ 𝒞_scusp(G, χ⁻¹)`, `θ₁` represent the orbital pairing
of `κ φ` (`κ = agCutoff`, with integrable outer integrands), and `b ∈ A_G(F)` with
`H_G(b) t ∈ D`.  For a test function `h` supported in the fibre `H_G⁻¹(t)`, the outer integrand of
`⟨φ, h⟩` is integrable and `⟨φ, h⟩ = c χ(b) ∫ θ₁(b g) h(g) dg` (`c = vol(A_G ∩ ker H_G)`):
`h = k(b ·)` with `k = h(b⁻¹ ·)` supported in `H_G⁻¹(D)`, where `κ = c⁻¹`. -/
theorem chiTransfer_fibre {φ θ₁ : ↥d.G → ℂ} (hφ : φ ∈ ScuspTestFn d χ)
    (hθ₁ : ∀ f' ∈ testFunctions ↥d.G,
      Integrable (fun x : d.GmodAG => orbitalInner d (d.agCutoff * φ) f' (Quotient.out x))
        Measure.haar ∧ ∫ g, θ₁ g * f' g ∂Measure.haar = orbitalPairing d (d.agCutoff * φ) f')
    {t : HCVal} {b : ↥d.AG} (hb : d.hcA b * t ∈ d.hcDomain) {h : ↥d.G → ℂ}
    (hh : h ∈ testFunctions ↥d.G) (hsupp : ∀ g, h g ≠ 0 → d.hcG g = t) :
    Integrable (fun x : d.GmodAG => orbitalInner d φ h (Quotient.out x)) Measure.haar ∧
      ∫ g, ((d.hcVol : ℂ) * ((χ.toHom b : Circle) : ℂ) * θ₁ ((b : ↥d.G) * g)) * h g
        ∂Measure.haar = orbitalPairing d φ h := by
  classical
  set c : ℂ := (d.hcVol : ℂ)
  have hc0 : c ≠ 0 := Complex.ofReal_ne_zero.2 d.hcVol_pos.ne'
  set χb : ℂ := ((χ.toHom b : Circle) : ℂ)
  set k : ↥d.G → ℂ := fun g => h ((b : ↥d.G)⁻¹ * g)
  have hk : k ∈ testFunctions ↥d.G := testFunctions_mul_left d hh _
  -- `κ k = c⁻¹ k`
  have hκk : d.agCutoff * k = c⁻¹ • k := by
    funext g
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hg : k g = 0
    · rw [hg, mul_zero, mul_zero]
    · have h1 := hsupp _ hg
      have h2 : d.hcG g ∈ d.hcDomain := by
        have e : g = (b : ↥d.G) * ((b : ↥d.G)⁻¹ * g) := by group
        rw [e, map_mul, h1]; exact hb
      simp only [GGPData.agCutoff, c]
      rw [ite_eq_left h2]
  -- `orbitalInner(φ, k) = c · orbitalInner(κφ, k)`
  have hk1 : ∀ y, orbitalInner d φ k y = c * orbitalInner d (d.agCutoff * φ) k y := by
    intro y
    rw [orbitalInner_mul_conjInv d (isAGCutoff_agCutoff d).conj, hκk, orbitalInner_smul_right,
      ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  -- `orbitalInner(φ, h) = χ(b) · orbitalInner(φ, k)`
  have hk2 : ∀ y, orbitalInner d φ h y = χb * orbitalInner d φ k y := by
    intro y
    have := orbitalInner_translate_AG d χ hφ.2.1 b⁻¹ k y
    have e : (fun x => k (((b⁻¹ : ↥d.AG) : ↥d.G)⁻¹ * x)) = h := by
      funext x
      simp only [k, InvMemClass.coe_inv, inv_inv, inv_mul_cancel_left]
    rw [e, map_inv, inv_inv] at this
    exact this
  have hinner : ∀ y, orbitalInner d φ h y = χb * c * orbitalInner d (d.agCutoff * φ) k y := by
    intro y; rw [hk2, hk1, mul_assoc]
  refine ⟨?_, ?_⟩
  · simp_rw [hinner]
    exact ((hθ₁ k hk).1).const_mul _
  · -- left side
    have hL : ∫ g, (c * χb * θ₁ ((b : ↥d.G) * g)) * h g ∂Measure.haar =
        c * χb * ∫ g, θ₁ g * k g ∂Measure.haar := by
      rw [← integral_mul_left_eq_self (fun g => θ₁ g * k g) (b : ↥d.G), ← integral_const_mul]
      congr 1; funext g
      simp only [k, inv_mul_cancel_left]; ring
    rw [hL, (hθ₁ k hk).2, orbitalPairing_eq, orbitalPairing_eq]
    simp_rw [hinner]
    rw [integral_const_mul]; ring

set_option maxHeartbeats 2000000 in
/-- **`χ`-transfer of `θ`** (Thesis §4.8, §7.1): for
strongly cuspidal `f₀ ∈ C_c^∞(G(F))`, the orbital pairing of `P_χ f₀` is represented by a
quasi-character, and its outer integrand is integrable on `G(F)/A_G(F)`.

Proof (own work, no Fubini).  Put `φ = P_χ f₀ ∈ 𝒞_scusp` (`chiProj_mem_scusp`) and let `θ₁` be the
quasi-character of the strongly cuspidal test function `κ φ` (`bp_thetaF_exists`; `κ = agCutoff`).
For `t ∈ H_G(G)` choose `b_t ∈ A_G(F)` with `H_G(b_t) t ∈ D` and set, on the clopen fibre
`H_G⁻¹(t)`, `θ(g) = c χ(b_t) θ₁(b_t g)` (`c = vol(A_G ∩ ker H_G)`).  Then:
* `θ` is locally a constant times a central translate of `θ₁`, hence locally integrable, continuous
  on `G_reg(F)` and a quasi-character (`hasGermExpansion_transfer`: `G_{bx} = G_x`, `𝔤_{bx} = 𝔤_x`,
  and `x e^X` stays in the fibre of `x` for small `X`, `eventually_mem_of_eq_mul_expA`);
* a test function `f'` is the finite sum of its cuts `f'_t` along the fibres of `H_G`
  (`sum_fibInd_mul`), and on each fibre `⟨φ, f'_t⟩ = ∫ θ f'_t` with integrable outer integrand
  (`chiTransfer_fibre`), so the same holds for `f'`. -/
theorem isThetaF_chiProj {f₀ : ↥d.G → ℂ} (hf₀ : f₀ ∈ testFunctions ↥d.G)
    (hcusp : IsStronglyCuspidalInline d f₀) :
    ∃ θ : ↥d.G → ℂ, IsThetaF d (chiProj d χ f₀) θ ∧
      (∀ ψ : NontrivialAddChar F, IsQuasiCharacter d.G d.lie d.bilin ψ θ) ∧
      ∀ f' ∈ testFunctions ↥d.G,
        Integrable (fun x : d.GmodAG => orbitalInner d (chiProj d χ f₀) f' (Quotient.out x))
          Measure.haar := by
  classical
  set φ := chiProj d χ f₀ with hφdef
  have hφ : φ ∈ ScuspTestFn d χ := chiProj_mem_scusp d χ hf₀ hcusp
  have hφc : Continuous φ := hφ.1.continuous
  obtain ⟨hf₁, hcusp₁, -⟩ := cutoff_mul_spec d χ (isAGCutoff_agCutoff d) hφ
  obtain ⟨θ₁, hθ₁li, hθ₁c, hθ₁qc, hθ₁⟩ := LitTF.bp_thetaF_exists d (d.agCutoff * φ) hf₁ hcusp₁
  choose rep hrep using fun t : HCVal => d.exists_hcDomain t
  have hrepD : ∀ t, d.hcA (rep t) * t ∈ d.hcDomain := fun t => (hrep t (rep t)).2 rfl
  set c : ℂ := (d.hcVol : ℂ)
  set θ : ↥d.G → ℂ := fun g =>
    c * ((χ.toHom (rep (d.hcG g)) : Circle) : ℂ) * θ₁ ((rep (d.hcG g) : ↥d.G) * g) with hθdef
  have hfib : ∀ t g, d.hcG g = t →
      θ g = c * ((χ.toHom (rep t) : Circle) : ℂ) * θ₁ ((rep t : ↥d.G) * g) := by
    intro t g hg; simp only [hθdef, hg]
  have hopen : ∀ t, IsOpen {g : ↥d.G | d.hcG g = t} :=
    fun t => d.isLocallyConstant_hcG.isOpen_fiber t
  have hev : ∀ g : ↥d.G, θ =ᶠ[𝓝 g] fun g' => c * ((χ.toHom (rep (d.hcG g)) : Circle) : ℂ) *
      θ₁ ((rep (d.hcG g) : ↥d.G) * g') := fun g =>
    Filter.mem_of_superset ((hopen (d.hcG g)).mem_nhds rfl) fun g' hg' => hfib _ g' hg'
  -- local integrability
  have hli : LocallyIntegrable θ (Measure.haar : Measure ↥d.G) := by
    intro g
    obtain ⟨U, hU, hint⟩ := locallyIntegrable_comp_mul_left d hθ₁li (rep (d.hcG g) : ↥d.G) g
    refine ⟨interior U ∩ {g' | d.hcG g' = d.hcG g},
      inter_mem (interior_mem_nhds.2 hU) ((hopen _).mem_nhds rfl), ?_⟩
    exact IntegrableOn.congr_fun ((hint.mono_set (Set.inter_subset_left.trans interior_subset)).const_mul
      (c * ((χ.toHom (rep (d.hcG g)) : Circle) : ℂ))) (fun g' hg' => (hfib _ g' hg'.2).symm)
      (isOpen_interior.inter (hopen _)).measurableSet
  -- continuity on the regular set
  have hcont : ContinuousOn θ (regularSet d.G d.lie) := by
    intro g hg
    set b := rep (d.hcG g)
    have hc' : ContinuousWithinAt (fun g' => c * ((χ.toHom b : Circle) : ℂ) *
        θ₁ ((b : ↥d.G) * g')) (regularSet d.G d.lie) g :=
      continuousWithinAt_const.mul ((hθ₁c _ (mul_mem_regularSet_of_mem_AG d b hg)).comp
        (continuous_const.mul continuous_id).continuousWithinAt
        (fun g' hg' => mul_mem_regularSet_of_mem_AG d b hg'))
    exact hc'.congr_of_eventuallyEq (eventually_nhdsWithin_of_eventually_nhds (hev g))
      (hfib _ g rfl)
  -- the fibrewise identities
  have hfibre : ∀ f' ∈ testFunctions ↥d.G, ∀ t,
      Integrable (fun x : d.GmodAG => orbitalInner d φ (fibInd d t * f') (Quotient.out x))
        Measure.haar ∧ ∫ g, θ g * (fibInd d t * f') g ∂Measure.haar =
          orbitalPairing d φ (fibInd d t * f') := by
    intro f' hf' t
    have hsupp : ∀ g, (fibInd d t * f') g ≠ 0 → d.hcG g = t := by
      intro g hg
      by_contra h
      exact hg (by simp [fibInd, h])
    obtain ⟨h1, h2⟩ := chiTransfer_fibre d χ hφ (fun f' hf' => hθ₁ f' hf') (hrepD t)
      (fibInd_mul_mem d hf' t) hsupp
    refine ⟨h1, ?_⟩
    rw [← h2]
    congr 1; funext g
    by_cases hg : d.hcG g = t
    · rw [hfib t g hg]
    · simp [fibInd, hg]
  have hpieces : ∀ (f' : ↥d.G → ℂ) (hf' : f' ∈ testFunctions ↥d.G) (y : ↥d.G),
      orbitalInner d φ f' y =
      ∑ t ∈ (d.finite_image_hcG hf'.2).toFinset, orbitalInner d φ (fibInd d t * f') y := by
    intro f' hf' y
    conv_lhs => rw [← sum_fibInd_mul d hf']
    unfold orbitalInner
    rw [← integral_finsetSum _ fun t _ =>
      integrable_orbitalInner_integrand d hφc (fibInd_mul_mem d hf' t) y]
    congr 1; funext g
    rw [Finset.sum_apply, Finset.mul_sum]
  have hint : ∀ f' ∈ testFunctions ↥d.G,
      Integrable (fun x : d.GmodAG => orbitalInner d φ f' (Quotient.out x)) Measure.haar := by
    intro f' hf'
    simp_rw [hpieces f' hf']
    exact integrable_finsetSum _ fun t _ => (hfibre f' hf' t).1
  refine ⟨θ, ⟨hli, hcont, fun f' hf' => ?_⟩, fun ψ => ⟨?_, fun x hx => ?_⟩, hint⟩
  · -- the pairing identity
    have e1 : ∫ g, θ g * f' g ∂Measure.haar =
        ∑ t ∈ (d.finite_image_hcG hf'.2).toFinset, ∫ g, θ g * (fibInd d t * f') g ∂Measure.haar := by
      rw [← integral_finsetSum _ fun t _ =>
        integrable_mul_testFunction d hli (fibInd_mul_mem d hf' t)]
      congr 1; funext g
      conv_lhs => rw [← sum_fibInd_mul d hf']
      rw [Finset.sum_apply, Finset.mul_sum]
    rw [e1, orbitalPairing_eq]
    simp_rw [hpieces f' hf']
    rw [integral_finsetSum _ fun t _ => (hfibre f' hf' t).1]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [(hfibre f' hf' t).2, orbitalPairing_eq]
  · -- conjugation invariance
    intro g y hy
    have hc : d.hcG (g * y * g⁻¹) = d.hcG y := d.hcG_conj g y
    rw [hfib _ _ hc, hfib _ y rfl]
    set b := rep (d.hcG y)
    have e : (b : ↥d.G) * (g * y * g⁻¹) = g * ((b : ↥d.G) * y) * g⁻¹ := by
      have hb := Subgroup.mem_center_iff.mp (d.AG_le_center b.2) g
      rw [← mul_assoc, ← mul_assoc, ← hb, mul_assoc g, mul_assoc]
    rw [e, (hθ₁qc ψ).1 g _ (mul_mem_regularSet_of_mem_AG d b hy)]
  · -- germ expansions, transported from `θ₁` at `b x`
    set b := rep (d.hcG x)
    refine hasGermExpansion_transfer d ψ (x₁ := (b : ↥d.G) * x)
      (c * ((χ.toHom b : Circle) : ℂ)) (grpCentralizer_mul_AG d b x)
      (lieCentralizer_mul_AG d b x) ?_ ((hθ₁qc ψ).2 _ (isSS_mul_AG d b hx))
    filter_upwards [eventually_mem_of_eq_mul_expA d x (hopen (d.hcG x)) rfl] with X hX y hy
    refine ⟨(b : ↥d.G) * y, ?_, hfib _ y (hX y hy)⟩
    rw [Subgroup.coe_mul, Units.val_mul, hy, Subgroup.coe_mul, Units.val_mul, mul_assoc]

/-! ### `θ_f` for `f ∈ 𝒞_scusp` -/

/-- For `f ∈ 𝒞_scusp(G, χ⁻¹)` there is a quasi-character representing its orbital pairing, with
integrable outer integrand (from `chiProj_surjective` and `isThetaF_chiProj`). -/
theorem exists_isThetaF_scusp {f : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d χ) :
    ∃ θ : ↥d.G → ℂ, IsThetaF d f θ ∧
      (∀ ψ : NontrivialAddChar F, IsQuasiCharacter d.G d.lie d.bilin ψ θ) ∧
      ∀ f' ∈ testFunctions ↥d.G,
        Integrable (fun x : d.GmodAG => orbitalInner d f f' (Quotient.out x)) Measure.haar := by
  obtain ⟨f₀, hf₀, hcusp, rfl⟩ := chiProj_surjective d χ hf
  exact isThetaF_chiProj d χ hf₀ hcusp

/-- **`θ_f` of a strongly cuspidal function** (Thesis §4.8, Prop 4.8.1(ii); BP Thm 5.5.1, Prop 5.6.1):
for `f ∈ ScuspTestFn d χ`, `thetaF d f`
represents the orbital pairing of `f` and is a quasi-character (for every `ψ`). -/
theorem thetaF_spec {f : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d χ) :
    IsThetaF d f (thetaF d f) ∧
      ∀ ψ : NontrivialAddChar F, IsQuasiCharacter d.G d.lie d.bilin ψ (thetaF d f) := by
  obtain ⟨θ, hθ, hqc, -⟩ := exists_isThetaF_scusp d χ hf
  exact ⟨isThetaF_thetaF_of_exists d f ⟨θ, hθ⟩, fun ψ =>
    isQuasiCharacter_congr_regularSet d ψ (hqc ψ) (eqOn_thetaF d hθ).symm⟩

/-- For `f ∈ 𝒞_scusp(G, χ⁻¹)` and `f' ∈ C_c^∞(G(F))`, `x ↦ ∫_G f(x⁻¹gx) f'(g) dg` is integrable
on `G(F)/A_G(F)` (Thesis Thm 4.7.1(ii) analogue; via `isThetaF_chiProj`). -/
theorem integrable_orbitalInner_scusp {f : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d χ)
    {f' : ↥d.G → ℂ} (hf' : f' ∈ testFunctions ↥d.G) :
    Integrable (fun x : d.GmodAG => orbitalInner d f f' (Quotient.out x)) Measure.haar :=
  (exists_isThetaF_scusp d χ hf).choose_spec.2.2 f' hf'

/-! ### Algebraic properties of `θ_f` -/

/-- `0` represents the orbital pairing of `0`. -/
theorem isThetaF_zero : IsThetaF d 0 0 := by
  refine ⟨locallyIntegrable_zero, continuousOn_const, fun f' _ => ?_⟩
  simp [orbitalPairing]

/-- `θ_0 = 0` on the regular set. -/
theorem thetaF_zero : Set.EqOn (thetaF d 0) 0 (regularSet d.G d.lie) :=
  eqOn_thetaF d (isThetaF_zero d)

/-- If `θ` represents the orbital pairing of `f`, then `c θ` represents that of `c f`. -/
theorem isThetaF_smul (c : ℂ) {f θ : ↥d.G → ℂ} (h : IsThetaF d f θ) :
    IsThetaF d (c • f) (c • θ) := by
  refine ⟨h.1.smul c, h.2.1.const_smul c, fun f' hf' => ?_⟩
  have e1 : (fun g => (c • θ) g * f' g) = fun g => c * (θ g * f' g) := by
    funext g; simp [mul_assoc]
  have e2 : ∀ x : d.GmodAG, (∫ g : ↥d.G, (c • f) ((Quotient.out x)⁻¹ * g * Quotient.out x) * f' g
      ∂Measure.haar) = c * ∫ g : ↥d.G, f ((Quotient.out x)⁻¹ * g * Quotient.out x) * f' g
      ∂Measure.haar := by
    intro x
    rw [← integral_const_mul]
    congr 1; funext g; simp [mul_assoc]
  rw [e1, integral_const_mul, h.2.2 f' hf', orbitalPairing, orbitalPairing]
  simp_rw [e2]
  rw [integral_const_mul]

/-- `θ_{c f} = c θ_f` on the regular set. -/
theorem thetaF_smul (c : ℂ) {f : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d χ) :
    Set.EqOn (thetaF d (c • f)) (c • thetaF d f) (regularSet d.G d.lie) :=
  eqOn_thetaF d (isThetaF_smul d c (thetaF_spec d χ hf).1)

/-- `θ_{f+g} = θ_f + θ_g` on the regular set. -/
theorem thetaF_add {f g : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d χ) (hg : g ∈ ScuspTestFn d χ) :
    Set.EqOn (thetaF d (f + g)) (thetaF d f + thetaF d g) (regularSet d.G d.lie) := by
  have hθf := (thetaF_spec d χ hf).1
  have hθg := (thetaF_spec d χ hg).1
  refine eqOn_thetaF d ⟨hθf.1.add hθg.1, hθf.2.1.add hθg.2.1, fun f' hf' => ?_⟩
  have e1 : (fun x => (thetaF d f + thetaF d g) x * f' x) =
      fun x => thetaF d f x * f' x + thetaF d g x * f' x := by
    funext x; simp [add_mul]
  rw [e1, integral_add (integrable_mul_testFunction d hθf.1 hf')
    (integrable_mul_testFunction d hθg.1 hf'), hθf.2.2 f' hf', hθg.2.2 f' hf',
    orbitalPairing_eq, orbitalPairing_eq, orbitalPairing_eq]
  have hinner : ∀ y : ↥d.G, orbitalInner d (f + g) f' y = orbitalInner d f f' y +
      orbitalInner d g f' y := by
    intro y
    unfold orbitalInner
    rw [← integral_add (integrable_orbitalInner_integrand d hf.1.continuous hf' y)
      (integrable_orbitalInner_integrand d hg.1.continuous hf' y)]
    congr 1; funext x; simp [add_mul]
  simp_rw [hinner]
  exact (integral_add (integrable_orbitalInner_scusp d χ hf hf')
    (integrable_orbitalInner_scusp d χ hg hf')).symm

/-- `θ_f` is conjugation invariant on the regular set. -/
theorem thetaF_conj (ψ : NontrivialAddChar F) {f : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d χ)
    (g y : ↥d.G) (hy : y ∈ regularSet d.G d.lie) :
    thetaF d f (g * y * g⁻¹) = thetaF d f y :=
  ((thetaF_spec d χ hf).2 ψ).1 g y hy

/-- `θ_f(a g) = χ(a)⁻¹ θ_f(g)`, at regular `g` with `a g` regular. -/
theorem thetaF_mul_AG_of_mem {f : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d χ) (a : ↥d.AG) {g : ↥d.G}
    (hg : g ∈ regularSet d.G d.lie) (hag : (a : ↥d.G) * g ∈ regularSet d.G d.lie) :
    thetaF d f ((a : ↥d.G) * g) = (((χ.toHom a)⁻¹ : Circle) : ℂ) * thetaF d f g := by
  have hθ := (thetaF_spec d χ hf).1
  have hca : ((χ.toHom a : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hθ'li : LocallyIntegrable (fun x => ((χ.toHom a : Circle) : ℂ) *
      thetaF d f ((a : ↥d.G) * x)) Measure.haar :=
    (locallyIntegrable_comp_mul_left d hθ.1 (a : ↥d.G)).smul ((χ.toHom a : Circle) : ℂ)
  have hae := ae_eq_of_integral_testFunctions hθ.1 hθ'li fun f' hf' =>
    (integral_translate_AG d χ hf.2.1 hθ a hf').symm
  have hreg := (hc_regularSet_open_conull d).1
  have hcm : Continuous (fun x : ↥d.G => (a : ↥d.G) * x) := continuous_const.mul continuous_id
  have hU : IsOpen (regularSet d.G d.lie ∩ (fun x => (a : ↥d.G) * x) ⁻¹' regularSet d.G d.lie) :=
    hreg.inter (hreg.preimage hcm)
  have hcont : ContinuousOn (fun x => ((χ.toHom a : Circle) : ℂ) *
      thetaF d f ((a : ↥d.G) * x))
      (regularSet d.G d.lie ∩ (fun x => (a : ↥d.G) * x) ⁻¹' regularSet d.G d.lie) :=
    continuousOn_const.mul (hθ.2.1.comp hcm.continuousOn fun x hx => hx.2)
  have heq := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hae) hU
    (hθ.2.1.mono Set.inter_subset_left) hcont ⟨hg, hag⟩
  simp only at heq
  rw [Circle.coe_inv, heq, ← mul_assoc, inv_mul_cancel₀ hca, one_mul]

/-- `θ_f(a g) = χ(a)⁻¹ θ_f(g)` on the regular set. -/
theorem thetaF_mul_AG {f : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d χ) (a : ↥d.AG) {g : ↥d.G}
    (hg : g ∈ regularSet d.G d.lie) :
    thetaF d f ((a : ↥d.G) * g) = (((χ.toHom a)⁻¹ : Circle) : ℂ) * thetaF d f g :=
  thetaF_mul_AG_of_mem d χ hf a hg (mul_mem_regularSet_of_mem_AG d a hg)

/-! ## The averaging form of the `χ`-transfer

The statements `IsAGCutoff`, `exists_isAGCutoff` (proved above, before `chiProj_surjective`, which
uses them) and `isThetaF_chiProj_avg` (proved below), used by `exists_scusp_of_qc_bp`
(`Scusp.lean`) for the `χ`-transfer of BP Cor 5.7.2(i). -/

section Core2Cutoff

variable (d : GGPData F) (χ : CentralCharOn d)

/-- **`θ_{f₀}` vanishes off `H_G⁻¹(H_G(supp f₀))`** on the regular set: for `f'` supported in the
clopen invariant set `U = {H_G ∉ H_G(supp f₀)}`, every orbital integral `∫ f₀(y⁻¹gy) f'(g) dg`
vanishes (`H_G` is conjugation invariant), so `1_U θ₀ = 0` a.e., hence `θ₀ = 0` on `U ∩ G_reg`. -/
theorem isThetaF_eq_zero_of_hcG_notMem {f₀ θ₀ : ↥d.G → ℂ} (hθ₀ : IsThetaF d f₀ θ₀) {g : ↥d.G}
    (hg : g ∈ regularSet d.G d.lie) (hgS : d.hcG g ∉ d.hcG '' tsupport f₀) : θ₀ g = 0 := by
  classical
  set S := d.hcG '' tsupport f₀
  set U : Set ↥d.G := d.hcG ⁻¹' Sᶜ
  have hUo : IsOpen U := d.isLocallyConstant_hcG _
  have hU : ∀ f' ∈ testFunctions ↥d.G, U.indicator f' ∈ testFunctions ↥d.G := by
    intro f' hf'
    have e : U.indicator f' = (fun g => if d.hcG g ∈ Sᶜ then (1 : ℂ) else 0) * f' := by
      funext g; simp only [Set.indicator, Pi.mul_apply, U, Set.mem_preimage]
      split_ifs <;> simp
    rw [e]
    exact ⟨(IsLocallyConstant.comp d.isLocallyConstant_hcG
      (fun s => if s ∈ Sᶜ then (1 : ℂ) else 0)).mul hf'.1, hf'.2.mul_left⟩
  have h0 : ∀ f' ∈ testFunctions ↥d.G, ∫ x, U.indicator θ₀ x * f' x ∂Measure.haar = 0 := by
    intro f' hf'
    have e : (fun x => U.indicator θ₀ x * f' x) = fun x => θ₀ x * U.indicator f' x := by
      funext x; simp only [Set.indicator]; split_ifs <;> simp
    rw [e, hθ₀.2.2 _ (hU f' hf'), orbitalPairing_eq]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
    show orbitalInner d f₀ (U.indicator f') (Quotient.out x) = 0
    unfold orbitalInner
    refine integral_eq_zero_of_ae (Eventually.of_forall fun g' => ?_)
    show f₀ _ * U.indicator f' g' = 0
    by_cases hg' : g' ∈ U
    · have : f₀ ((Quotient.out x)⁻¹ * g' * Quotient.out x) = 0 := by
        by_contra hne
        apply hg'
        show d.hcG g' ∈ S
        refine ⟨_, subset_tsupport f₀ hne, ?_⟩
        have := d.hcG_conj (Quotient.out x)⁻¹ g'
        rwa [inv_inv] at this
      rw [this, zero_mul]
    · rw [Set.indicator_of_notMem hg', mul_zero]
  have hae := ae_eq_zero_of_integral_testFunctions (hθ₀.1.indicator hUo.measurableSet) h0
  have hreg := (hc_regularSet_open_conull d).1
  have hae' : θ₀ =ᵐ[(Measure.haar : Measure ↥d.G).restrict (U ∩ regularSet d.G d.lie)] 0 := by
    refine (ae_restrict_iff' (hUo.inter hreg).measurableSet).2 ?_
    filter_upwards [hae] with x hx hxU
    simpa [Set.indicator_of_mem hxU.1] using hx
  exact Measure.eqOn_open_of_ae_eq hae' (hUo.inter hreg) (hθ₀.2.1.mono Set.inter_subset_right)
    continuousOn_const ⟨hgS, hg⟩

/-- `a ↦ f'(a⁻¹ ·)` is locally constant on `A_G(F)` for a test function `f'` (`f'` is invariant
under left translation by a neighbourhood of `1`). -/
theorem isLocallyConstant_translate_AG {f' : ↥d.G → ℂ} (hf' : f' ∈ testFunctions ↥d.G) :
    IsLocallyConstant (fun a : ↥d.AG => fun g : ↥d.G => f' ((a : ↥d.G)⁻¹ * g)) := by
  obtain ⟨U, hU, hUf⟩ := exists_nhds_one_mul_eq hf'.1 hf'.2
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a₀
  have hc : Continuous (fun a : ↥d.AG => (a : ↥d.G)⁻¹ * (a₀ : ↥d.G)) :=
    (continuous_subtype_val.inv).mul continuous_const
  have : (fun a : ↥d.AG => (a : ↥d.G)⁻¹ * (a₀ : ↥d.G)) ⁻¹' U ∈ 𝓝 a₀ :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU)
  filter_upwards [this] with a ha
  funext g
  have e : (a : ↥d.G)⁻¹ * g = ((a : ↥d.G)⁻¹ * a₀) * ((a₀ : ↥d.G)⁻¹ * g) := by group
  rw [e, hUf _ ha]

set_option maxHeartbeats 1000000 in
/-- **Finite decomposition of an `A_G`-integral** of `χ(a) Ψ(Φ(a))` with `Φ` locally constant and
`Ψ ∘ Φ` supported in a compact `K`: it is `∑_τ (∫_{K ∩ Φ⁻¹ τ} χ) Ψ(τ)` over the finitely many values
`τ` of `Φ` on `K`.  Only the value set matters, so two such integrals with the same `Ψ`-values agree. -/
theorem integral_char_mul_eq_sum {T : Type*} {Φ : ↥d.AG → T} (hΦ : IsLocallyConstant Φ)
    {K : Set ↥d.AG} (hK : IsCompact K) :
    ∃ (R : Finset T) (w : T → ℂ), (∀ τ ∈ R, ∃ a, Φ a = τ) ∧ ∀ Ψ : T → ℂ,
      (∀ a, a ∉ K → Ψ (Φ a) = 0) → ∫ a, ((χ.toHom a : Circle) : ℂ) * Ψ (Φ a) ∂Measure.haar =
        ∑ τ ∈ R, w τ * Ψ τ := by
  classical
  have hfin : (Φ '' K).Finite := by
    have : CompactSpace K := isCompact_iff_compactSpace.1 hK
    rw [Set.image_eq_range]
    exact (hΦ.comp_continuous continuous_subtype_val).range_finite
  set R := hfin.toFinset
  set E : T → Set ↥d.AG := fun τ => K ∩ Φ ⁻¹' {τ}
  have hEm : ∀ τ, MeasurableSet (E τ) := fun τ =>
    hK.isClosed.measurableSet.inter (hΦ.isOpen_fiber τ).measurableSet
  have hχc : Continuous (fun a : ↥d.AG => ((χ.toHom a : Circle) : ℂ)) :=
    continuous_subtype_val.comp χ.continuous
  have hint : ∀ τ, Integrable ((E τ).indicator fun a => ((χ.toHom a : Circle) : ℂ)) Measure.haar :=
    fun τ => (integrable_indicator_iff (hEm τ)).2
      ((hχc.continuousOn.integrableOn_compact hK).mono_set Set.inter_subset_left)
  refine ⟨R, fun τ => ∫ a, (E τ).indicator (fun a => ((χ.toHom a : Circle) : ℂ)) a ∂Measure.haar,
    fun τ hτ => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨a, -, ha⟩ := (hfin.mem_toFinset).1 hτ
    exact ⟨a, ha⟩
  have hpt : ∀ a, ((χ.toHom a : Circle) : ℂ) * Ψ (Φ a) =
      ∑ τ ∈ R, (E τ).indicator (fun a => ((χ.toHom a : Circle) : ℂ)) a * Ψ τ := by
    intro a
    by_cases ha : a ∈ K
    · rw [Finset.sum_eq_single (Φ a)]
      · rw [Set.indicator_of_mem (show a ∈ E (Φ a) from ⟨ha, rfl⟩)]
      · intro τ _ hτ
        have : a ∉ E τ := fun h => hτ (h.2.symm)
        rw [Set.indicator_of_notMem this, zero_mul]
      · intro h; exact absurd ((hfin.mem_toFinset).2 ⟨a, ha, rfl⟩) h
    · have h0 : Ψ (Φ a) = 0 := hΨ a ha
      refine (show ((χ.toHom a : Circle) : ℂ) * Ψ (Φ a) = 0 by rw [h0]; exact mul_zero _).trans ?_
      refine (Finset.sum_eq_zero fun τ _ => ?_).symm
      have : a ∉ E τ := fun h => ha h.1
      rw [Set.indicator_of_notMem this]; exact zero_mul _
  simp_rw [hpt]
  rw [integral_finsetSum _ fun τ _ => (hint τ).mul_const _]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_mul_const]

/-- `A_G(F)` is second countable (a subspace of `G(F)`). -/
instance secondCountableTopology_AG (d : GGPData F) : SecondCountableTopology ↥d.AG :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

/-- The shear `(a, g) ↦ (a, a g)` preserves `da × dg` on `A_G(F) × G(F)`. -/
theorem measurePreserving_AG_shear :
    MeasurePreserving (fun p : ↥d.AG × ↥d.G => (p.1, (p.1 : ↥d.G) * p.2))
      ((Measure.haar : Measure ↥d.AG).prod (Measure.haar : Measure ↥d.G))
      ((Measure.haar : Measure ↥d.AG).prod (Measure.haar : Measure ↥d.G)) :=
  (MeasurePreserving.id _).skew_product (g := fun (a : ↥d.AG) (x : ↥d.G) => (a : ↥d.G) * x)
    ((continuous_subtype_val.comp continuous_fst).mul continuous_snd).measurable
    (Eventually.of_forall fun _ => map_mul_left_eq_self _ _)

/-- The `A_G`-range: if `f(y⁻¹ g y) h(a⁻¹ g) ≠ 0` then `H_G(a) ∈ H_G(supp f) H_G(supp h)⁻¹`. -/
def agRange (f h : ↥d.G → ℂ) : Set ↥d.AG :=
  d.hcA ⁻¹' Set.image2 (fun s t => s * t⁻¹) (d.hcG '' tsupport f) (d.hcG '' tsupport h)

theorem isCompact_agRange {f h : ↥d.G → ℂ} (hf : HasCompactSupport f) (hh : HasCompactSupport h) :
    IsCompact (agRange d f h) :=
  d.isCompact_preimage_hcA ((d.finite_image_hcG hf).image2 _ (d.finite_image_hcG hh))

theorem mem_agRange {f h : ↥d.G → ℂ} {a : ↥d.AG} {g g' : ↥d.G} (hg : f g ≠ 0)
    (hg' : h ((a : ↥d.G)⁻¹ * g') ≠ 0) (hc : d.hcG g = d.hcG g') : a ∈ agRange d f h := by
  refine ⟨d.hcG g, ⟨g, subset_tsupport f hg, rfl⟩, d.hcG ((a : ↥d.G)⁻¹ * g'),
    ⟨_, subset_tsupport h hg', rfl⟩, ?_⟩
  simp only [map_mul, map_inv, hc, GGPData.hcA_apply, mul_inv_rev, inv_inv]
  exact mul_inv_cancel_left _ _

/-- Orbital integrals against `h(a⁻¹ ·)` vanish for `a` outside the `A_G`-range. -/
theorem orbitalInner_translate_eq_zero {f h : ↥d.G → ℂ} {a : ↥d.AG} (ha : a ∉ agRange d f h)
    (y : ↥d.G) : orbitalInner d f (fun g => h ((a : ↥d.G)⁻¹ * g)) y = 0 := by
  unfold orbitalInner
  refine integral_eq_zero_of_ae (Eventually.of_forall fun g => ?_)
  show f (y⁻¹ * g * y) * h ((a : ↥d.G)⁻¹ * g) = 0
  by_contra hne
  apply ha
  refine mem_agRange d (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne) ?_
  have := d.hcG_conj y⁻¹ g
  rwa [inv_inv] at this

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
/-- **Integrability on `A_G(F) × G(F)`** of `χ(a) θ'(a g) h(g)` for `θ'` locally integrable and
supported in `H_G⁻¹(S₀)` (`S₀` finite), and `h` bounded, measurable, compactly supported: after the
shear `(a, g) ↦ (a, a g)` it is dominated by `M 1_{A'}(a) · 1_L(g) |θ'(g)|` with `A'` compact. -/
theorem integrable_AG_prod {θ' h : ↥d.G → ℂ} (hθ' : LocallyIntegrable θ' Measure.haar)
    {S₀ : Set HCVal} (hS₀ : S₀.Finite) (hθS : ∀ g, θ' g ≠ 0 → d.hcG g ∈ S₀)
    (hh : Measurable h) {M : ℝ} (hM : ∀ g, ‖h g‖ ≤ M) {Kh : Set ↥d.G} (hKh : IsCompact Kh)
    (hhK : ∀ g, h g ≠ 0 → g ∈ Kh) :
    Integrable (fun p : ↥d.AG × ↥d.G =>
      ((χ.toHom p.1 : Circle) : ℂ) * θ' ((p.1 : ↥d.G) * p.2) * h p.2)
      ((Measure.haar : Measure ↥d.AG).prod Measure.haar) := by
  set T := d.hcG '' Kh
  have hT : T.Finite := d.finite_image_hcG hKh
  set A' : Set ↥d.AG := d.hcA ⁻¹' Set.image2 (fun s t => s * t⁻¹) S₀ T
  have hA' : IsCompact A' := d.isCompact_preimage_hcA (hS₀.image2 _ hT)
  set L : Set ↥d.G := (Subtype.val '' A') * Kh
  have hL : IsCompact L := (hA'.image continuous_subtype_val).mul hKh
  set F' : ↥d.AG × ↥d.G → ℂ := fun p =>
    ((χ.toHom p.1 : Circle) : ℂ) * θ' p.2 * h ((p.1 : ↥d.G)⁻¹ * p.2)
  have hcomp : (fun p : ↥d.AG × ↥d.G =>
      ((χ.toHom p.1 : Circle) : ℂ) * θ' ((p.1 : ↥d.G) * p.2) * h p.2) =
      F' ∘ fun p : ↥d.AG × ↥d.G => (p.1, (p.1 : ↥d.G) * p.2) := by
    funext p; simp [F', inv_mul_cancel_left]
  have hF'm : AEStronglyMeasurable F' ((Measure.haar : Measure ↥d.AG).prod Measure.haar) := by
    refine ((((continuous_subtype_val.comp χ.continuous).comp continuous_fst).aestronglyMeasurable).mul
      hθ'.aestronglyMeasurable.comp_snd).mul ?_
    exact (hh.comp ((continuous_subtype_val.comp continuous_fst).inv.mul
      continuous_snd).measurable).aestronglyMeasurable
  rw [hcomp, (measurePreserving_AG_shear d).integrable_comp hF'm]
  have hbound : ∀ p : ↥d.AG × ↥d.G,
      ‖F' p‖ ≤ A'.indicator (fun _ => M) p.1 * L.indicator (fun g => ‖θ' g‖) p.2 := by
    intro p
    by_cases h0 : F' p = 0
    · rw [h0, norm_zero]
      exact mul_nonneg (Set.indicator_nonneg (fun _ _ => (norm_nonneg _).trans (hM 1)) _)
        (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
    · have h1 : θ' p.2 ≠ 0 := fun h => h0 (by simp [F', h])
      have h2 : h ((p.1 : ↥d.G)⁻¹ * p.2) ≠ 0 := fun h => h0 (by simp [F', h])
      have hK := hhK _ h2
      have hpA : p.1 ∈ A' := by
        refine ⟨d.hcG p.2, hθS _ h1, d.hcG ((p.1 : ↥d.G)⁻¹ * p.2), ⟨_, hK, rfl⟩, ?_⟩
        simp only [map_mul, map_inv, GGPData.hcA_apply, mul_inv_rev, inv_inv]
        exact mul_inv_cancel_left _ _
      have hpL : p.2 ∈ L := ⟨(p.1 : ↥d.G), ⟨p.1, hpA, rfl⟩, _, hK, mul_inv_cancel_left _ _⟩
      rw [Set.indicator_of_mem hpA, Set.indicator_of_mem hpL]
      simp only [F', norm_mul, Circle.norm_coe, one_mul]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  have hint1 : Integrable (A'.indicator fun _ => M) (Measure.haar : Measure ↥d.AG) :=
    (integrable_indicator_iff hA'.measurableSet).2 (integrableOn_const hA'.measure_lt_top.ne)
  have hint2 : Integrable (L.indicator fun g => ‖θ' g‖) (Measure.haar : Measure ↥d.G) :=
    (integrable_indicator_iff hL.measurableSet).2 ((hθ'.integrableOn_isCompact hL).norm)
  exact (hint1.mul_prod hint2).mono' hF'm (Eventually.of_forall hbound)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
/-- **Orbital integrals of `P_χ f₀`**: `∫_G P_χ f₀(y⁻¹gy) h(g) dg = ∫_{A_G} χ(a) ∫_G f₀(y⁻¹gy) h(a⁻¹g) dg da`
(Fubini over `A_G(F) × G(F)`; the integrand is continuous with compact support, `agRange`). -/
theorem orbitalInner_chiProj {f₀ h : ↥d.G → ℂ} (hf₀ : f₀ ∈ testFunctions ↥d.G)
    (hh : h ∈ testFunctions ↥d.G) (y : ↥d.G) :
    orbitalInner d (chiProj d χ f₀) h y = ∫ a, ((χ.toHom a : Circle) : ℂ) *
      orbitalInner d f₀ (fun g => h ((a : ↥d.G)⁻¹ * g)) y ∂Measure.haar := by
  set Φ : ↥d.AG → ↥d.G → ℂ := fun a g =>
    ((χ.toHom a : Circle) : ℂ) * f₀ ((a : ↥d.G) * (y⁻¹ * g * y)) * h g
  have hΦc : Continuous (Function.uncurry Φ) := by
    refine ((continuous_subtype_val.comp (χ.continuous.comp continuous_fst)).mul
      (hf₀.1.continuous.comp ?_)).mul (hh.1.continuous.comp continuous_snd)
    exact (continuous_subtype_val.comp continuous_fst).mul
      ((continuous_const.mul continuous_snd).mul continuous_const)
  have hΦs : HasCompactSupport (Function.uncurry Φ) := by
    refine HasCompactSupport.intro ((isCompact_agRange d hf₀.2 hh.2).prod hh.2) fun p hp => ?_
    by_contra hne
    have h1 : f₀ ((p.1 : ↥d.G) * (y⁻¹ * p.2 * y)) ≠ 0 := fun h0 =>
      hne (show Φ p.1 p.2 = 0 by simp only [Φ, h0, mul_zero, zero_mul])
    have h2 : h p.2 ≠ 0 := fun h0 => hne (show Φ p.1 p.2 = 0 by simp only [Φ, h0, mul_zero])
    apply hp
    refine ⟨mem_agRange d h1 (g' := (p.1 : ↥d.G) * p.2) (by rwa [inv_mul_cancel_left]) ?_,
      subset_tsupport h h2⟩
    have hc := d.hcG_conj y⁻¹ p.2
    rw [inv_inv] at hc
    rw [map_mul d.hcG (p.1 : ↥d.G) (y⁻¹ * p.2 * y), hc, map_mul]
  have hint : Integrable (Function.uncurry Φ)
      ((Measure.haar : Measure ↥d.AG).prod (Measure.haar : Measure ↥d.G)) :=
    hΦc.integrable_of_hasCompactSupport hΦs
  unfold orbitalInner chiProj
  have e1 : ∀ g : ↥d.G, (∫ a : ↥d.AG, ((χ.toHom a : Circle) : ℂ) *
      f₀ ((a : ↥d.G) * (y⁻¹ * g * y)) ∂Measure.haar) * h g = ∫ a, Φ a g ∂Measure.haar :=
    fun g => by rw [← integral_mul_const]
  simp_rw [e1]
  rw [← integral_integral_swap hint]
  congr 1; funext a
  have hb : ∀ x : ↥d.G, (a : ↥d.G) * x = x * a := fun x =>
    (Subgroup.mem_center_iff.mp (d.AG_le_center a.2) x).symm
  rw [← integral_const_mul, ← integral_mul_left_eq_self
    (fun g => ((χ.toHom a : Circle) : ℂ) * (f₀ (y⁻¹ * g * y) * h ((a : ↥d.G)⁻¹ * g))) (a : ↥d.G)]
  congr 1; funext g
  simp only [Φ, inv_mul_cancel_left, conj_mul_of_commute hb y g]
  ring

set_option maxHeartbeats 1000000 in
/-- **The `χ`-average of `θ_{f₀}` is continuous on `G_reg(F)`** (dominated convergence: near a
regular `g₀` only `a` in a compact set contribute, `isThetaF_eq_zero_of_hcG_notMem`, and `θ_{f₀}`
is bounded on the compact set `A' N ⊆ G_reg(F)`). -/
theorem continuousOn_chiAvg {f₀ θ₀ : ↥d.G → ℂ} (hθ₀ : IsThetaF d f₀ θ₀)
    (hf₀ : HasCompactSupport f₀) :
    ContinuousOn (fun g => ∫ a : ↥d.AG, ((χ.toHom a : Circle) : ℂ) * θ₀ ((a : ↥d.G) * g)
      ∂Measure.haar) (regularSet d.G d.lie) := by
  intro g₀ hg₀
  have hreg := (hc_regularSet_open_conull d).1
  set t := d.hcG g₀
  set S₀ := d.hcG '' tsupport f₀
  have hS₀ : S₀.Finite := d.finite_image_hcG hf₀
  set A' : Set ↥d.AG := d.hcA ⁻¹' Set.image2 (fun s t' => s * t'⁻¹) S₀ {t}
  have hA' : IsCompact A' := d.isCompact_preimage_hcA (hS₀.image2 _ (Set.finite_singleton t))
  have hN₀ : regularSet d.G d.lie ∩ {g | d.hcG g = t} ∈ 𝓝 g₀ :=
    (hreg.inter (d.isLocallyConstant_hcG.isOpen_fiber t)).mem_nhds ⟨hg₀, rfl⟩
  obtain ⟨N, hN, hNsub, hNc⟩ := local_compact_nhds hN₀
  have hB : IsCompact ((Subtype.val '' A') * N) := (hA'.image continuous_subtype_val).mul hNc
  have hBreg : (Subtype.val '' A') * N ⊆ regularSet d.G d.lie := by
    rintro _ ⟨_, ⟨a, -, rfl⟩, g, hg, rfl⟩
    exact mul_mem_regularSet_of_mem_AG d a (hNsub hg).1
  obtain ⟨C, hC⟩ := hB.exists_bound_of_continuousOn (hθ₀.2.1.mono hBreg)
  have hχn : ∀ a : ↥d.AG, ‖((χ.toHom a : Circle) : ℂ)‖ = 1 := fun a => Circle.norm_coe _
  refine continuousWithinAt_of_dominated (bound := A'.indicator fun _ => C) ?_ ?_
    ((integrable_indicator_iff hA'.measurableSet).2 (integrableOn_const hA'.measure_lt_top.ne)) ?_
  · filter_upwards [self_mem_nhdsWithin] with g hg
    exact ((continuous_subtype_val.comp χ.continuous).mul (hθ₀.2.1.comp_continuous
      (continuous_subtype_val.mul continuous_const)
      fun a => mul_mem_regularSet_of_mem_AG d a hg)).aestronglyMeasurable
  · filter_upwards [mem_nhdsWithin_of_mem_nhds hN] with g hg
    refine Eventually.of_forall fun a => ?_
    by_cases ha : a ∈ A'
    · rw [Set.indicator_of_mem ha, norm_mul, hχn, one_mul]
      exact hC _ ⟨_, ⟨a, ha, rfl⟩, g, hg, rfl⟩
    · have h0 : θ₀ ((a : ↥d.G) * g) = 0 := by
        refine isThetaF_eq_zero_of_hcG_notMem d hθ₀ (mul_mem_regularSet_of_mem_AG d a (hNsub hg).1)
          fun hmem => ha ⟨_, hmem, t, rfl, ?_⟩
        show d.hcG ((a : ↥d.G) * g) * t⁻¹ = d.hcA a
        rw [map_mul, (hNsub hg).2, mul_inv_cancel_right]; rfl
      rw [Set.indicator_of_notMem ha, h0, mul_zero, norm_zero]
  · refine Eventually.of_forall fun a => ?_
    exact continuousWithinAt_const.mul ((hθ₀.2.1 _ (mul_mem_regularSet_of_mem_AG d a hg₀)).comp
      (continuous_const.mul continuous_id).continuousWithinAt
      fun g hg => mul_mem_regularSet_of_mem_AG d a hg)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
/-- **The `χ`-transfer formula** `θ_{P_χ f₀}(g) = ∫_{A_G(F)} χ(a) θ_{f₀}(a g) da` (Thesis
§7.1): for strongly cuspidal `f₀ ∈ C_c^∞(G(F))` and any `θ₀` representing
the orbital pairing of `f₀`, the `χ`-average of `θ₀` represents the orbital pairing of `P_χ f₀`.

Proof (own work).  Replace `θ₀` by `θ' = 1_{G_reg} θ₀` (equal a.e.; equal at the points `a g`,
`g` regular), which vanishes off `H_G⁻¹(H_G(supp f₀))` (`isThetaF_eq_zero_of_hcG_notMem`).
* Local integrability and the pairing: `χ(a) θ'(a g) h(g)` is integrable on `A_G(F) × G(F)`
  (`integrable_AG_prod`), so Fubini gives `∫ avg θ' · f' = ∫_{A_G} χ(a) ⟨f₀, f'(a⁻¹·)⟩ da`.
* `⟨P_χ f₀, f'⟩ = ∫_{G/A_G} ∫_{A_G} χ(a) ⟨⟨f₀, f'(a⁻¹·)⟩⟩(x) da dx` (`orbitalInner_chiProj`).  The
  map `a ↦ f'(a⁻¹·)` is locally constant and only `a` in the compact `agRange` contribute, so both
  `A_G`-integrals are the same finite sum `∑ w_τ (·)(τ)` (`integral_char_mul_eq_sum`), and the
  `G/A_G`-integral of a finite sum is computed with the integrability from `bp_thetaF_exists`.
* Continuity on `G_reg(F)`: dominated convergence (`continuousOn_chiAvg`). -/
theorem isThetaF_chiProj_avg {f₀ θ₀ : ↥d.G → ℂ} (hf₀ : f₀ ∈ testFunctions ↥d.G)
    (hcusp : IsStronglyCuspidalInline d f₀) (hθ₀ : IsThetaF d f₀ θ₀) :
    IsThetaF d (chiProj d χ f₀)
      (fun g => ∫ a : ↥d.AG, ((χ.toHom a : Circle) : ℂ) * θ₀ ((a : ↥d.G) * g) ∂Measure.haar) := by
  classical
  obtain ⟨_θb, -, -, -, hbp⟩ := LitTF.bp_thetaF_exists d f₀ hf₀ hcusp
  have hreg := hc_regularSet_open_conull d
  set R := regularSet d.G d.lie
  have hRae : ∀ᵐ g ∂(Measure.haar : Measure ↥d.G), g ∈ R := by
    rw [ae_iff]; exact hreg.2
  set S₀ := d.hcG '' tsupport f₀
  have hS₀ : S₀.Finite := d.finite_image_hcG hf₀.2
  set θ' : ↥d.G → ℂ := R.indicator θ₀
  have hθ'ae : θ' =ᵐ[Measure.haar] θ₀ := by
    filter_upwards [hRae] with g hg; exact Set.indicator_of_mem hg θ₀
  have hθ'li : LocallyIntegrable θ' Measure.haar := hθ₀.1.congr hθ'ae.symm
  have hθ'S : ∀ g, θ' g ≠ 0 → d.hcG g ∈ S₀ := by
    intro g hg
    by_contra hS
    by_cases hgR : g ∈ R
    · exact hg (show R.indicator θ₀ g = 0 by
        rw [Set.indicator_of_mem hgR]; exact isThetaF_eq_zero_of_hcG_notMem d hθ₀ hgR hS)
    · exact hg (Set.indicator_of_notMem hgR θ₀)
  have hθ'pair : ∀ k ∈ testFunctions ↥d.G, ∫ g, θ' g * k g ∂Measure.haar = orbitalPairing d f₀ k := by
    intro k hk
    rw [← hθ₀.2.2 k hk]
    exact integral_congr_ae (hθ'ae.mul (EventuallyEq.refl _ k))
  set avg' : ↥d.G → ℂ := fun g => ∫ a : ↥d.AG, ((χ.toHom a : Circle) : ℂ) * θ' ((a : ↥d.G) * g)
    ∂Measure.haar
  have havg : (fun g => ∫ a : ↥d.AG, ((χ.toHom a : Circle) : ℂ) * θ₀ ((a : ↥d.G) * g)
      ∂Measure.haar) =ᵐ[Measure.haar] avg' := by
    filter_upwards [hRae] with g hg
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    show _ = ((χ.toHom a : Circle) : ℂ) * R.indicator θ₀ ((a : ↥d.G) * g)
    rw [Set.indicator_of_mem (mul_mem_regularSet_of_mem_AG d a hg)]
  -- local integrability
  have hli' : LocallyIntegrable avg' Measure.haar := by
    intro x
    obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
    refine ⟨K, hKx, ?_⟩
    have hI := integrable_AG_prod d χ hθ'li hS₀ hθ'S (h := K.indicator 1)
      (measurable_one.indicator hK.measurableSet) (M := 1)
      (fun g => by by_cases hg : g ∈ K <;> simp [hg]) hK
      (fun g hg => by by_contra h; exact hg (Set.indicator_of_notMem h 1))
    have h2 := hI.integral_prod_right
    have e : (fun g : ↥d.G => ∫ a : ↥d.AG, ((χ.toHom (a, g).1 : Circle) : ℂ) *
        θ' (((a, g).1 : ↥d.G) * (a, g).2) * K.indicator 1 (a, g).2 ∂Measure.haar) =
        K.indicator avg' := by
      funext g
      by_cases hg : g ∈ K
      · simp only [Set.indicator_of_mem hg, Pi.one_apply, mul_one, avg']
      · simp only [Set.indicator_of_notMem hg, mul_zero, integral_zero]
    rw [e] at h2
    exact (integrable_indicator_iff hK.measurableSet).1 h2
  refine ⟨hli'.congr havg.symm, continuousOn_chiAvg d χ hθ₀ hf₀.2, fun f' hf' => ?_⟩
  -- the pairing
  set Φ : ↥d.AG → ↥d.G → ℂ := fun a g => f' ((a : ↥d.G)⁻¹ * g)
  have hΦtest : ∀ a, Φ a ∈ testFunctions ↥d.G := fun a => testFunctions_mul_left d hf' _
  obtain ⟨Rf, w, hRf, hdec⟩ := integral_char_mul_eq_sum d χ (isLocallyConstant_translate_AG d hf')
    (isCompact_agRange d hf₀.2 hf'.2)
  have hzero : ∀ a, a ∉ agRange d f₀ f' → ∀ y, orbitalInner d f₀ (Φ a) y = 0 :=
    fun a ha y => orbitalInner_translate_eq_zero d ha y
  obtain ⟨M, hM⟩ := hf'.1.continuous.bounded_above_of_compact_support hf'.2
  have hI := integrable_AG_prod d χ hθ'li hS₀ hθ'S hf'.1.continuous.measurable hM hf'.2
    (fun g hg => subset_tsupport f' hg)
  -- left side
  have hL : ∫ g, (∫ a : ↥d.AG, ((χ.toHom a : Circle) : ℂ) * θ₀ ((a : ↥d.G) * g) ∂Measure.haar) *
      f' g ∂Measure.haar = ∑ τ ∈ Rf, w τ * orbitalPairing d f₀ τ := by
    rw [integral_congr_ae (show (fun g => (∫ a : ↥d.AG, ((χ.toHom a : Circle) : ℂ) *
        θ₀ ((a : ↥d.G) * g) ∂Measure.haar) * f' g) =ᵐ[Measure.haar] fun g => avg' g * f' g from
        havg.mul (EventuallyEq.refl _ f'))]
    have e1 : ∀ g, avg' g * f' g = ∫ a : ↥d.AG, ((χ.toHom a : Circle) : ℂ) *
        θ' ((a : ↥d.G) * g) * f' g ∂Measure.haar := fun g => (integral_mul_const _ _).symm
    simp_rw [e1]
    rw [← integral_integral_swap (f := fun (a : ↥d.AG) (g : ↥d.G) =>
      ((χ.toHom a : Circle) : ℂ) * θ' ((a : ↥d.G) * g) * f' g) hI]
    have e2 : ∀ a : ↥d.AG, ∫ g, ((χ.toHom a : Circle) : ℂ) * θ' ((a : ↥d.G) * g) * f' g
        ∂Measure.haar = ((χ.toHom a : Circle) : ℂ) * orbitalPairing d f₀ (Φ a) := by
      intro a
      rw [← hθ'pair _ (hΦtest a), ← integral_const_mul,
        ← integral_mul_left_eq_self (fun g => ((χ.toHom a : Circle) : ℂ) * (θ' g * Φ a g))
          (a : ↥d.G)]
      congr 1; funext g
      simp only [Φ, inv_mul_cancel_left]; ring
    simp_rw [e2]
    refine hdec (fun τ => orbitalPairing d f₀ τ) fun a ha => ?_
    rw [orbitalPairing_eq]
    exact integral_eq_zero_of_ae (Eventually.of_forall fun x => hzero a ha _)
  -- right side
  have hR : orbitalPairing d (chiProj d χ f₀) f' = ∑ τ ∈ Rf, w τ * orbitalPairing d f₀ τ := by
    rw [orbitalPairing_eq]
    have e3 : ∀ x : d.GmodAG, orbitalInner d (chiProj d χ f₀) f' (Quotient.out x) =
        ∑ τ ∈ Rf, w τ * orbitalInner d f₀ τ (Quotient.out x) := by
      intro x
      rw [orbitalInner_chiProj d χ hf₀ hf']
      exact hdec (fun τ => orbitalInner d f₀ τ (Quotient.out x)) fun a ha => hzero a ha _
    simp_rw [e3]
    rw [integral_finsetSum _ fun τ hτ => ?_]
    · refine Finset.sum_congr rfl fun τ hτ => ?_
      rw [integral_const_mul, orbitalPairing_eq]
    · obtain ⟨a, rfl⟩ := hRf τ hτ
      exact ((hbp _ (hΦtest a)).1).const_mul _
  rw [hL, hR]

end Core2Cutoff

end GSpinGGP
