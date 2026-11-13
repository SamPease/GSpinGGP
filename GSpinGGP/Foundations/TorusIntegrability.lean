/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalGroups

/-!
# Local integrability of powers of eigenvalue-type functions (BP Lemma B.1.2)

General `p`-adic (in fact: locally compact nontrivially normed field) integrability lemmas behind
BP Astérisque 418, Lemma B.1.2(i),(ii) (stated there without proof), proved directly from the
scaling of Haar measure. `|·|_F` is the normalized absolute value `absF`.

* `distribHaarChar_eq_absF_pow`, `addHaar_smul_absF`: `d(c • v) = |c|_F^{dim V} dv`;
  `setLIntegral_smul_set`: the corresponding change of variables.
* `locallyIntegrable_of_homogeneous`: a function homogeneous of degree `κ > −dim V`
  (`f(c • x) = |c|_F^κ f(x)`) and locally integrable off `0` is locally integrable.
* `locallyIntegrable_prod_gauge_rpow`: `v ↦ ∏_i N_i(π_i v)^{a_i}` is locally integrable for linear
  maps `π_i` and gauges `N_i` of degree `e_i > 0` (continuous, positive off `0`,
  `N_i(c • y) = |c|_F^{e_i} N_i(y)`), provided `∑_{j∈J} e_j a_j > −rank (π_j)_{j∈J}` for all
  nonempty `J` (a sufficient condition; general form of B.1.2(ii)).
* `locallyIntegrable_prod_absF_rpow`: B.1.2(ii) (first part) for linearly independent forms over `F`.
* `integrable_of_chart`: integrability on a compact group from domination, at every translate, in
  a measure chart near `0` (the passage from the Lie algebra to the group in B.1.2(i)).
* Transport: `locallyIntegrable_comp_linearEquiv`, `locallyIntegrable_comp_fst`,
  `locallyIntegrable_comp_prodEquivOfIsCompl`.
-/

noncomputable section

open MeasureTheory Topology Filter Metric Set
open scoped Pointwise ENNReal NNReal

set_option linter.style.haveILetI false

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F] [LocallyCompactSpace F]

/-- `|a^n|_F = |a|_F^n`. -/
lemma absF_pow (a : F) (n : ℕ) : absF (a ^ n) = absF a ^ n := by
  induction n with
  | zero => simp [absF_one]
  | succ n ih => rw [pow_succ, absF_mul, ih, pow_succ]

section Scaling

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace F V] [FiniteDimensional F V]
  [MeasurableSpace V] [BorelSpace V]

/-- `d(c • v) = |c|_F^{dim V} dv`: the distributive Haar character of `Fˣ` on a finite-dimensional
`F`-vector space is `|·|_F^{dim V}`. -/
theorem distribHaarChar_eq_absF_pow [LocallyCompactSpace V] (c : Fˣ) :
    (distribHaarChar V c : ℝ) = absF (c : F) ^ Module.finrank F V := by
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : CompleteSpace F := complete_of_proper
  haveI : ProperSpace V := FiniteDimensional.proper F V
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  set n := Module.finrank F V
  let L : V ≃L[F] (Fin n → F) := (Module.finBasis F V).equivFun.toContinuousLinearEquiv
  let ν : Measure (Fin n → F) := Measure.pi fun _ => (Measure.addHaar : Measure F)
  let μ : Measure V := Measure.addHaar
  have hμ' : (μ.map L).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ≥0, μ.map L = κ • ν :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (μ.map L) ν⟩
  let B : Set F := closedBall 0 1
  let box : Set (Fin n → F) := Set.pi univ fun _ => B
  let s : Set V := L ⁻¹' box
  have hLm : Measurable L := L.continuous.measurable
  have hbox : MeasurableSet box := MeasurableSet.univ_pi fun _ => isClosed_closedBall.measurableSet
  have hs_eq : (c : Fˣ) • s = L ⁻¹' (Set.pi univ fun _ => (c : F) • B) := by
    ext v
    simp only [s, box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨w, hw, rfl⟩ i
      refine ⟨L w i, hw i (mem_univ _), ?_⟩
      simp
    · intro hv
      refine ⟨(c : Fˣ)⁻¹ • v, fun i _ => ?_, smul_inv_smul c v⟩
      obtain ⟨b, hb, hbv⟩ := hv i
      have : L ((c : Fˣ)⁻¹ • v) i = (c : F)⁻¹ * L v i := by simp [Units.smul_def]
      simp only [this, ← hbv, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]
      exact hb
  have hμs : μ s = κ * ν box := by
    rw [← Measure.map_apply hLm hbox, hκ]; rfl
  have hμcs : μ ((c : Fˣ) • s) = κ * ν (Set.pi univ fun _ => (c : F) • B) := by
    rw [hs_eq, ← Measure.map_apply hLm
      (MeasurableSet.univ_pi fun _ => (isClosed_closedBall.smul₀ _).measurableSet), hκ]; rfl
  have hcB : (Measure.addHaar : Measure F) ((c : F) • B) =
      ENNReal.ofReal (absF (c : F)) * Measure.addHaar B :=
    absF_haar _ c.ne_zero B
  have hνc : ν (Set.pi univ fun _ => (c : F) • B) =
      ENNReal.ofReal (absF (c : F) ^ n) * ν box := by
    simp only [ν, box, Measure.pi_pi, hcB, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    rw [ENNReal.ofReal_pow (absF_nonneg _)]
  have hs0 : μ s ≠ 0 := by
    refine (Measure.measure_pos_of_mem_nhds μ (x := 0) ?_).ne'
    refine L.continuous.continuousAt.preimage_mem_nhds ?_
    rw [map_zero]
    exact set_pi_mem_nhds finite_univ fun _ _ => closedBall_mem_nhds _ one_pos
  have hsfin : μ s ≠ ∞ := by
    refine (IsCompact.measure_lt_top ?_).ne
    have : IsCompact box := isCompact_univ_pi fun _ => isCompact_closedBall _ _
    simpa [s] using L.toHomeomorph.isCompact_preimage.mpr this
  have := distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (g := c) hs0 hsfin
    (r := ⟨absF (c : F) ^ n, pow_nonneg (absF_nonneg _) _⟩) (by
      rw [hμcs, hνc, hμs, ← mul_assoc, mul_comm (κ : ℝ≥0∞), mul_assoc]
      congr 1
      exact ENNReal.ofReal_eq_coe_nnreal _)
  rw [this]; rfl

/-- `μ(c • s) = |c|_F^{dim V} μ(s)` for an additive Haar measure on a finite-dimensional
`F`-vector space. -/
theorem addHaar_smul_absF (μ : Measure V) [μ.IsAddHaarMeasure] {c : F} (hc : c ≠ 0) (s : Set V) :
    μ (c • s) = ENNReal.ofReal (absF c ^ Module.finrank F V) * μ s := by
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : CompleteSpace F := complete_of_proper
  haveI : ProperSpace V := FiniteDimensional.proper F V
  have h := distribHaarChar_mul (μ := μ) (Units.mk0 c hc) s
  have h2 := distribHaarChar_eq_absF_pow (V := V) (Units.mk0 c hc)
  have hs : (Units.mk0 c hc • s : Set V) = c • s := rfl
  rw [hs] at h
  rw [← h, ← ENNReal.ofReal_coe_nnreal, h2]
  rfl

end Scaling

/-- `|·|_F` is monotone in the norm. -/
theorem absF_le_absF_of_norm_le {a b : F} (h : ‖a‖ ≤ ‖b‖) : absF a ≤ absF b := by
  by_cases ha : a = 0
  · rw [ha, absF_zero]; exact absF_nonneg b
  have hb : b ≠ 0 := by
    intro hb; rw [hb, norm_zero] at h; exact ha (norm_le_zero_iff.mp h)
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  let μ : Measure F := Measure.addHaar
  have hsub : a • closedBall (0 : F) 1 ⊆ b • closedBall (0 : F) 1 := by
    simp only [smul_closedBall _ _ zero_le_one, smul_zero, mul_one]
    exact closedBall_subset_closedBall h
  have hm := measure_mono (μ := μ) hsub
  rw [absF_haar μ ha, absF_haar μ hb] at hm
  have hpos := Metric.measure_closedBall_pos μ (0 : F) zero_lt_one
  have hfin := (isCompact_closedBall (0 : F) 1).measure_lt_top (μ := μ)
  have := (ENNReal.mul_le_mul_iff_left hpos.ne' hfin.ne).mp hm
  exact (ENNReal.ofReal_le_ofReal_iff (absF_nonneg b)).mp this

/-- `|a|_F < 1` when `‖a‖ < 1`. -/
theorem absF_lt_one_of_norm_lt_one {a : F} (h : ‖a‖ < 1) : absF a < 1 := by
  by_cases ha : a = 0
  · rw [ha, absF_zero]; exact zero_lt_one
  have hle : absF a ≤ 1 := by
    simpa [absF_one] using absF_le_absF_of_norm_le (a := a) (b := 1) (by simpa using h.le)
  refine lt_of_le_of_ne hle fun h1 => ?_
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  let μ : Measure F := Measure.addHaar
  let s : ℕ → Set F := fun k => closedBall 0 (‖a‖ ^ k)
  have hs : ∀ k, μ (s k) = μ (closedBall 0 1) := by
    intro k
    have : s k = a ^ k • closedBall (0 : F) 1 := by
      rw [smul_closedBall _ _ zero_le_one, smul_zero, mul_one, norm_pow]
    rw [this, absF_haar μ (pow_ne_zero k ha), absF_pow, h1, one_pow, ENNReal.ofReal_one, one_mul]
  have hanti : Antitone s := fun i j hij =>
    closedBall_subset_closedBall (pow_le_pow_of_le_one (norm_nonneg _) h.le hij)
  have hinter : (⋂ k, s k) = {0} := by
    ext x
    simp only [mem_iInter, mem_closedBall, dist_zero_right, mem_singleton_iff, s]
    constructor
    · intro hx
      by_contra hx0
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hx0) h
      exact absurd (hx k) (not_le.mpr hk)
    · rintro rfl k; simp
  have hfin := (isCompact_closedBall (0 : F) 1).measure_lt_top (μ := μ)
  have hm := hanti.measure_iInter (μ := μ)
    (fun k => isClosed_closedBall.measurableSet.nullMeasurableSet) ⟨0, by
      rw [hs]; exact hfin.ne⟩
  rw [hinter, measure_singleton] at hm
  simp only [hs, iInf_const] at hm
  exact (Metric.measure_closedBall_pos μ (0 : F) zero_lt_one).ne' hm.symm

section Scaling'

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace F V] [FiniteDimensional F V]
  [MeasurableSpace V] [BorelSpace V]

/-- Change of variables `x = c • y` for an additive Haar measure:
`∫_{c S} g = |c|_F^{dim V} ∫_S g(c y) dy`. -/
theorem setLIntegral_smul_set (μ : Measure V) [μ.IsAddHaarMeasure] {c : F} (hc : c ≠ 0)
    (g : V → ℝ≥0∞) {S : Set V} (hS : MeasurableSet S) :
    ∫⁻ x in c • S, g x ∂μ =
      ENNReal.ofReal (absF c ^ Module.finrank F V) * ∫⁻ y in S, g (c • y) ∂μ := by
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : CompleteSpace F := complete_of_proper
  haveI : ProperSpace V := FiniteDimensional.proper F V
  set d := Module.finrank F V
  let e : V ≃ᵐ V := MeasurableEquiv.smul₀ c hc
  have hmap : μ.map e = ENNReal.ofReal (absF c⁻¹ ^ d) • μ := by
    ext A hA
    rw [Measure.map_apply e.measurable hA, Measure.smul_apply, smul_eq_mul]
    have : (e : V → V) ⁻¹' A = c⁻¹ • A := preimage_smul₀ hc A
    rw [this, addHaar_smul_absF μ (inv_ne_zero hc)]
  have hcS : MeasurableSet (c • S) := hS.const_smul₀ c
  have h1 : ∫⁻ y in S, g (c • y) ∂μ = ∫⁻ y, (c • S).indicator g (e y) ∂μ := by
    rw [← lintegral_indicator hS]
    congr 1
    ext y
    have he : e y = c • y := rfl
    simp only [Set.indicator, he]
    classical
    change _ = if c • y ∈ c • S then g (c • y) else 0
    simp only [smul_mem_smul_set_iff₀ hc]
  rw [h1, ← lintegral_map_equiv, hmap, lintegral_smul_measure, lintegral_indicator hcS, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (pow_nonneg (absF_nonneg _) _), ← mul_pow, ← absF_mul,
    mul_inv_cancel₀ hc, absF_one, one_pow, ENNReal.ofReal_one, one_mul]

/-- **Homogeneous functions of degree `> −dim V` are locally integrable at `0`.**
If `f : V → ℝ` satisfies `f(c • x) = |c|_F^κ f(x)` (`c ≠ 0`) with `κ > −dim V`, and `f` is
locally integrable away from `0`, then `f` is locally integrable. (Decompose a ball into the
shells `ϖ^k R`, `R = {‖ϖ‖ ≤ ‖x‖ ≤ 1}`: the integral over `ϖ^k R` is
`(|ϖ|^{dim V + κ})^k ∫_R |f|`, a convergent geometric series.) -/
theorem locallyIntegrable_of_homogeneous (μ : Measure V) [μ.IsAddHaarMeasure] {f : V → ℝ}
    {κ : ℝ} (hκ : -(Module.finrank F V : ℝ) < κ)
    (hhom : ∀ c : F, c ≠ 0 → ∀ x, f (c • x) = absF c ^ κ * f x)
    (hf : LocallyIntegrableOn f {0}ᶜ μ) : LocallyIntegrable f μ := by
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : CompleteSpace F := complete_of_proper
  haveI : ProperSpace V := FiniteDimensional.proper F V
  set d := Module.finrank F V
  rcases Nat.eq_zero_or_pos d with hd | hd
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp hd
    have : f = fun _ => f 0 := funext fun x => congrArg f (Subsingleton.elim x 0)
    rw [this]; exact locallyIntegrable_const _
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos hd
  haveI := Module.punctured_nhds_neBot F V (0 : V)
  have h0 : μ {0} = 0 := measure_singleton 0
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one F
  have hϖ : ϖ ≠ 0 := norm_pos_iff.mp hϖ0
  set r := ‖ϖ‖
  set q := absF ϖ
  have hq0 : 0 < q := absF_pos hϖ
  have hq1 : q < 1 := absF_lt_one_of_norm_lt_one hϖ1
  set ρ := q ^ ((d : ℝ) + κ)
  have hρ1 : ρ < 1 := Real.rpow_lt_one hq0.le hq1 (by linarith)
  have hρ0 : 0 ≤ ρ := (Real.rpow_pos_of_pos hq0 _).le
  -- the compact shell
  set R : Set V := closedBall 0 1 \ ball 0 r
  have hRc : IsCompact R := (isCompact_closedBall 0 1).diff isOpen_ball
  have hRm : MeasurableSet R := measurableSet_closedBall.diff measurableSet_ball
  have hR0 : R ⊆ {0}ᶜ := by
    intro x hx h
    rw [mem_singleton_iff] at h
    exact hx.2 (by rw [h]; exact mem_ball_self hϖ0)
  have hRi : IntegrableOn f R μ := hf.integrableOn_compact_subset hR0 hRc
  set M := ∫⁻ y in R, ‖f y‖ₑ ∂μ
  have hM : M < ∞ := hRi.2
  -- the shells
  have hshell : ∀ k : ℕ, ∫⁻ x in ϖ ^ k • R, ‖f x‖ₑ ∂μ = ENNReal.ofReal ρ ^ k * M := by
    intro k
    have hk : ϖ ^ k ≠ 0 := pow_ne_zero k hϖ
    rw [setLIntegral_smul_set μ hk _ hRm]
    have : ∀ y, ‖f (ϖ ^ k • y)‖ₑ = ENNReal.ofReal (absF (ϖ ^ k) ^ κ) * ‖f y‖ₑ := by
      intro y
      rw [hhom _ hk, enorm_mul, Real.enorm_of_nonneg (Real.rpow_nonneg (absF_nonneg _) _)]
    simp_rw [this]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
      ← ENNReal.ofReal_mul (pow_nonneg (absF_nonneg _) _), ← ENNReal.ofReal_pow hρ0]
    congr 2
    rw [absF_pow, ← Real.rpow_natCast (absF ϖ ^ k) d, ← Real.rpow_add (pow_pos hq0 k),
      ← Real.rpow_natCast (absF ϖ) k, ← Real.rpow_mul hq0.le, ← Real.rpow_natCast ρ k,
      Real.rpow_natCast, ← Real.rpow_mul_natCast hq0.le, mul_comm]
  have hcover : closedBall (0 : V) 1 ⊆ {0} ∪ ⋃ k : ℕ, ϖ ^ k • R := by
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    right
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hex : ∃ k : ℕ, r ^ (k + 1) ≤ ‖x‖ := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hxpos hϖ1
      exact ⟨n, ((pow_le_pow_of_le_one hϖ0.le hϖ1.le (Nat.le_succ n)).trans hn.le)⟩
    classical
    set k := Nat.find hex
    have hk1 : r ^ (k + 1) ≤ ‖x‖ := Nat.find_spec hex
    have hk2 : ‖x‖ ≤ r ^ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, pow_zero]; simpa using hx
      · obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have := Nat.find_min hex (show j < k by omega)
        rw [hj]; exact (not_le.mp this).le
    refine mem_iUnion.mpr ⟨k, ?_⟩
    rw [mem_smul_set_iff_inv_smul_mem₀ (pow_ne_zero k hϖ)]
    have hrk : 0 < r ^ k := pow_pos hϖ0 k
    have hn : ‖(ϖ ^ k)⁻¹ • x‖ = ‖x‖ / r ^ k := by
      rw [norm_smul, norm_inv, norm_pow, inv_mul_eq_div]
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right, hn, div_le_one hrk]; exact hk2
    · rw [mem_ball, dist_zero_right, hn, not_lt, le_div_iff₀ hrk, ← pow_succ']; exact hk1
  have hball : IntegrableOn f (closedBall 0 1) μ := by
    refine ⟨?_, ?_⟩
    · have hae : AEStronglyMeasurable f μ := by
        have := hf.aestronglyMeasurable
        rwa [restrict_compl_singleton] at this
      exact hae.restrict
    · show ∫⁻ x in closedBall 0 1, ‖f x‖ₑ ∂μ < ∞
      calc ∫⁻ x in closedBall 0 1, ‖f x‖ₑ ∂μ
          ≤ ∫⁻ x in {0} ∪ ⋃ k : ℕ, ϖ ^ k • R, ‖f x‖ₑ ∂μ := lintegral_mono_set hcover
        _ ≤ ∫⁻ x in {0}, ‖f x‖ₑ ∂μ + ∫⁻ x in ⋃ k : ℕ, ϖ ^ k • R, ‖f x‖ₑ ∂μ :=
            lintegral_union_le _ _ _
        _ ≤ 0 + ∑' k : ℕ, ∫⁻ x in ϖ ^ k • R, ‖f x‖ₑ ∂μ := by
            gcongr
            · rw [Measure.restrict_eq_zero.mpr h0, lintegral_zero_measure]
            · exact lintegral_iUnion_le _ _
        _ = (1 - ENNReal.ofReal ρ)⁻¹ * M := by
            simp_rw [hshell, zero_add]
            rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
        _ < ∞ := by
            refine ENNReal.mul_lt_top ?_ hM
            rw [ENNReal.inv_lt_top, tsub_pos_iff_lt, ENNReal.ofReal_lt_one]
            exact hρ1
  intro x
  by_cases hx : x = 0
  · rw [hx]; exact ⟨_, closedBall_mem_nhds _ one_pos, hball⟩
  · have := hf x hx
    rwa [isOpen_compl_singleton.nhdsWithin_eq hx] at this

end Scaling'

section Transport

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace F V] [FiniteDimensional F V]
  [MeasurableSpace V] [BorelSpace V]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace F W] [FiniteDimensional F W]
  [MeasurableSpace W] [BorelSpace W]

/-- Local integrability for additive Haar measures is invariant under linear isomorphisms of
finite-dimensional `F`-vector spaces. -/
theorem locallyIntegrable_comp_linearEquiv (μ : Measure V) [μ.IsAddHaarMeasure]
    (ν : Measure W) [ν.IsAddHaarMeasure] (e : V ≃ₗ[F] W) {g : W → ℝ}
    (hg : LocallyIntegrable g ν) : LocallyIntegrable (g ∘ e) μ := by
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : CompleteSpace F := complete_of_proper
  haveI : ProperSpace V := FiniteDimensional.proper F V
  haveI : ProperSpace W := FiniteDimensional.proper F W
  let E : V ≃L[F] W := e.toContinuousLinearEquiv
  haveI : (μ.map E).IsAddHaarMeasure := E.isAddHaarMeasure_map μ
  have hmap : μ.map E = _ • ν := Measure.isAddLeftInvariant_eq_smul _ ν
  have h1 : LocallyIntegrable g (μ.map E) := by
    rw [hmap]
    intro x
    obtain ⟨U, hU, hi⟩ := hg x
    refine ⟨U, hU, ?_⟩
    rw [IntegrableOn, Measure.restrict_smul]
    exact hi.smul_measure_nnreal
  exact (locallyIntegrable_map_homeomorph E.toHomeomorph).mp h1

omit [NormedSpace F V] [FiniteDimensional F V] [BorelSpace V] [BorelSpace W] in
/-- A function of the first coordinate, locally integrable there, is locally integrable on a
product with a locally finite measure on the second factor. -/
theorem locallyIntegrable_comp_fst [LocallyCompactSpace W] (μ : Measure V) [SFinite μ]
    (ν : Measure W) [IsLocallyFiniteMeasure ν] [SFinite ν] {g : V → ℝ}
    (hg : LocallyIntegrable g μ) : LocallyIntegrable (fun z : V × W => g z.1) (μ.prod ν) := by
  rintro ⟨x, y⟩
  obtain ⟨U, hU, hi⟩ := hg x
  obtain ⟨K, hK, hKy⟩ := exists_compact_mem_nhds y
  refine ⟨U ×ˢ K, prod_mem_nhds hU hKy, ?_⟩
  rw [IntegrableOn, ← Measure.prod_restrict]
  haveI : IsFiniteMeasure (ν.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact hi.comp_fst _

/-- If `V = C ⊕ K` and `g` is locally integrable on `C`, then `v ↦ g(c)`, `v = c + k`, is
locally integrable on `V` (all measures additive Haar measures). -/
theorem locallyIntegrable_comp_prodEquivOfIsCompl (μ : Measure V) [μ.IsAddHaarMeasure]
    {C K : Submodule F V} (h : IsCompl C K) [MeasurableSpace C] [BorelSpace C]
    [MeasurableSpace K] [BorelSpace K] (μC : Measure C) [μC.IsAddHaarMeasure]
    (μK : Measure K) [μK.IsAddHaarMeasure] {g : C → ℝ} (hg : LocallyIntegrable g μC) :
    LocallyIntegrable (fun v => g ((Submodule.prodEquivOfIsCompl C K h).symm v).1) μ := by
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : CompleteSpace F := complete_of_proper
  haveI : ProperSpace C := FiniteDimensional.proper F C
  haveI : ProperSpace K := FiniteDimensional.proper F K
  have h1 := locallyIntegrable_comp_fst μC μK hg
  exact locallyIntegrable_comp_linearEquiv μ (μC.prod μK)
    (Submodule.prodEquivOfIsCompl C K h).symm h1

end Transport

section Gauge

universe u

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace F (E i)]

/-- **Local integrability of products of powers of gauges of linear maps** (a general form of
BP Astérisque 418, Lemma B.1.2(ii)). Let `π_i : V → E_i` (`i ∈ s`) be linear maps and
`N_i : E_i → ℝ` continuous *gauges* of degree `e_i > 0`: positive off `0` and homogeneous for the
normalized absolute value, `N_i(c • y) = |c|_F^{e_i} N_i(y)`. Suppose that for every nonempty
`J ⊆ s`, `∑_{j ∈ J} e_j a_j > −codim (⋂_{j∈J} ker π_j)` (the codimension is the rank of
`(π_j)_{j ∈ J}`).
Then `v ↦ ∏_{i ∈ s} N_i(π_i v)^{a_i}` is locally integrable for any additive Haar measure.
The condition over all `J` is sufficient, not necessary (with exponents of mixed sign it is
stronger than needed).

Intended applications (only the first case below, forms over `F`, is derived here:
`locallyIntegrable_prod_absF_rpow`): BP's case, `N_i = |·|` on a finite extension `E ⊇ F`
(normalized to extend `|·|_F`, degree `1`) and `π_i = λ_i` linear forms with values in `E`,
linearly independent over `E`, `a_i = s − 1 > −1` (the rank of `(λ_j)_{j∈J}` over `F` is at least
`|J|`); and the anisotropic blocks of a torus, `π_i` the projection to a block `𝔱_i` acting on
`W_i` and `N_i = |det(·|_{W_i})|_F`, of degree `dim W_i`, nonzero off `0` when `W_i` is a vector
space over a field containing `𝔱_i`.

Proof: strong induction on `s`. Choosing a complement `C` of `⋂_{i∈s} ker π_i` reduces to the
case of trivial common kernel; then the function is homogeneous of degree
`∑_{i∈s} e_i a_i > −dim V`
(`locallyIntegrable_of_homogeneous`), and near `v₀ ≠ 0` it is the product of the function for
the smaller family `{i : π_i v₀ = 0}` and a function continuous near `v₀`. -/
theorem locallyIntegrable_prod_gauge_rpow (N : ∀ i, E i → ℝ) (hNc : ∀ i, Continuous (N i))
    (hNpos : ∀ i y, y ≠ 0 → 0 < N i y) (e : ι → ℝ) (he : ∀ i, 0 < e i)
    (hNhom : ∀ i (c : F) y, N i (c • y) = absF c ^ e i * N i y) (a : ι → ℝ) (s : Finset ι) {V : Type u} [NormedAddCommGroup V] [NormedSpace F V]
    [FiniteDimensional F V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (π : ∀ i, V →ₗ[F] E i)
    (hcond : ∀ J ⊆ s, J.Nonempty →
      -(Module.finrank F (LinearMap.range (LinearMap.pi fun j : J => π j)) : ℝ) < ∑ j ∈ J, e j * a j) :
    LocallyIntegrable (fun v => ∏ i ∈ s, N i (π i v) ^ a i) μ := by
  classical
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : CompleteSpace F := complete_of_proper
  have hN0 : ∀ i y, 0 ≤ N i y := by
    intro i y
    by_cases hy : y = 0
    · have := hNhom i 0 y
      rw [zero_smul, absF_zero, Real.zero_rpow (he i).ne', zero_mul, ← hy] at this
      rw [this]
    · exact (hNpos i y hy).le
  induction s using Finset.strongInduction generalizing V with
  | H s ih =>
  -- the case of trivial common kernel
  have caseA : ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace F W] [FiniteDimensional F W]
      [MeasurableSpace W] [BorelSpace W] (μW : Measure W) [μW.IsAddHaarMeasure]
      (ρ : ∀ i, W →ₗ[F] E i), (∀ J ⊆ s, J.Nonempty →
        -(Module.finrank F (LinearMap.range (LinearMap.pi fun j : J => ρ j)) : ℝ) < ∑ j ∈ J, e j * a j) →
      (∀ w, (∀ i ∈ s, ρ i w = 0) → w = 0) →
      LocallyIntegrable (fun w => ∏ i ∈ s, N i (ρ i w) ^ a i) μW := by
    intro W _ _ _ _ _ μW _ ρ hc hker
    haveI : ProperSpace W := FiniteDimensional.proper F W
    have hNcont : ∀ i, Continuous fun w => N i (ρ i w) := fun i =>
      (hNc i).comp (ρ i).continuous_of_finiteDimensional
    rcases s.eq_empty_or_nonempty with hs | hs
    · simp only [hs, Finset.prod_empty]; exact locallyIntegrable_const 1
    refine locallyIntegrable_of_homogeneous (F := F) μW (κ := ∑ i ∈ s, e i * a i) ?_ ?_ ?_
    · have h := hc s subset_rfl hs
      have hk : LinearMap.ker (LinearMap.pi fun j : s => ρ j) = ⊥ := by
        rw [eq_bot_iff]
        intro w hw
        rw [LinearMap.mem_ker] at hw
        rw [Submodule.mem_bot]
        exact hker w fun i hi => congrFun hw ⟨i, hi⟩
      have := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi fun j : s => ρ j)
      rw [hk, finrank_bot, add_zero] at this
      rwa [this] at h
    · intro c hc w
      simp only [map_smul, hNhom]
      rw [Real.rpow_sum_of_pos (absF_pos hc), ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Real.mul_rpow (Real.rpow_nonneg (absF_nonneg _) _) (hN0 _ _),
        ← Real.rpow_mul (absF_nonneg _)]
    · intro v₀ hv₀
      have hv₀' : v₀ ≠ 0 := hv₀
      set t := s.filter (fun i => ρ i v₀ = 0)
      set S' := s.filter (fun i => ¬ ρ i v₀ = 0)
      have hts : t ⊂ s := by
        rw [Finset.filter_ssubset]
        by_contra h
        push Not at h
        exact hv₀' (hker v₀ h)
      have ht := ih t hts μW ρ fun J hJ hJne =>
        hc J (hJ.trans (Finset.filter_subset _ _)) hJne
      set U : Set W := ⋂ i ∈ S', {w | ρ i w ≠ 0}
      have hUo : IsOpen U := isOpen_biInter_finset fun i _ =>
        isOpen_ne_fun (ρ i).continuous_of_finiteDimensional continuous_const
      have hv₀U : v₀ ∈ U := by
        simp only [U, mem_iInter, mem_ofPred_eq]
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUo v₀ hv₀U
      set K := closedBall v₀ (ε / 2)
      have hKU : K ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hball
      have hgc : ContinuousOn (fun w => ∏ i ∈ S', N i (ρ i w) ^ a i) K := by
        refine continuousOn_finsetProd _ fun i hi w hw => ?_
        have hwU := hKU hw
        simp only [U, mem_iInter, mem_ofPred_eq] at hwU
        exact ((hNcont i).continuousAt.rpow_const
          (Or.inl (hNpos i _ (hwU i hi)).ne')).continuousWithinAt
      have hint := (ht.integrableOn_isCompact (isCompact_closedBall _ _)).mul_continuousOn hgc
        (isCompact_closedBall _ _)
      have hfg : (fun w => ∏ i ∈ s, N i (ρ i w) ^ a i) =
          fun w => (∏ i ∈ t, N i (ρ i w) ^ a i) * ∏ i ∈ S', N i (ρ i w) ^ a i :=
        funext fun w => (Finset.prod_filter_mul_prod_filter_not s (fun i => ρ i v₀ = 0) _).symm
      have : IntegrableAtFilter (fun w => ∏ i ∈ s, N i (ρ i w) ^ a i) (𝓝 v₀) μW :=
        ⟨K, closedBall_mem_nhds _ (half_pos hε), by rw [hfg]; exact hint⟩
      exact this.filter_mono nhdsWithin_le_nhds
  -- reduction to a complement of the common kernel
  haveI : ProperSpace V := FiniteDimensional.proper F V
  set Kr : Submodule F V := ⨅ i ∈ s, LinearMap.ker (π i)
  have hKr : ∀ k ∈ Kr, ∀ i ∈ s, π i k = 0 := by
    intro k hk i hi
    simp only [Kr, Submodule.mem_iInf, LinearMap.mem_ker] at hk
    exact hk i hi
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl Kr
  letI : MeasurableSpace C := borel C
  haveI : BorelSpace C := ⟨rfl⟩
  letI : MeasurableSpace Kr := borel Kr
  haveI : BorelSpace Kr := ⟨rfl⟩
  set ρ : ∀ i, C →ₗ[F] E i := fun i => (π i).comp C.subtype
  have hcondC : ∀ J ⊆ s, J.Nonempty →
      -(Module.finrank F (LinearMap.range (LinearMap.pi fun j : J => ρ j)) : ℝ) <
        ∑ j ∈ J, e j * a j := by
    intro J hJ hJne
    have hrange : LinearMap.range (LinearMap.pi fun j : J => ρ j) =
        LinearMap.range (LinearMap.pi fun j : J => π j) := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨c, rfl⟩
        exact ⟨c, rfl⟩
      · rintro _ ⟨v, rfl⟩
        have hv : v ∈ Kr ⊔ C := by rw [hC.sup_eq_top]; exact Submodule.mem_top
        obtain ⟨k, hk, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
        refine ⟨⟨c, hc⟩, ?_⟩
        funext j
        simp [ρ, hKr k hk j (hJ j.2)]
    rw [hrange]
    exact hcond J hJ hJne
  have hkerC : ∀ c : C, (∀ i ∈ s, ρ i c = 0) → c = 0 := by
    intro c hc
    have h1 : (c : V) ∈ Kr := by
      simp only [Kr, Submodule.mem_iInf, LinearMap.mem_ker]
      exact hc
    have h2 : (c : V) ∈ Kr ⊓ C := ⟨h1, c.2⟩
    rw [hC.inf_eq_bot, Submodule.mem_bot] at h2
    exact Subtype.ext h2
  have hA := caseA (Measure.addHaar : Measure C) ρ hcondC hkerC
  have hB := locallyIntegrable_comp_prodEquivOfIsCompl μ hC.symm (Measure.addHaar : Measure C)
    (Measure.addHaar : Measure Kr) hA
  convert hB using 2 with v
  refine Finset.prod_congr rfl fun i hi => ?_
  set x := (Submodule.prodEquivOfIsCompl C Kr hC.symm).symm v
  have hv : v = (x.1 : V) + (x.2 : V) := by
    have := (Submodule.prodEquivOfIsCompl C Kr hC.symm).apply_symm_apply v
    rw [Submodule.coe_prodEquivOfIsCompl'] at this
    exact this.symm
  simp only [ρ, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [hv, map_add, hKr _ x.2.2 i hi, add_zero]

end Gauge

section Forms

/-- Linearly independent linear forms `φ_j`, `j ∈ J`, have joint rank `|J|`. -/
theorem finrank_range_pi_of_linearIndependent {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] {ι : Type*} {φ : ι → Module.Dual K W}
    (hφ : LinearIndependent K φ) (J : Finset ι) :
    Module.finrank K (LinearMap.range (LinearMap.pi fun j : J => φ j)) = J.card := by
  have hli : LinearIndependent K (fun j : J => ⇑(φ j)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    exact Fintype.linearIndependent_iff.mp (hφ.comp _ Subtype.val_injective) c
      (LinearMap.ext fun w => by simpa using congrFun hc w)
  have hspan := span_flip_eq_top_iff_linearIndependent.mpr hli
  have hsurj : LinearMap.range (LinearMap.pi fun j : J => φ j) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact ⟨w, rfl⟩
  rw [hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]


/-- `|·|_F` is continuous at `0`. -/
theorem continuousAt_absF_zero : ContinuousAt (absF (F := F)) 0 := by
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one F
  have hϖ : ϖ ≠ 0 := norm_pos_iff.mp hϖ0
  have hq0 := absF_pos hϖ
  have hq1 := absF_lt_one_of_norm_lt_one hϖ1
  rw [ContinuousAt, absF_zero]
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hq1
  filter_upwards [closedBall_mem_nhds (0 : F) (pow_pos hϖ0 k)] with x hx
  rw [mem_closedBall, dist_zero_right] at hx
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (absF_nonneg x)]
  refine lt_of_le_of_lt ?_ hk
  rw [← absF_pow]
  exact absF_le_absF_of_norm_le (by rwa [norm_pow])

/-- Over an ultrametric local field, `|·|_F` is continuous. -/
theorem continuous_absF [IsUltrametricDist F] : Continuous (absF (F := F)) := by
  refine continuous_iff_continuousAt.mpr fun a => ?_
  by_cases ha : a = 0
  · rw [ha]; exact continuousAt_absF_zero
  · exact continuousAt_absF ha

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace F V] [FiniteDimensional F V]
  [MeasurableSpace V] [BorelSpace V]

/-- **BP Astérisque 418, Lemma B.1.2(ii), first part, for forms defined over `F`**: for linearly
independent `λ_1, …, λ_n ∈ V^*` and `σ > 0`, `v ↦ ∏ |λ_i(v)|_F^{σ−1}` is locally integrable on `V`.
BP's complex `s` with `Re s > 0` reduces to real `σ = Re s`, since `|x^{s−1}| = |x|^{Re s − 1}`.
Stated for ultrametric (`p`-adic) `F`. (For forms defined over an extension of `F` use
`locallyIntegrable_prod_gauge_rpow` with `N = |·|_E`.) -/
theorem locallyIntegrable_prod_absF_rpow [IsUltrametricDist F] (μ : Measure V)
    [μ.IsAddHaarMeasure] {ι : Type*} [Fintype ι] {φ : ι → Module.Dual F V}
    (hφ : LinearIndependent F φ) {σ : ℝ} (hσ : 0 < σ) :
    LocallyIntegrable (fun v => ∏ i, absF (φ i v) ^ (σ - 1)) μ := by
  refine locallyIntegrable_prod_gauge_rpow (E := fun _ => F) (fun _ => absF)
    (fun _ => continuous_absF) (fun _ _ hy => absF_pos hy) (fun _ => 1) (fun _ => one_pos)
    (fun _ c y => by rw [Real.rpow_one]; exact absF_mul c y)
    (fun _ => σ - 1) Finset.univ μ φ fun J _ hJ => ?_
  rw [finrank_range_pi_of_linearIndependent hφ, Finset.sum_const, nsmul_eq_mul, one_mul]
  have : (0 : ℝ) < J.card := by exact_mod_cast hJ.card_pos
  nlinarith

end Forms

section Chart

/-- **Integrability on a compact group from local integrability in a measure chart** (the
passage from the Lie algebra to the group in BP Astérisque 418, Lemma B.1.2(i)). Let `Q` be a compact group with a
finite left-invariant measure `ν`, and `Φ : 𝔤 → Q` a chart near `0`: continuous on an open
`U ∋ 0`, with `Φ(W)` a neighbourhood of `1` for every neighbourhood `W` of `0`, and carrying
`μ` to `ν`: `μ(S) = ν(Φ(S))` for measurable `S ⊆ U` (as `exp` does, `ExpHaar`). If `f` is
measurable and, for every `q₀ ∈ Q`, `|f(q₀ Φ(X))|` is bounded near `0` by a function `g`
integrable near `0`, then `f` is `ν`-integrable. For `T(F)` itself (not compact), apply it on a
compact open subgroup and its translates. -/
theorem integrable_of_chart {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q] (ν : Measure Q) [ν.IsMulLeftInvariant]
    [IsFiniteMeasure ν] {𝔤 : Type*} [TopologicalSpace 𝔤] [Zero 𝔤] [MeasurableSpace 𝔤]
    [OpensMeasurableSpace 𝔤] (μ : Measure 𝔤) (Φ : 𝔤 → Q) {U : Set 𝔤} (hUo : IsOpen U)
    (hU0 : (0 : 𝔤) ∈ U) (hΦc : ContinuousOn Φ U)
    (hΦn : ∀ W ∈ 𝓝 (0 : 𝔤), Φ '' W ∈ 𝓝 (1 : Q))
    (hΦμ : ∀ S ⊆ U, MeasurableSet S → μ S = ν (Φ '' S))
    {f : Q → ℝ} (hf : AEStronglyMeasurable f ν)
    (hloc : ∀ q₀ : Q, ∃ g : 𝔤 → ℝ, IntegrableAtFilter g (𝓝 0) μ ∧
      ∀ᶠ X in 𝓝 0, ‖f (q₀ * Φ X)‖ ≤ g X) :
    Integrable f ν := by
  classical
  -- for each `q₀`, a neighbourhood `q₀ Φ(W)` on which `f` is integrable
  have key : ∀ q₀ : Q, ∃ O ∈ 𝓝 q₀, IntegrableOn f O ν := by
    intro q₀
    obtain ⟨g, ⟨W₁, hW₁, hint⟩, hbd⟩ := hloc q₀
    set W₀ := W₁ ∩ {X | ‖f (q₀ * Φ X)‖ ≤ g X}
    have hW₀ : W₀ ∈ 𝓝 (0 : 𝔤) := inter_mem hW₁ hbd
    set W := interior W₀ ∩ U
    have hWo : IsOpen W := isOpen_interior.inter hUo
    have hW : W ∈ 𝓝 (0 : 𝔤) := inter_mem (interior_mem_nhds.mpr hW₀) (hUo.mem_nhds hU0)
    have hWW₀ : W ⊆ W₀ := inter_subset_left.trans interior_subset
    have hWU : W ⊆ U := inter_subset_right
    have hWm : MeasurableSet W := hWo.measurableSet
    set Φ' : 𝔤 → Q := W.piecewise Φ (fun _ => 1)
    have hΦ'm : Measurable Φ' :=
      (hΦc.mono hWU).measurable_piecewise continuousOn_const hWm
    have hΦ'W : ∀ X ∈ W, Φ' X = Φ X := fun X hX => piecewise_eq_of_mem _ _ _ hX
    -- `Φ` carries `μ|W` to `ν|Φ(W)`
    have hmap1 : (μ.restrict W).map Φ' = ν.restrict (Φ '' W) := by
      ext B hB
      rw [Measure.map_apply hΦ'm hB, Measure.restrict_apply (hΦ'm hB),
        Measure.restrict_apply hB]
      rw [hΦμ _ (inter_subset_right.trans hWU) ((hΦ'm hB).inter hWm)]
      congr 1
      ext y
      simp only [mem_image, mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨X, ⟨hXB, hXW⟩, rfl⟩
        exact ⟨by rw [← hΦ'W X hXW]; exact hXB, X, hXW, rfl⟩
      · rintro ⟨hyB, X, hXW, rfl⟩
        exact ⟨X, ⟨by rw [hΦ'W X hXW]; exact hyB, hXW⟩, rfl⟩
    -- left translation by `q₀`
    set O : Set Q := (q₀⁻¹ * ·) ⁻¹' (Φ '' W)
    have hmap2 : (ν.restrict (Φ '' W)).map (q₀ * ·) = ν.restrict O := by
      ext B hB
      rw [Measure.map_apply (measurable_const_mul q₀) hB,
        Measure.restrict_apply (measurable_const_mul q₀ hB), Measure.restrict_apply hB,
        ← measure_preimage_mul ν q₀ (B ∩ O)]
      congr 1
      ext y
      simp [O]
    have hmap : (μ.restrict W).map (fun X => q₀ * Φ' X) = ν.restrict O := by
      rw [← hmap2, ← hmap1, Measure.map_map (measurable_const_mul q₀) hΦ'm]
      rfl
    refine ⟨O, ?_, ?_⟩
    · refine (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_
      simpa using hΦn W hW
    · refine ⟨hf.restrict, ?_⟩
      show ∫⁻ y in O, ‖f y‖ₑ ∂ν < ∞
      have hm : Measurable fun X => q₀ * Φ' X := (measurable_const_mul q₀).comp hΦ'm
      have hae : AEMeasurable (fun y => ‖f y‖ₑ) ((μ.restrict W).map fun X => q₀ * Φ' X) := by
        rw [hmap]; exact hf.restrict.enorm
      rw [← hmap, lintegral_map' hae hm.aemeasurable]
      have hW0 : IntegrableOn g W μ := hint.mono_set (hWW₀.trans inter_subset_left)
      calc ∫⁻ X in W, ‖f (q₀ * Φ' X)‖ₑ ∂μ ≤ ∫⁻ X in W, ‖g X‖ₑ ∂μ := by
            refine setLIntegral_mono' hWm fun X hX => ?_
            rw [hΦ'W X hX, ← ofReal_norm, ← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal ((hWW₀ hX).2.trans (Real.le_norm_self _))
        _ < ∞ := hW0.2
  choose O hO hOi using key
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover O fun q _ => hO q
  have : IntegrableOn f (⋃ q ∈ t, O q) ν := integrableOn_finset_iUnion.mpr fun q _ => hOi q
  rw [← integrableOn_univ]
  exact this.mono_set ht

end Chart

end GSpinGGP
