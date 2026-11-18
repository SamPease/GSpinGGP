/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.HarmonicAnalysis.LogNorm
import GSpinGGP.HarmonicAnalysis.RelativeXi

/-!
# Polynomial growth and the integrability of `Ξ^{H\G}` (BP Prop 6.7.1(iii), (iv))

Beuzart-Plessis (Astérisque 418, proof of Prop 6.7.1(iii), pp. 151–152; Thesis Prop 8.4.1)
deduces the convergence of `∫_{H\G} Ξ^{H\G}(x)² σ_{H\G}(x)^{-d} dx` from

* (6.7.7) **polynomial growth** of `H(F)\G(F)`: the ball `{σ_{H\G} < R}` is covered by
  `≪ (1 + R)^N` translates `xC`; and
* the fact that on each `xC`, `Ξ^{H\G}² = vol(xC)^{-1}` up to a bounded factor
  (Prop 6.7.1(i)(a)), so that `∫_{xC} Ξ^{H\G}(y)² dy ≪ 1`.

He proves (6.7.7) from the weak Cartan decomposition `G = H A₀⁺ A K` (6.7.11), the comparison
`σ_{H\G} ∼ σ_G` on `A₀⁺A` (Prop 6.7.1(ii)(b)) and the polynomial growth of `A_min` (6.7.12).
This file proves all of this for an abstract quotient `π : G → X` with a right-invariant
measure (`IsInvariantQuotient`, `HarmonicAnalysis/RelativeXi.lean`), using no reductive
structure: no compactness of the centre and no unimodularity enter.

## Main definitions

* `HasPolynomialGrowth π σX D`: BP (6.7.7) for a compact covering set `D` (BP takes `D = C`;
  any compact `D` does, see `IsInvariantQuotient.exists_ofReal_relXi_sq_le`).
* `WeakCartanData π τ`: the input of BP's proof of (6.7.7): a set `S ⊆ G` and a compact `K` with
  `G = π⁻¹(π(S K))` (BP (6.7.11), `X = H\G`), the inequality `τ ≪ σ_X` on `S` (the nontrivial half
  of BP Prop 6.7.1(ii)(b)), and polynomial growth of `S` for `τ` (BP (6.7.12)), all for a log-norm
  `τ` on `G` and `σ_X = π_* τ` (`fiberInf`).

## Main results

* `IsInvariantQuotient.lintegral_relXi_sq_rpow_neg_lt_top` and
  `IsInvariantQuotient.integrable_relXi_sq_rpow_neg`: **BP Prop 6.7.1(iii)**, for every
  `d > N + 1`.
* `IsInvariantQuotient.lintegral_indicator_relXi_sq_rpow_le`: **BP Prop 6.7.1(iv)**:
  `∫_{σ_X ≤ c} Ξ(x)² σ_X(x)^d dx ≪ c^{N + d}`.
* `WeakCartanData.hasPolynomialGrowth`: BP (6.7.11) + (ii)(b) + (6.7.12) ⇒ (6.7.7).
* `IsInvariantQuotient.exists_integrable_of_weakCartanData`: Prop 6.7.1(iii) from a
  `WeakCartanData`, with the measurability of `Ξ` from outer regularity of `μ`.
-/

open MeasureTheory Set Topology Filter
open scoped ENNReal Pointwise

noncomputable section

namespace GSpinGGP

variable {G X : Type*} [Group G] {π : G → X}

/-- **Polynomial growth** of `X` (BP (6.7.7), after Bernstein): there are `M` and `N` such that
for every `R ≥ 1` the ball `{x ∈ X ; σ_X(x) < R}` is covered by at most `M (1 + R)^N` translates
`π(gD)`. BP takes `D = C`, the compact set defining `Ξ^{H\G}`; any compact `D` can be used. -/
def HasPolynomialGrowth (π : G → X) (σX : X → ℝ) (D : Set G) : Prop :=
  ∃ (M : ℝ) (N : ℕ), ∀ R : ℝ, 1 ≤ R → ∃ t : Finset G, (t.card : ℝ) ≤ M * (1 + R) ^ N ∧
    {x | σX x < R} ⊆ ⋃ g ∈ t, π '' ((g * ·) '' D)

/-- The real inequality behind the summation in BP's proof of 6.7.1(iii):
`(k + 1)^{-d} (k + 3)^N ≤ 3^N ((k + 1)^{d - N})⁻¹`. -/
theorem rpow_neg_mul_pow_le (k : ℕ) (N : ℕ) (d : ℝ) :
    ((k : ℝ) + 1) ^ (-d) * ((k : ℝ) + 3) ^ N ≤ 3 ^ N * (((k : ℝ) + 1) ^ (d - N))⁻¹ := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h3 : ((k : ℝ) + 3) ^ N ≤ (3 * ((k : ℝ) + 1)) ^ N :=
    pow_le_pow_left₀ (by positivity) (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]) N
  rw [mul_pow] at h3
  have e : ((k : ℝ) + 1) ^ (-d) * ((k : ℝ) + 1) ^ N = (((k : ℝ) + 1) ^ (d - N))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hk, ← Real.rpow_neg hk.le]; ring_nf
  calc ((k : ℝ) + 1) ^ (-d) * ((k : ℝ) + 3) ^ N
      ≤ ((k : ℝ) + 1) ^ (-d) * (3 ^ N * ((k : ℝ) + 1) ^ N) :=
        mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hk.le _)
    _ = 3 ^ N * (((k : ℝ) + 1) ^ (-d) * ((k : ℝ) + 1) ^ N) := by ring
    _ = _ := by rw [e]

/-- Bookkeeping: `ofReal(a) (n c) = ofReal(a n c)` for natural numbers `n`, `c`. -/
private theorem ofReal_mul_natCast_mul (a : ℝ) (n c : ℕ) :
    ENNReal.ofReal a * ((n : ℝ≥0∞) * c) = ENNReal.ofReal (a * (n * c)) := by
  rw [ENNReal.ofReal_mul' (by positivity), ← Nat.cast_mul, ← Nat.cast_mul,
    ENNReal.ofReal_natCast]

section Integrability

variable [MeasurableSpace X] {μ : Measure X} [TopologicalSpace G] [IsTopologicalGroup G]

namespace IsInvariantQuotient

variable (hπ : IsInvariantQuotient π μ)
include hπ

/-- **`∫_{xD} Ξ² ≪ 1`, uniformly over finite unions.** For `C` with nonempty interior and `D`
compact there is `n` such that, for every finite family of translates `π(gD)`, `g ∈ t`, the
function `ofReal(Ξ_C²)` is dominated on their union by a measurable `Φ` with `∫ Φ ≤ n · #t`. -/
theorem exists_lintegral_dominate {C D : Set G} (hCi : (interior C).Nonempty) (hD : IsCompact D)
    {ξ : X → ℝ} (hξ : ∀ g, ξ (π g) = relXi π μ C g) :
    ∃ n : ℕ, ∀ t : Finset G, ∃ Φ : X → ℝ≥0∞, Measurable Φ ∧ ∫⁻ x, Φ x ∂μ ≤ n * t.card ∧
      ∀ x ∈ ⋃ g ∈ t, π '' ((g * ·) '' D), ENNReal.ofReal (ξ x ^ 2) ≤ Φ x := by
  obtain ⟨n, hn, h⟩ := hπ.exists_ofReal_relXi_sq_le (C := C) hCi hD
  refine ⟨n, fun t => ?_⟩
  set T : G → Set X := fun g => toMeasurable μ (π '' ((g * ·) '' D))
  refine ⟨fun x => ∑ g ∈ t, (T g).indicator (fun _ => (n : ℝ≥0∞) * (relVol π μ D g)⁻¹) x,
    Finset.measurable_sum _ fun g _ =>
      measurable_const.indicator (measurableSet_toMeasurable _ _), ?_, ?_⟩
  · rw [lintegral_finsetSum _ fun g _ =>
      measurable_const.indicator (measurableSet_toMeasurable _ _)]
    calc ∑ g ∈ t, ∫⁻ x, (T g).indicator (fun _ => (n : ℝ≥0∞) * (relVol π μ D g)⁻¹) x ∂μ
        = ∑ g ∈ t, (n : ℝ≥0∞) * ((relVol π μ D g)⁻¹ * relVol π μ D g) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [lintegral_indicator_const (measurableSet_toMeasurable _ _), measure_toMeasurable,
            mul_assoc]
          rfl
      _ ≤ ∑ _g ∈ t, (n : ℝ≥0∞) * 1 := by
          gcongr with g; exact ENNReal.inv_mul_le_one _
      _ = n * t.card := by simp [mul_comm]
  · intro x hx
    simp only [mem_iUnion, mem_image] at hx
    obtain ⟨g, hg, _, ⟨e, he, rfl⟩, rfl⟩ := hx
    calc ENNReal.ofReal (ξ (π (g * e)) ^ 2) ≤ n * (relVol π μ D g)⁻¹ := by
          rw [hξ]; exact h g e he
      _ = (T g).indicator (fun _ => (n : ℝ≥0∞) * (relVol π μ D g)⁻¹) (π (g * e)) := by
          rw [indicator_of_mem (subset_toMeasurable μ _
            (mem_image_of_mem π (mem_image_of_mem (g * ·) he)))]
      _ ≤ _ := Finset.single_le_sum (f := fun g' =>
            (T g').indicator (fun _ => (n : ℝ≥0∞) * (relVol π μ D g')⁻¹) (π (g * e)))
            (fun _ _ => bot_le) hg

/-- **BP Prop 6.7.1(iii)** (the deduction from (6.7.7), BP p. 151): if `X` has polynomial
growth of degree `N` for `σ_X ≥ 1`, then `∫_X Ξ_C(x)² σ_X(x)^{-d} dx < ∞` for every `d > N + 1`.
Shell `{k + 1 ≤ σ_X < k + 2}` is covered by `≪ (k + 3)^N` translates `π(gD)`, on each of which
`∫ Ξ_C² ≪ 1` (`exists_lintegral_dominate`) and `σ_X^{-d} ≤ (k + 1)^{-d}`. No measurability is
needed for this bound. -/
theorem lintegral_relXi_sq_rpow_neg_lt_top {C D : Set G} (hCi : (interior C).Nonempty)
    (hD : IsCompact D) {ξ : X → ℝ} (hξ : ∀ g, ξ (π g) = relXi π μ C g) {σX : X → ℝ}
    (hσ1 : ∀ x, 1 ≤ σX x) {M : ℝ} {N : ℕ}
    (hgrowth : ∀ R : ℝ, 1 ≤ R → ∃ t : Finset G, (t.card : ℝ) ≤ M * (1 + R) ^ N ∧
      {x | σX x < R} ⊆ ⋃ g ∈ t, π '' ((g * ·) '' D))
    {d : ℝ} (hd : (N : ℝ) + 1 < d) :
    ∫⁻ x, ENNReal.ofReal (ξ x ^ 2 * σX x ^ (-d)) ∂μ < ∞ := by
  obtain ⟨n, hΦ⟩ := hπ.exists_lintegral_dominate hCi hD hξ
  choose t ht hcov using fun k : ℕ => hgrowth ((k : ℝ) + 2) (by linarith [k.cast_nonneg' (α := ℝ)])
  choose Φ hΦm hΦi hΦle using fun k => hΦ (t k)
  have hd0 : 0 ≤ d := by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
  -- pointwise domination by `∑ₖ (k + 1)^{-d} Φₖ`
  have hpt : ∀ x, ENNReal.ofReal (ξ x ^ 2 * σX x ^ (-d)) ≤
      ∑' k : ℕ, ENNReal.ofReal (((k : ℝ) + 1) ^ (-d)) * Φ k x := by
    intro x
    set k := ⌊σX x⌋₊ - 1
    have hfl : 1 ≤ ⌊σX x⌋₊ := Nat.one_le_floor_iff _ |>.2 (hσ1 x)
    have hk1 : (k : ℝ) + 1 ≤ σX x := by
      have : ((k + 1 : ℕ) : ℝ) ≤ σX x := by
        rw [show k + 1 = ⌊σX x⌋₊ by omega]; exact Nat.floor_le (by linarith [hσ1 x])
      exact_mod_cast this
    have hk2 : σX x < (k : ℝ) + 2 := by
      have := Nat.lt_floor_add_one (σX x)
      have e : ((⌊σX x⌋₊ : ℕ) : ℝ) = (k : ℝ) + 1 := by
        rw [show ⌊σX x⌋₊ = k + 1 by omega]; push_cast; ring
      linarith
    refine le_trans ?_ (ENNReal.le_tsum k)
    rw [ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_nonpos (by positivity) hk1 (neg_nonpos.2 hd0))) (hΦle k x (hcov k hk2))
  refine (lintegral_mono hpt).trans_lt ?_
  rw [lintegral_tsum fun k => ((hΦm k).const_mul _).aemeasurable]
  -- the series of bounds
  set a : ℕ → ℝ := fun k => n * max M 0 * 3 ^ N * (((k : ℝ) + 1) ^ (d - N))⁻¹
  have ha0 : ∀ k, 0 ≤ a k := fun k => by positivity
  have hsum : Summable a := by
    have : Summable fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (d - N))⁻¹ :=
      (summable_nat_add_iff 1).2 (Real.summable_nat_rpow_inv.2 (by linarith))
    simpa [a] using this.mul_left (n * max M 0 * 3 ^ N)
  calc ∑' k : ℕ, ∫⁻ x, ENNReal.ofReal (((k : ℝ) + 1) ^ (-d)) * Φ k x ∂μ
      ≤ ∑' k, ENNReal.ofReal (a k) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [lintegral_const_mul _ (hΦm k)]
        refine (mul_le_mul' le_rfl (hΦi k)).trans ?_
        rw [ofReal_mul_natCast_mul]
        refine ENNReal.ofReal_le_ofReal ?_
        have hc : ((t k).card : ℝ) ≤ max M 0 * ((k : ℝ) + 3) ^ N := by
          refine (ht k).trans ?_
          rw [show (1 : ℝ) + ((k : ℝ) + 2) = (k : ℝ) + 3 by ring]
          gcongr; exact le_max_left _ _
        have hr := rpow_neg_mul_pow_le k N d
        have hp : 0 ≤ ((k : ℝ) + 1) ^ (-d) := by positivity
        calc ((k : ℝ) + 1) ^ (-d) * (n * (t k).card)
            ≤ ((k : ℝ) + 1) ^ (-d) * (n * (max M 0 * ((k : ℝ) + 3) ^ N)) := by gcongr
          _ = n * max M 0 * (((k : ℝ) + 1) ^ (-d) * ((k : ℝ) + 3) ^ N) := by ring
          _ ≤ n * max M 0 * (3 ^ N * (((k : ℝ) + 1) ^ (d - N))⁻¹) := by gcongr
          _ = a k := by simp only [a]; ring
    _ = ENNReal.ofReal (∑' k, a k) := (ENNReal.ofReal_tsum_of_nonneg ha0 hsum).symm
    _ < ∞ := ENNReal.ofReal_lt_top

/-- **BP Prop 6.7.1(iii)**, integrable form: under polynomial growth of degree `N` and for
measurable `Ξ_C` and `σ_X ≥ 1`, `x ↦ Ξ_C(x)² σ_X(x)^{-d}` is integrable for every `d > N + 1`. -/
theorem integrable_relXi_sq_rpow_neg {C D : Set G} (hCi : (interior C).Nonempty)
    (hD : IsCompact D) {ξ : X → ℝ} (hξ : ∀ g, ξ (π g) = relXi π μ C g)
    (hξm : AEStronglyMeasurable ξ μ) {σX : X → ℝ} (hσ1 : ∀ x, 1 ≤ σX x) (hσm : Measurable σX)
    {M : ℝ} {N : ℕ}
    (hgrowth : ∀ R : ℝ, 1 ≤ R → ∃ t : Finset G, (t.card : ℝ) ≤ M * (1 + R) ^ N ∧
      {x | σX x < R} ⊆ ⋃ g ∈ t, π '' ((g * ·) '' D))
    {d : ℝ} (hd : (N : ℝ) + 1 < d) :
    Integrable (fun x => ξ x ^ 2 * σX x ^ (-d)) μ := by
  refine ⟨(hξm.pow 2).mul (hσm.pow_const _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (zero_le_one.trans (hσ1 x)) _))]
  exact hπ.lintegral_relXi_sq_rpow_neg_lt_top hCi hD hξ hσ1 hgrowth hd

/-- **BP Prop 6.7.1(iii)** from `HasPolynomialGrowth`: there is `d > 0` with
`Ξ_C² σ_X^{-d}` integrable. -/
theorem exists_integrable_of_hasPolynomialGrowth {C D : Set G} (hCi : (interior C).Nonempty)
    (hD : IsCompact D) {ξ : X → ℝ} (hξ : ∀ g, ξ (π g) = relXi π μ C g)
    (hξm : AEStronglyMeasurable ξ μ) {σX : X → ℝ} (hσ1 : ∀ x, 1 ≤ σX x) (hσm : Measurable σX)
    (hgrowth : HasPolynomialGrowth π σX D) :
    ∃ d : ℝ, 0 < d ∧ Integrable (fun x => ξ x ^ 2 * σX x ^ (-d)) μ := by
  obtain ⟨M, N, hg⟩ := hgrowth
  exact ⟨N + 2, by positivity,
    hπ.integrable_relXi_sq_rpow_neg hCi hD hξ hξm hσ1 hσm hg (by linarith)⟩

/-- **BP Prop 6.7.1(iv)** ("by similar arguments, this also follows from 6.7.7"): under
polynomial growth of degree `N`, for every `d ≥ 0` there is `A` with
`∫_{σ_X ≤ c} Ξ_C(x)² σ_X(x)^d dx ≤ A c^{N + d}` for all `c ≥ 1`. -/
theorem lintegral_indicator_relXi_sq_rpow_le {C D : Set G} (hCi : (interior C).Nonempty)
    (hD : IsCompact D) {ξ : X → ℝ} (hξ : ∀ g, ξ (π g) = relXi π μ C g) {σX : X → ℝ}
    (hσ1 : ∀ x, 1 ≤ σX x) {M : ℝ} {N : ℕ}
    (hgrowth : ∀ R : ℝ, 1 ≤ R → ∃ t : Finset G, (t.card : ℝ) ≤ M * (1 + R) ^ N ∧
      {x | σX x < R} ⊆ ⋃ g ∈ t, π '' ((g * ·) '' D))
    {d : ℝ} (hd : 0 ≤ d) :
    ∃ A : ℝ, ∀ c : ℝ, 1 ≤ c →
      ∫⁻ x, ENNReal.ofReal ({x | σX x ≤ c}.indicator (fun x => ξ x ^ 2 * σX x ^ d) x) ∂μ ≤
        ENNReal.ofReal (A * c ^ ((N : ℝ) + d)) := by
  obtain ⟨n, hΦ⟩ := hπ.exists_lintegral_dominate hCi hD hξ
  refine ⟨n * max M 0 * 3 ^ N, fun c hc => ?_⟩
  obtain ⟨t, ht, hcov⟩ := hgrowth (c + 1) (by linarith)
  obtain ⟨Φ, hΦm, hΦi, hΦle⟩ := hΦ t
  have hc0 : 0 ≤ c := by linarith
  have hpt : ∀ x, ENNReal.ofReal ({x | σX x ≤ c}.indicator (fun x => ξ x ^ 2 * σX x ^ d) x) ≤
      ENNReal.ofReal (c ^ d) * Φ x := by
    intro x
    by_cases hx : σX x ≤ c
    · rw [indicator_of_mem (show x ∈ {x | σX x ≤ c} from hx),
        ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (zero_le_one.trans (hσ1 x)) hx hd))
        (hΦle x (hcov (show σX x < c + 1 by linarith)))
    · rw [indicator_of_notMem (show x ∉ {x | σX x ≤ c} from hx)]; simp
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_const_mul _ hΦm]
  refine (mul_le_mul' le_rfl hΦi).trans ?_
  rw [ofReal_mul_natCast_mul]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcard : (t.card : ℝ) ≤ max M 0 * (3 ^ N * c ^ N) := by
    refine ht.trans ?_
    calc M * (1 + (c + 1)) ^ N ≤ max M 0 * (3 * c) ^ N := by
          gcongr
          · exact le_max_left _ _
          · linarith
      _ = max M 0 * (3 ^ N * c ^ N) := by rw [mul_pow]
  have hcd : c ^ d * c ^ N = c ^ ((N : ℝ) + d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith), add_comm]
  calc c ^ d * (n * t.card) ≤ c ^ d * (n * (max M 0 * (3 ^ N * c ^ N))) := by gcongr
    _ = n * max M 0 * 3 ^ N * (c ^ d * c ^ N) := by ring
    _ = _ := by rw [hcd]

end IsInvariantQuotient

end Integrability

/-! ### Weak Cartan data -/

variable [TopologicalSpace G]

/-- **The input of BP's proof of (6.7.7)** (BP pp. 151–152), for a log-norm `τ` on `G` and
`σ_X = π_* τ = fiberInf τ π`:
* `exists_eq_mul`: every `x ∈ X` is `π(s k)` with `s ∈ S`, `k ∈ K` (BP (6.7.11), the weak Cartan
  decomposition `G = H A₀⁺ A K` of Lemma 6.6.2(ii), with `S = A₀⁺A`);
* `le_fiberInf`: `τ(s) ≤ c σ_X(π s)` on `S` (the nontrivial half of BP Prop 6.7.1(ii)(b),
  `σ_{H\G}(a a₀) ∼ σ_G(a a₀)`);
* `growth`: the image in `X` of `{s ∈ S ; τ(s) < R}` is covered by `≤ M (1 + R)^N` translates
  `π(j C_S)` (BP (6.7.12), polynomial growth of `A_min = A₀A` with `C_S = C_min`).

For `X = H\G/A_G` the log-norm `τ` must be invariant modulo `A_G` (e.g. `σ_{A_G\G}`): `σ_X` is
`A_G`-invariant, so the comparison of `le_fiberInf` can only hold modulo `A_G`. -/
structure WeakCartanData (π : G → X) (τ : G → ℝ) where
  /-- the "cone" (BP: `A₀⁺ A`) -/
  S : Set G
  /-- the compact set of (6.7.11) -/
  K : Set G
  isCompact_K : IsCompact K
  exists_eq_mul : ∀ g, ∃ s ∈ S, ∃ k ∈ K, π g = π (s * k)
  /-- the constant in `τ ≪ σ_X` on `S` -/
  c : ℝ
  le_fiberInf : ∀ s ∈ S, τ s ≤ c * fiberInf τ π (π s)
  /-- the compact set of (6.7.12) (BP: `C_min`) -/
  CS : Set G
  isCompact_CS : IsCompact CS
  /-- the constants of (6.7.12) -/
  M : ℝ
  N : ℕ
  growth : ∀ R : ℝ, 1 ≤ R → ∃ t : Finset G, (t.card : ℝ) ≤ M * (1 + R) ^ N ∧
    π '' {s ∈ S | τ s < R} ⊆ ⋃ j ∈ t, π '' ((j * ·) '' CS)

namespace WeakCartanData

variable {τ : G → ℝ} (W : WeakCartanData π τ)

/-- The covering set `C_S K` of `WeakCartanData.hasPolynomialGrowth` is compact. -/
theorem isCompact_CS_mul_K [IsTopologicalGroup G] : IsCompact (W.CS * W.K) :=
  W.isCompact_CS.mul W.isCompact_K

/-- **BP (6.7.7) from (6.7.11), Prop 6.7.1(ii)(b) and (6.7.12)** (BP p. 152, "easy to see"):
`X` has polynomial growth for `σ_X = π_* τ`, with covering set `C_S K`. If `σ_X(x) < R` and
`x = π(s k)`, then `σ_X(π s) < R + C_K` (Prop 6.7.1(i)(b)), so `τ(s) < c(R + C_K) + 1`, and `s`
lies in one of the translates of (6.7.12). -/
theorem hasPolynomialGrowth (hτ : IsLogNorm τ) (hsurj : Function.Surjective π)
    (hdesc : ∀ g g' h : G, π g = π g' → π (g * h) = π (g' * h)) :
    HasPolynomialGrowth π (fiberInf τ π) (W.CS * W.K) := by
  obtain ⟨CK, hCK0, hCK⟩ := hτ.exists_fiberInf_mul_le_add π
    (fun h g g' hg => hdesc g g' h hg) W.isCompact_K
  have hM : 0 ≤ W.M := by
    obtain ⟨t, ht, -⟩ := W.growth 1 le_rfl
    have : (0 : ℝ) < (1 + 1) ^ W.N := by positivity
    nlinarith [(Nat.cast_nonneg t.card : (0 : ℝ) ≤ t.card)]
  set A : ℝ := 2 + |W.c| * (1 + CK)
  refine ⟨W.M * A ^ W.N, W.N, fun R hR => ?_⟩
  set R' : ℝ := |W.c| * (R + CK) + 1
  obtain ⟨t, ht, hcov⟩ := W.growth R' (by have := abs_nonneg W.c; nlinarith)
  refine ⟨t, ?_, ?_⟩
  · refine ht.trans ?_
    have h1 : 1 + R' ≤ A * (1 + R) := by
      have := abs_nonneg W.c
      have h2 : 0 ≤ |W.c| * CK * R := by positivity
      simp only [R', A]; nlinarith
    calc W.M * (1 + R') ^ W.N ≤ W.M * (A * (1 + R)) ^ W.N := by
          gcongr
      _ = W.M * A ^ W.N * (1 + R) ^ W.N := by rw [mul_pow]; ring
  · intro x hx
    simp only [mem_ofPred_eq] at hx
    obtain ⟨g, rfl⟩ := hsurj x
    obtain ⟨s, hs, k, hk, hg⟩ := W.exists_eq_mul g
    have hσs : fiberInf τ π (π s) ≤ fiberInf τ π (π g) + CK := by
      rw [hg]; exact (hCK s k hk).2
    have hτs : τ s < R' := by
      have h0 : 0 ≤ fiberInf τ π (π s) := zero_le_one.trans (hτ.one_le_fiberInf π s)
      calc τ s ≤ W.c * fiberInf τ π (π s) := W.le_fiberInf s hs
        _ ≤ |W.c| * fiberInf τ π (π s) := mul_le_mul_of_nonneg_right (le_abs_self _) h0
        _ ≤ |W.c| * (R + CK) := by
            gcongr; linarith
        _ < R' := lt_add_one _
    have hmem := hcov ⟨s, ⟨hs, hτs⟩, rfl⟩
    simp only [mem_iUnion, mem_image] at hmem
    obtain ⟨j, hj, _, ⟨e, he, rfl⟩, hje⟩ := hmem
    refine mem_iUnion₂.2 ⟨j, hj, j * (e * k), ⟨e * k, mul_mem_mul he hk, rfl⟩, ?_⟩
    rw [hg, ← mul_assoc]
    exact hdesc _ _ k hje

end WeakCartanData

/-- **BP Prop 6.7.1(iii) from weak Cartan data** (BP pp. 151–152): for an invariant quotient
`π : G → X` that is a quotient map, an outer regular `μ` (used only for the measurability of `Ξ`),
a log-norm `τ` on `G` with `σ_X = π_* τ` measurable, and `WeakCartanData π τ`, there is `d > 0`
with `∫_X Ξ_C(x)² σ_X(x)^{-d} dx < ∞`, for every compact `C` with nonempty interior. -/
theorem IsInvariantQuotient.exists_integrable_of_weakCartanData [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] [IsTopologicalGroup G] {μ : Measure X}
    [μ.OuterRegular] (hπ : IsInvariantQuotient π μ) (hq : IsQuotientMap π) {τ : G → ℝ}
    (hτ : IsLogNorm τ) (hσm : Measurable (fiberInf τ π)) (W : WeakCartanData π τ) {C : Set G}
    (hC : IsCompact C) (hCi : (interior C).Nonempty) {ξ : X → ℝ}
    (hξ : ∀ g, ξ (π g) = relXi π μ C g) :
    ∃ d : ℝ, 0 < d ∧ Integrable (fun x => ξ x ^ 2 * fiberInf τ π x ^ (-d)) μ :=
  hπ.exists_integrable_of_hasPolynomialGrowth hCi W.isCompact_CS_mul_K hξ
    (hπ.measurable_of_relXi hq hC hξ).aestronglyMeasurable
    (hτ.one_le_fiberInf_of_surjective π hq.surjective) hσm
    (W.hasPolynomialGrowth hτ hq.surjective hπ.descends)

end GSpinGGP
