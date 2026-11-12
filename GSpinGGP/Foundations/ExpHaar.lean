/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.ExpLocal

/-!
# `exp` carries an additive Haar measure to a Haar measure near `0` (`p`-adic case)

Over a `p`-adic field the Jacobian of `exp` is `1` near `0`. This file proves the measure-theoretic
form needed for the measures `dX` of `J^Lie` and `m^Lie_geom` (BP §1.6), without a change of
variables formula: `exp` is an isometry near `0`, so it carries cosets of small lattices to cosets of
small open subgroups.

* `exists_norm_exp_sub_exp_eq`: in an ultrametric Banach algebra with `‖1/n!‖ ≤ Rⁿ`,
  `‖e^x − e^y‖ = ‖x − y‖` on a small ball;
* `exists_expA_isometry`: the same for `expA` on a finite-dimensional algebra `A` (norm
  `‖lmulPi ·‖`), with `exp` onto the ball around `1`;
* `isEmbedding_units_val`: `Aˣ → A` is a topological embedding;
* `Measure.eq_of_forall_vadd_coset`: two finite measures carried by a compact open subgroup and
  uniform on the cosets of a basis of open subgroups are equal;
* `exists_isAddHaarMeasure_eq_expA_image`: for a group `𝓗 ⊆ Aˣ` whose Lie algebra near `0` is
  `𝔤 ⊕ F·1`, and every Haar measure on `𝓗/(scalars)`, some additive Haar measure `μ` on `𝔤` has
  `μ(S) = μK(e^S)` for `S` near `0`.
-/

noncomputable section

open MeasureTheory Topology Filter Pointwise

set_option linter.style.haveILetI false

namespace GSpinGGP

section Ultra

/-- The operator norm into an ultrametric space is ultrametric. -/
instance ContinuousLinearMap.isUltrametricDist {𝕜 E G : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    [IsUltrametricDist G] : IsUltrametricDist (E →L[𝕜] G) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun f g => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (le_max_of_le_left (norm_nonneg _)) fun x => ?_
  rw [add_apply, max_mul_of_nonneg _ _ (norm_nonneg x)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le_max (f.le_opNorm x) (g.le_opNorm x))

variable {E : Type*} [NormedRing E] [IsUltrametricDist E]

theorem norm_pow_succ_sub_pow_succ_le {x y : E} {r : ℝ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (n : ℕ) :
    ‖x ^ (n + 1) - y ^ (n + 1)‖ ≤ r ^ n * ‖x - y‖ := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hx
  induction n with
  | zero => simp
  | succ n ih =>
    have e : x ^ (n + 1 + 1) - y ^ (n + 1 + 1) =
        x * (x ^ (n + 1) - y ^ (n + 1)) + (x - y) * y ^ (n + 1) := by
      rw [pow_succ' x (n + 1), pow_succ' y (n + 1)]; noncomm_ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · calc ‖x * (x ^ (n + 1) - y ^ (n + 1))‖ ≤ ‖x‖ * ‖x ^ (n + 1) - y ^ (n + 1)‖ :=
            norm_mul_le _ _
        _ ≤ r * (r ^ n * ‖x - y‖) := by gcongr
        _ = r ^ (n + 1) * ‖x - y‖ := by ring
    · calc ‖(x - y) * y ^ (n + 1)‖ ≤ ‖x - y‖ * ‖y ^ (n + 1)‖ := norm_mul_le _ _
        _ ≤ ‖x - y‖ * r ^ (n + 1) := by
            gcongr
            exact (norm_pow_le' y n.succ_pos).trans (pow_le_pow_left₀ (norm_nonneg _) hy _)
        _ = r ^ (n + 1) * ‖x - y‖ := by ring

variable {𝕂 : Type*} [NontriviallyNormedField 𝕂] [CharZero 𝕂] [NormedAlgebra 𝕂 E] [CompleteSpace E]

open NormedSpace in
/-- **`exp` is an isometry near `0`** in an ultrametric Banach algebra over a field where
`‖1/n!‖ ≤ Rⁿ`: on a small closed ball, `‖e^x − e^y‖ = ‖x − y‖`. (The terms of degree `≥ 2` of
`e^x − e^y` have norm `≤ ‖x − y‖ / 2`.) -/
theorem exists_norm_exp_sub_exp_eq {R : ℝ} (hR : ∀ n : ℕ, ‖((n.factorial : 𝕂))⁻¹‖ ≤ R ^ n)
    (hrad : 0 < (expSeries 𝕂 E).radius) :
    ∃ r : ℝ, 0 < r ∧ (∀ x : E, ‖x‖ ≤ r → x ∈ Metric.eball (0 : E) (expSeries 𝕂 E).radius) ∧
      ∀ x y : E, ‖x‖ ≤ r → ‖y‖ ≤ r → ‖exp x - exp y‖ = ‖x - y‖ := by
  obtain ⟨r₂, hr₂0, hr₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hrad
  set R' := max R 1 with hR'
  have hR'1 : 1 ≤ R' := le_max_right _ _
  have hR'0 : 0 < R' := lt_of_lt_of_le one_pos hR'1
  set r := min (1 / (2 * R' ^ 2)) (r₂ : ℝ) with hrdef
  have hr0 : 0 < r := lt_min (by positivity) (by exact_mod_cast hr₂0)
  have hball : ∀ x : E, ‖x‖ ≤ r → x ∈ Metric.eball (0 : E) (expSeries 𝕂 E).radius := by
    intro x hx
    rw [Metric.mem_eball, edist_zero_right]
    refine lt_of_le_of_lt ?_ hr₂
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hx.trans (min_le_right _ _))
  refine ⟨r, hr0, hball, fun x y hx hy => ?_⟩
  by_cases hxy : x = y
  · simp [hxy]
  have hxy' : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hsx := expSeries_hasSum_exp_of_mem_ball' (𝕂 := 𝕂) x (hball x hx)
  have hsy := expSeries_hasSum_exp_of_mem_ball' (𝕂 := 𝕂) y (hball y hy)
  have hs := (hsx.sub hsy).sub (hasSum_ite_eq 1 (x - y))
  set b : ℕ → E := fun n => (((n.factorial : 𝕂))⁻¹ • x ^ n - ((n.factorial : 𝕂))⁻¹ • y ^ n) -
    if n = 1 then x - y else 0 with hb
  have hbn : ∀ n, ‖b n‖ ≤ ‖x - y‖ / 2 := by
    intro n
    match n with
    | 0 => simp [hb]; positivity
    | 1 => simp [hb]; positivity
    | m + 2 =>
      have hne : m + 2 ≠ 1 := by omega
      simp only [hb, ite_eq_right hne, sub_zero, ← smul_sub]
      have hRm : R' * r ≤ 1 := by
        calc R' * r ≤ R' * (1 / (2 * R' ^ 2)) := by gcongr; exact min_le_left _ _
          _ = 1 / (2 * R') := by field_simp
          _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      calc ‖((((m + 2).factorial : 𝕂))⁻¹ • (x ^ (m + 2) - y ^ (m + 2)))‖
          ≤ ‖(((m + 2).factorial : 𝕂))⁻¹‖ * ‖x ^ (m + 1 + 1) - y ^ (m + 1 + 1)‖ :=
            norm_smul_le _ _
        _ ≤ R' ^ (m + 2) * (r ^ (m + 1) * ‖x - y‖) := by
            gcongr
            · exact (hR _).trans (pow_le_pow_left₀ (by simpa using (norm_nonneg _).trans (hR 1)) (le_max_left _ _) _)
            · exact norm_pow_succ_sub_pow_succ_le hx hy (m + 1)
        _ = (R' ^ 2 * r) * (R' * r) ^ m * ‖x - y‖ := by ring
        _ ≤ (1 / 2) * 1 * ‖x - y‖ := by
            gcongr
            · calc R' ^ 2 * r ≤ R' ^ 2 * (1 / (2 * R' ^ 2)) := by gcongr; exact min_le_left _ _
                _ = 1 / 2 := by field_simp
            · exact pow_le_one₀ (by positivity) hRm
        _ = ‖x - y‖ / 2 := by ring
  have hD : ‖(exp x - exp y) - (x - y)‖ ≤ ‖x - y‖ / 2 := by
    rw [← hs.tsum_eq]
    exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) hbn
  have hlt : ‖(exp x - exp y) - (x - y)‖ < ‖x - y‖ := by linarith
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
  rw [sub_add_cancel, max_eq_right hlt.le] at this
  exact this

end Ultra

section ALevel

/-! ## The norm `‖a‖ = ‖lmulPi a‖` on a finite-dimensional algebra

`expA` is computed in the Banach algebra `End(F^d)` through left multiplication `lmulPi`; the
operator norm pulled back along `lmulPi` is ultrametric and submultiplicative, and `exp` is an
isometry for it near `0`. -/

variable (F : Type*) [NontriviallyNormedField F] [PAdicField F] {A : Type*} [Ring A] [Algebra F A]
  [Module.Finite F A] [TopologicalSpace A] [IsModuleTopology F A]

local notation "VA" => (Fin (Module.finrank F A) → F)

lemma lmulPi_add (a b : A) : lmulPi F (a + b) = lmulPi F a + lmulPi F b := map_add (lmulPiₗ F) a b

lemma lmulPi_sub (a b : A) : lmulPi F (a - b) = lmulPi F a - lmulPi F b := map_sub (lmulPiₗ F) a b

lemma lmulPi_neg (a : A) : lmulPi F (-a) = -lmulPi F a := map_neg (lmulPiₗ F) a

lemma lmulPi_zero : lmulPi F (0 : A) = 0 := map_zero (lmulPiₗ F)

lemma lmulPi_injective : Function.Injective (lmulPi F : A → VA →L[F] VA) :=
  Function.LeftInverse.injective (lmulPiInv_lmulPi F)

lemma norm_lmulPi_add_le (a b : A) :
    ‖lmulPi F (a + b)‖ ≤ max ‖lmulPi F a‖ ‖lmulPi F b‖ := by
  rw [lmulPi_add]; exact IsUltrametricDist.norm_add_le_max _ _

lemma norm_lmulPi_mul_le (a b : A) : ‖lmulPi F (a * b)‖ ≤ ‖lmulPi F a‖ * ‖lmulPi F b‖ := by
  rw [lmulPi_mul]; exact norm_mul_le _ _

lemma norm_lmulPi_one_le : ‖lmulPi F (1 : A)‖ ≤ 1 := by
  rw [lmulPi_one]; exact ContinuousLinearMap.norm_id_le

lemma norm_lmulPi_neg (a : A) : ‖lmulPi F (-a)‖ = ‖lmulPi F a‖ := by
  rw [lmulPi_neg, norm_neg]

lemma norm_lmulPi_sub_comm (a b : A) : ‖lmulPi F (a - b)‖ = ‖lmulPi F (b - a)‖ := by
  rw [← neg_sub, norm_lmulPi_neg]

/-- The balls `‖a‖ ≤ s` are neighbourhoods of `0`. -/
lemma lmulPi_ball_mem_nhds {s : ℝ} (hs : 0 < s) : {a : A | ‖lmulPi F a‖ ≤ s} ∈ 𝓝 (0 : A) := by
  have := (continuous_lmulPi F).continuousAt (x := (0 : A))
  rw [ContinuousAt, lmulPi_zero] at this
  have h2 := this (Metric.closedBall_mem_nhds (0 : VA →L[F] VA) hs)
  rw [Filter.mem_map] at h2
  exact Filter.mem_of_superset h2 fun a ha => by simpa using ha

/-- The balls `‖a‖ ≤ s` form a basis of neighbourhoods of `0`. -/
lemma exists_lmulPi_ball_subset {U : Set A} (hU : U ∈ 𝓝 (0 : A)) :
    ∃ s : ℝ, 0 < s ∧ ∀ a : A, ‖lmulPi F a‖ ≤ s → a ∈ U := by
  have h := (lmulPiInv F).continuous.continuousAt (x := (0 : VA →L[F] VA))
  rw [ContinuousAt, map_zero] at h
  obtain ⟨s, hs, hsU⟩ := Metric.mem_nhds_iff.mp (h hU)
  refine ⟨s / 2, half_pos hs, fun a ha => ?_⟩
  have : lmulPi F a ∈ Metric.ball (0 : VA →L[F] VA) s := by
    rw [mem_ball_zero_iff]; linarith
  simpa [lmulPiInv_lmulPi] using hsU this

/-- A unit `u` with `‖u − 1‖ < 1` has `‖u⁻¹ − 1‖ ≤ ‖u − 1‖`. -/
lemma norm_lmulPi_inv_sub_one_le (u : Aˣ) (hu : ‖lmulPi F ((u : A) - 1)‖ < 1) :
    ‖lmulPi F (((u⁻¹ : Aˣ) : A) - 1)‖ ≤ ‖lmulPi F ((u : A) - 1)‖ := by
  set s := ‖lmulPi F ((u : A) - 1)‖
  have e : ((u⁻¹ : Aˣ) : A) - 1 = -(((u⁻¹ : Aˣ) : A) * ((u : A) - 1)) := by
    rw [mul_sub, Units.inv_mul, mul_one]; abel
  have hinv : ‖lmulPi F ((u⁻¹ : Aˣ) : A)‖ ≤ 1 := by
    have e2 : ((u⁻¹ : Aˣ) : A) = 1 + -(((u⁻¹ : Aˣ) : A) * ((u : A) - 1)) := by
      rw [← e]; abel
    by_contra hc
    replace hc := lt_of_not_ge hc
    have h1 := norm_lmulPi_add_le F 1 (-(((u⁻¹ : Aˣ) : A) * ((u : A) - 1)))
    rw [← e2, norm_lmulPi_neg] at h1
    have h2 := norm_lmulPi_mul_le F ((u⁻¹ : Aˣ) : A) ((u : A) - 1)
    have h3 : ‖lmulPi F ((u⁻¹ : Aˣ) : A)‖ * s < ‖lmulPi F ((u⁻¹ : Aˣ) : A)‖ := by
      have := (norm_nonneg (lmulPi F ((u : A) - 1)))
      nlinarith
    rcases le_max_iff.mp h1 with h | h
    · linarith [norm_lmulPi_one_le F (A := A)]
    · linarith
  rw [e, norm_lmulPi_neg]
  calc _ ≤ ‖lmulPi F ((u⁻¹ : Aˣ) : A)‖ * s := norm_lmulPi_mul_le F _ _
    _ ≤ 1 * s := by gcongr
    _ = s := one_mul s

/-- **`exp` is an isometry near `0`, onto the ball around `1`** (for the norm `‖lmulPi ·‖`):
there are arbitrarily small `r ∈ (0, 1)` such that `‖e^X − e^Y‖ = ‖X − Y‖` for `‖X‖, ‖Y‖ ≤ r`, and
every `u` with `‖u − 1‖ ≤ r` is `e^W` with `‖W‖ ≤ r`. -/
theorem exists_expA_isometry {U : Set A} (hU : U ∈ 𝓝 (0 : A)) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ (∀ X : A, ‖lmulPi F X‖ ≤ r → X ∈ U) ∧
      (∀ X Y : A, ‖lmulPi F X‖ ≤ r → ‖lmulPi F Y‖ ≤ r →
        ‖lmulPi F (expA F X - expA F Y)‖ = ‖lmulPi F (X - Y)‖) ∧
      ∀ u : A, ‖lmulPi F (u - 1)‖ ≤ r → ∃ W : A, ‖lmulPi F W‖ ≤ r ∧ expA F W = u := by
  letI := isTopologicalRing_of_moduleTopology F A
  obtain ⟨R, -, hR⟩ := exists_norm_factorial_inv_le F
  obtain ⟨r₀, hr₀, -, hiso⟩ := exists_norm_exp_sub_exp_eq (𝕂 := F) (E := VA →L[F] VA) hR
    (expSeries_radius_pos_of_pAdic F _)
  obtain ⟨U₀, hU₀, -, hexp⟩ := expA_aux F (A := A)
  obtain ⟨log, hlc, hl1, hlog⟩ := exists_logA F (A := A)
  obtain ⟨s₁, hs₁, hs₁U⟩ := exists_lmulPi_ball_subset F (inter_mem hU hU₀)
  set r₁ := min (min r₀ s₁) (1 / 2) with hr₁
  have hr₁0 : 0 < r₁ := lt_min (lt_min hr₀ hs₁) (by norm_num)
  have hr₁r₀ : r₁ ≤ r₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hr₁s₁ : r₁ ≤ s₁ := (min_le_left _ _).trans (min_le_right _ _)
  -- the isometry on the `r₁`-ball
  have hiso' : ∀ X Y : A, ‖lmulPi F X‖ ≤ r₁ → ‖lmulPi F Y‖ ≤ r₁ →
      ‖lmulPi F (expA F X - expA F Y)‖ = ‖lmulPi F (X - Y)‖ := by
    intro X Y hX hY
    have hXU := (hs₁U X (hX.trans hr₁s₁)).2
    have hYU := (hs₁U Y (hY.trans hr₁s₁)).2
    rw [lmulPi_sub, lmulPi_sub, (hexp X hXU).2.2, (hexp Y hYU).2.2]
    exact hiso _ _ (hX.trans hr₁r₀) (hY.trans hr₁r₀)
  -- the logarithm on a ball around `1`
  have hev : ∀ᶠ u in 𝓝 (1 : A), expA F (log u) = u ∧ ‖lmulPi F (log u)‖ ≤ r₁ :=
    hlog.and (hlc.preimage_mem_nhds (t := {a : A | ‖lmulPi F a‖ ≤ r₁})
      (by rw [hl1]; exact lmulPi_ball_mem_nhds F hr₁0))
  have hev0 : (fun a : A => a + 1) ⁻¹' {u | expA F (log u) = u ∧ ‖lmulPi F (log u)‖ ≤ r₁} ∈
      𝓝 (0 : A) :=
    (continuous_id.add continuous_const : Continuous fun a : A => a + 1).continuousAt.preimage_mem_nhds
      (by show _ ∈ 𝓝 ((0 : A) + 1); rw [zero_add]; exact hev)
  obtain ⟨s₂, hs₂, hs₂U⟩ := exists_lmulPi_ball_subset F hev0
  refine ⟨min r₁ s₂, lt_min hr₁0 hs₂, ?_, fun X hX => (hs₁U X ?_).1, fun X Y hX hY =>
    hiso' X Y (hX.trans (min_le_left _ _)) (hY.trans (min_le_left _ _)), fun u hu => ?_⟩
  · exact (min_le_left _ _).trans_lt ((min_le_right _ _).trans_lt (by norm_num))
  · exact hX.trans ((min_le_left _ _).trans hr₁s₁)
  · obtain ⟨he, hn⟩ := hs₂U (u - 1) (hu.trans (min_le_right _ _))
    simp only [sub_add_cancel] at he hn
    refine ⟨log u, ?_, he⟩
    have := hiso' (log u) 0 hn (by simpa [lmulPi_zero] using hr₁0.le)
    rw [he, expA_zero_eq_one, sub_zero] at this
    rw [← this]; exact hu

/-- `lmulPi` of a unit, as a unit of `End(F^d)`. -/
def lmulPiUnit (u : Aˣ) : (VA →L[F] VA)ˣ :=
  ⟨lmulPi F u, lmulPi F ↑u⁻¹, by rw [← lmulPi_mul, Units.mul_inv, lmulPi_one],
    by rw [← lmulPi_mul, Units.inv_mul, lmulPi_one]⟩

include F in
/-- **`Aˣ → A` is a topological embedding**: inversion is continuous on the units of `A` (it is
`Ring.inverse` of `End(F^d)`, transported along `lmulPi`). -/
theorem isEmbedding_units_val : Topology.IsEmbedding (Units.val : Aˣ → A) := by
  refine Units.isEmbedding_val_mk' (f := fun a => lmulPiInv F (Ring.inverse (lmulPi F a)))
    ?_ fun u => ?_
  · rintro _ ⟨u, rfl⟩
    have h1 : ContinuousAt (fun a : A => Ring.inverse (lmulPi F a)) (u : A) :=
      ContinuousAt.comp (f := lmulPi F) (x := (u : A)) (g := Ring.inverse)
        (NormedRing.inverse_continuousAt (lmulPiUnit F u)) (continuous_lmulPi F).continuousAt
    exact ((lmulPiInv F).continuous.continuousAt.comp h1).continuousWithinAt
  · change lmulPiInv F (Ring.inverse ((lmulPiUnit F u : (VA →L[F] VA)ˣ) : VA →L[F] VA)) = _
    rw [Ring.inverse_unit]
    exact lmulPiInv_lmulPi F _

end ALevel


section CosetMeasure

/-! ## Measures that are uniform on the cosets of a basis of open subgroups -/

variable {V : Type*} [AddCommGroup V]

lemma mem_vadd_coset_iff {L : AddSubgroup V} {x w : V} :
    w ∈ x +ᵥ (L : Set V) ↔ -x + w ∈ L := by
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, SetLike.mem_coe]

lemma vadd_coset_eq_of_mem {L : AddSubgroup V} {x z : V} (hz : z ∈ x +ᵥ (L : Set V)) :
    x +ᵥ (L : Set V) = z +ᵥ (L : Set V) := by
  rw [mem_vadd_coset_iff] at hz
  ext w
  rw [mem_vadd_coset_iff, mem_vadd_coset_iff]
  constructor
  · intro hw
    have := L.sub_mem hw hz
    rwa [show -x + w - (-x + z) = -z + w by abel] at this
  · intro hw
    have := L.add_mem hz hw
    rwa [show -x + z + (-z + w) = -x + w by abel] at this

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
      rw [mem_vadd_coset_iff]
      have := QuotientAddGroup.eq.mp
        (Quotient.out_eq (QuotientAddGroup.mk (s := L.addSubgroupOf L₀) ⟨x, hx⟩))
      exact AddSubgroup.mem_addSubgroupOf.mp this
    · rintro ⟨q, hq⟩
      rw [mem_vadd_coset_iff] at hq
      have h1 := L₀.add_mem (Quotient.out q).2 (hL hq)
      rwa [add_neg_cancel_left] at h1
  have hdisj : Pairwise (Function.onFun Disjoint fun q => o q +ᵥ (L : Set V)) := by
    intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    intro w hw hw'
    rw [mem_vadd_coset_iff] at hw hw'
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
theorem Measure.eq_of_forall_vadd_coset (L : ℕ → AddSubgroup V) (hanti : Antitone L)
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
        rw [mem_vadd_coset_iff] at hw
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
      · rw [mem_vadd_coset_iff, neg_add_cancel]; exact (L n).zero_mem
      · intro w hw
        rw [mem_vadd_coset_iff] at hw
        have := hn hw
        simpa using this
  have hpi : IsPiSystem C := by
    rintro _ ⟨n, x, rfl⟩ _ ⟨m, y, rfl⟩ ⟨z, hzx, hzy⟩
    refine ⟨max n m, z, ?_⟩
    rw [vadd_coset_eq_of_mem hzx, vadd_coset_eq_of_mem hzy]
    ext w
    simp only [Set.mem_inter_iff, mem_vadd_coset_iff]
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

section ExpChart

/-! ## The exponential chart of a group modulo central scalars -/

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F] {A : Type*} [Ring A]
  [Algebra F A] [Module.Finite F A] [TopologicalSpace A] [IsModuleTopology F A]

local notation "VA" => (Fin (Module.finrank F A) → F)

variable (F) in
/-- `e^{t·1} = (e^t)·1` for `t ∈ F` near `0`. -/
lemma eventually_expA_algebraMap :
    ∀ᶠ t in 𝓝 (0 : F), expA F (algebraMap F A t) = algebraMap F A (expA F t) := by
  filter_upwards [eventually_map_expA (F := F) (A := F) (Algebra.linearMap F A)
    (fun X n => map_pow (algebraMap F A) X n)] with t ht
  exact ht.symm

variable (F) in
/-- The closed balls `‖a‖ ≤ s` of `A` are compact. -/
lemma isCompact_lmulPi_ball (s : ℝ) : IsCompact {a : A | ‖lmulPi F a‖ ≤ s} := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace (VA →L[F] VA) := FiniteDimensional.proper F _
  have hcl : IsClosed (LinearMap.range (lmulPiₗ F (A := A)) : Set (VA →L[F] VA)) :=
    Submodule.closed_of_finiteDimensional _
  have hK := ((isCompact_closedBall (0 : VA →L[F] VA) s).inter_right hcl).image
    (lmulPiInv F).continuous
  convert hK using 1
  ext a
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_inter_iff, Metric.mem_closedBall,
    dist_zero_right, SetLike.mem_coe, LinearMap.mem_range]
  constructor
  · intro ha
    exact ⟨lmulPi F a, ⟨ha, a, rfl⟩, lmulPiInv_lmulPi F a⟩
  · rintro ⟨b, ⟨hb, a', rfl⟩, rfl⟩
    rw [show (lmulPiₗ F a' : VA →L[F] VA) = lmulPi F a' from rfl, lmulPiInv_lmulPi]
    exact hb

lemma norm_lmulPi_le_one_of {a : A} (h : ‖lmulPi F (a - 1)‖ ≤ 1) : ‖lmulPi F a‖ ≤ 1 := by
  have := norm_lmulPi_add_le F (a - 1) 1
  rw [sub_add_cancel] at this
  exact this.trans (max_le h (norm_lmulPi_one_le F))

variable {𝓗 : Type*} [Group 𝓗]

variable (F) in
/-- The elements `h` with `‖j h − 1‖ ≤ s`, a subgroup for `0 ≤ s < 1`. -/
def unitBall (j : 𝓗 →* Aˣ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) : Subgroup 𝓗 where
  carrier := {h | ‖lmulPi F (((j h : Aˣ) : A) - 1)‖ ≤ s}
  one_mem' := by simpa [lmulPi_zero] using hs0
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_mul, Units.val_mul] at ha hb ⊢
    have e : ((j a : Aˣ) : A) * (j b : A) - 1 =
        (((j a : Aˣ) : A) - 1) * (j b : A) + (((j b : Aˣ) : A) - 1) := by noncomm_ring
    rw [e]
    refine (norm_lmulPi_add_le F _ _).trans (max_le ?_ hb)
    calc _ ≤ ‖lmulPi F (((j a : Aˣ) : A) - 1)‖ * ‖lmulPi F ((j b : Aˣ) : A)‖ :=
          norm_lmulPi_mul_le F _ _
      _ ≤ s * 1 := by
          gcongr
          exact norm_lmulPi_le_one_of (hb.trans hs1.le)
      _ = s := mul_one s
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, map_inv] at ha ⊢
    exact (norm_lmulPi_inv_sub_one_le F (j a) (ha.trans_lt hs1)).trans ha

lemma unitBall_mono (j : 𝓗 →* Aˣ) {s s' : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (hs'0 : 0 ≤ s')
    (hs'1 : s' < 1) (h : s ≤ s') : unitBall F j hs0 hs1 ≤ unitBall F j hs'0 hs'1 :=
  fun _ hx => le_trans hx h

/-- The elements `X ∈ 𝔤` with `‖X + t‖ ≤ s` for some scalar `t`: an additive subgroup. -/
def scalarBall (𝔤 : Submodule F A) {s : ℝ} (hs : 0 ≤ s) : AddSubgroup 𝔤 where
  carrier := {X | ∃ t : F, ‖lmulPi F ((X : A) + algebraMap F A t)‖ ≤ s}
  zero_mem' := ⟨0, by simpa [lmulPi_zero] using hs⟩
  add_mem' := by
    rintro X Y ⟨t, ht⟩ ⟨u, hu⟩
    refine ⟨t + u, ?_⟩
    have e : ((X + Y : 𝔤) : A) + algebraMap F A (t + u) =
        ((X : A) + algebraMap F A t) + ((Y : A) + algebraMap F A u) := by
      simp only [Submodule.coe_add, map_add]; abel
    rw [e]; exact (norm_lmulPi_add_le F _ _).trans (max_le ht hu)
  neg_mem' := by
    rintro X ⟨t, ht⟩
    refine ⟨-t, ?_⟩
    have e : ((-X : 𝔤) : A) + algebraMap F A (-t) = -((X : A) + algebraMap F A t) := by
      simp only [Submodule.coe_neg, map_neg]; abel
    rw [e, norm_lmulPi_neg]; exact ht

lemma scalarBall_mono (𝔤 : Submodule F A) {s s' : ℝ} (hs : 0 ≤ s) (hs' : 0 ≤ s')
    (h : s ≤ s') : scalarBall 𝔤 hs ≤ scalarBall 𝔤 hs' :=
  fun _ ⟨t, ht⟩ => ⟨t, ht.trans h⟩

lemma scalarBall_mem_nhds (𝔤 : Submodule F A) {s : ℝ} (hs : 0 < s) :
    (scalarBall 𝔤 hs.le : Set 𝔤) ∈ 𝓝 (0 : 𝔤) := by
  have h := (continuous_subtype_val (p := fun a : A => a ∈ 𝔤)).continuousAt (x := 0)
    |>.preimage_mem_nhds (by simpa using lmulPi_ball_mem_nhds F (A := A) hs)
  refine Filter.mem_of_superset h fun X hX => ⟨0, ?_⟩
  simpa using hX

lemma isOpen_scalarBall (𝔤 : Submodule F A) {s : ℝ} (hs : 0 < s) :
    IsOpen (scalarBall 𝔤 hs.le : Set 𝔤) := by
  haveI := isTopologicalRing_of_moduleTopology F A
  exact AddSubgroup.isOpen_of_mem_nhds _ (scalarBall_mem_nhds 𝔤 hs)

/-- **`exp` carries an additive Haar measure to a Haar measure near `0`** (`p`-adic case, Jacobian
`1`). Let `j : 𝓗 → Aˣ` be a topological embedding of a group, `Z ⊆ 𝓗` the elements mapped to
scalars (all scalars being in the image), and `𝔤 ⊆ A` a subspace meeting the scalars only in `0`,
such that near `0`, `e^X ∈ j(𝓗)` for `X ∈ 𝔤`, and `e^W ∈ j(𝓗)` forces `W ∈ 𝔤 ⊕ F·1` (so `𝔤 ⊕ F·1`
is the Lie algebra of `𝓗`). Then for every Haar measure `μK` on `𝓗/Z` there is an additive Haar
measure `μ` on `𝔤` with `μ(S) = μK(e^S Z)` for measurable `S` near `0`.

Proof: `exp` is an isometry from the ball `‖W‖ ≤ r` onto `‖u − 1‖ ≤ r`, so on the lattices
`L_s = {X ∈ 𝔤 : ‖X + t‖ ≤ s for some t}` it carries cosets `X + L_s` onto cosets
`e^X Γ_s`, `Γ_s = {‖h − 1‖ ≤ s}`. The image of an additive Haar measure and `μK` then give equal
mass to all such cosets, which generate the Borel sets (`Measure.eq_of_forall_vadd_coset`). -/
theorem exists_isAddHaarMeasure_eq_expA_image
    {𝓗 : Type*} [Group 𝓗] [TopologicalSpace 𝓗] [IsTopologicalGroup 𝓗]
    (j : 𝓗 →* Aˣ) (hj : Topology.IsEmbedding fun h => ((j h : Aˣ) : A))
    (Z : Subgroup 𝓗) [Z.Normal]
    (hZ : ∀ h, h ∈ Z ↔ ((j h : Aˣ) : A) ∈ Set.range (algebraMap F A))
    (hscal : ∀ c : F, c ≠ 0 → ∃ h, ((j h : Aˣ) : A) = algebraMap F A c)
    (𝔤 : Submodule F A) (h𝔤 : ∀ t : F, algebraMap F A t ∈ 𝔤 → t = 0)
    (hexp : ∀ᶠ X in 𝓝 (0 : A), X ∈ 𝔤 → ∃ h, ((j h : Aˣ) : A) = expA F X)
    (hlog : ∀ᶠ W in 𝓝 (0 : A), ∀ h, ((j h : Aˣ) : A) = expA F W →
      ∃ t : F, W - algebraMap F A t ∈ 𝔤)
    [T2Space (𝓗 ⧸ Z)] [MeasurableSpace (𝓗 ⧸ Z)] [BorelSpace (𝓗 ⧸ Z)]
    (μK : Measure (𝓗 ⧸ Z)) [μK.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μK]
    [μK.IsOpenPosMeasure]
    [MeasurableSpace 𝔤] [BorelSpace 𝔤] [SecondCountableTopology 𝔤] [LocallyCompactSpace 𝔤] :
    ∃ μ : Measure 𝔤, μ.IsAddHaarMeasure ∧ ∃ U ∈ 𝓝 (0 : 𝔤), ∀ S : Set 𝔤, MeasurableSet S →
      S ⊆ U → μ S = μK {q | ∃ X ∈ S, ∃ h : 𝓗, ((j h : Aˣ) : A) = expA F (X : A) ∧
        q = (h : 𝓗 ⧸ Z)} := by
  classical
  letI := isTopologicalRing_of_moduleTopology F A
  haveI := t2Space_of_moduleTopology F A
  have hjinj : Function.Injective fun h => ((j h : Aˣ) : A) := hj.injective
  ------------------------------------------------------------------
  -- the projection `W ↦ W − p(W)` onto `𝔤` along the scalars
  have hA1 : (1 : A) ∉ 𝔤 := fun h => one_ne_zero (h𝔤 1 (by simpa using h))
  obtain ⟨f, hf1, hf𝔤⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hA1 inferInstance
  set p : A →ₗ[F] F := (f 1)⁻¹ • f with hpdef
  have hpX : ∀ X ∈ 𝔤, p X = 0 := by
    intro X hX
    have : f X ∈ 𝔤.map f := Submodule.mem_map_of_mem hX
    rw [hf𝔤, Submodule.mem_bot] at this
    simp [hpdef, this]
  have hpt : ∀ t : F, p (algebraMap F A t) = t := by
    intro t
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
    simp [hpdef, hf1]
  set q : A →ₗ[F] A := LinearMap.id - (Algebra.linearMap F A) ∘ₗ p with hqdef
  have hq : ∀ W, q W = W - algebraMap F A (p W) := fun W => rfl
  have hpc : Continuous p := IsModuleTopology.continuous_of_linearMap p
  have hqc : Continuous q := IsModuleTopology.continuous_of_linearMap q
  have hq_of : ∀ W (t : F), W - algebraMap F A t ∈ 𝔤 → q W ∈ 𝔤 ∧ p W = t := by
    intro W t h
    have h1 := hpX _ h
    rw [map_sub, hpt, sub_eq_zero] at h1
    exact ⟨by rw [hq, h1]; exact h, h1⟩
  have hqX : ∀ X ∈ 𝔤, q X = X := fun X hX => by rw [hq, hpX X hX, map_zero, sub_zero]
  have hqt : ∀ X ∈ 𝔤, ∀ t : F, q (X + algebraMap F A t) = X := by
    intro X hX t
    rw [hq, map_add, hpX X hX, hpt, zero_add, add_sub_cancel_right]
  ------------------------------------------------------------------
  -- neighbourhoods of `0`
  obtain ⟨U3, hU3, hsub⟩ := exists_nhds_mem_of_expA_mem F (A := A)
  obtain ⟨U4, hU4, hadd⟩ := expA_add_of_commute F (A := A)
  obtain ⟨U6, hU6, hU6o, hcont⟩ := exists_nhds_continuousOn_expA F (A := A)
  obtain ⟨U7, hU7, hneg⟩ := expA_mul_expA_neg F (A := F)
  have hT : ∀ᶠ t in 𝓝 (0 : F), expA F (algebraMap F A t) = algebraMap F A (expA F t) ∧
      expA F t ≠ 0 := by
    filter_upwards [eventually_expA_algebraMap F (A := A), hU7] with t h1 h2
    exact ⟨h1, left_ne_zero_of_mul_eq_one (hneg t h2)⟩
  set hexpS := {X : A | X ∈ 𝔤 → ∃ h, ((j h : Aˣ) : A) = expA F X}
  have hU : {W : A | W ∈ hexpS} ∩ {W | ∀ h, ((j h : Aˣ) : A) = expA F W →
      ∃ t : F, W - algebraMap F A t ∈ 𝔤} ∩ U3 ∩ U4 ∩
      q ⁻¹' (hexpS ∩ U4 ∩ U6) ∩ (fun W => algebraMap F A (p W)) ⁻¹' U4 ∩
      p ⁻¹' {t | expA F (algebraMap F A t) = algebraMap F A (expA F t) ∧ expA F t ≠ 0}
      ∈ 𝓝 (0 : A) := by
    have hq0 : q 0 = 0 := map_zero q
    have hp0 : p 0 = 0 := map_zero p
    refine inter_mem (inter_mem (inter_mem (inter_mem (inter_mem (inter_mem hexp hlog) hU3) hU4)
      ?_) ?_) ?_
    · exact hqc.continuousAt.preimage_mem_nhds (by rw [hq0]; exact inter_mem (inter_mem hexp hU4) hU6)
    · exact ((continuous_algebraMap F A).comp hpc).continuousAt.preimage_mem_nhds
        (by simp only [Function.comp, hp0, map_zero]; exact hU4)
    · exact hpc.continuousAt.preimage_mem_nhds (by rw [hp0]; exact hT)
  obtain ⟨r, hr0, hr1, hrU, hiso, hsurj⟩ := exists_expA_isometry F hU
  have hUW : ∀ W : A, ‖lmulPi F W‖ ≤ r → (W ∈ 𝔤 → ∃ h, ((j h : Aˣ) : A) = expA F W) ∧
      (∀ h, ((j h : Aˣ) : A) = expA F W → ∃ t : F, W - algebraMap F A t ∈ 𝔤) ∧ W ∈ U3 ∧
      W ∈ U4 ∧ ((q W ∈ 𝔤 → ∃ h, ((j h : Aˣ) : A) = expA F (q W)) ∧ q W ∈ U4 ∧ q W ∈ U6) ∧
      algebraMap F A (p W) ∈ U4 ∧
      (expA F (algebraMap F A (p W)) = algebraMap F A (expA F (p W)) ∧ expA F (p W) ≠ 0) := by
    intro W hW
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, ⟨⟨h5, h6⟩, h7⟩⟩, h8⟩, h9⟩ := hrU W hW
    exact ⟨h1, h2, h3, h4, ⟨h5, h6, h7⟩, h8, h9⟩
  have hnorm0 : ∀ a : A, ‖lmulPi F a‖ = 0 → a = 0 := fun a h =>
    lmulPi_injective F (by rw [norm_eq_zero.mp h, lmulPi_zero])
  have hexp0 : expA F (0 : A) = 1 := expA_zero_eq_one F
  have hr0' : ‖lmulPi F (0 : A)‖ ≤ r := by rw [lmulPi_zero, norm_zero]; exact hr0.le
  have hexpball : ∀ W : A, ‖lmulPi F W‖ ≤ r → ‖lmulPi F (expA F W - 1)‖ = ‖lmulPi F W‖ := by
    intro W hW
    have := hiso W 0 hW hr0'
    rwa [hexp0, sub_zero] at this
  ------------------------------------------------------------------
  -- `e^W ∈ j(𝓗)` for `W ∈ 𝔤 ⊕ F` small, as `e^{q W} · (scalar)`
  have E1 : ∀ W : A, ‖lmulPi F W‖ ≤ r → q W ∈ 𝔤 → ∃ g z : 𝓗, z ∈ Z ∧
      ((j g : Aˣ) : A) = expA F (q W) ∧ ((j (g * z) : Aˣ) : A) = expA F W := by
    intro W hW hqW
    obtain ⟨-, -, -, -, ⟨h5, h6, -⟩, h8, h9e, h9n⟩ := hUW W hW
    obtain ⟨g, hg⟩ := h5 hqW
    obtain ⟨z, hz⟩ := hscal _ h9n
    refine ⟨g, z, (hZ z).2 ⟨_, hz.symm⟩, hg, ?_⟩
    have hW' : W = q W + algebraMap F A (p W) := by rw [hq, sub_add_cancel]
    rw [map_mul, Units.val_mul, hg, hz, ← h9e]
    conv_rhs => rw [hW']
    exact (hadd _ h6 _ h8 (Algebra.commutes _ _).symm).symm
  -- the chart `Φ : 𝔤 → 𝓗/Z`
  let Φ : 𝔤 → 𝓗 ⧸ Z := fun X =>
    if h : ∃ g : 𝓗, ((j g : Aˣ) : A) = expA F (X : A) then ((h.choose : 𝓗) : 𝓗 ⧸ Z) else 1
  have hΦ : ∀ (X : 𝔤) (g : 𝓗), ((j g : Aˣ) : A) = expA F (X : A) → Φ X = (g : 𝓗 ⧸ Z) := by
    intro X g hg
    have h : ∃ g : 𝓗, ((j g : Aˣ) : A) = expA F (X : A) := ⟨g, hg⟩
    simp only [Φ, dif_pos h]
    rw [hjinj (h.choose_spec.trans hg.symm)]
  have E2 : ∀ (W : A) (_ : ‖lmulPi F W‖ ≤ r) (hqW : q W ∈ 𝔤) (g : 𝓗),
      ((j g : Aˣ) : A) = expA F W → Φ ⟨q W, hqW⟩ = (g : 𝓗 ⧸ Z) := by
    intro W hW hqW g hg
    obtain ⟨g', z, hz, hg', hgz⟩ := E1 W hW hqW
    rw [hΦ _ g' hg', ← hjinj (hgz.trans hg.symm)]
    exact QuotientGroup.eq.mpr (by simpa using hz)
  have hball : ∀ {s : ℝ} (hs : 0 ≤ s) (X : 𝔤), X ∈ scalarBall 𝔤 hs ↔
      ∃ W : A, ‖lmulPi F W‖ ≤ s ∧ q W = (X : A) := by
    intro s hs X
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨_, ht, hqt X X.2 t⟩
    · rintro ⟨W, hW, hWX⟩
      refine ⟨p W, ?_⟩
      rwa [← hWX, hq, sub_add_cancel]
  -- the logarithm of `j(𝓗)` near `1`
  have E3 : ∀ {s : ℝ}, s ≤ r → ∀ h : 𝓗, ‖lmulPi F (((j h : Aˣ) : A) - 1)‖ ≤ s →
      ∃ W : A, ‖lmulPi F W‖ ≤ s ∧ q W ∈ 𝔤 ∧ expA F W = ((j h : Aˣ) : A) := by
    intro s hs h hh
    obtain ⟨W, hW, hWe⟩ := hsurj _ (hh.trans hs)
    have hWn : ‖lmulPi F W‖ = ‖lmulPi F (((j h : Aˣ) : A) - 1)‖ := by
      rw [← hexpball W hW, hWe]
    obtain ⟨t, ht⟩ := (hUW W hW).2.1 h hWe.symm
    exact ⟨W, by rw [hWn]; exact hh, (hq_of W t ht).1, hWe⟩
  have hgnorm : ∀ g : 𝓗, ‖lmulPi F (((j g : Aˣ) : A) - 1)‖ ≤ r →
      ‖lmulPi F ((j g : Aˣ) : A)‖ ≤ 1 ∧ ‖lmulPi F (((j g)⁻¹ : Aˣ) : A)‖ ≤ 1 := by
    intro g hg
    refine ⟨norm_lmulPi_le_one_of (hg.trans hr1.le), norm_lmulPi_le_one_of ?_⟩
    exact (norm_lmulPi_inv_sub_one_le F (j g) (hg.trans_lt hr1)).trans (hg.trans hr1.le)
  ------------------------------------------------------------------
  -- cosets of `L_s` go to cosets of `Γ_s`
  have E4 : ∀ {s : ℝ} (hs0 : 0 ≤ s) (hsr : s ≤ r) (X : 𝔤), X ∈ scalarBall 𝔤 hr0.le →
      Φ '' (X +ᵥ (scalarBall 𝔤 hs0 : Set 𝔤)) =
        Φ X • ((QuotientGroup.mk : 𝓗 → 𝓗 ⧸ Z) ''
          (unitBall F j hs0 (hsr.trans_lt hr1) : Set 𝓗)) := by
    intro s hs0 hsr X hX
    obtain ⟨Ŵ, hŴ, hqŴ⟩ := (hball hr0.le X).mp hX
    have hqŴ' : q Ŵ ∈ 𝔤 := hqŴ ▸ X.2
    obtain ⟨g, z, -, -, hgz⟩ := E1 Ŵ hŴ hqŴ'
    have hΦX : Φ X = ((g * z : 𝓗) : 𝓗 ⧸ Z) := by
      have := E2 Ŵ hŴ hqŴ' (g * z) hgz
      rwa [show (⟨q Ŵ, hqŴ'⟩ : 𝔤) = X from Subtype.ext hqŴ] at this
    have hg₀r : ‖lmulPi F (((j (g * z) : Aˣ) : A) - 1)‖ ≤ r := by
      rw [hgz, hexpball Ŵ hŴ]; exact hŴ
    obtain ⟨hg₀1, hg₀i⟩ := hgnorm _ hg₀r
    ext y
    constructor
    · rintro ⟨Y', hY', rfl⟩
      rw [mem_vadd_coset_iff] at hY'
      obtain ⟨Ŷ, hŶ, hqŶ⟩ := (hball hs0 _).mp hY'
      have hsum : ‖lmulPi F (Ŵ + Ŷ)‖ ≤ r :=
        (norm_lmulPi_add_le F _ _).trans (max_le hŴ (hŶ.trans hsr))
      have hqsum : q (Ŵ + Ŷ) = (Y' : A) := by
        rw [map_add, hqŴ, hqŶ, Submodule.coe_add, Submodule.coe_neg]; abel
      have hqsum' : q (Ŵ + Ŷ) ∈ 𝔤 := hqsum ▸ Y'.2
      obtain ⟨g', z', -, -, hg'z'⟩ := E1 _ hsum hqsum'
      have hΦY : Φ Y' = ((g' * z' : 𝓗) : 𝓗 ⧸ Z) := by
        have := E2 _ hsum hqsum' (g' * z') hg'z'
        rwa [show (⟨q (Ŵ + Ŷ), hqsum'⟩ : 𝔤) = Y' from Subtype.ext hqsum] at this
      rw [Set.mem_smul_set]
      refine ⟨(((g * z)⁻¹ * (g' * z') : 𝓗) : 𝓗 ⧸ Z), ⟨(g * z)⁻¹ * (g' * z'), ?_, rfl⟩, ?_⟩
      · show ‖lmulPi F (((j ((g * z)⁻¹ * (g' * z')) : Aˣ) : A) - 1)‖ ≤ s
        have e : ((j ((g * z)⁻¹ * (g' * z')) : Aˣ) : A) - 1 = (((j (g * z))⁻¹ : Aˣ) : A) *
            (((j (g' * z') : Aˣ) : A) - (j (g * z) : A)) := by
          rw [map_mul, map_inv, Units.val_mul, mul_sub, Units.inv_mul]
        rw [e]
        refine (norm_lmulPi_mul_le F _ _).trans ?_
        have h2 : ‖lmulPi F (((j (g' * z') : Aˣ) : A) - (j (g * z) : A))‖ = ‖lmulPi F Ŷ‖ := by
          rw [hg'z', hgz, hiso _ _ hsum hŴ, add_sub_cancel_left]
        rw [h2]
        calc _ ≤ 1 * ‖lmulPi F Ŷ‖ := mul_le_mul_of_nonneg_right hg₀i (norm_nonneg _)
          _ ≤ s := by rw [one_mul]; exact hŶ
      · rw [hΦX, hΦY, smul_eq_mul, ← QuotientGroup.mk_mul, mul_inv_cancel_left]
    · intro hy
      rw [Set.mem_smul_set] at hy
      obtain ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩ := hy
      have hγ' : ‖lmulPi F (((j γ : Aˣ) : A) - 1)‖ ≤ s := hγ
      have hgγ : ‖lmulPi F (((j (g * z * γ) : Aˣ) : A) - 1)‖ ≤ r :=
        (unitBall F j hr0.le hr1).mul_mem (show g * z ∈ unitBall F j hr0.le hr1 from hg₀r)
          (show γ ∈ unitBall F j hr0.le hr1 from hγ'.trans hsr)
      obtain ⟨Vh, hVh, hqVh, hVhe⟩ := E3 le_rfl _ hgγ
      have hdist : ‖lmulPi F (Vh - Ŵ)‖ ≤ s := by
        rw [← hiso _ _ hVh hŴ, hVhe, ← hgz]
        have e : ((j (g * z * γ) : Aˣ) : A) - (j (g * z) : A) =
            (j (g * z) : A) * (((j γ : Aˣ) : A) - 1) := by
          rw [map_mul (f := j) (g * z) γ, Units.val_mul, mul_sub, mul_one]
        rw [e]
        calc _ ≤ ‖lmulPi F ((j (g * z) : Aˣ) : A)‖ * ‖lmulPi F (((j γ : Aˣ) : A) - 1)‖ :=
              norm_lmulPi_mul_le F _ _
          _ ≤ 1 * s := mul_le_mul hg₀1 hγ' (norm_nonneg _) zero_le_one
          _ = s := one_mul s
      refine ⟨⟨q Vh, hqVh⟩, ?_, ?_⟩
      · rw [mem_vadd_coset_iff, hball hs0]
        refine ⟨Vh - Ŵ, hdist, ?_⟩
        rw [map_sub, hqŴ, Submodule.coe_add, Submodule.coe_neg]
        abel
      · rw [E2 Vh hVh hqVh (g * z * γ) hVhe.symm, hΦX, smul_eq_mul, QuotientGroup.mk_mul]
  ------------------------------------------------------------------
  -- injectivity of the chart on `L_r`
  have E5 : Set.InjOn Φ (scalarBall 𝔤 hr0.le : Set 𝔤) := by
    intro X hX X' hX' hXX'
    obtain ⟨Ŵ, hŴ, hqŴ⟩ := (hball hr0.le X).mp hX
    obtain ⟨Ŵ', hŴ', hqŴ'⟩ := (hball hr0.le X').mp hX'
    have h1 : q Ŵ ∈ 𝔤 := hqŴ ▸ X.2
    have h1' : q Ŵ' ∈ 𝔤 := hqŴ' ▸ X'.2
    obtain ⟨g, z, -, -, hgz⟩ := E1 Ŵ hŴ h1
    obtain ⟨g', z', -, -, hgz'⟩ := E1 Ŵ' hŴ' h1'
    have eΦ := E2 Ŵ hŴ h1 _ hgz
    have eΦ' := E2 Ŵ' hŴ' h1' _ hgz'
    rw [show (⟨q Ŵ, h1⟩ : 𝔤) = X from Subtype.ext hqŴ] at eΦ
    rw [show (⟨q Ŵ', h1'⟩ : 𝔤) = X' from Subtype.ext hqŴ'] at eΦ'
    rw [eΦ, eΦ'] at hXX'
    have huZ : (g * z)⁻¹ * (g' * z') ∈ Z := QuotientGroup.eq.mp hXX'
    obtain ⟨c, hc⟩ := (hZ _).1 huZ
    have hgr : g * z ∈ unitBall F j hr0.le hr1 := by
      show _ ≤ r; rw [hgz, hexpball Ŵ hŴ]; exact hŴ
    have hgr' : g' * z' ∈ unitBall F j hr0.le hr1 := by
      show _ ≤ r; rw [hgz', hexpball Ŵ' hŴ']; exact hŴ'
    have hur := (unitBall F j hr0.le hr1).mul_mem ((unitBall F j hr0.le hr1).inv_mem hgr) hgr'
    obtain ⟨Vh, hVh, -, hVhe⟩ := E3 le_rfl _ hur
    have hVhbot : Vh ∈ (⊥ : Subalgebra F A) := by
      refine hsub Vh (hUW Vh hVh).2.2.1 ⊥ ?_
      rw [hVhe, ← hc]; exact Subalgebra.algebraMap_mem _ c
    obtain ⟨v, hv⟩ := Algebra.mem_bot.mp hVhbot
    have hmul : expA F Ŵ' = expA F (Ŵ + Vh) := by
      rw [hadd _ (hUW Ŵ hŴ).2.2.2.1 _ (hUW Vh hVh).2.2.2.1
        (by rw [← hv]; exact (Algebra.commutes v Ŵ).symm), hVhe, ← hgz, ← hgz', ← Units.val_mul,
        ← map_mul, mul_inv_cancel_left]
    have hsumr : ‖lmulPi F (Ŵ + Vh)‖ ≤ r := (norm_lmulPi_add_le F _ _).trans (max_le hŴ hVh)
    have heq : Ŵ' = Ŵ + Vh := by
      have := hiso _ _ hŴ' hsumr
      rw [hmul, sub_self, lmulPi_zero, norm_zero] at this
      exact sub_eq_zero.mp (hnorm0 _ this.symm)
    apply Subtype.ext
    rw [← hqŴ, ← hqŴ', heq, ← hv, map_add,
      show q (algebraMap F A v) = 0 by rw [hq, hpt, sub_self], add_zero]
  ------------------------------------------------------------------
  -- continuity of the chart on `L_r`
  have hcontΦ : ContinuousOn Φ (scalarBall 𝔤 hr0.le : Set 𝔤) := by
    have hsmall : ∀ X ∈ (scalarBall 𝔤 hr0.le : Set 𝔤),
        ((X : A) ∈ 𝔤 → ∃ h, ((j h : Aˣ) : A) = expA F (X : A)) ∧ (X : A) ∈ U6 := by
      intro X hX
      obtain ⟨W, hW, hqW⟩ := (hball hr0.le X).mp hX
      obtain ⟨-, -, -, -, ⟨h5, -, h7⟩, -⟩ := hUW W hW
      rw [← hqW]; exact ⟨h5, h7⟩
    let ψ : 𝔤 → 𝓗 := fun X =>
      if h : ∃ g : 𝓗, ((j g : Aˣ) : A) = expA F (X : A) then h.choose else 1
    have hψ : ∀ X ∈ (scalarBall 𝔤 hr0.le : Set 𝔤),
        ((j (ψ X) : Aˣ) : A) = expA F (X : A) := by
      intro X hX
      have h : ∃ g : 𝓗, ((j g : Aˣ) : A) = expA F (X : A) := (hsmall X hX).1 X.2
      simp only [ψ, dif_pos h]; exact h.choose_spec
    have hψc : ContinuousOn ψ (scalarBall 𝔤 hr0.le : Set 𝔤) := by
      rw [hj.continuousOn_iff]
      refine ContinuousOn.congr (f := fun X : 𝔤 => expA F (X : A)) ?_ fun X hX => hψ X hX
      exact hcont.comp continuous_subtype_val.continuousOn fun X hX => (hsmall X hX).2
    refine (QuotientGroup.continuous_mk.comp_continuousOn hψc).congr fun X hX => ?_
    exact hΦ X (ψ X) (hψ X hX)
  ------------------------------------------------------------------
  -- compactness of `L_r`, openness of `Γ_r`
  have h𝔤closed : IsClosed (𝔤 : Set A) := Submodule.closed_of_finiteDimensional 𝔤
  have hcpt : IsCompact (scalarBall 𝔤 hr0.le : Set 𝔤) := by
    have hK : IsCompact (Subtype.val ⁻¹' (q '' {a : A | ‖lmulPi F a‖ ≤ r}) : Set 𝔤) :=
      h𝔤closed.isClosedEmbedding_subtypeVal.isCompact_preimage
        ((isCompact_lmulPi_ball F r).image hqc)
    refine hK.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ (isOpen_scalarBall 𝔤 hr0)) ?_
    intro X hX
    obtain ⟨W, hW, hqW⟩ := (hball hr0.le X).mp hX
    exact ⟨W, hW, hqW⟩
  have hΓopen : IsOpen (unitBall F j hr0.le hr1 : Set 𝓗) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    have hc : Continuous fun h : 𝓗 => ((j h : Aˣ) : A) - 1 := hj.continuous.sub continuous_const
    exact hc.continuousAt (x := 1) |>.preimage_mem_nhds (t := {a : A | ‖lmulPi F a‖ ≤ r})
      (by simp only [map_one, Units.val_one, sub_self]; exact lmulPi_ball_mem_nhds F hr0)
  ------------------------------------------------------------------
  -- the lattices `L n = L_{r/2ⁿ}`
  set s : ℕ → ℝ := fun n => r * (1 / 2) ^ n with hsdef
  have hs0 : ∀ n, 0 < s n := fun n => by positivity
  have hsr : ∀ n, s n ≤ r := fun n =>
    mul_le_of_le_one_right hr0.le (pow_le_one₀ (by norm_num) (by norm_num))
  set L : ℕ → AddSubgroup 𝔤 := fun n => scalarBall 𝔤 (hs0 n).le with hLdef
  have hL0 : L 0 = scalarBall 𝔤 hr0.le :=
    le_antisymm (scalarBall_mono 𝔤 _ _ (by simp [hsdef])) (scalarBall_mono 𝔤 _ _ (by simp [hsdef]))
  have hanti : Antitone L := fun n m h =>
    scalarBall_mono 𝔤 _ _ (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) h) hr0.le)
  have hbasis : ∀ U ∈ 𝓝 (0 : 𝔤), ∃ n, (L n : Set 𝔤) ⊆ U := by
    intro U hU'
    obtain ⟨u, hu, huU⟩ := (mem_nhds_subtype (𝔤 : Set A) 0 U).mp hU'
    have hu' : q ⁻¹' u ∈ 𝓝 (0 : A) :=
      hqc.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hu)
    obtain ⟨σ, hσ, hσu⟩ := exists_lmulPi_ball_subset F hu'
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hσ hr0) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, fun X hX => huU ?_⟩
    obtain ⟨W, hW, hqW⟩ := (hball (hs0 n).le X).mp hX
    show (X : A) ∈ u
    rw [← hqW]
    refine hσu W (hW.trans ?_)
    calc s n = r * (1 / 2) ^ n := rfl
      _ ≤ r * (σ / r) := mul_le_mul_of_nonneg_left hn.le hr0.le
      _ = σ := mul_div_cancel₀ σ hr0.ne'
  set L0 : Set 𝔤 := (L 0 : Set 𝔤) with hL0def
  have hL0eq : L0 = (scalarBall 𝔤 hr0.le : Set 𝔤) := by rw [hL0def, hL0]
  have hL0open : IsOpen L0 := isOpen_scalarBall 𝔤 (hs0 0)
  have hL0m : MeasurableSet L0 := hL0open.measurableSet
  have hcpt' : IsCompact L0 := by rw [hL0eq]; exact hcpt
  have hcont' : ContinuousOn Φ L0 := by rw [hL0eq]; exact hcontΦ
  have hinj' : Set.InjOn Φ L0 := by rw [hL0eq]; exact E5
  have hcos : ∀ n, ∀ x ∈ L 0, x +ᵥ (L n : Set 𝔤) ⊆ L0 := by
    intro n x hx y hy
    rw [mem_vadd_coset_iff] at hy
    have := (L 0).add_mem hx (hanti (Nat.zero_le n) hy)
    rwa [add_neg_cancel_left] at this
  ------------------------------------------------------------------
  -- the pull-back `ν` of `μK` by the chart
  haveI : CompactSpace L0 := isCompact_iff_compactSpace.mp hcpt'
  let fL : L0 → 𝓗 ⧸ Z := fun X => Φ X
  have hfc : Continuous fL := hcont'.domRestrict
  have hfi : Function.Injective fL := fun X Y h => Subtype.ext (hinj' X.2 Y.2 h)
  have hfe : MeasurableEmbedding fL := (hfc.isClosedEmbedding hfi).measurableEmbedding
  set ν : Measure 𝔤 := Measure.map Subtype.val (Measure.comap fL μK) with hνdef
  have hν : ∀ S, MeasurableSet S → ν S = μK (Φ '' (S ∩ L0)) := by
    intro S hS
    rw [hνdef, Measure.map_apply measurable_subtype_coe hS, hfe.comap_apply]
    congr 1
    ext y
    constructor
    · rintro ⟨X, hX, rfl⟩; exact ⟨X, ⟨hX, X.2⟩, rfl⟩
    · rintro ⟨X, ⟨hXS, hXL⟩, rfl⟩; exact ⟨⟨X, hXL⟩, hXS, rfl⟩
  have hνcos : ∀ n, ∀ x ∈ L 0, ν (x +ᵥ (L n : Set 𝔤)) =
      μK ((QuotientGroup.mk : 𝓗 → 𝓗 ⧸ Z) ''
        (unitBall F j (hs0 n).le ((hsr n).trans_lt hr1) : Set 𝓗)) := by
    intro n x hx
    rw [hν _ ((isOpen_scalarBall 𝔤 (hs0 n)).vadd x).measurableSet,
      Set.inter_eq_left.mpr (hcos n x hx), E4 (hs0 n).le (hsr n) x (hL0 ▸ hx), measure_smul]
  have hνL0 : ν L0 = μK ((QuotientGroup.mk : 𝓗 → 𝓗 ⧸ Z) ''
      (unitBall F j (hs0 0).le ((hsr 0).trans_lt hr1) : Set 𝓗)) := by
    rw [← hνcos 0 0 (L 0).zero_mem, zero_vadd]
  have hνpos : ν L0 ≠ 0 := by
    rw [hνL0]
    refine (IsOpen.measure_pos μK ?_ (Set.Nonempty.image _ ⟨1, Subgroup.one_mem _⟩)).ne'
    refine QuotientGroup.isOpenMap_coe _ ?_
    exact Subgroup.isOpen_mono (unitBall_mono j hr0.le hr1 _ _ (by simp [hsdef])) hΓopen
  have hνfin : ν L0 ≠ ⊤ := by
    rw [hν _ hL0m, Set.inter_self]
    exact ((hcpt'.image_of_continuousOn hcont').measure_lt_top).ne
  haveI : IsFiniteMeasure ν := ⟨by
    rw [← measure_add_measure_compl hL0m, hν _ hL0m.compl, Set.compl_inter_self, Set.image_empty,
      measure_empty, add_zero]
    exact lt_top_iff_ne_top.mpr hνfin⟩
  ------------------------------------------------------------------
  -- comparison with an additive Haar measure
  set lam : Measure 𝔤 := Measure.addHaar with hlamdef
  have hlam0 : lam L0 ≠ 0 := (hL0open.measure_pos lam ⟨0, (L 0).zero_mem⟩).ne'
  have hlamT : lam L0 ≠ ⊤ := hcpt'.measure_lt_top.ne
  set c : ENNReal := ν L0 / lam L0 with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Ne, ENNReal.div_eq_zero_iff]; exact not_or.mpr ⟨hνpos, hlamT⟩
  have hcT : c ≠ ⊤ := by
    rw [hcdef, Ne, ENNReal.div_eq_top]; push Not
    exact ⟨fun _ => hlam0, fun h => absurd h hνfin⟩
  have hext : c • lam.restrict L0 = ν := by
    haveI : IsFiniteMeasure (c • lam.restrict L0) := ⟨by
      rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
      exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hcT) (lt_top_iff_ne_top.mpr hlamT)⟩
    refine Measure.eq_of_forall_vadd_coset L hanti (fun n => isOpen_scalarBall 𝔤 (hs0 n)) hcpt'
      hbasis _ _ ?_ ?_ ?_ ?_ ?_
    · rw [Measure.smul_apply, Measure.restrict_apply hL0m.compl, Set.compl_inter_self,
        measure_empty, smul_zero]
    · rw [hν _ hL0m.compl, Set.compl_inter_self, Set.image_empty, measure_empty]
    · intro n x hx
      have hm := (isOpen_scalarBall 𝔤 (hs0 n)).measurableSet
      rw [Measure.smul_apply, Measure.smul_apply, Measure.restrict_apply (hm.const_vadd x),
        Measure.restrict_apply hm, Set.inter_eq_left.mpr (hcos n x hx),
        Set.inter_eq_left.mpr (show (L n : Set 𝔤) ⊆ L0 from hanti (Nat.zero_le n)),
        measure_vadd]
    · intro n x hx
      rw [hνcos n x hx, ← hνcos n 0 (L 0).zero_mem, zero_vadd]
    · rw [Measure.smul_apply, Measure.restrict_apply hL0m, Set.inter_self, smul_eq_mul, hcdef,
        ENNReal.div_mul_cancel hlam0 hlamT]
  ------------------------------------------------------------------
  haveI : (c • lam).IsAddHaarMeasure := Measure.IsAddHaarMeasure.smul lam hc0 hcT
  refine ⟨c • lam, inferInstance, L0 ∩ {X : 𝔤 | ‖lmulPi F (X : A)‖ ≤ r},
    inter_mem (hL0open.mem_nhds (L 0).zero_mem)
      ((continuous_subtype_val (p := fun a : A => a ∈ 𝔤)).continuousAt (x := (0 : 𝔤))
        |>.preimage_mem_nhds (t := {a : A | ‖lmulPi F a‖ ≤ r})
        (by simpa using lmulPi_ball_mem_nhds F (A := A) hr0)), fun S hS hSU => ?_⟩
  have hSL : S ∩ L0 = S := Set.inter_eq_left.mpr (hSU.trans Set.inter_subset_left)
  have h1 : (c • lam) S = ν S := by
    rw [← hext, Measure.smul_apply, Measure.smul_apply, Measure.restrict_apply hS, hSL]
  rw [h1, hν S hS, hSL]
  congr 1
  ext y
  constructor
  · rintro ⟨X, hXS, rfl⟩
    obtain ⟨g, hg⟩ := (hUW X (hSU hXS).2).1 X.2
    exact ⟨X, hXS, g, hg, hΦ X g hg⟩
  · rintro ⟨X, hXS, g, hg, rfl⟩
    exact ⟨X, hXS, hΦ X g hg⟩

end ExpChart

end GSpinGGP
