/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The function `Ξ^{H\G}` on a homogeneous space (BP §6.7)

Beuzart-Plessis (*A local trace formula for the Gan-Gross-Prasad conjecture for unitary groups:
the archimedean case*, Astérisque 418, §6.7, p. 147; Thesis §8.4) defines, for a compact subset
`C ⊆ G(F)` with nonempty interior,

  `Ξ^{H\G}_C(x) = vol_{H\G}(xC)^{-1/2}`,   `x ∈ H(F)\G(F)`.

Only three things about `H(F)\G(F)` enter the elementary properties of this function: the
projection `π : G → X` onto the homogeneous space, the fact that right translation by `G`
descends along `π`, and the right invariance of the measure on `X`. This file works in that
generality: `G` is any topological group, `X` any measurable space, `π : G → X` any map and `μ`
any measure on `X` (no unimodularity, no reductive structure, no compactness of a centre).

## Main definitions

* `IsInvariantQuotient π μ`: right translations descend along `π`, and
  `μ(π(S h)) = μ(π(S))` for all `S ⊆ G`, `h ∈ G`.
* `relVol π μ C g = μ(π(g C))`: the volume of `xC` for `x = π(g)`.
* `relXi π μ C g = μ(π(g C))^{-1/2}`: BP's `Ξ^{H\G}_C(x)` at `x = π(g)`, as a function of a
  representative `g` (it depends only on `π g`: `IsInvariantQuotient.relXi_eq_of_eq`). Lean's
  junk values `∞.toReal = 0` and `0 ^ (-1/2) = 0` make it `0` where the volume is `0` or `∞`.

## Main results

* `exists_finset_subset_iUnion_image_mul_right`: a compact set is covered by finitely many right
  translates `C j` of a set `C` with nonempty interior.
* `IsInvariantQuotient.exists_relVol_le`: the key estimate `μ(π(gD)) ≤ n μ(π(gC))` for all `g`,
  for `D` compact and `C` with nonempty interior.
* **BP Prop 6.7.1(i)(a)** (`IsInvariantQuotient.exists_relXi_mul_le`): `Ξ^{H\G}(xk) ∼ Ξ^{H\G}(x)`
  uniformly for `k` in a compact set; and the independence of `C` up to equivalence
  (`IsInvariantQuotient.exists_relXi_le_relXi`), stated without proof in BP p. 147.
  (BP Prop 6.7.1(i)(b), for the log-norm, is `IsLogNorm.exists_fiberInf_mul_le_add` of
  `HarmonicAnalysis/LogNorm.lean`.)
* `IsInvariantQuotient.exists_ofReal_relXi_sq_le`: on a set `π(gD)`, `Ξ^{H\G}_C(y)² ≤ n / μ(π(gD))`,
  which makes `∫_{xD} Ξ^{H\G}_C(y)² dy ≤ n` (the step of BP's proof of 6.7.1(iii) where "on each
  `xC`, `Ξ^{H\G}(x)² = vol(xC)^{-1}` cancels the volume").
* Measurability: `upperSemicontinuous_relVol` (for an outer regular `μ` and continuous `π`) and
  `IsInvariantQuotient.measurable_of_relXi` (for a quotient map `π`).
-/

open MeasureTheory Set Topology Filter
open scoped ENNReal Pointwise

noncomputable section

namespace GSpinGGP

variable {G X : Type*} [Group G] [MeasurableSpace X]

/-! ### The setting -/

/-- `π : G → X` is a quotient of `G` by a left action (such as `G → H\G` or `G → H\G/A` for a
central `A`) on which the right translations of `G` descend, and `μ` is a right-invariant measure
on `X`: `μ(π(S h)) = μ(π(S))` for every subset `S ⊆ G` and every `h ∈ G`. For `X = H\G` with a
`G`-invariant measure (the quotient of Haar measures for unimodular `G` and `H`), both hold. -/
structure IsInvariantQuotient (π : G → X) (μ : Measure X) : Prop where
  descends : ∀ g g' h : G, π g = π g' → π (g * h) = π (g' * h)
  measure_image_mul_right : ∀ (S : Set G) (h : G), μ (π '' ((· * h) '' S)) = μ (π '' S)

/-- The volume `μ(xC)` of the translate `xC = π(gC)` of `C ⊆ G`, for `x = π(g)`. -/
def relVol (π : G → X) (μ : Measure X) (C : Set G) (g : G) : ℝ≥0∞ :=
  μ (π '' ((g * ·) '' C))

/-- **BP's `Ξ^{H\G}_C(x) = vol_{H\G}(xC)^{-1/2}`** (BP §6.7, p. 147; Thesis §8.4) at `x = π(g)`,
as a function of the representative `g ∈ G`. It is `0` (a junk value) when `μ(π(gC))` is `0` or
`∞`; for a measure that is finite on compacts and positive on open sets, with `π` continuous and
open, neither happens for compact `C` with nonempty interior. -/
def relXi (π : G → X) (μ : Measure X) (C : Set G) (g : G) : ℝ :=
  (relVol π μ C g).toReal ^ (-(1 / 2 : ℝ))

variable {π : G → X} {μ : Measure X}

theorem relVol_mono {C C' : Set G} (h : C ⊆ C') (g : G) : relVol π μ C g ≤ relVol π μ C' g :=
  measure_mono (image_mono (image_mono h))

/-- `μ(π(gk C)) = μ(π(g (kC)))`. -/
theorem relVol_mul (C : Set G) (g k : G) : relVol π μ C (g * k) = relVol π μ ((k * ·) '' C) g := by
  simp only [relVol, image_image, mul_assoc]

theorem relXi_nonneg (C : Set G) (g : G) : 0 ≤ relXi π μ C g :=
  Real.rpow_nonneg ENNReal.toReal_nonneg _

/-- `Ξ_C(g)² = μ(π(gC))⁻¹` (with the junk value `0` when the volume is `0` or `∞`). -/
theorem relXi_sq (C : Set G) (g : G) : relXi π μ C g ^ 2 = (relVol π μ C g)⁻¹.toReal := by
  rw [relXi, ← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg, ENNReal.toReal_inv]
  norm_num [Real.rpow_neg_one]

/-- `Ξ_C(g) = √(μ(π(gC))⁻¹)`. -/
theorem relXi_eq_sqrt (C : Set G) (g : G) :
    relXi π μ C g = Real.sqrt (relVol π μ C g)⁻¹.toReal := by
  rw [← relXi_sq, Real.sqrt_sq (relXi_nonneg C g)]

/-- `ofReal(Ξ_C(g)²) ≤ μ(π(gC))⁻¹`. -/
theorem ofReal_relXi_sq_le_inv (C : Set G) (g : G) :
    ENNReal.ofReal (relXi π μ C g ^ 2) ≤ (relVol π μ C g)⁻¹ := by
  rw [relXi_sq]; exact ENNReal.ofReal_toReal_le

namespace IsInvariantQuotient

variable (hπ : IsInvariantQuotient π μ)
include hπ

/-- `μ(xC)` depends only on `x = π(g)`. -/
theorem relVol_eq_of_eq (C : Set G) {g g' : G} (h : π g = π g') :
    relVol π μ C g = relVol π μ C g' := by
  simp only [relVol, image_image, hπ.descends g g' _ h]

/-- `Ξ_C(x)` depends only on `x = π(g)`. -/
theorem relXi_eq_of_eq (C : Set G) {g g' : G} (h : π g = π g') :
    relXi π μ C g = relXi π μ C g' := by
  rw [relXi, relXi, hπ.relVol_eq_of_eq C h]

/-- `μ(π(gC) h) = μ(π(gC))`, in the form `μ(π((gC) j)) = μ(π(gC))`. -/
theorem measure_image_mul_right_relVol (C : Set G) (g j : G) :
    μ (π '' ((· * j) '' ((g * ·) '' C))) = relVol π μ C g :=
  hπ.measure_image_mul_right _ j

end IsInvariantQuotient

/-! ### Covering a compact set by right translates -/

section Covering

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- A compact set `K` is covered by finitely many **right** translates `C j` of a set `C` with
nonempty interior. (Mathlib's `compact_covered_by_mul_left_translates` is the left version; the
right one is what a right-invariant measure on `H\G` needs. It is also
`IsCompact.exists_finite_cover_smul` for `Gᵐᵒᵖ` acting on `G`, applied to `interior C`.) -/
theorem exists_finset_subset_iUnion_image_mul_right {K C : Set G} (hK : IsCompact K)
    (hC : (interior C).Nonempty) : ∃ t : Finset G, K ⊆ ⋃ j ∈ t, (· * j) '' C := by
  obtain ⟨c₀, hc₀⟩ := hC
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : G => (· * x) '' interior C)
    (fun x => isOpenMap_mul_right x _ isOpen_interior)
    (fun k _ => mem_iUnion.2 ⟨c₀⁻¹ * k, c₀, hc₀, by group⟩)
  exact ⟨t, ht.trans (iUnion₂_mono fun j _ => image_mono interior_subset)⟩

namespace IsInvariantQuotient

variable (hπ : IsInvariantQuotient π μ)
include hπ

/-- **The key estimate.** For `D ⊆ G` compact and `C ⊆ G` with nonempty interior there is
`n ≥ 1` with `μ(π(gD)) ≤ n μ(π(gC))` for all `g ∈ G`: cover `D` by `n - 1` right translates
`C j` and use the right invariance of `μ`. -/
theorem exists_relVol_le {D C : Set G} (hD : IsCompact D) (hC : (interior C).Nonempty) :
    ∃ n : ℕ, 0 < n ∧ ∀ g, relVol π μ D g ≤ n * relVol π μ C g := by
  obtain ⟨t, ht⟩ := exists_finset_subset_iUnion_image_mul_right hD hC
  refine ⟨t.card + 1, Nat.succ_pos _, fun g => ?_⟩
  calc relVol π μ D g ≤ μ (⋃ j ∈ t, π '' ((· * j) '' ((g * ·) '' C))) := by
        apply measure_mono
        rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
        have := ht he
        simp only [mem_iUnion, mem_image] at this
        obtain ⟨j, hj, c, hc, rfl⟩ := this
        exact mem_iUnion₂.2 ⟨j, hj, g * c * j, ⟨g * c, ⟨c, hc, rfl⟩, rfl⟩, by rw [mul_assoc]⟩
    _ ≤ ∑ j ∈ t, μ (π '' ((· * j) '' ((g * ·) '' C))) := measure_biUnion_finset_le _ _
    _ = t.card * relVol π μ C g := by
        rw [Finset.sum_congr rfl fun j _ => hπ.measure_image_mul_right_relVol C g j,
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((t.card + 1 : ℕ) : ℝ≥0∞) * relVol π μ C g := by gcongr; exact_mod_cast Nat.le_succ _

/-- **BP Prop 6.7.1(i)(a), volume form.** For `C` compact with nonempty interior and `K`
compact, `μ(π(gkC)) ∼ μ(π(gC))` uniformly in `g ∈ G` and `k ∈ K`. -/
theorem exists_relVol_mul_le {C K : Set G} (hC : IsCompact C) (hCi : (interior C).Nonempty)
    (hK : IsCompact K) :
    ∃ n : ℕ, 0 < n ∧ ∀ g, ∀ k ∈ K,
      relVol π μ C (g * k) ≤ n * relVol π μ C g ∧ relVol π μ C g ≤ n * relVol π μ C (g * k) := by
  obtain ⟨n₁, hn₁, h₁⟩ := hπ.exists_relVol_le (hK.mul hC) hCi
  obtain ⟨n₂, -, h₂⟩ := hπ.exists_relVol_le (hK.inv.mul hC) hCi
  refine ⟨n₁ + n₂, by omega, fun g k hk => ⟨?_, ?_⟩⟩
  · calc relVol π μ C (g * k) = relVol π μ ((k * ·) '' C) g := relVol_mul C g k
      _ ≤ relVol π μ (K * C) g := by
          refine relVol_mono ?_ g
          rintro _ ⟨c, hc, rfl⟩; exact mul_mem_mul hk hc
      _ ≤ n₁ * relVol π μ C g := h₁ g
      _ ≤ ((n₁ + n₂ : ℕ) : ℝ≥0∞) * relVol π μ C g := by gcongr; omega
  · calc relVol π μ C g = relVol π μ C (g * k * k⁻¹) := by rw [mul_inv_cancel_right]
      _ = relVol π μ ((k⁻¹ * ·) '' C) (g * k) := relVol_mul C _ _
      _ ≤ relVol π μ (K⁻¹ * C) (g * k) := by
          refine relVol_mono ?_ _
          rintro _ ⟨c, hc, rfl⟩; exact mul_mem_mul (inv_mem_inv.2 hk) hc
      _ ≤ n₂ * relVol π μ C (g * k) := h₂ _
      _ ≤ ((n₁ + n₂ : ℕ) : ℝ≥0∞) * relVol π μ C (g * k) := by gcongr; omega

end IsInvariantQuotient

end Covering

/-! ### From volumes to `Ξ` -/

/-- If `a ≤ n b` with `n ≥ 1`, then `b⁻¹ ≤ n a⁻¹` (in `ℝ≥0∞`, including `0` and `∞`). -/
private theorem ennreal_inv_le_natCast_mul_inv {a b : ℝ≥0∞} {n : ℕ} (hn : 0 < n) (h : a ≤ n * b) :
    b⁻¹ ≤ n * a⁻¹ := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← div_eq_mul_inv, ← ENNReal.inv_div (Or.inl (ENNReal.natCast_ne_top n)) (Or.inl hn0),
    ENNReal.inv_le_inv, ENNReal.div_le_iff hn0 (ENNReal.natCast_ne_top n), mul_comm]
  exact h

/-- If `a ≤ n b` and `b ≤ m a` (with `n ≥ 1`), then `(b⁻¹).toReal ≤ n (a⁻¹).toReal`. -/
private theorem ennreal_toReal_inv_le_natCast_mul {a b : ℝ≥0∞} {n m : ℕ} (hn : 0 < n) (hab : a ≤ n * b)
    (hba : b ≤ m * a) : b⁻¹.toReal ≤ n * a⁻¹.toReal := by
  rcases eq_or_ne a 0 with rfl | ha
  · have : b = 0 := by simpa using hba
    simp [this]
  have hfin : (n : ℝ≥0∞) * a⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (ENNReal.inv_ne_top.2 ha)
  calc b⁻¹.toReal ≤ ((n : ℝ≥0∞) * a⁻¹).toReal :=
        ENNReal.toReal_mono hfin (ennreal_inv_le_natCast_mul_inv hn hab)
    _ = n * a⁻¹.toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]

/-- Two-sided comparability of volumes gives comparability of `Ξ`:
if `μ(π(gC)) ≤ n μ(π(g'C))` and `μ(π(g'C)) ≤ m μ(π(gC))`, then `Ξ_C(g') ≤ √n Ξ_C(g)`. -/
theorem relXi_le_of_relVol_le {C : Set G} {g g' : G} {n m : ℕ} (hn : 0 < n)
    (h₁ : relVol π μ C g ≤ n * relVol π μ C g') (h₂ : relVol π μ C g' ≤ m * relVol π μ C g) :
    relXi π μ C g' ≤ Real.sqrt n * relXi π μ C g := by
  rw [relXi_eq_sqrt, relXi_eq_sqrt, ← Real.sqrt_mul (Nat.cast_nonneg n)]
  exact Real.sqrt_le_sqrt (ennreal_toReal_inv_le_natCast_mul hn h₁ h₂)

section Translation

variable [TopologicalSpace G] [IsTopologicalGroup G]

namespace IsInvariantQuotient

variable (hπ : IsInvariantQuotient π μ)
include hπ

/-- **BP Prop 6.7.1(i)(a)**: for `C` compact with nonempty interior and `K` compact,
`Ξ^{H\G}_C(xk) ∼ Ξ^{H\G}_C(x)` uniformly in `x` and `k ∈ K`: there is `c > 0` with
`Ξ_C(gk) ≤ c Ξ_C(g)` and `Ξ_C(g) ≤ c Ξ_C(gk)` (BP leaves this to the reader). -/
theorem exists_relXi_mul_le {C K : Set G} (hC : IsCompact C) (hCi : (interior C).Nonempty)
    (hK : IsCompact K) :
    ∃ c, 0 < c ∧ ∀ g, ∀ k ∈ K,
      relXi π μ C (g * k) ≤ c * relXi π μ C g ∧ relXi π μ C g ≤ c * relXi π μ C (g * k) := by
  obtain ⟨n, hn, h⟩ := hπ.exists_relVol_mul_le hC hCi hK
  exact ⟨Real.sqrt n, Real.sqrt_pos.2 (by exact_mod_cast hn), fun g k hk =>
    ⟨relXi_le_of_relVol_le hn (h g k hk).2 (h g k hk).1,
      relXi_le_of_relVol_le hn (h g k hk).1 (h g k hk).2⟩⟩

/-- **Independence of `C`** (BP p. 147, "not hard to see"): for compact `C, C'` with nonempty
interiors, `Ξ_{C'} ≪ Ξ_C` (and, exchanging them, `Ξ_{C'} ∼ Ξ_C`). -/
theorem exists_relXi_le_relXi {C C' : Set G} (hC : IsCompact C) (hCi : (interior C).Nonempty)
    (hC' : IsCompact C') (hC'i : (interior C').Nonempty) :
    ∃ c, 0 < c ∧ ∀ g, relXi π μ C' g ≤ c * relXi π μ C g := by
  obtain ⟨n, hn, h₁⟩ := hπ.exists_relVol_le hC hC'i
  obtain ⟨m, -, h₂⟩ := hπ.exists_relVol_le hC' hCi
  refine ⟨Real.sqrt n, Real.sqrt_pos.2 (by exact_mod_cast hn), fun g => ?_⟩
  rw [relXi_eq_sqrt, relXi_eq_sqrt, ← Real.sqrt_mul (Nat.cast_nonneg n)]
  exact Real.sqrt_le_sqrt (ennreal_toReal_inv_le_natCast_mul hn (h₁ g) (h₂ g))

/-- **`Ξ²` on a translate `π(gD)`** (the step of BP's proof of Prop 6.7.1(iii), p. 151, where
"`∫_{yC} Ξ^{H\G}(x)² dx ≪ vol(yC) Ξ^{H\G}(y)²`"): for `D` compact and `C` with nonempty interior
there is `n ≥ 1` with `Ξ_C(g e)² ≤ n μ(π(gD))⁻¹` for all `g ∈ G` and `e ∈ D`. -/
theorem exists_ofReal_relXi_sq_le {C D : Set G} (hCi : (interior C).Nonempty) (hD : IsCompact D) :
    ∃ n : ℕ, 0 < n ∧ ∀ g, ∀ e ∈ D,
      ENNReal.ofReal (relXi π μ C (g * e) ^ 2) ≤ n * (relVol π μ D g)⁻¹ := by
  obtain ⟨n, hn, h⟩ := hπ.exists_relVol_le (hD.inv.mul hD) hCi
  refine ⟨n, hn, fun g e he => (ofReal_relXi_sq_le_inv C _).trans ?_⟩
  refine ennreal_inv_le_natCast_mul_inv hn ((?_ : relVol π μ D g ≤ _).trans (h (g * e)))
  calc relVol π μ D g = relVol π μ D (g * e * e⁻¹) := by rw [mul_inv_cancel_right]
    _ = relVol π μ ((e⁻¹ * ·) '' D) (g * e) := relVol_mul D _ _
    _ ≤ relVol π μ (D⁻¹ * D) (g * e) := by
        refine relVol_mono ?_ _
        rintro _ ⟨d, hd, rfl⟩; exact mul_mem_mul (inv_mem_inv.2 he) hd

end IsInvariantQuotient

end Translation

/-! ### Measurability -/

section Measurability

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]

/-- **`g ↦ μ(π(gC))` is upper semicontinuous** for `C` compact, `π` continuous and `μ` outer
regular: if `μ(π(gC)) < t`, take an open `U ⊇ π(gC)` with `μ(U) < t`; then `g'C ⊆ π⁻¹(U)` for
`g'` near `g`. -/
theorem upperSemicontinuous_relVol [μ.OuterRegular] (hπc : Continuous π) {C : Set G}
    (hC : IsCompact C) : UpperSemicontinuous (relVol π μ C) := by
  intro g t ht
  obtain ⟨U, hUA, hUo, hUt⟩ := Set.exists_isOpen_lt_of_lt _ t ht
  have hK : IsCompact ((g * ·) '' C) := hC.image (continuous_const.mul continuous_id)
  obtain ⟨V, hV, hVK⟩ := compact_open_separated_mul_left hK (hUo.preimage hπc)
    (image_subset_iff.1 hUA)
  have hcont : Tendsto (fun g' : G => g' * g⁻¹) (𝓝 g) (𝓝 1) := by
    have hc : Continuous fun g' : G => g' * g⁻¹ := by fun_prop
    have h := hc.tendsto g
    simp only [mul_inv_cancel] at h
    exact h
  filter_upwards [hcont hV] with g' hg'
  refine lt_of_le_of_lt (measure_mono ?_) hUt
  rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  have : g' * g⁻¹ * (g * c) ∈ π ⁻¹' U := hVK (mul_mem_mul hg' ⟨c, hc, rfl⟩)
  simpa [mul_assoc] using this

variable [OpensMeasurableSpace X]

/-- **Measurability of `Ξ^{H\G}_C` on the quotient**: if `π` is a quotient map, `μ` is outer
regular and `C` is compact, then any `ξ : X → ℝ` with `ξ(π g) = Ξ_C(g)` is Borel measurable. -/
theorem IsInvariantQuotient.measurable_of_relXi [μ.OuterRegular] (hπ : IsInvariantQuotient π μ)
    (hq : IsQuotientMap π) {C : Set G} (hC : IsCompact C) {ξ : X → ℝ}
    (hξ : ∀ g, ξ (π g) = relXi π μ C g) : Measurable ξ := by
  set s := Function.surjInv hq.surjective
  have hs : ∀ x, π (s x) = x := Function.surjInv_eq hq.surjective
  -- the volume as a function on `X`
  set V : X → ℝ≥0∞ := fun x => relVol π μ C (s x)
  have hV : V ∘ π = relVol π μ C := funext fun g => hπ.relVol_eq_of_eq C (hs (π g))
  have hVusc : UpperSemicontinuous V := by
    refine upperSemicontinuous_iff_isOpen_preimage.2 fun t => ?_
    rw [← hq.isOpen_preimage, ← preimage_comp, hV]
    exact upperSemicontinuous_iff_isOpen_preimage.1 (upperSemicontinuous_relVol hq.continuous hC) t
  have : ξ = fun x => (V x).toReal ^ (-(1 / 2 : ℝ)) := funext fun x => by
    conv_lhs => rw [← hs x]
    rw [hξ]; rfl
  rw [this]
  exact (hVusc.measurable.ennreal_toReal).pow_const _

end Measurability

/-- An invariant quotient stays invariant after composing with a homomorphism
`q : G →* Γ` (e.g. `G → G/A` followed by `G/A → H\G/A`). -/
theorem IsInvariantQuotient.comp_monoidHom {G Γ X : Type*} [Group G] [Group Γ]
    [MeasurableSpace X] {p : Γ → X} {μ : Measure X} (hp : IsInvariantQuotient p μ)
    (q : G →* Γ) : IsInvariantQuotient (p ∘ q) μ where
  descends g g' h hgg := by
    simp only [Function.comp_apply, map_mul] at hgg ⊢
    exact hp.descends _ _ _ hgg
  measure_image_mul_right A h := by
    have e : (p ∘ q) '' ((· * h) '' A) = p '' ((· * q h) '' (q '' A)) := by
      simp only [image_image, Function.comp_apply, map_mul]
    rw [e, hp.measure_image_mul_right, image_comp]

end GSpinGGP
