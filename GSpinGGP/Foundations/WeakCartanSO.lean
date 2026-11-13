/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.BasisNorm
import TauCeti.LinearAlgebra.QuadraticForm.Transvection.Basic
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.HyperbolicPair

/-!
# The orbit lemma for the weak Cartan decomposition of `SO(V₀)` relative to `SO(W)`

Let `(V, Q)` be a quadratic space over a nonarchimedean field `F` of characteristic zero, with an
orthogonal basis `b` of anisotropic vectors. Two basis vectors `b i₀`, `b i₁` with
`Q (b i₀) = ν`, `Q (b i₁) = -ν` span a hyperbolic plane with isotropic vectors
`u = b i₀ + b i₁`, `u' = b i₀ - b i₁`, and the split torus `a(λ)` of this plane scales `u` by `λ`
and `u'` by `λ⁻¹`. The orbit lemma (the analogue for orthogonal groups of Beuzart-Plessis's
Lemme 11.0.2 for unitary groups, used for Thesis Prop. 8.3.1) says that every vector `v` with
`Q v = ν`, in the span of `b i₀`, `b i₁` and further basis vectors `b j` (`j ∈ S'`, `S'`
nonempty), is moved by a *bounded* element of `SO(Q)` to `a(λ)⁻¹ (b i₀)` for some `λ` with
`0 < ‖λ‖ ≤ 1`. The element moves only the basis vectors in the span.

The proof uses Eichler transvections (`QuadraticMap.transvection`) and reflections; the bound is
in the coordinate operator norm `basisOpNorm b`, whose bounded subsets of `SO(Q)` are relatively
compact (`isCompact_specialOrthogonal_setOf_basisOpNorm_le`).

* `orbit_lemma`: the statement.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Module QuadraticMap

namespace GSpinGGP

namespace WeakCartan

variable {F : Type*} [NontriviallyNormedField F] [CharZero F]
variable {V : Type*} [AddCommGroup V] [Module F V] {n : ℕ} {b : Module.Basis (Fin n) F V}
  {Q : QuadraticForm F V}

/-! ## Bounded isometries fixing the basis vectors outside a set -/

/-- `g` is an isometry of determinant `±1`, of operator norm at most `M`, fixing `b k` for
`k ∉ S`. -/
def Good (Q : QuadraticForm F V) (b : Module.Basis (Fin n) F V) (S : Finset (Fin n)) (M : ℝ)
    (g : V ≃ₗ[F] V) : Prop :=
  g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
    (LinearEquiv.det g = 1 ∨ LinearEquiv.det g = -1) ∧
    basisOpNorm b (g : V →ₗ[F] V) ≤ M ∧ ∀ k ∉ S, g (b k) = b k

theorem Good.mul [IsUltrametricDist F] {S : Finset (Fin n)} {M M' : ℝ} {g h : V ≃ₗ[F] V}
    (hg : Good Q b S M g) (hh : Good Q b S M' h) : Good Q b S (M * M') (g * h) := by
  obtain ⟨hgO, hgd, hgM, hgS⟩ := hg
  obtain ⟨hhO, hhd, hhM, hhS⟩ := hh
  refine ⟨mul_mem hgO hhO, ?_, ?_, fun k hk => ?_⟩
  · rw [map_mul]
    rcases hgd with h1 | h1 <;> rcases hhd with h2 | h2 <;> simp [h1, h2]
  · exact (basisOpNorm_mul_le g h).trans
      (mul_le_mul hgM hhM (basisOpNorm_nonneg _) ((basisOpNorm_nonneg _).trans hgM))
  · rw [LinearEquiv.mul_apply, hhS k hk, hgS k hk]

omit [CharZero F] in
theorem Good.mono {S : Finset (Fin n)} {M M' : ℝ} {g : V ≃ₗ[F] V} (hg : Good Q b S M g)
    (h : M ≤ M') : Good Q b S M' g :=
  ⟨hg.1, hg.2.1, hg.2.2.1.trans h, hg.2.2.2⟩

omit [CharZero F] in
theorem good_one {S : Finset (Fin n)} : Good Q b S 1 1 :=
  ⟨one_mem _, Or.inl (by simp), basisOpNorm_id_le, fun _ _ => rfl⟩

/-! ## Elementary moves -/

section Moves

variable [IsUltrametricDist F] [FiniteDimensional F V] (hb : IsOrthoBasis Q b)
include hb

omit [CharZero F] in
/-- A reflection in a basis vector is bounded and moves only that basis vector. -/
theorem good_reflection {S : Finset (Fin n)} {j : Fin n} (hj : j ∈ S) :
    letI := invertibleOfNonzero (hb.apply_ne_zero j)
    Good Q b S (1 + ‖(Q (b j))⁻¹‖ * polarBound Q b)
      (TauCeti.QuadraticMap.reflection Q (b j)) := by
  let := invertibleOfNonzero (hb.apply_ne_zero j)
  have h0 : 0 ≤ ‖(Q (b j))⁻¹‖ * polarBound Q b := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q (b j), Or.inr ?_, ?_,
    fun k hk => ?_⟩
  · rw [TauCeti.QuadraticMap.det_reflection]
  · refine (basisOpNorm_le_iff (by positivity)).2 fun i => ?_
    rw [LinearEquiv.coe_coe, TauCeti.QuadraticMap.reflection_apply]
    refine (basisNorm_sub_le _ _).trans (max_le (by rw [basisNorm_basis]; exact le_add_of_nonneg_right h0) ?_)
    rw [basisNorm_smul, basisNorm_basis, mul_one, norm_mul, invOf_eq_inv]
    have := hb.norm_polar_le (b j) (b i)
    simp only [basisNorm_basis, mul_one] at this
    nlinarith [norm_nonneg (Q (b j))⁻¹, norm_nonneg (polar Q (b j) (b i))]
  · have hkj : k ≠ j := fun h => hk (h ▸ hj)
    exact TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero Q (b j)
      (hb.polar_eq_zero j k hkj.symm)

omit [FiniteDimensional F V] in
/-- An Eichler transvection `E_{u,w}` with `‖u‖ ≤ 1`, `‖w‖ ≤ R` is bounded, and fixes every basis
vector orthogonal to `u` and `w`. -/
theorem good_transvection {S : Finset (Fin n)} {u w : V} (hu : Q u = 0) (huw : polar Q u w = 0)
    (hu1 : basisNorm b u ≤ 1) {R : ℝ} (hR : 0 ≤ R) (hwR : basisNorm b w ≤ R)
    (hfix : ∀ k ∉ S, polar Q (b k) u = 0 ∧ polar Q (b k) w = 0) :
    Good Q b S (1 + polarBound Q b * R + formBound Q b * R ^ 2 * polarBound Q b)
      (QuadraticMap.transvection Q hu huw) := by
  have hcP : 0 ≤ polarBound Q b := norm_nonneg _
  have hcQ : 0 ≤ formBound Q b := norm_nonneg _
  refine ⟨QuadraticMap.transvection_mem_orthogonalGroup hu huw,
    Or.inl (QuadraticMap.det_transvection hu huw), ?_, fun k hk => ?_⟩
  · refine (basisOpNorm_le_iff (by positivity)).2 fun i => ?_
    rw [LinearEquiv.coe_coe, QuadraticMap.transvection_apply]
    have hxu := hb.norm_polar_le (b i) u
    have hxw := hb.norm_polar_le (b i) w
    have hQw := hb.norm_apply_le w
    simp only [basisNorm_basis, mul_one] at hxu hxw
    have hu0 := basisNorm_nonneg (b := b) u
    have hw0 := basisNorm_nonneg (b := b) w
    refine (basisNorm_sub_le _ _).trans (max_le ((basisNorm_sub_le _ _).trans
      (max_le ((basisNorm_add_le _ _).trans (max_le ?_ ?_)) ?_)) ?_)
    · simp only [basisNorm_basis]; nlinarith [mul_nonneg hcP hR, mul_nonneg (mul_nonneg hcQ
        (pow_nonneg hR 2)) hcP]
    · rw [basisNorm_smul]
      calc ‖polar Q (b i) u‖ * basisNorm b w ≤ (polarBound Q b * 1) * R := by
            refine mul_le_mul (hxu.trans ?_) hwR hw0 (by positivity)
            exact mul_le_mul_of_nonneg_left hu1 hcP
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hcQ (pow_nonneg hR 2)) hcP]
    · rw [basisNorm_smul]
      calc ‖polar Q (b i) w‖ * basisNorm b u ≤ (polarBound Q b * R) * 1 := by
            refine mul_le_mul (hxw.trans ?_) hu1 hu0 (by positivity)
            exact mul_le_mul_of_nonneg_left hwR hcP
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hcQ (pow_nonneg hR 2)) hcP]
    · rw [basisNorm_smul, norm_mul]
      calc ‖Q w‖ * ‖polar Q (b i) u‖ * basisNorm b u
          ≤ (formBound Q b * R ^ 2) * (polarBound Q b * 1) * 1 := by
            refine mul_le_mul (mul_le_mul (hQw.trans ?_) (hxu.trans ?_) (norm_nonneg _)
              (by positivity)) hu1 hu0 (by positivity)
            · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw0 hwR 2) hcQ
            · exact mul_le_mul_of_nonneg_left hu1 hcP
        _ ≤ _ := by nlinarith [mul_nonneg hcP hR]
  · exact QuadraticMap.transvection_apply_of_polar_eq_zero hu huw (hfix k hk).1 (hfix k hk).2

end Moves

/-! ## The orbit lemma -/

section Orbit

variable [IsUltrametricDist F] [FiniteDimensional F V] (hb : IsOrthoBasis Q b) {i₀ i₁ : Fin n} (hne : i₀ ≠ i₁) {ν : F}
  (h₀ : Q (b i₀) = ν) (h₁ : Q (b i₁) = -ν) {S' : Finset (Fin n)} (h₀S : i₀ ∉ S') (h₁S : i₁ ∉ S')

omit [CharZero F] [IsUltrametricDist F] in
theorem polar_basis_self (i : Fin n) : polar Q (b i) (b i) = 2 * Q (b i) := by
  rw [polar_self, two_nsmul, two_mul]

section Facts

include hb hne h₀ h₁

omit [IsUltrametricDist F] in
theorem pairU_isotropic : Q (b i₀ + b i₁) = 0 := by
  rw [QuadraticMap.map_add (⇑Q), h₀, h₁, hb.polar_eq_zero i₀ i₁ hne]; ring

omit [IsUltrametricDist F] in
theorem pairV_isotropic : Q (b i₀ - b i₁) = 0 := by
  rw [sub_eq_add_neg, QuadraticMap.map_add (⇑Q), QuadraticMap.map_neg, polar_neg_right, h₀, h₁,
    hb.polar_eq_zero i₀ i₁ hne]; ring

omit [IsUltrametricDist F] in
theorem polar_pairU_pairV : polar Q (b i₀ + b i₁) (b i₀ - b i₁) = 4 * ν := by
  simp only [polar_add_left, polar_sub_right, polar_basis_self, h₀, h₁,
    hb.polar_eq_zero i₀ i₁ hne, hb.polar_eq_zero i₁ i₀ hne.symm]; ring

end Facts

include hb in
omit [IsUltrametricDist F] in
theorem polar_basis_eq_zero_of_repr {y : V} {i : Fin n} (hy : b.repr y i = 0) :
    polar Q y (b i) = 0 := by
  rw [hb.polar_basis_right, hy, zero_mul]

/-- `y` lies in the span of the `b j`, `j ∈ S'`. -/
def InY (b : Module.Basis (Fin n) F V) (S' : Finset (Fin n)) (y : V) : Prop :=
  ∀ j ∉ S', b.repr y j = 0

omit [CharZero F] [IsUltrametricDist F] in
theorem InY.add {y z : V} (hy : InY b S' y) (hz : InY b S' z) : InY b S' (y + z) :=
  fun j hj => by simp [hy j hj, hz j hj]

omit [CharZero F] [IsUltrametricDist F] in
theorem InY.smul {y : V} (c : F) (hy : InY b S' y) : InY b S' (c • y) :=
  fun j hj => by simp [hy j hj]

omit [CharZero F] [IsUltrametricDist F] in
theorem inY_basis {j : Fin n} (hj : j ∈ S') : InY b S' (b j) := fun k hk => by
  have : k ≠ j := fun h => hk (h ▸ hj)
  simp [this.symm]

section Facts2

include hb h₀S h₁S

omit [IsUltrametricDist F] in
theorem polar_pairU_of_inY {y : V} (hy : InY b S' y) : polar Q y (b i₀ + b i₁) = 0 := by
  rw [polar_add_right, polar_basis_eq_zero_of_repr hb (hy _ h₀S),
    polar_basis_eq_zero_of_repr hb (hy _ h₁S), add_zero]

omit [IsUltrametricDist F] in
theorem polar_pairV_of_inY {y : V} (hy : InY b S' y) : polar Q y (b i₀ - b i₁) = 0 := by
  rw [polar_sub_right, polar_basis_eq_zero_of_repr hb (hy _ h₀S),
    polar_basis_eq_zero_of_repr hb (hy _ h₁S), sub_zero]

end Facts2

include hb in
omit [IsUltrametricDist F] in
theorem polar_of_inY_of_not_mem {y : V} (hy : InY b S' y) {k : Fin n} (hk : k ∉ S') :
    polar Q (b k) y = 0 := by
  rw [polar_comm, hb.polar_basis_right, hy k hk, zero_mul]

include hb in
omit [IsUltrametricDist F] in
theorem polar_basis_pair {k i₀ i₁ : Fin n} (hk₀ : k ≠ i₀) (hk₁ : k ≠ i₁) (s : F) :
    polar Q (b k) (b i₀ + s • b i₁) = 0 := by
  rw [polar_add_right, polar_smul_right, hb.polar_eq_zero k i₀ hk₀,
    hb.polar_eq_zero k i₁ hk₁]; simp

include hb hne h₀ h₁ h₀S h₁S in
/-- The effect of the transvection `E_{u,w}` (`u = b i₀ + b i₁`, `w ∈ Y`) on
`α u + β u' + y`. -/
theorem transvection_pairU_apply {w : V} (hw : InY b S' w)
    (hu : Q (b i₀ + b i₁) = 0) (huw : polar Q (b i₀ + b i₁) w = 0)
    (α β : F) {y : V} (hy : InY b S' y) :
    QuadraticMap.transvection Q hu huw (α • (b i₀ + b i₁) + β • (b i₀ - b i₁) + y) =
      (α - 4 * ν * β * Q w - polar Q y w) • (b i₀ + b i₁) + β • (b i₀ - b i₁) +
        (y + (4 * ν * β) • w) := by
  have e1 := polar_pairU_pairV hb hne h₀ h₁
  have e2 : polar Q (b i₀ + b i₁) (b i₀ + b i₁) = 0 := by
    rw [polar_self, pairU_isotropic hb hne h₀ h₁, smul_zero]
  have e3 := polar_pairU_of_inY hb h₀S h₁S hy
  have e4 : polar Q (b i₀ + b i₁) w = 0 := huw
  have e5 : polar Q w (b i₀ - b i₁) = 0 := polar_pairV_of_inY hb h₀S h₁S hw
  rw [QuadraticMap.transvection_apply]
  simp only [polar_add_left, polar_smul_left, smul_eq_mul, e2, e3, polar_comm Q (b i₀ - b i₁),
    e1, e4, e5]
  module

include hb hne h₀ h₁ h₀S h₁S in
/-- The effect of the transvection `E_{u',w}` (`u' = b i₀ - b i₁`, `w ∈ Y`) on
`α u + β u' + y`. -/
theorem transvection_pairV_apply {w : V} (hw : InY b S' w)
    (hv : Q (b i₀ - b i₁) = 0) (hvw : polar Q (b i₀ - b i₁) w = 0)
    (α β : F) {y : V} (hy : InY b S' y) :
    QuadraticMap.transvection Q hv hvw (α • (b i₀ + b i₁) + β • (b i₀ - b i₁) + y) =
      α • (b i₀ + b i₁) + (β - 4 * ν * α * Q w - polar Q y w) • (b i₀ - b i₁) +
        (y + (4 * ν * α) • w) := by
  have e1 := polar_pairU_pairV hb hne h₀ h₁
  have e2 : polar Q (b i₀ - b i₁) (b i₀ - b i₁) = 0 := by
    rw [polar_self, pairV_isotropic hb hne h₀ h₁, smul_zero]
  have e3 := polar_pairV_of_inY hb h₀S h₁S hy
  have e4 : polar Q (b i₀ - b i₁) w = 0 := hvw
  have e5 : polar Q (b i₀ + b i₁) w = 0 := by
    rw [polar_comm]; exact polar_pairU_of_inY hb h₀S h₁S hw
  rw [QuadraticMap.transvection_apply]
  simp only [polar_add_left, polar_smul_left, smul_eq_mul, e2, e3, e1, e4, e5]
  module

omit [CharZero F] in
theorem norm_two_le_one : ‖(2 : F)‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (1 : F) 1
  rw [one_add_one_eq_two, norm_one, max_self] at this
  exact this

omit [CharZero F] [IsUltrametricDist F] in
theorem exists_basisNorm_eq (hn : 0 < n) (y : V) :
    ∃ j, ‖b.repr y j‖ = basisNorm b y := by
  have : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => ‖b.repr y j‖) this
  exact ⟨j, le_antisymm (norm_repr_le_basisNorm y j)
    ((basisNorm_le_iff (norm_nonneg _)).2 fun k => hj k (Finset.mem_univ k))⟩

omit [CharZero F] in
theorem basisNorm_pair_le {i₀ i₁ : Fin n} (s : F) (hs : ‖s‖ ≤ 1) :
    basisNorm b (b i₀ + s • b i₁) ≤ 1 :=
  (basisNorm_add_le _ _).trans (max_le (by simp) (by simpa [basisNorm_smul] using hs))

section Stages

include hb hne h₀ h₁ h₀S h₁S

/-- The swap `u ↔ u'` (the reflection in `b i₁`) on `α u + β u' + y`. -/
theorem reflection_pair_apply (α β : F) {y : V} (hy : InY b S' y) :
    letI := invertibleOfNonzero (hb.apply_ne_zero i₁)
    TauCeti.QuadraticMap.reflection Q (b i₁) (α • (b i₀ + b i₁) + β • (b i₀ - b i₁) + y) =
      β • (b i₀ + b i₁) + α • (b i₀ - b i₁) + y := by
  let := invertibleOfNonzero (hb.apply_ne_zero i₁)
  have hν : ν ≠ 0 := fun h => hb.apply_ne_zero i₀ (h₀.trans h)
  have hc : ⅟(Q (b i₁)) * polar Q (b i₁) (α • (b i₀ + b i₁) + β • (b i₀ - b i₁) + y) =
      2 * α - 2 * β := by
    rw [invOf_eq_inv]
    simp only [polar_add_right, polar_smul_right, polar_sub_right, polar_basis_self,
      hb.polar_eq_zero i₁ i₀ hne.symm, h₁, smul_eq_mul, polar_of_inY_of_not_mem hb hy h₁S]
    field_simp
    ring
  rw [TauCeti.QuadraticMap.reflection_apply, hc]
  module

/-- **Step A.** After possibly swapping `u` and `u'`, the `u`-coordinate dominates. -/
theorem stage_swap (α β : F) {y : V} (hy : InY b S' y) :
    ∃ g, Good Q b (insert i₀ (insert i₁ S')) (1 + ‖(Q (b i₁))⁻¹‖ * polarBound Q b) g ∧
      ∃ α' β' : F, ‖β'‖ ≤ ‖α'‖ ∧
        g (α • (b i₀ + b i₁) + β • (b i₀ - b i₁) + y) =
          α' • (b i₀ + b i₁) + β' • (b i₀ - b i₁) + y := by
  by_cases h : ‖β‖ ≤ ‖α‖
  · exact ⟨1, good_one.mono (le_add_of_nonneg_right (mul_nonneg (norm_nonneg _)
      (norm_nonneg _))), α, β, h, rfl⟩
  · let := invertibleOfNonzero (hb.apply_ne_zero i₁)
    exact ⟨_, good_reflection hb (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), β, α,
      (not_le.1 h).le, reflection_pair_apply hb hne h₀ h₁ h₀S h₁S α β hy⟩

/-- **Step B.** Transfer from `Y` to the `u`-coordinate: afterwards the `u`-coordinate dominates
both the `u'`-coordinate and (up to the factor `μ`) the `Y`-component. -/
theorem stage_transfer {μ : ℝ} (hμ0 : 0 < μ) (hμν : μ * ‖4 * ν‖ ≤ ‖(2 : F)‖)
    (hμQ : ∀ j, μ ≤ ‖(2 : F)‖ * ‖Q (b j)‖) (α β : F) {y : V} (hy : InY b S' y)
    (hβα : ‖β‖ ≤ ‖α‖) :
    ∃ g, Good Q b (insert i₀ (insert i₁ S'))
        (1 + polarBound Q b * 1 + formBound Q b * 1 ^ 2 * polarBound Q b) g ∧
      ∃ (α' : F) (y' : V), InY b S' y' ∧ ‖β‖ ≤ ‖α'‖ ∧ μ * basisNorm b y' ≤ ‖α'‖ ∧
        g (α • (b i₀ + b i₁) + β • (b i₀ - b i₁) + y) =
          α' • (b i₀ + b i₁) + β • (b i₀ - b i₁) + y' := by
  have hcP : 0 ≤ polarBound Q b := norm_nonneg _
  have hcQ : 0 ≤ formBound Q b := norm_nonneg _
  by_cases h : μ * basisNorm b y ≤ ‖α‖
  · exact ⟨1, good_one.mono (by nlinarith [mul_nonneg hcQ hcP]), α, y, hy, hβα, h, rfl⟩
  rw [not_le] at h
  set N := basisNorm b y with hN
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) i₀.2
  obtain ⟨j, hj⟩ := exists_basisNorm_eq (b := b) hn y
  have hNpos : 0 < N := by
    by_contra hle
    have : N = 0 := le_antisymm (not_lt.1 hle) (basisNorm_nonneg y)
    rw [this, mul_zero] at h
    exact absurd h (not_lt.2 (norm_nonneg α))
  have hjS : j ∈ S' := by
    by_contra hjS
    rw [hy j hjS, norm_zero] at hj
    exact hNpos.ne hj
  have hu := pairU_isotropic hb hne h₀ h₁
  have huw : polar Q (b i₀ + b i₁) (b j) = 0 := by
    rw [polar_comm]; exact polar_pairU_of_inY hb h₀S h₁S (inY_basis hjS)
  have hgood := good_transvection (S := insert i₀ (insert i₁ S')) hb hu huw
    (by simpa using basisNorm_pair_le (b := b) (i₀ := i₀) (i₁ := i₁) 1 (by simp)) zero_le_one
    (by simp) (fun k hk => by
      simp only [Finset.mem_insert, not_or] at hk
      refine ⟨by simpa using polar_basis_pair hb hk.1 hk.2.1 1, ?_⟩
      exact hb.polar_eq_zero k j (fun h => hk.2.2 (h ▸ hjS)))
  -- the dominant term
  have hQj : 0 < ‖Q (b j)‖ := norm_pos_iff.2 (hb.apply_ne_zero j)
  have hpol : polar Q y (b j) = b.repr y j * (2 * Q (b j)) := by
    rw [hb.polar_basis_right, polar_basis_self]
  set D := N * (‖(2 : F)‖ * ‖Q (b j)‖) with hD
  have hpolN : ‖polar Q y (b j)‖ = D := by
    rw [hpol, norm_mul, norm_mul, hj]
  have hμD : μ * N ≤ D := by
    rw [hD, mul_comm N]
    exact mul_le_mul_of_nonneg_right (hμQ j) hNpos.le
  have hαD : ‖α‖ < D := h.trans_le hμD
  have hβD : ‖4 * ν * β * Q (b j)‖ < D := by
    rw [norm_mul, norm_mul]
    calc ‖4 * ν‖ * ‖β‖ * ‖Q (b j)‖ ≤ ‖4 * ν‖ * ‖α‖ * ‖Q (b j)‖ := by gcongr
      _ < ‖4 * ν‖ * (μ * N) * ‖Q (b j)‖ := by
          have h4 : 0 < ‖4 * ν‖ := norm_pos_iff.2 (mul_ne_zero (by norm_num)
            (fun h => hb.apply_ne_zero i₀ (h₀.trans h)))
          gcongr
      _ = μ * ‖4 * ν‖ * N * ‖Q (b j)‖ := by ring
      _ ≤ ‖(2 : F)‖ * N * ‖Q (b j)‖ := by gcongr
      _ = D := by ring
  have hβD' : ‖-(4 * ν * β * Q (b j))‖ < D := by rwa [norm_neg]
  have hrest : ‖α - 4 * ν * β * Q (b j)‖ < D := by
    rw [sub_eq_add_neg]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max α _) (max_lt hαD hβD')
  have hα' : ‖α - 4 * ν * β * Q (b j) - polar Q y (b j)‖ = D := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg, hpolN]; exact hrest.ne), norm_neg, hpolN, max_eq_right hrest.le]
  -- the new `Y`-component is no larger
  have hy' : basisNorm b (y + (4 * ν * β) • b j) ≤ N := by
    refine (basisNorm_add_le _ _).trans (max_le le_rfl ?_)
    rw [basisNorm_smul, basisNorm_basis, mul_one, norm_mul]
    calc ‖4 * ν‖ * ‖β‖ ≤ ‖4 * ν‖ * (μ * N) := by
          gcongr; exact hβα.trans h.le
      _ = μ * ‖4 * ν‖ * N := by ring
      _ ≤ ‖(2 : F)‖ * N := by gcongr
      _ ≤ 1 * N := by gcongr; exact norm_two_le_one
      _ = N := one_mul N
  have hfin : μ * basisNorm b (y + (4 * ν * β) • b j) ≤ D :=
    (mul_le_mul_of_nonneg_left hy' hμ0.le).trans hμD
  exact ⟨_, hgood, α - 4 * ν * β * Q (b j) - polar Q y (b j), y + (4 * ν * β) • b j,
    hy.add (InY.smul _ (inY_basis hjS)), by rw [hα']; exact hβα.trans hαD.le,
    by rw [hα']; exact hfin,
    transvection_pairU_apply hb hne h₀ h₁ h₀S h₁S (inY_basis hjS) hu huw α β hy⟩

end Stages

end Orbit

end WeakCartan

end GSpinGGP
