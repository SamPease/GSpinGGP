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
and `u'` by `λ⁻¹`. The orbit lemma (the analogue for orthogonal groups of Lemme 11.0.2 in §11 of
Beuzart-Plessis's thèse, proved there for unitary groups; used for Thesis Prop. 8.3.1) says
that every vector `v` with `Q v = ν`, in the span of `b i₀`, `b i₁` and further basis vectors `b j` (`j ∈ S'`, `S'`
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

variable [IsUltrametricDist F] (hb : IsOrthoBasis Q b)
include hb

omit [CharZero F] hb in
theorem norm_two_le_one : ‖(2 : F)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_natCast_le_one F 2

omit [CharZero F] in
/-- A reflection in a basis vector is bounded and moves only that basis vector. -/
theorem good_reflection [FiniteDimensional F V] {S : Finset (Fin n)} {j : Fin n} (hj : j ∈ S) :
    letI := invertibleOfNonzero (hb.apply_ne_zero j)
    Good Q b S 1 (TauCeti.QuadraticMap.reflection Q (b j)) := by
  let := invertibleOfNonzero (hb.apply_ne_zero j)
  refine ⟨TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q (b j), Or.inr ?_, ?_,
    fun k hk => ?_⟩
  · rw [TauCeti.QuadraticMap.det_reflection]
  · refine (basisOpNorm_le_iff zero_le_one).2 fun i => ?_
    rw [LinearEquiv.coe_coe, QuadraticMap.reflection_basis_apply Q b hb.isOrtho]
    refine (basisNorm_sub_le _ _).trans (max_le (by rw [basisNorm_basis]) ?_)
    rw [basisNorm_smul, basisNorm_basis, mul_one, norm_mul]
    have := (norm_repr_le_basisNorm (b := b) (b i) j).trans (basisNorm_basis i).le
    nlinarith [norm_two_le_one (F := F), norm_nonneg (2 : F), norm_nonneg (b.repr (b i) j)]
  · have hkj : k ≠ j := fun h => hk (h ▸ hj)
    exact TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero Q (b j)
      (hb.polar_eq_zero j k hkj.symm)

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

variable [IsUltrametricDist F] (hb : IsOrthoBasis Q b) {i₀ i₁ : Fin n} (hne : i₀ ≠ i₁) {ν : F}
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
  rw [polar_comm, QuadraticMap.polar_basis_left Q b hb.isOrtho, hy, mul_zero]

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
  rw [QuadraticMap.polar_basis_left Q b hb.isOrtho, hy k hk, mul_zero]

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
  rw [QuadraticMap.reflection_basis_apply Q b hb.isOrtho]
  simp [hne, hy i₁ h₁S]
  module

/-- **Step A.** After possibly swapping `u` and `u'`, the `u`-coordinate dominates. -/
theorem stage_swap [FiniteDimensional F V] (α β : F) {y : V} (hy : InY b S' y) :
    ∃ g, Good Q b (insert i₀ (insert i₁ S')) 1 g ∧
      ∃ α' β' : F, ‖β'‖ ≤ ‖α'‖ ∧
        g (α • (b i₀ + b i₁) + β • (b i₀ - b i₁) + y) =
          α' • (b i₀ + b i₁) + β' • (b i₀ - b i₁) + y := by
  by_cases h : ‖β‖ ≤ ‖α‖
  · exact ⟨1, good_one, α, β, h, rfl⟩
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
    rw [polar_comm, QuadraticMap.polar_basis_left Q b hb.isOrtho, mul_comm]
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

/-- **Step C.** Clear the `Y`-component with the transvection `E_{u', w}`,
`w = -(4να)⁻¹ y`. -/
theorem stage_clear {μ : ℝ} (hμ0 : 0 < μ) (α β : F) (hα : α ≠ 0) {y : V} (hy : InY b S' y)
    (hμy : μ * basisNorm b y ≤ ‖α‖) :
    ∃ g, Good Q b (insert i₀ (insert i₁ S'))
        (1 + polarBound Q b * (μ * ‖4 * ν‖)⁻¹ +
          formBound Q b * ((μ * ‖4 * ν‖)⁻¹) ^ 2 * polarBound Q b) g ∧
      ∃ β' : F, g (α • (b i₀ + b i₁) + β • (b i₀ - b i₁) + y) =
          α • (b i₀ + b i₁) + β' • (b i₀ - b i₁) := by
  have hν : ν ≠ 0 := fun h => hb.apply_ne_zero i₀ (h₀.trans h)
  have h4ν : (4 * ν : F) ≠ 0 := mul_ne_zero (by norm_num) hν
  set w : V := -(4 * ν * α)⁻¹ • y with hw
  have hwY : InY b S' w := InY.smul _ hy
  have hv := pairV_isotropic hb hne h₀ h₁
  have hvw : polar Q (b i₀ - b i₁) w = 0 := by
    rw [polar_comm]; exact polar_pairV_of_inY hb h₀S h₁S hwY
  have hR : 0 ≤ (μ * ‖4 * ν‖)⁻¹ := by positivity
  have hwR : basisNorm b w ≤ (μ * ‖4 * ν‖)⁻¹ := by
    rw [hw, basisNorm_smul, norm_neg, norm_inv, norm_mul]
    have hα0 : 0 < ‖α‖ := norm_pos_iff.2 hα
    have h40 : 0 < ‖4 * ν‖ := norm_pos_iff.2 h4ν
    rw [inv_mul_le_iff₀ (by positivity), mul_inv]
    calc basisNorm b y ≤ ‖α‖ * μ⁻¹ := by
          rw [le_mul_inv_iff₀ hμ0]; linarith [mul_comm μ (basisNorm b y)]
      _ = ‖4 * ν‖ * ‖α‖ * (μ⁻¹ * ‖4 * ν‖⁻¹) := by field_simp
  have hpair := basisNorm_pair_le (b := b) (i₀ := i₀) (i₁ := i₁) (-1) (by simp)
  have hgood := good_transvection (S := insert i₀ (insert i₁ S')) hb hv hvw
    (by simpa [sub_eq_add_neg] using hpair) hR hwR (fun k hk => by
      simp only [Finset.mem_insert, not_or] at hk
      exact ⟨by simpa [sub_eq_add_neg] using polar_basis_pair hb hk.1 hk.2.1 (-1),
        polar_of_inY_of_not_mem hb hwY hk.2.2⟩)
  refine ⟨_, hgood, β - 4 * ν * α * Q w - polar Q y w, ?_⟩
  rw [transvection_pairV_apply hb hne h₀ h₁ h₀S h₁S hwY hv hvw α β hy]
  have : y + (4 * ν * α) • w = 0 := by
    rw [hw, smul_smul, mul_neg, mul_inv_cancel₀ (mul_ne_zero h4ν hα), neg_smul, one_smul,
      add_neg_cancel]
  rw [this, add_zero]

/-- The value of `Q` on `α u + β u' + y` with `y ∈ Y`. -/
theorem apply_pair_add (α β : F) {y : V} (hy : InY b S' y) :
    Q (α • (b i₀ + b i₁) + β • (b i₀ - b i₁) + y) = 4 * ν * α * β + Q y := by
  rw [QuadraticMap.map_add (⇑Q), QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul,
    QuadraticMap.map_smul, pairU_isotropic hb hne h₀ h₁, pairV_isotropic hb hne h₀ h₁,
    polar_smul_left, polar_smul_right, polar_pairU_pairV hb hne h₀ h₁, polar_add_left,
    polar_smul_left, polar_smul_left, polar_comm Q _ y, polar_comm Q _ y,
    polar_pairU_of_inY hb h₀S h₁S hy, polar_pairV_of_inY hb h₀S h₁S hy]
  simp only [smul_eq_mul]
  ring

end Stages

omit [CharZero F] [IsUltrametricDist F] in
/-- The normal form `a u + c u'` with `4ac = 1` and `‖c‖ ≤ ‖a‖` is
`(2t)⁻¹ u + (t/2) u'` with `0 < ‖t‖ ≤ 1`. -/
theorem exists_param [CharZero F] {a c : F} (hac : 4 * a * c = 1) (hca : ‖c‖ ≤ ‖a‖) :
    ∃ t : F, t ≠ 0 ∧ ‖t‖ ≤ 1 ∧ a = (2 * t)⁻¹ ∧ c = t / 2 := by
  have ha : a ≠ 0 := by rintro rfl; simp at hac
  refine ⟨(2 * a)⁻¹, inv_ne_zero (mul_ne_zero two_ne_zero ha), ?_, by field_simp, ?_⟩
  · rw [norm_inv, inv_le_one₀ (norm_pos_iff.2 (mul_ne_zero two_ne_zero ha))]
    have h1 : ‖(4 : F) * a * c‖ = 1 := by rw [hac, norm_one]
    have h2 : (1 : ℝ) ≤ ‖(2 : F) * a‖ ^ 2 := by
      calc (1 : ℝ) = ‖(4 : F)‖ * ‖a‖ * ‖c‖ := by rw [← h1, norm_mul, norm_mul]
        _ ≤ ‖(4 : F)‖ * ‖a‖ * ‖a‖ := by gcongr
        _ = ‖(2 : F) * a‖ ^ 2 := by
          rw [norm_mul, show (4 : F) = 2 * 2 by norm_num, norm_mul]; ring
    nlinarith [norm_nonneg ((2 : F) * a)]
  · field_simp
    linear_combination hac

section Assembly

include hb hne h₀ h₁ h₀S h₁S

omit [IsUltrametricDist F] in
/-- Every vector supported on `{i₀, i₁} ∪ S'` is `α u + β u' + y` with `y ∈ Y`. -/
theorem exists_pair_decomp {v : V} (hv : ∀ j, j ≠ i₀ → j ≠ i₁ → j ∉ S' → b.repr v j = 0) :
    ∃ (α β : F) (y : V), InY b S' y ∧ v = α • (b i₀ + b i₁) + β • (b i₀ - b i₁) + y := by
  refine ⟨(b.repr v i₀ + b.repr v i₁) / 2, (b.repr v i₀ - b.repr v i₁) / 2,
    v - ((b.repr v i₀ + b.repr v i₁) / 2) • (b i₀ + b i₁) -
      ((b.repr v i₀ - b.repr v i₁) / 2) • (b i₀ - b i₁), fun j hj => ?_, by abel⟩
  by_cases hj₀ : j = i₀
  · subst hj₀
    simp [hne]
    ring
  by_cases hj₁ : j = i₁
  · subst hj₁
    simp [hne.symm]
    ring
  simp [Ne.symm hj₀, Ne.symm hj₁, hv j hj₀ hj₁ hj]

/-- The orbit lemma before fixing the determinant: an isometry of determinant `±1`. -/
theorem orbit_core [FiniteDimensional F V] :
    ∃ M, ∀ v : V, (∀ j, j ≠ i₀ → j ≠ i₁ → j ∉ S' → b.repr v j = 0) → Q v = ν →
      ∃ g, Good Q b (insert i₀ (insert i₁ S')) M g ∧ ∃ t : F, t ≠ 0 ∧ ‖t‖ ≤ 1 ∧
        g v = (2 * t)⁻¹ • (b i₀ + b i₁) + (t / 2) • (b i₀ - b i₁) := by
  have hν : ν ≠ 0 := fun h => hb.apply_ne_zero i₀ (h₀.trans h)
  have h4ν : 0 < ‖4 * ν‖ := norm_pos_iff.2 (mul_ne_zero (by norm_num) hν)
  set qi : ℝ := ‖fun j => (Q (b j))⁻¹‖ with hqi
  have hqi0 : 0 ≤ qi := norm_nonneg _
  set μ : ℝ := ‖(2 : F)‖ / (‖4 * ν‖ + qi) with hμ
  have h20 : 0 < ‖(2 : F)‖ := norm_pos_iff.2 two_ne_zero
  have hμ0 : 0 < μ := div_pos h20 (by positivity)
  have hμν : μ * ‖4 * ν‖ ≤ ‖(2 : F)‖ := by
    rw [hμ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hμQ : ∀ j, μ ≤ ‖(2 : F)‖ * ‖Q (b j)‖ := by
    intro j
    have hQj : 0 < ‖Q (b j)‖ := norm_pos_iff.2 (hb.apply_ne_zero j)
    have hinv : ‖Q (b j)‖⁻¹ ≤ qi := by
      have := norm_le_pi_norm (fun j => (Q (b j))⁻¹) j
      rwa [norm_inv] at this
    rw [hμ, div_le_iff₀ (by positivity)]
    have : 1 ≤ ‖Q (b j)‖ * (‖4 * ν‖ + qi) := by
      have := mul_le_mul_of_nonneg_left hinv hQj.le
      rw [mul_inv_cancel₀ hQj.ne'] at this
      nlinarith
    nlinarith
  set Mσ : ℝ := 1
  set MB := 1 + polarBound Q b * 1 + formBound Q b * 1 ^ 2 * polarBound Q b
  set MC := 1 + polarBound Q b * (μ * ‖4 * ν‖)⁻¹ +
    formBound Q b * ((μ * ‖4 * ν‖)⁻¹) ^ 2 * polarBound Q b
  refine ⟨Mσ * (MC * (MB * Mσ)), fun v hv hQv => ?_⟩
  obtain ⟨α, β, y, hy, rfl⟩ := exists_pair_decomp hb hne h₀ h₁ h₀S h₁S hv
  obtain ⟨g₁, hg₁, α₁, β₁, h₁', e₁⟩ := stage_swap hb hne h₀ h₁ h₀S h₁S α β hy
  obtain ⟨g₂, hg₂, α₂, y₂, hy₂, h₂a, h₂b, e₂⟩ :=
    stage_transfer hb hne h₀ h₁ h₀S h₁S hμ0 hμν hμQ α₁ β₁ hy h₁'
  have hQ₂ : Q (α₂ • (b i₀ + b i₁) + β₁ • (b i₀ - b i₁) + y₂) = ν := by
    rw [← e₂, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hg₂.1, ← e₁,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hg₁.1, hQv]
  have hα₂ : α₂ ≠ 0 := by
    rintro rfl
    have hβ₁ : β₁ = 0 := norm_le_zero_iff.1 (by simpa using h₂a)
    have hy₂0 : y₂ = 0 := by
      have : basisNorm b y₂ ≤ 0 := by
        have := h₂b; rw [norm_zero] at this
        exact nonpos_of_mul_nonpos_right this hμ0
      exact basisNorm_eq_zero.1 (le_antisymm this (basisNorm_nonneg _))
    rw [hβ₁, hy₂0] at hQ₂
    simp at hQ₂
    exact hν hQ₂.symm
  obtain ⟨g₃, hg₃, β₃, e₃⟩ := stage_clear hb hne h₀ h₁ h₀S h₁S hμ0 α₂ β₁ hα₂ hy₂ h₂b
  have hQ₃ : 4 * α₂ * β₃ = 1 := by
    have h := hQ₂
    rw [← TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hg₃.1, e₃,
      show α₂ • (b i₀ + b i₁) + β₃ • (b i₀ - b i₁) =
        α₂ • (b i₀ + b i₁) + β₃ • (b i₀ - b i₁) + (0 : V) by rw [add_zero],
      apply_pair_add hb hne h₀ h₁ h₀S h₁S α₂ β₃ (fun _ _ => by simp), map_zero,
      add_zero] at h
    have : ν * (4 * α₂ * β₃) = ν * 1 := by linear_combination h
    exact mul_left_cancel₀ hν this
  have hMσ : 1 ≤ Mσ := le_rfl
  have hfinal : ∃ g₄, Good Q b (insert i₀ (insert i₁ S')) Mσ g₄ ∧ ∃ t : F, t ≠ 0 ∧
      ‖t‖ ≤ 1 ∧ g₄ (α₂ • (b i₀ + b i₁) + β₃ • (b i₀ - b i₁)) =
        (2 * t)⁻¹ • (b i₀ + b i₁) + (t / 2) • (b i₀ - b i₁) := by
    by_cases hc : ‖β₃‖ ≤ ‖α₂‖
    · obtain ⟨t, ht0, ht1, ha, hc'⟩ := exists_param hQ₃ hc
      exact ⟨1, good_one.mono hMσ, t, ht0, ht1, by rw [ha, hc']; rfl⟩
    · have hQ₃' : 4 * β₃ * α₂ = 1 := by rw [← hQ₃]; ring
      obtain ⟨t, ht0, ht1, ha, hc'⟩ := exists_param hQ₃' (not_le.1 hc).le
      let := invertibleOfNonzero (hb.apply_ne_zero i₁)
      refine ⟨_, good_reflection hb (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)),
        t, ht0, ht1, ?_⟩
      have := reflection_pair_apply hb hne h₀ h₁ h₀S h₁S α₂ β₃ (y := 0) (fun _ _ => by simp)
      simp only [add_zero] at this
      rw [this, ha, hc']
  obtain ⟨g₄, hg₄, t, ht0, ht1, e₄⟩ := hfinal
  refine ⟨g₄ * (g₃ * (g₂ * g₁)), hg₄.mul (hg₃.mul (hg₂.mul hg₁)), t, ht0, ht1, ?_⟩
  simp only [LinearEquiv.mul_apply]
  rw [e₁, e₂, e₃, e₄]

/-- **The orbit lemma** (used for Thesis Prop. 8.3.1; the orthogonal analogue of Lemme 11.0.2 in
§11 of Beuzart-Plessis's thèse). Let `b` be an orthogonal basis of anisotropic vectors, `i₀ ≠ i₁`
with `Q (b i₀) = ν`, `Q (b i₁) = -ν`, and `S'` a nonempty set of further indices. There is `M`
such that every `v` supported on `{i₀, i₁} ∪ S'` with `Q v = ν` is moved by some `g ∈ SO(Q)`
of operator norm at most `M`, fixing the basis vectors outside `{i₀, i₁} ∪ S'`, to
`(2t)⁻¹ u + (t/2) u'` (`u = b i₀ + b i₁`, `u' = b i₀ - b i₁`) with `0 < ‖t‖ ≤ 1`. This vector is
the image of `b i₀ = (u + u')/2` under the inverse of the torus element `u ↦ t u`,
`u' ↦ t⁻¹ u'`. -/
theorem orbit_lemma [FiniteDimensional F V] (hS' : S'.Nonempty) :
    ∃ M, ∀ v : V, (∀ j, j ≠ i₀ → j ≠ i₁ → j ∉ S' → b.repr v j = 0) → Q v = ν →
      ∃ g ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q,
        basisOpNorm b (g : V →ₗ[F] V) ≤ M ∧
        (∀ k, k ≠ i₀ → k ≠ i₁ → k ∉ S' → g (b k) = b k) ∧
        ∃ t : F, t ≠ 0 ∧ ‖t‖ ≤ 1 ∧
          g v = (2 * t)⁻¹ • (b i₀ + b i₁) + (t / 2) • (b i₀ - b i₁) := by
  obtain ⟨j₂, hj₂⟩ := hS'
  obtain ⟨M, hM⟩ := orbit_core hb hne h₀ h₁ h₀S h₁S
  set Mρ : ℝ := 1
  have hMρ : 1 ≤ Mρ := le_rfl
  refine ⟨Mρ * M, fun v hv hQv => ?_⟩
  obtain ⟨g, hg, t, ht0, ht1, e⟩ := hM v hv hQv
  have hS : ∀ k, k ≠ i₀ → k ≠ i₁ → k ∉ S' → k ∉ insert i₀ (insert i₁ S') := by
    intro k h0 h1 h2; simp [h0, h1, h2]
  have hM0 : 0 ≤ M := (basisOpNorm_nonneg _).trans hg.2.2.1
  rcases hg.2.1 with hdet | hdet
  · exact ⟨g, TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff.2 ⟨hg.1, hdet⟩,
      hg.2.2.1.trans (le_mul_of_one_le_left hM0 hMρ),
      fun k h0 h1 h2 => hg.2.2.2 k (hS k h0 h1 h2), t, ht0, ht1, e⟩
  · let := invertibleOfNonzero (hb.apply_ne_zero j₂)
    have hρ := good_reflection hb (S := insert i₀ (insert i₁ S')) (j := j₂)
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hj₂))
    have hgρ := hρ.mul hg
    have hj₂0 : j₂ ≠ i₀ := fun h => h₀S (h ▸ hj₂)
    have hj₂1 : j₂ ≠ i₁ := fun h => h₁S (h ▸ hj₂)
    refine ⟨_, TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff.2 ⟨hgρ.1, ?_⟩, hgρ.2.2.1,
      fun k h0 h1 h2 => hgρ.2.2.2 k (hS k h0 h1 h2), t, ht0, ht1, ?_⟩
    · rw [map_mul, hdet, TauCeti.QuadraticMap.det_reflection]; simp
    · rw [LinearEquiv.mul_apply, e]
      refine TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero Q (b j₂) ?_
      rw [polar_add_right, polar_smul_right, polar_smul_right,
        show b i₀ - b i₁ = b i₀ + (-1 : F) • b i₁ by simp [sub_eq_add_neg],
        polar_basis_pair hb hj₂0 hj₂1, show b i₀ + b i₁ = b i₀ + (1 : F) • b i₁ by simp,
        polar_basis_pair hb hj₂0 hj₂1]
      simp

end Assembly

end Orbit

end WeakCartan

end GSpinGGP
