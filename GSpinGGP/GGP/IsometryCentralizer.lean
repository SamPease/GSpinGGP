/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Centralizers of a semisimple isometry with abelian Lie algebra

Let `B` be a nondegenerate symmetric bilinear form on a finite-dimensional space `V` over an
algebraically closed field of characteristic `0`, and `X` a semisimple isometry of `B`, with
fixed space `V' = ker (X − 1)`.  Let `𝔩` be the space of `B`-skew endomorphisms commuting with `X`
and vanishing on `V'`, and `S` the group of isometries of determinant `1` commuting with `X` and
fixing `V'` pointwise.

**Main result** (`commute_of_isLieAbelian`): if `𝔩` is abelian, then `S` is commutative.

Proof.  `V` is the direct sum of the eigenspaces `E_μ` of `X`, `B(E_μ, E_ν) = 0` unless `μν = 1`,
and every `h ∈ S` preserves each `E_μ`.  The skew maps `z ↦ B(w,z) u − B(u,z) w` with `u ∈ E_μ`,
`w ∈ E_{μ⁻¹}` lie in `𝔩`; as `𝔩` is abelian, `dim E_μ ≤ 1` for `μ ≠ ±1` and `dim E_{−1} ≤ 2`.
For `h ∈ S`, `h − h⁻¹ ∈ 𝔩`.  On a line `E_μ` any two maps commute.  On `E = E_{−1}` of dimension
`2`, `det (h|_E) = 1` (the lines `E_μ`, `E_{μ⁻¹}` contribute `c · c⁻¹`), so by Cayley–Hamilton
`h + h⁻¹` is a scalar on `E`, and `h = ½ tr + ½ (h − h⁻¹)` there; the `h − h⁻¹` commute. -/

noncomputable section

open Module LinearMap

namespace GSpinGGP

namespace IsomCent

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable (B : LinearMap.BilinForm K V)

/-- `B`-isometries. -/
def IsIsom (h : V →ₗ[K] V) : Prop := ∀ u v, B (h u) (h v) = B u v

/-- `B`-skew endomorphisms. -/
def IsSkew (Y : V →ₗ[K] V) : Prop := ∀ u v, B (Y u) v = - B u (Y v)

/-- The skew map `z ↦ B(w,z) u − B(u,z) w`. -/
def wedge (u w : V) : V →ₗ[K] V := (B w).smulRight u - (B u).smulRight w

theorem wedge_apply (u w z : V) : wedge B u w z = B w z • u - B u z • w := rfl

variable {B}

theorem isSkew_wedge (hB : B.IsSymm) (u w : V) : IsSkew B (wedge B u w) := by
  intro z z'
  simp only [wedge_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  have h1 := hB.eq u z'; have h2 := hB.eq w z'; have h3 := hB.eq z u; have h4 := hB.eq z w
  rw [h1, h2, ← h3, ← h4]; ring

/-- An isometry of a nondegenerate form is injective. -/
theorem IsIsom.injective (hnd : B.Nondegenerate) {h : V →ₗ[K] V} (hh : IsIsom B h) :
    Function.Injective h := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  refine hnd.1 z fun v => ?_
  rw [← hh z v, hz, map_zero, LinearMap.zero_apply]

/-! ## Eigenspaces of an isometry -/

section Eigen

variable {X : Module.End K V}

open Module.End

/-- `B(E_μ, E_ν) = 0` unless `μν = 1`. -/
theorem bform_eigen_eq_zero (hX : IsIsom B X) {μ ν : K} (hμν : μ * ν ≠ 1) {u v : V}
    (hu : u ∈ X.eigenspace μ) (hv : v ∈ X.eigenspace ν) : B u v = 0 := by
  rw [mem_eigenspace_iff] at hu hv
  have h := hX u v
  rw [hu, hv, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h
  have : (1 - ν * μ) * B u v = 0 := by rw [sub_mul, one_mul, h, sub_self]
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd (by rw [mul_comm]; linear_combination -h0) hμν
  · exact h0

/-- `B(w, Xz) = μ B(w, z)` for `w ∈ E_{μ'}`, `μ μ' = 1`. -/
theorem bform_eigen_X (hX : IsIsom B X) {μ μ' : K} (h1 : μ * μ' = 1) {w : V}
    (hw : w ∈ X.eigenspace μ') (z : V) : B w (X z) = μ * B w z := by
  rw [mem_eigenspace_iff] at hw
  have hμ' : μ' ≠ 0 := right_ne_zero_of_mul_eq_one h1
  have hw' : w = X (μ'⁻¹ • w) := by rw [map_smul, hw, smul_smul, inv_mul_cancel₀ hμ', one_smul]
  conv_lhs => rw [hw']
  rw [hX, map_smul, LinearMap.smul_apply, smul_eq_mul]
  congr 1
  calc μ'⁻¹ = μ * μ' * μ'⁻¹ := by rw [h1, one_mul]
    _ = μ := by rw [mul_assoc, mul_inv_cancel₀ hμ', mul_one]

/-- The wedge of `u ∈ E_μ` and `w ∈ E_{μ'}`, `μμ' = 1`, commutes with `X`. -/
theorem commute_wedge (hB : B.IsSymm) (hX : IsIsom B X) {μ μ' : K} (h1 : μ * μ' = 1) {u w : V}
    (hu : u ∈ X.eigenspace μ) (hw : w ∈ X.eigenspace μ') : Commute X (wedge B u w) := by
  have h1' : μ' * μ = 1 := by rw [mul_comm, h1]
  ext z
  simp only [Module.End.mul_apply, wedge_apply, map_sub, map_smul]
  rw [bform_eigen_X hX h1 hw, bform_eigen_X hX h1' hu, (mem_eigenspace_iff.1 hu),
    (mem_eigenspace_iff.1 hw), smul_smul, smul_smul, mul_comm μ, mul_comm μ']

/-- The wedge of `u ∈ E_μ`, `w ∈ E_{μ'}` with `μ, μ' ≠ 1` kills the fixed space. -/
theorem wedge_eq_zero_of_fixed (hX : IsIsom B X) {μ μ' : K} (hμ : μ ≠ 1) (hμ' : μ' ≠ 1) {u w : V}
    (hu : u ∈ X.eigenspace μ) (hw : w ∈ X.eigenspace μ') {z : V} (hz : z ∈ X.eigenspace 1) :
    wedge B u w z = 0 := by
  rw [wedge_apply, bform_eigen_eq_zero hX (by simpa using hμ') hw hz,
    bform_eigen_eq_zero hX (by simpa using hμ) hu hz, zero_smul, zero_smul, sub_zero]

variable [IsAlgClosed K] [FiniteDimensional K V]

/-- Pairing: for `u ∈ E_μ`, every value `B u v` is attained on `E_{μ⁻¹}`. -/
theorem exists_eigen_pair (hX : IsIsom B X) (hss : X.IsSemisimple) {μ : K} {u : V}
    (hu : u ∈ X.eigenspace μ) (v : V) : ∃ w ∈ X.eigenspace μ⁻¹, B u w = B u v := by
  have hv : v ∈ ⨆ ν : K, X.eigenspace ν := by rw [hss.iSup_eigenspace_eq_top]; trivial
  induction hv using Submodule.iSup_induction' with
  | mem ν y hy =>
    by_cases hν : μ * ν = 1
    · refine ⟨y, ?_, rfl⟩
      rwa [show μ⁻¹ = ν from (eq_inv_of_mul_eq_one_right hν).symm]
    · exact ⟨0, Submodule.zero_mem _, by rw [map_zero, bform_eigen_eq_zero hX hν hu hy]⟩
  | zero => exact ⟨0, Submodule.zero_mem _, rfl⟩
  | add y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨w₁, hw₁, e₁⟩ := h₁
    obtain ⟨w₂, hw₂, e₂⟩ := h₂
    exact ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, by rw [map_add, map_add, e₁, e₂]⟩

end Eigen

/-! ## Multiplicities -/

section Mult

variable {X : Module.End K V}

open Module.End

/-- `𝔩` is abelian: skew endomorphisms commuting with `X` and vanishing on `V'` commute. -/
def LieAbelian (B : LinearMap.BilinForm K V) (X : Module.End K V) : Prop :=
  ∀ Y₁ Y₂ : Module.End K V, IsSkew B Y₁ → IsSkew B Y₂ → Commute X Y₁ → Commute X Y₂ →
    (∀ z ∈ X.eigenspace 1, Y₁ z = 0) → (∀ z ∈ X.eigenspace 1, Y₂ z = 0) → Commute Y₁ Y₂

theorem exists_pair_of_one_lt_finrank (E : Submodule K V) (h : 1 < finrank K E) :
    ∃ x ∈ E, ∃ y ∈ E, ∀ s t : K, s • x + t • y = 0 → s = 0 ∧ t = 0 := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := K) (lt_trans zero_lt_one h)
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  obtain ⟨y, hy⟩ := exists_linearIndependent_pair_of_one_lt_finrank h hx
  refine ⟨x, x.2, y, y.2, fun s t hst => (LinearIndependent.pair_iff.1 hy) s t ?_⟩
  exact Subtype.ext (by simpa using hst)

variable [IsAlgClosed K] [FiniteDimensional K V]

/-- A nonzero `u ∈ E_μ` pairs nontrivially with `E_{μ⁻¹}`. -/
theorem exists_eigen_pair_ne_zero (hnd : B.Nondegenerate) (hX : IsIsom B X)
    (hss : X.IsSemisimple) {μ : K} {u : V} (hu : u ∈ X.eigenspace μ) (hu0 : u ≠ 0) :
    ∃ w ∈ X.eigenspace μ⁻¹, B u w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hu0 (hnd.1 u fun v => ?_)
  obtain ⟨w, hw, e⟩ := exists_eigen_pair hX hss hu v
  rw [← e, hcon w hw]

/-- **`dim E_μ ≤ 1` for `μ ≠ ±1`** when `𝔩` is abelian. -/
theorem finrank_eigenspace_le_one (hB : B.IsSymm) (hnd : B.Nondegenerate) (hX : IsIsom B X)
    (hss : X.IsSemisimple) (hL : LieAbelian B X) {μ : K} (hμ1 : μ ≠ 1) (hμ2 : μ * μ ≠ 1) :
    finrank K (X.eigenspace μ) ≤ 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u₁, hu₁, u₂, hu₂, hind⟩ := exists_pair_of_one_lt_finrank _ hcon
  have hne : ∀ u : V, u = u₁ ∨ u = u₂ → u ≠ 0 := by
    rintro u (rfl | rfl) rfl
    · exact one_ne_zero (hind 1 0 (by simp)).1
    · exact one_ne_zero (hind 0 1 (by simp)).2
  obtain ⟨w₁, hw₁, hB₁⟩ := exists_eigen_pair_ne_zero hnd hX hss hu₁ (hne _ (Or.inl rfl))
  obtain ⟨w₂, hw₂, hB₂⟩ := exists_eigen_pair_ne_zero hnd hX hss hu₂ (hne _ (Or.inr rfl))
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    refine hne u₁ (Or.inl rfl) (IsIsom.injective hnd hX ?_)
    rw [mem_eigenspace_iff.1 hu₁, zero_smul, map_zero]
  have h1 : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ0
  have hμ'1 : μ⁻¹ ≠ 1 := by rwa [ne_eq, inv_eq_one]
  have h22 : B u₂ u₁ = 0 := bform_eigen_eq_zero hX hμ2 hu₂ hu₁
  have h11 : B u₁ u₁ = 0 := bform_eigen_eq_zero hX hμ2 hu₁ hu₁
  have h12 : B u₁ u₂ = 0 := bform_eigen_eq_zero hX hμ2 hu₁ hu₂
  have hc := hL (wedge B u₁ w₂) (wedge B u₂ w₁) (isSkew_wedge hB _ _) (isSkew_wedge hB _ _)
    (commute_wedge hB hX h1 hu₁ hw₂) (commute_wedge hB hX h1 hu₂ hw₁)
    (fun z hz => wedge_eq_zero_of_fixed hX hμ1 hμ'1 hu₁ hw₂ hz)
    (fun z hz => wedge_eq_zero_of_fixed hX hμ1 hμ'1 hu₂ hw₁ hz)
  have hz := congrArg (fun f : Module.End K V => f u₁) hc.eq
  simp only [Module.End.mul_apply, wedge_apply, map_sub, map_smul, h22, h11, h12, zero_smul,
    sub_zero, smul_zero] at hz
  -- `B(w₁,u₁) (B(w₂,u₂) u₁ − B(w₂,u₁) u₂) = 0`
  have hw1 : B w₁ u₁ ≠ 0 := fun h => hB₁ (by rw [hB.eq u₁ w₁]; exact h)
  have hw2 : B w₂ u₂ ≠ 0 := fun h => hB₂ (by rw [hB.eq u₂ w₂]; exact h)
  have key : (B w₁ u₁ * B w₂ u₂) • u₁ + (-(B w₂ u₁ * B w₁ u₁)) • u₂ = 0 := by
    rw [neg_smul, ← sub_eq_add_neg, sub_eq_zero]
    simpa [smul_smul, mul_comm] using hz
  exact mul_ne_zero hw1 hw2 (hind _ _ key).1

/-- An anisotropic vector in `E_{−1}` if it is nonzero (characteristic `0`). -/
theorem exists_anisotropic_neg_one [CharZero K] (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (hX : IsIsom B X) (hss : X.IsSemisimple) {e : V} (he : e ∈ X.eigenspace (-1)) (he0 : e ≠ 0) :
    ∃ v ∈ X.eigenspace (-1), B v v ≠ 0 := by
  obtain ⟨e', he', hee'⟩ := exists_eigen_pair_ne_zero hnd hX hss he he0
  rw [inv_neg, inv_one] at he'
  by_cases h1 : B e e = 0
  · by_cases h2 : B e' e' = 0
    · refine ⟨e + e', Submodule.add_mem _ he he', ?_⟩
      have hs := hB.eq e' e
      simp only [map_add, LinearMap.add_apply, h1, h2, zero_add, add_zero]
      rw [hs, ← two_mul]
      exact mul_ne_zero two_ne_zero hee'
    · exact ⟨e', he', h2⟩
  · exact ⟨e, he, h1⟩

/-- **`dim E_{−1} ≤ 2`** when `𝔩` is abelian. -/
theorem finrank_eigenspace_neg_one_le_two [CharZero K] (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (hX : IsIsom B X) (hss : X.IsSemisimple) (hL : LieAbelian B X) :
    finrank K (X.eigenspace (-1)) ≤ 2 := by
  by_contra hcon
  push Not at hcon
  set E := X.eigenspace (-1) with hE
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  obtain ⟨v, hv, hvv⟩ := exists_anisotropic_neg_one hB hnd hX hss e.2
    (fun h => he (Subtype.ext h))
  -- the kernel of `B v` on `E` has dimension `≥ 2`
  let f : E →ₗ[K] K := (B v).domRestrict E
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  have hr : finrank K (LinearMap.range f) ≤ 1 := by
    simpa using Submodule.finrank_le (LinearMap.range f)
  obtain ⟨x, hx, y, hy, hind⟩ := exists_pair_of_one_lt_finrank (V := E) (LinearMap.ker f)
    (by omega)
  set u : V := (x : V)
  set w : V := (y : V)
  have hBvu : B v u = 0 := hx
  have hBvw : B v w = 0 := hy
  have hBuv : B u v = 0 := by rw [hB.eq]; exact hBvu
  have hBwv : B w v = 0 := by rw [hB.eq]; exact hBvw
  have hBwu : B w u = B u w := hB.eq w u
  have hw0 : w ≠ 0 := by
    intro h0
    have := (hind 0 1 (by rw [zero_smul, one_smul, zero_add]; exact Subtype.ext h0)).2
    exact one_ne_zero this
  obtain ⟨z, hz⟩ : ∃ z, B w z ≠ 0 := by
    by_contra h; push Not at h; exact hw0 (hnd.1 w h)
  have hm : (-1 : K) * -1 = 1 := by norm_num
  have h1 : (-1 : K) ≠ 1 := by norm_num
  have hc := hL (wedge B u v) (wedge B v w) (isSkew_wedge hB _ _) (isSkew_wedge hB _ _)
    (commute_wedge hB hX hm x.2 hv) (commute_wedge hB hX hm hv y.2)
    (fun z hz => wedge_eq_zero_of_fixed hX h1 h1 x.2 hv hz)
    (fun z hz => wedge_eq_zero_of_fixed hX h1 h1 hv y.2 hz)
  have hzz := congrArg (fun F : Module.End K V => F z) hc.eq
  simp only [Module.End.mul_apply, wedge_apply, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hBvu, hBvw, hBuv, hBwv, hBwu, mul_zero, zero_smul,
    sub_zero, zero_sub, smul_neg, neg_neg] at hzz
  have key : (B v v * B w z) • x + (-(B v v * B u z)) • y = 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero]
    rw [neg_smul, ← sub_eq_add_neg, sub_eq_zero]
    rw [sub_neg_eq_add, sub_neg_eq_add, add_comm, add_left_cancel_iff] at hzz
    rw [mul_smul, mul_smul, smul_comm (B v v) (B w z), smul_comm (B v v) (B u z)]
    exact hzz
  exact mul_ne_zero hvv hz (hind _ _ key).1

end Mult

end IsomCent

end GSpinGGP
