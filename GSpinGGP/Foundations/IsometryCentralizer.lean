/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import TauCeti.LinearAlgebra.Matrix.Block

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

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {B : M →ₗ[R] M →ₗ[R] N} {f : Module.End R M}

/-- Skew-adjointness, unfolded: `B (f u) v = - B u (f v)`. -/
theorem isSkewAdjoint_iff : B.IsSkewAdjoint f ↔ ∀ u v, B (f u) v = -B u (f v) := by
  simp only [IsSkewAdjoint, IsAdjointPair, Pi.neg_apply, map_neg]

theorem IsSkewAdjoint.eq (h : B.IsSkewAdjoint f) (u v : M) : B (f u) v = -B u (f v) :=
  isSkewAdjoint_iff.1 h u v

end LinearMap

open Module LinearMap

namespace GSpinGGP

namespace IsomCent

/-- `B`-isometries. -/
def IsIsom {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (B : LinearMap.BilinForm R M) (h : M →ₗ[R] M) : Prop :=
  ∀ u v, B (h u) (h v) = B u v

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable (B : LinearMap.BilinForm K V)

/-- The skew map `z ↦ B(w,z) u − B(u,z) w`. -/
def wedge (u w : V) : V →ₗ[K] V := (B w).smulRight u - (B u).smulRight w

theorem wedge_apply (u w z : V) : wedge B u w z = B w z • u - B u z • w := rfl

variable {B}

theorem isSkewAdjoint_wedge (hB : B.IsSymm) (u w : V) : B.IsSkewAdjoint (wedge B u w) := by
  refine LinearMap.isSkewAdjoint_iff.2 fun z z' => ?_
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
  ∀ Y₁ Y₂ : Module.End K V, B.IsSkewAdjoint Y₁ → B.IsSkewAdjoint Y₂ → Commute X Y₁ →
    Commute X Y₂ → (∀ z ∈ X.eigenspace 1, Y₁ z = 0) → (∀ z ∈ X.eigenspace 1, Y₂ z = 0) →
    Commute Y₁ Y₂

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
  have hc := hL (wedge B u₁ w₂) (wedge B u₂ w₁) (isSkewAdjoint_wedge hB _ _)
    (isSkewAdjoint_wedge hB _ _)
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
  have hc := hL (wedge B u v) (wedge B v w) (isSkewAdjoint_wedge hB _ _)
    (isSkewAdjoint_wedge hB _ _)
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

/-! ## The eigenspace decomposition and determinants -/

section Decomp

/-- The determinant of an endomorphism preserving an internal direct sum decomposition is the
product of the determinants of its restrictions. -/
theorem det_eq_prod_det_restrict [FiniteDimensional K V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → Submodule K V} (hN : DirectSum.IsInternal N) (f : Module.End K V)
    (hf : ∀ i, Set.MapsTo f (N i) (N i)) :
    LinearMap.det f = ∏ i, LinearMap.det (f.restrict (hf i)) := by
  classical
  let b : (i : ι) → Basis _ K (N i) := fun i => Module.Free.chooseBasis K (N i)
  rw [← LinearMap.det_toMatrix (hN.collectedBasis b),
    LinearMap.toMatrix_directSum_collectedBasis_eq_blockDiagonal' hN hN b b hf,
    Matrix.det_blockDiagonal']
  simp_rw [LinearMap.det_toMatrix]

variable {X : Module.End K V}

open Module.End

/-- Over an algebraically closed field, `V` is the internal direct sum of the eigenspaces of a
semisimple `X`. -/
theorem isInternal_eigenspace [DecidableEq K] [IsAlgClosed K] [FiniteDimensional K V] (hss : X.IsSemisimple) :
    DirectSum.IsInternal (fun μ : X.Eigenvalues => X.eigenspace (μ : K)) := by
  classical
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨X.eigenspaces_iSupIndep.comp Subtype.val_injective, ?_⟩
  refine eq_top_iff.2 ?_
  rw [← hss.iSup_eigenspace_eq_top]
  refine iSup_le fun μ => ?_
  by_cases h : X.HasEigenvalue μ
  · exact le_iSup_of_le (⟨μ, h⟩ : X.Eigenvalues) le_rfl
  · rw [hasEigenvalue_iff, not_not] at h
    rw [h]; exact bot_le

end Decomp

/-! ## The group `S` -/

section Group

variable {X : Module.End K V}

open Module.End

theorem mapsTo_eigenspace_of_commute {h : Module.End K V} (hc : Commute X h) (μ : K) :
    ∀ v ∈ X.eigenspace μ, h v ∈ X.eigenspace μ := by
  intro v hv
  rw [mem_eigenspace_iff] at hv ⊢
  rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hv, map_smul]

/-- Endomorphisms of a space of dimension `≤ 1` commute. -/
theorem commute_of_finrank_le_one {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (h1 : finrank K E ≤ 1) (f g : Module.End K E) : Commute f g := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h0 | h1
  · have : Subsingleton E := Module.finrank_zero_iff.1 h0
    exact LinearMap.ext fun x => Subsingleton.elim _ _
  · obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h1 f
    rw [hc]
    exact (Commute.one_left g).smul_left c

/-- Cayley–Hamilton in dimension `2`. -/
theorem sq_sub_trace_add_det {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (h2 : finrank K E = 2) (f : Module.End K E) :
    f ^ 2 - LinearMap.trace K E f • f + LinearMap.det f • (1 : Module.End K E) = 0 := by
  let b := Module.finBasisOfFinrankEq K E h2
  have hc : f.charpoly = Polynomial.X ^ 2 - Polynomial.C (LinearMap.trace K E f) * Polynomial.X +
      Polynomial.C (LinearMap.det f) := by
    rw [← LinearMap.charpoly_toMatrix f b, Matrix.charpoly_fin_two,
      LinearMap.trace_eq_matrix_trace K b, LinearMap.det_toMatrix]
  have := LinearMap.aeval_self_charpoly f
  rw [hc] at this
  simpa [Algebra.smul_def] using this

variable [IsAlgClosed K] [FiniteDimensional K V]

theorem hasEigenvalue_inv (hnd : B.Nondegenerate) (hX : IsIsom B X) (hss : X.IsSemisimple)
    {μ : K} (hμ : X.HasEigenvalue μ) : X.HasEigenvalue μ⁻¹ := by
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hasEigenvalue_iff.1 hμ)
  obtain ⟨w, hw, hBw⟩ := exists_eigen_pair_ne_zero hnd hX hss hu hu0
  refine hasEigenvalue_iff.2 fun hbot => hBw ?_
  rw [hbot, Submodule.mem_bot] at hw
  rw [hw, map_zero]

/-- On a line `E_μ` (`μ ≠ ±1`) and its partner `E_{μ⁻¹}`, `h` acts by `c` and `c⁻¹`. -/
theorem det_restrict_mul_inv [CharZero K] (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (hX : IsIsom B X) (hss : X.IsSemisimple) (hL : LieAbelian B X) {h : Module.End K V}
    (hi : IsIsom B h) (hc : Commute X h) (hfix : ∀ z ∈ X.eigenspace 1, h z = z) {μ : K}
    (hμ : X.HasEigenvalue μ) (hμm : μ ≠ -1) :
    LinearMap.det (h.restrict (mapsTo_eigenspace_of_commute hc μ)) *
      LinearMap.det (h.restrict (mapsTo_eigenspace_of_commute hc μ⁻¹)) = 1 := by
  by_cases hμ1 : μ = 1
  · subst hμ1
    have hid : h.restrict (mapsTo_eigenspace_of_commute hc 1) = LinearMap.id :=
      LinearMap.ext fun v => Subtype.ext (hfix v v.2)
    have hid' : h.restrict (mapsTo_eigenspace_of_commute hc (1 : K)⁻¹) = LinearMap.id :=
      LinearMap.ext fun v => Subtype.ext (hfix v (by simpa using v.2))
    rw [hid, hid', LinearMap.det_id, LinearMap.det_id, one_mul]
  have hμ2 : μ * μ ≠ 1 := by
    intro h2
    have : (μ - 1) * (μ + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 this with h0 | h0
    · exact hμ1 (by linear_combination h0)
    · exact hμm (by linear_combination h0)
  have hμ' : X.HasEigenvalue μ⁻¹ := hasEigenvalue_inv hnd hX hss hμ
  have hμ'1 : μ⁻¹ ≠ 1 := by rwa [ne_eq, inv_eq_one]
  have hμ'2 : μ⁻¹ * μ⁻¹ ≠ 1 := by
    rw [← mul_inv]; intro h; exact hμ2 (inv_eq_one.1 h)
  have hr : ∀ ν : K, X.HasEigenvalue ν → ν ≠ 1 → ν * ν ≠ 1 → finrank K (X.eigenspace ν) = 1 := by
    intro ν hν h1 h2
    have hle := finrank_eigenspace_le_one hB hnd hX hss hL h1 h2
    have hpos : 0 < finrank K (X.eigenspace ν) :=
      Nat.pos_of_ne_zero fun h0 => (hasEigenvalue_iff.1 hν) (Submodule.finrank_eq_zero.1 h0)
    omega
  obtain ⟨c, hc1, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
    (hr μ hμ hμ1 hμ2) (h.restrict (mapsTo_eigenspace_of_commute hc μ))
  obtain ⟨c', hc2, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
    (hr μ⁻¹ hμ' hμ'1 hμ'2) (h.restrict (mapsTo_eigenspace_of_commute hc μ⁻¹))
  rw [hc1, hc2, LinearMap.det_smul, LinearMap.det_smul, LinearMap.det_id, LinearMap.det_id,
    hr μ hμ hμ1 hμ2, hr μ⁻¹ hμ' hμ'1 hμ'2, pow_one, pow_one, mul_one, mul_one]
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hasEigenvalue_iff.1 hμ)
  obtain ⟨w, hw, hBw⟩ := exists_eigen_pair_ne_zero hnd hX hss hu hu0
  have hhu : h u = c • u := by
    have := LinearMap.congr_fun hc1 ⟨u, hu⟩
    rw [Subtype.ext_iff, LinearMap.coe_restrict_apply] at this
    simpa using this
  have hhw : h w = c' • w := by
    have := LinearMap.congr_fun hc2 ⟨w, hw⟩
    rw [Subtype.ext_iff, LinearMap.coe_restrict_apply] at this
    simpa using this
  have := hi u w
  rw [hhu, hhw, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
    ← mul_assoc] at this
  have h0 : (c * c' - 1) * B u w = 0 := by linear_combination this
  rcases mul_eq_zero.1 h0 with h0 | h0
  · linear_combination h0
  · exact absurd h0 hBw

theorem ne_zero_of_hasEigenvalue (hnd : B.Nondegenerate) (hX : IsIsom B X) {μ : K}
    (hμ : X.HasEigenvalue μ) : μ ≠ 0 := by
  rintro rfl
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hasEigenvalue_iff.1 hμ)
  refine hu0 (IsIsom.injective hnd hX ?_)
  rw [mem_eigenspace_iff.1 hu, zero_smul, map_zero]

/-- **`det (h|_{E_{−1}}) = 1`** for `h ∈ S`: the other eigenspaces pair off as `E_μ, E_{μ⁻¹}`
with determinants `c, c⁻¹`, or are `E_1`, where `h = 1`. -/
theorem det_restrict_neg_one [CharZero K] (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (hX : IsIsom B X) (hss : X.IsSemisimple) (hL : LieAbelian B X) {h : Module.End K V}
    (hi : IsIsom B h) (hd : LinearMap.det h = 1) (hc : Commute X h)
    (hfix : ∀ z ∈ X.eigenspace 1, h z = z) :
    LinearMap.det (h.restrict (mapsTo_eigenspace_of_commute hc (-1))) = 1 := by
  classical
  by_cases hm : X.HasEigenvalue (-1)
  swap
  · have hbot : X.eigenspace (-1) = ⊥ := by rwa [hasEigenvalue_iff, not_not] at hm
    have h0 : finrank K (X.eigenspace (-1)) = 0 := by rw [hbot, finrank_bot]
    exact LinearMap.det_eq_one_of_finrank_eq_zero h0 _
  let f : X.Eigenvalues → K := fun μ =>
    LinearMap.det (h.restrict (mapsTo_eigenspace_of_commute hc (μ : K)))
  have hprod : LinearMap.det h = ∏ μ, f μ :=
    det_eq_prod_det_restrict (isInternal_eigenspace hss) h
      (fun μ => mapsTo_eigenspace_of_commute hc (μ : K))
  let m : X.Eigenvalues := ⟨-1, hm⟩
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ m)] at hprod
  have hne : ∀ μ ∈ Finset.univ.erase m, (μ : K) ≠ -1 := by
    intro μ hμ heq
    exact (Finset.mem_erase.1 hμ).1 (Subtype.ext heq)
  have hrest : ∏ μ ∈ Finset.univ.erase m, f μ = 1 := by
    refine Finset.prod_involution
      (fun μ _ => (⟨(μ : K)⁻¹, hasEigenvalue_inv hnd hX hss μ.2⟩ : X.Eigenvalues)) ?_ ?_ ?_ ?_
    · intro μ hμ
      exact det_restrict_mul_inv hB hnd hX hss hL hi hc hfix μ.2 (hne μ hμ)
    · intro μ hμ hf heq
      have hinv : (μ : K)⁻¹ = μ := congrArg Subtype.val heq
      have h0 := ne_zero_of_hasEigenvalue hnd hX μ.2
      have hsq : ((μ : K) - 1) * ((μ : K) + 1) = 0 := by
        have : (μ : K) * (μ : K) = 1 := by
          calc (μ : K) * μ = μ * (μ : K)⁻¹ := by rw [hinv]
            _ = 1 := mul_inv_cancel₀ h0
        linear_combination this
      rcases mul_eq_zero.1 hsq with h1 | h1
      · apply hf
        have hμ1 : (μ : K) = 1 := by linear_combination h1
        have hid : h.restrict (mapsTo_eigenspace_of_commute hc (μ : K)) = LinearMap.id :=
          LinearMap.ext fun v => Subtype.ext (hfix v (by rw [← hμ1]; exact v.2))
        show LinearMap.det (h.restrict (mapsTo_eigenspace_of_commute hc (μ : K))) = 1
        rw [hid, LinearMap.det_id]
      · exact hne μ hμ (by linear_combination h1)
    · intro μ hμ
      refine Finset.mem_erase.2 ⟨fun heq => hne μ hμ ?_, Finset.mem_univ _⟩
      have : (μ : K)⁻¹ = -1 := congrArg Subtype.val heq
      rw [← inv_inv (μ : K), this, inv_neg, inv_one]
    · intro μ hμ
      exact Subtype.ext (inv_inv _)
  rw [hrest, mul_one, hd] at hprod
  exact hprod.symm

/-- The inverse of an isometry `h ∈ S`, and `h − h⁻¹ ∈ 𝔩`. -/
theorem exists_inv_mem_lie (hnd : B.Nondegenerate) (hX : IsIsom B X) {h : Module.End K V}
    (hi : IsIsom B h) (hc : Commute X h) (hfix : ∀ z ∈ X.eigenspace 1, h z = z) :
    ∃ g : Module.End K V, (∀ v, h (g v) = v) ∧ (∀ v, g (h v) = v) ∧
      B.IsSkewAdjoint ⇑(h - g) ∧ Commute X (h - g) ∧ ∀ z ∈ X.eigenspace 1, (h - g) z = 0 := by
  let e := LinearEquiv.ofInjectiveEndo h (IsIsom.injective hnd hi)
  let g : Module.End K V := e.symm
  have hhg : ∀ v, h (g v) = v := fun v => e.apply_symm_apply v
  have hgh : ∀ v, g (h v) = v := fun v => e.symm_apply_apply v
  refine ⟨g, hhg, hgh, ?_, ?_, ?_⟩
  · refine LinearMap.isSkewAdjoint_iff.2 fun u v => ?_
    simp only [LinearMap.sub_apply, map_sub, LinearMap.sub_apply]
    have e1 : B (h u) v = B u (g v) := by conv_lhs => rw [← hhg v]; exact hi u (g v)
    have e2 : B (g u) v = B u (h v) := by rw [← hi (g u) v, hhg]
    rw [e1, e2]; ring
  · have hXg : Commute X g := by
      refine LinearMap.ext fun v => ?_
      apply IsIsom.injective hnd hi
      simp only [Module.End.mul_apply]
      rw [hhg, ← Module.End.mul_apply h X, ← hc.eq, Module.End.mul_apply, hhg]
    exact hc.sub_right hXg
  · intro z hz
    have : g z = z := by conv_lhs => rw [← hfix z hz]; exact hgh z
    rw [LinearMap.sub_apply, hfix z hz, this, sub_self]

/-- **Main result.**  If `𝔩` is abelian, the isometries of determinant `1` commuting with `X` and
fixing `ker (X − 1)` pointwise commute with each other. -/
theorem commute_of_lieAbelian [CharZero K] (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (hX : IsIsom B X) (hss : X.IsSemisimple) (hL : LieAbelian B X) {h₁ h₂ : Module.End K V}
    (hi₁ : IsIsom B h₁) (hi₂ : IsIsom B h₂) (hd₁ : LinearMap.det h₁ = 1)
    (hd₂ : LinearMap.det h₂ = 1) (hc₁ : Commute X h₁) (hc₂ : Commute X h₂)
    (hf₁ : ∀ z ∈ X.eigenspace 1, h₁ z = z) (hf₂ : ∀ z ∈ X.eigenspace 1, h₂ z = z) :
    Commute h₁ h₂ := by
  refine LinearMap.ext fun v => ?_
  simp only [Module.End.mul_apply]
  have hv : v ∈ ⨆ μ : K, X.eigenspace μ := by rw [hss.iSup_eigenspace_eq_top]; trivial
  induction hv using Submodule.iSup_induction' with
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | mem μ v hv =>
    -- restrictions to `E_μ`
    let r₁ := h₁.restrict (mapsTo_eigenspace_of_commute hc₁ μ)
    let r₂ := h₂.restrict (mapsTo_eigenspace_of_commute hc₂ μ)
    have hrest : Commute r₁ r₂ → h₁ (h₂ v) = h₂ (h₁ v) := by
      intro hr
      have := LinearMap.congr_fun hr.eq ⟨v, hv⟩
      rw [Subtype.ext_iff] at this
      simpa [r₁, r₂, Module.End.mul_apply, LinearMap.coe_restrict_apply] using this
    by_cases hμ1 : μ = 1
    · subst hμ1
      rw [hf₂ v hv, hf₁ v hv, hf₂ v hv]
    by_cases hμm : μ = -1
    swap
    · have hμ2 : μ * μ ≠ 1 := by
        intro h2
        have : (μ - 1) * (μ + 1) = 0 := by linear_combination h2
        rcases mul_eq_zero.1 this with h0 | h0
        · exact hμ1 (by linear_combination h0)
        · exact hμm (by linear_combination h0)
      exact hrest (commute_of_finrank_le_one
        (finrank_eigenspace_le_one hB hnd hX hss hL hμ1 hμ2) r₁ r₂)
    subst hμm
    have hle := finrank_eigenspace_neg_one_le_two hB hnd hX hss hL
    by_cases h2 : finrank K (X.eigenspace (-1)) ≤ 1
    · exact hrest (commute_of_finrank_le_one h2 r₁ r₂)
    have h2 : finrank K (X.eigenspace (-1)) = 2 := by omega
    obtain ⟨g₁, hhg₁, hgh₁, hs₁, hcY₁, hz₁⟩ := exists_inv_mem_lie hnd hX hi₁ hc₁ hf₁
    obtain ⟨g₂, hhg₂, hgh₂, hs₂, hcY₂, hz₂⟩ := exists_inv_mem_lie hnd hX hi₂ hc₂ hf₂
    have hY := (hL _ _ hs₁ hs₂ hcY₁ hcY₂ hz₁ hz₂).eq
    -- on `E_{−1}`: `g w = t w − h w` (Cayley–Hamilton, `det = 1`)
    have hinv : ∀ {h g : Module.End K V} (hc : Commute X h), (∀ v, g (h v) = v) →
        LinearMap.det (h.restrict (mapsTo_eigenspace_of_commute hc (-1))) = 1 →
        ∀ w ∈ X.eigenspace (-1), g w =
          LinearMap.trace K _ (h.restrict (mapsTo_eigenspace_of_commute hc (-1))) • w - h w := by
      intro h g hc hgh hdet w hw
      have hCH := sq_sub_trace_add_det h2 (h.restrict (mapsTo_eigenspace_of_commute hc (-1)))
      rw [hdet, one_smul] at hCH
      have := LinearMap.congr_fun hCH ⟨w, hw⟩
      rw [Subtype.ext_iff] at this
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, pow_two,
        Module.End.mul_apply, LinearMap.coe_restrict_apply, Submodule.coe_add, Submodule.coe_sub,
        Submodule.coe_smul, Module.End.one_apply, LinearMap.zero_apply,
        Submodule.coe_zero] at this
      -- `h (h w) − t h w + w = 0`; apply `g`
      have := congrArg g this
      rw [map_add, map_sub, hgh, map_smul, hgh, map_zero] at this
      linear_combination (norm := module) this
    have hd₁' := det_restrict_neg_one hB hnd hX hss hL hi₁ hd₁ hc₁ hf₁
    have hd₂' := det_restrict_neg_one hB hnd hX hss hL hi₂ hd₂ hc₂ hf₂
    set t₁ := LinearMap.trace K _ (h₁.restrict (mapsTo_eigenspace_of_commute hc₁ (-1)))
    set t₂ := LinearMap.trace K _ (h₂.restrict (mapsTo_eigenspace_of_commute hc₂ (-1)))
    have hm₁ := mapsTo_eigenspace_of_commute hc₁ (-1)
    have hm₂ := mapsTo_eigenspace_of_commute hc₂ (-1)
    have a1 := hinv hc₁ hgh₁ hd₁' v hv
    have a2 := hinv hc₂ hgh₂ hd₂' v hv
    have a3 := hinv hc₁ hgh₁ hd₁' _ (hm₂ v hv)
    have a4 := hinv hc₂ hgh₂ hd₂' _ (hm₁ v hv)
    have eq := LinearMap.congr_fun hY v
    simp only [Module.End.mul_apply, LinearMap.sub_apply, map_sub, map_smul, a1, a2, a3,
      a4] at eq
    linear_combination (norm := module) (1 / 4 : K) • eq

/-- An isometry commuting with `X` has a two-sided inverse commuting with `X`. -/
theorem exists_inv_of_isIsom (hnd : B.Nondegenerate) {h : Module.End K V} (hi : IsIsom B h)
    (hc : Commute X h) :
    ∃ g : Module.End K V, (∀ v, h (g v) = v) ∧ (∀ v, g (h v) = v) ∧ Commute X g ∧
      ∀ u v, B (h u) v = B u (g v) := by
  let e := LinearEquiv.ofInjectiveEndo h (IsIsom.injective hnd hi)
  let g : Module.End K V := e.symm
  have hhg : ∀ v, h (g v) = v := fun v => e.apply_symm_apply v
  have hgh : ∀ v, g (h v) = v := fun v => e.symm_apply_apply v
  refine ⟨g, hhg, hgh, ?_, fun u v => ?_⟩
  · refine LinearMap.ext fun v => ?_
    apply IsIsom.injective hnd hi
    simp only [Module.End.mul_apply]
    rw [hhg, ← Module.End.mul_apply h X, ← hc.eq, Module.End.mul_apply, hhg]
  · conv_lhs => rw [← hhg v]
    exact hi u (g v)

/-- `(h − h⁻¹)(2 − X − X⁻¹) ∈ 𝔩` for an isometry `h` commuting with `X`, with
`2 − X − X⁻¹ = 4` on `E₋₁`. -/
theorem exists_mem_lie_of_commute (hnd : B.Nondegenerate)
    (hX : IsIsom B X) {h : Module.End K V} (hi : IsIsom B h) (hc : Commute X h) :
    ∃ g S : Module.End K V, (∀ v, h (g v) = v) ∧ (∀ v, g (h v) = v) ∧
      B.IsSkewAdjoint ⇑((h - g) * S) ∧ Commute X ((h - g) * S) ∧
      (∀ z ∈ X.eigenspace 1, ((h - g) * S) z = 0) ∧
      (∀ w ∈ X.eigenspace (-1), S w = (4 : K) • w) ∧
      ∀ w, S (X w) = X (S w) := by
  obtain ⟨g, hhg, hgh, hXg, hBg⟩ := exists_inv_of_isIsom hnd hi hc
  obtain ⟨gX, hXgX, hgXX, hXgX', hBgX⟩ := exists_inv_of_isIsom hnd hX (Commute.refl X)
  set S : Module.End K V := (2 : K) • 1 - X - gX with hS
  -- `S` is self-adjoint and commutes with `X`, `h`, `g`
  have hSadj : ∀ u v, B (S u) v = B u (S v) := by
    intro u v
    have e1 : B (X u) v = B u (gX v) := hBgX u v
    have e2 : B (gX u) v = B u (X v) := by rw [← hX (gX u) v, hXgX]
    simp only [hS, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
      map_smul, LinearMap.sub_apply, LinearMap.smul_apply, e1, e2]
    ring
  have hXgXc : Commute X gX := hXgX'
  have hgXh : Commute gX h := by
    refine LinearMap.ext fun v => ?_
    apply IsIsom.injective hnd hX
    simp only [Module.End.mul_apply]
    rw [hXgX, ← Module.End.mul_apply X h, hc.eq, Module.End.mul_apply, hXgX]
  have hgXg : Commute gX g := by
    refine LinearMap.ext fun v => ?_
    apply IsIsom.injective hnd hX
    simp only [Module.End.mul_apply]
    rw [hXgX, ← Module.End.mul_apply X g, hXg.eq, Module.End.mul_apply, hXgX]
  have hSh : Commute S h :=
    (((Commute.one_left h).smul_left (2 : K)).sub_left hc).sub_left hgXh
  have hSg : Commute S g :=
    (((Commute.one_left g).smul_left (2 : K)).sub_left hXg).sub_left hgXg
  have hSX : Commute S X :=
    (((Commute.one_left X).smul_left (2 : K)).sub_left (Commute.refl X)).sub_left hXgX'.symm
  have hAS : Commute (h - g) S := (hSh.sub_right hSg).symm
  have hAskew : ∀ u v, B ((h - g) u) v = - B u ((h - g) v) := by
    intro u v
    have e2 : B (g u) v = B u (h v) := by rw [← hi (g u) v, hhg]
    simp only [LinearMap.sub_apply, map_sub, LinearMap.sub_apply, hBg, e2]
    ring
  have hgX1 : ∀ z ∈ X.eigenspace 1, gX z = z := by
    intro z hz
    rw [Module.End.mem_eigenspace_iff, one_smul] at hz
    conv_lhs => rw [← hz]
    exact hgXX z
  have hgXm : ∀ w ∈ X.eigenspace (-1), gX w = -w := by
    intro w hw
    rw [Module.End.mem_eigenspace_iff, neg_one_smul] at hw
    have := hgXX w
    rw [hw, map_neg] at this
    rw [← neg_neg (gX w), this]
  refine ⟨g, S, hhg, hgh, LinearMap.isSkewAdjoint_iff.2 fun u v => ?_,
    ((hc.sub_right hXg).mul_right hSX.symm), fun z hz => ?_,
    fun w hw => ?_, fun w => ?_⟩
  · rw [Module.End.mul_apply, hAskew, hSadj, ← Module.End.mul_apply S, ← hAS.eq]
  · have : S z = 0 := by
      rw [Module.End.mem_eigenspace_iff, one_smul] at hz
      simp only [hS, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hz,
        hgX1 z (by rw [Module.End.mem_eigenspace_iff, one_smul]; exact hz)]
      module
    rw [Module.End.mul_apply, this, map_zero]
  · have hw' := hw
    rw [Module.End.mem_eigenspace_iff, neg_one_smul] at hw'
    simp only [hS, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hw',
      hgXm w hw]
    module
  · rw [← Module.End.mul_apply, hSX.eq, Module.End.mul_apply]


/-- **Variant of `commute_of_lieAbelian`**: only `h₁` need fix `ker (X − 1)`; for `h₂` it suffices that
`det h₂|_{E₋₁} = 1`. -/
theorem commute_of_lieAbelian_of_det [CharZero K] (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (hX : IsIsom B X) (hss : X.IsSemisimple) (hL : LieAbelian B X) {h₁ h₂ : Module.End K V}
    (hi₁ : IsIsom B h₁) (hi₂ : IsIsom B h₂) (hd₁ : LinearMap.det h₁ = 1)
    (hc₁ : Commute X h₁) (hc₂ : Commute X h₂)
    (hf₁ : ∀ z ∈ X.eigenspace 1, h₁ z = z)
    (hd₂' : LinearMap.det (h₂.restrict (mapsTo_eigenspace_of_commute hc₂ (-1))) = 1) :
    Commute h₁ h₂ := by
  refine LinearMap.ext fun v => ?_
  simp only [Module.End.mul_apply]
  have hv : v ∈ ⨆ μ : K, X.eigenspace μ := by rw [hss.iSup_eigenspace_eq_top]; trivial
  induction hv using Submodule.iSup_induction' with
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | mem μ v hv =>
    -- restrictions to `E_μ`
    let r₁ := h₁.restrict (mapsTo_eigenspace_of_commute hc₁ μ)
    let r₂ := h₂.restrict (mapsTo_eigenspace_of_commute hc₂ μ)
    have hrest : Commute r₁ r₂ → h₁ (h₂ v) = h₂ (h₁ v) := by
      intro hr
      have := LinearMap.congr_fun hr.eq ⟨v, hv⟩
      rw [Subtype.ext_iff] at this
      simpa [r₁, r₂, Module.End.mul_apply, LinearMap.coe_restrict_apply] using this
    by_cases hμ1 : μ = 1
    · subst hμ1
      rw [hf₁ v hv, hf₁ _ (mapsTo_eigenspace_of_commute hc₂ 1 v hv)]
    by_cases hμm : μ = -1
    swap
    · have hμ2 : μ * μ ≠ 1 := by
        intro h2
        have : (μ - 1) * (μ + 1) = 0 := by linear_combination h2
        rcases mul_eq_zero.1 this with h0 | h0
        · exact hμ1 (by linear_combination h0)
        · exact hμm (by linear_combination h0)
      exact hrest (commute_of_finrank_le_one
        (finrank_eigenspace_le_one hB hnd hX hss hL hμ1 hμ2) r₁ r₂)
    subst hμm
    have hle := finrank_eigenspace_neg_one_le_two hB hnd hX hss hL
    by_cases h2 : finrank K (X.eigenspace (-1)) ≤ 1
    · exact hrest (commute_of_finrank_le_one h2 r₁ r₂)
    have h2 : finrank K (X.eigenspace (-1)) = 2 := by omega
    obtain ⟨g₁, hhg₁, hgh₁, hs₁, hcY₁, hz₁⟩ := exists_inv_mem_lie hnd hX hi₁ hc₁ hf₁
    obtain ⟨g₂, S, hhg₂, hgh₂, hs₂, hcY₂, hz₂, hS4, -⟩ := exists_mem_lie_of_commute hnd hX hi₂ hc₂
    have hY := (hL _ _ hs₁ hs₂ hcY₁ hcY₂ hz₁ hz₂).eq
    -- on `E_{−1}`: `g w = t w − h w` (Cayley–Hamilton, `det = 1`)
    have hinv : ∀ {h g : Module.End K V} (hc : Commute X h), (∀ v, g (h v) = v) →
        LinearMap.det (h.restrict (mapsTo_eigenspace_of_commute hc (-1))) = 1 →
        ∀ w ∈ X.eigenspace (-1), g w =
          LinearMap.trace K _ (h.restrict (mapsTo_eigenspace_of_commute hc (-1))) • w - h w := by
      intro h g hc hgh hdet w hw
      have hCH := sq_sub_trace_add_det h2 (h.restrict (mapsTo_eigenspace_of_commute hc (-1)))
      rw [hdet, one_smul] at hCH
      have := LinearMap.congr_fun hCH ⟨w, hw⟩
      rw [Subtype.ext_iff] at this
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, pow_two,
        Module.End.mul_apply, LinearMap.coe_restrict_apply, Submodule.coe_add, Submodule.coe_sub,
        Submodule.coe_smul, Module.End.one_apply, LinearMap.zero_apply,
        Submodule.coe_zero] at this
      -- `h (h w) − t h w + w = 0`; apply `g`
      have := congrArg g this
      rw [map_add, map_sub, hgh, map_smul, hgh, map_zero] at this
      linear_combination (norm := module) this
    have hd₁' := det_restrict_neg_one hB hnd hX hss hL hi₁ hd₁ hc₁ hf₁
    set t₁ := LinearMap.trace K _ (h₁.restrict (mapsTo_eigenspace_of_commute hc₁ (-1)))
    set t₂ := LinearMap.trace K _ (h₂.restrict (mapsTo_eigenspace_of_commute hc₂ (-1)))
    have hm₁ := mapsTo_eigenspace_of_commute hc₁ (-1)
    have hm₂ := mapsTo_eigenspace_of_commute hc₂ (-1)
    have a1 := hinv hc₁ hgh₁ hd₁' v hv
    have a2 := hinv hc₂ hgh₂ hd₂' v hv
    have a3 := hinv hc₁ hgh₁ hd₁' _ (hm₂ v hv)
    have a4 := hinv hc₂ hgh₂ hd₂' _ (hm₁ v hv)
    have hg₁v : g₁ v ∈ X.eigenspace (-1) := by
      rw [a1]; exact sub_mem (Submodule.smul_mem _ _ hv) (hm₁ v hv)
    have eq := LinearMap.congr_fun hY v
    simp only [Module.End.mul_apply, LinearMap.sub_apply] at eq
    rw [hS4 v hv, hS4 _ (sub_mem (hm₁ v hv) hg₁v)] at eq
    simp only [map_sub, map_smul, LinearMap.sub_apply, a1, a2, a3, a4] at eq
    linear_combination (norm := module) (1 / 16 : K) • eq

/-- `LieAbelian` is invariant under isometric isomorphisms conjugating the operators. -/
theorem LieAbelian.of_equiv {V₁ : Type*} [AddCommGroup V₁] [Module K V₁]
    {B₁ : LinearMap.BilinForm K V₁} {X₁ : Module.End K V₁} (e : V₁ ≃ₗ[K] V)
    (hB : ∀ u v, B (e u) (e v) = B₁ u v) (hX : ∀ v, X (e v) = e (X₁ v))
    (hL : LieAbelian B₁ X₁) : LieAbelian B X := by
  intro Y₁ Y₂ hs₁ hs₂ hc₁ hc₂ hf₁ hf₂
  let c : Module.End K V → Module.End K V₁ := fun Y => e.symm.toLinearMap ∘ₗ Y ∘ₗ e.toLinearMap
  have hcY : ∀ Y : Module.End K V, B.IsSkewAdjoint Y → B₁.IsSkewAdjoint (c Y) := by
    intro Y hY
    refine LinearMap.isSkewAdjoint_iff.2 fun u v => ?_
    simp only [c, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← hB, ← hB, e.apply_symm_apply, e.apply_symm_apply, hY.eq]
  have hcc : ∀ Y : Module.End K V, Commute X Y → Commute X₁ (c Y) := by
    intro Y hY
    refine LinearMap.ext fun v => ?_
    simp only [c, Module.End.mul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    apply e.injective
    rw [e.apply_symm_apply, ← hX, e.apply_symm_apply, ← Module.End.mul_apply X Y, hY.eq,
      Module.End.mul_apply, hX]
  have hcf : ∀ Y : Module.End K V, (∀ z ∈ X.eigenspace 1, Y z = 0) →
      ∀ z ∈ X₁.eigenspace 1, c Y z = 0 := by
    intro Y hY z hz
    simp only [c, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hY (e z) (by
      rw [Module.End.mem_eigenspace_iff, one_smul] at hz ⊢
      rw [hX, hz]), map_zero]
  have h := (hL _ _ (hcY _ hs₁) (hcY _ hs₂) (hcc _ hc₁) (hcc _ hc₂) (hcf _ hf₁) (hcf _ hf₂)).eq
  refine LinearMap.ext fun v => ?_
  have := LinearMap.congr_fun h (e.symm v)
  simp only [c, Module.End.mul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    e.apply_symm_apply] at this
  simpa using congrArg e this


/-- **`LieAbelian` from a subspace containing the moved part**: if `X` preserves `U` and every
eigenspace of `X` for `μ ≠ 1` lies in `U`, then `LieAbelian` for `X|_U` gives it for `X`. -/
theorem LieAbelian.of_restrict (hss : X.IsSemisimple) (U : Submodule K V)
    (hXU : ∀ u ∈ U, X u ∈ U) (hU : ∀ μ, μ ≠ 1 → X.eigenspace μ ≤ U)
    (hL : LieAbelian (B.restrict U) (X.restrict hXU)) : LieAbelian B X := by
  intro Y₁ Y₂ hs₁ hs₂ hc₁ hc₂ hf₁ hf₂
  -- `Y` maps `V` into `U`
  have hmapsU : ∀ Y : Module.End K V, Commute X Y → (∀ z ∈ X.eigenspace 1, Y z = 0) →
      ∀ v, Y v ∈ U := by
    intro Y hc hf v
    have hv : v ∈ ⨆ μ : K, X.eigenspace μ := by rw [hss.iSup_eigenspace_eq_top]; trivial
    induction hv using Submodule.iSup_induction' with
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact U.add_mem ha hb
    | mem μ w hw =>
      by_cases hμ : μ = 1
      · subst hμ; rw [hf w hw]; exact U.zero_mem
      · exact hU μ hμ (mapsTo_eigenspace_of_commute hc μ w hw)
  have hm₁ := hmapsU Y₁ hc₁ hf₁
  have hm₂ := hmapsU Y₂ hc₂ hf₂
  let r₁ : Module.End K U := Y₁.restrict (fun u _ => hm₁ u)
  let r₂ : Module.End K U := Y₂.restrict (fun u _ => hm₂ u)
  have hskew : ∀ (Y : Module.End K V) (h : ∀ v, Y v ∈ U), B.IsSkewAdjoint Y →
      LinearMap.IsSkewAdjoint (B.restrict U) (Y.restrict (fun u _ => h u)) := by
    intro Y h hY
    exact LinearMap.isSkewAdjoint_iff.2 fun u v => hY.eq u v
  have hcom : ∀ (Y : Module.End K V) (h : ∀ v, Y v ∈ U), Commute X Y →
      Commute (X.restrict hXU) (Y.restrict (fun u _ => h u)) := by
    intro Y h hY
    refine LinearMap.ext fun u => Subtype.ext ?_
    simp only [Module.End.mul_apply, LinearMap.coe_restrict_apply]
    rw [← Module.End.mul_apply X Y, hY.eq, Module.End.mul_apply]
  have hfix : ∀ (Y : Module.End K V) (h : ∀ v, Y v ∈ U), (∀ z ∈ X.eigenspace 1, Y z = 0) →
      ∀ z ∈ Module.End.eigenspace (X.restrict hXU) 1, Y.restrict (fun u _ => h u) z = 0 := by
    intro Y h hY z hz
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply, Submodule.coe_zero]
    apply hY
    rw [Module.End.mem_eigenspace_iff, one_smul] at hz ⊢
    exact congrArg Subtype.val hz
  have key := (hL _ _ (hskew _ hm₁ hs₁) (hskew _ hm₂ hs₂) (hcom _ hm₁ hc₁) (hcom _ hm₂ hc₂)
    (hfix _ hm₁ hf₁) (hfix _ hm₂ hf₂)).eq
  refine LinearMap.ext fun v => ?_
  simp only [Module.End.mul_apply]
  have hv : v ∈ ⨆ μ : K, X.eigenspace μ := by rw [hss.iSup_eigenspace_eq_top]; trivial
  induction hv using Submodule.iSup_induction' with
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
  | mem μ w hw =>
    by_cases hμ : μ = 1
    · subst hμ; rw [hf₁ w hw, hf₂ w hw, map_zero, map_zero]
    · have := congrArg Subtype.val (LinearMap.congr_fun key ⟨w, hU μ hμ hw⟩)
      simpa [Module.End.mul_apply, LinearMap.coe_restrict_apply] using this

end Group

end IsomCent

end GSpinGGP
