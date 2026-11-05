/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.IsometryCentralizer

/-!
# Joint eigenspaces of a commuting isometry and skew map

Let `B` be a bilinear form, `P` an isometry and `N` a skew endomorphism (`B(N u, v) = −B(u, N v)`)
with `N P = P N`. The joint eigenspaces `E_{(μ,c)} = E_μ(P) ∩ E_c(N)` and `E_{(ν,c')}` are
orthogonal unless `(ν, c') = (μ⁻¹, −c)`, and (for `P`, `N` semisimple over an algebraically closed
field) every value of `B` on `E_{(μ,c)} × V` is attained on `E_{(μ⁻¹,−c)}` (`exists_joint_eigen_pair`).
A nondegenerate pairing of two subspaces has dual bases (`exists_dual_family`). The wedges `u ∧ w`
(`u ∈ E_{(μ,c)}`, `w ∈ E_{(μ⁻¹,−c)}`) commute with `P` and `N` (`commute_wedge`,
`commute_wedge_of_skew`), and `d²` of them are independent (`le_finrank_of_wedge_dual`).
-/

noncomputable section

open Module Module.End LinearMap

namespace GSpinGGP

namespace IsomCent

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {B : LinearMap.BilinForm K V} {N : Module.End K V}

/-- `B(E_c(N), E_c'(N)) = 0` unless `c + c' = 0`, for `N` skew. -/
theorem bform_eigen_eq_zero_of_skew (hN : IsSkew B N) {c c' : K} (hcc' : c + c' ≠ 0) {u v : V}
    (hu : u ∈ N.eigenspace c) (hv : v ∈ N.eigenspace c') : B u v = 0 := by
  rw [mem_eigenspace_iff] at hu hv
  have h := hN u v
  rw [hu, hv, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h
  have : (c + c') * B u v = 0 := by linear_combination h
  exact (mul_eq_zero.1 this).resolve_left hcc'

/-- The wedge of `u ∈ E_c(N)` and `w ∈ E_{−c}(N)` commutes with the skew `N`. -/
theorem commute_wedge_of_skew (hN : IsSkew B N) {c : K} {u w : V}
    (hu : u ∈ N.eigenspace c) (hw : w ∈ N.eigenspace (-c)) : Commute N (wedge B u w) := by
  rw [mem_eigenspace_iff] at hu hw
  ext z
  simp only [Module.End.mul_apply, wedge_apply, map_sub, map_smul]
  have h1 : B w (N z) = c * B w z := by
    rw [← neg_neg (B w (N z)), ← hN, hw, map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
  have h2 : B u (N z) = -c * B u z := by
    rw [← neg_neg (B u (N z)), ← hN, hu, map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
  rw [h1, h2, hu, hw]
  module

/-- **`d²` independent wedges.** If `u, w : Fin d → V` satisfy `B(w_j, u_k) = δ_{jk}` and
`B(u_i, u_k) = 0`, the wedges `u_i ∧ w_j` are linearly independent; so a subspace `C` containing them has dimension
`≥ d²`. -/
theorem le_finrank_of_wedge_dual [FiniteDimensional K V] {C : Submodule K (Module.End K V)}
    {d : ℕ} (u w : Fin d → V) (huu : ∀ i k, B (u i) (u k) = 0)
    (hwu : ∀ j k, B (w j) (u k) = if j = k then 1 else 0) (hmem : ∀ i j, wedge B (u i) (w j) ∈ C) :
    d * d ≤ finrank K C := by
  let f : Fin d × Fin d → C := fun p => ⟨wedge B (u p.1) (w p.2), hmem p.1 p.2⟩
  have hf : LinearIndependent K f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc ⟨l, k⟩
    have h := congrArg (fun M : C => B (w l) ((M : Module.End K V) (u k))) hc
    simp only [f, Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      wedge_apply, map_sum, map_smul, huu, hwu, zero_smul, sub_zero, smul_eq_mul,
      ZeroMemClass.coe_zero, LinearMap.zero_apply, map_zero, ite_smul, one_smul] at h
    simpa [Fintype.sum_prod_type, apply_ite (B (w l)), hwu, Finset.sum_ite_eq, Finset.sum_ite_eq',
      mul_ite] using h
  simpa using hf.fintype_card_le_finrank

/-- **Dual bases for a nondegenerate pairing** `E × E' → K`, `(x, y) ↦ B y x`: `dim E' = dim E`, and
there are `u_k ∈ E`, `w_j ∈ E'` with `B(w_j, u_k) = δ_{jk}`. -/
theorem exists_dual_family [FiniteDimensional K V] {E E' : Submodule K V}
    (h1 : ∀ x ∈ E, x ≠ 0 → ∃ y ∈ E', B y x ≠ 0) (h2 : ∀ y ∈ E', y ≠ 0 → ∃ x ∈ E, B y x ≠ 0) :
    finrank K E' = finrank K E ∧ ∃ u w : Fin (finrank K E) → V, (∀ k, u k ∈ E) ∧ (∀ j, w j ∈ E') ∧
      ∀ j k, B (w j) (u k) = if j = k then 1 else 0 := by
  let φ : E' →ₗ[K] E →ₗ[K] K := B.compl₁₂ E'.subtype E.subtype
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    by_contra hne
    obtain ⟨x, hx, hB⟩ := h2 y y.2 (fun h => hne (Subtype.ext h))
    exact hB (LinearMap.congr_fun (LinearMap.mem_ker.1 hy) ⟨x, hx⟩)
  have hψ : Function.Injective φ.flip := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    by_contra hne
    obtain ⟨y, hy, hB⟩ := h1 x x.2 (fun h => hne (Subtype.ext h))
    exact hB (LinearMap.congr_fun (LinearMap.mem_ker.1 hx) ⟨y, hy⟩)
  have : φ.IsPerfPair := LinearMap.IsPerfPair.of_injective hφ hψ
  have hd : finrank K E' = finrank K E := Module.finrank_of_isPerfPair φ
  let e := φ.toPerfPair
  let b := Module.finBasis K E
  refine ⟨hd, fun k => b k, fun j => e.symm (b.dualBasis j), fun k => (b k).2,
    fun j => (e.symm (b.dualBasis j)).2, fun j k => ?_⟩
  have := LinearMap.congr_fun (e.apply_symm_apply (b.dualBasis j)) (b k)
  rw [LinearMap.toPerfPair_apply] at this
  rw [Module.Basis.dualBasis_apply_self] at this
  simp only [eq_comm (a := j)]
  rw [← this]
  rfl

variable {P : Module.End K V}

variable [IsAlgClosed K] [FiniteDimensional K V]

/-- **Joint pairing**: for `u ∈ E_μ(P) ∩ E_c(N)` (`P` a semisimple isometry, `N` a semisimple skew
map commuting with it), every value `B u v` is attained on `E_{μ⁻¹}(P) ∩ E_{−c}(N)`. -/
theorem exists_joint_eigen_pair (hP : IsIsom B P) (hssP : P.IsSemisimple) (hN : IsSkew B N)
    (hssN : N.IsSemisimple) (hc : Commute N P) {μ c : K} {u : V} (hu : u ∈ P.eigenspace μ)
    (hu' : u ∈ N.eigenspace c) (v : V) :
    ∃ w ∈ P.eigenspace μ⁻¹ ⊓ N.eigenspace (-c), B u w = B u v := by
  have hv : v ∈ ⨆ κ : K, N.eigenspace κ := by rw [hssN.iSup_eigenspace_eq_top]; trivial
  induction hv using Submodule.iSup_induction' with
  | mem κ y hy =>
    by_cases hκ : c + κ = 0
    · obtain rfl : κ = -c := by linear_combination hκ
      -- decompose `y ∈ E_{−c}(N)` along the eigenspaces of `P`
      set E := N.eigenspace (-c)
      have hE : ∀ x ∈ E, P x ∈ E := mapsTo_eigenspace_of_commute hc (-c)
      have hssE : Module.End.IsSemisimple (P.restrict hE) :=
        hssP.restrict ((Module.End.mem_invtSubmodule _).2 hE)
      have hy' : (⟨y, hy⟩ : E) ∈ ⨆ ν : K, Module.End.eigenspace (P.restrict hE) ν := by
        rw [hssE.iSup_eigenspace_eq_top]; trivial
      suffices ∀ z : E, z ∈ ⨆ ν : K, Module.End.eigenspace (P.restrict hE) ν →
          ∃ w ∈ P.eigenspace μ⁻¹ ⊓ N.eigenspace (-c), B u w = B u z from this _ hy'
      intro z hz
      induction hz using Submodule.iSup_induction' with
      | mem ν z hz =>
        have hzP : (z : V) ∈ P.eigenspace ν := eigenspace_restrict_le_eigenspace P hE ν ⟨z, hz, rfl⟩
        by_cases hν : μ * ν = 1
        · refine ⟨z, ⟨?_, z.2⟩, rfl⟩
          rwa [show μ⁻¹ = ν from (eq_inv_of_mul_eq_one_right hν).symm]
        · exact ⟨0, zero_mem _, by rw [map_zero, bform_eigen_eq_zero hP hν hu hzP]⟩
      | zero => exact ⟨0, zero_mem _, by simp⟩
      | add z₁ z₂ _ _ h₁ h₂ =>
        obtain ⟨w₁, hw₁, e₁⟩ := h₁
        obtain ⟨w₂, hw₂, e₂⟩ := h₂
        exact ⟨w₁ + w₂, add_mem hw₁ hw₂, by rw [map_add, Submodule.coe_add, map_add, e₁, e₂]⟩
    · exact ⟨0, zero_mem _, by rw [map_zero, bform_eigen_eq_zero_of_skew hN hκ hu' hy]⟩
  | zero => exact ⟨0, zero_mem _, rfl⟩
  | add y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨w₁, hw₁, e₁⟩ := h₁
    obtain ⟨w₂, hw₂, e₂⟩ := h₂
    exact ⟨w₁ + w₂, add_mem hw₁ hw₂, by rw [map_add, map_add, e₁, e₂]⟩

end IsomCent

end GSpinGGP
