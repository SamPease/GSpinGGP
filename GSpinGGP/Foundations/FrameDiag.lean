/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.HypFrame

/-!
# Frame-diagonal maps

For a hyperbolic frame `eᵢ, fᵢ` with orthogonal complement `W` (`IsHypFrame`), a linear map `k` is
*diagonal in the frame* if it acts on `W` by a scalar `c` and scales `eᵢ, fᵢ` by `aᵢ, bᵢ`.  Torus
elements (`c = 1`, `bᵢ = aᵢ⁻¹`) and elements of its Lie algebra (`c = 0`, `bᵢ = −aᵢ`) are of this
form.  When all the values `c, aᵢ, bᵢ` are distinct, the maps commuting with `k` preserve `W` and
scale every `eᵢ, fᵢ` (`IsHypFrame.eq_smul_e_of_commute_diag`, `IsHypFrame.mapsTo_of_commute_diag`),
hence commute with every frame-diagonal map (`IsHypFrame.commute_of_commute_diag`).  This is the
additive form of `IsHypFrame.mem_hypTorus_of_commute`.
-/

noncomputable section

open QuadraticMap

namespace GSpinGGP

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

namespace IsHypFrame

variable {Q : QuadraticForm K V} {W : Submodule K V} {n : ℕ} {e f : Fin n → V}


section Diag

variable {k : V →ₗ[K] V} {c : K} {a b : Fin n → K}

theorem apply_eq_of_diag (hF : IsHypFrame Q W e f) (hkW : ∀ w ∈ W, k w = c • w)
    (hke : ∀ i, k (e i) = a i • e i) (hkf : ∀ i, k (f i) = b i • f i) (v : V) :
    k v = c • (v - frameSum Q e f v) + ∑ j, ((a j * polar Q v (f j)) • e j +
      (b j * polar Q v (e j)) • f j) := by
  conv_lhs => rw [← add_sub_cancel (frameSum Q e f v) v]
  rw [map_add, hkW _ (hF.proj_mem v), add_comm]
  simp only [frameSum, map_sum, map_add, map_smul, hke, hkf, smul_smul, mul_comm]

theorem polar_apply_f_of_diag (hF : IsHypFrame Q W e f) (hkW : ∀ w ∈ W, k w = c • w)
    (hke : ∀ i, k (e i) = a i • e i) (hkf : ∀ i, k (f i) = b i • f i) (v : V) (j : Fin n) :
    polar Q (k v) (f j) = a j * polar Q v (f j) := by
  rw [hF.apply_eq_of_diag hkW hke hkf, polar_add_left, polar_smul_left,
    ((hF.mem_iff _).1 (hF.proj_mem v) j).2, smul_zero, zero_add, hF.polar_sum_f]

theorem polar_apply_e_of_diag (hF : IsHypFrame Q W e f) (hkW : ∀ w ∈ W, k w = c • w)
    (hke : ∀ i, k (e i) = a i • e i) (hkf : ∀ i, k (f i) = b i • f i) (v : V) (j : Fin n) :
    polar Q (k v) (e j) = b j * polar Q v (e j) := by
  rw [hF.apply_eq_of_diag hkW hke hkf, polar_add_left, polar_smul_left,
    ((hF.mem_iff _).1 (hF.proj_mem v) j).1, smul_zero, zero_add, hF.polar_sum_e]

/-- An eigenvector of a frame-diagonal `k` for the eigenvalue `c` of `W` lies in `W`, when `c` is
none of the `aᵢ, bᵢ`. -/
theorem mem_of_diag (hF : IsHypFrame Q W e f) (hkW : ∀ w ∈ W, k w = c • w)
    (hke : ∀ i, k (e i) = a i • e i) (hkf : ∀ i, k (f i) = b i • f i)
    (hac : ∀ i, a i ≠ c) (hbc : ∀ i, b i ≠ c) {v : V} (hv : k v = c • v) : v ∈ W := by
  rw [hF.mem_iff]
  intro j
  have h1 := hF.polar_apply_f_of_diag hkW hke hkf v j
  have h2 := hF.polar_apply_e_of_diag hkW hke hkf v j
  rw [hv, polar_smul_left, smul_eq_mul] at h1 h2
  exact ⟨(mul_eq_mul_right_iff.mp h2.symm).resolve_left (hbc j),
    (mul_eq_mul_right_iff.mp h1.symm).resolve_left (hac j)⟩

/-- Eigenvectors of a frame-diagonal `k` for an eigenvalue `μ ≠ c` lie in the span of the frame,
and only meet the coordinates `fⱼ` (resp. `eⱼ`) with `aⱼ = μ` (resp. `bⱼ = μ`). -/
theorem eigen_of_diag (hF : IsHypFrame Q W e f) (hkW : ∀ w ∈ W, k w = c • w)
    (hke : ∀ i, k (e i) = a i • e i) (hkf : ∀ i, k (f i) = b i • f i) {μ : K} {v : V}
    (hv : k v = μ • v) (hμ : μ ≠ c) :
    v = frameSum Q e f v ∧ (∀ j, polar Q v (f j) ≠ 0 → μ = a j) ∧
      (∀ j, polar Q v (e j) ≠ 0 → μ = b j) := by
  refine ⟨?_, fun j hj => ?_, fun j hj => ?_⟩
  · have h1 := hF.apply_eq_of_diag hkW hke hkf v
    have h2 : frameSum Q e f (k v) = ∑ j, ((a j * polar Q v (f j)) • e j +
        (b j * polar Q v (e j)) • f j) := by
      simp only [frameSum, hF.polar_apply_f_of_diag hkW hke hkf,
        hF.polar_apply_e_of_diag hkW hke hkf]
    have h3 : frameSum Q e f (μ • v) = μ • frameSum Q e f v := by
      simp only [frameSum, polar_smul_left, Finset.smul_sum, smul_add, smul_smul, smul_eq_mul]
    rw [hv, h3] at h2
    rw [← h2, hv] at h1
    have h4 : (μ - c) • (v - frameSum Q e f v) = 0 := by
      rw [sub_smul, smul_sub, smul_sub, h1, smul_sub]
      abel
    rw [← sub_eq_zero]
    exact (smul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 hμ)
  · have h := hF.polar_apply_f_of_diag hkW hke hkf v j
    rw [hv, polar_smul_left, smul_eq_mul] at h
    exact mul_right_cancel₀ hj h
  · have h := hF.polar_apply_e_of_diag hkW hke hkf v j
    rw [hv, polar_smul_left, smul_eq_mul] at h
    exact mul_right_cancel₀ hj h

variable (hF : IsHypFrame Q W e f) (hkW : ∀ w ∈ W, k w = c • w)
  (hke : ∀ i, k (e i) = a i • e i) (hkf : ∀ i, k (f i) = b i • f i)
  (hac : ∀ i, a i ≠ c) (hbc : ∀ i, b i ≠ c) (ha : Function.Injective a)
  (hb : Function.Injective b) (hab : ∀ i j, a i ≠ b j) {h : V →ₗ[K] V} (hc : Commute k h)
include hF hkW hke hkf hac hbc ha hb hab hc

omit hbc hb in
/-- A map commuting with a *regular* frame-diagonal `k` (the `c, aᵢ, bᵢ` distinct) scales each
`eᵢ`. -/
theorem eq_smul_e_of_commute_diag (i : Fin n) : h (e i) = polar Q (h (e i)) (f i) • e i := by
  have hv : k (h (e i)) = a i • h (e i) := by
    rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hke, map_smul]
  obtain ⟨hs, hfj, hej⟩ := hF.eigen_of_diag hkW hke hkf hv (hac i)
  refine hs.trans ?_
  unfold frameSum
  rw [Finset.sum_eq_single i]
  · have : polar Q (h (e i)) (e i) = 0 := by_contra fun h0 => hab i i (hej i h0)
    rw [this, zero_smul, add_zero]
  · intro j _ hji
    have h1 : polar Q (h (e i)) (f j) = 0 := by_contra fun h0 => hji (ha (hfj j h0)).symm
    have h2 : polar Q (h (e i)) (e j) = 0 := by_contra fun h0 => hab i j (hej j h0)
    rw [h1, h2, zero_smul, zero_smul, add_zero]
  · simp

omit hac ha in
/-- A map commuting with a regular frame-diagonal `k` scales each `fᵢ`. -/
theorem eq_smul_f_of_commute_diag (i : Fin n) : h (f i) = polar Q (h (f i)) (e i) • f i := by
  have hv : k (h (f i)) = b i • h (f i) := by
    rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hkf, map_smul]
  obtain ⟨hs, hfj, hej⟩ := hF.eigen_of_diag hkW hke hkf hv (hbc i)
  refine hs.trans ?_
  unfold frameSum
  rw [Finset.sum_eq_single i]
  · have : polar Q (h (f i)) (f i) = 0 := by_contra fun h0 => hab i i (hfj i h0).symm
    rw [this, zero_smul, zero_add]
  · intro j _ hji
    have h1 : polar Q (h (f i)) (f j) = 0 := by_contra fun h0 => hab j i (hfj j h0).symm
    have h2 : polar Q (h (f i)) (e j) = 0 := by_contra fun h0 => hji (hb (hej j h0)).symm
    rw [h1, h2, zero_smul, zero_smul, add_zero]
  · simp

omit ha hb hab in
/-- A map commuting with a frame-diagonal `k` (with `c` none of the `aᵢ, bᵢ`) preserves `W`. -/
theorem mapsTo_of_commute_diag {w : V} (hw : w ∈ W) : h w ∈ W := by
  refine hF.mem_of_diag hkW hke hkf hac hbc ?_
  rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hkW w hw, map_smul]

/-- **Maps commuting with a regular frame-diagonal map commute with every frame-diagonal map**:
if `h` commutes with `k` (the `c, aᵢ, bᵢ` distinct), then `h` commutes with any `k'` acting on
`W` by a scalar and scaling each `eᵢ`, `fᵢ`. -/
theorem commute_of_commute_diag {k' : V →ₗ[K] V} {c' : K} {a' b' : Fin n → K}
    (hkW' : ∀ w ∈ W, k' w = c' • w) (hke' : ∀ i, k' (e i) = a' i • e i)
    (hkf' : ∀ i, k' (f i) = b' i • f i) : Commute k' h := by
  refine hF.linearMap_ext (fun w hw => ?_) (fun i => ?_) (fun i => ?_)
  · rw [Module.End.mul_apply, Module.End.mul_apply,
      hkW' _ (hF.mapsTo_of_commute_diag hkW hke hkf hac hbc hc hw), hkW' w hw, map_smul]
  · have he := hF.eq_smul_e_of_commute_diag hkW hke hkf hac ha hab hc i
    rw [Module.End.mul_apply, Module.End.mul_apply, hke', map_smul, he, map_smul, hke',
      smul_comm]
  · have hf := hF.eq_smul_f_of_commute_diag hkW hke hkf hbc hb hab hc i
    rw [Module.End.mul_apply, Module.End.mul_apply, hkf', map_smul, hf, map_smul, hkf',
      smul_comm]

omit hac hbc ha hb hab hc in
/-- Two frame-diagonal maps commute. -/
theorem commute_of_diag {k' : V →ₗ[K] V} {c' : K} {a' b' : Fin n → K}
    (hkW' : ∀ w ∈ W, k' w = c' • w) (hke' : ∀ i, k' (e i) = a' i • e i)
    (hkf' : ∀ i, k' (f i) = b' i • f i) : Commute k k' := by
  refine hF.linearMap_ext (fun w hw => ?_) (fun i => ?_) (fun i => ?_)
  · rw [Module.End.mul_apply, Module.End.mul_apply, hkW' w hw, hkW w hw, map_smul, map_smul,
      hkW w hw, hkW' w hw, smul_comm]
  · rw [Module.End.mul_apply, Module.End.mul_apply, hke', hke, map_smul, map_smul, hke, hke',
      smul_comm]
  · rw [Module.End.mul_apply, Module.End.mul_apply, hkf', hkf, map_smul, map_smul, hkf, hkf',
      smul_comm]

end Diag

/-- **A skew frame-diagonal map with prescribed values**: `D v = Σ aⱼ (polar(v, fⱼ) eⱼ −
polar(v, eⱼ) fⱼ)` kills `W`, scales `eᵢ` by `aᵢ` and `fᵢ` by `−aᵢ`, and is skew for `polar`. -/
theorem exists_skew_diag (hF : IsHypFrame Q W e f) (a : Fin n → K) :
    ∃ D : V →ₗ[K] V, (∀ w ∈ W, D w = (0 : K) • w) ∧ (∀ i, D (e i) = a i • e i) ∧
      (∀ i, D (f i) = (-a i) • f i) ∧ ∀ u v, polar Q (D u) v = -polar Q u (D v) := by
  classical
  let D : V →ₗ[K] V := ∑ j, (a j • ((polarBilin Q).flip (f j)).smulRight (e j) -
    a j • ((polarBilin Q).flip (e j)).smulRight (f j))
  have hD : ∀ v, D v = ∑ j, ((a j * polar Q v (f j)) • e j - (a j * polar Q v (e j)) • f j) :=
    fun v => by simp [D, LinearMap.sum_apply, smul_smul]
  refine ⟨D, fun w hw => ?_, fun i => ?_, fun i => ?_, fun u v => ?_⟩
  · rw [hD, zero_smul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [((hF.mem_iff w).1 hw j).1, ((hF.mem_iff w).1 hw j).2]
    simp
  · rw [hD]
    simp [hF.polar_ee, hF.polar_ef]
  · rw [hD]
    simp [hF.polar_ff, hF.polar_fe, neg_smul]
  · rw [hD, hD, ← polarBilin_apply_apply, ← polarBilin_apply_apply, map_sum, map_sum,
      LinearMap.sum_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      polarBilin_apply_apply, smul_eq_mul]
    rw [polar_comm Q (e j) v, polar_comm Q (f j) v]
    ring

end IsHypFrame

end GSpinGGP
