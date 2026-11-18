/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Polynomial growth from integer coordinates

The polynomial growth of a split torus (BP (6.7.12), Beuzart-Plessis, Astérisque 418, proof of
Prop. 6.7.1(iii), p. 152: the set `{a ∈ A_min(F) ; σ(a) < R}` is covered by `≪ (1 + R)^N`
translates of a fixed compact set) is a lattice-point count: `A_min(F)` modulo its maximal compact
subgroup is a lattice `ℤ^N`, the log-norm grows linearly in the lattice coordinates, and the
number of lattice points in a box of side `R` is `≪ (1 + R)^N`.

This file isolates the count, for an arbitrary set `T` in a monoid `G` with integer coordinates
`v : G → ι → ℤ`, so that it does not depend on any structure of reductive groups.

## Main results

* `exists_finset_cover_of_intCoord`: if the coordinates of `a ∈ T` are bounded linearly by `τ(a)`,
  and two elements of `T` with the same coordinates differ by an element `e` of a fixed set `E`
  up to a factor `z` in a fixed set `Z` (`a' = z (a e)`), then `{a ∈ T ; τ(a) < R}` is covered by
  `≤ M (1 + R)^{|ι|}` sets `Z · j · E`, `j ∈ T`.
* `abs_floor_le_abs_add_one`, `norm_div_lt_exp_of_floor_log_norm_eq`, `abs_log_norm_le_log`: the
  coordinate `⌊log ‖x‖⌋ ∈ ℤ` of a nonzero element `x` of a normed field: it is bounded by
  `|log ‖x‖| + 1`,
  and two elements with the same coordinate have quotient of norm in `(e⁻¹, e)`. With this
  coordinate no uniformizer or discreteness of the value group is needed.
-/

open Set

noncomputable section

namespace GSpinGGP

/-- The number of integer vectors in the box `[-B, B]^ι` is `(2B + 1)^{|ι|}`. -/
theorem card_piFinset_Icc_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (B : ℕ) :
    (Fintype.piFinset fun _ : ι => Finset.Icc (-(B : ℤ)) B).card =
      (2 * B + 1) ^ Fintype.card ι := by
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Int.card_Icc]
  congr 1
  omega

/-- **Polynomial growth from integer coordinates.** Let `T` be a subset of a monoid `G`, `τ` a
function on `G` and `v : G → ι → ℤ` coordinates on `T` with `c |vᵢ(a)| ≤ τ(a) + C` (`c > 0`).
Suppose that two elements `a, a'` of `T` with the same coordinates satisfy `a' = z (a e)` with
`z ∈ Z`, `e ∈ E`. Then there is `M` such that for every `R ≥ 1` some finite `t ⊆ T` of size
`≤ M (1 + R)^{|ι|}` has `{a ∈ T ; τ(a) < R} ⊆ ⋃_{j ∈ t} Z · j · E`.

This is the counting behind BP (6.7.12) (polynomial growth of `A_min`), with `E` a compact set,
`Z` the split centre and `v` the coordinates `⌊log ‖tᵢ‖⌋` of the eigenvalues `tᵢ`. -/
theorem exists_finset_cover_of_intCoord {G ι : Type*} [Mul G] [Fintype ι] {T Z E : Set G}
    {τ : G → ℝ} (v : G → ι → ℤ) {c C : ℝ} (hc : 0 < c)
    (hv : ∀ a ∈ T, ∀ i, c * |(v a i : ℝ)| ≤ τ a + C)
    (hE : ∀ a ∈ T, ∀ a' ∈ T, v a = v a' → ∃ z ∈ Z, ∃ e ∈ E, a' = z * (a * e)) :
    ∃ M : ℝ, ∀ R : ℝ, 1 ≤ R → ∃ t : Finset G, (t : Set G) ⊆ T ∧
      (t.card : ℝ) ≤ M * (1 + R) ^ Fintype.card ι ∧
      ∀ a ∈ T, τ a < R → ∃ z ∈ Z, ∃ j ∈ t, ∃ e ∈ E, a = z * (j * e) := by
  classical
  set C' := max C 0
  set A : ℝ := 2 * (1 + C') / c + 3
  refine ⟨A ^ Fintype.card ι, fun R hR => ?_⟩
  set B : ℕ := ⌈(R + C') / c⌉₊
  set box : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(B : ℤ)) B
  set occ := box.filter fun m => ∃ a ∈ T, v a = m
  have hocc : ∀ m : occ, ∃ a ∈ T, v a = m := fun m => (Finset.mem_filter.1 m.2).2
  set rep : occ → G := fun m => (hocc m).choose
  refine ⟨occ.attach.image rep, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hj
    exact (hocc m).choose_spec.1
  · have hC' : 0 ≤ C' := le_max_right _ _
    have hcard : ((occ.attach.image rep).card : ℝ) ≤ (2 * B + 1 : ℕ) ^ Fintype.card ι := by
      have h1 : (occ.attach.image rep).card ≤ box.card :=
        Finset.card_image_le.trans ((Finset.card_attach).le.trans (Finset.card_filter_le _ _))
      rw [card_piFinset_Icc_neg] at h1
      exact_mod_cast h1
    refine hcard.trans ?_
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have hB : (B : ℝ) < (R + C') / c + 1 := Nat.ceil_lt_add_one (by positivity)
    have hRC : (R + C') / c ≤ (1 + C') * (1 + R) / c := by
      gcongr; nlinarith
    push_cast
    calc 2 * (B : ℝ) + 1 ≤ 2 * ((R + C') / c + 1) + 1 := by linarith
      _ ≤ 2 * ((1 + C') * (1 + R) / c) + 3 * (1 + R) := by linarith
      _ = A * (1 + R) := by simp only [A]; ring
  · intro a ha hτ
    have hm : v a ∈ occ := by
      refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, a, ha, rfl⟩
      have h1 := hv a ha i
      have hle : |(v a i : ℝ)| ≤ (R + C') / c := by
        rw [le_div_iff₀ hc]
        have : C ≤ C' := le_max_left _ _
        nlinarith [abs_nonneg (v a i : ℝ)]
      have hB : (R + C') / c ≤ (B : ℝ) := Nat.le_ceil _
      have habs : |(v a i : ℝ)| ≤ B := hle.trans hB
      rw [abs_le] at habs
      rw [Finset.mem_Icc]
      constructor <;> [exact_mod_cast habs.1; exact_mod_cast habs.2]
    obtain ⟨hj, hjv⟩ := (hocc ⟨v a, hm⟩).choose_spec
    obtain ⟨z, hz, e, he, hae⟩ := hE _ hj a ha hjv
    exact ⟨z, hz, rep ⟨v a, hm⟩, Finset.mem_image.2 ⟨⟨v a, hm⟩, Finset.mem_attach _ _, rfl⟩, e, he,
      hae⟩

section NormCoord

variable {𝕜 : Type*} [NormedField 𝕜]

/-- `|⌊r⌋| ≤ |r| + 1` for real `r`. -/
theorem abs_floor_le_abs_add_one (r : ℝ) : |(⌊r⌋ : ℝ)| ≤ |r| + 1 := by
  have h1 := Int.floor_le r
  have h2 := Int.lt_floor_add_one r
  rw [abs_le]
  constructor <;> cases abs_cases r <;> linarith

/-- Two nonzero elements with the same coordinate `⌊log ‖·‖⌋` have quotient of norm `< e`. -/
theorem norm_div_lt_exp_of_floor_log_norm_eq {x y : 𝕜} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ⌊Real.log ‖x‖⌋ = ⌊Real.log ‖y‖⌋) : ‖x / y‖ < Real.exp 1 := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
  rw [norm_div, ← Real.exp_log (div_pos hx' hy'), Real.exp_lt_exp, Real.log_div hx'.ne' hy'.ne']
  exact (le_abs_self _).trans_lt (Int.abs_sub_lt_one_of_floor_eq_floor h)

/-- `|log ‖t‖| ≤ log M` when `‖t‖, ‖t⁻¹‖ ≤ M`. -/
theorem abs_log_norm_le_log {t : 𝕜} (ht : t ≠ 0) {M : ℝ} (h1 : ‖t‖ ≤ M) (h2 : ‖t⁻¹‖ ≤ M) :
    |Real.log ‖t‖| ≤ Real.log M := by
  have ht' : 0 < ‖t‖ := norm_pos_iff.2 ht
  have hti : 0 < ‖t⁻¹‖ := norm_pos_iff.2 (inv_ne_zero ht)
  rw [abs_le]
  constructor
  · have := Real.log_le_log hti h2
    rw [norm_inv, Real.log_inv] at this
    linarith
  · exact Real.log_le_log ht' h1

end NormCoord

end GSpinGGP
