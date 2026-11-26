/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.SpecialK
import GSpinGGP.TraceFormula.W1Lie
import GSpinGGP.Foundations.TorusIntegrability
import GSpinGGP.Foundations.ValueGroup

/-!
# The two transcriptions of W1's special lattices agree

Waldspurger's special lattices (*Une formule intégrale reliée à la conjecture locale de
Gross–Prasad*, Compositio Math. 146 (2010), §7.1, arXiv p. 34) are transcribed twice:

* `SpecialLattice Q` (`GGP/SpecialK.lean`) takes W1's bilinear form to be `polar Q`, and
  `r = |ϖ^c|` as a norm of `F^×`, so that no uniformizer is chosen;
* `LuoDatum.IsSpecialLattice Q ϖ` (`TraceFormula/W1Lie.lean`) takes it to be `bform Q = ½ polar Q`,
  with a uniformizer `ϖ`, `c ∈ ℤ` and the absolute value `absF`.

`SpecialLattice.isSpecialLattice`: the lattice `S.R` of a `SpecialLattice` satisfies
`IsSpecialLattice Q ϖ` for every uniformizer `ϖ`.  The dictionary: the hyperbolic system
`w_i = v_{i−1}`, `w_{−i} = 2 v'_{i−1}` (`i = 1, …, n`), so that
`bform(w_i, w_{−i}) = polar(v, v') = 1`;
the same `V_an`; and `c` with `|ϖ|^c = r / ‖2‖`, so that W1's `q(v) = ½ Q v` has
`val_F(½ Q v) ≥ c` exactly when `‖Q v‖ ≤ r`, and the coefficient `b` of `ϖ^c w_{−i} = 2ϖ^c v'`
has `|b| ≤ 1` exactly when `‖2ϖ^c b‖ ≤ r`.
-/

noncomputable section

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- `|·|_F` and `‖·‖` define the same order on `F`. -/
theorem absF_le_absF_iff {a b : F} : absF a ≤ absF b ↔ ‖a‖ ≤ ‖b‖ := by
  refine ⟨fun h => ?_, absF_le_absF_of_norm_le⟩
  by_contra hlt
  push Not at hlt
  have ha : a ≠ 0 := fun ha => by rw [ha, norm_zero] at hlt; exact (norm_nonneg b).not_gt hlt
  have h1 : ‖b / a‖ < 1 := by rw [norm_div, div_lt_one (norm_pos_iff.2 ha)]; exact hlt
  have h2 := absF_lt_one_of_norm_lt_one h1
  have hb : b = (b / a) * a := by field_simp
  rw [hb, absF_mul] at h
  have hpos := absF_pos ha
  nlinarith

/-- `|·|_F` commutes with integer powers. -/
theorem absF_zpow (a : F) (c : ℤ) : absF (a ^ c) = absF a ^ c := by
  rcases c with c | c
  · simp [absF_pow]
  · rw [zpow_negSucc, zpow_negSucc, absF_inv, absF_pow]

/-- `bform = ½ polar`. -/
theorem bform_eq_half_polar {U : Type*} [AddCommGroup U] [Module F U] (Q : QuadraticForm F U)
    (x y : U) : bform Q x y = ⅟(2 : F) * QuadraticMap.polar Q x y := by
  rw [polar_eq_two_mul_bform, ← mul_assoc, invOf_mul_self, one_mul]

namespace LuoDatum

/-- A uniformizer for `absF` is one for `‖·‖`. -/
theorem IsUniformizer.norm {ϖ : F} (hϖ : IsUniformizer ϖ) :
    0 < ‖ϖ‖ ∧ ‖ϖ‖ < 1 ∧ ∀ x : F, ‖x‖ < 1 → ‖x‖ ≤ ‖ϖ‖ := by
  obtain ⟨h0, h1, hmax⟩ := hϖ
  have hne : ϖ ≠ 0 := fun h => by rw [h, absF_zero] at h0; exact lt_irrefl _ h0
  refine ⟨norm_pos_iff.2 hne, ?_, fun x hx => absF_le_absF_iff.1 (hmax x
    (absF_lt_one_of_norm_lt_one hx))⟩
  by_contra h
  push Not at h
  have := absF_le_absF_iff.2 (show ‖(1 : F)‖ ≤ ‖ϖ‖ by rwa [norm_one])
  rw [absF_one] at this
  linarith

end LuoDatum

namespace SpecialLattice

variable {U : Type*} [AddCommGroup U] [Module F U] {Q : QuadraticForm F U} (S : SpecialLattice Q)

/-- The hyperbolic system of `S` in W1's indexing by `ℤ`, for `q(·,·) = bform Q`:
`w_i = v_{i−1}` and `w_{−i} = 2 v'_{i−1}` for `1 ≤ i ≤ n` (and `0` elsewhere). -/
def wZ (i : ℤ) : U :=
  if h : 0 < i ∧ i.toNat - 1 < S.n then S.v ⟨i.toNat - 1, h.2⟩
  else if h' : i < 0 ∧ (-i).toNat - 1 < S.n then (2 : F) • S.v' ⟨(-i).toNat - 1, h'.2⟩ else 0

omit [PAdicField F] in
theorem wZ_pos (k : Fin S.n) : S.wZ ((k : ℕ) + 1) = S.v k := by
  have h : 0 < ((k : ℕ) + 1 : ℤ) ∧ (((k : ℕ) + 1 : ℤ)).toNat - 1 < S.n := by omega
  rw [wZ, dite_eq_left h]
  congr 1

omit [PAdicField F] in
theorem wZ_neg (k : Fin S.n) : S.wZ (-((k : ℕ) + 1 : ℤ)) = (2 : F) • S.v' k := by
  have h : ¬ (0 < -((k : ℕ) + 1 : ℤ) ∧ (-((k : ℕ) + 1 : ℤ)).toNat - 1 < S.n) := by omega
  have h' : -((k : ℕ) + 1 : ℤ) < 0 ∧ (-(-((k : ℕ) + 1 : ℤ))).toNat - 1 < S.n := by omega
  rw [wZ, dite_eq_right h, dite_eq_left h']
  congr 2

omit [NontriviallyNormedField F] [PAdicField F] [Module F U] in
theorem exists_fin_of_abs {n : ℕ} {i : ℤ} (h1 : 1 ≤ |i|) (h2 : |i| ≤ n) :
    ∃ k : Fin n, i = (k : ℕ) + 1 ∨ i = -((k : ℕ) + 1 : ℤ) := by
  rcases le_or_gt 0 i with hi | hi
  · rw [abs_of_nonneg hi] at h1 h2
    exact ⟨⟨(i - 1).toNat, by omega⟩, Or.inl (by simp; omega)⟩
  · rw [abs_of_neg hi] at h1 h2
    exact ⟨⟨(-i - 1).toNat, by omega⟩, Or.inr (by simp; omega)⟩

omit [PAdicField F] in
theorem polar_v'_v (i j : Fin S.n) :
    QuadraticMap.polar Q (S.v' i) (S.v j) = if j = i then 1 else 0 := by
  rw [QuadraticMap.polar_comm, S.polar_v_v']

omit [PAdicField F] in
/-- `V = Z ⊕ V_an`: `x − Σ polar(x, v'_k) v_k − Σ polar(x, v_k) v'_k ∈ V_an`. -/
theorem sub_sum_mem_Van (x : U) :
    x - (∑ k, QuadraticMap.polar Q x (S.v' k) • S.v k +
      ∑ k, QuadraticMap.polar Q x (S.v k) • S.v' k) ∈ S.Van := by
  rw [mem_hypOrth]
  intro j
  simp only [← QuadraticMap.polarBilin_apply_apply, map_sub, map_add, map_sum, map_smul,
    smul_eq_mul]
  simp only [QuadraticMap.polarBilin_apply_apply, S.polar_v_v, S.polar_v_v', S.polar_v'_v,
    S.polar_v'_v', mul_zero, Finset.sum_const_zero, mul_ite, mul_one, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, zero_add, add_zero]
  constructor <;> rw [QuadraticMap.polar_comm] <;> ring

end SpecialLattice

open LuoDatum in
/-- **A `SpecialLattice` is a special lattice in the sense of `LuoDatum.IsSpecialLattice`**, for any
uniformizer `ϖ` (W1 §7.1 with `q(·,·) = polar Q` versus `q(·,·) = bform Q`): take
`w_i = v_{i−1}`, `w_{−i} = 2 v'_{i−1}`, the same `V_an`, and `c` with `|ϖ|^c = r / ‖2‖`. -/
theorem SpecialLattice.isSpecialLattice {U : Type*} [AddCommGroup U] [Module F U]
    {Q : QuadraticForm F U} (S : SpecialLattice Q) {ϖ : F} (hϖ : IsUniformizer ϖ) :
    IsSpecialLattice Q ϖ S.R := by
  obtain ⟨h0, h1, hmax⟩ := hϖ.norm
  obtain ⟨a, ha0, hra⟩ := S.exists_norm_eq
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hi2 : (⅟(2 : F)) ≠ 0 := by rw [invOf_eq_inv]; exact inv_ne_zero h2
  set t : F := ⅟(2 : F) * a with ht_def
  have ht0 : t ≠ 0 := mul_ne_zero hi2 ha0
  obtain ⟨c, hc⟩ := exists_norm_eq_zpow h0 h1 hmax ht0
  have hϖ0 : ϖ ≠ 0 := norm_pos_iff.1 h0
  -- `|ϖ|_F^c = |t|_F`, `‖ϖ^c‖ = ‖t‖`
  have hnc : ‖ϖ ^ c‖ = ‖t‖ := by rw [norm_zpow, hc]
  have hac : absF ϖ ^ c = absF t := by
    rw [← absF_zpow]; exact absF_eq_of_norm_eq ht0 hnc
  have hn2 : ‖⅟(2 : F)‖ * ‖(2 : F)‖ = 1 := by rw [← norm_mul, invOf_mul_self, norm_one]
  have hcw : ϖ ^ c * 2 ≠ 0 := mul_ne_zero (zpow_ne_zero c hϖ0) h2
  have hn2c : ‖ϖ ^ c * 2‖ = S.r := by
    rw [norm_mul, hnc, ht_def, norm_mul, ← hra]
    linear_combination ‖a‖ * hn2
  -- `val_F(½ Q v) ≥ c` iff `‖Q v‖ ≤ r`
  have hQle : ∀ y : U, absF (⅟(2 : F) * Q y) ≤ absF ϖ ^ c ↔ ‖Q y‖ ≤ S.r := by
    intro y
    rw [hac, absF_le_absF_iff, ht_def, norm_mul, norm_mul, ← hra]
    exact mul_le_mul_iff_of_pos_left (norm_pos_iff.2 hi2)
  have hQeq : ∀ y : U, ‖Q y‖ = S.r → absF (⅟(2 : F) * Q y) = absF ϖ ^ c := by
    intro y hy
    rw [hac]
    refine absF_eq_of_norm_eq ht0 ?_
    rw [ht_def, norm_mul, norm_mul, hy, hra]
  -- the sums over `w_{−i}`
  have hsum : ∀ b : Fin S.n → F, ∑ i, b i • (ϖ ^ c • S.wZ (-((i : ℕ) + 1 : ℤ))) =
      ∑ i, (b i * (ϖ ^ c * 2)) • S.v' i := by
    intro b
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [S.wZ_neg, smul_smul, smul_smul, mul_assoc]
  have hsumv : ∀ a : Fin S.n → F, ∑ i, a i • S.wZ ((i : ℕ) + 1) = ∑ i, a i • S.v i := by
    intro a
    exact Finset.sum_congr rfl fun i _ => by rw [S.wZ_pos]
  have habs : ∀ k : Fin S.n, |((k : ℕ) : ℤ) + 1| = (k : ℕ) + 1 := fun k => abs_of_pos (by omega)
  refine ⟨S.Van, S.n, S.wZ, c, S.aniso, ?_, ?_, ?_, ?_, ?_⟩
  · -- `bform(w_i, w_j) = δ_{i,−j}`
    intro i j hi1 hi2' hj1 hj2
    obtain ⟨k, rfl | rfl⟩ := SpecialLattice.exists_fin_of_abs hi1 hi2' <;>
    obtain ⟨l, rfl | rfl⟩ := SpecialLattice.exists_fin_of_abs hj1 hj2
    · rw [S.wZ_pos, S.wZ_pos, bform_eq_half_polar, S.polar_v_v, mul_zero,
        ite_eq_right (by omega)]
    · rw [S.wZ_pos, S.wZ_neg, LinearMap.map_smul, bform_eq_half_polar, smul_eq_mul,
        ← mul_assoc, mul_invOf_self, one_mul, S.polar_v_v']
      by_cases h : k = l
      · subst h; simp
      · rw [ite_eq_right h, ite_eq_right]; intro h'; exact h (Fin.ext (by omega))
    · rw [S.wZ_neg, S.wZ_pos, LinearMap.map_smul₂, bform_eq_half_polar, smul_eq_mul,
        ← mul_assoc, mul_invOf_self, one_mul, S.polar_v'_v]
      by_cases h : l = k
      · subst h; simp
      · rw [ite_eq_right h, ite_eq_right]; intro h'; exact h (Fin.ext (by omega))
    · rw [S.wZ_neg, S.wZ_neg, LinearMap.map_smul₂, LinearMap.map_smul,
        bform_eq_half_polar,        S.polar_v'_v', ite_eq_right (by omega)]
      simp
  · -- `w_i ⊥ V_an`
    intro i hi1 hi2' y hy
    rw [mem_hypOrth] at hy
    obtain ⟨k, rfl | rfl⟩ := SpecialLattice.exists_fin_of_abs hi1 hi2'
    · rw [S.wZ_pos, bform_eq_half_polar, (hy k).1, mul_zero]
    · rw [S.wZ_neg, LinearMap.map_smul₂, bform_eq_half_polar, (hy k).2, mul_zero,
        smul_zero]
  · -- `V = Z ⊕ V_an`
    refine eq_top_iff.2 fun x _ => Submodule.mem_sup.2 ⟨_, ?_, _, S.sub_sum_mem_Van x,
      add_sub_cancel _ _⟩
    refine add_mem (sum_mem fun k _ => Submodule.smul_mem _ _ ?_)
      (sum_mem fun k _ => Submodule.smul_mem _ _ ?_)
    · rw [← S.wZ_pos]
      exact Submodule.subset_span ⟨_, ⟨by rw [habs]; omega, by rw [habs]; omega⟩, rfl⟩
    · have : S.v' k = ⅟(2 : F) • S.wZ (-((k : ℕ) + 1 : ℤ)) := by
        rw [S.wZ_neg, smul_smul, invOf_mul_self, one_smul]
      rw [this]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨?_, ?_⟩, rfl⟩)
      · rw [abs_neg, habs]; omega
      · rw [abs_neg, habs]; omega
  · -- `c` is a value of `val_F ∘ q` on `V_an`
    intro hne
    obtain ⟨y, hy, hQy⟩ := S.attained hne
    exact ⟨y, hy, hQeq y hQy⟩
  · -- the lattice
    ext x
    constructor
    · rintro ⟨a, b, y, ha, hb, hy, hQy, rfl⟩
      refine ⟨a, fun i => b i * (ϖ ^ c * 2)⁻¹, y, fun i => ?_, fun i => ?_, hy, (hQle y).2 hQy, ?_⟩
      · rw [← absF_one (F := F), absF_le_absF_iff, norm_one]; exact ha i
      · rw [← absF_one (F := F), absF_le_absF_iff, norm_mul, norm_inv, hn2c, norm_one]
        rcases S.r_nonneg.eq_or_lt with h | h
        · rw [← h, inv_zero, mul_zero]; exact zero_le_one
        · rw [mul_inv_le_iff₀ h, one_mul]; exact hb i
      · rw [hsum, hsumv]
        congr 2
        exact Finset.sum_congr rfl fun i _ => by rw [inv_mul_cancel_right₀ hcw]
    · rintro ⟨a, b, y, ha, hb, hy, hQy, rfl⟩
      refine ⟨a, fun i => b i * (ϖ ^ c * 2), y, fun i => ?_, fun i => ?_, hy, (hQle y).1 hQy, ?_⟩
      · have := absF_le_absF_iff.1 (show absF (a i) ≤ absF 1 by rw [absF_one]; exact ha i)
        rwa [norm_one] at this
      · rw [norm_mul, hn2c]
        have := absF_le_absF_iff.1 (show absF (b i) ≤ absF 1 by rw [absF_one]; exact hb i)
        rw [norm_one] at this
        exact mul_le_of_le_one_left S.r_nonneg this
      · rw [hsum, hsumv]

end GSpinGGP
