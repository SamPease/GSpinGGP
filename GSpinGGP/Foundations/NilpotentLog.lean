/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# The logarithm of a unipotent element

For `x` nilpotent in a `ℚ`-algebra `A`, the truncated logarithm series
`log (1 + x) = x − x²/2 + x³/3 − ⋯` (a finite sum) is nilpotent and `exp (log (1 + x)) = 1 + x`
(`IsNilpotent.exp`). The identity is the power series identity `exp ∘ log = 1 + X`
(`PowerSeries.subst_exp_log`) evaluated at `x` through truncation: `f ↦ (trunc n f)(x)` is
multiplicative when `xⁿ = 0` (`aeval_trunc_mul_of_pow_eq_zero`).
-/

open Polynomial PowerSeries Finset

namespace GSpinGGP

variable {A : Type*} [Ring A] [Algebra ℚ A] {x : A} {n : ℕ}

/-- For `xⁿ = 0`, truncating a polynomial at degree `n` does not change its value at `x`. -/
theorem aeval_trunc_coe_of_pow_eq_zero (hx : x ^ n = 0) (P : ℚ[X]) :
    aeval x (trunc n (P : ℚ⟦X⟧)) = aeval x P := by
  have hdvd : (Polynomial.X : ℚ[X]) ^ n ∣ P - trunc n (P : ℚ⟦X⟧) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, coeff_trunc, ite_eq_left hd, Polynomial.coeff_coe, sub_self]
  obtain ⟨Q, hQ⟩ := hdvd
  have := congrArg (aeval x) hQ
  rw [map_sub, map_mul, map_pow, aeval_X, hx, zero_mul, sub_eq_zero] at this
  exact this.symm

/-- For `xⁿ = 0`, `f ↦ (trunc n f)(x)` is multiplicative on `ℚ⟦X⟧`. -/
theorem aeval_trunc_mul_of_pow_eq_zero (hx : x ^ n = 0) (f g : ℚ⟦X⟧) :
    aeval x (trunc n (f * g)) = aeval x (trunc n f) * aeval x (trunc n g) := by
  rw [← trunc_trunc_mul_trunc, ← Polynomial.coe_mul, aeval_trunc_coe_of_pow_eq_zero hx, map_mul]

/-- For `xⁿ = 0`, `f ↦ (trunc n f)(x)` commutes with powers. -/
theorem aeval_trunc_pow_of_pow_eq_zero (hx : x ^ n = 0) (f : ℚ⟦X⟧) (k : ℕ) :
    aeval x (trunc n (f ^ k)) = aeval x (trunc n f) ^ k := by
  induction k with
  | zero =>
    rcases n with _ | n
    · have : Subsingleton A := subsingleton_of_zero_eq_one (by simpa using hx.symm)
      exact Subsingleton.elim _ _
    · rw [pow_zero, pow_zero, trunc_one, map_one]
  | succ k ih => rw [pow_succ, aeval_trunc_mul_of_pow_eq_zero hx, ih, pow_succ]

/-- The logarithm `log (1 + x) = ∑_{k ≥ 1} (−1)^{k+1} xᵏ / k` of a unipotent `1 + x`, truncated at
`xⁿ = 0`. -/
noncomputable def nilLog (n : ℕ) (x : A) : A :=
  aeval x (trunc n (PowerSeries.log ℚ))

theorem commute_aeval_self (x : A) (P : ℚ[X]) : Commute x (aeval x P) := by
  simpa using (Commute.all (Polynomial.X : ℚ[X]) P).map (aeval x)

theorem nilLog_eq_mul (hx : x ^ n = 0) :
    ∃ y : A, Commute x y ∧ nilLog n x = x * y := by
  obtain ⟨g, hg⟩ : (PowerSeries.X : ℚ⟦X⟧) ∣ PowerSeries.log ℚ :=
    PowerSeries.X_dvd_iff.mpr constantCoeff_log
  refine ⟨aeval x (trunc n g), commute_aeval_self x _, ?_⟩
  rw [nilLog, hg, aeval_trunc_mul_of_pow_eq_zero hx, ← Polynomial.coe_X,
    aeval_trunc_coe_of_pow_eq_zero hx, aeval_X]

theorem nilLog_pow_eq_zero (hx : x ^ n = 0) : nilLog n x ^ n = 0 := by
  obtain ⟨y, hc, hL⟩ := nilLog_eq_mul hx
  rw [hL, hc.mul_pow, hx, zero_mul]

/-- The truncation of `exp ∘ log` is the truncated sum `∑_{k<n} logᵏ / k!`. -/
theorem trunc_subst_exp_log (n : ℕ) :
    trunc n ((PowerSeries.exp ℚ).subst (PowerSeries.log ℚ)) =
      trunc n (∑ k ∈ range n, ((k.factorial : ℚ)⁻¹) • PowerSeries.log ℚ ^ k) := by
  obtain ⟨g, hg⟩ : (PowerSeries.X : ℚ⟦X⟧) ∣ PowerSeries.log ℚ :=
    PowerSeries.X_dvd_iff.mpr constantCoeff_log
  have hz : ∀ m d : ℕ, m < d → PowerSeries.coeff m (PowerSeries.log ℚ ^ d) = 0 := by
    intro m d hmd
    rw [hg, mul_pow, PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega)]
  ext m
  rw [coeff_trunc, coeff_trunc]
  split_ifs with hm
  · rw [coeff_subst' HasSubst.log, finsum_eq_sum_of_support_subset (s := range n), map_sum]
    · refine sum_congr rfl fun k _ => ?_
      simp [PowerSeries.coeff_exp, smul_eq_mul]
    · intro d hd
      rw [Function.mem_support] at hd
      rw [Finset.mem_coe, Finset.mem_range]
      by_contra hdn
      exact hd (by rw [hz m d (by omega), smul_zero])
  · rfl

/-- **`exp (log (1 + x)) = 1 + x`** for nilpotent `x` (`xⁿ = 0`). -/
theorem exp_nilLog (hx : x ^ n = 0) : IsNilpotent.exp (nilLog n x) = 1 + x := by
  rw [IsNilpotent.exp_eq_sum (nilLog_pow_eq_zero hx)]
  have h1 : ∀ k : ℕ, nilLog n x ^ k = aeval x (trunc n (PowerSeries.log ℚ ^ k)) := fun k => by
    rw [aeval_trunc_pow_of_pow_eq_zero hx]; rfl
  simp_rw [h1, ← map_smul, ← map_sum, ← trunc_subst_exp_log, subst_exp_log]
  rw [← Polynomial.coe_X, ← Polynomial.coe_one, ← Polynomial.coe_add,
    aeval_trunc_coe_of_pow_eq_zero hx, map_add, map_one, aeval_X]

end GSpinGGP
