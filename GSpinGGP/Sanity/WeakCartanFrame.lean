/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.WeakCartanTheorem

/-!
# Sanity witness: a maximal frame of length `l = 1`

Over `ℚ_[p]`, the form `x₀² - x₁² + p x₂²` (a hyperbolic plane plus the anisotropic line `⟨p⟩`)
with its standard basis and `ν = 1` is a maximal frame of length `1` (`isFrame_Qp`): maximality is
`p y² ≠ 1`, as `p y²` has odd valuation. So `IsFrame` is not vacuous beyond `l = 0`, and the
hypotheses of `relCartan_SO` are met by a frame with a nontrivial split torus. The general
existence statement is `WeakCartan.exists_isFrame`.
-/

open Module QuadraticMap GSpinGGP GSpinGGP.WeakCartan

namespace GSpinGGP.Sanity.WeakCartanFrame

variable (p : ℕ) [Fact p.Prime]

/-- `x₀² - x₁² + p x₂²` on `ℚ_[p]³`: a hyperbolic plane plus the line `⟨p⟩`. -/
noncomputable abbrev Qp : QuadraticForm ℚ_[p] (Fin 3 → ℚ_[p]) :=
  weightedSumSquares ℚ_[p] ![1, -1, (p : ℚ_[p])]

theorem isOrthoBasis_Qp : IsOrthoBasis (Qp p) (Pi.basisFun ℚ_[p] (Fin 3)) where
  isOrtho i j hij := by
    rw [isOrtho_def]
    fin_cases i <;> fin_cases j <;> simp_all [weightedSumSquares_apply, Fin.sum_univ_three] <;> ring
  apply_ne_zero i := by
    have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    fin_cases i <;> simp [weightedSumSquares_apply, Fin.sum_univ_three, hp]

/-- `p y² ≠ 1` in `ℚ_[p]`: the valuation of the left side is odd. -/
theorem p_mul_sq_ne_one (y : ℚ_[p]) : (p : ℚ_[p]) * (y * y) ≠ 1 := by
  intro h
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hy : y ≠ 0 := by rintro rfl; simp at h
  have := congrArg Padic.valuation h
  rw [Padic.valuation_mul hp (mul_ne_zero hy hy), Padic.valuation_mul hy hy, Padic.valuation_p,
    Padic.valuation_one] at this
  omega

/-- The basis `e₀, e₁, e₂` is a maximal frame of length `l = 1` for `ν = 1`. -/
theorem isFrame_Qp : IsFrame (Qp p) (Pi.basisFun ℚ_[p] (Fin 3)) 1 1 where
  lt := by norm_num
  apply_eq i hi := by
    fin_cases i
    · simp [weightedSumSquares_apply, Fin.sum_univ_three]
    · simp [weightedSumSquares_apply, Fin.sum_univ_three]
    · simp at hi
  maximal x hx := by
    have h0 := hx 0 (by simp)
    have h1 := hx 1 (by simp)
    simp only [Pi.basisFun_repr] at h0 h1
    simp only [weightedSumSquares_apply, Fin.sum_univ_three, h0, h1]
    simpa using p_mul_sq_ne_one p (x 2)

/-- The relative Cartan decomposition applies to this frame, whose split torus is
one-dimensional. -/
example := relCartan_SO (isOrthoBasis_Qp p) (isFrame_Qp p)

example : numPairs 1 0 = 1 := rfl

/-- The existence theorem applies to this form and the anisotropic vector `e₀`: it is
nondegenerate, having an orthogonal basis of anisotropic vectors. -/
example : ∃ (n l : ℕ) (b : Module.Basis (Fin n) ℚ_[p] (Fin 3 → ℚ_[p])),
    IsOrthoBasis (Qp p) b ∧ ∃ hf : IsFrame (Qp p) b (Qp p (Pi.single 0 1)) l,
      b ⟨0, (Nat.zero_le l).trans_lt hf.lt⟩ = Pi.single 0 1 := by
  let _ : Invertible (2 : ℚ_[p]) := invertibleOfNonzero two_ne_zero
  refine exists_isFrame (nondegenerate_of_isOrthoᵢ (b := Pi.basisFun ℚ_[p] (Fin 3))
    (fun i j hij => associated_isOrtho.mpr ((isOrthoBasis_Qp p).isOrtho i j hij))
    (isOrthoBasis_Qp p).apply_ne_zero) ?_
  simpa using (isOrthoBasis_Qp p).apply_ne_zero 0

end GSpinGGP.Sanity.WeakCartanFrame
