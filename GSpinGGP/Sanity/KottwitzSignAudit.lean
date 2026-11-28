/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.Triple

/-!
# Sanity checks for the Kottwitz sign over `ℝ` and `ℂ`

`kottwitzSign` (`GGP/Triple.lean`) is split by case on the field.  This file checks that the
archimedean branches are the ones selected for `ℝ` and `ℂ`, and checks the arithmetic of the real
formula on signatures.

**The real sign.**  Over `ℝ`, Kottwitz 1983, p. 290, gives `e(G) = (-1)^{q(G') - q(G)}`, with
`G'` the quasi-split inner form and `q` one half of the dimension of the symmetric space of the
simply connected cover of the derived group (p. 289).  For `G = GSpin(W) × GSpin(V)` this cover is
`Spin(W) × Spin(V)`, and `Spin(p,q)` has a symmetric space of dimension `pq`.  Over `ℝ` the Witt
index of a form of signature `(p,q)` is `min(p,q)`, so `pq = w (n - w)` (`symSpaceDim`).  Thus
`2 q(G) = symSpaceDim W + symSpaceDim V` (`GGPData.symSpaceDim`, up to the dimension `≤ 2`
convention noted at `symSpaceDim`), and the relative sign `e(G) e(G_α) = (-1)^{q(G) - q(G_α)}` is
`1` iff `2q(G) ≡ 2q(G_α) mod 4`, the difference being even.

**Evenness and the value.**  An inner twist keeps dimension and discriminant `(-1)^q`, so it changes
the negative index of `W` (and of `V = W ⊕ Z`, `Z` fixed) by an even number `2k`;
`two_mul_realExponent` shows `2q(G) - 2q(G_α) = 2 (k (2(q-p) + (b-a)) + 4k²)` for `W` of signature
`(p,q)` and `Z` of signature `(a,b)`, and `a + b = dim Z` is odd, so `q(G) - q(G_α) ≡ k mod 2`
(`realExponent_parity`).

**What the examples check.**  The numerical examples check the arithmetic of the formula on
signatures: the Witt index of a real form of signature `(p,q)` is taken to be `min(p,q)`, which is
not proved here.  `kottwitzSign_real` ties them to the definition: over `ℝ`, `kottwitzSign` is
`realSign` of the two values of `GGPData.symSpaceDim`.
-/

namespace GSpinGGP.KottwitzSignAudit

/-! ## The branches selected for `ℝ` and `ℂ` -/

theorem not_isSquare_neg_one_real : ¬ IsSquare (-1 : ℝ) := by
  rintro ⟨x, hx⟩
  nlinarith [mul_self_nonneg x]

/-- The real sign as a function of `2q(G)` and `2q(G_α)`. -/
def realSign (S S' : ℕ) : ℤ := if S % 4 = S' % 4 then 1 else -1

/-- Over `ℂ` the Kottwitz sign is `1` (Kottwitz 1983, p. 290). -/
theorem kottwitzSign_complex (d : GGPData ℂ) (τ : InnerTwist d.QW) : kottwitzSign d τ = 1 :=
  kottwitzSign_of_isSquare not_isUltrametricDist_complex (IsAlgClosed.isSquare _) d τ

/-- Over `ℝ` the Kottwitz sign is `realSign (2q(G)) (2q(G_α))`. -/
theorem kottwitzSign_real (d : GGPData ℝ) (τ : InnerTwist d.QW) :
    kottwitzSign d τ = realSign d.symSpaceDim (d.twist τ).symSpaceDim :=
  kottwitzSign_of_not_isSquare not_isUltrametricDist_real not_isSquare_neg_one_real d τ

/-! ## The arithmetic of the real formula -/

/-- `w (n - w) = pq` for `w = min(p,q)`, `n = p + q`. -/
example (p q : ℕ) : min p q * (p + q - min p q) = p * q := by
  rw [← min_add_max p q, Nat.add_sub_cancel_left, min_mul_max]

/-- `W` of signature `(p,q)`, `Z` of signature `(a,b)`, and the twist `W_α` of signature
`(p - 2k, q + 2k)`: `2q(G) - 2q(G_α)` is twice `k (2(q-p) + (b-a)) + 4k²`. -/
theorem two_mul_realExponent (p q a b k : ℤ) :
    (p * q + (p + a) * (q + b)) - ((p - 2 * k) * (q + 2 * k) + (p + a - 2 * k) * (q + b + 2 * k)) =
      2 * (k * (2 * (q - p) + (b - a)) + 4 * k ^ 2) := by
  ring

/-- `q(G) - q(G_α) ≡ k mod 2` when `dim Z = a + b` is odd. -/
theorem realExponent_parity (p q a b k : ℤ) (hab : Odd (a + b)) :
    Even (k * (2 * (q - p) + (b - a)) + 4 * k ^ 2 - k) := by
  obtain ⟨j, hj⟩ := hab
  have hb : b = 2 * j + 1 - a := by linarith
  subst hb
  exact ⟨k * (q - p) - k * a + j * k + 2 * k ^ 2, by ring⟩

/-! ## Worked examples (signatures; `w = min(p,q)`) -/

/-- `W = (2,0)`, `Z = ⟨-1⟩`, `V = (2,1)`, twisted to `W_α = (0,2)`, `V_α = (0,3)`
(`SO(2) × SO(2,1)` against `SO(2) × SO(3)`): `2q = 0 + 2` against `0 + 0`, sign `-1`. -/
example : realSign (min 2 0 * (2 - min 2 0) + min 2 1 * (3 - min 2 1))
    (min 0 2 * (2 - min 0 2) + min 0 3 * (3 - min 0 3)) = -1 := by decide

/-- `W = (4,0)`, `V = (5,0)` (compact) twisted to `W_α = (0,4)`, `V_α = (1,4)`: `k = 2`, sign `1`
although the twist is nontrivial. -/
example : realSign (min 4 0 * (4 - min 4 0) + min 5 0 * (5 - min 5 0))
    (min 0 4 * (4 - min 0 4) + min 1 4 * (5 - min 1 4)) = 1 := by decide

/-- `W = (3,0)`, `V = (4,0)` (compact) twisted to the quasi-split `W_α = (1,2)`, `V_α = (2,2)`:
`2q = 0` against `2 + 4`, sign `-1` (`q(G_α) = 3`). -/
example : realSign (min 3 0 * (3 - min 3 0) + min 4 0 * (4 - min 4 0))
    (min 1 2 * (3 - min 1 2) + min 2 2 * (4 - min 2 2)) = -1 := by decide

/-- `W = (3,2)`, `V = (4,2)` (quasi-split) twisted to `W_α = (5,0)`, `V_α = (6,0)`:
`2q = 6 + 8` against `0`, sign `-1`; here the parity of the sum of Witt indices,
`2 + 0 + 2 + 0`, is even, so the `p`-adic formula would give `1`. -/
example : realSign (min 3 2 * (5 - min 3 2) + min 4 2 * (6 - min 4 2))
    (min 5 0 * (5 - min 5 0) + min 6 0 * (6 - min 6 0)) = -1 := by decide

/-- A twist with the same signature has sign `1`. -/
example (S : ℕ) : realSign S S = 1 := by simp [realSign]

end GSpinGGP.KottwitzSignAudit
