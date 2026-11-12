/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.SoCentralizer

/-!
# Single-block nilpotent skew maps

Let `(V, q)` be a quadratic space over a field of characteristic `≠ 2`, and `N ∈ so(V)` nilpotent
with `N^{2k} ≠ 0` on a space of dimension `2k + 1` (one Jordan block).

* `bform_pow_pow`, `bform_pow_odd`: `b(N^i v, N^j v) = (-1)^i b(v, N^{i+j} v)`, and
  `b(v, N^j v) = 0` for `j` odd.
* `exists_normal_vector`: a cyclic vector `v` with `b(v, N^j v) = 0` for `j < 2k`;
  `bform_chain_normal`: then the Gram matrix of `v, N v, …, N^{2k} v` is anti-diagonal.
* `bform_top_ne_zero`: `b(v, N^{2k} v) ≠ 0` for a nondegenerate form.
* `eq_zero_of_finrank_le_two`: a nilpotent skew map in dimension `≤ 2` is `0`.
-/

noncomputable section

open Module

namespace GSpinGGP

namespace SingleBlock

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]

section Gram

variable {Q : QuadraticForm K V} {N : Module.End K V}

/-- `b(N^i v, N^j v) = (-1)^i b(v, N^{i+j} v)` for `N` skew. -/
theorem bform_pow_pow (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w)) (v : V) (i j : ℕ) :
    bform Q ((N ^ i) v) ((N ^ j) v) = (-1) ^ i * bform Q v ((N ^ (i + j)) v) := by
  have h := bform_pow_skew hN i v ((N ^ j) v)
  rw [← Module.End.mul_apply, ← pow_add] at h
  rw [h, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

/-- `b(v, N^j v) = 0` for `j` odd and `N` skew. -/
theorem bform_pow_odd (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w)) (v : V) {j : ℕ}
    (hj : Odd j) : bform Q v ((N ^ j) v) = 0 := by
  have h := bform_pow_skew hN j v v
  rw [hj.neg_one_pow, QuadraticMap.associated_isSymm K Q ((N ^ j) v) v] at h
  have h2 : (2 : K) * bform Q v ((N ^ j) v) = 0 := by
    change bform Q v ((N ^ j) v) = -1 * bform Q v ((N ^ j) v) at h
    linear_combination h
  exact (mul_eq_zero.1 h2).resolve_left (two_ne_zero' K)

/-- The effect of `v ↦ v + c N^{2m} v` on `β_l = b(v, N^l v)`. -/
theorem bform_shift (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w)) (v : V) (c : K)
    (m l : ℕ) :
    bform Q (v + c • (N ^ (2 * m)) v) ((N ^ l) (v + c • (N ^ (2 * m)) v)) =
      bform Q v ((N ^ l) v) + 2 * c * bform Q v ((N ^ (l + 2 * m)) v) +
        c ^ 2 * bform Q v ((N ^ (l + 4 * m)) v) := by
  have e1 : (N ^ l) ((N ^ (2 * m)) v) = (N ^ (l + 2 * m)) v := by
    rw [← Module.End.mul_apply, ← pow_add]
  have h1 := bform_pow_pow hN v (2 * m) l
  have h2 := bform_pow_pow hN v (2 * m) (l + 2 * m)
  have hs : ((-1 : K)) ^ (2 * m) = 1 := by rw [pow_mul]; simp
  rw [hs, one_mul] at h1 h2
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, e1, smul_eq_mul]
  rw [h1, h2, show 2 * m + l = l + 2 * m by ring, show 2 * m + (l + 2 * m) = l + 4 * m by ring]
  ring

end Gram


section Normal

variable {Q : QuadraticForm K V} {N : Module.End K V}

/-- **Normal form of a cyclic vector**: if `N` is skew, `N^{2k+1} = 0` and `b(v, N^{2k} v) ≠ 0`,
some `v'` has `b(v', N^l v') = 0` for all `l < 2k`, with `N^{2k} v'` and `b(v', N^{2k} v')`
unchanged (`v'` is `p(N) v` with `p(0) = 1`).  Kill `b(v, N^{2k-2m} v)`, `m = 1, …, k`, by `v ↦ v + c N^{2m} v`
(`bform_shift`), which leaves the higher `b(v, N^l v)` alone. -/
theorem exists_normal_vector (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w)) {k : ℕ}
    (hk : N ^ (2 * k + 1) = 0) (v : V) (hv : bform Q v ((N ^ (2 * k)) v) ≠ 0) :
    ∃ v' : V, (N ^ (2 * k)) v' = (N ^ (2 * k)) v ∧
      bform Q v' ((N ^ (2 * k)) v') = bform Q v ((N ^ (2 * k)) v) ∧
      ∀ l < 2 * k, bform Q v' ((N ^ l) v') = 0 := by
  have hz : ∀ l, 2 * k + 1 ≤ l → ∀ x, (N ^ l) x = 0 := fun l hl x => by
    rw [← Nat.add_sub_cancel' hl, pow_add, hk, zero_mul, LinearMap.zero_apply]
  suffices H : ∀ t ≤ k, ∃ v' : V, (N ^ (2 * k)) v' = (N ^ (2 * k)) v ∧
      bform Q v' ((N ^ (2 * k)) v') = bform Q v ((N ^ (2 * k)) v) ∧
      ∀ l, 2 * k - 2 * t ≤ l → l < 2 * k → bform Q v' ((N ^ l) v') = 0 by
    obtain ⟨v', h1, h2, h3⟩ := H k le_rfl
    exact ⟨v', h1, h2, fun l hl => h3 l (by omega) hl⟩
  intro t
  induction t with
  | zero => intro _; exact ⟨v, rfl, rfl, fun l h1 h2 => by omega⟩
  | succ t ih =>
    intro ht
    obtain ⟨v', h1, h2, h3⟩ := ih (by omega)
    set β := bform Q v ((N ^ (2 * k)) v) with hβ
    set c : K := -bform Q v' ((N ^ (2 * k - 2 * (t + 1))) v') / (2 * β) with hc
    refine ⟨v' + c • (N ^ (2 * (t + 1))) v', ?_, ?_, ?_⟩
    · rw [map_add, map_smul, ← Module.End.mul_apply, ← pow_add,
        hz (2 * k + 2 * (t + 1)) (by omega), smul_zero, add_zero, h1]
    · rw [bform_shift hN, hz (2 * k + 2 * (t + 1)) (by omega),
        hz (2 * k + 4 * (t + 1)) (by omega), map_zero, h2]
      ring
    · intro l hl1 hl2
      rcases Nat.even_or_odd l with he | ho
      · rw [bform_shift hN, hz (l + 4 * (t + 1)) (by omega), map_zero, mul_zero, add_zero]
        by_cases hl : l = 2 * k - 2 * (t + 1)
        · rw [show l + 2 * (t + 1) = 2 * k by omega, h2, hl, hc]
          field_simp
          ring
        · obtain ⟨r, hr⟩ := he
          rw [h3 l (by omega) hl2, hz (l + 2 * (t + 1)) (by omega), map_zero]
          ring
      · exact bform_pow_odd hN _ ho

end Normal

section Chain

variable [FiniteDimensional K V] {Q : QuadraticForm K V} {N : Module.End K V}

omit [Invertible (2 : K)] in
/-- A nilpotent `N` on a space of dimension `2k + 1` has `N^{2k+1} = 0` (Cayley–Hamilton). -/
theorem pow_eq_zero_of_finrank_eq {k : ℕ} (hdim : finrank K V = 2 * k + 1) (hn : IsNilpotent N) :
    N ^ (2 * k + 1) = 0 := by
  have := LinearMap.aeval_self_charpoly N
  rwa [hn.charpoly_eq_X_pow_finrank, map_pow, Polynomial.aeval_X, hdim] at this

/-- The chain basis `v, N v, …, N^{2k} v`. -/
def chainBasis {k : ℕ} (hdim : finrank K V = 2 * k + 1) (N : Module.End K V) {v : V}
    (hv : (N ^ (2 * k)) v ≠ 0) (hv' : (N ^ (2 * k + 1)) v = 0) : Basis (Fin (2 * k + 1)) K V :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_pow_apply hv hv')
    (by rw [Fintype.card_fin, hdim])

omit [Invertible (2 : K)] [FiniteDimensional K V] in
theorem chainBasis_apply {k : ℕ} (hdim : finrank K V = 2 * k + 1) {v : V}
    (hv : (N ^ (2 * k)) v ≠ 0) (hv' : (N ^ (2 * k + 1)) v = 0) (i : Fin (2 * k + 1)) :
    chainBasis hdim N hv hv' i = (N ^ (i : ℕ)) v := by
  simp [chainBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

omit [FiniteDimensional K V] in
/-- `b(v, N^{2k} v) ≠ 0` when `N^{2k} v ≠ 0` (nondegeneracy: `N^{2k} v` is orthogonal to
`N v, …, N^{2k} v`). -/
theorem bform_top_ne_zero (hQ : IsNondeg Q) (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w))
    {k : ℕ} (hdim : finrank K V = 2 * k + 1) (hk : N ^ (2 * k + 1) = 0) {v : V}
    (hv : (N ^ (2 * k)) v ≠ 0) : bform Q v ((N ^ (2 * k)) v) ≠ 0 := by
  intro h0
  have hv' : (N ^ (2 * k + 1)) v = 0 := by rw [hk, LinearMap.zero_apply]
  apply hv
  refine (isNondeg_iff Q).1 hQ _ fun y => ?_
  have : bform Q ((N ^ (2 * k)) v) = 0 := by
    refine (chainBasis hdim N hv hv').ext fun i => ?_
    rw [chainBasis_apply, bform_pow_pow hN, LinearMap.zero_apply]
    rcases Nat.eq_zero_or_pos (i : ℕ) with hi | hi
    · rw [hi, add_zero, h0, mul_zero]
    · rw [← Nat.add_sub_cancel' (show 2 * k + 1 ≤ 2 * k + i by omega), pow_add, hk, zero_mul,
        LinearMap.zero_apply, map_zero, mul_zero]
  rw [this, LinearMap.zero_apply]

omit [FiniteDimensional K V] in
/-- Gram matrix of a normalized chain: `b(N^i v, N^j v) = (-1)^i β δ_{i+j, 2k}`. -/
theorem bform_chain_normal (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w)) {k : ℕ}
    (hk : N ^ (2 * k + 1) = 0) {v : V} (hnorm : ∀ l < 2 * k, bform Q v ((N ^ l) v) = 0)
    (i j : ℕ) :
    bform Q ((N ^ i) v) ((N ^ j) v) =
      if i + j = 2 * k then (-1) ^ i * bform Q v ((N ^ (2 * k)) v) else 0 := by
  rw [bform_pow_pow hN]
  split_ifs with h
  · rw [h]
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · rw [hnorm _ h', mul_zero]
    · rw [← Nat.add_sub_cancel' (show 2 * k + 1 ≤ i + j by omega), pow_add, hk, zero_mul,
        LinearMap.zero_apply, map_zero, mul_zero]

/-- The anti-diagonal sign matrix `M₀ i j = (-1)^i δ_{i+j, 2k}`. -/
def antiDiag (k : ℕ) : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) K :=
  Matrix.of fun i j => if (i : ℕ) + j = 2 * k then (-1) ^ (i : ℕ) else 0


end Chain

section Small

variable [FiniteDimensional K V] {Q : QuadraticForm K V}

/-- **A nilpotent skew map in dimension `≤ 2` is `0`** (`so(V)` is `0` or a torus): if `N v ≠ 0`
then `v, N v` is a basis, `N² v = 0`, and `N v` is orthogonal to both. -/
theorem eq_zero_of_finrank_le_two (hQ : IsNondeg Q) (hdim : finrank K V ≤ 2)
    {N : Module.End K V} (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w)) (hn : IsNilpotent N) :
    N = 0 := by
  by_contra h0
  obtain ⟨v, hv⟩ : ∃ v, N v ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (LinearMap.ext h)
  have hv1 : (N ^ 1) v ≠ 0 := by rwa [pow_one]
  obtain ⟨m, hm, h1, h2⟩ := exists_pow_apply_ne_zero_of_isNilpotent hn hv1
  have hli := linearIndependent_pow_apply h1 h2
  have hle := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at hle
  have hm1 : m = 1 := by omega
  subst hm1
  have hcard : Fintype.card (Fin 2) = finrank K V := by rw [Fintype.card_fin]; omega
  set b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  apply hv
  refine (isNondeg_iff Q).1 hQ _ fun y => ?_
  have : bform Q (N v) = 0 := by
    refine b.ext fun i => ?_
    rw [show b i = (N ^ (i : ℕ)) v by simp [b, coe_basisOfLinearIndependentOfCardEqFinrank],
      LinearMap.zero_apply]
    have := bform_pow_pow hN v 1 i
    rw [pow_one] at this
    rw [this]
    obtain ⟨i, hi⟩ := i
    interval_cases i
    · show (-1) ^ 1 * bform Q v ((N ^ (1 + 0)) v) = 0
      rw [bform_pow_odd hN v (by decide : Odd (1 + 0)), mul_zero]
    · show (-1) ^ 1 * bform Q v ((N ^ (1 + 1)) v) = 0
      rw [h2, map_zero, mul_zero]
  rw [this, LinearMap.zero_apply]

end Small

end SingleBlock

end GSpinGGP
