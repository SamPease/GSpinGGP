/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.QuadClassify
import GSpinGGP.Foundations.SoCentralizer
import TauCeti.LinearAlgebra.QuadraticForm.Witt.Extension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
import TauCeti.LinearAlgebra.BilinearForm.Isometry

/-!
# Rational classification of single-block nilpotent skew maps and of the orbit `O_ν`

Let `(V, q)` be a nondegenerate quadratic space of odd dimension `2k + 1` over a field of
characteristic `≠ 2`, and `N ∈ so(V)` nilpotent with `N^{2k} ≠ 0` (one Jordan block).

* `exists_normal_vector`: there is `v` with `b(v, N^j v) = 0` for `j < 2k` (and `b(v, N^{2k} v) ≠ 0`,
  `bform_top_ne_zero`); in the basis `v, N v, …, N^{2k} v` the Gram matrix is `β · antiDiag k`
  (`gdet_chainBasis`).
* `exists_isometryEquiv_conj_of_pow_ne_zero`: two such pairs `(V₁, N₁)`, `(V₂, N₂)` with `V₁ ≅ V₂`
  are isometric: `β₂/β₁` is a square since `β^{2k+1}` is the Gram determinant up to a constant.
* `exists_isometry_det_one_conj_of_pow_ne_zero`: on one space the isometry can be taken in `SO(V)`
  (compose with `−1`, which commutes with `N` and has determinant `−1`).
* `exists_isometry_det_one_conj_of_isInOrbitNu`: Luo's orbit `O_ν` (`IsInOrbitNu`, after
  Waldspurger 2010 §7.1 / Luo §2.1) on a space of dimension `2k + 2` is a single `SO(V)`-orbit.
* `eq_zero_of_finrank_le_two`: a nilpotent skew map in dimension `≤ 2` is `0`.
* `exists_isometry_det_one_conj_of_pow_ne_zero_sub`, `exists_isometry_det_one_conj_of_isInOrbitNu_sub`:
  the same on an orthogonal summand `U` of `V = U ⊥ B`, by an element of `SO(V)` fixing `B` pointwise
  (`extendById`).
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
some `v' = p(N) v` (`p(0) = 1`) has `b(v', N^l v') = 0` for all `l < 2k`, with `N^{2k} v'` and
`b(v', N^{2k} v')` unchanged.  Kill `b(v, N^{2k-2m} v)`, `m = 1, …, k`, by `v ↦ v + c N^{2m} v`
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
/-- A nilpotent `N` with `N^{2k} v ≠ 0` on a space of dimension `2k + 1` has `N^{2k+1} = 0`. -/
theorem pow_succ_eq_zero {k : ℕ} (hdim : finrank K V = 2 * k + 1) (hn : IsNilpotent N) {v : V}
    (hv : (N ^ (2 * k)) v ≠ 0) : (N ^ (2 * k + 1)) v = 0 := by
  obtain ⟨k', hk', h1, h2⟩ := exists_pow_apply_ne_zero_of_isNilpotent hn hv
  have hle := (linearIndependent_pow_apply h1 h2).fintype_card_le_finrank
  rw [Fintype.card_fin, hdim] at hle
  rwa [show 2 * k = k' by omega]

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

omit [Invertible (2 : K)] in
/-- A nilpotent `N` with `N^{2k} ≠ 0` on a space of dimension `2k + 1` has `N^{2k+1} = 0`. -/
theorem pow_eq_zero_of_pow_ne_zero {k : ℕ} (hdim : finrank K V = 2 * k + 1) (hn : IsNilpotent N)
    {v : V} (hv : (N ^ (2 * k)) v ≠ 0) : N ^ (2 * k + 1) = 0 := by
  have hv' := pow_succ_eq_zero hdim hn hv
  refine (chainBasis hdim N hv hv').ext fun i => ?_
  rw [chainBasis_apply, ← Module.End.mul_apply, ← pow_add, add_comm, pow_add,
    Module.End.mul_apply, hv', map_zero, LinearMap.zero_apply]

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

omit [FiniteDimensional K V] in
/-- The Gram determinant of a normalized chain basis is `β^{2k+1} det M₀`. -/
theorem gdet_chainBasis {k : ℕ} (hdim : finrank K V = 2 * k + 1)
    (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w)) (hk : N ^ (2 * k + 1) = 0) {x : V}
    (hx : (N ^ (2 * k)) x ≠ 0) (hx' : (N ^ (2 * k + 1)) x = 0)
    (hnorm : ∀ l < 2 * k, bform Q x ((N ^ l) x) = 0) :
    QuadClassify.gdet Q (chainBasis hdim N hx hx') =
      bform Q x ((N ^ (2 * k)) x) ^ (2 * k + 1) * (antiDiag k).det := by
  have : QuadraticForm.toMatrix (chainBasis hdim N hx hx') Q =
      bform Q x ((N ^ (2 * k)) x) • antiDiag k := by
    ext i j
    simp only [QuadraticForm.toMatrix, LinearMap.toMatrix₂_apply, chainBasis_apply, antiDiag,
      Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [bform_chain_normal hN hk hnorm _ _]
    split_ifs <;> ring
  unfold QuadClassify.gdet
  rw [this, Matrix.det_smul, Fintype.card_fin]

end Chain

section Iso

variable [FiniteDimensional K V] {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
  [FiniteDimensional K V₂]

open QuadClassify in
/-- **Single-block nilpotent skew maps on isometric spaces are conjugate.**  If `(V, q) ≅ (V₂, q₂)`
are nondegenerate of dimension `2k + 1` and `N, N₂` are nilpotent skew with `N^{2k}, N₂^{2k} ≠ 0`,
some isometry `φ : V ≅ V₂` has `φ N = N₂ φ`.  Normalize cyclic vectors `v, w`
(`exists_normal_vector`): the Gram matrices are `β M₀` and `β₂ M₀`, so comparing Gram
determinants `β₂^{2k+1} = D² β^{2k+1}` and `β/β₂` is a square `a²`; then `N^i v ↦ N₂^i (a w)`. -/
theorem exists_isometryEquiv_conj_of_pow_ne_zero {Q : QuadraticForm K V}
    {Q₂ : QuadraticForm K V₂} (hQ : IsNondeg Q) (I : Q.IsometryEquiv Q₂) {k : ℕ}
    (hdim : finrank K V = 2 * k + 1) {N : Module.End K V} {N₂ : Module.End K V₂}
    (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w))
    (hN₂ : ∀ u w, bform Q₂ (N₂ u) w = -bform Q₂ u (N₂ w))
    (hn : IsNilpotent N) (hn₂ : IsNilpotent N₂) (hp : N ^ (2 * k) ≠ 0)
    (hp₂ : N₂ ^ (2 * k) ≠ 0) :
    ∃ φ : Q.IsometryEquiv Q₂, ∀ x, φ (N x) = N₂ (φ x) := by
  classical
  have hdim₂ : finrank K V₂ = 2 * k + 1 := I.toLinearEquiv.finrank_eq.symm.trans hdim
  have hQ₂ : IsNondeg Q₂ := (DiscRel.of_isometryEquiv I).isNondeg hQ
  obtain ⟨v₀, hv₀⟩ : ∃ v, (N ^ (2 * k)) v ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (LinearMap.ext h)
  obtain ⟨w₀, hw₀⟩ : ∃ w, (N₂ ^ (2 * k)) w ≠ 0 := by
    by_contra h
    push Not at h
    exact hp₂ (LinearMap.ext h)
  have hk := pow_eq_zero_of_pow_ne_zero hdim hn hv₀
  have hk₂ := pow_eq_zero_of_pow_ne_zero hdim₂ hn₂ hw₀
  obtain ⟨v, hv1, -, hv3⟩ := exists_normal_vector hN hk v₀ (bform_top_ne_zero hQ hN hdim hk hv₀)
  obtain ⟨w, hw1, -, hw3⟩ :=
    exists_normal_vector hN₂ hk₂ w₀ (bform_top_ne_zero hQ₂ hN₂ hdim₂ hk₂ hw₀)
  have hv : (N ^ (2 * k)) v ≠ 0 := hv1 ▸ hv₀
  have hw : (N₂ ^ (2 * k)) w ≠ 0 := hw1 ▸ hw₀
  have hz : ∀ l, 2 * k + 1 ≤ l → ∀ x, (N ^ l) x = 0 := fun l hl x => by
    rw [← Nat.add_sub_cancel' hl, pow_add, hk, zero_mul, LinearMap.zero_apply]
  have hz₂ : ∀ l, 2 * k + 1 ≤ l → ∀ x, (N₂ ^ l) x = 0 := fun l hl x => by
    rw [← Nat.add_sub_cancel' hl, pow_add, hk₂, zero_mul, LinearMap.zero_apply]
  set β := bform Q v ((N ^ (2 * k)) v) with hβdef
  set β₂ := bform Q₂ w ((N₂ ^ (2 * k)) w) with hβ₂def
  have hβ : β ≠ 0 := bform_top_ne_zero hQ hN hdim hk hv
  have hβ₂ : β₂ ≠ 0 := bform_top_ne_zero hQ₂ hN₂ hdim₂ hk₂ hw
  -- Gram determinants
  set M₀ := antiDiag (K := K) k
  set b := chainBasis hdim N hv (by rw [hk, LinearMap.zero_apply]) with hb
  set b₂ := chainBasis hdim₂ N₂ hw (by rw [hk₂, LinearMap.zero_apply]) with hb₂
  have hd1 := gdet_chainBasis hdim hN hk hv (by rw [hk, LinearMap.zero_apply]) hv3
  have hd2 := gdet_chainBasis hdim₂ hN₂ hk₂ hw (by rw [hk₂, LinearMap.zero_apply]) hw3
  have hch := gdet_change Q₂ (b.map I.toLinearEquiv) b₂
  rw [gdet_map_isometry] at hch
  set D := ((b.map I.toLinearEquiv).toMatrix b₂).det
  have hD : D ≠ 0 := det_basis_toMatrix_ne_zero _ _
  have hne : gdet Q b ≠ 0 := (isNondeg_iff_gdet_ne_zero Q b).1 hQ
  have hM₀ne : M₀.det ≠ 0 := right_ne_zero_of_mul (hd1 ▸ hne)
  have hpow : β₂ ^ (2 * k + 1) = D ^ 2 * β ^ (2 * k + 1) := by
    apply mul_right_cancel₀ hM₀ne
    rw [← hd2, hch, hd1]
    ring
  -- the square root `a` of `β / β₂`
  set r := β / β₂ with hr
  have hr0 : r ≠ 0 := div_ne_zero hβ hβ₂
  set a := D⁻¹ / r ^ k with ha
  have ha0 : a ≠ 0 := div_ne_zero (inv_ne_zero hD) (pow_ne_zero _ hr0)
  have ha2 : a ^ 2 * β₂ = β := by
    have hr' : D ^ 2 * r ^ (2 * k + 1) = 1 := by
      rw [hr, div_pow, hpow]
      field_simp
    have hrk : r ^ (2 * k) ≠ 0 := pow_ne_zero _ hr0
    have : a ^ 2 = r := by
      rw [ha, div_pow, inv_pow, ← pow_mul, show k * 2 = 2 * k by ring]
      field_simp
      linear_combination -hr'
    rw [this, hr]
    field_simp
  -- the rescaled cyclic vector
  set w' := a • w with hw'
  have hw'1 : (N₂ ^ (2 * k)) w' ≠ 0 := by
    rw [hw', map_smul]
    exact smul_ne_zero ha0 hw
  have hw'2 : (N₂ ^ (2 * k + 1)) w' = 0 := by rw [hk₂, LinearMap.zero_apply]
  have hw'b : ∀ l, bform Q₂ w' ((N₂ ^ l) w') = a ^ 2 * bform Q₂ w ((N₂ ^ l) w) := fun l => by
    simp only [hw', map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hw'3 : ∀ l < 2 * k, bform Q₂ w' ((N₂ ^ l) w') = 0 := fun l hl => by
    rw [hw'b, hw3 l hl, mul_zero]
  set b₂' := chainBasis hdim₂ N₂ hw'1 hw'2
  set φ : V ≃ₗ[K] V₂ := b.equiv b₂' (Equiv.refl _) with hφ
  have hφpow : ∀ j : ℕ, φ ((N ^ j) v) = (N₂ ^ j) w' := fun j => by
    by_cases hj : j ≤ 2 * k
    · have h1 : (N ^ j) v = b ⟨j, by omega⟩ := by rw [hb, chainBasis_apply]
      have h2 : (N₂ ^ j) w' = b₂' ⟨j, by omega⟩ := by rw [chainBasis_apply]
      rw [h1, h2, hφ, Basis.equiv_apply, Equiv.refl_apply]
    · rw [hz j (by omega), hz₂ j (by omega), map_zero]
  have hφb : ∀ x y, bform Q₂ (φ x) (φ y) = bform Q x y := by
    have : (bform Q₂).compl₁₂ (φ : V →ₗ[K] V₂) (φ : V →ₗ[K] V₂) = bform Q := by
      refine LinearMap.BilinForm.ext_basis b fun i j => ?_
      simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
      rw [hb, chainBasis_apply, chainBasis_apply, hφpow, hφpow,
        bform_chain_normal hN₂ hk₂ hw'3 _ _,
        bform_chain_normal hN hk hv3 _ _, hw'b, ha2]
    intro x y
    exact LinearMap.congr_fun₂ this x y
  refine ⟨⟨φ, fun x => ?_⟩, fun x => ?_⟩
  · rw [← QuadraticMap.associated_eq_self_apply K Q₂, ← QuadraticMap.associated_eq_self_apply K Q]
    exact hφb x x
  · change φ (N x) = N₂ (φ x)
    have : (φ : V →ₗ[K] V₂) ∘ₗ N = N₂ ∘ₗ (φ : V →ₗ[K] V₂) := by
      refine b.ext fun i => ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hb, chainBasis_apply, ← Module.End.mul_apply, ← pow_succ', hφpow, hφpow,
        ← Module.End.mul_apply, ← pow_succ']
    exact LinearMap.congr_fun this x

/-- An isometry of a nondegenerate space has determinant `±1`. -/
theorem det_isometryEquiv_eq_one_or {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    (g : Q.IsometryEquiv Q) :
    LinearMap.det (g.toLinearEquiv : V →ₗ[K] V) = 1 ∨
      LinearMap.det (g.toLinearEquiv : V →ₗ[K] V) = -1 := by
  have hB : (bform Q).SeparatingLeft := fun w hw => hQ.1 w hw
  have hi : TauCeti.BilinForm.IsIsometry (bform Q) (g.toLinearEquiv : V →ₗ[K] V) :=
    fun u v => bform_isometry g.toIsometry u v
  have hsq := hi.det_sq_eq_one (Module.Free.chooseBasis K V)
    (mem_nonZeroDivisors_of_ne_zero ((LinearMap.separatingLeft_iff_det_ne_zero _).mp hB))
  exact sq_eq_one_iff.1 hsq

/-- `−1` as an isometry. -/
def negIsometry (Q : QuadraticForm K V) : Q.IsometryEquiv Q where
  toLinearEquiv := LinearEquiv.neg K
  map_app' x := QuadraticMap.map_neg Q x

/-- **Single-block nilpotent skew maps are `SO(V)`-conjugate**: as
`exists_isometryEquiv_conj_of_pow_ne_zero` on one space, corrected by `−1` (central, determinant
`−1` in odd dimension). -/
theorem exists_isometry_det_one_conj_of_pow_ne_zero {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    {k : ℕ} (hdim : finrank K V = 2 * k + 1) {N N' : Module.End K V}
    (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w))
    (hN' : ∀ u w, bform Q (N' u) w = -bform Q u (N' w))
    (hn : IsNilpotent N) (hn' : IsNilpotent N') (hp : N ^ (2 * k) ≠ 0) (hp' : N' ^ (2 * k) ≠ 0) :
    ∃ g : Q.IsometryEquiv Q, LinearMap.det (g.toLinearEquiv : V →ₗ[K] V) = 1 ∧
      ∀ x, g (N x) = N' (g x) := by
  obtain ⟨φ, hφ⟩ := exists_isometryEquiv_conj_of_pow_ne_zero hQ (QuadraticMap.IsometryEquiv.refl Q)
    hdim hN hN' hn hn' hp hp'
  rcases det_isometryEquiv_eq_one_or hQ φ with h | h
  · exact ⟨φ, h, hφ⟩
  · refine ⟨φ.trans (negIsometry Q), ?_, fun x => ?_⟩
    · have hneg : ((negIsometry Q).toLinearEquiv : V →ₗ[K] V) = (-1 : K) • LinearMap.id := by
        ext x; simp [negIsometry]
      change LinearMap.det (((negIsometry Q).toLinearEquiv : V →ₗ[K] V) ∘ₗ
        (φ.toLinearEquiv : V →ₗ[K] V)) = 1
      rw [LinearMap.det_comp, hneg, LinearMap.det_smul, LinearMap.det_id, h, hdim]
      rw [pow_succ, pow_mul]
      simp
    · change -(φ (N x)) = N' (-(φ x))
      rw [hφ, map_neg]

end Iso

section Orth

variable {Q : QuadraticForm K V}

/-- An orthogonal summand of a subspace `U` without radical has no radical. -/
theorem isNondeg_comp_of_sup {U A B : Submodule K V}
    (hU : ∀ x ∈ U, (∀ y ∈ U, bform Q x y = 0) → x = 0) (hAB : A ⊔ B = U)
    (horth : ∀ a ∈ A, ∀ b ∈ B, bform Q a b = 0) : IsNondeg (Q.comp A.subtype) := by
  have hAU : A ≤ U := hAB ▸ le_sup_left
  refine (isNondeg_iff _).2 fun x hx => Subtype.ext (hU x (hAU x.2) fun y hy => ?_)
  rw [← hAB] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add, horth _ x.2 _ hb, add_zero]
  have := hx ⟨a, ha⟩
  rwa [bform_comp_subtype] at this

/-- A subspace `U` with `IsNondeg (Q|_U)` has no radical. -/
theorem radical_free_of_isNondeg {U : Submodule K V} (hU : IsNondeg (Q.comp U.subtype)) :
    ∀ x ∈ U, (∀ y ∈ U, bform Q x y = 0) → x = 0 := fun x hx h => by
  have := (isNondeg_iff _).1 hU ⟨x, hx⟩ fun y => by rw [bform_comp_subtype]; exact h y y.2
  exact congrArg Subtype.val this

/-- `A ⊔ B ≅ A ⊥ B` for orthogonal `A, B` with `A ⊓ B = 0`. -/
def orthSupIso {A B : Submodule K V} (hd : Disjoint A B)
    (horth : ∀ a ∈ A, ∀ b ∈ B, bform Q a b = 0) :
    ((Q.comp A.subtype).prod (Q.comp B.subtype)).IsometryEquiv (Q.comp (A ⊔ B).subtype) where
  toLinearEquiv := LinearEquiv.ofBijective
    ((Submodule.inclusion le_sup_left).coprod (Submodule.inclusion le_sup_right)) ⟨by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      rintro ⟨a, b⟩ h
      rw [LinearMap.mem_ker, LinearMap.coprod_apply] at h
      have h' : (a : V) + b = 0 := congrArg Subtype.val h
      have hb : (b : V) ∈ A := by
        rw [eq_neg_of_add_eq_zero_right h']
        exact A.neg_mem a.2
      have hb0 : (b : V) = 0 := (Submodule.disjoint_def.1 hd) _ hb b.2
      have ha0 : (a : V) = 0 := by rw [eq_neg_of_add_eq_zero_left h', hb0, neg_zero]
      exact Prod.ext (Subtype.ext ha0) (Subtype.ext hb0), by
      rintro ⟨x, hx⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩⟩
  map_app' p := by
    change Q ((p.1 : V) + (p.2 : V)) = Q p.1 + Q p.2
    rw [QuadraticMap.map_add Q, polar_eq_two_mul_bform, horth _ p.1.2 _ p.2.2, mul_zero, add_zero]

/-- Equal subspaces carry isometric forms. -/
def isoOfEq {A B : Submodule K V} (h : A = B) :
    (Q.comp A.subtype).IsometryEquiv (Q.comp B.subtype) where
  toLinearEquiv := LinearEquiv.ofEq A B h
  map_app' _ := rfl

/-- Lines spanned by vectors of the same length are isometric. -/
def lineIso {e e' : V} (he : e ≠ 0) (he' : e' ≠ 0) (hQ : Q e = Q e') :
    (Q.comp (K ∙ e).subtype).IsometryEquiv (Q.comp (K ∙ e').subtype) where
  toLinearEquiv := (LinearEquiv.toSpanNonzeroSingleton K V e he).symm.trans
    (LinearEquiv.toSpanNonzeroSingleton K V e' he')
  map_app' x := by
    set c := (LinearEquiv.toSpanNonzeroSingleton K V e he).symm x
    have hx : x = LinearEquiv.toSpanNonzeroSingleton K V e he c := by
      rw [LinearEquiv.apply_symm_apply]
    change Q ((LinearEquiv.toSpanNonzeroSingleton K V e' he' c : K ∙ e') : V) = Q (x : V)
    rw [hx, LinearEquiv.toSpanNonzeroSingleton_apply, LinearEquiv.toSpanNonzeroSingleton_apply]
    simp only [QuadraticMap.map_smul, hQ]

/-- Nondegenerate split forms of the same even dimension are isometric (both are `H^k`). -/
theorem nonempty_isometryEquiv_of_split {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁]
    [FiniteDimensional K V₁] [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
    {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} (h₁ : IsNondeg Q₁) (h₂ : IsNondeg Q₂)
    (hs₁ : IsSplitQF Q₁) (hs₂ : IsSplitQF Q₂) (hd : finrank K V₁ = finrank K V₂)
    (he : Even (finrank K V₁)) : Nonempty (Q₁.IsometryEquiv Q₂) := by
  obtain ⟨k₁, Qa₁, -, ⟨I₁⟩, hk₁⟩ := witt_decomposition Q₁ h₁
  obtain ⟨k₂, Qa₂, -, ⟨I₂⟩, hk₂⟩ := witt_decomposition Q₂ h₂
  unfold IsSplitQF at hs₁ hs₂
  obtain ⟨t, ht⟩ := he
  have h1 : k₁ = 0 := by omega
  have h2 : k₂ = 0 := by omega
  have hw : wittIndex Q₂ = wittIndex Q₁ := by omega
  subst h1 h2
  rw [hw] at I₂
  have : Qa₁ = Qa₂ := by
    ext x
    rw [Subsingleton.elim x 0, QuadraticMap.map_zero, QuadraticMap.map_zero]
  subst this
  exact ⟨I₁.trans I₂.symm⟩

end Orth

section OrbitNuAux

variable [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
/-- `x ∈ (K e)^⊥` iff `b(e, x) = 0`. -/
theorem mem_orthogonal_span_singleton {e x : V} :
    x ∈ (bform Q).orthogonal (K ∙ e) ↔ bform Q e x = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h; exact h e (Submodule.mem_span_singleton_self e)
  · intro h n hn
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hn
    change bform Q (c • e) x = 0
    rw [LinearMap.map_smul₂, h, smul_zero]

omit [FiniteDimensional K V] in
/-- An anisotropic vector `e ∈ U` splits `U = K e ⊥ (U ∩ e^⊥)`. -/
theorem span_sup_inf_orthogonal {U : Submodule K V} {e : V} (he : e ∈ U) (hQe : Q e ≠ 0) :
    (K ∙ e) ⊔ (U ⊓ (bform Q).orthogonal (K ∙ e)) = U ∧
      Disjoint (K ∙ e) (U ⊓ (bform Q).orthogonal (K ∙ e)) ∧
      ∀ a ∈ K ∙ e, ∀ b ∈ U ⊓ (bform Q).orthogonal (K ∙ e), bform Q a b = 0 := by
  have hee : bform Q e e = Q e := QuadraticMap.associated_eq_self_apply K Q e
  have horth : ∀ a ∈ K ∙ e, ∀ b ∈ U ⊓ (bform Q).orthogonal (K ∙ e), bform Q a b = 0 := by
    intro a ha b hb
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
    rw [LinearMap.map_smul₂, mem_orthogonal_span_singleton.1 hb.2,
      smul_zero]
  refine ⟨le_antisymm (sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 he) inf_le_left)
    fun u hu => ?_, ?_, horth⟩
  · set c := bform Q e u / Q e
    rw [show u = c • e + (u - c • e) by abel]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))
      ⟨U.sub_mem hu (U.smul_mem _ he), mem_orthogonal_span_singleton.2 ?_⟩
    rw [map_sub, map_smul, hee, smul_eq_mul]
    simp only [c, div_mul_cancel₀ _ hQe, sub_self]
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have := mem_orthogonal_span_singleton.1 hx'.2
    rw [map_smul, hee, smul_eq_mul] at this
    rw [(mul_eq_zero.1 this).resolve_right hQe, zero_smul]

omit [Invertible (2 : K)] in
/-- `finrank (A ⊔ B) = finrank A + finrank B` for `A ⊓ B = 0`. -/
theorem finrank_sup_of_disjoint {A B : Submodule K V} (hd : Disjoint A B) :
    finrank K ↥(A ⊔ B) = finrank K A + finrank K B := by
  have := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hd.eq_bot, finrank_bot, add_zero] at this
  exact this

omit [FiniteDimensional K V] in
/-- The restriction of a skew map to an invariant subspace is skew. -/
theorem skew_restrict {N : Module.End K V} (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w))
    {U : Submodule K V} (hNU : ∀ u ∈ U, N u ∈ U) :
    ∀ u w : U, bform (Q.comp U.subtype) (N.restrict hNU u) w =
      -bform (Q.comp U.subtype) u (N.restrict hNU w) := fun u w => by
  simp only [bform_comp_subtype, LinearMap.coe_restrict_apply]
  exact hN u w

end OrbitNuAux

section OrbitNu

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
variable {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W] {Q : QuadraticForm F W}

/-- The data of `IsInOrbitNu Q ⊤ ν N` (`W = F d₀ ⊥ U₁`, `U₁ = F e ⊥ S`), with the consequences of
nondegeneracy and the dimension count. -/
theorem isInOrbitNu_top_data (hQ : IsNondeg Q) {k : ℕ} (hdim : finrank F W = 2 * k + 2) {ν : F}
    (hν : ν ≠ 0) {N : Module.End F W} (h : IsInOrbitNu Q ⊤ ν N) :
    ∃ (d₀ : W) (U₁ : Submodule F W) (e : W),
      Q d₀ ≠ 0 ∧ (∀ u ∈ U₁, bform Q d₀ u = 0) ∧ (F ∙ d₀) ⊔ U₁ = ⊤ ∧ N d₀ = 0 ∧
      (∀ u ∈ U₁, N u ∈ U₁) ∧ (∃ u ∈ U₁, (N ^ (2 * k)) u ≠ 0) ∧
      IsNondeg (Q.comp U₁.subtype) ∧ finrank F U₁ = 2 * k + 1 ∧
      e ∈ U₁ ∧ Q e = ν ∧ IsSplitQF (Q.comp (U₁ ⊓ (bform Q).orthogonal (F ∙ e)).subtype) ∧
      IsNondeg (Q.comp (U₁ ⊓ (bform Q).orthogonal (F ∙ e)).subtype) ∧
      finrank F ↥(U₁ ⊓ (bform Q).orthogonal (F ∙ e)) = 2 * k := by
  obtain ⟨d₀, U₁, -, hd, -, horth, hspan, hNd, hNU, ⟨u, hu, hpow⟩, e, he, hQe, hsplit⟩ := h
  have hd0 : d₀ ≠ 0 := fun h0 => hd (by rw [h0, QuadraticMap.map_zero])
  have hee : bform Q d₀ d₀ = Q d₀ := QuadraticMap.associated_eq_self_apply F Q d₀
  have hdisj : Disjoint (F ∙ d₀) U₁ := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have := horth _ hx'
    rw [map_smul, hee, smul_eq_mul] at this
    rw [(mul_eq_zero.1 this).resolve_right hd, zero_smul]
  have hdimU : finrank F U₁ = 2 * k + 1 := by
    have := finrank_sup_of_disjoint hdisj
    rw [hspan, finrank_top, _root_.finrank_span_singleton hd0, hdim] at this
    omega
  have hrad : ∀ x ∈ (⊤ : Submodule F W), (∀ y ∈ (⊤ : Submodule F W), bform Q x y = 0) → x = 0 :=
    fun x _ hx => (isNondeg_iff Q).1 hQ x fun y => hx y trivial
  have hU₁ : IsNondeg (Q.comp U₁.subtype) := by
    refine isNondeg_comp_of_sup hrad (by rw [sup_comm]; exact hspan) fun a ha b hb => ?_
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
    rw [map_smul, QuadraticMap.associated_isSymm F Q a d₀, horth a ha, smul_zero]
  have hQe0 : Q e ≠ 0 := by rw [hQe]; exact hν
  have he0 : e ≠ 0 := fun h0 => hQe0 (by rw [h0, QuadraticMap.map_zero])
  obtain ⟨hS1, hS2, hS3⟩ := span_sup_inf_orthogonal (Q := Q) he hQe0
  have hSnd : IsNondeg (Q.comp (U₁ ⊓ (bform Q).orthogonal (F ∙ e)).subtype) := by
    refine isNondeg_comp_of_sup (radical_free_of_isNondeg hU₁) (by rw [sup_comm]; exact hS1)
      fun a ha b hb => ?_
    rw [QuadraticMap.associated_isSymm F Q a b]
    exact hS3 b hb a ha
  have hSdim : finrank F ↥(U₁ ⊓ (bform Q).orthogonal (F ∙ e)) = 2 * k := by
    have := finrank_sup_of_disjoint hS2
    rw [hS1, _root_.finrank_span_singleton he0, hdimU] at this
    omega
  refine ⟨d₀, U₁, e, hd, horth, hspan, hNd, hNU, ⟨u, hu, ?_⟩, hU₁, hdimU, he, hQe, hsplit, hSnd,
    hSdim⟩
  rwa [hdimU, show 2 * k + 1 - 1 = 2 * k by omega] at hpow

/-- **The orbit `O_ν` is a single `SO(W)`-orbit** (Waldspurger 2010 §7.1; Luo §2.1): on a
nondegenerate `W` of dimension `2k + 2`, two nilpotent skew maps in `O_ν` (`IsInOrbitNu Q ⊤ ν`) are
conjugate under `SO(W)`.  Both `U₁ = F e ⊥ S` are `⟨ν⟩ ⊥ H^k`; the single blocks on `U₁, U₁'` are
conjugate by an isometry (`exists_isometryEquiv_conj_of_pow_ne_zero`), which extends to `W`
(Witt) and then carries `d₀` to a multiple of `d₀'`; the reflection in `d₀'` commutes with `N'`
and fixes the determinant. -/
theorem exists_isometry_det_one_conj_of_isInOrbitNu (hQ : IsNondeg Q) {k : ℕ}
    (hdim : finrank F W = 2 * k + 2) {ν : F} (hν : ν ≠ 0) {N N' : Module.End F W}
    (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w))
    (hN' : ∀ u w, bform Q (N' u) w = -bform Q u (N' w))
    (hn : IsNilpotent N) (hn' : IsNilpotent N') (h : IsInOrbitNu Q ⊤ ν N)
    (h' : IsInOrbitNu Q ⊤ ν N') :
    ∃ g : Q.IsometryEquiv Q, LinearMap.det (g.toLinearEquiv : W →ₗ[F] W) = 1 ∧
      ∀ x, g (N x) = N' (g x) := by
  classical
  obtain ⟨d₀, U₁, e, hd, horth, hspan, hNd, hNU, ⟨u, hu, hpow⟩, hU₁, hdimU, he, hQe, hsplit,
    hSnd, hSdim⟩ := isInOrbitNu_top_data hQ hdim hν h
  obtain ⟨d₀', U₁', e', hd', horth', hspan', hNd', hNU', ⟨u', hu', hpow'⟩, hU₁', hdimU', he', hQe',
    hsplit', hSnd', hSdim'⟩ := isInOrbitNu_top_data hQ hdim hν h'
  -- `U₁ ≅ U₁'`
  have hQe0 : Q e ≠ 0 := by rw [hQe]; exact hν
  have hQe0' : Q e' ≠ 0 := by rw [hQe']; exact hν
  have he0 : e ≠ 0 := fun h0 => hQe0 (by rw [h0, QuadraticMap.map_zero])
  have he0' : e' ≠ 0 := fun h0 => hQe0' (by rw [h0, QuadraticMap.map_zero])
  obtain ⟨hS1, hS2, hS3⟩ := span_sup_inf_orthogonal (Q := Q) he hQe0
  obtain ⟨hS1', hS2', hS3'⟩ := span_sup_inf_orthogonal (Q := Q) he' hQe0'
  obtain ⟨J⟩ := nonempty_isometryEquiv_of_split hSnd hSnd' hsplit hsplit' (hSdim.trans hSdim'.symm)
    ⟨k, by rw [hSdim]; ring⟩
  let I : (Q.comp U₁.subtype).IsometryEquiv (Q.comp U₁'.subtype) :=
    ((isoOfEq hS1.symm).trans (orthSupIso hS2 hS3).symm).trans
      ((((lineIso he0 he0' (hQe.trans hQe'.symm)).prod J).trans (orthSupIso hS2' hS3')).trans
        (isoOfEq hS1'))
  -- the single blocks on `U₁, U₁'`
  have hpU : (N.restrict hNU) ^ (2 * k) ≠ 0 := fun h0 => hpow (by
    have := LinearMap.congr_fun h0 ⟨u, hu⟩
    rw [Module.End.pow_restrict, LinearMap.restrict_apply] at this
    exact congrArg Subtype.val this)
  have hpU' : (N'.restrict hNU') ^ (2 * k) ≠ 0 := fun h0 => hpow' (by
    have := LinearMap.congr_fun h0 ⟨u', hu'⟩
    rw [Module.End.pow_restrict, LinearMap.restrict_apply] at this
    exact congrArg Subtype.val this)
  obtain ⟨φ, hφ⟩ := exists_isometryEquiv_conj_of_pow_ne_zero hU₁ I hdimU (skew_restrict hN hNU)
    (skew_restrict hN' hNU') (Module.End.isNilpotent.restrict hNU hn)
    (Module.End.isNilpotent.restrict hNU' hn') hpU hpU'
  -- extend to `W` (Witt)
  let φ' : (Q.restrict U₁).IsometryEquiv (Q.restrict U₁') :=
    { toLinearEquiv := φ.toLinearEquiv, map_app' := φ.map_app }
  obtain ⟨g, hg⟩ := QuadraticMap.IsometryEquiv.exists_extension φ'
    ((isNondeg_iff_nondegenerate _).1 hU₁)
  have hgU : ∀ x : U₁, g x = φ x := hg
  have hgb : ∀ x y, bform Q (g x) (g y) = bform Q x y := fun x y => bform_isometry g.toIsometry x y
  -- `g d₀ ∈ F d₀'`, so `N' (g d₀) = 0`
  have hgd : N' (g d₀) = 0 := by
    have hmem : g d₀ ∈ (F ∙ d₀') ⊔ U₁' := by rw [hspan']; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem
    have hb0 : b = 0 := by
      refine radical_free_of_isNondeg hU₁' b hb fun y hy => ?_
      obtain ⟨z, hz⟩ := φ.toLinearEquiv.surjective ⟨y, hy⟩
      have hy' : y = g z := by rw [hgU]; exact (congrArg Subtype.val hz).symm
      have h1 : bform Q (g d₀) y = 0 := by
        rw [hy', hgb, horth _ z.2]
      have h2 : bform Q a y = 0 := by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
        rw [LinearMap.map_smul₂, horth' _ hy, smul_zero]
      rw [← hab, map_add, LinearMap.add_apply, h2, zero_add] at h1
      exact h1
    rw [← hab, hb0, add_zero]
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
    rw [map_smul, hNd', smul_zero]
  have hconj : ∀ x, g (N x) = N' (g x) := by
    intro x
    have hmem : x ∈ (F ∙ d₀) ⊔ U₁ := by rw [hspan]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
    have h1 : g (N b) = N' (g b) := by
      have e1 := hgU ⟨N b, hNU b hb⟩
      have e2 := hgU ⟨b, hb⟩
      simp only at e1 e2
      rw [e1, e2]
      exact congrArg Subtype.val (hφ ⟨b, hb⟩)
    simp only [map_add, map_smul, hNd, smul_zero, zero_add, hgd, h1]
  rcases det_isometryEquiv_eq_one_or hQ g with hdet | hdet
  · exact ⟨g, hdet, hconj⟩
  -- correct the determinant by the reflection in `d₀'`
  have : Invertible (Q d₀') := invertibleOfNonzero hd'
  set r := TauCeti.QuadraticMap.reflection Q d₀'
  have hr : ∀ y, r y = y - (⅟(Q d₀') * QuadraticMap.polar Q d₀' y) • d₀' :=
    TauCeti.QuadraticMap.reflection_apply Q d₀'
  have hrQ : ∀ y, Q (r y) = Q y :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup (Q := Q) (v := d₀')
  let R : Q.IsometryEquiv Q := ⟨r, hrQ⟩
  refine ⟨g.trans R, ?_, fun x => ?_⟩
  · have hdr : LinearMap.det (r : W →ₗ[F] W) = -1 := by
      rw [← LinearEquiv.coe_det, TauCeti.QuadraticMap.det_reflection, Units.val_neg, Units.val_one]
    change LinearMap.det ((r : W →ₗ[F] W) ∘ₗ (g.toLinearEquiv : W →ₗ[F] W)) = 1
    rw [LinearMap.det_comp, hdr, hdet]
    ring
  · change r (g (N x)) = N' (r (g x))
    rw [hr, hr, hconj, map_sub, map_smul, hNd', smul_zero, sub_zero, polar_eq_two_mul_bform,
      QuadraticMap.associated_isSymm F Q d₀' (N' (g x)), hN', hNd', map_zero, neg_zero, mul_zero,
      mul_zero, zero_smul, sub_zero]

end OrbitNu

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

section Extend

variable {Q : QuadraticForm K V} {A B : Submodule K V}

/-- An isometry of `A` extended by the identity on an orthogonal complement `B`. -/
def extendById (hc : IsCompl A B) (horth : ∀ a ∈ A, ∀ b ∈ B, bform Q a b = 0)
    (f : (Q.comp A.subtype).IsometryEquiv (Q.comp A.subtype)) : Q.IsometryEquiv Q :=
  ((QuadClassify.orthIso hc horth).symm.trans
    (f.prod (QuadraticMap.IsometryEquiv.refl _))).trans (QuadClassify.orthIso hc horth)

theorem extendById_apply_left (hc : IsCompl A B) (horth : ∀ a ∈ A, ∀ b ∈ B, bform Q a b = 0)
    (f : (Q.comp A.subtype).IsometryEquiv (Q.comp A.subtype)) (a : A) :
    extendById hc horth f a = f a := by
  change ((Submodule.prodEquivOfIsCompl A B hc) ((f.prod (QuadraticMap.IsometryEquiv.refl _))
    ((Submodule.prodEquivOfIsCompl A B hc).symm a)) : V) = f a
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
  change ((f a : A) : V) + ((0 : B) : V) = f a
  rw [Submodule.coe_zero, add_zero]

theorem extendById_apply_right (hc : IsCompl A B) (horth : ∀ a ∈ A, ∀ b ∈ B, bform Q a b = 0)
    (f : (Q.comp A.subtype).IsometryEquiv (Q.comp A.subtype)) (b : B) :
    extendById hc horth f b = b := by
  change ((Submodule.prodEquivOfIsCompl A B hc) ((f.prod (QuadraticMap.IsometryEquiv.refl _))
    ((Submodule.prodEquivOfIsCompl A B hc).symm b)) : V) = b
  rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
  change ((f 0 : A) : V) + ((b : B) : V) = b
  rw [map_zero, Submodule.coe_zero, zero_add]

theorem det_extendById [FiniteDimensional K V] (hc : IsCompl A B)
    (horth : ∀ a ∈ A, ∀ b ∈ B, bform Q a b = 0)
    (f : (Q.comp A.subtype).IsometryEquiv (Q.comp A.subtype)) :
    LinearMap.det ((extendById hc horth f).toLinearEquiv : V →ₗ[K] V) =
      LinearMap.det (f.toLinearEquiv : A →ₗ[K] A) := by
  set e := Submodule.prodEquivOfIsCompl A B hc
  have : ((extendById hc horth f).toLinearEquiv : V →ₗ[K] V) =
      (e : (A × B) →ₗ[K] V) ∘ₗ ((f.toLinearEquiv : A →ₗ[K] A).prodMap LinearMap.id) ∘ₗ
        (e.symm : V →ₗ[K] (A × B)) := by
    ext x
    rfl
  rw [this, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, mul_one]

end Extend

section Sub

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
variable {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W] {Q : QuadraticForm F W}

/-- `IsInOrbitNu Q U ν N` passes to `U` itself: `IsInOrbitNu (Q|_U) ⊤ ν (N|_U)`. -/
theorem isInOrbitNu_restrict {U : Submodule F W} {ν : F} {N : Module.End F W}
    (hNU : ∀ u ∈ U, N u ∈ U) (h : IsInOrbitNu Q U ν N) :
    IsInOrbitNu (Q.comp U.subtype) ⊤ ν (N.restrict hNU) := by
  classical
  obtain ⟨d₀, U₁, hd₀U, hd, hU₁U, horth, hspan, hNd, hNU₁, ⟨u, hu, hpow⟩, e, he, hQe, hsplit⟩ := h
  set U₁' := U₁.comap U.subtype
  have hfin : finrank F U₁' = finrank F U₁ := (Submodule.comapSubtypeEquivOfLe hU₁U).finrank_eq
  -- the split part, transported
  set e' : U := ⟨e, hU₁U he⟩
  have hmap : (U₁' ⊓ (bform (Q.comp U.subtype)).orthogonal (F ∙ e')).map U.subtype =
      U₁ ⊓ (bform Q).orthogonal (F ∙ e) := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_inf, mem_orthogonal_span_singleton,
      bform_comp_subtype, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨hy1, hy2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨⟨x, hU₁U hx1⟩, ⟨hx1, hx2⟩, rfl⟩
  let J : ((Q.comp U.subtype).comp
      (U₁' ⊓ (bform (Q.comp U.subtype)).orthogonal (F ∙ e')).subtype).IsometryEquiv
      (Q.comp (U₁ ⊓ (bform Q).orthogonal (F ∙ e)).subtype) :=
    { toLinearEquiv := (Submodule.equivMapOfInjective _ U.injective_subtype _).trans
        (LinearEquiv.ofEq _ _ hmap)
      map_app' := fun _ => rfl }
  refine ⟨⟨d₀, hd₀U⟩, U₁', trivial, hd, le_top, fun w hw => ?_, ?_, Subtype.ext hNd,
    fun w hw => hNU₁ _ hw, ⟨⟨u, hU₁U hu⟩, hu, ?_⟩, e', he, hQe, ?_⟩
  · rw [bform_comp_subtype]; exact horth _ hw
  · rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    rw [← hspan] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
    refine Submodule.mem_sup.2 ⟨c • ⟨d₀, hd₀U⟩,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ⟨b, hU₁U hb⟩, hb, rfl⟩
  · rw [hfin]
    intro h0
    apply hpow
    rw [Module.End.pow_restrict, LinearMap.restrict_apply] at h0
    exact congrArg Subtype.val h0
  · unfold IsSplitQF at hsplit ⊢
    rw [J.toLinearEquiv.finrank_eq, QuadClassify.wittIndex_eq_of_isometryEquiv J]
    exact hsplit

omit [FiniteDimensional F W] in
/-- `N` preserves `U` when `IsInOrbitNu Q U ν N`. -/
theorem mapsTo_of_isInOrbitNu {U : Submodule F W} {ν : F} {N : Module.End F W}
    (h : IsInOrbitNu Q U ν N) : ∀ u ∈ U, N u ∈ U := by
  obtain ⟨d₀, U₁, -, -, hU₁U, -, hspan, hNd, hNU₁, -⟩ := h
  intro x hx
  rw [← hspan] at hx ⊢
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
  rw [map_add, map_smul, hNd, smul_zero, zero_add]
  exact Submodule.mem_sup_right (hNU₁ b hb)

/-- **`O_ν` on a subspace**: if `W = U ⊥ B` and `N, N' ∈ O_ν(U)` (nilpotent skew on `W`), some
`g ∈ SO(W)` fixing `B` pointwise has `g N = N' g` on `U`. -/
theorem exists_isometry_det_one_conj_of_isInOrbitNu_sub (hQ : IsNondeg Q) {U B : Submodule F W}
    (hc : IsCompl U B) (horth : ∀ a ∈ U, ∀ b ∈ B, bform Q a b = 0) {k : ℕ}
    (hdim : finrank F U = 2 * k + 2) {ν : F} (hν : ν ≠ 0) {N N' : Module.End F W}
    (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w))
    (hN' : ∀ u w, bform Q (N' u) w = -bform Q u (N' w))
    (hn : IsNilpotent N) (hn' : IsNilpotent N') (h : IsInOrbitNu Q U ν N)
    (h' : IsInOrbitNu Q U ν N') :
    ∃ g : Q.IsometryEquiv Q, LinearMap.det (g.toLinearEquiv : W →ₗ[F] W) = 1 ∧
      (∀ b ∈ B, g b = b) ∧ ∀ u ∈ U, g (N u) = N' (g u) := by
  have hrad : ∀ x ∈ (⊤ : Submodule F W), (∀ y ∈ (⊤ : Submodule F W), bform Q x y = 0) → x = 0 :=
    fun x _ hx => (isNondeg_iff Q).1 hQ x fun y => hx y trivial
  have hU : IsNondeg (Q.comp U.subtype) := isNondeg_comp_of_sup hrad hc.sup_eq_top horth
  have hNU := mapsTo_of_isInOrbitNu h
  have hNU' := mapsTo_of_isInOrbitNu h'
  obtain ⟨f, hf1, hf2⟩ := exists_isometry_det_one_conj_of_isInOrbitNu hU hdim hν
    (skew_restrict hN hNU) (skew_restrict hN' hNU') (Module.End.isNilpotent.restrict hNU hn)
    (Module.End.isNilpotent.restrict hNU' hn') (isInOrbitNu_restrict hNU h)
    (isInOrbitNu_restrict hNU' h')
  refine ⟨extendById hc horth f, by rw [det_extendById, hf1],
    fun b hb => extendById_apply_right hc horth f ⟨b, hb⟩, fun u hu => ?_⟩
  have h1 := extendById_apply_left hc horth f ⟨N u, hNU u hu⟩
  have h2 := extendById_apply_left hc horth f ⟨u, hu⟩
  simp only at h1 h2
  rw [h1, h2]
  exact congrArg Subtype.val (hf2 ⟨u, hu⟩)

/-- **Single blocks on a subspace**: if `W = U ⊥ B`, `dim U = 2k + 1`, and `N, N'` are nilpotent
skew, preserve `U`, and have `N^{2k}, N'^{2k} ≠ 0` on `U`, some `g ∈ SO(W)` fixing `B` pointwise
has `g N = N' g` on `U`. -/
theorem exists_isometry_det_one_conj_of_pow_ne_zero_sub (hQ : IsNondeg Q) {U B : Submodule F W}
    (hc : IsCompl U B) (horth : ∀ a ∈ U, ∀ b ∈ B, bform Q a b = 0) {k : ℕ}
    (hdim : finrank F U = 2 * k + 1) {N N' : Module.End F W}
    (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w))
    (hN' : ∀ u w, bform Q (N' u) w = -bform Q u (N' w))
    (hn : IsNilpotent N) (hn' : IsNilpotent N') (hNU : ∀ u ∈ U, N u ∈ U)
    (hNU' : ∀ u ∈ U, N' u ∈ U) (hp : ∃ u ∈ U, (N ^ (2 * k)) u ≠ 0)
    (hp' : ∃ u ∈ U, (N' ^ (2 * k)) u ≠ 0) :
    ∃ g : Q.IsometryEquiv Q, LinearMap.det (g.toLinearEquiv : W →ₗ[F] W) = 1 ∧
      (∀ b ∈ B, g b = b) ∧ ∀ u ∈ U, g (N u) = N' (g u) := by
  have hrad : ∀ x ∈ (⊤ : Submodule F W), (∀ y ∈ (⊤ : Submodule F W), bform Q x y = 0) → x = 0 :=
    fun x _ hx => (isNondeg_iff Q).1 hQ x fun y => hx y trivial
  have hU : IsNondeg (Q.comp U.subtype) := isNondeg_comp_of_sup hrad hc.sup_eq_top horth
  have hpU : ∀ {M : Module.End F W} (hMU : ∀ u ∈ U, M u ∈ U), (∃ u ∈ U, (M ^ (2 * k)) u ≠ 0) →
      (M.restrict hMU) ^ (2 * k) ≠ 0 := fun hMU ⟨u, hu, hpow⟩ h0 => hpow (by
    have := LinearMap.congr_fun h0 ⟨u, hu⟩
    rw [Module.End.pow_restrict, LinearMap.restrict_apply] at this
    exact congrArg Subtype.val this)
  obtain ⟨f, hf1, hf2⟩ := exists_isometry_det_one_conj_of_pow_ne_zero hU hdim
    (skew_restrict hN hNU) (skew_restrict hN' hNU') (Module.End.isNilpotent.restrict hNU hn)
    (Module.End.isNilpotent.restrict hNU' hn') (hpU hNU hp) (hpU hNU' hp')
  refine ⟨extendById hc horth f, by rw [det_extendById, hf1],
    fun b hb => extendById_apply_right hc horth f ⟨b, hb⟩, fun u hu => ?_⟩
  have h1 := extendById_apply_left hc horth f ⟨N u, hNU u hu⟩
  have h2 := extendById_apply_left hc horth f ⟨u, hu⟩
  simp only at h1 h2
  rw [h1, h2]
  exact congrArg Subtype.val (hf2 ⟨u, hu⟩)

end Sub

end SingleBlock

end GSpinGGP
