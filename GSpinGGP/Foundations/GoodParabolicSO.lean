/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.WeakCartanTheorem

/-!
# The estimates of the good minimal parabolic of `SO(W) × SO(V₀)`

Set-up of `GSpinGGP.Foundations.WeakCartanFrame`: `b` is an orthogonal basis of anisotropic
vectors of `(V₀, Q)` over a non-archimedean field whose first `l + 1` vectors form a maximal frame
`w₀ = b 0, …, w_l = b l` (`Q wᵢ = (-1)ⁱ ν`). `H = SO(W)`, `W = w₀^⊥`, is `fixer Q b 1`, embedded
diagonally in `G₀ = SO(W) × SO(V₀)`. The split tori `A_V = multiTorus hb hf 0` (pairs
`(w_{2i}, w_{2i+1})`) and `A_W = multiTorus hb hf 1` (pairs `(w_{2i+1}, w_{2i+2})`) are those of
the good minimal parabolic `P̄₀ = P̄_W × P̄_{V₀}` of the proof of Thesis Prop. 8.1.1(i) (the
stabilizers of the flags `⟨u′₁⟩ ⊂ ⟨u′₁, u′₂⟩ ⊂ ⋯` and `⟨u₁⟩ ⊂ ⟨u₁, u₂⟩ ⊂ ⋯`). As in
`weakCartan_G0_SO`, the expanding chamber `A₀⁺` of `P̄₀` is written as the set of
`(a_W, a_V) = ((multiTorus hb hf 1 s)⁻¹, (multiTorus hb hf 0 t)⁻¹)` with `s`, `t` in the
contracting chambers `InChamber n l 1 s`, `InChamber n l 0 t`. Norms are the coordinate operator
norm `‖·‖ = basisOpNorm b`.

This file proves Thesis Prop. 8.1.1(iii) in the codimension-one case, i.e. the inequalities
(Thesis (8.1.7), (8.1.8); BP Prop. 6.4.1, (6.4.7), (6.4.8)), in multiplicative form:

* `norm_le_of_mem_chamber` (I): `‖h‖ + ‖a_W‖ + ‖a_V‖ ≪ max(1, ‖h a_W‖, ‖h a_V‖)^N`;
* `norm_le_conj_of_mem_chamber` (II): `‖h‖ ≪ max(1, ‖a_W⁻¹ h a_W‖, ‖a_V⁻¹ h a_V‖)`,

for `h ∈ H` and `(a_W, a_V) ∈ A₀⁺`. Taking logarithms gives `σ(h) + σ(a) ≪ σ(ha)` and
`σ(h) ≪ σ(a⁻¹ha)` for the log-norm `σ = log max(1, ‖·‖)` (up to the additive constants that
`σ ≥ 1` absorbs).

The chamber is that of the orthogonal group: its roots are `tᵢ/tₖ`, `tᵢtₖ` (`i < k`) and, when the
anisotropic part is nonzero, `tᵢ`; there is no root `tᵢ²`. When `V₀` (resp. `W`) has no
anisotropic part beyond the frame, the last coordinate of `A_V` (resp. `A_W`) may have absolute
value `> 1` on `A₀⁺`. The proof of (II) handles the last frame vector `w_l` in that case by the
torus of the other factor, which fixes `w_l`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Module QuadraticMap

namespace GSpinGGP

namespace WeakCartan

variable {F : Type*} [NontriviallyNormedField F] [CharZero F]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {n : ℕ}
  {b : Module.Basis (Fin n) F V} {Q : QuadraticForm F V}

/-! ## Basis vectors indexed by `ℕ` -/

/-- The basis vector `b m`, and `0` for `m ≥ n`. -/
def bn (b : Module.Basis (Fin n) F V) (m : ℕ) : V := if h : m < n then b ⟨m, h⟩ else 0

theorem bn_of_lt {m : ℕ} (h : m < n) : bn b m = b ⟨m, h⟩ := by simp [bn, h]

theorem bn_of_le {m : ℕ} (h : n ≤ m) : bn b m = 0 := by simp [bn]; omega

theorem basisNorm_bn_le (m : ℕ) : basisNorm b (bn b m) ≤ 1 := by
  unfold bn
  split_ifs
  · rw [basisNorm_basis]
  · rw [basisNorm_zero]; exact zero_le_one

/-- Elements of `fixer Q b j` fix `bn b m` for `m < j`. -/
theorem apply_bn_of_mem_fixer {j : ℕ} {g : V ≃ₗ[F] V} (hg : g ∈ fixer Q b j) {m : ℕ}
    (hm : m < j) : g (bn b m) = bn b m := by
  unfold bn
  split_ifs with h
  · exact hg.2 _ hm
  · exact map_zero g

/-! ## Eigenvectors of the split tori -/

section Eigen

variable (hb : IsOrthoBasis Q b) {ν : F} {l : ℕ} (hf : IsFrame Q b ν l)

theorem levelTorus_apply_bn_of_ne (j : ℕ) (t : Fˣ) {m : ℕ} (hm : m ≠ j) (hm' : m ≠ j + 1) :
    levelTorus hb hf j t (bn b m) = bn b m := by
  by_cases hj : j + 1 ≤ l
  · rw [levelTorus_of_le hb hf hj]
    unfold bn
    split_ifs with h
    · exact pairTorus_apply_basis_of_ne _ _ _ _ _ (by simp [Fin.ext_iff]; omega)
        (by simp [Fin.ext_iff]; omega)
    · exact map_zero _
  · rw [levelTorus_of_not_le hb hf hj]; rfl

theorem levelTorus_apply_add {j : ℕ} (hj : j + 1 ≤ l) (t : Fˣ) :
    levelTorus hb hf j t (bn b j + bn b (j + 1)) = (t : F) • (bn b j + bn b (j + 1)) := by
  rw [levelTorus_of_le hb hf hj, bn_of_lt (hf.idx_lt (by omega)), bn_of_lt (hf.idx_lt hj),
    map_add, pairTorus_apply_left, pairTorus_apply_right]
  module

theorem levelTorus_apply_sub {j : ℕ} (hj : j + 1 ≤ l) (t : Fˣ) :
    levelTorus hb hf j t (bn b j - bn b (j + 1)) = (t : F)⁻¹ • (bn b j - bn b (j + 1)) := by
  rw [levelTorus_of_le hb hf hj, bn_of_lt (hf.idx_lt (by omega)), bn_of_lt (hf.idx_lt hj),
    map_sub, pairTorus_apply_left, pairTorus_apply_right]
  module

theorem multiTorus_apply_bn_of_lt (ts : List Fˣ) (j : ℕ) {m : ℕ} (hm : m < j) :
    multiTorus hb hf j ts (bn b m) = bn b m :=
  apply_bn_of_mem_fixer (multiTorus_mem_fixer hb hf ts j) hm

theorem multiTorus_apply_bn_of_ge :
    ∀ (ts : List Fˣ) (j : ℕ) {m : ℕ}, j + 2 * ts.length ≤ m →
      multiTorus hb hf j ts (bn b m) = bn b m
  | [], _, _, _ => rfl
  | t :: ts, j, m, hm => by
    simp only [List.length_cons] at hm
    rw [multiTorus_cons, LinearEquiv.mul_apply,
      levelTorus_apply_bn_of_ne hb hf j t (by omega) (by omega),
      multiTorus_apply_bn_of_ge ts (j + 2) (by omega)]

/-- `u_k = b (j+2k) + b (j+2k+1)` is an eigenvector of the level-`j` torus, eigenvalue `t_k`. -/
theorem multiTorus_apply_add :
    ∀ (ts : List Fˣ) (j k : ℕ) (hk : k < ts.length), j + 2 * k + 1 ≤ l →
      multiTorus hb hf j ts (bn b (j + 2 * k) + bn b (j + 2 * k + 1)) =
        (ts[k] : F) • (bn b (j + 2 * k) + bn b (j + 2 * k + 1))
  | t :: ts, j, 0, _, hl => by
    simp only [mul_zero, add_zero] at hl ⊢
    rw [multiTorus_cons, LinearEquiv.mul_apply, levelTorus_apply_add hb hf hl, map_smul, map_add,
      multiTorus_apply_bn_of_lt hb hf ts (j + 2) (by omega),
      multiTorus_apply_bn_of_lt hb hf ts (j + 2) (by omega)]
    rfl
  | t :: ts, j, k + 1, hk, hl => by
    have e1 : j + 2 * (k + 1) = j + 2 + 2 * k := by ring
    rw [e1, multiTorus_cons, LinearEquiv.mul_apply, map_add,
      levelTorus_apply_bn_of_ne hb hf j t (by omega) (by omega),
      levelTorus_apply_bn_of_ne hb hf j t (by omega) (by omega),
      multiTorus_apply_add ts (j + 2) k (by simpa using hk) (by omega)]
    rfl

/-- `v_k = b (j+2k) - b (j+2k+1)` is an eigenvector of the level-`j` torus, eigenvalue `t_k⁻¹`. -/
theorem multiTorus_apply_sub :
    ∀ (ts : List Fˣ) (j k : ℕ) (hk : k < ts.length), j + 2 * k + 1 ≤ l →
      multiTorus hb hf j ts (bn b (j + 2 * k) - bn b (j + 2 * k + 1)) =
        (ts[k] : F)⁻¹ • (bn b (j + 2 * k) - bn b (j + 2 * k + 1))
  | t :: ts, j, 0, _, hl => by
    simp only [mul_zero, add_zero] at hl ⊢
    rw [multiTorus_cons, LinearEquiv.mul_apply, levelTorus_apply_sub hb hf hl, map_smul, map_sub,
      multiTorus_apply_bn_of_lt hb hf ts (j + 2) (by omega),
      multiTorus_apply_bn_of_lt hb hf ts (j + 2) (by omega)]
    rfl
  | t :: ts, j, k + 1, hk, hl => by
    have e1 : j + 2 * (k + 1) = j + 2 + 2 * k := by ring
    rw [e1, multiTorus_cons, LinearEquiv.mul_apply, map_sub,
      levelTorus_apply_bn_of_ne hb hf j t (by omega) (by omega),
      levelTorus_apply_bn_of_ne hb hf j t (by omega) (by omega),
      multiTorus_apply_sub ts (j + 2) k (by simpa using hk) (by omega)]
    rfl

end Eigen

/-! ## Conjugation by a torus -/

section Conj

/-- If `A x = α x` and `A y = β y` for an isometry `A`, then
`polar(h x, y) = α β polar((A h A⁻¹) x, y)`. -/
theorem polar_apply_eq_mul_conj {A : V ≃ₗ[F] V}
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h : V ≃ₗ[F] V) {x y : V} {α β : F}
    (hx : A x = α • x) (hy : A y = β • y) :
    polar Q (h x) y = α * β * polar Q ((A * h * A⁻¹) x) y := by
  have h1 : (A * h * A⁻¹) (A x) = A (h x) := by
    simp only [LinearEquiv.mul_apply]
    rw [show A⁻¹ (A x) = x from A.symm_apply_apply x]
  rw [← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hA (h x) y, ← h1, hx, hy,
    map_smul, polar_smul_left, polar_smul_right, smul_eq_mul, smul_eq_mul]
  ring

variable [IsUltrametricDist F]

theorem norm_polar_apply_le (hb : IsOrthoBasis Q b) (g : V ≃ₗ[F] V) (x y : V) :
    ‖polar Q (g x) y‖ ≤
      polarBound Q b * basisOpNorm b (g : V →ₗ[F] V) * basisNorm b x * basisNorm b y := by
  refine (hb.norm_polar_le _ _).trans ?_
  have h1 := basisNorm_apply_le (b := b) (g : V →ₗ[F] V) x
  have hp : 0 ≤ polarBound Q b := norm_nonneg _
  calc polarBound Q b * basisNorm b (g x) * basisNorm b y
      ≤ polarBound Q b * (basisOpNorm b (g : V →ₗ[F] V) * basisNorm b x) * basisNorm b y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hp) (basisNorm_nonneg y)
    _ = _ := by ring

/-- The basic estimate: for eigenvectors `x`, `y` of an isometry `A`, of norm `≤ 1` and with
eigenvalues `α`, `β` such that `|α β| ≤ 1`, the coefficient `polar(h x, y)` is bounded by the
norm of `A h A⁻¹`. -/
theorem norm_polar_le_of_eigen (hb : IsOrthoBasis Q b) {A : V ≃ₗ[F] V}
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h : V ≃ₗ[F] V) {x y : V} {α β : F}
    (hx : A x = α • x) (hy : A y = β • y) (hαβ : ‖α * β‖ ≤ 1) (hxn : basisNorm b x ≤ 1)
    (hyn : basisNorm b y ≤ 1) :
    ‖polar Q (h x) y‖ ≤
      polarBound Q b * basisOpNorm b ((A * h * A⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) := by
  set N := basisOpNorm b ((A * h * A⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V)
  have hp : 0 ≤ polarBound Q b * N := mul_nonneg (norm_nonneg _) (basisOpNorm_nonneg _)
  have hxy : basisNorm b x * basisNorm b y ≤ 1 := by
    nlinarith [basisNorm_nonneg (b := b) x, basisNorm_nonneg (b := b) y]
  have h2 : ‖polar Q ((A * h * A⁻¹) x) y‖ ≤ polarBound Q b * N := by
    refine (norm_polar_apply_le hb (A * h * A⁻¹) x y).trans ?_
    calc polarBound Q b * N * basisNorm b x * basisNorm b y
        = (polarBound Q b * N) * (basisNorm b x * basisNorm b y) := by ring
      _ ≤ (polarBound Q b * N) * 1 := mul_le_mul_of_nonneg_left hxy hp
      _ = _ := mul_one _
  rw [polar_apply_eq_mul_conj hA h hx hy, norm_mul]
  calc ‖α * β‖ * ‖polar Q ((A * h * A⁻¹) x) y‖ ≤ 1 * (polarBound Q b * N) :=
        mul_le_mul hαβ h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end Conj

/-! ## Chambers -/

section Chamber

variable {l : ℕ}

theorem InChamber.rel_of_lt {j : ℕ} {ts : List Fˣ} (h : InChamber n l j ts) {k m : ℕ}
    (hkm : k < m) (hm : m < ts.length) :
    ‖(ts[k] : F)‖ ≤ ‖(ts[m] : F)‖ ∧ ‖(ts[k] : F) * ts[m]‖ ≤ 1 := by
  have h2 := h.2.1
  have e : ∀ us : List Fˣ, (do let a ← us; pure (a : F)) = us.map (fun a : Fˣ => (a : F)) := by
    intro us
    induction us with
    | nil => rfl
    | cons a us ih => exact congrArg (List.cons (a : F)) ih
  rw [e] at h2
  have := List.pairwise_iff_getElem.1 h2 k m (by simp; omega) (by simpa using hm) hkm
  simp only [List.getElem_map] at this
  exact this

/-- Every coordinate but the last has absolute value `≤ 1`, and the last one too when the
anisotropic part is nonzero. -/
theorem InChamber.norm_le_one {j : ℕ} {ts : List Fˣ} (h : InChamber n l j ts) {k : ℕ}
    (hk : k < ts.length) (h' : k + 1 < ts.length ∨ j + 2 * ts.length < n) :
    ‖(ts[k] : F)‖ ≤ 1 := by
  rcases h' with h' | h'
  · obtain ⟨h1, h2⟩ := h.rel_of_lt (Nat.lt_succ_self k) h'
    rw [norm_mul] at h2
    nlinarith [mul_le_mul_of_nonneg_left h1 (norm_nonneg (ts[k] : F)), norm_nonneg (ts[k] : F)]
  · exact h.2.2 h' _ (List.getElem_mem hk)

end Chamber

/-! ## The induction for (II) -/

section Level

variable [IsUltrametricDist F] (hb : IsOrthoBasis Q b) {ν : F} {l : ℕ} (hf : IsFrame Q b ν l)

omit [CharZero F] [FiniteDimensional F V] in
theorem norm_sub_le_max_of_ultra (x y : F) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max x (-y)

theorem basisNorm_bn_add_le (p q : ℕ) : basisNorm b (bn b p + bn b q) ≤ 1 :=
  (basisNorm_add_le _ _).trans (max_le (basisNorm_bn_le p) (basisNorm_bn_le q))

theorem basisNorm_bn_sub_le (p q : ℕ) : basisNorm b (bn b p - bn b q) ≤ 1 :=
  (basisNorm_sub_le _ _).trans (max_le (basisNorm_bn_le p) (basisNorm_bn_le q))

theorem multiTorus_mem_orthogonalGroup (ts : List Fˣ) (j : ℕ) :
    multiTorus hb hf j ts ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  mem_orthogonalGroup_of_mem_fixer (multiTorus_mem_fixer hb hf ts j)

include hb in
/-- A fixed vector pair: if an isometry `T` fixes `x` and `y`, `polar(h x, y)` is bounded by the
norm of `T h T⁻¹`. -/
theorem norm_polar_le_of_fixed {T : V ≃ₗ[F] V}
    (hT : T ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h : V ≃ₗ[F] V) {x y : V} (hx : T x = x)
    (hy : T y = y) (hxn : basisNorm b x ≤ 1) (hyn : basisNorm b y ≤ 1) :
    ‖polar Q (h x) y‖ ≤
      polarBound Q b * basisOpNorm b ((T * h * T⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) :=
  norm_polar_le_of_eigen hb hT h (α := 1) (β := 1) (by rw [one_smul]; exact hx)
    (by rw [one_smul]; exact hy) (by simp) hxn hyn

include hb in
/-- The eigenvector estimates for `u_k` against `u_m`, `v_m` (`k ≤ m`) at level `j`. -/
theorem norm_polar_pair_le {j : ℕ} {ts : List Fˣ} (hts : InChamber n l j ts) (h : V ≃ₗ[F] V)
    {k m : ℕ} (hkm : k ≤ m) (hm : m < ts.length)
    (hkk : m = k → ‖(ts[m] : F)‖ ≤ 1) :
    ‖polar Q (h (bn b (j + 2 * k) + bn b (j + 2 * k + 1)))
        (bn b (j + 2 * m) + bn b (j + 2 * m + 1))‖ ≤
        polarBound Q b * basisOpNorm b
          ((multiTorus hb hf j ts * h * (multiTorus hb hf j ts)⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) ∧
      ‖polar Q (h (bn b (j + 2 * k) + bn b (j + 2 * k + 1)))
          (bn b (j + 2 * m) - bn b (j + 2 * m + 1))‖ ≤
        polarBound Q b * basisOpNorm b
          ((multiTorus hb hf j ts * h * (multiTorus hb hf j ts)⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) := by
  have hlen := hts.1
  simp only [numPairs] at hlen
  have hk : k < ts.length := by omega
  refine ⟨norm_polar_le_of_eigen hb (multiTorus_mem_orthogonalGroup hb hf ts j) h
    (multiTorus_apply_add hb hf ts j k hk (by omega))
    (multiTorus_apply_add hb hf ts j m hm (by omega)) ?_ (basisNorm_bn_add_le _ _)
    (basisNorm_bn_add_le _ _),
    norm_polar_le_of_eigen hb (multiTorus_mem_orthogonalGroup hb hf ts j) h
    (multiTorus_apply_add hb hf ts j k hk (by omega))
    (multiTorus_apply_sub hb hf ts j m hm (by omega)) ?_ (basisNorm_bn_add_le _ _)
    (basisNorm_bn_sub_le _ _)⟩
  · rcases hkm.lt_or_eq with hlt | rfl
    · exact (hts.rel_of_lt hlt hm).2
    · have := hkk rfl
      rw [norm_mul]
      nlinarith [norm_nonneg (ts[k] : F)]
  · rcases hkm.lt_or_eq with hlt | rfl
    · obtain ⟨h1, -⟩ := hts.rel_of_lt hlt hm
      rw [norm_mul, norm_inv, ← div_eq_mul_inv]
      exact div_le_one_of_le₀ h1 (norm_nonneg _)
    · rw [mul_inv_cancel₀ (Units.ne_zero _), norm_one]

include hb in
/-- The level estimate: `polar(h u_k, b_p)` for `p ≥ j + 2k` is bounded by the norm of
`T h T⁻¹`, `T` the level-`j` torus, provided `|t_k| ≤ 1` or `b_p` lies beyond the `k`-th pair. -/
theorem norm_polar_level_le {j : ℕ} {ts : List Fˣ} (hts : InChamber n l j ts) (h : V ≃ₗ[F] V)
    {k p : ℕ} (hk : k < ts.length) (hp : j + 2 * k ≤ p)
    (hkp : ‖(ts[k] : F)‖ ≤ 1 ∨ j + 2 * k + 2 ≤ p) :
    ‖polar Q (h (bn b (j + 2 * k) + bn b (j + 2 * k + 1))) (bn b p)‖ ≤
      ‖(2 : F)‖⁻¹ * (polarBound Q b * basisOpNorm b
        ((multiTorus hb hf j ts * h * (multiTorus hb hf j ts)⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V)) := by
  set B := polarBound Q b * basisOpNorm b
    ((multiTorus hb hf j ts * h * (multiTorus hb hf j ts)⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V)
  have hB : 0 ≤ B := mul_nonneg (norm_nonneg _) (basisOpNorm_nonneg _)
  have h2 : 1 ≤ ‖(2 : F)‖⁻¹ := one_le_norm_two_inv
  have hlen := hts.1
  simp only [numPairs] at hlen
  by_cases hpn : n ≤ p
  · rw [bn_of_le hpn, polar_zero_right, norm_zero]; positivity
  by_cases hpl : j + 2 * ts.length ≤ p
  · refine (norm_polar_le_of_eigen hb (multiTorus_mem_orthogonalGroup hb hf ts j) h
      (multiTorus_apply_add hb hf ts j k hk (by omega)) (β := 1)
      (by rw [one_smul]; exact multiTorus_apply_bn_of_ge hb hf ts j hpl) ?_
      (basisNorm_bn_add_le _ _) (basisNorm_bn_le _)).trans (le_mul_of_one_le_left hB h2)
    rw [mul_one]
    exact hts.norm_le_one hk (Or.inr (by omega))
  obtain ⟨m, hpm⟩ : ∃ m, p = j + 2 * m ∨ p = j + 2 * m + 1 := ⟨(p - j) / 2, by omega⟩
  have hm : m < ts.length := by omega
  have hkm : k ≤ m := by omega
  obtain ⟨A1, A2⟩ := norm_polar_pair_le hb hf hts h hkm hm (fun hmk => by
    subst hmk
    rcases hkp with hkp | hkp
    · exact hkp
    · omega)
  have h2n : ‖(2 : F)⁻¹‖ = ‖(2 : F)‖⁻¹ := norm_inv _
  rcases hpm with rfl | rfl
  · rw [show bn b (j + 2 * m) = (2 : F)⁻¹ • ((bn b (j + 2 * m) + bn b (j + 2 * m + 1)) +
        (bn b (j + 2 * m) - bn b (j + 2 * m + 1))) by module,
      polar_smul_right, polar_add_right, smul_eq_mul, norm_mul, h2n]
    exact mul_le_mul_of_nonneg_left
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le A1 A2)) (by positivity)
  · rw [show bn b (j + 2 * m + 1) = (2 : F)⁻¹ • ((bn b (j + 2 * m) + bn b (j + 2 * m + 1)) -
        (bn b (j + 2 * m) - bn b (j + 2 * m + 1))) by module,
      polar_smul_right, polar_sub_right, smul_eq_mul, norm_mul, h2n]
    exact mul_le_mul_of_nonneg_left
      ((norm_sub_le_max_of_ultra _ _).trans (max_le A1 A2)) (by positivity)

include hb in
/-- One step of the induction (Thesis (8.1.11), with the chamber of the orthogonal group): from
the bound for `b_{j+2k}` to the bound for `b_{j+2k+1}`, at level `j`. When `|t_k| > 1` (the last
pair of a level without anisotropic part), `b_{j+2k+1}` is the last basis vector and is fixed by
the isometry `T'` (the torus of the other level). -/
theorem step_level {j : ℕ} {ts : List Fˣ} (hts : InChamber n l j ts) {T' : V ≃ₗ[F] V}
    (hT' : T' ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h : V ≃ₗ[F] V) {k : ℕ}
    (hk : k < ts.length) {E : ℝ}
    (hA : ‖(2 : F)‖⁻¹ * (polarBound Q b * basisOpNorm b
        ((multiTorus hb hf j ts * h * (multiTorus hb hf j ts)⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V)) ≤ E)
    (hB : polarBound Q b * basisOpNorm b ((T' * h * T'⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) ≤ E)
    (hbad : ¬ ‖(ts[k] : F)‖ ≤ 1 → T' (bn b (j + 2 * k + 1)) = bn b (j + 2 * k + 1))
    (ih : ∀ p, j + 2 * k ≤ p → ‖polar Q (h (bn b (j + 2 * k))) (bn b p)‖ ≤ E) :
    ∀ p, j + 2 * k + 1 ≤ p → ‖polar Q (h (bn b (j + 2 * k + 1))) (bn b p)‖ ≤ E := by
  intro p hp
  have hlen := hts.1
  simp only [numPairs] at hlen
  have hl := hf.lt
  by_cases htk : ‖(ts[k] : F)‖ ≤ 1
  · rw [show bn b (j + 2 * k + 1) = (bn b (j + 2 * k) + bn b (j + 2 * k + 1)) - bn b (j + 2 * k)
      by abel, map_sub, polar_sub_left]
    exact (norm_sub_le_max_of_ultra _ _).trans (max_le
      ((norm_polar_level_le hb hf hts h hk (by omega) (Or.inl htk)).trans hA) (ih p (by omega)))
  · have hn : ¬ (k + 1 < ts.length ∨ j + 2 * ts.length < n) := fun h' =>
      htk (hts.norm_le_one hk h')
    by_cases hpn : n ≤ p
    · rw [bn_of_le hpn, polar_zero_right, norm_zero]
      exact (mul_nonneg (norm_nonneg _) (basisOpNorm_nonneg _)).trans hB
    have hpe : p = j + 2 * k + 1 := by omega
    subst hpe
    exact (norm_polar_le_of_fixed hb hT' h (hbad htk) (hbad htk) (basisNorm_bn_le _)
      (basisNorm_bn_le _)).trans hB

end Level

/-! ## The estimates -/

section Main

variable [IsUltrametricDist F] (hb : IsOrthoBasis Q b) {ν : F} {l : ℕ} (hf : IsFrame Q b ν l)

include hb in
/-- The coefficients `polar(h b_i, b_p)`, `i ≤ p`, of `h ∈ H` are bounded by
`max(1, ‖a_V⁻¹ h a_V‖, ‖a_W⁻¹ h a_W‖)` on the chamber (Thesis (8.1.11), corrected for the
chamber of the orthogonal group). -/
theorem norm_polar_le_conj {s t : List Fˣ} (hs : InChamber n l 1 s) (ht : InChamber n l 0 t)
    {h : V ≃ₗ[F] V} (hh : h ∈ fixer Q b 1) :
    ∀ i p, i ≤ p → ‖polar Q (h (bn b i)) (bn b p)‖ ≤ ‖(2 : F)‖⁻¹ * polarBound Q b *
      max 1 (max
        (basisOpNorm b ((multiTorus hb hf 0 t * h * (multiTorus hb hf 0 t)⁻¹ : V ≃ₗ[F] V) :
          V →ₗ[F] V))
        (basisOpNorm b ((multiTorus hb hf 1 s * h * (multiTorus hb hf 1 s)⁻¹ : V ≃ₗ[F] V) :
          V →ₗ[F] V))) := by
  set NA := basisOpNorm b ((multiTorus hb hf 0 t * h * (multiTorus hb hf 0 t)⁻¹ : V ≃ₗ[F] V) :
    V →ₗ[F] V)
  set NB := basisOpNorm b ((multiTorus hb hf 1 s * h * (multiTorus hb hf 1 s)⁻¹ : V ≃ₗ[F] V) :
    V →ₗ[F] V)
  set P := polarBound Q b
  set D := max 1 (max NA NB)
  have h2 : 1 ≤ ‖(2 : F)‖⁻¹ := one_le_norm_two_inv
  have hP : 0 ≤ P := norm_nonneg _
  have hD1 : 1 ≤ D := le_max_left _ _
  have hDA : NA ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hDB : NB ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  have hK : 0 ≤ ‖(2 : F)‖⁻¹ * P := by positivity
  have hEA : ‖(2 : F)‖⁻¹ * (P * NA) ≤ ‖(2 : F)‖⁻¹ * P * D := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hDA hK
  have hEB : ‖(2 : F)‖⁻¹ * (P * NB) ≤ ‖(2 : F)‖⁻¹ * P * D := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hDB hK
  have hEA' : P * NA ≤ ‖(2 : F)‖⁻¹ * P * D :=
    (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hP h2) (basisOpNorm_nonneg _)).trans
      (by rw [mul_assoc, mul_assoc]; exact hEA.trans_eq (by ring))
  have hEB' : P * NB ≤ ‖(2 : F)‖⁻¹ * P * D :=
    (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hP h2) (basisOpNorm_nonneg _)).trans
      (by rw [mul_assoc, mul_assoc]; exact hEB.trans_eq (by ring))
  have hlenS := hs.1
  have hlenT := ht.1
  simp only [numPairs] at hlenS hlenT
  have hl := hf.lt
  have hAO := multiTorus_mem_orthogonalGroup hb hf t 0
  have hBO := multiTorus_mem_orthogonalGroup hb hf s 1
  intro i
  induction i with
  | zero =>
    intro p _
    rw [apply_bn_of_mem_fixer hh (by omega)]
    refine (hb.norm_polar_le _ _).trans ?_
    have e1 := basisNorm_bn_le (b := b) 0
    have e2 := basisNorm_bn_le (b := b) p
    have e3 := basisNorm_nonneg (b := b) (bn b 0)
    have e4 := basisNorm_nonneg (b := b) (bn b p)
    have : P * basisNorm b (bn b 0) * basisNorm b (bn b p) ≤ P := by
      calc P * basisNorm b (bn b 0) * basisNorm b (bn b p) ≤ P * 1 * 1 := by gcongr
        _ = P := by ring
    refine this.trans ((le_mul_of_one_le_left hP h2).trans ?_)
    exact le_mul_of_one_le_right hK hD1
  | succ i ih =>
    intro p hp
    by_cases hil : i + 1 ≤ l
    · obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' i
      · subst hk
        have e : 0 + 2 * k = 2 * k := by ring
        have := step_level hb hf ht hBO h (k := k) (by omega) hEA hEB'
          (fun hbad => by
            have hn : ¬ (k + 1 < t.length ∨ 0 + 2 * t.length < n) := fun h' =>
              hbad (ht.norm_le_one (by omega) h')
            exact multiTorus_apply_bn_of_ge hb hf s 1 (by omega))
          (fun p hp => by rw [e]; exact ih p (by omega)) p (by omega)
        rwa [e] at this
      · subst hk
        have e : 1 + 2 * k = 2 * k + 1 := by ring
        have := step_level hb hf hs hAO h (k := k) (by omega) hEB hEA'
          (fun hbad => by
            have hn : ¬ (k + 1 < s.length ∨ 1 + 2 * s.length < n) := fun h' =>
              hbad (hs.norm_le_one (by omega) h')
            exact multiTorus_apply_bn_of_ge hb hf t 0 (by omega))
          (fun p hp => by rw [e]; exact ih p (by omega)) p (by omega)
        rwa [e] at this
    · exact (norm_polar_le_of_fixed hb hAO h (multiTorus_apply_bn_of_ge hb hf t 0 (by omega))
        (multiTorus_apply_bn_of_ge hb hf t 0 (by omega)) (basisNorm_bn_le _)
        (basisNorm_bn_le _)).trans hEA'

include hb in
/-- `‖(T h T⁻¹)⁻¹‖ = ‖T h⁻¹ T⁻¹‖ ≤ κ ‖T h T⁻¹‖` for isometries `T`, `h`. -/
theorem basisOpNorm_conj_inv_le {T h : V ≃ₗ[F] V}
    (hT : T ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    basisOpNorm b ((T * h⁻¹ * T⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) ≤
      adjBound Q b * basisOpNorm b ((T * h * T⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) := by
  have e : T * h⁻¹ * T⁻¹ = (T * h * T⁻¹)⁻¹ := by group
  rw [e]
  exact hb.basisOpNorm_symm_le (mul_mem (mul_mem hT hh) (inv_mem hT))

include hb in
/-- **Thesis Prop. 8.1.1(iii), inequality (8.1.2), in codimension one** (BP Prop. 6.4.1(iii),
(6.4.8)), for `G₀ = SO(W) × SO(V₀)` and the good minimal parabolic `P̄₀ = P̄_W × P̄_{V₀}` of the
frame, over a non-archimedean field: `σ(h) ≪ σ(a⁻¹ h a)` for `h ∈ H = SO(W)` and
`a = (a_W, a_V) ∈ A₀⁺`, in the form `‖h‖ ≤ C max(1, ‖a_V⁻¹ h a_V‖, ‖a_W⁻¹ h a_W‖)` with
`a_V = (multiTorus hb hf 0 t)⁻¹`, `a_W = (multiTorus hb hf 1 s)⁻¹`, `s`, `t` in the contracting
chambers (the chambers of the orthogonal group, see the module docstring). -/
theorem norm_le_conj_of_mem_chamber :
    ∃ C : ℝ, ∀ h ∈ fixer Q b 1, ∀ s t : List Fˣ, InChamber n l 1 s → InChamber n l 0 t →
      basisOpNorm b (h : V →ₗ[F] V) ≤ C * max 1 (max
        (basisOpNorm b ((multiTorus hb hf 0 t * h * (multiTorus hb hf 0 t)⁻¹ : V ≃ₗ[F] V) :
          V →ₗ[F] V))
        (basisOpNorm b ((multiTorus hb hf 1 s * h * (multiTorus hb hf 1 s)⁻¹ : V ≃ₗ[F] V) :
          V →ₗ[F] V))) := by
  set Cq : ℝ := ‖fun p : Fin n => (2 * Q (b p))⁻¹‖
  set κ : ℝ := max 1 (adjBound Q b)
  set K : ℝ := ‖(2 : F)‖⁻¹ * polarBound Q b
  have hK : 0 ≤ K := mul_nonneg (by positivity) (norm_nonneg _)
  have hCq : 0 ≤ Cq := norm_nonneg _
  have hκ : 1 ≤ κ := le_max_left _ _
  have hκ' : adjBound Q b ≤ κ := le_max_right _ _
  refine ⟨Cq * (K * κ), fun h hh s t hs ht => ?_⟩
  set NA := basisOpNorm b ((multiTorus hb hf 0 t * h * (multiTorus hb hf 0 t)⁻¹ : V ≃ₗ[F] V) :
    V →ₗ[F] V)
  set NB := basisOpNorm b ((multiTorus hb hf 1 s * h * (multiTorus hb hf 1 s)⁻¹ : V ≃ₗ[F] V) :
    V →ₗ[F] V)
  set D := max 1 (max NA NB)
  have hD : 0 ≤ D := zero_le_one.trans (le_max_left _ _)
  have hhO := mem_orthogonalGroup_of_mem_fixer hh
  have hhi : h⁻¹ ∈ fixer Q b 1 := inv_mem hh
  -- the bound for `h⁻¹`
  have hDinv : max 1 (max
      (basisOpNorm b ((multiTorus hb hf 0 t * h⁻¹ * (multiTorus hb hf 0 t)⁻¹ : V ≃ₗ[F] V) :
        V →ₗ[F] V))
      (basisOpNorm b ((multiTorus hb hf 1 s * h⁻¹ * (multiTorus hb hf 1 s)⁻¹ : V ≃ₗ[F] V) :
        V →ₗ[F] V))) ≤ κ * D := by
    have a1 := basisOpNorm_conj_inv_le hb (multiTorus_mem_orthogonalGroup hb hf t 0) hhO
    have a2 := basisOpNorm_conj_inv_le hb (multiTorus_mem_orthogonalGroup hb hf s 1) hhO
    have hNA : 0 ≤ NA := basisOpNorm_nonneg _
    have hNB : 0 ≤ NB := basisOpNorm_nonneg _
    have hA : adjBound Q b * NA ≤ κ * D :=
      mul_le_mul hκ' ((le_max_left _ _).trans (le_max_right _ _)) hNA (by positivity)
    have hB : adjBound Q b * NB ≤ κ * D :=
      mul_le_mul hκ' ((le_max_right _ _).trans (le_max_right _ _)) hNB (by positivity)
    refine max_le ?_ (max_le (a1.trans hA) (a2.trans hB))
    nlinarith [le_max_left 1 (max NA NB)]
  -- all coefficients
  have hcoef : ∀ i p : Fin n, ‖polar Q (h (b i)) (b p)‖ ≤ K * (κ * D) := by
    intro i p
    rcases le_total i.val p.val with hip | hpi
    · have := norm_polar_le_conj hb hf hs ht hh i p hip
      rw [bn_of_lt i.isLt, bn_of_lt p.isLt] at this
      exact this.trans (mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_left hD hκ) hK)
    · have e : polar Q (h (b i)) (b p) = polar Q (h⁻¹ (b p)) (b i) := by
        rw [polar_comm, ← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
          (inv_mem hhO) (b p) (h (b i))]
        congr 1
        exact h.symm_apply_apply (b i)
      have := norm_polar_le_conj hb hf hs ht hhi p i hpi
      rw [bn_of_lt i.isLt, bn_of_lt p.isLt] at this
      rw [e]
      exact this.trans (mul_le_mul_of_nonneg_left hDinv hK)
  have hC : 0 ≤ Cq * (K * (κ * D)) :=
    mul_nonneg hCq (mul_nonneg hK (mul_nonneg (zero_le_one.trans hκ) hD))
  rw [mul_assoc, mul_assoc]
  refine (basisOpNorm_le_iff hC).2 fun i => (basisNorm_le_iff hC).2 fun p => ?_
  rw [LinearEquiv.coe_coe, hb.repr_eq_polar_div, polar_comm, div_eq_mul_inv, norm_mul, mul_comm]
  exact mul_le_mul (norm_le_pi_norm (fun p : Fin n => (2 * Q (b p))⁻¹) p) (hcoef i p)
    (norm_nonneg _) (norm_nonneg _)

/-! ## Inequality (I) -/

/-- A bound for the torus: if every coordinate satisfies `‖2‖⁻¹ max(|t|, |t|⁻¹) ≤ R` and
`1 ≤ R`, then `‖multiTorus j ts‖ ≤ R ^ length`. -/
theorem basisOpNorm_multiTorus_le {R : ℝ} (hR : 1 ≤ R) :
    ∀ (ts : List Fˣ) (j : ℕ), (∀ t ∈ ts, ‖(2 : F)‖⁻¹ * max ‖(t : F)‖ ‖(t : F)‖⁻¹ ≤ R) →
      basisOpNorm b ((multiTorus hb hf j ts : V ≃ₗ[F] V) : V →ₗ[F] V) ≤ R ^ ts.length
  | [], _, _ => by simpa using basisOpNorm_id_le (b := b)
  | t :: ts, j, h => by
    rw [multiTorus_cons, List.length_cons, pow_succ]
    refine (basisOpNorm_mul_le _ _).trans (mul_le_mul
      (basisOpNorm_multiTorus_le hR ts (j + 2) fun t ht => h t (List.mem_cons_of_mem _ ht))
      ?_ (basisOpNorm_nonneg _) (pow_nonneg (zero_le_one.trans hR) _))
    by_cases hj : j + 1 ≤ l
    · rw [levelTorus_of_le hb hf hj]
      exact (basisOpNorm_pairTorus_le hb _ _ _ t).trans (h t List.mem_cons_self)
    · rw [levelTorus_of_not_le hb hf hj]
      exact basisOpNorm_id_le.trans hR

/-- On the chamber, every coordinate is controlled by the first: `max(|t_k|, |t_k|⁻¹) ≤
max(|t_0|, |t_0|⁻¹)`. -/
theorem InChamber.max_le_head {j : ℕ} {ts : List Fˣ} (hts : InChamber n l j ts)
    (h0 : 0 < ts.length) {t : Fˣ} (ht : t ∈ ts) :
    max ‖(t : F)‖ ‖(t : F)‖⁻¹ ≤ max ‖(ts[0] : F)‖ ‖(ts[0] : F)‖⁻¹ := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ht
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact le_rfl
  obtain ⟨h1, h2⟩ := hts.rel_of_lt hk0 hk
  have p0 : (0 : ℝ) < ‖(ts[0] : F)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have pk : (0 : ℝ) < ‖(ts[k] : F)‖ := norm_pos_iff.2 (Units.ne_zero _)
  rw [norm_mul] at h2
  refine max_le (le_max_of_le_right ?_) (le_max_of_le_right ?_)
  · calc ‖(ts[k] : F)‖ = (‖(ts[0] : F)‖ * ‖(ts[k] : F)‖) * ‖(ts[0] : F)‖⁻¹ := by
          rw [mul_comm ‖(ts[0] : F)‖, mul_assoc, mul_inv_cancel₀ p0.ne', mul_one]
      _ ≤ (1 : ℝ) * ‖(ts[0] : F)‖⁻¹ := mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 p0.le)
      _ = _ := one_mul _
  · exact inv_anti₀ p0 h1

include hb in
/-- The first coordinate of the `V₀`-torus is read off from `h a_V`: for `h ∈ H`,
`|2ν| max(|t₀|, |t₀|⁻¹) ≤ c_P ‖h a_V‖` (Thesis (8.1.9): `b(h a_V u₁, w₀) = a¹ ν`, used for
`u_{±1}` so that no chamber condition is needed). -/
theorem norm_head_le {t : List Fˣ} (h0 : 0 < t.length) (hlen : t.length = numPairs l 0)
    {h : V ≃ₗ[F] V} (hh : h ∈ fixer Q b 1) :
    ‖2 * ν‖ * max ‖(t[0] : F)‖ ‖(t[0] : F)‖⁻¹ ≤
      polarBound Q b * basisOpNorm b ((h * (multiTorus hb hf 0 t)⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) := by
  simp only [numPairs] at hlen
  have hl1 : 0 + 2 * 0 + 1 ≤ l := by omega
  have hn : 0 < n := by have := hf.lt; omega
  set A := multiTorus hb hf 0 t
  set g := h * A⁻¹
  have hAO := multiTorus_mem_orthogonalGroup hb hf t 0
  have hhO := mem_orthogonalGroup_of_mem_fixer hh
  have hfix : h (bn b 0) = bn b 0 := apply_bn_of_mem_fixer hh (by omega)
  have hQ0 : Q (bn b 0) = ν := by
    rw [bn_of_lt hn]; simpa using hf.apply_eq ⟨0, hn⟩ (by simp)
  have hn1 : 1 < n := by have := hf.lt; omega
  have hp01 : polar Q (bn b 1) (bn b 0) = 0 := by
    rw [bn_of_lt hn, bn_of_lt hn1]; exact hb.polar_eq_zero _ _ (by simp [Fin.ext_iff])
  have hp00 : polar Q (bn b 0) (bn b 0) = 2 * ν := by
    rw [QuadraticMap.polar_self, two_nsmul, hQ0]; ring
  have hinv : ∀ (x : V) (α : F), α ≠ 0 → A x = α • x → A⁻¹ x = α⁻¹ • x := by
    intro x α hα hx
    have : A⁻¹ (A x) = x := A.symm_apply_apply x
    rw [hx, map_smul] at this
    calc A⁻¹ x = α⁻¹ • (α • A⁻¹ x) := by rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
      _ = α⁻¹ • x := by rw [this]
  have bound : ∀ (x : V) (β : F), A⁻¹ x = β • x → polar Q x (bn b 0) = 2 * ν →
      basisNorm b x ≤ 1 →
      ‖2 * ν‖ * ‖β‖ ≤ polarBound Q b * basisOpNorm b (g : V →ₗ[F] V) := by
    intro x β hx hpx hxn
    have e1 : g x = h (β • x) := by
      change h (A⁻¹ x) = _
      rw [hx]
    have e2 : polar Q (h (β • x)) (bn b 0) = polar Q (β • x) (bn b 0) := by
      conv_lhs => rw [← hfix]
      exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hhO _ _
    have e : polar Q (g x) (bn b 0) = β * (2 * ν) := by
      rw [e1, e2, polar_smul_left, smul_eq_mul, hpx]
    have := norm_polar_apply_le hb g x (bn b 0)
    rw [e, norm_mul, mul_comm] at this
    refine this.trans ?_
    have hP : 0 ≤ polarBound Q b * basisOpNorm b (g : V →ₗ[F] V) :=
      mul_nonneg (norm_nonneg _) (basisOpNorm_nonneg _)
    have e2 := basisNorm_bn_le (b := b) 0
    have e3 := basisNorm_nonneg (b := b) x
    calc polarBound Q b * basisOpNorm b (g : V →ₗ[F] V) * basisNorm b x * basisNorm b (bn b 0)
        = (polarBound Q b * basisOpNorm b (g : V →ₗ[F] V)) *
            (basisNorm b x * basisNorm b (bn b 0)) := by ring
      _ ≤ (polarBound Q b * basisOpNorm b (g : V →ₗ[F] V)) * 1 :=
          mul_le_mul_of_nonneg_left (by nlinarith) hP
      _ = _ := mul_one _
  have hu := multiTorus_apply_add hb hf t 0 0 h0 hl1
  have hv := multiTorus_apply_sub hb hf t 0 0 h0 hl1
  simp only [mul_zero, add_zero, zero_add] at hu hv
  have h1 := bound _ _ (hinv _ _ (Units.ne_zero _) hu)
    (by rw [polar_add_left, hp00, hp01, add_zero]) (basisNorm_bn_add_le _ _)
  have h2 := bound _ _ (hinv _ _ (inv_ne_zero (Units.ne_zero _)) hv)
    (by rw [polar_sub_left, hp00, hp01, sub_zero]) (basisNorm_bn_sub_le _ _)
  rw [norm_inv] at h1
  rw [inv_inv] at h2
  rw [mul_max_of_nonneg _ _ (norm_nonneg _)]
  exact max_le h2 h1

include hb in
/-- **Thesis Prop. 8.1.1(iii), inequality (8.1.1), in codimension one** (BP Prop. 6.4.1(iii),
(6.4.7)), for `G₀ = SO(W) × SO(V₀)` and the good minimal parabolic `P̄₀ = P̄_W × P̄_{V₀}` of the
frame, over a non-archimedean field: `σ(h) + σ(a) ≪ σ(h a)` for `h ∈ H = SO(W)` and
`a = (a_W, a_V) ∈ A₀⁺`, in the form
`max(‖h‖, ‖a_W‖, ‖a_V‖) ≤ C max(1, ‖h a_W‖, ‖h a_V‖)^N`, with `a_V = (multiTorus hb hf 0 t)⁻¹`,
`a_W = (multiTorus hb hf 1 s)⁻¹` and `t` in the contracting chamber of the `V₀`-torus (no
condition on `s` is needed). -/
theorem norm_le_of_mem_chamber :
    ∃ (C : ℝ) (N : ℕ), ∀ h ∈ fixer Q b 1, ∀ s t : List Fˣ, InChamber n l 0 t →
      max (basisOpNorm b (h : V →ₗ[F] V)) (max
        (basisOpNorm b (((multiTorus hb hf 1 s)⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V))
        (basisOpNorm b (((multiTorus hb hf 0 t)⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V))) ≤
      C * max 1 (max
        (basisOpNorm b ((h * (multiTorus hb hf 1 s)⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V))
        (basisOpNorm b ((h * (multiTorus hb hf 0 t)⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V))) ^ N := by
  set L := numPairs l 0
  set c : ℝ := ‖(2 : F)‖⁻¹ * max 1 (polarBound Q b * ‖2 * ν‖⁻¹)
  set κ : ℝ := max 1 (adjBound Q b)
  have h2 : 1 ≤ ‖(2 : F)‖⁻¹ := one_le_norm_two_inv
  have hc : 1 ≤ c := one_le_mul_of_one_le_of_one_le h2 (le_max_left _ _)
  have hκ : 1 ≤ κ := le_max_left _ _
  refine ⟨κ * c ^ L, L + 2, fun h hh s t ht => ?_⟩
  set A := multiTorus hb hf 0 t
  set B := multiTorus hb hf 1 s
  set NW := basisOpNorm b ((h * B⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V)
  set NV := basisOpNorm b ((h * A⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V)
  set M := max 1 (max NW NV)
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hNW : NW ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hNV : NV ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hlen : t.length = L := ht.1
  have hhO := mem_orthogonalGroup_of_mem_fixer hh
  -- the coordinates of the torus
  have hR : ∀ u ∈ t, ‖(2 : F)‖⁻¹ * max ‖(u : F)‖ ‖(u : F)‖⁻¹ ≤ c * M := by
    intro u hu
    have h0 : 0 < t.length := List.length_pos_of_mem hu
    have hν : ν ≠ 0 := by
      have hn : 0 < n := by have := hf.lt; omega
      have := hf.apply_eq ⟨0, hn⟩ (by simp)
      simp only [pow_zero, one_mul] at this
      exact this ▸ hb.apply_ne_zero _
    have h2ν : 0 < ‖2 * ν‖ := norm_pos_iff.2 (mul_ne_zero two_ne_zero hν)
    have hhead := norm_head_le hb hf h0 hlen hh
    have hmax := ht.max_le_head h0 hu
    have : max ‖(u : F)‖ ‖(u : F)‖⁻¹ ≤ max 1 (polarBound Q b * ‖2 * ν‖⁻¹) * M := by
      refine hmax.trans ?_
      rw [← le_div_iff₀' h2ν] at hhead
      refine hhead.trans ?_
      rw [div_eq_mul_inv, mul_right_comm]
      exact mul_le_mul (le_max_right _ _) hNV (basisOpNorm_nonneg _)
        (zero_le_one.trans (le_max_left _ _))
    calc ‖(2 : F)‖⁻¹ * max ‖(u : F)‖ ‖(u : F)‖⁻¹
        ≤ ‖(2 : F)‖⁻¹ * (max 1 (polarBound Q b * ‖2 * ν‖⁻¹) * M) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = c * M := by ring
  have hcM : 1 ≤ c * M := one_le_mul_of_one_le_of_one_le hc hM
  have hAn : basisOpNorm b (A : V →ₗ[F] V) ≤ (c * M) ^ L := by
    rw [← hlen]; exact basisOpNorm_multiTorus_le hb hf hcM t 0 hR
  have hAin : basisOpNorm b ((A⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) ≤ (c * M) ^ L := by
    rw [← multiTorus_map_inv, ← hlen, ← List.length_map (f := fun x : Fˣ => x⁻¹)]
    refine basisOpNorm_multiTorus_le hb hf hcM _ 0 fun u hu => ?_
    obtain ⟨u', hu', rfl⟩ := List.mem_map.1 hu
    have := hR u' hu'
    rwa [Units.val_inv_eq_inv_val, norm_inv, inv_inv, max_comm]
  have hpow : (c * M) ^ L = c ^ L * M ^ L := mul_pow _ _ _
  have hcL : 0 ≤ c ^ L := pow_nonneg (zero_le_one.trans hc) _
  -- `‖h‖ ≤ ‖h a_V‖ ‖a_V⁻¹‖`
  have hh' : basisOpNorm b (h : V →ₗ[F] V) ≤ c ^ L * M ^ (L + 1) := by
    have e : h = (h * A⁻¹) * A := by group
    calc basisOpNorm b (h : V →ₗ[F] V) = basisOpNorm b (((h * A⁻¹) * A : V ≃ₗ[F] V) :
          V →ₗ[F] V) := by rw [← e]
      _ ≤ NV * basisOpNorm b (A : V →ₗ[F] V) := basisOpNorm_mul_le _ _
      _ ≤ M * (c ^ L * M ^ L) := mul_le_mul hNV (hAn.trans_eq hpow) (basisOpNorm_nonneg _) hM0
      _ = c ^ L * M ^ (L + 1) := by ring
  -- `‖a_W‖ ≤ ‖h⁻¹‖ ‖h a_W‖`
  have hBn : basisOpNorm b ((B⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) ≤ κ * c ^ L * M ^ (L + 2) := by
    have e : B⁻¹ = h⁻¹ * (h * B⁻¹) := by group
    have hhi : basisOpNorm b ((h⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) ≤ κ * (c ^ L * M ^ (L + 1)) :=
      (hb.basisOpNorm_symm_le hhO).trans (mul_le_mul (le_max_right _ _) hh'
        (basisOpNorm_nonneg _) (zero_le_one.trans hκ))
    calc basisOpNorm b ((B⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) = basisOpNorm b
          ((h⁻¹ * (h * B⁻¹) : V ≃ₗ[F] V) : V →ₗ[F] V) := by rw [← e]
      _ ≤ basisOpNorm b ((h⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) * NW := basisOpNorm_mul_le _ _
      _ ≤ κ * (c ^ L * M ^ (L + 1)) * M := mul_le_mul hhi hNW (basisOpNorm_nonneg _)
          (by positivity)
      _ = κ * c ^ L * M ^ (L + 2) := by ring
  have hM1 : M ^ (L + 1) ≤ M ^ (L + 2) := pow_le_pow_right₀ hM (by omega)
  have hML : M ^ L ≤ M ^ (L + 2) := pow_le_pow_right₀ hM (by omega)
  have hκc : c ^ L ≤ κ * c ^ L := le_mul_of_one_le_left hcL hκ
  refine max_le ?_ (max_le ?_ ?_)
  · exact hh'.trans (mul_le_mul hκc hM1 (by positivity) (by positivity))
  · exact hBn
  · exact (hAin.trans_eq hpow).trans (mul_le_mul hκc hML (by positivity) (by positivity))

end Main

end WeakCartan

end GSpinGGP
