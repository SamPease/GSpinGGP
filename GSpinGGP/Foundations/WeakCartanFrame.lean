/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.WeakCartanRotation
import GSpinGGP.Foundations.HypFrame

/-!
# Frames, split tori and chambers for the weak Cartan decomposition of `SO(V₀)`

Let `b` be an orthogonal basis of anisotropic vectors of a quadratic space `(V, Q)` (over a
non-archimedean, p-adic, field for the decomposition itself). A *frame of
length `l`* is the statement that the first `l + 1` basis vectors have `Q (b i) = (-1)ⁱ ν`
and that no vector with coordinates `≤ l` zero (equivalently, orthogonal to them, given
`IsOrthoBasis`) has `Q = (-1)^{l+1} ν` (maximality). The *level* `j ≤ l`
is the subgroup `G_j = fixer Q b j` of `SO(Q)` fixing `b 0, …, b (j-1)`; it is the special
orthogonal group of `span (b j, b (j+1), …)` relative to `v₀ = b j`, and `G_{j+1}` is the
stabilizer of `v₀`. This is the set-up of the weak Cartan decomposition (Thesis Prop. 8.3.1,
the orthogonal analogue of Prop. 11.0.1 in §11 of Beuzart-Plessis's thèse).

* `levelTorus hb hf j t`: the split torus `a(t)` of the hyperbolic plane `⟨b j, b (j+1)⟩`
  (`pairTorus`), for `j + 1 ≤ l`.
* `multiTorus hb hf j [t₀, t₁, …]`: the split torus of level `j`, the product of the
  `levelTorus (j + 2i) tᵢ`. Its coordinates act on `u_{±i} = b (j+2i) ± b (j+2i+1)` by
  `t_i^{±1}`.
* `InChamber n l j ts`: the chamber of `multiTorus j ts` contracting the flag
  `⟨u₁⟩ ⊂ ⟨u₁, u₂⟩ ⊂ …`, i.e. `|α| ≤ 1` for every root `α` of that flag stabilizer:
  `tᵢ / tₖ` and `tᵢ tₖ` for `i < k`, and `tᵢ` when the anisotropic part of level `j` is nonzero
  (types B, D and, for one pair without anisotropic part, the torus T).
* `IsFrame.unitsSMul`, `fixer_unitsSMul`: rescaling the basis by units `wᵢ` (Mathlib's
  `Module.Basis.unitsSMul`) keeps the fixers, and keeps the frame when `wᵢ² = 1` on it.
* `signBasis e b`: the basis `((-1)^{e i} b i)`; it is again a frame with the same fixers, and
  the torus of a pair is unchanged or inverted according as its two signs agree or not
  (`levelTorus_signBasis`, `multiTorus_signBasis_of_even`, `multiTorus_signBasis_of_odd`). For
  `e = id` both flags are reversed.
* `inChamber_cons`: the chamber adjustment for the induction.
* `isHypFrame_pair`, `multiTorus_mem_hypTorus`: the pairs of level `j` form a hyperbolic frame
  (`IsHypFrame`) with complement the span of the other basis vectors, and the split torus of level
  `j` lies in its torus `hypTorus`.
* `exists_isFrame`: in a nondegenerate quadratic space every anisotropic vector starts a maximal
  frame of an orthogonal basis.
* `basisNat`, `multiTorus_apply_add`, `multiTorus_apply_sub`, `multiTorus_apply_pairE`,
  `multiTorus_apply_pairF`: the eigenvectors `b (j+2k) ± b (j+2k+1)` of the level-`j` torus;
  `basisOpNorm_multiTorus_le`: a bound for its norm.
* `InChamber.rel_of_lt`, `InChamber.norm_le_one`, `InChamber.max_le_head`: chamber inequalities.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Module QuadraticMap

namespace GSpinGGP

namespace WeakCartan

variable {F : Type*} [NontriviallyNormedField F] [CharZero F]
variable {V : Type*} [AddCommGroup V] [Module F V] {n : ℕ} {b : Module.Basis (Fin n) F V}
  {Q : QuadraticForm F V}

/-! ## Frames and levels -/

/-- The first `l + 1` vectors of `b` form a maximal frame for `ν`: `Q (b i) = (-1)ⁱ ν` for
`i ≤ l`, and no vector with coordinates `≤ l` zero (equivalently orthogonal to them, given
`IsOrthoBasis`) has `Q = (-1)^{l+1} ν`. -/
structure IsFrame (Q : QuadraticForm F V) (b : Module.Basis (Fin n) F V) (ν : F) (l : ℕ) :
    Prop where
  lt : l < n
  apply_eq : ∀ i : Fin n, i.val ≤ l → Q (b i) = (-1) ^ i.val * ν
  maximal : ∀ x : V, (∀ i : Fin n, i.val ≤ l → b.repr x i = 0) → Q x ≠ (-1) ^ (l + 1) * ν

variable [FiniteDimensional F V]

/-- The level `j` group: elements of `SO(Q)` fixing `b i` for `i < j`. -/
def fixer (Q : QuadraticForm F V) (b : Module.Basis (Fin n) F V) (j : ℕ) :
    Subgroup (V ≃ₗ[F] V) where
  carrier := {g | g ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q ∧
    ∀ i : Fin n, i.val < j → g (b i) = b i}
  one_mem' := ⟨one_mem _, fun _ _ => rfl⟩
  mul_mem' := fun {g h} hg hh => ⟨mul_mem hg.1 hh.1, fun i hi => by
    rw [LinearEquiv.mul_apply, hh.2 i hi, hg.2 i hi]⟩
  inv_mem' := fun {g} hg => ⟨inv_mem hg.1, fun i hi => by
    conv_lhs => rw [← hg.2 i hi]
    exact g.symm_apply_apply (b i)⟩

theorem mem_fixer_iff {j : ℕ} {g : V ≃ₗ[F] V} :
    g ∈ fixer Q b j ↔ g ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q ∧
      ∀ i : Fin n, i.val < j → g (b i) = b i := Iff.rfl

theorem fixer_anti {j j' : ℕ} (h : j ≤ j') : fixer Q b j' ≤ fixer Q b j :=
  fun _ hg => ⟨hg.1, fun i hi => hg.2 i (lt_of_lt_of_le hi h)⟩

theorem mem_orthogonalGroup_of_mem_fixer {j : ℕ} {g : V ≃ₗ[F] V} (hg : g ∈ fixer Q b j) :
    g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  TauCeti.QuadraticMap.specialOrthogonalGroup_le_orthogonalGroup Q hg.1

section Level

variable {ν : F} {l : ℕ}

theorem IsFrame.idx_lt (hf : IsFrame Q b ν l) {j : ℕ} (hj : j ≤ l) : j < n :=
  lt_of_le_of_lt hj hf.lt

theorem IsFrame.apply_left (hf : IsFrame Q b ν l) {j : ℕ} (hj : j + 1 ≤ l) :
    Q (b ⟨j, hf.idx_lt (by omega)⟩) = (-1) ^ j * ν :=
  hf.apply_eq _ (by simp only; omega)

theorem IsFrame.apply_right (hf : IsFrame Q b ν l) {j : ℕ} (hj : j + 1 ≤ l) :
    Q (b ⟨j + 1, hf.idx_lt hj⟩) = -((-1) ^ j * ν) := by
  rw [hf.apply_eq _ hj]; simp only [pow_succ]; ring

private theorem mk_ne_mk_add_one {j : ℕ} (h₀ : j < n) (h₁ : j + 1 < n) :
    (⟨j, h₀⟩ : Fin n) ≠ ⟨j + 1, h₁⟩ :=
  Fin.ne_of_val_ne (Nat.ne_add_one j)

/-- The split torus `a(t)` of the hyperbolic plane `⟨b j, b (j+1)⟩` (for `j + 1 ≤ l`; the
identity otherwise). -/
def levelTorus (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l) (j : ℕ) (t : Fˣ) :
    V ≃ₗ[F] V :=
  if hj : j + 1 ≤ l then
    pairTorus hb (mk_ne_mk_add_one (hf.idx_lt (by omega)) (hf.idx_lt hj)) (hf.apply_left hj)
      (hf.apply_right hj) t
  else 1

variable (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l)

theorem levelTorus_of_le {j : ℕ} (hj : j + 1 ≤ l) (t : Fˣ) :
    levelTorus hb hf j t = pairTorus hb (mk_ne_mk_add_one (hf.idx_lt (by omega)) (hf.idx_lt hj))
      (hf.apply_left hj) (hf.apply_right hj) t := by
  rw [levelTorus, dite_eq_left hj]

theorem levelTorus_of_not_le {j : ℕ} (hj : ¬ j + 1 ≤ l) (t : Fˣ) :
    levelTorus hb hf j t = 1 := by
  rw [levelTorus, dite_eq_right hj]

theorem levelTorus_mul (j : ℕ) (s t : Fˣ) :
    levelTorus hb hf j (s * t) = levelTorus hb hf j s * levelTorus hb hf j t := by
  by_cases hj : j + 1 ≤ l
  · simp only [levelTorus_of_le hb hf hj, pairTorus_mul]
  · simp [levelTorus_of_not_le hb hf hj]

theorem levelTorus_inv (j : ℕ) (t : Fˣ) :
    levelTorus hb hf j t⁻¹ = (levelTorus hb hf j t)⁻¹ := by
  by_cases hj : j + 1 ≤ l
  · simp only [levelTorus_of_le hb hf hj, pairTorus_inv]
  · simp [levelTorus_of_not_le hb hf hj]

theorem levelTorus_mem_fixer (j : ℕ) (t : Fˣ) : levelTorus hb hf j t ∈ fixer Q b j := by
  by_cases hj : j + 1 ≤ l
  · rw [levelTorus_of_le hb hf hj]
    refine ⟨pairTorus_mem_specialOrthogonalGroup _ _ _ _ _, fun i hi => ?_⟩
    exact pairTorus_apply_basis_of_ne _ _ _ _ _ (by simp [Fin.ext_iff]; omega)
      (by simp [Fin.ext_iff]; omega)
  · rw [levelTorus_of_not_le hb hf hj]; exact one_mem _

end Level

/-! ## Commutation with the pair torus -/

theorem levelTorus_commute {ν : F} {l : ℕ} (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l)
    {j : ℕ} {x : V ≃ₗ[F] V} (hx : x ∈ fixer Q b (j + 2)) (t : Fˣ) :
    x * levelTorus hb hf j t = levelTorus hb hf j t * x := by
  by_cases hj : j + 1 ≤ l
  · rw [levelTorus_of_le hb hf hj]
    exact pairTorus_commute _ _ _ _ (mem_orthogonalGroup_of_mem_fixer hx)
      (hx.2 _ (by simp)) (hx.2 _ (by simp)) t
  · simp [levelTorus_of_not_le hb hf hj]

/-! ## The split torus of a level -/

section Multi

variable {ν : F} {l : ℕ} (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l)

/-- The split torus of level `j`: `multiTorus j [t₀, t₁, …] = ⋯ a_{j+2}(t₁) a_j(t₀)`, acting on
`b (j+2i) ± b (j+2i+1)` by `tᵢ^{±1}`. -/
def multiTorus : ℕ → List Fˣ → V ≃ₗ[F] V
  | _, [] => 1
  | j, t :: ts => multiTorus (j + 2) ts * levelTorus hb hf j t

@[simp]
theorem multiTorus_nil (j : ℕ) : multiTorus hb hf j [] = 1 := rfl

theorem multiTorus_cons (j : ℕ) (t : Fˣ) (ts : List Fˣ) :
    multiTorus hb hf j (t :: ts) = multiTorus hb hf (j + 2) ts * levelTorus hb hf j t := rfl

theorem multiTorus_mem_fixer (ts : List Fˣ) : ∀ j, multiTorus hb hf j ts ∈ fixer Q b j := by
  induction ts with
  | nil => intro j; exact one_mem _
  | cons t ts ih =>
    intro j
    exact mul_mem (fixer_anti (by omega) (ih (j + 2))) (levelTorus_mem_fixer hb hf j t)

theorem multiTorus_map_inv (ts : List Fˣ) :
    ∀ j, multiTorus hb hf j (ts.map (·⁻¹)) = (multiTorus hb hf j ts)⁻¹ := by
  induction ts with
  | nil => intro j; simp
  | cons t ts ih =>
    intro j
    rw [List.map_cons, multiTorus_cons, multiTorus_cons, ih, levelTorus_inv, mul_inv_rev]
    exact ((Commute.inv_inv (levelTorus_commute hb hf
      (multiTorus_mem_fixer hb hf ts (j + 2)) t))).eq

end Multi

/-! ## Changing the signs of the basis -/

section Sign

/-- Rescaling the basis by units with `wᵢ² = 1` for `i ≤ l` keeps the frame. -/
theorem IsFrame.unitsSMul {ν : F} {l : ℕ} (hf : IsFrame Q b ν l) (w : Fin n → Fˣ)
    (hw : ∀ i : Fin n, i.val ≤ l → (w i : F) ^ 2 = 1) : IsFrame Q (b.unitsSMul w) ν l where
  lt := hf.lt
  apply_eq i hi := by rw [apply_unitsSMul, hw i hi, one_mul]; exact hf.apply_eq i hi
  maximal x hx := hf.maximal x fun i hi => by
    have := hx i hi
    rwa [Module.Basis.repr_unitsSMul, smul_eq_zero_iff_eq] at this

/-- Rescaling the basis by units does not change the fixers. -/
theorem fixer_unitsSMul (w : Fin n → Fˣ) (j : ℕ) : fixer Q (b.unitsSMul w) j = fixer Q b j := by
  ext g
  simp only [mem_fixer_iff, Module.Basis.unitsSMul_apply, Units.smul_def, map_smul]
  refine and_congr_right fun _ => forall_congr' fun i => imp_congr_right fun _ => ?_
  exact smul_right_inj (w i).ne_zero

variable (e : ℕ → ℕ)

/-- The basis `((-1)^{e i} b i)`. -/
def signBasis (b : Module.Basis (Fin n) F V) : Module.Basis (Fin n) F V :=
  b.unitsSMul fun i => (-1) ^ e i.val

theorem signBasis_apply (i : Fin n) : signBasis e b i = ((-1 : F) ^ e i.val) • b i := by
  rw [signBasis, Module.Basis.unitsSMul_apply, Units.smul_def]; simp

theorem _root_.GSpinGGP.IsOrthoBasis.signBasis (hb : IsOrthoBasis Q b) :
    IsOrthoBasis Q (signBasis e b) :=
  hb.unitsSMul _

theorem IsFrame.signBasis {ν : F} {l : ℕ} (hf : IsFrame Q b ν l) :
    IsFrame Q (signBasis e b) ν l :=
  hf.unitsSMul _ fun i _ => by simp [← pow_mul]

theorem fixer_signBasis (j : ℕ) : fixer Q (signBasis e b) j = fixer Q b j :=
  fixer_unitsSMul _ j

/-- Changing the signs of the basis: the torus of the pair `(b j, b (j+1))` is unchanged if the
two signs agree and inverted if they differ. -/
theorem levelTorus_signBasis {ν : F} {l : ℕ} (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l)
    (j : ℕ) (t : Fˣ) :
    levelTorus (hb.signBasis e) (hf.signBasis e) j t =
      levelTorus hb hf j (if Odd (e j + e (j + 1)) then t⁻¹ else t) := by
  set t' : Fˣ := if Odd (e j + e (j + 1)) then t⁻¹ else t
  set σ : F := (-1) ^ e j with hσd
  set σ' : F := (-1) ^ e (j + 1) with hσd'
  have hσ : σ * σ = 1 := by rw [← mul_pow]; norm_num
  have hσ' : σ' * σ' = 1 := by rw [← mul_pow]; norm_num
  have hc : ((t' : F) + (t' : F)⁻¹) / 2 = ((t : F) + (t : F)⁻¹) / 2 := by
    simp only [t']; split_ifs <;> simp [add_comm]
  have hs : ((t' : F) - (t' : F)⁻¹) / 2 = σ * σ' * (((t : F) - (t : F)⁻¹) / 2) := by
    have hδ : σ * σ' = (-1) ^ (e j + e (j + 1)) := by rw [pow_add]
    simp only [t']; split_ifs with h
    · rw [hδ, h.neg_one_pow, Units.val_inv_eq_inv_val, inv_inv]; ring
    · rw [hδ, (Nat.not_odd_iff_even.1 h).neg_one_pow]; ring
  by_cases hj : j + 1 ≤ l
  · rw [levelTorus_of_le _ _ hj, levelTorus_of_le _ _ hj]
    refine b.ext' fun m => ?_
    by_cases hm₀ : m = ⟨j, hf.idx_lt (by omega)⟩
    · subst hm₀
      have e0 := pairTorus_apply_left (hb.signBasis e)
        (mk_ne_mk_add_one (hf.idx_lt (by omega)) (hf.idx_lt hj)) ((hf.signBasis e).apply_left hj)
        ((hf.signBasis e).apply_right hj) t
      simp only [signBasis_apply, map_smul] at e0
      rw [← hσd, ← hσd'] at e0
      rw [pairTorus_apply_left, hc, hs]
      calc _ = σ • σ • _ := by rw [smul_smul, hσ, one_smul]
        _ = _ := by
          rw [e0, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
          congr 1 <;> congr 1
          · linear_combination ((t : F) + (t : F)⁻¹) / 2 * hσ
          · ring
    by_cases hm₁ : m = ⟨j + 1, hf.idx_lt hj⟩
    · subst hm₁
      have e0 := pairTorus_apply_right (hb.signBasis e)
        (mk_ne_mk_add_one (hf.idx_lt (by omega)) (hf.idx_lt hj)) ((hf.signBasis e).apply_left hj)
        ((hf.signBasis e).apply_right hj) t
      simp only [signBasis_apply, map_smul] at e0
      rw [← hσd, ← hσd'] at e0
      rw [pairTorus_apply_right, hc, hs]
      calc _ = σ' • σ' • _ := by rw [smul_smul, hσ', one_smul]
        _ = _ := by
          rw [e0, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
          congr 1 <;> congr 1
          · ring
          · linear_combination ((t : F) + (t : F)⁻¹) / 2 * hσ'
    · have e0 := pairTorus_apply_basis_of_ne (hb.signBasis e)
        (mk_ne_mk_add_one (hf.idx_lt (by omega)) (hf.idx_lt hj)) ((hf.signBasis e).apply_left hj)
        ((hf.signBasis e).apply_right hj) t hm₀ hm₁
      rw [signBasis_apply, map_smul] at e0
      rw [pairTorus_apply_basis_of_ne _ _ _ _ _ hm₀ hm₁]
      exact (smul_right_injective V (pow_ne_zero _ (by norm_num : (-1 : F) ≠ 0))) e0
  · simp [levelTorus_of_not_le _ _ hj]

/-- If every pair of level `j` changes relative sign, the level-`j` torus is inverted. -/
theorem multiTorus_signBasis_of_odd {ν : F} {l : ℕ} (hb : IsOrthoBasis Q b)
    (hf : IsFrame Q b ν l) (ts : List Fˣ) :
    ∀ j, (∀ k, Odd (e (j + 2 * k) + e (j + 2 * k + 1))) →
      multiTorus (hb.signBasis e) (hf.signBasis e) j ts = multiTorus hb hf j (ts.map (·⁻¹)) := by
  induction ts with
  | nil => intro j _; rfl
  | cons t ts ih =>
    intro j h
    rw [List.map_cons, multiTorus_cons, multiTorus_cons, ih (j + 2) (fun k => by
      have := h (k + 1); rwa [show j + 2 * (k + 1) = j + 2 + 2 * k by ring] at this),
      levelTorus_signBasis, ite_eq_left (by simpa using h 0)]

/-- If no pair of level `j` changes relative sign, the level-`j` torus is unchanged. -/
theorem multiTorus_signBasis_of_even {ν : F} {l : ℕ} (hb : IsOrthoBasis Q b)
    (hf : IsFrame Q b ν l) (ts : List Fˣ) :
    ∀ j, (∀ k, Even (e (j + 2 * k) + e (j + 2 * k + 1))) →
      multiTorus (hb.signBasis e) (hf.signBasis e) j ts = multiTorus hb hf j ts := by
  induction ts with
  | nil => intro j _; rfl
  | cons t ts ih =>
    intro j h
    rw [multiTorus_cons, multiTorus_cons, ih (j + 2) (fun k => by
      have := h (k + 1); rwa [show j + 2 * (k + 1) = j + 2 + 2 * k by ring] at this),
      levelTorus_signBasis, ite_eq_right (Nat.not_odd_iff_even.2 (by simpa using h 0))]

end Sign

/-! ## Chambers -/

/-- The number of hyperbolic pairs `(b (j+2i), b (j+2i+1))` of level `j` inside the frame. -/
def numPairs (l j : ℕ) : ℕ := (l + 1 - j) / 2

/-- The contracting chamber of the level-`j` torus: `|α(a)| ≤ 1` for the roots `tᵢ / tₖ`,
`tᵢ tₖ` (`i < k`) and, when the anisotropic part `span (b m : j + 2 r ≤ m)` is nonzero, `tᵢ`.
Here `r = numPairs l j` is the number of coordinates. -/
def InChamber (n l j : ℕ) (ts : List Fˣ) : Prop :=
  ts.length = numPairs l j ∧
    ts.Pairwise (fun s t : Fˣ => ‖(s : F)‖ ≤ ‖(t : F)‖ ∧ ‖(s : F) * t‖ ≤ 1) ∧
    (j + 2 * ts.length < n → ∀ t ∈ ts, ‖(t : F)‖ ≤ 1)

theorem inChamber_nil {n l j : ℕ} (h : l ≤ j) : InChamber (F := F) n l j [] :=
  ⟨by simp [numPairs]; omega, List.Pairwise.nil, fun _ _ h => by simp at h⟩

/-- **Chamber adjustment.** Prepending to a chamber element of level `j + 2` a coordinate
`t` with `‖t‖ ≤ min(1, ‖t₁‖, ‖t₁‖⁻¹)` gives a chamber element of level `j`. -/
theorem inChamber_cons {n l j : ℕ} (hj : j + 1 ≤ l) {t t₁ : Fˣ} {ts : List Fˣ}
    (h : InChamber n l (j + 2) (t₁ :: ts)) (ht1 : ‖(t : F)‖ ≤ 1)
    (ht₁ : ‖(t : F)‖ ≤ ‖(t₁ : F)‖) (ht₁' : ‖(t : F)‖ * ‖(t₁ : F)‖ ≤ 1) :
    InChamber n l j (t :: t₁ :: ts) := by
  obtain ⟨hlen, hpw, han⟩ := h
  refine ⟨by simp only [List.length_cons] at hlen ⊢; simp only [numPairs] at hlen ⊢; omega,
    List.Pairwise.cons (fun s hs => ?_) hpw, fun hn s hs => ?_⟩
  · rcases List.mem_cons.1 hs with rfl | hs
    · exact ⟨ht₁, by rw [norm_mul]; exact ht₁'⟩
    · have h1 := (List.pairwise_cons.1 hpw).1 s hs
      refine ⟨ht₁.trans h1.1, ?_⟩
      rw [norm_mul]
      calc ‖(t : F)‖ * ‖(s : F)‖ ≤ ‖(t₁ : F)‖ * ‖(s : F)‖ :=
            mul_le_mul_of_nonneg_right ht₁ (norm_nonneg _)
        _ ≤ 1 := by rw [← norm_mul]; exact h1.2
  · rcases List.mem_cons.1 hs with rfl | hs
    · exact ht1
    · exact han (by simp only [List.length_cons] at hn ⊢; omega) s hs

/-- A single coordinate: the only condition is `‖t‖ ≤ 1` when the anisotropic part is nonzero. -/
theorem inChamber_single {n l j : ℕ} (hj : j + 1 ≤ l) (hl : l ≤ j + 2) {t : Fˣ}
    (ht : j + 2 < n → ‖(t : F)‖ ≤ 1) : InChamber n l j [t] :=
  ⟨by simp [numPairs]; omega, List.pairwise_singleton _ _,
    fun hn s hs => by rw [List.mem_singleton.1 hs]; exact ht (by simpa using hn)⟩

/-- In the chamber of level `j + 1` with at least three frame vectors after `b (j+1)`, the first
coordinate has `‖s‖ ≤ 1` (it is a root in type B, and `|s₀|² ≤ |s₀ s₁| ≤ 1` in type D). -/
theorem InChamber.norm_head_le_one {n l j : ℕ} (hl : j + 3 ≤ l) (hn : l < n) {s : Fˣ}
    {ss : List Fˣ} (h : InChamber n l (j + 1) (s :: ss)) : ‖(s : F)‖ ≤ 1 := by
  obtain ⟨hlen, hpw, han⟩ := h
  simp only [List.length_cons, numPairs] at hlen
  by_cases han' : j + 1 + 2 * (s :: ss).length < n
  · exact han han' s (by simp)
  · simp only [List.length_cons] at han'
    obtain ⟨s', ss', rfl⟩ : ∃ s' ss', ss = s' :: ss' := by
      cases ss with
      | nil => simp at hlen han'; omega
      | cons s' ss' => exact ⟨s', ss', rfl⟩
    have h1 := (List.pairwise_cons.1 hpw).1 s' (by simp)
    have h2 : ‖(s : F)‖ * ‖(s : F)‖ ≤ 1 := by
      calc ‖(s : F)‖ * ‖(s : F)‖ ≤ ‖(s : F)‖ * ‖(s' : F)‖ :=
            mul_le_mul_of_nonneg_left h1.1 (norm_nonneg _)
        _ ≤ 1 := by rw [← norm_mul]; exact h1.2
    nlinarith [norm_nonneg (s : F)]

/-! ## The hyperbolic frame of a level

The pairs `(b (j+2i), b (j+2i+1))`, `i < numPairs l j`, give the hyperbolic frame
`eᵢ = b (j+2i) + b (j+2i+1)`, `fᵢ = (4 (-1)^{j+2i} ν)⁻¹ (b (j+2i) - b (j+2i+1))` of
`HypFrame.lean` (`isHypFrame_pair`), whose complement is the span of the other basis vectors, and
the split torus of level `j` lies in its torus (`multiTorus_mem_hypTorus`). -/

section HypFrame

variable {ν : F} {l : ℕ}

theorem add_one_le_of_lt_numPairs {j i : ℕ} (hi : i < numPairs l j) :
    j + 2 * i + 1 ≤ l := by
  simp only [numPairs] at hi; omega

private theorem pair_idx_ne {j i k : ℕ} (h : i ≠ k) :
    j + 2 * i ≠ j + 2 * k ∧ j + 2 * i + 1 ≠ j + 2 * k ∧ j + 2 * i ≠ j + 2 * k + 1 ∧
      j + 2 * i + 1 ≠ j + 2 * k + 1 := by
  omega

/-- The isotropic vectors `b (j+2i) + b (j+2i+1)` of the pairs of level `j`. -/
def pairE (hf : IsFrame Q b ν l) (j : ℕ) (i : Fin (numPairs l j)) : V :=
  b ⟨j + 2 * i, hf.idx_lt (by have := add_one_le_of_lt_numPairs i.2; omega)⟩ +
    b ⟨j + 2 * i + 1, hf.idx_lt (add_one_le_of_lt_numPairs i.2)⟩

theorem pairE_mem_span (hf : IsFrame Q b ν l) (j : ℕ) (i : Fin (numPairs l j)) {M : ℕ}
    (hM : j + 2 * (i : ℕ) + 1 < M) :
    pairE hf j i ∈ Submodule.span F (b '' {m | m.val < M}) :=
  add_mem (Submodule.subset_span ⟨_, by simp only [Set.mem_ofPred_eq]; omega, rfl⟩)
    (Submodule.subset_span ⟨_, by simp only [Set.mem_ofPred_eq]; omega, rfl⟩)

/-- The isotropic vectors `(4 (-1)^{j+2i} ν)⁻¹ (b (j+2i) - b (j+2i+1))` of the pairs of level
`j`, dual to `pairE`. -/
def pairF (hf : IsFrame Q b ν l) (j : ℕ) (i : Fin (numPairs l j)) : V :=
  (4 * ((-1) ^ (j + 2 * i.val) * ν))⁻¹ •
    (b ⟨j + 2 * i, hf.idx_lt (by have := add_one_le_of_lt_numPairs i.2; omega)⟩ -
      b ⟨j + 2 * i + 1, hf.idx_lt (add_one_le_of_lt_numPairs i.2)⟩)

/-- The span of the basis vectors outside the pairs of level `j`. -/
def pairCompl (b : Module.Basis (Fin n) F V) (l j : ℕ) : Submodule F V :=
  Submodule.span F (b '' {m | ¬ (j ≤ m.val ∧ m.val < j + 2 * numPairs l j)})

private theorem polar_basis_basis (hb : IsOrthoBasis Q b) (p q : Fin n) :
    polar Q (b p) (b q) = if p.val = q.val then 2 * Q (b p) else 0 := by
  rw [polar_basis_left Q b hb.isOrtho, b.repr_self, Finsupp.single_apply]
  by_cases h : q = p
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (Fin.ext h'.symm)), mul_zero]

/-- **The pairs of level `j` form a hyperbolic frame**, with complement the span of the other
basis vectors. -/
theorem isHypFrame_pair (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l) (j : ℕ) :
    IsHypFrame Q (pairCompl b l j) (pairE hf j) (pairF hf j) where
  polar_ee i k := by
    by_cases hik : i = k
    · subst hik
      have hj := add_one_le_of_lt_numPairs i.2
      rw [polar_self, pairE, pairU_isotropic hb (mk_ne_mk_add_one _ _) (hf.apply_left hj)
        (hf.apply_right hj), smul_zero]
    · obtain ⟨h1, h2, h3, h4⟩ := pair_idx_ne (j := j) (Fin.val_ne_of_ne hik)
      simp only [pairE, polar_add_left, polar_add_right, polar_basis_basis hb, h1, h2, h3, h4,
        ↓reduceIte, add_zero]
  polar_ff i k := by
    by_cases hik : i = k
    · subst hik
      have hj := add_one_le_of_lt_numPairs i.2
      rw [polar_self, pairF, pairV_scaled_isotropic hb (mk_ne_mk_add_one _ _) (hf.apply_left hj)
        (hf.apply_right hj), smul_zero]
    · obtain ⟨h1, h2, h3, h4⟩ := pair_idx_ne (j := j) (Fin.val_ne_of_ne hik)
      simp only [pairF, polar_smul_left, polar_smul_right, polar_sub_left, polar_sub_right,
        polar_basis_basis hb, h1, h2, h3, h4, ↓reduceIte, sub_self, smul_zero]
  polar_ef i k := by
    by_cases hik : i = k
    · subst hik
      have hj := add_one_le_of_lt_numPairs i.2
      rw [ite_eq_left_iff.2 (fun h => absurd rfl h), pairE, pairF]
      exact polar_pairU_pairV_scaled hb (mk_ne_mk_add_one _ _) (hf.apply_left hj)
        (hf.apply_right hj)
    · obtain ⟨h1, h2, h3, h4⟩ := pair_idx_ne (j := j) (Fin.val_ne_of_ne hik)
      simp only [pairE, pairF, polar_smul_right, polar_add_left, polar_sub_right,
        polar_basis_basis hb, ite_eq_right hik, h1, h2, h3, h4, ↓reduceIte, add_zero, sub_self,
        smul_zero]
  mem_iff v := by
    have hrepr : ∀ m : Fin n, polar Q v (b m) = 0 ↔ b.repr v m = 0 := fun m => by
      rw [polar_comm, polar_basis_left Q b hb.isOrtho]
      simp [hb.apply_ne_zero m]
    have hpair : ∀ i : Fin (numPairs l j),
        (polar Q v (pairE hf j i) = 0 ∧ polar Q v (pairF hf j i) = 0) ↔
          (b.repr v ⟨j + 2 * i, hf.idx_lt (by have := add_one_le_of_lt_numPairs i.2; omega)⟩ = 0 ∧
            b.repr v ⟨j + 2 * i + 1, hf.idx_lt (add_one_le_of_lt_numPairs i.2)⟩ = 0) := fun i => by
      have hν : ν ≠ 0 := fun h => hb.apply_ne_zero _ ((hf.apply_eq ⟨0, hf.idx_lt (Nat.zero_le _)⟩
        (Nat.zero_le _)).trans (by simp [h]))
      rw [← hrepr, ← hrepr, pairE, pairF, polar_add_right, polar_smul_right, polar_sub_right,
        smul_eq_mul, mul_eq_zero, inv_eq_zero]
      have h4 : (4 * ((-1) ^ (j + 2 * i.val) * ν) : F) ≠ 0 :=
        mul_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero _ (by norm_num)) hν)
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · exact absurd h2 h4
        · exact ⟨by linear_combination (h1 + h2) / 2, by linear_combination (h1 - h2) / 2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [h1, h2, add_zero], Or.inr (by rw [h1, h2, sub_zero])⟩
    rw [pairCompl, Basis.mem_span_image]
    constructor
    · intro hS i
      rw [hpair]
      have hi := add_one_le_of_lt_numPairs i.2
      refine ⟨by_contra fun h => ?_, by_contra fun h => ?_⟩ <;>
      · have := hS (Finsupp.mem_support_iff.2 h)
        simp only [Set.mem_ofPred_eq] at this
        omega
    · intro h m hm
      by_contra hmS
      simp only [Set.mem_ofPred_eq, not_not] at hmS
      have hi : (m.val - j) / 2 < numPairs l j := by simp only [numPairs] at hmS ⊢; omega
      have hi' := add_one_le_of_lt_numPairs hi
      have := (hpair ⟨_, hi⟩).1 (h _)
      rcases Nat.even_or_odd (m.val - j) with ⟨r, hr⟩ | ⟨r, hr⟩
      · have hm' : m = ⟨j + 2 * ((m.val - j) / 2), hf.idx_lt (by omega)⟩ :=
          Fin.ext (by dsimp only; omega)
        exact Finsupp.mem_support_iff.1 hm (hm' ▸ this.1)
      · have hm' : m = ⟨j + 2 * ((m.val - j) / 2) + 1, hf.idx_lt (by omega)⟩ :=
          Fin.ext (by dsimp only; omega)
        exact Finsupp.mem_support_iff.1 hm (hm' ▸ this.2)

/-- The torus of the `i`-th pair of level `j` is the torus of that pair of the hyperbolic frame. -/
theorem levelTorus_eq_pairTorus [Invertible (2 : F)] (hb : IsOrthoBasis Q b)
    (hf : IsFrame Q b ν l) (j : ℕ) (i : Fin (numPairs l j)) (t : Fˣ) :
    levelTorus hb hf (j + 2 * i) t = ((isHypFrame_pair hb hf j).pairTorus i t : V ≃ₗ[F] V) := by
  rw [levelTorus_of_le hb hf (add_one_le_of_lt_numPairs i.2)]
  rfl

/-- **The split torus of level `j` lies in the torus of the hyperbolic frame of level `j`.** -/
theorem multiTorus_mem_hypTorus (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l) (j : ℕ)
    (ts : List Fˣ) :
    multiTorus hb hf j ts ∈ hypTorus (pairCompl b l j) (pairE hf j) (pairF hf j) := by
  let _ : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  suffices H : ∀ (k : ℕ) (ts : List Fˣ),
      multiTorus hb hf (j + 2 * k) ts ∈ hypTorus (pairCompl b l j) (pairE hf j) (pairF hf j) by
    simpa using H 0 ts
  intro k ts
  induction ts generalizing k with
  | nil => exact one_mem _
  | cons t ts ih =>
    rw [multiTorus_cons, show j + 2 * k + 2 = j + 2 * (k + 1) by ring]
    refine mul_mem (ih (k + 1)) ?_
    by_cases hk : j + 2 * k + 1 ≤ l
    · have hk' : k < numPairs l j := by simp only [numPairs]; omega
      rw [show k = ((⟨k, hk'⟩ : Fin (numPairs l j)) : ℕ) from rfl, levelTorus_eq_pairTorus]
      exact (isHypFrame_pair hb hf j).pairTorus_mem_hypTorus _ t
    · rw [levelTorus_of_not_le hb hf hk]; exact one_mem _

end HypFrame

/-! ## Basis vectors indexed by `ℕ`, and eigenvectors of the split tori

`basisNat b m` is `b m` for `m < n` and `0` otherwise. Inductions over the frame (and over the
levels `j`, `j + 2`, …) then need no bound proofs on indices: a statement about `basisNat b m` for
`m ≥ n` holds trivially. The eigenvector statements for the `Fin (numPairs l j)`-indexed vectors
`pairE`, `pairF` of the hyperbolic frame of level `j` follow (`multiTorus_apply_pairE`,
`multiTorus_apply_pairF`). -/

/-- The basis vector `b m`, and `0` for `m ≥ n`. -/
def basisNat (b : Module.Basis (Fin n) F V) (m : ℕ) : V := if h : m < n then b ⟨m, h⟩ else 0

theorem basisNat_of_lt {m : ℕ} (h : m < n) : basisNat b m = b ⟨m, h⟩ := by simp [basisNat, h]

theorem basisNat_of_le {m : ℕ} (h : n ≤ m) : basisNat b m = 0 := by simp [basisNat]; omega

theorem basisNorm_basisNat_le (m : ℕ) : basisNorm b (basisNat b m) ≤ 1 := by
  unfold basisNat
  split_ifs
  · rw [basisNorm_basis]
  · rw [basisNorm_zero]; exact zero_le_one

/-- Elements of `fixer Q b j` fix `basisNat b m` for `m < j`. -/
theorem apply_basisNat_of_mem_fixer {j : ℕ} {g : V ≃ₗ[F] V} (hg : g ∈ fixer Q b j) {m : ℕ}
    (hm : m < j) : g (basisNat b m) = basisNat b m := by
  unfold basisNat
  split_ifs with h
  · exact hg.2 _ hm
  · exact map_zero g

/-! ## Eigenvectors of the split tori -/

section Eigen

variable (hb : IsOrthoBasis Q b) {ν : F} {l : ℕ} (hf : IsFrame Q b ν l)

theorem levelTorus_apply_basisNat_of_ne (j : ℕ) (t : Fˣ) {m : ℕ} (hm : m ≠ j) (hm' : m ≠ j + 1) :
    levelTorus hb hf j t (basisNat b m) = basisNat b m := by
  by_cases hj : j + 1 ≤ l
  · rw [levelTorus_of_le hb hf hj]
    unfold basisNat
    split_ifs with h
    · exact pairTorus_apply_basis_of_ne _ _ _ _ _ (by simp [Fin.ext_iff]; omega)
        (by simp [Fin.ext_iff]; omega)
    · exact map_zero _
  · rw [levelTorus_of_not_le hb hf hj]; rfl

theorem levelTorus_apply_add {j : ℕ} (hj : j + 1 ≤ l) (t : Fˣ) :
    levelTorus hb hf j t (basisNat b j + basisNat b (j + 1)) =
      (t : F) • (basisNat b j + basisNat b (j + 1)) := by
  rw [levelTorus_of_le hb hf hj, basisNat_of_lt (hf.idx_lt (by omega)),
    basisNat_of_lt (hf.idx_lt hj),
    map_add, pairTorus_apply_left, pairTorus_apply_right]
  module

theorem levelTorus_apply_sub {j : ℕ} (hj : j + 1 ≤ l) (t : Fˣ) :
    levelTorus hb hf j t (basisNat b j - basisNat b (j + 1)) =
      (t : F)⁻¹ • (basisNat b j - basisNat b (j + 1)) := by
  rw [levelTorus_of_le hb hf hj, basisNat_of_lt (hf.idx_lt (by omega)),
    basisNat_of_lt (hf.idx_lt hj),
    map_sub, pairTorus_apply_left, pairTorus_apply_right]
  module

theorem multiTorus_apply_basisNat_of_lt (ts : List Fˣ) (j : ℕ) {m : ℕ} (hm : m < j) :
    multiTorus hb hf j ts (basisNat b m) = basisNat b m :=
  apply_basisNat_of_mem_fixer (multiTorus_mem_fixer hb hf ts j) hm

theorem multiTorus_apply_basisNat_of_ge :
    ∀ (ts : List Fˣ) (j : ℕ) {m : ℕ}, j + 2 * ts.length ≤ m →
      multiTorus hb hf j ts (basisNat b m) = basisNat b m
  | [], _, _, _ => rfl
  | t :: ts, j, m, hm => by
    simp only [List.length_cons] at hm
    rw [multiTorus_cons, LinearEquiv.mul_apply,
      levelTorus_apply_basisNat_of_ne hb hf j t (by omega) (by omega),
      multiTorus_apply_basisNat_of_ge ts (j + 2) (by omega)]

/-- `u_k = b (j+2k) + b (j+2k+1)` is an eigenvector of the level-`j` torus, eigenvalue `t_k`. -/
theorem multiTorus_apply_add :
    ∀ (ts : List Fˣ) (j k : ℕ) (hk : k < ts.length), j + 2 * k + 1 ≤ l →
      multiTorus hb hf j ts (basisNat b (j + 2 * k) + basisNat b (j + 2 * k + 1)) =
        (ts[k] : F) • (basisNat b (j + 2 * k) + basisNat b (j + 2 * k + 1))
  | t :: ts, j, 0, _, hl => by
    simp only [mul_zero, add_zero] at hl ⊢
    rw [multiTorus_cons, LinearEquiv.mul_apply, levelTorus_apply_add hb hf hl, map_smul, map_add,
      multiTorus_apply_basisNat_of_lt hb hf ts (j + 2) (by omega),
      multiTorus_apply_basisNat_of_lt hb hf ts (j + 2) (by omega)]
    rfl
  | t :: ts, j, k + 1, hk, hl => by
    have e1 : j + 2 * (k + 1) = j + 2 + 2 * k := by ring
    rw [e1, multiTorus_cons, LinearEquiv.mul_apply, map_add,
      levelTorus_apply_basisNat_of_ne hb hf j t (by omega) (by omega),
      levelTorus_apply_basisNat_of_ne hb hf j t (by omega) (by omega),
      multiTorus_apply_add ts (j + 2) k (by simpa using hk) (by omega)]
    rfl

/-- `v_k = b (j+2k) - b (j+2k+1)` is an eigenvector of the level-`j` torus, eigenvalue `t_k⁻¹`. -/
theorem multiTorus_apply_sub :
    ∀ (ts : List Fˣ) (j k : ℕ) (hk : k < ts.length), j + 2 * k + 1 ≤ l →
      multiTorus hb hf j ts (basisNat b (j + 2 * k) - basisNat b (j + 2 * k + 1)) =
        (ts[k] : F)⁻¹ • (basisNat b (j + 2 * k) - basisNat b (j + 2 * k + 1))
  | t :: ts, j, 0, _, hl => by
    simp only [mul_zero, add_zero] at hl ⊢
    rw [multiTorus_cons, LinearEquiv.mul_apply, levelTorus_apply_sub hb hf hl, map_smul, map_sub,
      multiTorus_apply_basisNat_of_lt hb hf ts (j + 2) (by omega),
      multiTorus_apply_basisNat_of_lt hb hf ts (j + 2) (by omega)]
    rfl
  | t :: ts, j, k + 1, hk, hl => by
    have e1 : j + 2 * (k + 1) = j + 2 + 2 * k := by ring
    rw [e1, multiTorus_cons, LinearEquiv.mul_apply, map_sub,
      levelTorus_apply_basisNat_of_ne hb hf j t (by omega) (by omega),
      levelTorus_apply_basisNat_of_ne hb hf j t (by omega) (by omega),
      multiTorus_apply_sub ts (j + 2) k (by simpa using hk) (by omega)]
    rfl

theorem multiTorus_mem_orthogonalGroup (ts : List Fˣ) (j : ℕ) :
    multiTorus hb hf j ts ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  mem_orthogonalGroup_of_mem_fixer (multiTorus_mem_fixer hb hf ts j)

/-- `pairE hf j i` is an eigenvector of the level-`j` torus, with eigenvalue `t_i`. -/
theorem multiTorus_apply_pairE {j : ℕ} {ts : List Fˣ} (hlen : ts.length = numPairs l j)
    (i : Fin (numPairs l j)) :
    multiTorus hb hf j ts (pairE hf j i) = (ts[i.val]'(by omega) : F) • pairE hf j i := by
  have e : pairE hf j i = basisNat b (j + 2 * i) + basisNat b (j + 2 * i + 1) := by
    rw [pairE, basisNat_of_lt, basisNat_of_lt]
  rw [e]
  exact multiTorus_apply_add hb hf ts j i (by omega) (add_one_le_of_lt_numPairs i.2)

/-- `pairF hf j i` is an eigenvector of the level-`j` torus, with eigenvalue `t_i⁻¹`. -/
theorem multiTorus_apply_pairF {j : ℕ} {ts : List Fˣ} (hlen : ts.length = numPairs l j)
    (i : Fin (numPairs l j)) :
    multiTorus hb hf j ts (pairF hf j i) = (ts[i.val]'(by omega) : F)⁻¹ • pairF hf j i := by
  have e : pairF hf j i = (4 * ((-1) ^ (j + 2 * i.val) * ν))⁻¹ •
      (basisNat b (j + 2 * i) - basisNat b (j + 2 * i + 1)) := by
    rw [pairF, basisNat_of_lt, basisNat_of_lt]
  rw [e, map_smul, multiTorus_apply_sub hb hf ts j i (by omega) (add_one_le_of_lt_numPairs i.2),
    smul_comm]

end Eigen

section UltraFrame

variable [IsUltrametricDist F] {ν : F} {l : ℕ} (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l)

theorem basisNorm_basisNat_add_le (p q : ℕ) : basisNorm b (basisNat b p + basisNat b q) ≤ 1 :=
  (basisNorm_add_le _ _).trans (max_le (basisNorm_basisNat_le p) (basisNorm_basisNat_le q))

theorem basisNorm_basisNat_sub_le (p q : ℕ) : basisNorm b (basisNat b p - basisNat b q) ≤ 1 :=
  (basisNorm_sub_le _ _).trans (max_le (basisNorm_basisNat_le p) (basisNorm_basisNat_le q))

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

end UltraFrame

/-! ## Chambers -/

section Chamber

variable {l : ℕ}

theorem InChamber.rel_of_lt {j : ℕ} {ts : List Fˣ} (h : InChamber n l j ts) {k m : ℕ}
    (hkm : k < m) (hm : m < ts.length) :
    ‖(ts[k] : F)‖ ≤ ‖(ts[m] : F)‖ ∧ ‖(ts[k] : F) * ts[m]‖ ≤ 1 :=
  List.pairwise_iff_getElem.1 h.2.1 k m (by omega) hm hkm

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

end Chamber

/-! ## Existence of maximal frames -/

omit [CharZero F] in
/-- **Existence of a maximal frame.** In a nondegenerate quadratic space, every anisotropic `v₀`
is the first vector of an orthogonal basis of anisotropic vectors whose first `l + 1` vectors form
a maximal frame for `ν = Q v₀`. Greedily: take orthogonal `w₀ = v₀, w₁, …, w_l` with
`Q wᵢ = (-1)ⁱ ν` and `l` as large as possible (it is bounded by the dimension, since such a family
is linearly independent); then `(-1)^{l+1} ν` is not represented by `{w₀, …, w_l}^⊥`, and an
orthogonal basis of that complement completes the family (`exists_isOrthoBasis_append`). -/
theorem exists_isFrame [NeZero (2 : F)] (hQ : Q.Nondegenerate) {v₀ : V} (hv₀ : Q v₀ ≠ 0) :
    ∃ (n l : ℕ) (b : Module.Basis (Fin n) F V), IsOrthoBasis Q b ∧
      ∃ hf : IsFrame Q b (Q v₀) l, b ⟨0, (Nat.zero_le l).trans_lt hf.lt⟩ = v₀ := by
  classical
  let _ : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  -- `P k`: an orthogonal family `w₀ = v₀, …, w_k` with `Q wᵢ = (-1)ⁱ Q v₀`
  let P : ℕ → Prop := fun k => ∃ w : Fin (k + 1) → V, w 0 = v₀ ∧
    (∀ i, Q (w i) = (-1) ^ i.val * Q v₀) ∧ ∀ i j, i ≠ j → Q.IsOrtho (w i) (w j)
  have hP0 : P 0 := ⟨fun _ => v₀, rfl, fun i => by simp [Fin.fin_one_eq_zero i],
    fun i j h => (h (Fin.ext (by have := i.2; have := j.2; omega))).elim⟩
  have hbound : ∀ k, P k → k + 1 ≤ finrank F V := by
    rintro k ⟨w, -, hwQ, hwo⟩
    have hli : LinearIndependent F w := LinearMap.BilinForm.linearIndependent_of_iIsOrtho
      (fun i j hij => isOrtho_polarBilin.mpr (hwo i j hij)) fun i => by
        rw [polarBilin_apply_apply, polar_self, two_smul, ← two_mul, hwQ]
        exact mul_ne_zero two_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hv₀)
    simpa using hli.fintype_card_le_finrank
  set l := Nat.findGreatest P (finrank F V)
  obtain ⟨w, hw0, hwQ, hwo⟩ : P l := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hmax : ¬ P (l + 1) := fun h => by
    have h1 := hbound (l + 1) h
    have h2 := Nat.le_findGreatest (P := P) (by omega : l + 1 ≤ finrank F V) h
    omega
  obtain ⟨m, c, b, hb, hbw⟩ := exists_isOrthoBasis_append hQ hwo fun i => by
    rw [hwQ]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hv₀
  have hbw' : ∀ i : Fin (l + 1 + m), (hi : i.val ≤ l) → b i = w ⟨i.val, by omega⟩ := by
    intro i hi
    have hi' : i = Fin.castAdd m ⟨i.val, by omega⟩ := Fin.ext rfl
    rw [hbw]; conv_lhs => rw [hi']
    rw [Fin.append_left]
  have hf : IsFrame Q b (Q v₀) l :=
    { lt := by omega
      apply_eq := fun i hi => by rw [hbw' i hi, hwQ]
      maximal := fun x hx hQx => hmax ⟨Fin.snoc w x, ?_, fun i => ?_, fun i j hij => ?_⟩ }
  · exact ⟨_, _, b, hb, hf, by rw [hbw' _ (Nat.zero_le _)]; exact hw0⟩
  · rw [← Fin.castSucc_zero, Fin.snoc_castSucc, hw0]
  · induction i using Fin.lastCases with
    | last => rw [Fin.snoc_last, hQx, Fin.val_last]
    | cast i => rw [Fin.snoc_castSucc, hwQ, Fin.val_castSucc]
  · -- `x` is orthogonal to the `wᵢ`
    have hxo : ∀ i, Q.IsOrtho (w i) x := fun i => by
      rw [← isOrtho_polarBilin, polarBilin_apply_apply, ← hbw' ⟨i.val, by omega⟩ (by simp; omega),
        polar_basis_left Q b hb.isOrtho, hx _ (by simp; omega), mul_zero]
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
    · exact absurd rfl hij
    · exact isOrtho_comm.mp (hxo _)
    · exact hxo _
    · exact hwo _ _ fun h => hij (by rw [h])

end WeakCartan

end GSpinGGP
