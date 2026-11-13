/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.WeakCartanRotation

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
* `signBasis e b`: the basis `((-1)^{e i} b i)`; it is again a frame with the same fixers, and
  the torus of a pair is unchanged or inverted according as its two signs agree or not
  (`levelTorus_signBasis`, `multiTorus_signBasis_of_even`, `multiTorus_signBasis_of_odd`). For
  `e = id` both flags are reversed.
* `inChamber_cons`: the chamber adjustment for the induction.
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

theorem idx_ne {j : ℕ} (h₀ : j < n) (h₁ : j + 1 < n) :
    (⟨j, h₀⟩ : Fin n) ≠ ⟨j + 1, h₁⟩ := by
  simp [Fin.ext_iff]

/-- The split torus `a(t)` of the hyperbolic plane `⟨b j, b (j+1)⟩` (for `j + 1 ≤ l`; the
identity otherwise). -/
def levelTorus (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l) (j : ℕ) (t : Fˣ) :
    V ≃ₗ[F] V :=
  if hj : j + 1 ≤ l then
    pairTorus hb (idx_ne (hf.idx_lt (by omega)) (hf.idx_lt hj)) (hf.apply_left hj)
      (hf.apply_right hj) t
  else 1

variable (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l)

theorem levelTorus_of_le {j : ℕ} (hj : j + 1 ≤ l) (t : Fˣ) :
    levelTorus hb hf j t = pairTorus hb (idx_ne (hf.idx_lt (by omega)) (hf.idx_lt hj))
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

/-- An isometry fixing `b i₀` and `b i₁` commutes with the split torus of the pair. -/
theorem pairTorus_commute (hb : IsOrthoBasis Q b) {i₀ i₁ : Fin n} (hne : i₀ ≠ i₁) {ν : F}
    (h₀ : Q (b i₀) = ν) (h₁ : Q (b i₁) = -ν) {x : V ≃ₗ[F] V}
    (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx₀ : x (b i₀) = b i₀)
    (hx₁ : x (b i₁) = b i₁) (t : Fˣ) :
    x * pairTorus hb hne h₀ h₁ t = pairTorus hb hne h₀ h₁ t * x := by
  have hu : x (b i₀ + b i₁) = b i₀ + b i₁ := by rw [map_add, hx₀, hx₁]
  have hv : x ((4 * ν)⁻¹ • (b i₀ - b i₁)) = (4 * ν)⁻¹ • (b i₀ - b i₁) := by
    rw [map_smul, map_sub, hx₀, hx₁]
  have hp : ∀ y w, x w = w → polar Q (x y) w = polar Q y w := fun y w hw => by
    conv_lhs => rw [← hw]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hx y w
  ext y
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, pairTorus_apply, pairTorus_apply,
    hp y _ hu, hp y _ hv, map_add, map_add, map_smul, map_smul, hu, hv]

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

variable (e : ℕ → ℕ)

/-- The basis `((-1)^{e i} b i)`. -/
def signBasis (b : Module.Basis (Fin n) F V) : Module.Basis (Fin n) F V :=
  b.unitsSMul fun i => (-1) ^ e i.val

theorem signBasis_apply (i : Fin n) : signBasis e b i = ((-1 : F) ^ e i.val) • b i := by
  rw [signBasis, Module.Basis.unitsSMul_apply, Units.smul_def]; simp

theorem sign_sq (i : ℕ) : ((-1 : F) ^ i) * (-1) ^ i = 1 := by
  rw [← mul_pow]; simp

theorem apply_signBasis (i : Fin n) : Q (signBasis e b i) = Q (b i) := by
  rw [signBasis_apply, QuadraticMap.map_smul, smul_eq_mul, sign_sq, one_mul]

theorem signBasis_repr (x : V) (i : Fin n) :
    (signBasis e b).repr x i = (-1 : F) ^ e i.val * b.repr x i := by
  rw [signBasis, Module.Basis.repr_unitsSMul, Units.smul_def]
  simp [← inv_pow]

theorem _root_.GSpinGGP.IsOrthoBasis.signBasis (hb : IsOrthoBasis Q b) :
    IsOrthoBasis Q (signBasis e b) where
  isOrtho i j hij := by
    rw [signBasis_apply, signBasis_apply]
    rw [← QuadraticMap.isOrtho_polarBilin, QuadraticMap.polarBilin_apply_apply, polar_smul_left,
      polar_smul_right, hb.polar_eq_zero i j hij]
    simp
  apply_ne_zero i := by rw [apply_signBasis]; exact hb.apply_ne_zero i

theorem IsFrame.signBasis {ν : F} {l : ℕ} (hf : IsFrame Q b ν l) :
    IsFrame Q (signBasis e b) ν l where
  lt := hf.lt
  apply_eq i hi := by rw [apply_signBasis]; exact hf.apply_eq i hi
  maximal x hx := hf.maximal x fun i hi => by
    have := hx i hi
    rw [signBasis_repr] at this
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ (by norm_num))

theorem fixer_signBasis (j : ℕ) : fixer Q (signBasis e b) j = fixer Q b j := by
  ext g
  simp only [mem_fixer_iff, signBasis_apply, map_smul]
  refine and_congr_right fun _ => forall_congr' fun i => imp_congr_right fun _ => ?_
  exact smul_right_inj (pow_ne_zero _ (by norm_num))

/-- Changing the signs of the basis: the torus of the pair `(b j, b (j+1))` is unchanged if the
two signs agree and inverted if they differ. -/
theorem levelTorus_signBasis {ν : F} {l : ℕ} (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l)
    (j : ℕ) (t : Fˣ) :
    levelTorus (hb.signBasis e) (hf.signBasis e) j t =
      levelTorus hb hf j (if Odd (e j + e (j + 1)) then t⁻¹ else t) := by
  set t' : Fˣ := if Odd (e j + e (j + 1)) then t⁻¹ else t
  set σ : F := (-1) ^ e j with hσd
  set σ' : F := (-1) ^ e (j + 1) with hσd'
  have hσ : σ * σ = 1 := sign_sq _
  have hσ' : σ' * σ' = 1 := sign_sq _
  have hσ2 : σ ^ 2 = 1 := by rw [_root_.sq]; exact hσ
  have hσ2' : σ' ^ 2 = 1 := by rw [_root_.sq]; exact hσ'
  have hc : ((t' : F) + (t' : F)⁻¹) / 2 = ((t : F) + (t : F)⁻¹) / 2 := by
    simp only [t']; split_ifs <;> simp [add_comm]
  have hs : ((t' : F) - (t' : F)⁻¹) / 2 = σ * σ' * (((t : F) - (t : F)⁻¹) / 2) := by
    have hδ : σ * σ' = (-1) ^ (e j + e (j + 1)) := by rw [pow_add]
    simp only [t']; split_ifs with h
    · rw [hδ, h.neg_one_pow]; simp; ring
    · rw [hδ, (Nat.not_odd_iff_even.1 h).neg_one_pow]; ring
  by_cases hj : j + 1 ≤ l
  · rw [levelTorus_of_le _ _ hj, levelTorus_of_le _ _ hj]
    refine b.ext' fun m => ?_
    by_cases hm₀ : m = ⟨j, hf.idx_lt (by omega)⟩
    · subst hm₀
      have e0 := pairTorus_apply_left (hb.signBasis e)
        (idx_ne (hf.idx_lt (by omega)) (hf.idx_lt hj)) ((hf.signBasis e).apply_left hj)
        ((hf.signBasis e).apply_right hj) t
      simp only [signBasis_apply, map_smul] at e0
      rw [← hσd, ← hσd'] at e0
      rw [pairTorus_apply_left, hc, hs]
      calc _ = σ • σ • _ := by rw [smul_smul, hσ, one_smul]
        _ = _ := by
          rw [e0, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
          congr 1 <;> congr 1 <;> (ring_nf; try simp only [hσ2]; try ring)
    by_cases hm₁ : m = ⟨j + 1, hf.idx_lt hj⟩
    · subst hm₁
      have e0 := pairTorus_apply_right (hb.signBasis e)
        (idx_ne (hf.idx_lt (by omega)) (hf.idx_lt hj)) ((hf.signBasis e).apply_left hj)
        ((hf.signBasis e).apply_right hj) t
      simp only [signBasis_apply, map_smul] at e0
      rw [← hσd, ← hσd'] at e0
      rw [pairTorus_apply_right, hc, hs]
      calc _ = σ' • σ' • _ := by rw [smul_smul, hσ', one_smul]
        _ = _ := by
          rw [e0, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
          congr 1 <;> congr 1 <;> (ring_nf; try simp only [hσ2']; try ring)
    · have e0 := pairTorus_apply_basis_of_ne (hb.signBasis e)
        (idx_ne (hf.idx_lt (by omega)) (hf.idx_lt hj)) ((hf.signBasis e).apply_left hj)
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
    ts.Pairwise (fun s t => ‖(s : F)‖ ≤ ‖(t : F)‖ ∧ ‖(s : F) * t‖ ≤ 1) ∧
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

end WeakCartan

end GSpinGGP
