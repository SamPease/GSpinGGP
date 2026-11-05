/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.QuadClassify

/-!
# Witt indices of the two `p`-adic classes, and the Kottwitz sign

Own work, from the cited classical results of `Literature/GSpin.lean` only (Witt cancellation,
Witt decomposition, the classification of quadratic forms over `p`-adic fields).

* `hypForm_succ_iso`: `H^{n+1} ≅ H^n ⊥ H`.
* `exists_isotropic_of_discRel_hyp`: if the forms of dimension `N` and the discriminant of `R`
  fall into two classes, every form of the discriminant and dimension of `H ⊥ R` is isotropic
  (counting: `R ↦ H ⊥ R` is injective by Witt cancellation, and there are at most two classes).
* `not_anisotropic_of_five_le`: a `p`-adic form of dimension `≥ 5` is isotropic (Lam, Ch. VI,
  Thm. 2.12, here derived from the class count).
* `wittIndex_odd_pair`, `even_wittIndex_add_of_even`: for two forms of the same dimension and
  discriminant, the Witt indices differ by `1` (odd dimension, the two classes) or by an even
  number (even dimension).
* `kottwitzSign_eq_neg_one`: for `G` quasi-split and `W_α ≇ W`, `e(G_α) = -1`; and
  `kottwitzSign_eq_one_of_nonempty`: `e(G_α) = 1` when `W_α ≅ W`.
-/

noncomputable section
open scoped Classical
open Module
set_option linter.unusedSectionVars false

namespace GSpinGGP
namespace WittParity

open QuadClassify

variable {K : Type*} [Field K] [Invertible (2 : K)]

section Hyp

/-- `H^n(v) = Σ_i v_i v_{rev i}`. -/
theorem hypForm_apply (n : ℕ) (v : Fin (2 * n) → K) :
    hypForm K n v = ∑ i, v i * v (Fin.rev i) := by
  unfold hypForm Matrix.toQuadraticForm'
  rw [LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (Fin.rev i)]
  · simp only [hypMatrix, smul_eq_mul]
    rw [if_pos (by rw [Fin.val_rev]; have := i.2; omega)]
    ring
  · intro j _ hj
    simp only [hypMatrix, smul_eq_mul]
    rw [if_neg]
    · ring
    · intro h
      apply hj
      ext
      rw [Fin.val_rev]
      omega
  · simp

/-- The embedding `Fin (2n) ⊕ Fin 2 → Fin (2n+2)`: `j ↦ j+1`, the extra pair to `0, 2n+1`. -/
def hypSplitFun (n : ℕ) : Fin (2 * n) ⊕ Fin 2 → Fin (2 * (n + 1))
  | Sum.inl j => ⟨j + 1, by have := j.2; omega⟩
  | Sum.inr i => ⟨if (i : ℕ) = 0 then 0 else 2 * n + 1, by split_ifs <;> omega⟩

theorem hypSplitFun_injective (n : ℕ) : Function.Injective (hypSplitFun n) := by
  rintro (j | i) (j' | i') h <;> simp only [hypSplitFun, Fin.mk.injEq] at h
  · exact congrArg Sum.inl (Fin.ext (by omega))
  · have := j.2; split_ifs at h <;> omega
  · have := j'.2; split_ifs at h <;> omega
  · congr 1; ext; have := i.2; have := i'.2; split_ifs at h <;> omega

/-- The bijection `Fin (2n) ⊕ Fin 2 ≃ Fin (2n+2)`. -/
def hypSplit (n : ℕ) : Fin (2 * n) ⊕ Fin 2 ≃ Fin (2 * (n + 1)) :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).2
    ⟨hypSplitFun_injective n, by simp; ring⟩)

theorem hypSplit_rev (n : ℕ) (s : Fin (2 * n) ⊕ Fin 2) :
    Fin.rev (hypSplit n s) = hypSplit n (Sum.map Fin.rev Fin.rev s) := by
  rcases s with j | i <;>
    simp only [hypSplit, Equiv.ofBijective_apply, hypSplitFun, Sum.map_inl, Sum.map_inr] <;> ext <;>
    simp only [Fin.val_rev]
  · have := j.2; omega
  · have := i.2; split_ifs <;> omega

/-- **`H^{n+1} ≅ H^n ⊥ H`** (reordering the coordinates). -/
def hypForm_succ_iso (n : ℕ) :
    (hypForm K (n + 1)).IsometryEquiv ((hypForm K n).prod (hypForm K 1)) where
  toLinearEquiv := (LinearEquiv.funCongrLeft K K (hypSplit n)).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ K K)
  map_app' v := by
    simp only [LinearEquiv.trans_apply, QuadraticMap.prod_apply]
    rw [hypForm_apply, hypForm_apply, hypForm_apply]
    rw [← (hypSplit n).sum_comp, Fintype.sum_sum_type]
    simp only [hypSplit_rev, Sum.map_inl, Sum.map_inr]
    rfl

end Hyp

section Generic

variable {V₁ V₂ V₃ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

/-- `DiscRel` from Gram determinants in bases with index types of the same size. -/
theorem discRel_of_gdet {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂]
    [DecidableEq ι₂] {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} (b₁ : Basis ι₁ K V₁)
    (b₂ : Basis ι₂ K V₂) (hcard : Fintype.card ι₂ = Fintype.card ι₁) {c : K} (hc : c ≠ 0)
    (h : gdet Q₂ b₂ = c ^ 2 * gdet Q₁ b₁) : DiscRel Q₁ Q₂ :=
  ⟨_, b₁.reindex (Fintype.equivFin ι₁), b₂.reindex ((Fintype.equivFin ι₂).trans (finCongr hcard)),
    c, hc, by rw [gdet_reindex, gdet_reindex, h]⟩

theorem gdet_basisFun {m : ℕ} (Q : QuadraticForm K (Fin m → K)) :
    gdet Q (Pi.basisFun K (Fin m)) = Q.discr' := by
  rw [gdet, QuadraticForm.toMatrix_eq_toMatrix']
  rfl

/-- The Gram determinant of `Σ w_i x_i²` is `Π w_i`. -/
theorem gdet_wss {m : ℕ} (w : Fin m → K) :
    gdet (QuadraticMap.weightedSumSquares K w) (Pi.basisFun K (Fin m)) = ∏ i, w i := by
  rw [gdet_basisFun, QuadraticForm.discr']
  have : QuadraticForm.toMatrix' (QuadraticMap.weightedSumSquares K w : QuadraticForm K _) =
      Matrix.diagonal w := by
    ext i j
    simp only [QuadraticForm.toMatrix', LinearMap.toMatrix₂'_apply]
    rcases eq_or_ne i j with rfl | hij
    · rw [QuadraticMap.associated_eq_self_apply, QuadraticMap.weightedSumSquares_apply,
        Matrix.diagonal_apply_eq]
      simp [Pi.single_apply]
    · rw [Matrix.diagonal_apply_ne _ hij, QuadraticMap.associated_apply]
      have h : QuadraticMap.weightedSumSquares K w (Pi.single i 1 + Pi.single j 1) -
          QuadraticMap.weightedSumSquares K w (Pi.single i 1) -
          QuadraticMap.weightedSumSquares K w (Pi.single j 1) = 0 := by
        simp only [QuadraticMap.weightedSumSquares_apply, Pi.add_apply, Pi.single_apply,
          smul_eq_mul]
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_eq_zero fun x _ => ?_
        by_cases hx : x = i <;> by_cases hy : x = j <;> simp_all
      rw [h, smul_zero]
  rw [this, Matrix.det_diagonal]

theorem invOf_two_end_apply (x : K) : (⅟(2 : Module.End K K)) x = ⅟2 * x := by
  have h : (⅟(2 : Module.End K K)) = (⅟(2 : K)) • LinearMap.id := by
    apply invOf_eq_right_inv
    ext
    simp [Module.End.mul_apply]
  rw [h]
  rfl

/-- The Gram determinant of the hyperbolic plane is `-1`. -/
theorem gdet_hyp_one : gdet (hypForm K 1) (Pi.basisFun K (Fin (2 * 1))) = -1 := by
  rw [gdet_basisFun, QuadraticForm.discr', Matrix.det_fin_two]
  have e : ∀ i j : Fin (2 * 1), QuadraticForm.toMatrix' (hypForm K 1) i j =
      if i = j then 0 else 1 := by
    intro i j
    simp only [QuadraticForm.toMatrix', LinearMap.toMatrix₂'_apply, hypForm,
      Matrix.toQuadraticForm', QuadraticMap.associated_toQuadraticMap]
    rw [Module.End.smul_def, invOf_two_end_apply]
    have h2 : (2 : K)⁻¹ * 2 = 1 := by rw [← invOf_eq_inv]; exact invOf_mul_self 2
    fin_cases i <;> fin_cases j <;>
      simp [hypMatrix, Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec, Fin.sum_univ_two,
        Pi.single_apply] <;> linear_combination h2
  rw [e, e, e, e]
  simp

/-- An isometry pulls back isotropic vectors. -/
theorem not_anisotropic_of_isometryEquiv {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (e : Q₁.IsometryEquiv Q₂) (h : ¬ Q₂.Anisotropic) : ¬ Q₁.Anisotropic := by
  intro ha
  apply h
  intro v hv
  have h0 := ha (e.symm v) (by rw [e.symm.map_app]; exact hv)
  have := congrArg e h0
  simpa using this

/-- `H ⊥ P` is isotropic. -/
theorem not_anisotropic_hyp_prod (P : QuadraticForm K V₁) :
    ¬ ((hypForm K 1).prod P).Anisotropic := by
  intro ha
  have h := ha (Pi.single 0 1, 0) (by
    rw [QuadraticMap.prod_apply, hypForm_apply, map_zero, add_zero]
    simp [Fin.sum_univ_succ, Pi.single_apply, Fin.rev])
  have := congrArg (fun p => p.1 0) h
  simp at this

/-- Cancelling a common orthogonal summand in `DiscRel`. -/
theorem discRel_cancel {V₄ : Type*} [AddCommGroup V₄] [Module K V₄] [FiniteDimensional K V₁]
    [FiniteDimensional K V₂] [FiniteDimensional K V₄] {X : QuadraticForm K V₄}
    {A : QuadraticForm K V₁} {B : QuadraticForm K V₂} (hnd : IsNondeg (X.prod A))
    (h : DiscRel (X.prod A) (X.prod B)) : DiscRel A B := by
  have hdim := finrank_eq_of_discRel h
  rw [Module.finrank_prod, Module.finrank_prod] at hdim
  set bX := Module.finBasis K V₄
  set bA := Module.finBasis K V₁
  set bB := Module.finBasisOfFinrankEq K V₂ (show finrank K V₂ = finrank K V₁ by omega)
  obtain ⟨c, hc, hcd⟩ := h.bases (bX.prod bA) (bX.prod bB)
  rw [gdet_prod, gdet_prod] at hcd
  rw [isNondeg_iff_gdet_ne_zero _ (bX.prod bA), gdet_prod] at hnd
  exact ⟨_, bA, bB, c, hc, mul_left_cancel₀ (left_ne_zero_of_mul hnd) (by rw [hcd]; ring)⟩

/-- A form `P` on `K^{j+1}` with `DiscRel A (H ⊥ P)`, for `dim A = j + 3`. -/
theorem exists_hyp_prod_discRel [FiniteDimensional K V₁] {A : QuadraticForm K V₁}
    (hA : IsNondeg A) {j : ℕ} (hj : finrank K V₁ = j + 3) :
    ∃ P : QuadraticForm K (Fin (j + 1) → K), IsNondeg P ∧ DiscRel A ((hypForm K 1).prod P) := by
  set b := Module.finBasisOfFinrankEq K V₁ hj
  set δ := gdet A b
  have hδ : δ ≠ 0 := (isNondeg_iff_gdet_ne_zero A b).1 hA
  set P := QuadraticMap.weightedSumSquares K (Fin.cons (-δ) 1 : Fin (j + 1) → K)
  have hP : gdet P (Pi.basisFun K (Fin (j + 1))) = -δ := by
    rw [gdet_wss, Fin.prod_cons]
    simp
  refine ⟨P, (isNondeg_iff_gdet_ne_zero P (Pi.basisFun K _)).2 (by rw [hP]; exact neg_ne_zero.2 hδ),
    discRel_of_gdet b ((Pi.basisFun K (Fin (2 * 1))).prod (Pi.basisFun K (Fin (j + 1))))
      (by simp; omega) one_ne_zero ?_⟩
  rw [gdet_prod, gdet_hyp_one, hP]
  ring

/-- `(A ⊥ B) ⊥ C ≅ A ⊥ (B ⊥ C)`. -/
def assocIso (Q₁ : QuadraticForm K V₁) (Q₂ : QuadraticForm K V₂) (Q₃ : QuadraticForm K V₃) :
    ((Q₁.prod Q₂).prod Q₃).IsometryEquiv (Q₁.prod (Q₂.prod Q₃)) where
  toFun p := (p.1.1, (p.1.2, p.2))
  invFun p := ((p.1, p.2.1), p.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  map_app' p := by
    simp only [QuadraticMap.prod_apply]
    abel

/-- `Q ⊥ 0 ≅ Q` for the zero space `K⁰`. -/
def prodZeroIso (Q : QuadraticForm K V₁) (A : QuadraticForm K (Fin 0 → K)) :
    (Q.prod A).IsometryEquiv Q where
  toLinearEquiv := LinearEquiv.prodUnique
  map_app' p := by
    rw [QuadraticMap.prod_apply, Subsingleton.elim p.2 0, map_zero, add_zero]
    rfl

end Generic

section Padic

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
variable {V₁ V₂ V₃ : Type*} [AddCommGroup V₁] [Module F V₁] [FiniteDimensional F V₁]
  [AddCommGroup V₂] [Module F V₂] [FiniteDimensional F V₂]
  [AddCommGroup V₃] [Module F V₃] [FiniteDimensional F V₃]

/-- A form in coordinates. -/
theorem exists_fin_iso (Q : QuadraticForm F V₁) {n : ℕ} (hn : finrank F V₁ = n) :
    ∃ P : QuadraticForm F (Fin n → F), Nonempty (P.IsometryEquiv Q) := by
  let e : V₁ ≃ₗ[F] (Fin n → F) := LinearEquiv.ofFinrankEq _ _ (by rw [hn, Module.finrank_fin_fun])
  exact ⟨Q.comp e.symm.toLinearMap, ⟨{ toLinearEquiv := e.symm, map_app' := fun _ => rfl }⟩⟩

theorem pigeon_fin {m : ℕ} {P₁ P₂ P₃ : QuadraticForm F (Fin m → F)} (h₁ : IsNondeg P₁)
    (h₂ : DiscRel P₁ P₂) (h₃ : DiscRel P₁ P₃) :
    Nonempty (P₁.IsometryEquiv P₂) ∨ Nonempty (P₁.IsometryEquiv P₃) ∨
      Nonempty (P₂.IsometryEquiv P₃) := by
  obtain ⟨n, R, -, -, -, huniq, -, -, -, hn2⟩ := padic_quadratic_classes P₁ h₁
  obtain ⟨i₁, ⟨e₁⟩, -⟩ := huniq P₁ h₁ ⟨1, one_ne_zero, by ring⟩
  obtain ⟨i₂, ⟨e₂⟩, -⟩ := huniq P₂ (h₂.isNondeg h₁) ((sameDisc_iff_discRel _ _).2 h₂)
  obtain ⟨i₃, ⟨e₃⟩, -⟩ := huniq P₃ (h₃.isNondeg h₁) ((sameDisc_iff_discRel _ _).2 h₃)
  have : i₁ = i₂ ∨ i₁ = i₃ ∨ i₂ = i₃ := by
    by_contra hc
    push_neg at hc
    have a := Fin.val_ne_of_ne hc.1
    have b := Fin.val_ne_of_ne hc.2.1
    have c := Fin.val_ne_of_ne hc.2.2
    have := i₁.2
    have := i₂.2
    have := i₃.2
    omega
  rcases this with h | h | h <;> subst h
  · exact Or.inl ⟨e₁.trans e₂.symm⟩
  · exact Or.inr (Or.inl ⟨e₁.trans e₃.symm⟩)
  · exact Or.inr (Or.inr ⟨e₂.trans e₃.symm⟩)

/-- **At most two classes**: among three forms of the same dimension and discriminant, two are
isometric (`padic_quadratic_classes`). -/
theorem pigeon {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂} {Q₃ : QuadraticForm F V₃}
    (h₁ : IsNondeg Q₁) (h₂ : DiscRel Q₁ Q₂) (h₃ : DiscRel Q₁ Q₃) :
    Nonempty (Q₁.IsometryEquiv Q₂) ∨ Nonempty (Q₁.IsometryEquiv Q₃) ∨
      Nonempty (Q₂.IsometryEquiv Q₃) := by
  obtain ⟨P₁, ⟨J₁⟩⟩ := exists_fin_iso Q₁ rfl
  obtain ⟨P₂, ⟨J₂⟩⟩ := exists_fin_iso Q₂ (finrank_eq_of_discRel h₂).symm
  obtain ⟨P₃, ⟨J₃⟩⟩ := exists_fin_iso Q₃ (finrank_eq_of_discRel h₃).symm
  have k₁ : IsNondeg P₁ := (DiscRel.of_isometryEquiv J₁.symm).isNondeg h₁
  have k₂ : DiscRel P₁ P₂ :=
    ((DiscRel.of_isometryEquiv J₁).trans h₂).trans (DiscRel.of_isometryEquiv J₂.symm)
  have k₃ : DiscRel P₁ P₃ :=
    ((DiscRel.of_isometryEquiv J₁).trans h₃).trans (DiscRel.of_isometryEquiv J₃.symm)
  rcases pigeon_fin k₁ k₂ k₃ with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inl ⟨(J₁.symm.trans e).trans J₂⟩
  · exact Or.inr (Or.inl ⟨(J₁.symm.trans e).trans J₃⟩)
  · exact Or.inr (Or.inr ⟨(J₂.symm.trans e).trans J₃⟩)

/-- Forms of dimension `≤ 1` are determined by their discriminant. -/
theorem iso_of_finrank_le_one {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}
    (h₁ : IsNondeg Q₁) (h₂ : DiscRel Q₁ Q₂) (hd : finrank F V₁ ≤ 1) :
    Nonempty (Q₁.IsometryEquiv Q₂) := by
  obtain ⟨P₁, ⟨J₁⟩⟩ := exists_fin_iso Q₁ rfl
  obtain ⟨P₂, ⟨J₂⟩⟩ := exists_fin_iso Q₂ (finrank_eq_of_discRel h₂).symm
  have k₁ : IsNondeg P₁ := (DiscRel.of_isometryEquiv J₁.symm).isNondeg h₁
  have k₂ : DiscRel P₁ P₂ :=
    ((DiscRel.of_isometryEquiv J₁).trans h₂).trans (DiscRel.of_isometryEquiv J₂.symm)
  obtain ⟨n, R, -, -, -, huniq, -, h1, -, -⟩ := padic_quadratic_classes P₁ k₁
  have hn := h1 hd
  obtain ⟨i₁, ⟨e₁⟩, -⟩ := huniq P₁ k₁ ⟨1, one_ne_zero, by ring⟩
  obtain ⟨i₂, ⟨e₂⟩, -⟩ := huniq P₂ (k₂.isNondeg k₁) ((sameDisc_iff_discRel _ _).2 k₂)
  have : i₁ = i₂ := Fin.ext (by have := i₁.2; have := i₂.2; omega)
  subst this
  exact ⟨((J₁.symm.trans e₁).trans e₂.symm).trans J₂⟩

/-- In dimension `≥ 3`, or for a non-hyperbolic plane, there is a second class. -/
theorem exists_other_class {k : ℕ} {P : QuadraticForm F (Fin k → F)} (hP : IsNondeg P)
    (hk : 3 ≤ k ∨ (k = 2 ∧ ¬ IsSquare (-P.discr'))) :
    ∃ P' : QuadraticForm F (Fin k → F), IsNondeg P' ∧ DiscRel P P' ∧
      ¬ Nonempty (P.IsometryEquiv P') := by
  obtain ⟨n, R, i₀, hR0, hR, huniq, h3, -, h2, hn2⟩ := padic_quadratic_classes P hP
  have hn : n = 2 := by
    rcases hk with hk | ⟨hk, hsq⟩
    · exact h3 hk
    · have := i₀.2
      by_contra hne
      exact hsq ((h2 hk).1 (by omega))
  subst hn
  set j : Fin 2 := if i₀ = 0 then 1 else 0 with hjdef
  have hj : j ≠ i₀ := by fin_cases i₀ <;> simp [hjdef]
  refine ⟨R j, (hR j).1, (sameDisc_iff_discRel _ _).1 (hR j).2, fun ⟨e⟩ => hj ?_⟩
  obtain ⟨i, -, hi⟩ := huniq (R j) (hR j).1 (hR j).2
  have hRe : Nonempty ((R j).IsometryEquiv (R i₀)) := by rw [hR0]; exact ⟨e.symm⟩
  exact (hi j ⟨QuadraticMap.IsometryEquiv.refl _⟩).trans (hi i₀ hRe).symm

/-- If `P₁ ≇ P₂` have the same dimension and discriminant, every form with the discriminant
and dimension of `H ⊥ P₁` is isotropic (counting classes; Witt cancellation). -/
theorem not_anisotropic_of_two_classes {A : QuadraticForm F V₁} {P₁ : QuadraticForm F V₂}
    {P₂ : QuadraticForm F V₃} (hA : IsNondeg A) (h12 : DiscRel P₁ P₂)
    (hne : ¬ Nonempty (P₁.IsometryEquiv P₂)) (hd : DiscRel A ((hypForm F 1).prod P₁)) :
    ¬ A.Anisotropic := by
  intro ha
  have hd2 : DiscRel A ((hypForm F 1).prod P₂) := hd.trans ((DiscRel.refl' _).prod h12)
  rcases pigeon hA hd hd2 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact not_anisotropic_of_isometryEquiv e (not_anisotropic_hyp_prod P₁) ha
  · exact not_anisotropic_of_isometryEquiv e (not_anisotropic_hyp_prod P₂) ha
  · exact hne (witt_cancellation _ _ _ ⟨e⟩)

/-- **An anisotropic `p`-adic form has dimension `≤ 4`** (Lam, Ch. VI, Thm. 2.12; here derived
from the class count). -/
theorem finrank_le_four_of_anisotropic {A : QuadraticForm F V₁} (hA : IsNondeg A)
    (ha : A.Anisotropic) : finrank F V₁ ≤ 4 := by
  by_contra h
  obtain ⟨j, hj⟩ : ∃ j, finrank F V₁ = j + 3 := ⟨finrank F V₁ - 3, by omega⟩
  obtain ⟨P, hP, hd⟩ := exists_hyp_prod_discRel hA hj
  obtain ⟨P', -, h12, hne⟩ := exists_other_class hP (Or.inl (by omega))
  exact not_anisotropic_of_two_classes hA h12 hne hd ha

/-- Two anisotropic ternary forms with the same discriminant are isometric. -/
theorem iso_of_anisotropic_three {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}
    (h₁ : IsNondeg Q₁) (a₁ : Q₁.Anisotropic) (a₂ : Q₂.Anisotropic) (hd : DiscRel Q₁ Q₂)
    (h3 : finrank F V₁ = 3) : Nonempty (Q₁.IsometryEquiv Q₂) := by
  obtain ⟨P, -, hR⟩ := exists_hyp_prod_discRel h₁ (j := 0) h3
  rcases pigeon h₁ hd hR with he | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact he
  · exact (not_anisotropic_of_isometryEquiv e (not_anisotropic_hyp_prod P) a₁).elim
  · exact (not_anisotropic_of_isometryEquiv e (not_anisotropic_hyp_prod P) a₂).elim

/-- An anisotropic plane has a second class of its discriminant. -/
theorem exists_other_class_plane {P : QuadraticForm F (Fin 2 → F)} (hP : IsNondeg P)
    (ha : P.Anisotropic) :
    ∃ P' : QuadraticForm F (Fin 2 → F), IsNondeg P' ∧ DiscRel P P' ∧
      ¬ Nonempty (P.IsometryEquiv P') := by
  refine exists_other_class hP (Or.inr ⟨rfl, fun hsq => ?_⟩)
  obtain ⟨v, hv, hQv⟩ := exists_isotropic_of_isSquare P hsq
  exact hv (ha v hQv)

/-- A second class of the dimension and discriminant: in dimension `≥ 3`, or for an anisotropic
plane (`exists_other_class`, `exists_other_class_plane`). -/
theorem exists_other_class_of {n : ℕ} {P : QuadraticForm F (Fin n → F)} (hP : IsNondeg P)
    (hn : 3 ≤ n ∨ (n = 2 ∧ P.Anisotropic)) :
    ∃ P' : QuadraticForm F (Fin n → F), IsNondeg P' ∧ DiscRel P P' ∧
      ¬ Nonempty (P.IsometryEquiv P') := by
  rcases hn with h | ⟨rfl, ha⟩
  · exact exists_other_class hP (Or.inl h)
  · exact exists_other_class_plane hP ha

/-- The Witt decomposition `Q ≅ H^w ⊥ Q_an`, with `dim Q_an ≤ 4` over a `p`-adic field. -/
theorem exists_decomp {Q : QuadraticForm F V₁} (h : IsNondeg Q) :
    ∃ (k : ℕ) (Qa : QuadraticForm F (Fin k → F)), Qa.Anisotropic ∧ IsNondeg Qa ∧
      Nonempty (Q.IsometryEquiv ((hypForm F (wittIndex Q)).prod Qa)) ∧
      finrank F V₁ = 2 * wittIndex Q + k ∧ k ≤ 4 := by
  obtain ⟨k, Qa, ha, ⟨I⟩, hk⟩ := witt_decomposition Q h
  have hnd : IsNondeg Qa := isNondeg_of_prod_right ((DiscRel.of_isometryEquiv I).isNondeg h)
  have := finrank_le_four_of_anisotropic hnd ha
  rw [Module.finrank_fin_fun] at this
  exact ⟨k, Qa, ha, hnd, ⟨I⟩, hk, this⟩

/-- **Odd dimension**: two non-isometric forms of the same odd dimension and discriminant have
Witt indices of opposite parity (they are `H^w ⊥ ⟨a⟩` and `H^{w-1} ⊥ (anisotropic ternary)`). -/
theorem odd_wittIndex_add_of_not_iso {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}
    (h₁ : IsNondeg Q₁) (hd : DiscRel Q₁ Q₂) (hodd : Odd (finrank F V₁))
    (hne : ¬ Nonempty (Q₁.IsometryEquiv Q₂)) : Odd (wittIndex Q₁ + wittIndex Q₂) := by
  have h₂ := hd.isNondeg h₁
  have hdim := finrank_eq_of_discRel hd
  obtain ⟨k₁, A₁, a₁, n₁, ⟨I₁⟩, hk₁, l₁⟩ := exists_decomp h₁
  obtain ⟨k₂, A₂, a₂, n₂, ⟨I₂⟩, hk₂, l₂⟩ := exists_decomp h₂
  rw [Nat.odd_iff] at hodd ⊢
  by_contra hev
  have hw : wittIndex Q₂ = wittIndex Q₁ := by omega
  obtain rfl : k₂ = k₁ := by omega
  rw [hw] at I₂
  have hD : DiscRel ((hypForm F (wittIndex Q₁)).prod A₁) ((hypForm F (wittIndex Q₁)).prod A₂) :=
    ((DiscRel.of_isometryEquiv I₁).symm.trans hd).trans (DiscRel.of_isometryEquiv I₂)
  have hnd := (DiscRel.of_isometryEquiv I₁).isNondeg h₁
  have hA := discRel_cancel hnd hD
  have hJ : Nonempty (A₁.IsometryEquiv A₂) := by
    rcases (show k₂ = 1 ∨ k₂ = 3 by omega) with hk | hk
    · exact iso_of_finrank_le_one n₁ hA (by rw [Module.finrank_fin_fun]; omega)
    · exact iso_of_anisotropic_three n₁ a₁ a₂ hA (by rw [Module.finrank_fin_fun]; omega)
  obtain ⟨J⟩ := hJ
  exact hne ⟨(I₁.trans ((QuadraticMap.IsometryEquiv.refl _).prod J)).trans I₂.symm⟩

/-- In even dimension the Witt indices of two forms of the same discriminant do not differ by
`1`. -/
theorem wittIndex_ne_succ {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}
    (h₁ : IsNondeg Q₁) (hd : DiscRel Q₁ Q₂) (hev : Even (finrank F V₁)) :
    wittIndex Q₁ ≠ wittIndex Q₂ + 1 := by
  intro hw
  have h₂ := hd.isNondeg h₁
  have hdim := finrank_eq_of_discRel hd
  obtain ⟨k₁, A₁, a₁, n₁, ⟨I₁⟩, hk₁, l₁⟩ := exists_decomp h₁
  obtain ⟨k₂, A₂, a₂, n₂, ⟨I₂⟩, hk₂, l₂⟩ := exists_decomp h₂
  rw [Nat.even_iff] at hev
  obtain rfl : k₂ = k₁ + 2 := by omega
  rw [hw] at I₁
  let I₁' := (I₁.trans ((hypForm_succ_iso (wittIndex Q₂)).prod
    (QuadraticMap.IsometryEquiv.refl A₁))).trans (assocIso _ _ _)
  have hD : DiscRel ((hypForm F (wittIndex Q₂)).prod ((hypForm F 1).prod A₁))
      ((hypForm F (wittIndex Q₂)).prod A₂) :=
    ((DiscRel.of_isometryEquiv I₁').symm.trans hd).trans (DiscRel.of_isometryEquiv I₂)
  have hnd := (DiscRel.of_isometryEquiv I₁').isNondeg h₁
  have hA := discRel_cancel hnd hD
  rcases (show k₁ = 0 ∨ k₁ = 2 by omega) with rfl | rfl
  · have hH : DiscRel A₂ (hypForm F 1) :=
      hA.symm.trans (DiscRel.of_isometryEquiv (prodZeroIso _ A₁))
    obtain ⟨c, hc, hcd⟩ := hH.bases (Pi.basisFun F (Fin (0 + 2))) (Pi.basisFun F (Fin (2 * 1)))
    rw [gdet_hyp_one, gdet_basisFun] at hcd
    have hsq : IsSquare (-A₂.discr') := ⟨c⁻¹, by field_simp; linear_combination hcd⟩
    obtain ⟨v, hv, hQv⟩ := exists_isotropic_of_isSquare A₂ hsq
    exact hv (a₂ v hQv)
  · obtain ⟨P', -, h12, hne⟩ := exists_other_class_plane n₁ a₁
    exact not_anisotropic_of_two_classes n₂ h12 hne hA.symm a₂

/-- **Even dimension**: two forms of the same even dimension and discriminant have Witt indices
of the same parity. -/
theorem even_wittIndex_add {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}
    (h₁ : IsNondeg Q₁) (hd : DiscRel Q₁ Q₂) (hev : Even (finrank F V₁)) :
    Even (wittIndex Q₁ + wittIndex Q₂) := by
  have h₂ := hd.isNondeg h₁
  have hdim := finrank_eq_of_discRel hd
  have n1 := wittIndex_ne_succ h₁ hd hev
  have n2 := wittIndex_ne_succ h₂ hd.symm (hdim ▸ hev)
  obtain ⟨k₁, -, -, -, -, hk₁, l₁⟩ := exists_decomp h₁
  obtain ⟨k₂, -, -, -, -, hk₂, l₂⟩ := exists_decomp h₂
  rw [Nat.even_iff] at hev ⊢
  omega

/-- **The Kottwitz sign of a nontrivial inner form is `-1`** (`p`-adic).  If `W_α ≇ W`, then
also `V_α ≇ V` (Witt cancellation); of `W`, `V` one is odd-dimensional, where the Witt indices
have opposite parity, and on the even-dimensional one they have the same parity. -/
theorem kottwitzSign_eq_neg_one (d : GGPData F) (τ : InnerTwist d.QW)
    (hne : ¬ Nonempty (d.QW.IsometryEquiv τ.Q')) : kottwitzSign d τ = -1 := by
  have hd : DiscRel d.QW τ.Q' := (sameDisc_iff_discRel _ _).1 τ.sameDisc
  have hdV : DiscRel d.QV (τ.Q'.prod d.QZ) := hd.prod (DiscRel.refl' d.QZ)
  have hneV : ¬ Nonempty (d.QV.IsometryEquiv (τ.Q'.prod d.QZ)) := by
    rintro ⟨I⟩
    exact hne (witt_cancellation d.QZ d.QW τ.Q'
      ⟨((QuadraticMap.IsometryEquiv.prodComm d.QZ d.QW).trans I).trans
        (QuadraticMap.IsometryEquiv.prodComm τ.Q' d.QZ)⟩)
  have hdimV : finrank F d.V = d.m + (2 * d.r + 1) := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]
  unfold kottwitzSign
  show (-1 : ℤ) ^ (wittIndex d.QW + wittIndex τ.Q' + wittIndex d.QV +
    wittIndex (τ.Q'.prod d.QZ)) = -1
  apply Odd.neg_one_pow
  rw [Nat.odd_iff]
  rcases Nat.even_or_odd d.m with hm | hm
  · have hW := even_wittIndex_add d.nondeg hd (by rwa [Module.finrank_fin_fun])
    have hV := odd_wittIndex_add_of_not_iso d.nondeg_QV hdV
      (by rw [hdimV]; exact hm.add_odd (odd_two_mul_add_one _)) hneV
    rw [Nat.even_iff] at hW
    rw [Nat.odd_iff] at hV
    omega
  · have hW := odd_wittIndex_add_of_not_iso d.nondeg hd (by rwa [Module.finrank_fin_fun]) hne
    have hV := even_wittIndex_add d.nondeg_QV hdV
      (by rw [hdimV]; exact hm.add_odd (odd_two_mul_add_one _))
    rw [Nat.odd_iff] at hW
    rw [Nat.even_iff] at hV
    omega

/-- The Kottwitz sign of an inner form isometric to `W` is `1`. -/
theorem kottwitzSign_eq_one_of_nonempty (d : GGPData F) (τ : InnerTwist d.QW)
    (h : Nonempty (d.QW.IsometryEquiv τ.Q')) : kottwitzSign d τ = 1 := by
  obtain ⟨e⟩ := h
  have hW := wittIndex_eq_of_isometryEquiv e
  have hV := wittIndex_eq_of_isometryEquiv
    (e.prod (QuadraticMap.IsometryEquiv.refl d.QZ))
  unfold kottwitzSign
  show (-1 : ℤ) ^ (wittIndex d.QW + wittIndex τ.Q' + wittIndex (d.QW.prod d.QZ) +
    wittIndex (τ.Q'.prod d.QZ)) = 1
  rw [← hW, ← hV, show ∀ a b : ℕ, a + a + b + b = 2 * (a + b) from fun a b => by ring, pow_mul]
  norm_num

end Padic

end WittParity
end GSpinGGP
