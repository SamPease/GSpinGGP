/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.SemisimpleRank
import GSpinGGP.GGP.Steinberg

/-!
# `dim so(V)_X = ⌊dim V / 2⌋` over any field of characteristic `0`

`finrank_soCent_of_commute` (algebraically closed fields) descends to any field `F` of
characteristic `0` (`finrank_soCent_of_commute_of_charZero`): in a basis, `so(V)_X` is the matrix space
`so(J)_A`, whose dimension does not change over `F̄` (`finrank_soCentMat_map`); over `F̄` the
matrix `A` stays a semisimple isometry of determinant `1` (its minimal polynomial is separable), and
`so(J)_A` stays abelian, being spanned by `so(J)_A(F)`.
-/

noncomputable section

open Module LinearMap

namespace GSpinGGP

section MatrixForm

variable {K : Type*} [Field K] [Invertible (2 : K)] {n : ℕ}

/-- The quadratic form `v ↦ vᵀ Φ v` of a symmetric matrix `Φ` has bilinear form `Φ`. -/
theorem bform_toQuadraticMap {Φ : Matrix (Fin n) (Fin n) K} (hΦ : Φ.transpose = Φ)
    (u w : Fin n → K) :
    bform (LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' K Φ)) u w =
      Matrix.toLinearMap₂' K Φ u w := by
  have hs : ∀ x y, Matrix.toLinearMap₂' K Φ x y = Matrix.toLinearMap₂' K Φ y x := fun x y => by
    rw [Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_apply', Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hΦ, dotProduct_comm]
  exact LinearMap.congr_fun₂ (QuadraticMap.associated_left_inverse (S := K) (h := hs)) u w

/-- **Matrix form of `finrank_soCent_of_commute`.** Over an algebraically closed field of
characteristic `0`, let `Φ` be symmetric with `det Φ ≠ 0` and `X` with `Xᵀ Φ X = Φ`, `det X = 1`,
`X` semisimple and `so(Φ)_X` abelian. Then `dim so(Φ)_X = ⌊n/2⌋`. -/
theorem finrank_soCentMat_of_commute [CharZero K] [IsAlgClosed K] {Φ X : Matrix (Fin n) (Fin n) K}
    (hΦ : Φ.transpose = Φ) (hΦd : Φ.det ≠ 0) (hiso : X.transpose * Φ * X = Φ)
    (hss : Module.End.IsSemisimple (Matrix.toLin' X)) (hdet : X.det = 1)
    (hab : ∀ M₁ ∈ soCentMat Φ X, ∀ M₂ ∈ soCentMat Φ X, Commute M₁ M₂) :
    finrank K (soCentMat Φ X) = n / 2 := by
  set Q : QuadraticForm K (Fin n → K) :=
    LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' K Φ)
  have hbf := bform_toQuadraticMap hΦ
  let b := Pi.basisFun K (Fin n)
  have hJ : LinearMap.toMatrix₂ b b (bform Q) = Φ := by
    ext i j
    rw [LinearMap.toMatrix₂_apply, hbf, Matrix.toLinearMap₂'_apply']
    simp [b]
  have hA : LinearMap.toMatrix b b (Matrix.toLin' X) = X := by
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  have e := soCentMat_toMatrix b Q (Matrix.toLin' X)
  rw [hJ, hA] at e
  have hQ : IsNondeg Q := by
    rw [IsNondeg, LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b]
    convert hΦd
    exact hJ
  have hXi : IsomCent.IsIsom (bform Q) (Matrix.toLin' X) := fun u v => by
    rw [hbf, hbf]
    conv_rhs => rw [← hiso]
    simp only [Matrix.toLinearMap₂'_apply', Matrix.toLin'_apply, Matrix.dotProduct_mulVec,
      Matrix.vecMul_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hab' : ∀ M₁ ∈ soCent Q (Matrix.toLin' X), ∀ M₂ ∈ soCent Q (Matrix.toLin' X),
      Commute M₁ M₂ := by
    intro M₁ h₁ M₂ h₂
    have m₁ : LinearMap.toMatrix b b M₁ ∈ soCentMat Φ X := e ▸ Submodule.mem_map_of_mem h₁
    have m₂ : LinearMap.toMatrix b b M₂ ∈ soCentMat Φ X := e ▸ Submodule.mem_map_of_mem h₂
    have hc := (hab _ m₁ _ m₂).eq
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul] at hc
    exact (LinearMap.toMatrix b b).injective hc
  rw [e, LinearEquiv.finrank_map_eq,
    finrank_soCent_of_commute hQ hXi hss (by rw [LinearMap.det_toLin', hdet]) hab', finrank_fin_fun]

end MatrixForm

section Descent

/-- If `so(J)_A` is abelian over `F`, it stays abelian over any extension `K`. -/
theorem commute_soCentMat_map {F K : Type*} [Field F] [Field K] [Algebra F K] {n : ℕ}
    {J A : Matrix (Fin n) (Fin n) F}
    (hab : ∀ M₁ ∈ soCentMat J A, ∀ M₂ ∈ soCentMat J A, Commute M₁ M₂) :
    ∀ M₁ ∈ soCentMat (J.map (algebraMap F K)) (A.map (algebraMap F K)),
      ∀ M₂ ∈ soCentMat (J.map (algebraMap F K)) (A.map (algebraMap F K)), Commute M₁ M₂ := by
  intro M₁ h₁ M₂ h₂
  rw [soCentMat_map_eq_span] at h₁ h₂
  exact commute_of_mem_span_map hab h₁ h₂

variable {F : Type*} [Field F] [CharZero F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- **`dim so(V)_X = ⌊dim V/2⌋` over any field of characteristic `0`**: `X` a semisimple isometry
of the nondegenerate form `Q` with `det X = 1` and `so(V)_X` abelian. -/
theorem finrank_soCent_of_commute_of_charZero {Q : QuadraticForm F V} (hQ : IsNondeg Q)
    {X : Module.End F V} (hX : IsomCent.IsIsom (bform Q) X) (hss : X.IsSemisimple)
    (hdet : LinearMap.det X = 1) (hab : ∀ M₁ ∈ soCent Q X, ∀ M₂ ∈ soCent Q X, Commute M₁ M₂) :
    finrank F (soCent Q X) = finrank F V / 2 := by
  set n := finrank F V
  let b := Module.finBasis F V
  set J := LinearMap.toMatrix₂ b b (bform Q)
  set A := LinearMap.toMatrix b b X
  have e := soCentMat_toMatrix b Q X
  have hsymm : ∀ x y, bform Q x y = bform Q y x := bform_comm Q
  have hJ : J.transpose = J := by ext i j; simp [J, LinearMap.toMatrix₂_apply, hsymm]
  have hJd : J.det ≠ 0 := (LinearMap.nondegenerate_iff_det_ne_zero b).1 hQ
  have hAJA : A.transpose * J * A = J := by
    have hc : (bform Q).compl₁₂ X X = bform Q := LinearMap.ext₂ fun u v => hX u v
    rw [← LinearMap.toMatrix₂_compl₁₂ b b, hc]
  have habM : ∀ M₁ ∈ soCentMat J A, ∀ M₂ ∈ soCentMat J A, Commute M₁ M₂ := by
    intro M₁ h₁ M₂ h₂
    rw [e] at h₁ h₂
    obtain ⟨N₁, hN₁, rfl⟩ := h₁
    obtain ⟨N₂, hN₂, rfl⟩ := h₂
    have := congrArg (LinearMap.toMatrix b b) (hab N₁ hN₁ N₂ hN₂).eq
    simp only [LinearMap.toMatrix_mul] at this
    exact this
  let K := AlgebraicClosure F
  let φ := algebraMap F K
  have : CharZero K := charZero_of_injective_algebraMap φ.injective
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  have hfin : finrank F (soCent Q X) = finrank F (soCentMat J A) := by
    rw [e, LinearEquiv.finrank_map_eq]
  rw [hfin, ← finrank_soCentMat_map (K := K)]
  refine finrank_soCentMat_of_commute ?_ ?_ ?_ ?_ ?_ (commute_soCentMat_map habM)
  · rw [← Matrix.transpose_map, hJ]
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero φ).2 hJd
  · rw [← Matrix.transpose_map]
    simp only [← RingHom.mapMatrix_apply, ← map_mul, hAJA]
  · exact isSemisimple_toLin'_map (isSemisimple_toLin'_toMatrix b hss)
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, LinearMap.det_toMatrix, hdet, map_one]

/-- **The centralizer of a regular semisimple `g ∈ GSpin(V)` has dimension `⌊dim V/2⌋ + 1`**, the
rank of `gspin(V)`: `g` semisimple on `C(V)` with `gspin(V)_g` abelian. -/
theorem finrank_lieCentralizer_gspin_of_isLieAbelian {Q : QuadraticForm F V} (hQ : IsNondeg Q)
    (g : GSpin Q)
    (hss : Module.End.IsSemisimple
      (LinearMap.mulLeft F ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))
    (hab : IsLieAbelian
      (lieCentralizer (gspin Q) ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))) :
    finrank F (lieCentralizer (gspin Q) ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) =
      finrank F V / 2 + 1 := by
  rw [finrank_lieCentralizer_gspin_unit hQ g, finrank_soCent_of_commute_of_charZero hQ
    (fun x y => bform_specP g x y) (isSemisimple_specP_of_isSS Q g hss) (det_specP g)
    (commute_of_isLieAbelian_lieCentralizer hQ g hab)]

end Descent

end GSpinGGP
