/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.JointRank
import GSpinGGP.GGP.RegularRank
import GSpinGGP.Foundations.MatrixBaseChange

/-!
# The joint centralizer over a field of characteristic `0`

`jointClauses` (algebraically closed fields) descends to any field `F` of characteristic `0`
(`jointClauses_of_charZero`): in a basis, `so(V)_P ⊓ so(V)_N` is the kernel of a linear map of
matrices, whose dimension is unchanged over `F̄` and which is spanned there by its `F`-points
(`finrank_ker_map_matrix`, `ker_map_matrix_eq_span`).
-/

noncomputable section

open Module LinearMap

namespace GSpinGGP

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {n : ℕ}

/-- A semisimple matrix over a perfect field stays semisimple over any extension. -/
theorem isSemisimple_toLin'_map [PerfectField F] {A : Matrix (Fin n) (Fin n) F}
    (hA : Module.End.IsSemisimple (Matrix.toLin' A)) :
    Module.End.IsSemisimple (Matrix.toLin' (A.map (algebraMap F K))) := by
  have hsep : (minpoly F (Matrix.toLin' A)).Separable :=
    PerfectField.separable_iff_squarefree.2 hA.minpoly_squarefree
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := (minpoly F (Matrix.toLin' A)).map (algebraMap F K)) (hsep.map).squarefree ?_
  have h0 : Polynomial.aeval A (minpoly F (Matrix.toLin' A)) = 0 := by
    rw [Matrix.minpoly_toLin']; exact minpoly.aeval F A
  rw [show Matrix.toLin' (A.map (algebraMap F K)) = Matrix.toLinAlgEquiv' (A.map (algebraMap F K))
      from rfl, Polynomial.aeval_algHom_apply, Polynomial.aeval_map_algebraMap,
    show A.map (algebraMap F K) = (Algebra.ofId F K).mapMatrix A from rfl,
    Polynomial.aeval_algHom_apply, h0, map_zero, map_zero]

section JointMat

variable {R : Type*} [CommRing R]

/-- `B ↦ (Bᵀ J + J B, B A − A B, B C − C B)`, whose kernel is `so(J)_A ⊓ so(J)_C`. -/
def jointMatMap (J A C : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R →ₗ[R] (Fin 3 → Matrix (Fin n) (Fin n) R) where
  toFun B := ![B.transpose * J + J * B, B * A - A * B, B * C - C * B]
  map_add' B B' := by
    funext i; fin_cases i <;>
      simp [Matrix.transpose_add, add_mul, mul_add, sub_eq_add_neg, neg_add] <;> abel
  map_smul' c B := by
    funext i; fin_cases i <;> simp [Matrix.transpose_smul, smul_sub, smul_add]

theorem ker_jointMatMap (J A C : Matrix (Fin n) (Fin n) R) :
    LinearMap.ker (jointMatMap J A C) = soCentMat J A ⊓ soCentMat J C := by
  ext B
  simp only [LinearMap.mem_ker, Submodule.mem_inf, soCentMat_eq_ker, soCentMatMap,
    LinearMap.coe_mk, AddHom.coe_mk, jointMatMap, Prod.mk_eq_zero]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp at h0 h1 h2
    exact ⟨⟨h0, h1⟩, h0, h2⟩
  · rintro ⟨⟨h0, h1⟩, -, h2⟩
    funext i; fin_cases i <;> simp [h0, h1, h2]

theorem jointMatMap_map (φ : R →+* K) (J A C M : Matrix (Fin n) (Fin n) R) (i : Fin 3) :
    jointMatMap (J.map φ) (A.map φ) (C.map φ) (M.map φ) i = (jointMatMap J A C M i).map φ := by
  fin_cases i <;>
    simp [jointMatMap, ← Matrix.transpose_map, ← RingHom.mapMatrix_apply, map_mul, map_add, map_sub] <;>
    rfl

end JointMat

section MatClauses

variable {R : Type*} [CommRing R]

/-- The four clauses for `S = so(J)_A ⊓ so(J)_C` (matrices) with bound `ℓ`. -/
def JointClausesMat (J A C : Matrix (Fin n) (Fin n) R) (ℓ : ℕ) : Prop :=
  ℓ ≤ finrank R ↥(soCentMat J A ⊓ soCentMat J C) ∧
  (finrank R ↥(soCentMat J A ⊓ soCentMat J C) = ℓ ↔
    ∀ M₁ ∈ soCentMat J A ⊓ soCentMat J C, ∀ M₂ ∈ soCentMat J A ⊓ soCentMat J C, Commute M₁ M₂) ∧
  (finrank R ↥(soCentMat J A ⊓ soCentMat J C) = ℓ →
    ∀ M ∈ soCentMat J A ⊓ soCentMat J C, IsNilpotent M → M = 0) ∧
  (finrank R ↥(soCentMat J A ⊓ soCentMat J C) = ℓ → ∀ H : Matrix (Fin n) (Fin n) R,
    H.transpose * J * H = J → IsNilpotent (H - 1) → Commute A H → Commute C H → H = 1)

end MatClauses

section AlgClosed

variable [Invertible (2 : K)] [CharZero K] [IsAlgClosed K]

/-- **The four clauses for matrices over an algebraically closed field.** -/
theorem jointClausesMat_of_isAlgClosed {J A C : Matrix (Fin n) (Fin n) K}
    (hJ : J.transpose = J) (hJd : J.det ≠ 0) (hiso : A.transpose * J * A = J)
    (hssA : Module.End.IsSemisimple (Matrix.toLin' A)) (hdet : A.det = 1)
    (hsk : C.transpose * J + J * C = 0) (hssC : Module.End.IsSemisimple (Matrix.toLin' C))
    (hc : Commute C A) : JointClausesMat J A C (n / 2) := by
  set Q : QuadraticForm K (Fin n → K) :=
    LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' K J)
  have hbf := bform_toQuadraticMap hJ
  let b := Pi.basisFun K (Fin n)
  have hJb : LinearMap.toMatrix₂ b b (bform Q) = J := by
    ext i j
    rw [LinearMap.toMatrix₂_apply, hbf, Matrix.toLinearMap₂'_apply']
    simp [b]
  have hM : ∀ X : Matrix (Fin n) (Fin n) K, LinearMap.toMatrix b b (Matrix.toLin' X) = X :=
    fun X => by rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  have eA := soCentMat_toMatrix b Q (Matrix.toLin' A)
  have eC := soCentMat_toMatrix b Q (Matrix.toLin' C)
  rw [hJb, hM] at eA eC
  have hS : soCentMat J A ⊓ soCentMat J C =
      (soCent Q (Matrix.toLin' A) ⊓ soCent Q (Matrix.toLin' C)).map
        (LinearMap.toMatrix b b).toLinearMap := by
    rw [eA, eC, Submodule.map_inf _ (LinearMap.toMatrix b b).injective]
  have hQ : IsNondeg Q := by
    rw [IsNondeg, LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b]
    convert hJd
    exact hJb
  have hiso' : ∀ {X : Matrix (Fin n) (Fin n) K}, X.transpose * J * X = J →
      IsomCent.IsIsom (bform Q) (Matrix.toLin' X) := fun hX u v => by
    rw [hbf, hbf]
    conv_rhs => rw [← hX]
    simp only [Matrix.toLinearMap₂'_apply', Matrix.toLin'_apply, Matrix.dotProduct_mulVec,
      Matrix.vecMul_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hskC : IsomCent.IsSkew (bform Q) (Matrix.toLin' C) := fun u v => by
    rw [hbf, hbf, eq_neg_iff_add_eq_zero]
    have : (C.transpose * J + J * C) = 0 := hsk
    simp only [Matrix.toLinearMap₂'_apply', Matrix.toLin'_apply, Matrix.dotProduct_mulVec,
      Matrix.vecMul_mulVec]
    rw [Matrix.vecMul_vecMul, ← add_dotProduct, ← Matrix.vecMul_add, this, Matrix.vecMul_zero,
      zero_dotProduct]
  set T := Matrix.toLinAlgEquiv' (R := K) (n := Fin n)
  have hT : ∀ X : Matrix (Fin n) (Fin n) K, T X = Matrix.toLin' X := fun _ => rfl
  have hcAC : Commute (Matrix.toLin' C) (Matrix.toLin' A) := by
    rw [← hT, ← hT]; exact hc.map T
  obtain ⟨l, ab, nil, uni⟩ := jointClauses (Q := Q) hQ (hiso' hiso) hssA hskC hssC hcAC
    (by rw [LinearMap.det_toLin', hdet])
  have hfin : finrank K ↥(soCentMat J A ⊓ soCentMat J C) =
      finrank K ↥(soCent Q (Matrix.toLin' A) ⊓ soCent Q (Matrix.toLin' C)) := by
    rw [hS, LinearEquiv.finrank_map_eq]
  have hn : finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hmem : ∀ M : Matrix (Fin n) (Fin n) K, M ∈ soCentMat J A ⊓ soCentMat J C ↔
      Matrix.toLin' M ∈ soCent Q (Matrix.toLin' A) ⊓ soCent Q (Matrix.toLin' C) := by
    intro M
    rw [hS]
    constructor
    · rintro ⟨X, hX, rfl⟩
      rwa [LinearEquiv.coe_coe, LinearMap.toMatrix_eq_toMatrix', Matrix.toLin'_toMatrix']
    · intro h
      exact ⟨Matrix.toLin' M, h, hM M⟩
  rw [hn] at l ab nil uni
  refine ⟨hfin ▸ l, ⟨fun he M₁ h₁ M₂ h₂ => ?_, fun hab => ?_⟩, fun he M hM' hnil => ?_,
    fun he H hH hnil hAH hCH => ?_⟩
  · have := (ab.1 (hfin ▸ he) _ ((hmem M₁).1 h₁) _ ((hmem M₂).1 h₂))
    rw [← hT, ← hT] at this
    simpa using this.map T.symm
  · rw [hfin]
    refine ab.2 fun X₁ h₁ X₂ h₂ => ?_
    have m₁ : LinearMap.toMatrix' X₁ ∈ soCentMat J A ⊓ soCentMat J C := by
      rw [hmem, Matrix.toLin'_toMatrix']; exact h₁
    have m₂ : LinearMap.toMatrix' X₂ ∈ soCentMat J A ⊓ soCentMat J C := by
      rw [hmem, Matrix.toLin'_toMatrix']; exact h₂
    have := (hab _ m₁ _ m₂).map T
    simpa [hT, Matrix.toLin'_toMatrix'] using this
  · have h0 := nil (hfin ▸ he) _ ((hmem M).1 hM') (by rw [← hT]; exact hnil.map T)
    rw [← hT] at h0
    exact T.injective (h0.trans (map_zero T).symm)
  · have h1 := uni (hfin ▸ he) (Matrix.toLin' H) (hiso' hH)
      (by rw [← hT, ← map_one T, ← map_sub]; exact hnil.map T)
      (by rw [← hT, ← hT]; exact hAH.map T) (by rw [← hT, ← hT]; exact hCH.map T)
    rw [← hT, ← map_one T] at h1
    exact T.injective h1

end AlgClosed

end GSpinGGP
