/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.JointRank
import GSpinGGP.GGP.RegularRank

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

variable {n : ℕ}

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

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **The four clauses for matrices over an algebraically closed field.** -/
theorem jointClausesMat_of_isAlgClosed {J A C : Matrix (Fin n) (Fin n) K}
    (hJ : J.transpose = J) (hJd : J.det ≠ 0) (hiso : A.transpose * J * A = J)
    (hssA : Module.End.IsSemisimple (Matrix.toLin' A)) (hdet : A.det = 1)
    (hsk : C.transpose * J + J * C = 0) (hssC : Module.End.IsSemisimple (Matrix.toLin' C))
    (hc : Commute C A) : JointClausesMat J A C (n / 2) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
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
      (bform Q).IsOrthogonal (Matrix.toLin' X) := fun hX u v => by
    rw [hbf, hbf]
    conv_rhs => rw [← hX]
    simp only [Matrix.toLinearMap₂'_apply', Matrix.toLin'_apply, Matrix.dotProduct_mulVec,
      Matrix.vecMul_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hskC : (bform Q).IsSkewAdjoint (Matrix.toLin' C) :=
      LinearMap.isSkewAdjoint_iff.2 fun u v => by
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

section CharZero

variable {F : Type*} [Field F] [CharZero F]

/-- **The four clauses for matrices over a field of characteristic `0`**, by descent from the
algebraic closure. -/
theorem jointClausesMat_of_charZero {J A C : Matrix (Fin n) (Fin n) F}
    (hJ : J.transpose = J) (hJd : J.det ≠ 0) (hiso : A.transpose * J * A = J)
    (hssA : Module.End.IsSemisimple (Matrix.toLin' A)) (hdet : A.det = 1)
    (hsk : C.transpose * J + J * C = 0) (hssC : Module.End.IsSemisimple (Matrix.toLin' C))
    (hc : Commute C A) : JointClausesMat J A C (n / 2) := by
  let K := AlgebraicClosure F
  let φ := algebraMap F K
  have : CharZero K := charZero_of_injective_algebraMap φ.injective
  let M' := φ.mapMatrix (m := Fin n)
  have hM'inj : Function.Injective M' := fun X Y h => Matrix.map_injective φ.injective h
  have hK := jointClausesMat_of_isAlgClosed (J := M' J) (A := M' A) (C := M' C)
    (by rw [show (M' J).transpose = M' J.transpose from rfl, hJ]) (by rw [← RingHom.map_det]; exact (map_ne_zero φ).2 hJd)
    (by rw [show (M' A).transpose = M' A.transpose from rfl, ← map_mul, ← map_mul, hiso])
    (isSemisimple_toLin'_map hssA) (by rw [← RingHom.map_det, hdet, map_one])
    (by rw [show (M' C).transpose = M' C.transpose from rfl, ← map_mul, ← map_mul, ← map_add,
      hsk, map_zero])
    (isSemisimple_toLin'_map hssC) (hc.map M')
  have hfg : ∀ X i, jointMatMap (M' J) (M' A) (M' C) (X.map φ) i =
      (jointMatMap J A C X i).map φ := fun X i => jointMatMap_map φ J A C X i
  have hfin := finrank_ker_map_matrix _ _ hfg
  have hspan := ker_map_matrix_eq_span _ _ hfg
  rw [ker_jointMatMap, ker_jointMatMap] at hfin hspan
  have hmemK : ∀ X ∈ soCentMat J A ⊓ soCentMat J C,
      M' X ∈ soCentMat (M' J) (M' A) ⊓ soCentMat (M' J) (M' C) := fun X hX =>
    hspan ▸ Submodule.subset_span ⟨X, hX, rfl⟩
  obtain ⟨l, ab, nil, uni⟩ := hK
  refine ⟨hfin ▸ l, ⟨fun he M₁ h₁ M₂ h₂ => ?_, fun hab => ?_⟩, fun he M hM hnil => ?_,
    fun he H hH hnil hAH hCH => ?_⟩
  · have := ab.1 (hfin.trans he) _ (hmemK M₁ h₁) _ (hmemK M₂ h₂)
    exact hM'inj (by rw [map_mul, map_mul]; exact this.eq)
  · rw [← hfin]
    refine ab.2 fun X₁ h₁ X₂ h₂ => ?_
    rw [hspan] at h₁ h₂
    exact commute_of_mem_span_map hab h₁ h₂
  · have h0 := nil (hfin.trans he) _ (hmemK M hM) (hnil.map M')
    exact hM'inj (h0.trans (map_zero M').symm)
  · have h1 := uni (hfin.trans he) (M' H)
      (by rw [show (M' H).transpose = M' H.transpose from rfl, ← map_mul, ← map_mul, hH])
      (by rw [← map_one M', ← map_sub]; exact hnil.map M') (hAH.map M') (hCH.map M')
    exact hM'inj (h1.trans (map_one M').symm)

variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- **The joint centralizer over a field of characteristic `0`**: `jointClauses` for `F`. -/
theorem jointClauses_of_charZero [Invertible (2 : F)] {Q : QuadraticForm F V} {P N : Module.End F V}
    (hQ : IsNondeg Q) (hP : (bform Q).IsOrthogonal P) (hssP : P.IsSemisimple)
    (hN : (bform Q).IsSkewAdjoint N) (hssN : N.IsSemisimple) (hc : Commute N P)
    (hdet : LinearMap.det P = 1) : JointClauses Q P N (finrank F V / 2) := by
  let b := Module.finBasis F V
  set J := LinearMap.toMatrix₂ b b (bform Q)
  set T := LinearMap.toMatrixAlgEquiv b
  have hT : ∀ X, T X = LinearMap.toMatrix b b X := fun _ => rfl
  have hsymm : ∀ x y, bform Q x y = bform Q y x := bform_comm Q
  have hJ : J.transpose = J := by ext i j; simp [J, LinearMap.toMatrix₂_apply, hsymm]
  have hJd : J.det ≠ 0 := (LinearMap.nondegenerate_iff_det_ne_zero b).1 hQ
  have hisoM : ∀ {X : Module.End F V}, (bform Q).IsOrthogonal X →
      (T X).transpose * J * T X = J := fun {X} hX => by
    have hc' : (bform Q).compl₁₂ X X = bform Q := LinearMap.ext₂ fun u v => hX u v
    rw [hT, ← LinearMap.toMatrix₂_compl₁₂ b b, hc']
  have hskM : (T N).transpose * J + J * T N = 0 := by
    have h0 : (bform Q).compl₁₂ N LinearMap.id + (bform Q).compl₁₂ LinearMap.id N = 0 :=
      LinearMap.ext₂ fun u v => by simp [hN.eq u v]
    have := congrArg (LinearMap.toMatrix₂ b b) h0
    rwa [map_add, LinearMap.toMatrix₂_compl₁₂ b b, LinearMap.toMatrix₂_compl₁₂ b b,
      LinearMap.toMatrix_id, Matrix.transpose_one, one_mul, mul_one, map_zero] at this
  obtain ⟨l, ab, nil, uni⟩ := jointClausesMat_of_charZero hJ hJd (hisoM hP)
    (isSemisimple_toLin'_toMatrix b hssP) (by rw [hT, LinearMap.det_toMatrix, hdet]) hskM
    (isSemisimple_toLin'_toMatrix b hssN) (hc.map T)
  have eA := soCentMat_toMatrix b Q P
  have eC := soCentMat_toMatrix b Q N
  have hS : soCentMat J (T P) ⊓ soCentMat J (T N) =
      (soCent Q P ⊓ soCent Q N).map (LinearMap.toMatrix b b).toLinearMap := by
    rw [hT, hT, eA, eC, Submodule.map_inf _ (LinearMap.toMatrix b b).injective]
  have hfin : finrank F ↥(soCentMat J (T P) ⊓ soCentMat J (T N)) =
      finrank F ↥(soCent Q P ⊓ soCent Q N) := by
    rw [hS, LinearEquiv.finrank_map_eq]
  have hmem : ∀ X : Module.End F V,
      X ∈ soCent Q P ⊓ soCent Q N ↔ T X ∈ soCentMat J (T P) ⊓ soCentMat J (T N) := by
    intro X
    rw [hS, Submodule.mem_map_equiv, hT, LinearEquiv.symm_apply_apply]
  have hn : finrank F V = Fintype.card (Fin (finrank F V)) := by simp
  rw [hfin] at l ab nil uni
  refine ⟨l, ⟨fun he M₁ h₁ M₂ h₂ => ?_, fun hab => ?_⟩, fun he M hM hnil => ?_,
    fun he h hh hnil hPh hNh => ?_⟩
  · have := ab.1 he _ ((hmem M₁).1 h₁) _ ((hmem M₂).1 h₂)
    simpa using this.map T.symm
  · refine ab.2 fun X₁ h₁ X₂ h₂ => ?_
    have m₁ : T.symm X₁ ∈ soCent Q P ⊓ soCent Q N := by rw [hmem, AlgEquiv.apply_symm_apply]; exact h₁
    have m₂ : T.symm X₂ ∈ soCent Q P ⊓ soCent Q N := by rw [hmem, AlgEquiv.apply_symm_apply]; exact h₂
    simpa using (hab _ m₁ _ m₂).map T
  · have h0 := nil he _ ((hmem M).1 hM) (hnil.map T)
    exact T.injective (h0.trans (map_zero T).symm)
  · have h1 := uni he (T h) (hisoM hh) (by rw [← map_one T, ← map_sub]; exact hnil.map T)
      (hPh.map T) (hNh.map T)
    exact T.injective (h1.trans (map_one T).symm)

end CharZero

end GSpinGGP
