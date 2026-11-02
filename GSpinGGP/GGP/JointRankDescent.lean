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

end GSpinGGP
