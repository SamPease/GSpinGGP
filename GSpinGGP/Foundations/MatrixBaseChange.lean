/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.MatrixAlgebra

/-!
# Matrices under extension of scalars

For a field extension `K / F`:

* `matrixBaseChangeEquiv`: `K ⊗[F] Mat_n(F) ≃ Mat_n(K)`, `K`-linearly.
* `finrank_ker_map_matrix`, `ker_map_matrix_eq_span`: for `F`-linear `f : Mat_n(F) → (ι → Mat_n(F))`
  with a `K`-linear counterpart `g` (`g (M.map φ) = (f M).map φ`), the kernel of `g` has the same
  dimension as that of `f` and is spanned by the images of the kernel of `f`.
* `commute_of_mem_span_map`: pairwise commuting matrices over `F` span pairwise commuting matrices
  over `K`.
* `isSemisimple_toLin'_map`: a semisimple matrix over a perfect field stays semisimple over `K`;
  `isSemisimple_toLin'_toMatrix`: the matrix of a semisimple endomorphism is semisimple.
-/

noncomputable section

open Module
open scoped TensorProduct

namespace GSpinGGP

variable {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

variable (F K) in
/-- `K ⊗[F] Mat_n(F) ≃ Mat_n(K)`, `K`-linearly: `a ⊗ M ↦ a • M.map (algebraMap F K)`. -/
def matrixBaseChangeEquiv :
    K ⊗[F] Matrix n n F ≃ₗ[K] Matrix n n K :=
  { (matrixEquivTensor n F K).symm.toLinearEquiv with
    map_smul' := fun c x => by
      change (matrixEquivTensor n F K).symm (c • x) = c • (matrixEquivTensor n F K).symm x
      induction x using TensorProduct.inductionOn with
      | tmul a M =>
        rw [TensorProduct.smul_tmul', matrixEquivTensor_apply_symm, matrixEquivTensor_apply_symm,
          smul_smul, smul_eq_mul]
      | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add] }

variable (F K) in
@[simp]
theorem matrixBaseChangeEquiv_tmul (a : K) (M : Matrix n n F) :
    matrixBaseChangeEquiv (n := n) F K (a ⊗ₜ M) = a • M.map (algebraMap F K) :=
  matrixEquivTensor_apply_symm _ _ _ _ _

variable (n ι F K) in
/-- `K ⊗[F] (ι → Mat_n(F)) ≃ (ι → Mat_n(K))`. -/
def matrixPiBaseChangeEquiv :
    K ⊗[F] (ι → Matrix n n F) ≃ₗ[K] (ι → Matrix n n K) :=
  (TensorProduct.piRight F K K fun _ : ι => Matrix n n F).trans
    (LinearEquiv.piCongrRight fun _ => matrixBaseChangeEquiv (n := n) F K)

@[simp]
theorem matrixPiBaseChangeEquiv_tmul (a : K) (f : ι → Matrix n n F) (i : ι) :
    matrixPiBaseChangeEquiv n ι F K (a ⊗ₜ f) i = a • (f i).map (algebraMap F K) := by
  simp [matrixPiBaseChangeEquiv, matrixBaseChangeEquiv_tmul]

section Kernel

omit [DecidableEq n] [DecidableEq ι]

variable (f : Matrix n n F →ₗ[F] (ι → Matrix n n F)) (g : Matrix n n K →ₗ[K] (ι → Matrix n n K))
  (hfg : ∀ M i, g (M.map (algebraMap F K)) i = (f M i).map (algebraMap F K))
include hfg

/-- **Kernel dimension is unchanged by extension of scalars.** -/
theorem finrank_ker_map_matrix : finrank K (LinearMap.ker g) = finrank F (LinearMap.ker f) := by
  classical
  let e1 := matrixBaseChangeEquiv (n := n) F K
  let e2 := matrixPiBaseChangeEquiv n ι F K
  have hcomm : ∀ x, g (e1 x) = e2 (f.baseChange K x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a M =>
      funext i
      rw [LinearMap.baseChange_tmul, matrixPiBaseChangeEquiv_tmul]
      change g (matrixBaseChangeEquiv F K (a ⊗ₜ M)) i = _
      rw [matrixBaseChangeEquiv_tmul, map_smul, Pi.smul_apply, hfg]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hker : LinearMap.ker g = (LinearMap.ker (f.baseChange K)).map e1.toLinearMap := by
    ext y
    rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
    have := hcomm (e1.symm y)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [this, LinearEquiv.map_eq_zero_iff]
  rw [hker, LinearEquiv.finrank_map_eq]
  exact (LinearMap.tensorKerEquiv K K f).finrank_eq.symm.trans Module.finrank_baseChange

/-- **The kernel over `K` is spanned by the kernel over `F`.** -/
theorem ker_map_matrix_eq_span :
    LinearMap.ker g = Submodule.span K
      ((fun M : Matrix n n F => M.map (algebraMap F K)) '' LinearMap.ker f) := by
  classical
  set φ := algebraMap F K
  have hle : Submodule.span K ((fun M : Matrix n n F => M.map φ) '' LinearMap.ker f) ≤
      LinearMap.ker g := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨M, hM, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hM ⊢
    funext i
    rw [hfg, hM]
    simp
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  let b := Module.finBasis F (LinearMap.ker f)
  have hli : LinearIndependent K fun i => ((b i : Matrix n n F)).map φ := by
    have h1 := Module.Flat.linearIndependent_one_tmul (S := K)
      (b.linearIndependent.map' (LinearMap.ker f).subtype (Submodule.ker_subtype _))
    have h2 := h1.map' (matrixBaseChangeEquiv (n := n) F K).toLinearMap (LinearEquiv.ker _)
    simpa [Function.comp_def, matrixBaseChangeEquiv_tmul] using h2
  rw [finrank_ker_map_matrix f g hfg, Module.finrank_eq_card_basis b, ← finrank_span_eq_card hli]
  exact Submodule.finrank_mono (Submodule.span_mono (by
    rintro _ ⟨i, rfl⟩; exact ⟨_, (b i).2, rfl⟩))

end Kernel

omit [DecidableEq n] in
/-- If the matrices in `S` commute pairwise over `F`, so do the matrices in the `K`-span of their
images over `K`. -/
theorem commute_of_mem_span_map {S : Set (Matrix n n F)}
    (hS : ∀ M₁ ∈ S, ∀ M₂ ∈ S, Commute M₁ M₂) {X Y : Matrix n n K}
    (hX : X ∈ Submodule.span K ((fun M : Matrix n n F => M.map (algebraMap F K)) '' S))
    (hY : Y ∈ Submodule.span K ((fun M : Matrix n n F => M.map (algebraMap F K)) '' S)) :
    Commute X Y := by
  classical
  induction hX using Submodule.span_induction with
  | mem x hx =>
    induction hY using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨M, hM, rfl⟩ := hx
      obtain ⟨N, hN, rfl⟩ := hy
      exact (hS M hM N hN).map (algebraMap F K).mapMatrix
    | zero => exact Commute.zero_right _
    | add y z _ _ hy hz => exact hy.add_right hz
    | smul c y _ hy => exact hy.smul_right c
  | zero => exact Commute.zero_left _
  | add x y _ _ hx hy => exact hx.add_left hy
  | smul c x _ hx => exact hx.smul_left c

/-- A semisimple matrix over a perfect field stays semisimple over any extension. -/
theorem isSemisimple_toLin'_map [PerfectField F] {A : Matrix n n F}
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

/-- The matrix (as `toLin'`) of a semisimple endomorphism in a basis is semisimple. -/
theorem isSemisimple_toLin'_toMatrix {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (b : Basis n F V) {X : Module.End F V} (hX : X.IsSemisimple) :
    Module.End.IsSemisimple (Matrix.toLin' (LinearMap.toMatrix b b X)) := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hX.minpoly_squarefree ?_
  rw [show Matrix.toLin' (LinearMap.toMatrix b b X) =
      Matrix.toLinAlgEquiv' (LinearMap.toMatrix b b X) from rfl, Polynomial.aeval_algHom_apply,
    show LinearMap.toMatrix b b X = LinearMap.toMatrixAlgEquiv b X from rfl,
    Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero, map_zero]

end GSpinGGP
