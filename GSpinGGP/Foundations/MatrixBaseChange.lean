/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.SoCentralizer

/-!
# Kernels of matrix maps under extension of scalars

For a field extension `K / F` and `F`-linear `f : Mat_n(F) → (ι → Mat_n(F))` with a `K`-linear
counterpart `g` (`g (M.map φ) = (f M).map φ`), the kernel of `g` has the same dimension as that of `f`
(`finrank_ker_map_matrix`) and is spanned by the images of the kernel of `f`
(`ker_map_matrix_eq_span`).
-/

noncomputable section

open Module
open scoped TensorProduct

namespace GSpinGGP

variable {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- `K ⊗[F] (ι → Mat_n(F)) ≃ (ι → Mat_n(K))`. -/
def matrixPiBaseChangeEquiv (n ι F K : Type*) [Fintype n] [DecidableEq n] [Fintype ι]
    [DecidableEq ι] [Field F] [Field K] [Algebra F K] :
    K ⊗[F] (ι → Matrix n n F) ≃ₗ[K] (ι → Matrix n n K) :=
  (TensorProduct.piRight F K K fun _ : ι => Matrix n n F).trans
    (LinearEquiv.piCongrRight fun _ => matrixBaseChangeEquiv (n := n) F K)

theorem matrixPiBaseChangeEquiv_tmul (a : K) (f : ι → Matrix n n F) (i : ι) :
    matrixPiBaseChangeEquiv n ι F K (a ⊗ₜ f) i = a • (f i).map (algebraMap F K) := by
  simp [matrixPiBaseChangeEquiv, matrixBaseChangeEquiv_tmul]

variable (f : Matrix n n F →ₗ[F] (ι → Matrix n n F)) (g : Matrix n n K →ₗ[K] (ι → Matrix n n K))
  (hfg : ∀ M i, g (M.map (algebraMap F K)) i = (f M i).map (algebraMap F K))
include hfg

/-- **Kernel dimension is unchanged by extension of scalars.** -/
theorem finrank_ker_map_matrix : finrank K (LinearMap.ker g) = finrank F (LinearMap.ker f) := by
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

end GSpinGGP
