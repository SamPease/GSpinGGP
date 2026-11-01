/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TorusTransfer
import GSpinGGP.GGP.IsometryCentralizer

/-!
# `S_x(F̄)` is commutative

For `x ∈ GSpin(W)(F)` let `X = P(x)_{F̄}` on `W_{F̄}`.  The group `S_x(F̄) = P(T_x(F̄))`
consists of isometries of determinant `1` commuting with `X` and fixing `W'_x ⊗ F̄ = ker (X − 1)`
pointwise.  By `IsomCent.commute_of_lieAbelian` it is commutative as soon as `X` is semisimple and
the skew endomorphisms of `W_{F̄}` commuting with `X` and vanishing on `ker (X − 1)` commute
(`torusBarFbar_commute_of`).
-/

noncomputable section

open CliffordAlgebra Module
open scoped TensorProduct

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- A nondegenerate form stays nondegenerate over `F̄` (the Gram determinant is unchanged). -/
theorem isNondeg_baseChange {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (Q : QuadraticForm F V) (hQ : IsNondeg Q) :
    IsNondeg (Q.baseChange (AlgebraicClosure F)) := by
  unfold IsNondeg bform at *
  set b := Module.Free.chooseBasis F V
  rw [QuadraticForm.associated_baseChange,
    LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange (AlgebraicClosure F))]
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b] at hQ
  have : LinearMap.BilinForm.toMatrix (b.baseChange (AlgebraicClosure F))
      (LinearMap.BilinForm.baseChange (AlgebraicClosure F) (QuadraticMap.associated Q)) =
      (algebraMap F (AlgebraicClosure F)).mapMatrix
        (LinearMap.BilinForm.toMatrix b (QuadraticMap.associated Q)) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      LinearMap.BilinForm.toMatrix_apply, Module.Basis.baseChange_apply,
      Module.Basis.baseChange_apply, LinearMap.BilinForm.baseChange_tmul, mul_one,
      Algebra.smul_def, mul_one]
  rw [this, ← RingHom.map_det]
  exact (map_ne_zero _).2 hQ

namespace GGPData

variable (d : GGPData F)


/-- `P(x)_{F̄} = P(x ⊗ 1)` on `W_{F̄}`. -/
theorem specP_bcUnits (x : GSpin d.QW) (w : AlgebraicClosure F ⊗[F] (Fin d.m → F)) :
    specP (d.QW.baseChange (AlgebraicClosure F))
        ⟨bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ), TorusTransfer.bcUnits_mem_GSpin d.QW x⟩ w =
      (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange (AlgebraicClosure F) w := by
  apply ι_injective (d.QW.baseChange (AlgebraicClosure F))
  rw [ι_specP]
  exact TorusTransfer.bcUnits_conj_ι' d.QW x w

/-- Flatness: `ker (A_{F̄}) ⊆ (ker A)_{F̄}`. -/
theorem mem_baseChange_ker {V : Type*} [AddCommGroup V] [Module F V] (A : V →ₗ[F] V)
    {u : AlgebraicClosure F ⊗[F] V} (hu : u ∈ LinearMap.ker (A.baseChange (AlgebraicClosure F))) :
    u ∈ (LinearMap.ker A).baseChange (AlgebraicClosure F) := by
  have hk := Module.Flat.ker_lTensor_eq (R := F) (AlgebraicClosure F) (AlgebraicClosure F) A
  have hu' : u ∈ LinearMap.ker
      (TensorProduct.AlgebraTensorModule.lTensor (AlgebraicClosure F) (AlgebraicClosure F) A) := hu
  rw [hk] at hu'
  obtain ⟨u₀, rfl⟩ := hu'
  clear hu
  induction u₀ using TensorProduct.inductionOn with
  | tmul z k =>
    show z ⊗ₜ (k : V) ∈ _
    exact Submodule.tmul_mem_baseChange_of_mem z k.2
  | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb

/-- **`S_x(F̄)` is commutative**, given that `X = P(x)_{F̄}` is semisimple and that the skew
endomorphisms of `W_{F̄}` commuting with `X` and vanishing on `ker (X − 1)` commute. -/
theorem torusBarFbar_commute_of (x : ↥(GSpin d.QW))
    (hss : Module.End.IsSemisimple
      ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange (AlgebraicClosure F)))
    (hL : IsomCent.LieAbelian (bform (d.QW.baseChange (AlgebraicClosure F)))
      ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange (AlgebraicClosure F))) :
    ∀ s ∈ d.torusBarFbar x, ∀ t ∈ d.torusBarFbar x, Commute s t := by
  rintro s ⟨g₁, hg₁, rfl⟩ t ⟨g₂, hg₂, rfl⟩
  let X := (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange (AlgebraicClosure F)
  let xb : GSpin (d.QW.baseChange (AlgebraicClosure F)) := ⟨bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ),
    TorusTransfer.bcUnits_mem_GSpin d.QW x⟩
  have hX : X = (specP (d.QW.baseChange (AlgebraicClosure F)) xb : _ →ₗ[AlgebraicClosure F] AlgebraicClosure F ⊗[F] (Fin d.m → F)) :=
    LinearMap.ext fun w => (specP_bcUnits d x w).symm
  have hnd : (bform (d.QW.baseChange (AlgebraicClosure F))).Nondegenerate := isNondeg_baseChange _ d.nondeg
  have hB : (bform (d.QW.baseChange (AlgebraicClosure F))).IsSymm := ⟨fun u v => bform_comm (d.QW.baseChange (AlgebraicClosure F)) u v⟩
  have hiso : ∀ g : GSpin (d.QW.baseChange (AlgebraicClosure F)), IsomCent.IsIsom (bform (d.QW.baseChange (AlgebraicClosure F))) (specP (d.QW.baseChange (AlgebraicClosure F)) g : _ →ₗ[AlgebraicClosure F] AlgebraicClosure F ⊗[F] (Fin d.m → F)) :=
    fun g u v => bform_specP g u v
  have hcomm : ∀ g ∈ d.torusFbar x, Commute X (specP (d.QW.baseChange (AlgebraicClosure F)) g : _ →ₗ[AlgebraicClosure F] AlgebraicClosure F ⊗[F] (Fin d.m → F)) := by
    intro g hg
    have hc : xb * g = g * xb := by
      apply Subtype.ext
      exact hg.1.eq.symm
    rw [hX]
    refine LinearMap.ext fun w => ?_
    show specP (d.QW.baseChange (AlgebraicClosure F)) xb (specP (d.QW.baseChange (AlgebraicClosure F)) g w) = specP (d.QW.baseChange (AlgebraicClosure F)) g (specP (d.QW.baseChange (AlgebraicClosure F)) xb w)
    rw [← LinearEquiv.mul_apply, ← map_mul, hc, map_mul, LinearEquiv.mul_apply]
  have hfix : ∀ g ∈ d.torusFbar x, ∀ z ∈ Module.End.eigenspace X 1,
      (specP (d.QW.baseChange (AlgebraicClosure F)) g : _ →ₗ[AlgebraicClosure F] AlgebraicClosure F ⊗[F] (Fin d.m → F)) z = z := by
    intro g hg z hz
    apply hg.2
    rw [Module.End.mem_eigenspace_iff, one_smul] at hz
    apply mem_baseChange_ker
    rw [LinearMap.mem_ker, LinearMap.baseChange_sub, LinearMap.baseChange_id, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    exact hz
  have hXi : IsomCent.IsIsom (bform (d.QW.baseChange (AlgebraicClosure F))) X := by
    rw [hX]; exact hiso xb
  have hc := IsomCent.commute_of_lieAbelian hB hnd hXi hss hL (hiso g₁) (hiso g₂)
    (det_specP g₁) (det_specP g₂) (hcomm g₁ hg₁) (hcomm g₂ hg₂) (hfix g₁ hg₁) (hfix g₂ hg₂)
  apply Units.ext
  simp only [Units.val_mul, coe_specMatFbar]
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  exact congrArg _ hc.eq

end GGPData

end GSpinGGP
