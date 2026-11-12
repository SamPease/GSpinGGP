/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TorusTransfer
import GSpinGGP.Foundations.IsometryCentralizer
import GSpinGGP.Foundations.IsometryDet
import GSpinGGP.GGP.Descent
import GSpinGGP.GGP.Steinberg
import TauCeti.LinearAlgebra.TensorProduct.Kernel

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

section Semisimple

variable {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]

open Polynomial

omit [Module.Finite F V] in
/-- Semisimplicity survives base change to `F̄` (characteristic `0`: squarefree polynomials stay
squarefree). -/
theorem isSemisimple_baseChange {f : Module.End F V} [Module.Finite F V]
    (hf : f.IsSemisimple) : Module.End.IsSemisimple (f.baseChange (AlgebraicClosure F)) :=
  IsomCent.isSemisimple_baseChange_algebraicClosure hf

/-- A semisimple element of the algebra `End V` (`IsSS`: `L_f` semisimple on `End V`) is a
semisimple endomorphism: `L_f` and `f` have the same minimal polynomial (`Algebra.lmul` is
injective).  Converse of `isSS_of_isSemisimple`. -/
theorem isSemisimple_of_isSS {f : Module.End F V} (hf : IsSS F f) : f.IsSemisimple := by
  have h : minpoly F (Algebra.lmul F (Module.End F V) f) = minpoly F f :=
    minpoly.algHom_eq _ (Algebra.lmul_injective (R := F)) f
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero ?_ (minpoly.aeval F f)
  rw [← h]
  exact Module.End.IsSemisimple.minpoly_squarefree hf

end Semisimple

section Lift

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
/-- `[ι a ι c, ι v] = 2 b(c,v) ι a − 2 b(a,v) ι c`. -/
theorem commutator_ι_mul_ι (a c v : V) :
    ι Q a * ι Q c * ι Q v - ι Q v * (ι Q a * ι Q c) =
      (2 * bform Q c v) • ι Q a - (2 * bform Q a v) • ι Q c := by
  have h1 := CliffordAlgebra.ι_mul_ι_add_swap (Q := Q) c v
  have h2 := CliffordAlgebra.ι_mul_ι_add_swap (Q := Q) a v
  rw [polar_eq_two_mul_bform] at h1 h2
  have e1 : ι Q c * ι Q v = algebraMap K _ (2 * bform Q c v) - ι Q v * ι Q c := by
    rw [← h1]; abel
  have e2 : ι Q v * ι Q a = algebraMap K _ (2 * bform Q a v) - ι Q a * ι Q v := by
    rw [← h2]; abel
  rw [mul_assoc, e1, ← mul_assoc (ι Q v), e2, mul_sub, sub_mul, ← Algebra.commutes,
    ← Algebra.smul_def, ← Algebra.smul_def]
  simp only [mul_assoc]
  abel

/-- **Lifting `so(V)` to `C(V)`**: a `b`-skew endomorphism `Y` of a nondegenerate `V` is
`[Ŷ, ·]` on `ι(V)` for an even `Ŷ = ¼ Σ ι(Y bᵢ) ι(dᵢ) ∈ gspin(V)` (`dᵢ` the `b`-dual basis). -/
theorem exists_lift_skew (hQ : IsNondeg Q) (Y : Module.End K V)
    (hY : ∀ u v, bform Q (Y u) v = - bform Q u (Y v)) :
    ∃ Yh : CliffordAlgebra Q, Yh ∈ gspin Q ∧ ∀ v, Yh * ι Q v - ι Q v * Yh = ι Q (Y v) := by
  classical
  let b := Module.finBasis K V
  have hsym : (bform Q).IsSymm := ⟨fun u v => bform_comm Q u v⟩
  let dB := (bform Q).dualBasis hQ b
  refine ⟨(⅟2 * ⅟2 : K) • ∑ i, ι Q (Y (b i)) * ι Q (dB i), (gspin Q).smul_mem _
    (Submodule.sum_mem _ fun i _ => ι_mul_ι_mem_gspin Q _ _), fun v => ?_⟩
  have e1 : ∑ i, bform Q (dB i) v • b i = v := by
    conv_rhs => rw [← b.sum_repr v]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    conv_lhs => rw [← b.sum_repr v]
    have hd : ∀ x, (bform Q) (dB i) (b x) = if x = i then 1 else 0 := fun x =>
      LinearMap.BilinForm.apply_dualBasis_left hQ b i x
    simp only [map_sum, map_smul, smul_eq_mul, hd, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have e2 : ∑ i, bform Q (b i) (Y v) • dB i = Y v := by
    conv_rhs => rw [← dB.sum_repr (Y v)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hr := LinearMap.BilinForm.dualBasis_repr_apply hQ b (Y v) i
    rw [hr, bform_comm]
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [commutator_ι_mul_ι, Finset.sum_sub_distrib]
  have s1 : ∑ x, (2 * bform Q (dB x) v) • ι Q (Y (b x)) = (2 : K) • ι Q (Y v) := by
    conv_rhs => rw [← e1]
    simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
  have s2 : ∑ x, (2 * bform Q (Y (b x)) v) • ι Q (dB x) = (-2 : K) • ι Q (Y v) := by
    conv_rhs => rw [← e2]
    simp only [map_sum, map_smul, Finset.smul_sum, smul_smul, hY, bform_comm Q (b _) (Y v)]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1; ring
  rw [s1, s2, ← sub_smul, smul_smul]
  have h4 : (⅟2 * ⅟2 : K) * (2 - -2) = 1 := by
    rw [show (2 : K) - -2 = 2 * 2 by ring, mul_mul_mul_comm, invOf_mul_self, one_mul]
  rw [h4, one_smul]

end Lift

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

/-- Flatness: `ker (A_{F̄}) ⊆ (ker A)_{F̄}` (Tau Ceti's `LinearMap.ker_baseChange_of_flat`). -/
theorem mem_baseChange_ker {V : Type*} [AddCommGroup V] [Module F V] (A : V →ₗ[F] V)
    {u : AlgebraicClosure F ⊗[F] V} (hu : u ∈ LinearMap.ker (A.baseChange (AlgebraicClosure F))) :
    u ∈ (LinearMap.ker A).baseChange (AlgebraicClosure F) := by
  rwa [← LinearMap.ker_baseChange_of_flat]

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
  have hiso : ∀ g : GSpin (d.QW.baseChange (AlgebraicClosure F)), LinearMap.IsOrthogonal (bform (d.QW.baseChange (AlgebraicClosure F))) (specP (d.QW.baseChange (AlgebraicClosure F)) g : _ →ₗ[AlgebraicClosure F] AlgebraicClosure F ⊗[F] (Fin d.m → F)) :=
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
  have hXi : LinearMap.IsOrthogonal (bform (d.QW.baseChange (AlgebraicClosure F))) X := by
    rw [hX]; exact hiso xb
  have hc := IsomCent.commute_of_lieAbelian hB hnd hXi hss hL (hiso g₁) (hiso g₂)
    (det_specP g₁) (det_specP g₂) (hcomm g₁ hg₁) (hcomm g₂ hg₂) (hfix g₁ hg₁) (hfix g₂ hg₂)
  apply Units.ext
  simp only [Units.val_mul, coe_specMatFbar]
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  exact congrArg _ hc.eq

end GGPData

end GSpinGGP
