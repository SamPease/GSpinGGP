/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TorusTransfer
import GSpinGGP.GGP.IsometryCentralizer
import GSpinGGP.GGP.Descent
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

section Semisimple

variable {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]

open Polynomial

/-- `P(x)` is semisimple for semisimple `x` (characteristic `0`). -/
theorem isSemisimple_specP_of_isSS (Q : QuadraticForm F V) (x : GSpin Q)
    (hx : IsSS F (((x : (CliffordAlgebra Q)ˣ)) : CliffordAlgebra Q)) :
    Module.End.IsSemisimple (specP Q x : V →ₗ[F] V) := by
  set a : CliffordAlgebra Q := (((x : (CliffordAlgebra Q)ˣ)) : CliffordAlgebra Q) with ha
  set ai : CliffordAlgebra Q := ((((x : (CliffordAlgebra Q)ˣ))⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) with hai
  -- `a⁻¹ ∈ F[a]`
  have hinv : ai ∈ Algebra.adjoin F {a} := by
    let A := Algebra.adjoin F {a}
    let f : A →ₗ[F] A := LinearMap.mulLeft F (⟨a, Algebra.subset_adjoin rfl⟩ : A)
    have hinj : Function.Injective f := by
      intro y z h
      apply Subtype.ext
      have h' : a * (y : CliffordAlgebra Q) = a * z := congrArg Subtype.val h
      have := congrArg (ai * ·) h'
      simpa only [← mul_assoc, ha, hai, Units.inv_mul, one_mul] using this
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hinj) 1
    have hy' : a * (y : CliffordAlgebra Q) = 1 := congrArg Subtype.val hy
    have : (y : CliffordAlgebra Q) = ai := by
      calc (y : CliffordAlgebra Q) = ai * (a * y) := by
            rw [← mul_assoc, hai, ha, Units.inv_mul, one_mul]
        _ = ai := by rw [hy', mul_one]
    rw [← this]; exact y.2
  -- `L_a` and `R_{a⁻¹}` are commuting semisimple operators
  have hqa : aeval a (minpoly F (LinearMap.mulLeft F a)) = 0 := by
    have h0 : aeval (LinearMap.mulLeft F a) (minpoly F (LinearMap.mulLeft F a)) = 0 :=
      minpoly.aeval F _
    rw [show LinearMap.mulLeft F a = Algebra.lmul F (CliffordAlgebra Q) a from rfl,
      aeval_algHom_apply] at h0
    exact Algebra.lmul_injective (R := F) (h0.trans (map_zero _).symm)
  have hRa : Module.End.IsSemisimple (LinearMap.mulRight F a) :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hx.minpoly_squarefree
      (by rw [aeval_mulRight, hqa, LinearMap.mulRight_zero_eq_zero])
  have hRai : Module.End.IsSemisimple (LinearMap.mulRight F ai) := by
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hinv
    obtain ⟨r, hr⟩ := hinv
    have hr' : aeval a r = ai := hr
    rw [← hr', ← aeval_mulRight]
    exact hRa.aeval r
  have hc : Module.End.IsSemisimple (LinearMap.mulLeft F a * LinearMap.mulRight F ai) :=
    Module.End.IsSemisimple.mul_of_commute (LinearMap.commute_mulLeft_right a ai) hx hRai
  -- `ι ∘ P(x) = c ∘ ι`, so the minimal polynomial of `c` kills `P(x)`
  set c := LinearMap.mulLeft F a * LinearMap.mulRight F ai
  have hint : ∀ v, ι Q (specP Q x v) = c (ι Q v) := fun v => by
    rw [ι_specP]
    simp only [c, Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, ha,
      hai, mul_assoc]
  have hpow : ∀ (n : ℕ) v, ι Q (((specP Q x : V →ₗ[F] V) ^ n) v) = (c ^ n) (ι Q v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, LinearEquiv.coe_coe,
        hint, ih]
  have hint' : ∀ (q : F[X]) v, ι Q (aeval (specP Q x : V →ₗ[F] V) q v) = aeval c q (ι Q v) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq => intro v; simp only [map_add, LinearMap.add_apply, hp, hq]
    | monomial n b =>
      intro v
      rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
        Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul, hpow]
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hc.minpoly_squarefree ?_
  refine LinearMap.ext fun v => ι_injective Q ?_
  rw [hint', minpoly.aeval, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

omit [Module.Finite F V] in
/-- Semisimplicity survives base change to `F̄` (characteristic `0`: squarefree polynomials stay
squarefree). -/
theorem isSemisimple_baseChange {f : Module.End F V} [Module.Finite F V]
    (hf : f.IsSemisimple) : Module.End.IsSemisimple (f.baseChange (AlgebraicClosure F)) := by
  have hsep : (minpoly F f).Separable :=
    PerfectField.separable_iff_squarefree.2 hf.minpoly_squarefree
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (hsep.map (f := algebraMap F (AlgebraicClosure F))).squarefree ?_
  rw [Polynomial.aeval_map_algebraMap]
  have : f.baseChange (AlgebraicClosure F) =
      Module.End.baseChangeHom F (AlgebraicClosure F) V f := rfl
  rw [this, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]

end Semisimple

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
