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

/-- **The lift commutes with `g`** when `P(g)` commutes with `Y`: `g Ŷ g⁻¹ − Ŷ` is even and commutes
with `ι(V)`, hence a scalar, and it is traceless. -/
theorem commute_of_lift (hQ : IsNondeg Q) (g : GSpin Q) {Y : Module.End K V}
    (hYc : Commute (specP Q g : V →ₗ[K] V) Y) {Yh : CliffordAlgebra Q} (hYh0 : Yh ∈ gspin Q)
    (hYh : ∀ v, Yh * ι Q v - ι Q v * Yh = ι Q (Y v)) :
    ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * Yh =
      Yh * ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  set a : CliffordAlgebra Q := ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  set b : CliffordAlgebra Q :=
    (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  have hba : b * a = 1 := Units.inv_mul _
  have hab : a * b = 1 := Units.mul_inv _
  have hb0 : b ∈ even Q := (g⁻¹ : GSpin Q).2.1
  set D := a * Yh * b - Yh with hD
  have hDc : ∀ v, ι Q v * D = D * ι Q v := by
    intro v
    set u := specP Q g⁻¹ v
    have hv : ι Q v = a * ι Q u * b := by
      rw [← ι_specP, specP_inv_apply_apply]
    have hYv : Y v = specP Q g (Y u) := by
      have := LinearMap.congr_fun hYc.eq u
      simp only [Module.End.mul_apply, LinearEquiv.coe_coe] at this
      rw [this, specP_inv_apply_apply]
    have e1 : a * Yh * b * (a * ι Q u * b) = a * (Yh * ι Q u) * b := by
      simp only [mul_assoc]; rw [← mul_assoc b a, hba, one_mul]
    have e2 : a * ι Q u * b * (a * Yh * b) = a * (ι Q u * Yh) * b := by
      simp only [mul_assoc]; rw [← mul_assoc b a, hba, one_mul]
    have h1 : a * Yh * b * ι Q v - ι Q v * (a * Yh * b) = ι Q (Y v) := by
      rw [hv, e1, e2, ← sub_mul, ← mul_sub, hYh, hYv, ι_specP]
    have h2 := hYh v
    rw [hD, mul_sub, sub_mul]
    rw [← sub_eq_zero]
    rw [show ι Q v * (a * Yh * b) - ι Q v * Yh - (a * Yh * b * ι Q v - Yh * ι Q v) =
      (Yh * ι Q v - ι Q v * Yh) - (a * Yh * b * ι Q v - ι Q v * (a * Yh * b)) by abel, h1, h2,
      sub_self]
  have hD0 : D ∈ evenOdd Q 0 := by
    rw [← even_toSubmodule]
    exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ g.2.1 hYh0.1) hb0)
      hYh0.1
  obtain ⟨r, hr⟩ := eq_algebraMap_of_commute_ι hQ hD0 hDc
  have htr : cliffTrace Q D = 0 := by
    rw [hD, sub_eq_add_neg, cliffTrace_add,
      show cliffTrace Q (a * Yh * b) = cliffTrace Q (b * (a * Yh)) from trace_mulLeft_comm Q _ _,
      ← mul_assoc, hba, one_mul, ← neg_one_smul K Yh, cliffTrace_smul]
    ring
  have hr0 : r = 0 := by
    rw [hr, Algebra.algebraMap_eq_smul_one, cliffTrace_smul, cliffTrace_one] at htr
    exact (mul_eq_zero.mp htr).resolve_right (cast_finrank_cliffordAlgebra_ne_zero Q)
  have hD' : a * Yh * b = Yh := by
    rw [← sub_eq_zero, ← hD, hr, hr0, map_zero]
  calc a * Yh = a * Yh * b * a := by rw [mul_assoc _ b, hba, mul_one]
    _ = Yh * a := by rw [hD']

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
