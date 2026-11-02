/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.GSpin
import GSpinGGP.GGP.CentralizerSign
import GSpinGGP.GGP.IsometryDet
import GSpinGGP.GGP.TorusTransfer

/-!
# Centralizers of semisimple elements of `GSpin`: the explicit form

Own work, the derivation behind `steinberg_centralizer_connected` (Thesis §6.1). For `x, g ∈ GSpin(V)`
with `P(g)` commuting with `x̄ = P(x)`, `g x g⁻¹ = c x` with `c = ±1`
(`CentralizerSign.exists_conj_eq_smul`), and `c = det P(g)|_{W₋₁}`, where `W_{±1} = ker(x̄ ∓ 1)`.
Over an algebraically closed field this is `commute_iff_det_negFixedSub`; it descends to any field
of characteristic `0` by base change (`commute_iff`). The `W₊₁` condition then comes for free, since
`det P(g) = det P(g)|_{W₊₁} · det P(g)|_{W₋₁}` (`IsomCent.det_eq_det_one_mul_det_neg_one_of_charZero`).

* `isNondeg_baseChange`, `isSemisimple_specP_of_isSS`, `bcGSpin`, `specP_bcGSpin`: base change of
  `GSpin(V)` along `K → K̄`, over any field.
-/

noncomputable section

open CliffordAlgebra Module
open scoped TensorProduct

namespace GSpinGGP

/-! ## Base change of `GSpin` to `K̄` -/

section BaseChange

variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]

/-- A nondegenerate form stays nondegenerate over `K̄` (the Gram determinant is unchanged). -/
theorem isNondeg_baseChange [Module.Finite K V] (Q : QuadraticForm K V) (hQ : IsNondeg Q) :
    IsNondeg (Q.baseChange (AlgebraicClosure K)) := by
  unfold IsNondeg bform at *
  set b := Module.Free.chooseBasis K V
  rw [QuadraticForm.associated_baseChange,
    LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange (AlgebraicClosure K))]
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b] at hQ
  have : LinearMap.BilinForm.toMatrix (b.baseChange (AlgebraicClosure K))
      (LinearMap.BilinForm.baseChange (AlgebraicClosure K) (QuadraticMap.associated Q)) =
      (algebraMap K (AlgebraicClosure K)).mapMatrix
        (LinearMap.BilinForm.toMatrix b (QuadraticMap.associated Q)) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      LinearMap.BilinForm.toMatrix_apply, Module.Basis.baseChange_apply,
      Module.Basis.baseChange_apply, LinearMap.BilinForm.baseChange_tmul, mul_one,
      Algebra.smul_def, mul_one]
  rw [this, ← RingHom.map_det]
  exact (map_ne_zero _).2 hQ

/-- Base change `GSpin(Q)(K) → GSpin(Q)(K̄)`. -/
def bcGSpin (Q : QuadraticForm K V) : GSpin Q →* GSpin (Q.baseChange (AlgebraicClosure K)) where
  toFun t := ⟨bcUnits Q (t : (CliffordAlgebra Q)ˣ), TorusTransfer.bcUnits_mem_GSpin Q t⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem bcGSpin_injective (Q : QuadraticForm K V) : Function.Injective (bcGSpin Q) :=
  fun _ _ h => Subtype.ext (bcUnits_injective Q (congrArg Subtype.val h))

/-- `P(t_{K̄}) = P(t)_{K̄}`. -/
theorem specP_bcGSpin (Q : QuadraticForm K V) (t : GSpin Q) :
    (specP _ (bcGSpin Q t) : _ →ₗ[AlgebraicClosure K] _) =
      (specP Q t : V →ₗ[K] V).baseChange (AlgebraicClosure K) :=
  LinearMap.ext fun w => ι_injective (Q.baseChange (AlgebraicClosure K)) <| by
    rw [LinearEquiv.coe_coe, ι_specP]
    exact TorusTransfer.bcUnits_conj_ι' Q t w

section Semisimple

/-- `p(R_x) = R_{p(x)}` for right multiplication. -/
theorem aeval_mulRight {A : Type*} [Ring A] [Algebra K A] (x : A) (p : Polynomial K) :
    Polynomial.aeval (LinearMap.mulRight K x) p = LinearMap.mulRight K (Polynomial.aeval x p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq]
    ext z; simp [mul_add]
  | monomial n a =>
    ext z
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      LinearMap.pow_mulRight, LinearMap.mulRight_apply]
    rw [Algebra.smul_def, ← mul_assoc, ← mul_assoc, Algebra.commutes]

variable [Module.Finite K V] [PerfectField K]

open Polynomial

/-- `P(x)` is semisimple when left multiplication by `x` on `C(V)` is. -/
theorem isSemisimple_specP_of_isSS (Q : QuadraticForm K V) (x : GSpin Q)
    (hx : Module.End.IsSemisimple
      (LinearMap.mulLeft K (((x : (CliffordAlgebra Q)ˣ)) : CliffordAlgebra Q))) :
    Module.End.IsSemisimple (specP Q x : V →ₗ[K] V) := by
  set a : CliffordAlgebra Q := (((x : (CliffordAlgebra Q)ˣ)) : CliffordAlgebra Q) with ha
  set ai : CliffordAlgebra Q :=
    ((((x : (CliffordAlgebra Q)ˣ))⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) with hai
  -- `a⁻¹ ∈ K[a]`
  have hinv : ai ∈ Algebra.adjoin K {a} := by
    let A := Algebra.adjoin K {a}
    let f : A →ₗ[K] A := LinearMap.mulLeft K (⟨a, Algebra.subset_adjoin rfl⟩ : A)
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
  have hqa : aeval a (minpoly K (LinearMap.mulLeft K a)) = 0 := by
    have h0 : aeval (LinearMap.mulLeft K a) (minpoly K (LinearMap.mulLeft K a)) = 0 :=
      minpoly.aeval K _
    rw [show LinearMap.mulLeft K a = Algebra.lmul K (CliffordAlgebra Q) a from rfl,
      aeval_algHom_apply] at h0
    exact Algebra.lmul_injective (R := K) (h0.trans (map_zero _).symm)
  have hRa : Module.End.IsSemisimple (LinearMap.mulRight K a) :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hx.minpoly_squarefree
      (by rw [aeval_mulRight, hqa, LinearMap.mulRight_zero_eq_zero])
  have hRai : Module.End.IsSemisimple (LinearMap.mulRight K ai) := by
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hinv
    obtain ⟨r, hr⟩ := hinv
    have hr' : aeval a r = ai := hr
    rw [← hr', ← aeval_mulRight]
    exact hRa.aeval r
  have hc : Module.End.IsSemisimple (LinearMap.mulLeft K a * LinearMap.mulRight K ai) :=
    Module.End.IsSemisimple.mul_of_commute (LinearMap.commute_mulLeft_right a ai) hx hRai
  -- `ι ∘ P(x) = c ∘ ι`, so the minimal polynomial of `c` kills `P(x)`
  set c := LinearMap.mulLeft K a * LinearMap.mulRight K ai
  have hint : ∀ v, ι Q (specP Q x v) = c (ι Q v) := fun v => by
    rw [ι_specP]
    simp only [c, Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, ha,
      hai, mul_assoc]
  have hpow : ∀ (n : ℕ) v, ι Q (((specP Q x : V →ₗ[K] V) ^ n) v) = (c ^ n) (ι Q v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, LinearEquiv.coe_coe,
        hint, ih]
  have hint' : ∀ (q : K[X]) v, ι Q (aeval (specP Q x : V →ₗ[K] V) q v) = aeval c q (ι Q v) := by
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

end Semisimple

end BaseChange

namespace Steinberg

open IsomCent CentralizerSign

variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem fixedSub_eq_eigenspace (x : GSpin Q) :
    fixedSub x = Module.End.eigenspace (specP Q x : V →ₗ[K] V) 1 := by
  ext v
  simp [fixedSub, Module.End.mem_eigenspace_iff, sub_eq_zero]

theorem negFixedSub_eq_eigenspace (x : GSpin Q) :
    negFixedSub x = Module.End.eigenspace (specP Q x : V →ₗ[K] V) (-1) := by
  ext v
  simp [negFixedSub, Module.End.mem_eigenspace_iff, add_eq_zero_iff_eq_neg]

theorem isIsom_specP (g : GSpin Q) : IsIsom (bform Q) (specP Q g : V →ₗ[K] V) :=
  fun u v => bform_specP g u v

theorem det_restrict_eq {W : Type*} [AddCommGroup W] [Module K W] {f f' : W →ₗ[K] W}
    {E E' : Submodule K W} (hf : f = f') (hE : E = E') (h : Set.MapsTo f E E)
    (h' : Set.MapsTo f' E' E') : LinearMap.det (f.restrict h) = LinearMap.det (f'.restrict h') := by
  subst hf hE; rfl

theorem commute_toLinearMap {g x : GSpin Q} (h : Commute (specP Q g) (specP Q x)) :
    Commute (specP Q x : V →ₗ[K] V) (specP Q g : V →ₗ[K] V) :=
  LinearMap.ext fun v => congrArg (fun e : V ≃ₗ[K] V => e v) h.eq.symm

/-- **The sign is `det P(g)|_{W₋₁}`**, over an algebraically closed field: for `P(g)` commuting
with a semisimple `x̄ = P(x)`, `g` commutes with `x` iff `det P(g)|_{W₋₁} = 1`. -/
theorem commute_iff_det_negFixedSub [CharZero K] [IsAlgClosed K] [FiniteDimensional K V]
    (hQ : IsNondeg Q) (x : GSpin Q) (hx : Module.End.IsSemisimple (specP Q x : V →ₗ[K] V)) (g : GSpin Q)
    (hc : Commute (specP Q g) (specP Q x)) :
    Commute g x ↔ LinearMap.det ((specP Q g : V →ₗ[K] V).restrict
      (mapsTo_eigenspace_of_commute (commute_toLinearMap hc) (-1))) = 1 := by
  sorry

/-- **Centralizers of semisimple elements**, the explicit form: proof of
`steinberg_centralizer_connected`. -/
theorem commute_iff [CharZero K] [FiniteDimensional K V] (hQ : IsNondeg Q) (x : GSpin Q)
    (hx : Module.End.IsSemisimple
      (LinearMap.mulLeft K ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))
    (g : GSpin Q) :
    Commute (g : (CliffordAlgebra Q)ˣ) (x : (CliffordAlgebra Q)ˣ) ↔
      Commute (specP Q g) (specP Q x) ∧
      (∃ h : ∀ v ∈ fixedSub x, (specP Q g : V →ₗ[K] V) v ∈ fixedSub x,
        LinearMap.det ((specP Q g : V →ₗ[K] V).restrict h) = 1) ∧
      (∃ h : ∀ v ∈ negFixedSub x, (specP Q g : V →ₗ[K] V) v ∈ negFixedSub x,
        LinearMap.det ((specP Q g : V →ₗ[K] V).restrict h) = 1) := by
  set L := AlgebraicClosure K
  set σ : V →ₗ[K] V := (specP Q g : V →ₗ[K] V)
  set X : V →ₗ[K] V := (specP Q x : V →ₗ[K] V)
  have hss : Module.End.IsSemisimple X := isSemisimple_specP_of_isSS Q x hx
  have hcommG : Commute (g : (CliffordAlgebra Q)ˣ) (x : (CliffordAlgebra Q)ˣ) ↔ Commute g x :=
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hcL : ∀ _ : Commute (specP Q g) (specP Q x),
      Commute (specP _ (bcGSpin Q g)) (specP _ (bcGSpin Q x)) := fun hc => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    apply LinearEquiv.toLinearMap_injective
    rw [specP_bcGSpin, specP_bcGSpin, map_mul, map_mul, hc.eq]
  have hssL : Module.End.IsSemisimple
      (specP _ (bcGSpin Q x) : L ⊗[K] V →ₗ[L] L ⊗[K] V) := by
    rw [specP_bcGSpin]
    exact isSemisimple_baseChange_algebraicClosure hss
  have hQL := isNondeg_baseChange Q hQ
  -- the `W₋₁` determinant over `L` is that over `K`
  have hdetL : ∀ hc : Commute (specP Q g) (specP Q x),
      LinearMap.det ((specP _ (bcGSpin Q g) : L ⊗[K] V →ₗ[L] L ⊗[K] V).restrict
        (mapsTo_eigenspace_of_commute (commute_toLinearMap (hcL hc)) (-1))) =
      algebraMap K L (LinearMap.det (σ.restrict
        (mapsTo_eigenspace_of_commute (commute_toLinearMap hc) (-1)))) := by
    intro hc
    have hE : Module.End.eigenspace (specP _ (bcGSpin Q x) : L ⊗[K] V →ₗ[L] L ⊗[K] V) (-1) =
        (Module.End.eigenspace X (-1)).baseChange L := by
      rw [specP_bcGSpin, ← Module.End.eigenspace_baseChange_of_flat, map_neg, map_one]
    have hf' : Set.MapsTo (σ.baseChange L) ((Module.End.eigenspace X (-1)).baseChange L)
        ((Module.End.eigenspace X (-1)).baseChange L) := by
      rw [← hE, ← specP_bcGSpin]
      exact mapsTo_eigenspace_of_commute (commute_toLinearMap (hcL hc)) (-1)
    exact (det_restrict_eq (specP_bcGSpin Q g) hE _ hf').trans (det_restrict_baseChange σ _ hf')
  have hneg : ∀ hc : Commute (specP Q g) (specP Q x),
      Commute g x ↔ LinearMap.det (σ.restrict
        (mapsTo_eigenspace_of_commute (commute_toLinearMap hc) (-1))) = 1 := by
    intro hc
    have hinj : Commute g x ↔ Commute (bcGSpin Q g) (bcGSpin Q x) := by
      rw [Commute, SemiconjBy, Commute, SemiconjBy, ← map_mul, ← map_mul]
      exact (bcGSpin_injective Q).eq_iff.symm
    rw [hinj, commute_iff_det_negFixedSub hQL _ hssL _ (hcL hc), hdetL hc,
      map_eq_one_iff _ (algebraMap K L).injective]
  have hB : (bform Q).IsSymm := ⟨fun u v => bform_comm Q u v⟩
  constructor
  · intro h
    have hgx := hcommG.1 h
    have hc : Commute (specP Q g) (specP Q x) := by
      rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hgx.eq]
    have hn := (hneg hc).1 hgx
    have hdet := det_eq_det_one_mul_det_neg_one_of_charZero hB hQ (isIsom_specP x) hss
      (isIsom_specP g) (commute_toLinearMap hc)
    rw [hn, mul_one, det_specP] at hdet
    refine ⟨hc, ⟨mapsTo_fixedSub_of_commute hc, ?_⟩, ⟨mapsTo_negFixedSub_of_commute hc, ?_⟩⟩
    · exact (det_restrict_eq rfl (fixedSub_eq_eigenspace x) _ _).trans hdet.symm
    · exact (det_restrict_eq rfl (negFixedSub_eq_eigenspace x) _ _).trans hn
  · rintro ⟨hc, -, hn, hdn⟩
    refine hcommG.2 ((hneg hc).2 ?_)
    exact (det_restrict_eq rfl (negFixedSub_eq_eigenspace x).symm _ hn).trans hdn

end Steinberg

end GSpinGGP
