/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.GSpin
import GSpinGGP.GGP.CentralizerSign
import GSpinGGP.GGP.PairBlock
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

theorem det_restrict_eq {W : Type*} [AddCommGroup W] [Module K W] {f f' : W →ₗ[K] W}
    {E E' : Submodule K W} (hf : f = f') (hE : E = E') (h : Set.MapsTo f E E)
    (h' : Set.MapsTo f' E' E') : LinearMap.det (f.restrict h) = LinearMap.det (f'.restrict h') := by
  subst hf hE; rfl

/-! ### Reflections in eigenvectors of `P(x)` at `±1` -/

/-- `E₁ ⊥ E₋₁`. -/
theorem polar_eq_zero_of_mem_eigenspace {x : GSpin Q} {u v : V}
    (hu : u ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) 1)
    (hv : v ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) (-1)) :
    QuadraticMap.polar Q u v = 0 := by
  rw [Module.End.mem_eigenspace_iff] at hu hv
  have h := polar_specP x u v
  rw [LinearEquiv.coe_coe] at hu hv
  rw [hu, hv, one_smul, neg_one_smul, QuadraticMap.polar_neg_right] at h
  have h2 : (2 : K) * QuadraticMap.polar Q u v = 0 := by linear_combination -h
  exact (mul_eq_zero.1 h2).resolve_left (Invertible.ne_zero (2 : K))

/-- The reflection in an eigenvector of `P(x)` with eigenvalue `ε = ±1` commutes with `P(x)`. -/
theorem quadReflection_comm {x : GSpin Q} {u : V} {ε : K} (hε : ε * ε = 1)
    (hu : u ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) ε) :
    (specP Q x : V →ₗ[K] V) * quadReflection Q u = quadReflection Q u * (specP Q x : V →ₗ[K] V) := by
  rw [Module.End.mem_eigenspace_iff, LinearEquiv.coe_coe] at hu
  refine LinearMap.ext fun v => ?_
  have hp : QuadraticMap.polar Q u (specP Q x v) = ε * QuadraticMap.polar Q u v := by
    have h := polar_specP x u v
    rw [hu, QuadraticMap.polar_smul_left, smul_eq_mul] at h
    calc QuadraticMap.polar Q u (specP Q x v) = (ε * ε) * QuadraticMap.polar Q u (specP Q x v) := by
          rw [hε, one_mul]
      _ = ε * QuadraticMap.polar Q u v := by rw [← h]; ring
  simp only [Module.End.mul_apply, quadReflection_apply, map_sub, map_smul, LinearEquiv.coe_coe,
    hu, hp, smul_smul]
  congr 2
  ring

/-- A product of reflections in vectors `polar`-orthogonal to `v` fixes `v`. -/
theorem list_prod_quadReflection_apply_of_polar {v : V} :
    ∀ l : List V, (∀ u ∈ l, QuadraticMap.polar Q u v = 0) →
      (l.map (quadReflection Q)).prod v = v
  | [], _ => rfl
  | u :: t, h => by
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply,
      list_prod_quadReflection_apply_of_polar t fun w hw => h w (List.mem_cons_of_mem _ hw),
      quadReflection_apply, h u List.mem_cons_self, zero_smul, smul_zero, sub_zero]

/-- A product of reflections in vectors commuting with `P(x)` (eigenvalues `±1`) commutes with
`P(x)`. -/
theorem list_prod_quadReflection_comm {x : GSpin Q} :
    ∀ l : List V, (∀ u ∈ l, u ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) 1 ∨
        u ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) (-1)) →
      Commute (specP Q x : V →ₗ[K] V) (l.map (quadReflection Q)).prod
  | [], _ => Commute.one_right _
  | u :: t, h => by
    rw [List.map_cons, List.prod_cons]
    refine Commute.mul_right ?_
      (list_prod_quadReflection_comm t fun w hw => h w (List.mem_cons_of_mem _ hw))
    rcases h u List.mem_cons_self with hu | hu
    · exact quadReflection_comm (one_mul 1) hu
    · exact quadReflection_comm (by ring) hu

/-- **Cartan–Dieudonné on a nondegenerate subspace.** An isometry `σ` of `V` preserving a
nondegenerate subspace `E` agrees on `E` with a product of reflections of `V` in anisotropic vectors
of `E`, and `det σ|_E = (-1)^{#reflections}`. -/
theorem exists_reflections_eq_on [FiniteDimensional K V] (E : Submodule K V)
    (hE : ∀ u ∈ E, (∀ w ∈ E, bform Q u w = 0) → u = 0) (σ : V ≃ₗ[K] V)
    (hσ : ∀ v, Q (σ v) = Q v) (hmaps : ∀ v ∈ E, σ v ∈ E) :
    ∃ l : List V, (∀ u ∈ l, u ∈ E ∧ Q u ≠ 0) ∧
      (∀ y ∈ E, (l.map (quadReflection Q)).prod y = σ y) ∧
      LinearMap.det ((σ : V →ₗ[K] V).restrict hmaps) = (-1) ^ l.length := by
  classical
  let Q₁ : QuadraticForm K E := Q.comp E.subtype
  have hb : ∀ u w : E, bform Q₁ u w = bform Q u w := fun u w => by
    simp [Q₁, bform, QuadraticMap.associated_comp]
  have hQ₁ : Q₁.Nondegenerate := by
    refine (isNondeg_iff_nondegenerate Q₁).1 ⟨fun u hu => ?_, fun w hw => ?_⟩
    · exact Subtype.ext (hE u u.2 fun w hw => by simpa [hb] using hu ⟨w, hw⟩)
    · refine Subtype.ext (hE w w.2 fun u hu => ?_)
      rw [bform_comm]
      simpa [hb] using hw ⟨u, hu⟩
  let f := (σ : V →ₗ[K] V).restrict hmaps
  have hinj : Function.Injective f := fun a b h =>
    Subtype.ext (σ.injective (congrArg Subtype.val h))
  let σ₁ : E ≃ₗ[K] E := LinearEquiv.ofInjectiveEndo f hinj
  have hσ₁ : σ₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q₁ := fun y => hσ y
  obtain ⟨l, hl, -, hprod⟩ :=
    TauCeti.QuadraticMap.exists_reflectionOrthogonal_list_prod_eq Q₁ hQ₁ ⟨σ₁, hσ₁⟩
  have key : ∀ l : List (TauCeti.QuadraticMap.orthogonalGroup Q₁),
      (∀ r ∈ l, ∃ (v : E) (_ : Invertible (Q₁ v)),
        TauCeti.QuadraticMap.reflectionOrthogonal Q₁ v = r) →
      ∃ m : List V, (∀ u ∈ m, u ∈ E ∧ Q u ≠ 0) ∧ m.length = l.length ∧
        (∀ y : E, (m.map (quadReflection Q)).prod (y : V) =
          (((l.prod : TauCeti.QuadraticMap.orthogonalGroup Q₁) : E ≃ₗ[K] E) y : V)) ∧
        LinearEquiv.det ((l.prod : TauCeti.QuadraticMap.orthogonalGroup Q₁) : E ≃ₗ[K] E) =
          (-1) ^ l.length := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨[], by simp, rfl, fun y => rfl, by simp⟩
    | cons r t ih =>
      intro h
      obtain ⟨v, hinv, rfl⟩ := h r List.mem_cons_self
      obtain ⟨m, hm1, hm2, hm3, hm4⟩ := ih fun r' hr' => h r' (List.mem_cons_of_mem _ hr')
      refine ⟨(v : V) :: m, ?_, by simp [hm2], fun y => ?_, ?_⟩
      · intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨v.2, (isUnit_of_invertible (Q₁ v)).ne_zero⟩
        · exact hm1 u hu
      · rw [List.map_cons, List.prod_cons, Module.End.mul_apply, hm3, List.prod_cons,
          Subgroup.coe_mul, LinearEquiv.mul_apply, TauCeti.QuadraticMap.coe_reflectionOrthogonal,
          TauCeti.QuadraticMap.reflection_apply, quadReflection_apply]
        simp only [smul_smul, invOf_eq_inv]
        rfl
      · rw [List.prod_cons, Subgroup.coe_mul, map_mul, hm4,
          TauCeti.QuadraticMap.coe_reflectionOrthogonal, TauCeti.QuadraticMap.det_reflection,
          List.length_cons, pow_succ']
  obtain ⟨m, hm1, hm2, hm3, hm4⟩ := key l hl
  refine ⟨m, hm1, fun y hy => ?_, ?_⟩
  · rw [hm3 ⟨y, hy⟩, hprod]; rfl
  · have : f = ((σ₁ : E ≃ₗ[K] E) : E →ₗ[K] E) := rfl
    rw [show (σ : V →ₗ[K] V).restrict hmaps = f from rfl, this, ← LinearEquiv.coe_det,
      show σ₁ = ((l.prod : TauCeti.QuadraticMap.orthogonalGroup Q₁) : E ≃ₗ[K] E) by rw [hprod],
      hm4, hm2]
    simp

/-- An even product of anisotropic vectors lies in `GSpin(V)` and lifts the product of the
reflections. -/
theorem exists_gspin_list_prod :
    ∀ l : List V, (∀ u ∈ l, Q u ≠ 0) → Even l.length →
      ∃ y : GSpin Q, ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = (l.map (ι Q)).prod ∧
        (specP Q y : V →ₗ[K] V) = (l.map (quadReflection Q)).prod
  | [], _, _ => ⟨1, by simp, by simp; rfl⟩
  | [_], _, h => by simp at h
  | a :: b :: t, hl, h => by
    obtain ⟨y, hy1, hy2⟩ := exists_gspin_list_prod t
      (fun u hu => hl u (by simp [hu])) (by simpa [Nat.even_add_one] using h)
    have ha := hl a (by simp)
    have hb := hl b (by simp)
    refine ⟨gspinPair Q ha hb * y, ?_, ?_⟩
    · simp only [List.map_cons, List.prod_cons, ← hy1, ← mul_assoc]
      rfl
    · simp only [List.map_cons, List.prod_cons, ← hy2, ← mul_assoc, ← specP_gspinPair Q ha hb,
        map_mul]
      rfl

/-- **Pair blocks are sign-trivial**: an element of `GSpin(V)` whose image commutes with `P(x)` and
is the identity on `E₁ ⊕ E₋₁` commutes with `x` (over an algebraically closed field).
Proved in `PairBlock.commute_of_fix`: the elements `1 + s ι(u) ι(w)` (`u ∈ E_μ`, `w ∈ E_{μ⁻¹}`)
commute with `x` and realize every invertible endomorphism of `E_μ`, so `g` agrees with a product
of them up to a scalar. -/
theorem commute_of_fix [CharZero K] [IsAlgClosed K] [FiniteDimensional K V]
    (hQ : IsNondeg Q) (x : GSpin Q) (hx : Module.End.IsSemisimple (specP Q x : V →ₗ[K] V))
    (g : GSpin Q) (hc : Commute (specP Q g) (specP Q x))
    (h1 : ∀ v ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) 1, specP Q g v = v)
    (h2 : ∀ v ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) (-1), specP Q g v = v) :
    Commute g x := by
  classical
  exact PairBlock.commute_of_fix hQ hx g hc h1 h2

/-- **The sign is `det P(g)|_{W₋₁}`**, over an algebraically closed field: for `P(g)` commuting
with a semisimple `x̄ = P(x)`, `g` commutes with `x` iff `det P(g)|_{W₋₁} = 1`. -/
theorem commute_iff_det_negFixedSub [CharZero K] [IsAlgClosed K] [FiniteDimensional K V]
    (hQ : IsNondeg Q) (x : GSpin Q) (hx : Module.End.IsSemisimple (specP Q x : V →ₗ[K] V)) (g : GSpin Q)
    (hc : Commute (specP Q g) (specP Q x)) :
    Commute g x ↔ LinearMap.det ((specP Q g : V →ₗ[K] V).restrict
      (mapsTo_eigenspace_of_commute (commute_toLinearMap hc) (-1))) = 1 := by
  classical
  have hB : (bform Q).IsSymm := ⟨fun u v => bform_comm Q u v⟩
  have hcl := commute_toLinearMap hc
  have hE1 : ∀ u ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) 1,
      (∀ w ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) 1, bform Q u w = 0) → u = 0 := by
    have h := (pairing_eigenspace hB hQ (isIsom_specP x) hx 1).2
    rwa [inv_one] at h
  have hEm : ∀ u ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) (-1),
      (∀ w ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) (-1), bform Q u w = 0) → u = 0 := by
    have h := (pairing_eigenspace hB hQ (isIsom_specP x) hx (-1)).2
    rwa [inv_neg, inv_one] at h
  -- Cartan–Dieudonné on `E₁` and on `E₋₁`
  obtain ⟨l₁, hl₁, hp₁, hd₁⟩ := exists_reflections_eq_on _ hE1 (specP Q g) (specP_isometry g)
    (mapsTo_eigenspace_of_commute hcl 1)
  obtain ⟨l₂, hl₂, hp₂, hd₂⟩ := exists_reflections_eq_on _ hEm (specP Q g) (specP_isometry g)
    (mapsTo_eigenspace_of_commute hcl (-1))
  have hdetσ := det_eq_det_one_mul_det_neg_one hB hQ (isIsom_specP x) hx (isIsom_specP g) hcl
  rw [det_specP, hd₁, hd₂, ← pow_add] at hdetσ
  have heven : Even (l₁ ++ l₂).length := by
    rw [List.length_append]
    exact (neg_one_pow_eq_one_iff_even (by norm_num)).1 hdetσ.symm
  obtain ⟨y, hy1, hy2⟩ := exists_gspin_list_prod (l₁ ++ l₂) (fun u hu => by
    rcases List.mem_append.1 hu with h | h
    exacts [(hl₁ u h).2, (hl₂ u h).2]) heven
  -- `P(y)` agrees with `P(g)` on `E₁` and `E₋₁`
  have hfix1 : ∀ v ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) 1, specP Q y v = specP Q g v := by
    intro v hv
    show (specP Q y : V →ₗ[K] V) v = _
    rw [hy2, List.map_append, List.prod_append, Module.End.mul_apply,
      list_prod_quadReflection_apply_of_polar l₂ fun u hu => by
        rw [QuadraticMap.polar_comm]; exact polar_eq_zero_of_mem_eigenspace hv (hl₂ u hu).1,
      hp₁ v hv]
  have hfix2 : ∀ v ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) (-1), specP Q y v = specP Q g v := by
    intro v hv
    show (specP Q y : V →ₗ[K] V) v = _
    rw [hy2, List.map_append, List.prod_append, Module.End.mul_apply, hp₂ v hv]
    exact list_prod_quadReflection_apply_of_polar l₁ fun u hu =>
      polar_eq_zero_of_mem_eigenspace (hl₁ u hu).1 (mapsTo_eigenspace_of_commute hcl (-1) v hv)
  have hπ : ∀ ε : K, (∀ v ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) ε, specP Q y v = specP Q g v) →
      ∀ v ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) ε, specP Q (y⁻¹ * g) v = v := by
    intro ε h v hv
    apply (specP Q y).injective
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel_left, h v hv]
  have hyx : Commute (specP Q y) (specP Q x) := by
    rw [Commute, SemiconjBy]
    apply LinearEquiv.toLinearMap_injective
    rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul, hy2]
    exact (list_prod_quadReflection_comm (l₁ ++ l₂) fun u hu => by
      rcases List.mem_append.1 hu with h | h
      exacts [Or.inl (hl₁ u h).1, Or.inr (hl₂ u h).1]).eq.symm
  have hπx : Commute (y⁻¹ * g) x := by
    refine commute_of_fix hQ x hx _ ?_ (hπ 1 hfix1) (hπ (-1) hfix2)
    rw [map_mul, map_inv]
    exact hyx.inv_left.mul_left hc
  -- the sign of `y`
  set ε : V → K := fun v => if specP Q x v = v then 1 else -1
  have hεpos : ∀ w ∈ l₁, specP Q x w = w ∧ ε w = 1 := by
    intro w hw
    have h1 := Module.End.mem_eigenspace_iff.1 (hl₁ w hw).1
    rw [LinearEquiv.coe_coe, one_smul] at h1
    exact ⟨h1, if_pos h1⟩
  have hεneg : ∀ w ∈ l₂, specP Q x w = -w ∧ ε w = -1 := by
    intro w hw
    have h1 := Module.End.mem_eigenspace_iff.1 (hl₂ w hw).1
    rw [LinearEquiv.coe_coe, neg_one_smul] at h1
    refine ⟨h1, if_neg fun he => (hl₂ w hw).2 ?_⟩
    have h2 : (2 : K) • w = 0 := by
      rw [two_smul]; nth_rewrite 1 [← he]; rw [h1, neg_add_cancel]
    rw [(smul_eq_zero.1 h2).resolve_left (Invertible.ne_zero (2 : K)), map_zero]
  have hε : ∀ w ∈ l₁ ++ l₂, specP Q x w = ε w • w := by
    intro w hw
    rcases List.mem_append.1 hw with h | h
    · rw [(hεpos w h).2, one_smul]; exact (hεpos w h).1
    · rw [(hεneg w h).2, neg_one_smul]; exact (hεneg w h).1
  have hprodε : ((l₁ ++ l₂).map ε).prod = (-1) ^ l₂.length := by
    have e1 : (l₁.map ε).prod = 1 := by
      rw [List.prod_eq_pow_length _ 1 fun a ha => ?_, one_pow]
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
      exact (hεpos w hw).2
    have e2 : (l₂.map ε).prod = (-1) ^ l₂.length := by
      rw [List.prod_eq_pow_length _ (-1) fun a ha => ?_, List.length_map]
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
      exact (hεneg w hw).2
    rw [List.map_append, List.prod_append, e1, e2, one_mul]
  have hsign := mul_prod_ι_of_specP_eq_smul x ε (l₁ ++ l₂) hε
  rw [hprodε, ← hy1] at hsign
  rw [hd₂]
  have hiff : Commute g x ↔ Commute y x := by
    constructor
    · intro h
      have : y = g * (y⁻¹ * g)⁻¹ := by group
      rw [this]; exact h.mul_left hπx.inv_left
    · intro h
      have : g = y * (y⁻¹ * g) := by group
      rw [this]; exact h.mul_left hπx
  have hcomm : Commute y x ↔ ((y * x : GSpin Q) : (CliffordAlgebra Q)ˣ).val =
      ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) :=
    ⟨fun h => congrArg (fun z : GSpin Q => ((z : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) h,
      fun h => Subtype.ext (Units.ext h)⟩
  rw [hiff, hcomm, hsign]
  constructor
  · intro h
    have := congrArg (· * ((((y * x : GSpin Q) : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q)) h
    simp only [Units.mul_inv] at this
    rw [show ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ((x : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q) = ((y * x : GSpin Q) : (CliffordAlgebra Q)ˣ).val from rfl, mul_assoc,
      Units.mul_inv, mul_one] at this
    exact algebraMap_injective Q (this.symm.trans (map_one _).symm)
  · intro h
    rw [h, map_one, one_mul]
    rfl

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
