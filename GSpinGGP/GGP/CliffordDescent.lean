/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.PAdicQuadraticForms
import GSpinGGP.GGP.Hilbert90Units
import GSpinGGP.GGP.GaloisTorus
import TauCeti.NumberTheory.LocalField.QuadraticForm.Witt
import TauCeti.LinearAlgebra.CliffordAlgebra.CentralSimple.Even

/-!
# Quadratic forms with isomorphic Clifford algebras

Over a `p`-adic field, two nondegenerate forms of the same dimension and discriminant are
isometric as soon as their Clifford algebras (even dimension), or their even Clifford algebras
(odd dimension), are isomorphic: they then have the same Clifford invariant, and Tau Ceti classifies
regular forms over a nonarchimedean local field by rank, signed discriminant and Clifford invariant
(`TauCeti.RegularFormClass.eq_iff_rank_eq_and_signedDiscr_eq_and_cliffordInvariant_eq`).
-/

noncomputable section

open TauCeti QuadraticMap Module
open scoped TensorProduct

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **Isomorphic Clifford algebras give isometric forms** (`p`-adic, same dimension and
discriminant): in even dimension `C(Q₁) ≅ C(Q₂)`, in odd dimension `C⁺(Q₁) ≅ C⁺(Q₂)`. -/
theorem nonempty_isometryEquiv_of_cliffordAlgEquiv {m : ℕ} {Q₁ Q₂ : QuadraticForm F (Fin m → F)}
    (h₁ : IsNondeg Q₁) (h₂ : IsNondeg Q₂) (hd : SameDisc Q₁ Q₂)
    (hc : (Even m ∧ Nonempty (CliffordAlgebra Q₁ ≃ₐ[F] CliffordAlgebra Q₂)) ∨
      (Odd m ∧ Nonempty (CliffordAlgebra.even Q₁ ≃ₐ[F] CliffordAlgebra.even Q₂))) :
    Nonempty (Q₁.IsometryEquiv Q₂) := by
  let := normValuativeRel F
  have := NormValuativeRel.isNonarchimedeanLocalField F
  have hn₁ := (isNondeg_iff_nondegenerate Q₁).1 h₁
  have hn₂ := (isNondeg_iff_nondegenerate Q₂).1 h₂
  have hrank : (formClass Q₁ hn₁).rank = (formClass Q₂ hn₂).rank := by
    rw [rank_formClass, rank_formClass]
  have hdisc := (PAdicQuadAux.sameDisc_iff Q₁ Q₂ h₁ h₂).1 hd
  have hsd : RegularFormClass.signedDiscr (formClass Q₁ hn₁) =
      RegularFormClass.signedDiscr (formClass Q₂ hn₂) := by
    rw [RegularFormClass.signedDiscr_eq_sign_add_discr,
      RegularFormClass.signedDiscr_eq_sign_add_discr, hrank, hdisc]
  have hcl : RegularFormClass.cliffordInvariant (formClass Q₁ hn₁) =
      RegularFormClass.cliffordInvariant (formClass Q₂ hn₂) := by
    rcases hc with ⟨hm, ⟨e⟩⟩ | ⟨hm, ⟨e⟩⟩
    · have hm' : Even (finrank F (Fin m → F)) := by rwa [finrank_fin_fun]
      have := CliffordAlgebra.isCentral_of_even_finrank hn₂ hm'
      have := CliffordAlgebra.isSimpleRing_of_even_finrank hn₂ hm'
      let A : CSA F := ⟨AlgCat.of F (CliffordAlgebra Q₂)⟩
      rw [RegularFormClass.cliffordInvariant_formClass_of_even Q₁ hn₁ hm' A e,
        RegularFormClass.cliffordInvariant_formClass_of_even Q₂ hn₂ hm' A AlgEquiv.refl]
    · have hm' : Odd (finrank F (Fin m → F)) := by rwa [finrank_fin_fun]
      have := CliffordAlgebra.isCentral_even_of_odd_finrank hn₂ hm'
      have := CliffordAlgebra.isSimpleRing_even_of_odd_finrank hn₂ hm'
      let A : CSA F := ⟨AlgCat.of F (CliffordAlgebra.even Q₂)⟩
      rw [RegularFormClass.cliffordInvariant_formClass_of_odd Q₁ hn₁ hm' A e,
        RegularFormClass.cliffordInvariant_formClass_of_odd Q₂ hn₂ hm' A AlgEquiv.refl]
  have heq : formClass Q₁ hn₁ = formClass Q₂ hn₂ :=
    RegularFormClass.eq_iff_rank_eq_and_signedDiscr_eq_and_cliffordInvariant_eq.2
      ⟨hrank, hsd, hcl⟩
  exact (formClass_eq_iff Q₁ hn₁ Q₂ hn₂).1 heq

section BaseChangeSub

variable {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)

set_option hygiene false in
local notation "Kb" => AlgebraicClosure F

/-- The `F̄`-span `F̄ ⊗ C ⊆ C(Q_{F̄})` of a subalgebra `C` of `C(Q)`. -/
def bcSub (C : Subalgebra F (CliffordAlgebra Q)) :
    Subalgebra Kb (CliffordAlgebra (Q.baseChange Kb)) :=
  (C.baseChange Kb).map (CliffordAlgebra.ofBaseChange Kb Q)

/-- `F̄ ⊗ C → C(Q_{F̄})`. -/
def bcSubHom (C : Subalgebra F (CliffordAlgebra Q)) :
    Kb ⊗[F] C →ₐ[Kb] CliffordAlgebra (Q.baseChange Kb) :=
  (CliffordAlgebra.ofBaseChange Kb Q).comp (Algebra.TensorProduct.map (AlgHom.id Kb Kb) C.val)

theorem bcSubHom_injective (C : Subalgebra F (CliffordAlgebra Q)) :
    Function.Injective (bcSubHom Q C) := by
  have h1 : Function.Injective (CliffordAlgebra.ofBaseChange Kb Q) :=
    (CliffordAlgebra.equivBaseChange Kb Q).symm.injective
  have h2 : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id Kb Kb) C.val : Kb ⊗[F] C → _) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := Kb) C.val.toLinearMap
      Subtype.val_injective
  exact h1.comp h2

theorem range_bcSubHom (C : Subalgebra F (CliffordAlgebra Q)) :
    (bcSubHom Q C).range = bcSub Q C := by
  rw [bcSubHom, AlgHom.range_comp, bcSub, Subalgebra.baseChange]

/-- The basis `1 ⊗ bᵢ` of `F̄ ⊗ C`, inside `C(Q_{F̄})`. -/
def bcSubBasis (C : Subalgebra F (CliffordAlgebra Q)) {ι : Type*} (b : Module.Basis ι F C) :
    Module.Basis ι Kb (bcSub Q C) :=
  ((Algebra.TensorProduct.basis Kb b).map
    (AlgEquiv.ofInjective _ (bcSubHom_injective Q C)).toLinearEquiv).map
    (Subalgebra.equivOfEq _ _ (range_bcSubHom Q C)).toLinearEquiv

theorem coe_bcSubBasis (C : Subalgebra F (CliffordAlgebra Q)) {ι : Type*}
    (b : Module.Basis ι F C) (i : ι) : (bcSubBasis Q C b i : CliffordAlgebra (Q.baseChange Kb)) =
      bcHom Q (b i : CliffordAlgebra Q) := by
  rw [bcSubBasis, Module.Basis.map_apply, Module.Basis.map_apply]
  change ((AlgEquiv.ofInjective _ (bcSubHom_injective Q C)
    ((Algebra.TensorProduct.basis Kb b) i) : _) : CliffordAlgebra (Q.baseChange Kb)) = _
  rw [AlgEquiv.ofInjective_apply, Algebra.TensorProduct.basis_apply]
  rfl

/-- `σ` preserves `F̄ ⊗ C`. -/
theorem galC_mem_bcSub (C : Subalgebra F (CliffordAlgebra Q)) (σ : GalF F)
    {z : CliffordAlgebra (Q.baseChange Kb)} (hz : z ∈ bcSub Q C) : galC Q σ z ∈ bcSub Q C := by
  obtain ⟨y, ⟨t, rfl⟩, rfl⟩ := hz
  refine ⟨_, ⟨Algebra.TensorProduct.map (σ : Kb →ₐ[F] Kb) (AlgHom.id F C) t, rfl⟩, ?_⟩
  simp only [galC, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    CliffordAlgebra.toBaseChange_ofBaseChange]
  congr 1
  induction t using TensorProduct.inductionOn with
  | tmul k c => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The Galois action `galC` on `F̄ ⊗ C`. -/
def bcSubAction (C : Subalgebra F (CliffordAlgebra Q)) {N : ℕ} (b : Module.Basis (Fin N) F C) :
    GalAlgAction F (bcSub Q C) (bcSubBasis Q C b) where
  act σ := (galC Q σ).restrict (bcSub Q C) (bcSub Q C) fun _ hz => galC_mem_bcSub Q C σ hz
  act_mul σ τ z := Subtype.ext (galC_galC Q σ τ z).symm
  act_smul σ c z := Subtype.ext (by
    change galC Q σ (c • (z : CliffordAlgebra (Q.baseChange Kb))) = σ c • galC Q σ z
    rw [Algebra.smul_def, map_mul, galC_algebraMap, ← Algebra.smul_def])
  act_basis σ i := Subtype.ext (by
    change galC Q σ (bcSubBasis Q C b i : CliffordAlgebra (Q.baseChange Kb)) = _
    rw [coe_bcSubBasis, galC_bcHom])

/-- `C → F̄ ⊗ C`, `c ↦ 1 ⊗ c`. -/
def bcSubIncl (C : Subalgebra F (CliffordAlgebra Q)) : C →ₐ[F] bcSub Q C :=
  (((bcSubHom Q C).restrictScalars F).comp Algebra.TensorProduct.includeRight).codRestrict
    ((bcSub Q C).restrictScalars F) fun c => by
      rw [← range_bcSubHom]; exact ⟨(1 : Kb) ⊗ₜ c, rfl⟩

theorem coe_bcSubIncl (C : Subalgebra F (CliffordAlgebra Q)) (c : C) :
    (bcSubIncl Q C c : CliffordAlgebra (Q.baseChange Kb)) = bcHom Q (c : CliffordAlgebra Q) :=
  rfl

theorem bcHom_smul (f : F) (x : CliffordAlgebra Q) : bcHom Q (f • x) = f • bcHom Q x := by
  rw [Algebra.smul_def, map_mul, bcHom_algebraMap, Algebra.smul_def,
    IsScalarTower.algebraMap_apply F Kb (CliffordAlgebra (Q.baseChange Kb))]

/-- **Descent**: a Galois-fixed element of `F̄ ⊗ C` lies in `C`. -/
theorem exists_bcHom_of_mem_bcSub (C : Subalgebra F (CliffordAlgebra Q)) {N : ℕ}
    (b : Module.Basis (Fin N) F C) {z : CliffordAlgebra (Q.baseChange Kb)} (hz : z ∈ bcSub Q C)
    (hfix : ∀ σ : GalF F, galC Q σ z = z) : ∃ c ∈ C, bcHom Q c = z := by
  set e := bcSubBasis Q C b
  have hrat : ∀ i, ∃ f : F, algebraMap F Kb f = e.repr ⟨z, hz⟩ i := fun i =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 fun σ => by
      rw [← (bcSubAction Q C b).repr_act]
      congr 2
      exact Subtype.ext (hfix σ)
  choose f hf using hrat
  refine ⟨(∑ i, f i • b i : C), (∑ i, f i • b i : C).2, ?_⟩
  have hz' : (⟨z, hz⟩ : bcSub Q C) = ∑ i, e.repr ⟨z, hz⟩ i • e i := (e.sum_repr _).symm
  have := congrArg (bcSub Q C).val hz'
  rw [map_sum] at this
  change z = _ at this
  rw [this, show ((∑ i, f i • b i : C) : CliffordAlgebra Q) = C.val (∑ i, f i • b i) from rfl,
    map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul C.val, bcHom_smul, map_smul (bcSub Q C).val, ← hf, algebraMap_smul]
  exact congrArg _ (coe_bcSubBasis Q C b i).symm

end BaseChangeSub

section Descent

set_option hygiene false in
local notation "Kb" => AlgebraicClosure F

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
  {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}

/-- **An inner twist split by Hilbert 90 descends.** Let `Θ : C(Q₁)_{F̄} ≅ C(Q₂)_{F̄}` carry
`F̄ ⊗ C₁` onto `F̄ ⊗ C₂` and satisfy `σ(Θ z) = Θ(v_σ σ(z) v_σ⁻¹)` for a continuous cocycle `v` in
`(F̄ ⊗ C₁)ˣ`, with `C₁` simple. Then `C₁ ≅ C₂` over `F`: with `v_σ = u⁻¹ σ(u)` (Hilbert 90,
`exists_units_eq_inv_mul_act`), `z ↦ Θ(u⁻¹ z u)` is Galois-equivariant. -/
theorem nonempty_algEquiv_of_twist (C₁ : Subalgebra F (CliffordAlgebra Q₁))
    (C₂ : Subalgebra F (CliffordAlgebra Q₂)) [IsSimpleRing C₁] [IsArtinianRing C₁] {N₁ N₂ : ℕ}
    (b₁ : Module.Basis (Fin N₁) F C₁) (b₂ : Module.Basis (Fin N₂) F C₂)
    (Θ : CliffordAlgebra (Q₁.baseChange Kb) ≃ₐ[Kb] CliffordAlgebra (Q₂.baseChange Kb))
    (hΘ₁ : ∀ y ∈ bcSub Q₁ C₁, Θ y ∈ bcSub Q₂ C₂) (hΘ₂ : ∀ y ∈ bcSub Q₂ C₂, Θ.symm y ∈ bcSub Q₁ C₁)
    (v : GalF F → (bcSub Q₁ C₁)ˣ) (hv : ∃ E : IntermediateField F Kb, FiniteDimensional F E ∧
      ∀ σ τ : GalF F, (∀ x ∈ E, σ x = τ x) → v σ = v τ)
    (hcoc : ∀ σ τ, (v (σ * τ) : CliffordAlgebra (Q₁.baseChange Kb)) =
      (v σ : CliffordAlgebra (Q₁.baseChange Kb)) * galC Q₁ σ (v τ : CliffordAlgebra _))
    (hΘv : ∀ σ z, galC Q₂ σ (Θ z) = Θ ((v σ : CliffordAlgebra (Q₁.baseChange Kb)) *
      galC Q₁ σ z * (((v σ)⁻¹ : (bcSub Q₁ C₁)ˣ) : CliffordAlgebra (Q₁.baseChange Kb)))) :
    Nonempty (C₁ ≃ₐ[F] C₂) := by
  classical
  obtain ⟨u, hu⟩ := exists_units_eq_inv_mul_act (bcSubAction Q₁ C₁ b₁) (bcSubIncl Q₁ C₁) b₁
    (fun i => Subtype.ext (by rw [coe_bcSubIncl, coe_bcSubBasis])) v hv
    (fun σ τ => Subtype.ext (hcoc σ τ))
  set U : CliffordAlgebra (Q₁.baseChange Kb) := ((u : bcSub Q₁ C₁) : CliffordAlgebra (Q₁.baseChange Kb))
  set Ui : CliffordAlgebra (Q₁.baseChange Kb) := (((u⁻¹ : (bcSub Q₁ C₁)ˣ) : bcSub Q₁ C₁) :
    CliffordAlgebra (Q₁.baseChange Kb))
  have hUUi : U * Ui = 1 := congrArg Subtype.val u.mul_inv
  have hUiU : Ui * U = 1 := congrArg Subtype.val u.inv_mul
  have hv' : ∀ σ, (v σ : CliffordAlgebra (Q₁.baseChange Kb)) = Ui * galC Q₁ σ U := fun σ =>
    congrArg Subtype.val (hu σ)
  have hgU : ∀ σ, galC Q₁ σ U * galC Q₁ σ Ui = 1 := fun σ => by rw [← map_mul, hUUi, map_one]
  have hgUi : ∀ σ, galC Q₁ σ Ui * galC Q₁ σ U = 1 := fun σ => by rw [← map_mul, hUiU, map_one]
  have hvinv : ∀ σ, (((v σ)⁻¹ : (bcSub Q₁ C₁)ˣ) : CliffordAlgebra (Q₁.baseChange Kb)) =
      galC Q₁ σ Ui * U := fun σ => by
    have h1 : (v σ : CliffordAlgebra (Q₁.baseChange Kb)) *
        (((v σ)⁻¹ : (bcSub Q₁ C₁)ˣ) : CliffordAlgebra (Q₁.baseChange Kb)) = 1 :=
      congrArg Subtype.val (v σ).mul_inv
    calc (((v σ)⁻¹ : (bcSub Q₁ C₁)ˣ) : CliffordAlgebra (Q₁.baseChange Kb))
        = (galC Q₁ σ Ui * U * (v σ : CliffordAlgebra (Q₁.baseChange Kb))) *
            (((v σ)⁻¹ : (bcSub Q₁ C₁)ˣ) : CliffordAlgebra (Q₁.baseChange Kb)) := by
          rw [hv', show galC Q₁ σ Ui * U * (Ui * galC Q₁ σ U) = 1 by
            rw [mul_assoc, ← mul_assoc U, hUUi, one_mul, hgUi], one_mul]
      _ = galC Q₁ σ Ui * U := by rw [mul_assoc, h1, mul_one]
  -- `Φ z = Θ(u⁻¹ z u)` is Galois-equivariant
  let Φ : CliffordAlgebra (Q₁.baseChange Kb) → CliffordAlgebra (Q₂.baseChange Kb) :=
    fun z => Θ (Ui * z * U)
  have hΦ : ∀ σ z, galC Q₂ σ (Φ z) = Φ (galC Q₁ σ z) := fun σ z => by
    simp only [Φ]
    rw [hΘv, hv', hvinv, map_mul (galC Q₁ σ), map_mul (galC Q₁ σ)]
    congr 1
    calc Ui * galC Q₁ σ U * (galC Q₁ σ Ui * galC Q₁ σ z * galC Q₁ σ U) * (galC Q₁ σ Ui * U)
        = Ui * (galC Q₁ σ U * galC Q₁ σ Ui) * galC Q₁ σ z *
            (galC Q₁ σ U * galC Q₁ σ Ui) * U := by noncomm_ring
      _ = Ui * galC Q₁ σ z * U := by rw [hgU, mul_one, mul_one]
  have hΦmul : ∀ x y, Φ (x * y) = Φ x * Φ y := fun x y => by
    simp only [Φ, ← map_mul]
    congr 1
    calc Ui * (x * y) * U = Ui * x * (U * Ui) * y * U := by rw [hUUi, mul_one]; noncomm_ring
      _ = Ui * x * U * (Ui * y * U) := by noncomm_ring
  have hΦinj : Function.Injective Φ := fun x y h => by
    have h' := Θ.injective h
    calc x = U * (Ui * x * U) * Ui := by
          rw [← mul_assoc, ← mul_assoc, hUUi, one_mul, mul_assoc, hUUi, mul_one]
      _ = U * (Ui * y * U) * Ui := by rw [h']
      _ = y := by rw [← mul_assoc, ← mul_assoc, hUUi, one_mul, mul_assoc, hUUi, mul_one]
  have hUmem : U ∈ bcSub Q₁ C₁ := (u : bcSub Q₁ C₁).2
  have hUimem : Ui ∈ bcSub Q₁ C₁ := ((u⁻¹ : (bcSub Q₁ C₁)ˣ) : bcSub Q₁ C₁).2
  have hbc : ∀ c : C₁, bcHom Q₁ (c : CliffordAlgebra Q₁) ∈ bcSub Q₁ C₁ := fun c =>
    (bcSubIncl Q₁ C₁ c).2
  -- the image of `C₁` lies in `C₂`
  have hex : ∀ c : C₁, ∃ c' ∈ C₂, bcHom Q₂ c' = Φ (bcHom Q₁ (c : CliffordAlgebra Q₁)) :=
    fun c => exists_bcHom_of_mem_bcSub Q₂ C₂ b₂
      (hΘ₁ _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hUimem (hbc c)) hUmem))
      (fun σ => by rw [hΦ, galC_bcHom])
  choose g hgC hg using hex
  have hcoe : ∀ c d : C₁, ((c * d : C₁) : CliffordAlgebra Q₁) = c * d := fun _ _ => rfl
  have hscal : ∀ k : Kb, Φ (algebraMap Kb _ k) = algebraMap Kb _ k := fun k => by
    simp only [Φ]
    rw [← Algebra.commutes, mul_assoc, hUiU, mul_one, AlgEquiv.commutes]
  let f : C₁ →ₐ[F] C₂ :=
    { toFun := fun c => ⟨g c, hgC c⟩
      map_one' := Subtype.ext (bcHom_injective Q₂ (by
        rw [hg, OneMemClass.coe_one, map_one, show (1 : CliffordAlgebra (Q₁.baseChange Kb)) =
          algebraMap Kb _ 1 from (map_one _).symm, hscal, map_one, OneMemClass.coe_one,
          map_one]))
      map_mul' := fun c d => Subtype.ext (bcHom_injective Q₂ (by
        change bcHom Q₂ (g (c * d)) = bcHom Q₂ (g c * g d)
        rw [map_mul, hg, hg, hg, hcoe, map_mul, hΦmul]))
      map_zero' := Subtype.ext (bcHom_injective Q₂ (by
        change bcHom Q₂ (g 0) = bcHom Q₂ 0
        rw [hg]; simp [Φ]))
      map_add' := fun c d => Subtype.ext (bcHom_injective Q₂ (by
        change bcHom Q₂ (g (c + d)) = bcHom Q₂ (g c + g d)
        rw [map_add, hg, hg, hg]; simp [Φ, mul_add, add_mul]))
      commutes' := fun r => Subtype.ext (bcHom_injective Q₂ (by
        change bcHom Q₂ (g (algebraMap F C₁ r)) = bcHom Q₂ (algebraMap F (CliffordAlgebra Q₂) r)
        rw [hg, show ((algebraMap F C₁ r : C₁) : CliffordAlgebra Q₁) =
          algebraMap F (CliffordAlgebra Q₁) r from rfl, bcHom_algebraMap, bcHom_algebraMap,
          hscal])) }
  refine ⟨AlgEquiv.ofBijective f ⟨fun c d h => ?_, fun c' => ?_⟩⟩
  · have h1 : bcHom Q₂ (g c) = bcHom Q₂ (g d) := congrArg (fun x : C₂ => bcHom Q₂ x) h
    rw [hg, hg] at h1
    exact Subtype.ext (bcHom_injective Q₁ (hΦinj h1))
  · set y := U * Θ.symm (bcHom Q₂ (c' : CliffordAlgebra Q₂)) * Ui
    have hΦy : Φ y = bcHom Q₂ (c' : CliffordAlgebra Q₂) := by
      simp only [Φ, y]
      rw [show Ui * (U * Θ.symm (bcHom Q₂ ↑c') * Ui) * U = Θ.symm (bcHom Q₂ ↑c') by
        rw [← mul_assoc, ← mul_assoc, hUiU, one_mul, mul_assoc, hUiU, mul_one],
        AlgEquiv.apply_symm_apply]
    have hymem : y ∈ bcSub Q₁ C₁ :=
      Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hUmem
        (hΘ₂ _ (bcSubIncl Q₂ C₂ c').2)) hUimem
    obtain ⟨c, hc, hcy⟩ := exists_bcHom_of_mem_bcSub Q₁ C₁ b₁ hymem fun σ => hΦinj (by
      rw [← hΦ, hΦy, galC_bcHom])
    refine ⟨⟨c, hc⟩, Subtype.ext (bcHom_injective Q₂ ?_)⟩
    change bcHom Q₂ (g ⟨c, hc⟩) = _
    rw [hg]
    change Φ (bcHom Q₁ c) = _
    rw [hcy, hΦy]

end Descent

end GSpinGGP
