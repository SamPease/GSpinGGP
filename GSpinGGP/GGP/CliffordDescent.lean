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

end BaseChangeSub

end GSpinGGP
