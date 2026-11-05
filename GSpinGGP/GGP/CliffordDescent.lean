/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.PAdicQuadraticForms
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

end GSpinGGP
