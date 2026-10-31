import GSpinGGP.Foundations.QuadraticForms
import GSpinGGP.Foundations.LocalFieldBridge
import TauCeti.NumberTheory.LocalField.QuadraticForm.Classification
import TauCeti.NumberTheory.LocalField.QuadraticForm.Realization

/-!
# Quadratic forms over a `p`-adic field with a given discriminant

`padic_quadratic_classes`: for a nondegenerate `Q` on `F^m`, the nondegenerate forms on `F^m`
with the same discriminant fall into `n ≤ 2` isometry classes, with `n = 2` for `m ≥ 3`, `n = 1`
for `m ≤ 1`, and, for `m = 2`, `n = 1` exactly when `-det Q` is a square (Lam, *Introduction to
Quadratic Forms over Fields*, Ch. VI §2; O'Meara, *Introduction to Quadratic Forms*, §63).

Derived from Tau Ceti's classification of regular forms over a nonarchimedean local field by
rank, discriminant and Hasse invariant
(`QuadraticForm.equivalent_iff_finrank_eq_and_discr_eq_and_localHasse_eq`), and its list of the
realizable invariants (`TauCeti.RegularFormClass.exists_rank_eq_discr_eq_localHasse_eq_iff`),
through `NormValuativeRel.isNonarchimedeanLocalField`.
-/

noncomputable section

open TauCeti QuadraticMap

namespace GSpinGGP

namespace PAdicQuadAux

variable {F : Type*} [Field F] [Invertible (2 : F)]

theorem isNondeg_iff_discr'_ne_zero {m : ℕ} (q : QuadraticForm F (Fin m → F)) :
    IsNondeg q ↔ q.discr' ≠ 0 := by
  rw [IsNondeg, LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (Pi.basisFun F (Fin m)),
    LinearMap.BilinForm.toMatrix_basisFun]
  rfl

/-- The discriminant of the class of a nondegenerate form on `F^m` is the square class of its
Gram determinant. -/
theorem discr_formClass_eq {m : ℕ} (q : QuadraticForm F (Fin m → F)) (hq : IsNondeg q) :
    RegularFormClass.discr (formClass q ((isNondeg_iff_nondegenerate q).1 hq)) =
      squareClass (Units.mk0 q.discr' ((isNondeg_iff_discr'_ne_zero q).1 hq)) :=
  discr_formClass_eq_squareClass q _ (Pi.basisFun F (Fin m))
    (by rw [Units.val_mk0, QuadraticForm.discr_eq_discr'])

/-- `SameDisc` is equality of discriminants of classes. -/
theorem sameDisc_iff {m : ℕ} (q q' : QuadraticForm F (Fin m → F)) (hq : IsNondeg q)
    (hq' : IsNondeg q') :
    SameDisc q q' ↔
      RegularFormClass.discr (formClass q ((isNondeg_iff_nondegenerate q).1 hq)) =
        RegularFormClass.discr (formClass q' ((isNondeg_iff_nondegenerate q').1 hq')) := by
  have h₀ := (isNondeg_iff_discr'_ne_zero q).1 hq
  have h₁ := (isNondeg_iff_discr'_ne_zero q').1 hq'
  rw [discr_formClass_eq q hq, discr_formClass_eq q' hq', squareClass_eq_iff_isSquare_mul]
  constructor
  · rintro ⟨c, hc, hcd⟩
    refine ⟨Units.mk0 (c * q.discr') (mul_ne_zero hc h₀), Units.ext ?_⟩
    simp only [Units.val_mul, Units.val_mk0, hcd]
    ring
  · rintro ⟨r, hr⟩
    have hr' : q.discr' * q'.discr' = (r : F) * r := by simpa using congrArg Units.val hr
    refine ⟨(r : F) / q.discr', div_ne_zero r.ne_zero h₀, ?_⟩
    field_simp
    linear_combination hr'

/-- A form on `F^m` realizing a given class of rank `m`. -/
theorem exists_form_of_rank_eq {m : ℕ} (x : RegularFormClass F) (hx : x.rank = m) :
    ∃ (q : QuadraticForm F (Fin m → F)) (hq : IsNondeg q),
      formClass q ((isNondeg_iff_nondegenerate q).1 hq) = x := by
  obtain ⟨p, rfl⟩ := Quotient.exists_rep x
  have hpm : p.1 = m := by rw [← hx]; rfl
  let L : (Fin m → F) ≃ₗ[F] (Fin p.1 → F) := LinearEquiv.funCongrLeft F F (finCongr hpm)
  let q : QuadraticForm F (Fin m → F) := (presentedForm p).comp L.toLinearMap
  let e : q.IsometryEquiv (presentedForm p) := { L with map_app' := fun _ => rfl }
  have hq' : q.Nondegenerate := e.nondegenerate_iff.2 (nondegenerate_presentedForm p)
  have hq : IsNondeg q := (isNondeg_iff_nondegenerate q).2 hq'
  exact ⟨q, hq, formClass_mk q _ p ⟨e⟩⟩

theorem units_ne_neg (s : ℤˣ) : -s ≠ s := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> decide

theorem units_eq_or_eq_neg (s t : ℤˣ) : t = s ∨ t = -s := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;>
    simp

end PAdicQuadAux

open PAdicQuadAux

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- **Classification of quadratic forms over a `p`-adic field with a given discriminant**
(Lam, Ch. VI §2; O'Meara §63). For a nondegenerate `Q` on `F^m`, a system of representatives
`R : Fin n → _` of the isometry classes of nondegenerate forms on `F^m` with the discriminant of
`Q`, containing `Q` at `i₀`; `n = 2` if `m ≥ 3`, `n = 1` if `m ≤ 1`, and for `m = 2`, `n = 1`
iff `-det Q` is a square. `discr'` is the Gram determinant (Mathlib `QuadraticForm.discr'`). -/
theorem padic_quadratic_classes {m : ℕ} (Q : QuadraticForm F (Fin m → F)) (hQ : IsNondeg Q) :
    ∃ (n : ℕ) (R : Fin n → QuadraticForm F (Fin m → F)) (i₀ : Fin n),
      R i₀ = Q ∧ (∀ i, IsNondeg (R i) ∧ SameDisc Q (R i)) ∧
      (∀ Q' : QuadraticForm F (Fin m → F), IsNondeg Q' → SameDisc Q Q' →
        ∃! i, Nonempty (Q'.IsometryEquiv (R i))) ∧
      (3 ≤ m → n = 2) ∧ (m ≤ 1 → n = 1) ∧ (m = 2 → (n = 1 ↔ IsSquare (-Q.discr'))) ∧ n ≤ 2 := by
  classical
  let := normValuativeRel F
  have := NormValuativeRel.isNonarchimedeanLocalField F
  set hQ' := (isNondeg_iff_nondegenerate Q).1 hQ
  set c := formClass Q hQ'
  set d := RegularFormClass.discr c
  set s := RegularFormClass.localHasse c
  have hcr : c.rank = m := by simp [c, rank_formClass]
  -- equivalence of two nondegenerate forms on `F^m`
  have hequiv : ∀ (q₁ q₂ : QuadraticForm F (Fin m → F)) (h₁ : IsNondeg q₁) (h₂ : IsNondeg q₂),
      Nonempty (q₁.IsometryEquiv q₂) ↔
        RegularFormClass.discr (formClass q₁ ((isNondeg_iff_nondegenerate q₁).1 h₁)) =
          RegularFormClass.discr (formClass q₂ ((isNondeg_iff_nondegenerate q₂).1 h₂)) ∧
        RegularFormClass.localHasse (formClass q₁ ((isNondeg_iff_nondegenerate q₁).1 h₁)) =
          RegularFormClass.localHasse (formClass q₂ ((isNondeg_iff_nondegenerate q₂).1 h₂)) := by
    intro q₁ q₂ h₁ h₂
    rw [← QuadraticMap.Equivalent,
      QuadraticForm.equivalent_iff_finrank_eq_and_discr_eq_and_localHasse_eq q₁
        ((isNondeg_iff_nondegenerate q₁).1 h₁) ((isNondeg_iff_nondegenerate q₂).1 h₂)]
    simp
  -- `d = [-1]` iff `-det Q` is a square
  have hsq : d = squareClass (-1 : Fˣ) ↔ IsSquare (-Q.discr') := by
    rw [show d = _ from discr_formClass_eq Q hQ, squareClass_eq_iff_isSquare_mul,
      ← isSquare_units_val_iff]
    simp
  have hdisc : ∀ Q' : QuadraticForm F (Fin m → F), ∀ hQ'' : IsNondeg Q', SameDisc Q Q' →
      RegularFormClass.discr (formClass Q' ((isNondeg_iff_nondegenerate Q').1 hQ'')) = d :=
    fun Q' hQ'' h => ((sameDisc_iff Q Q' hQ hQ'').1 h).symm
  have hself : IsNondeg Q ∧ SameDisc Q Q := ⟨hQ, (sameDisc_iff Q Q hQ hQ).2 rfl⟩
  by_cases hother : ∃ x : RegularFormClass F, x.rank = m ∧ RegularFormClass.discr x = d ∧
      RegularFormClass.localHasse x = -s
  · obtain ⟨x, hxr, hxd, hxs⟩ := hother
    obtain ⟨Q₁, hQ₁, hcl⟩ := exists_form_of_rank_eq x hxr
    refine ⟨2, ![Q, Q₁], 0, rfl, ?_, ?_, fun _ => rfl, ?_, ?_, le_rfl⟩
    · intro i
      fin_cases i
      · exact hself
      · exact ⟨hQ₁, (sameDisc_iff Q Q₁ hQ hQ₁).2 (by rw [hcl, hxd])⟩
    · intro Q' hQ'' hsd
      have hd' := hdisc Q' hQ'' hsd
      rcases units_eq_or_eq_neg s (RegularFormClass.localHasse
          (formClass Q' ((isNondeg_iff_nondegenerate Q').1 hQ''))) with hs' | hs'
      · refine ⟨0, (hequiv Q' Q hQ'' hQ).2 ⟨hd', hs'⟩, fun j hj => ?_⟩
        fin_cases j
        · rfl
        · exfalso
          obtain ⟨-, h⟩ := (hequiv Q' Q₁ hQ'' hQ₁).1 hj
          rw [hs', hcl, hxs] at h
          exact units_ne_neg s h.symm
      · refine ⟨1, (hequiv Q' Q₁ hQ'' hQ₁).2 ⟨by rw [hd', hcl, hxd], by rw [hs', hcl, hxs]⟩,
          fun j hj => ?_⟩
        fin_cases j
        · exfalso
          obtain ⟨-, h⟩ := (hequiv Q' Q hQ'' hQ).1 hj
          rw [hs'] at h
          exact units_ne_neg s h
        · rfl
    · intro hm
      exfalso
      have h1 : s = 1 := RegularFormClass.localHasse_eq_one_of_rank_le_one (by omega)
      have h2 : RegularFormClass.localHasse x = 1 :=
        RegularFormClass.localHasse_eq_one_of_rank_le_one (by omega)
      rw [hxs, h1] at h2
      exact units_ne_neg 1 h2
    · intro hm
      simp only [OfNat.ofNat_ne_one, false_iff]
      intro hneg
      have hd1 := hsq.2 hneg
      have h1 : s = 1 :=
        RegularFormClass.localHasse_eq_one_of_rank_eq_two_of_discr_eq_neg_one (by omega) hd1
      have h2 : RegularFormClass.localHasse x = 1 :=
        RegularFormClass.localHasse_eq_one_of_rank_eq_two_of_discr_eq_neg_one (by omega)
          (by rw [hxd, hd1])
      rw [hxs, h1] at h2
      exact units_ne_neg 1 h2
  · refine ⟨1, ![Q], 0, rfl, ?_, ?_, ?_, fun _ => rfl, ?_, by norm_num⟩
    · intro i
      fin_cases i
      exact hself
    · intro Q' hQ'' hsd
      have hd' := hdisc Q' hQ'' hsd
      rcases units_eq_or_eq_neg s (RegularFormClass.localHasse
          (formClass Q' ((isNondeg_iff_nondegenerate Q').1 hQ''))) with hs' | hs'
      · exact ⟨0, (hequiv Q' Q hQ'' hQ).2 ⟨hd', hs'⟩, fun j _ => Subsingleton.elim _ _⟩
      · exact absurd ⟨_, by simp [rank_formClass], hd', hs'⟩ hother
    · intro hm
      exfalso
      exact hother (RegularFormClass.exists_of_realization (by omega) d (-s) (by omega)
        (by omega))
    · intro hm
      simp only [true_iff]
      by_contra hneg
      exact hother (RegularFormClass.exists_of_realization (by omega) d (-s) (by omega)
        (fun _ hd1 => absurd (hsq.1 hd1) hneg))

end GSpinGGP
