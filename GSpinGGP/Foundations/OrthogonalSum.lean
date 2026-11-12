/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.QuadraticForms
import GSpinGGP.Foundations.SoCentralizer
import TauCeti.LinearAlgebra.BilinearForm.Isometry

/-!
# Orthogonal sums of subspaces and isometries between them

* `det_isometryEquiv_eq_one_or`: an isometry of a nondegenerate space has determinant `±1`.
* `orthSupIso`, `isoOfEq`, `lineIso`: isometries `A ⊔ B ≅ A ⊥ B`, between equal subspaces, and
  between lines spanned by vectors of the same length.
* `nonempty_isometryEquiv_of_split`: split nondegenerate forms of the same even dimension are
  isometric.
* `span_sup_inf_orthogonal`: `U = K e ⊥ (U ∩ e^⊥)` for `e ∈ U` anisotropic.
* `isNondeg_comp_of_sup`, `skew_restrict`, `finrank_sup_of_disjoint`: restriction lemmas.
-/

noncomputable section

open Module

namespace GSpinGGP

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]

section Det

variable [FiniteDimensional K V]

/-- An isometry of a nondegenerate space has determinant `±1`. -/
theorem det_isometryEquiv_eq_one_or {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    (g : Q.IsometryEquiv Q) :
    LinearMap.det (g.toLinearEquiv : V →ₗ[K] V) = 1 ∨
      LinearMap.det (g.toLinearEquiv : V →ₗ[K] V) = -1 := by
  have hB : (bform Q).SeparatingLeft := fun w hw => hQ.1 w hw
  have hi : TauCeti.BilinForm.IsIsometry (bform Q) (g.toLinearEquiv : V →ₗ[K] V) :=
    fun u v => bform_isometry g.toIsometry u v
  have hsq := hi.det_sq_eq_one (Module.Free.chooseBasis K V)
    (mem_nonZeroDivisors_of_ne_zero ((LinearMap.separatingLeft_iff_det_ne_zero _).mp hB))
  exact sq_eq_one_iff.1 hsq


end Det

section Orth

variable {Q : QuadraticForm K V}

/-- An orthogonal summand of a subspace `U` without radical has no radical. -/
theorem isNondeg_comp_of_sup {U A B : Submodule K V}
    (hU : ∀ x ∈ U, (∀ y ∈ U, bform Q x y = 0) → x = 0) (hAB : A ⊔ B = U)
    (horth : ∀ a ∈ A, ∀ b ∈ B, bform Q a b = 0) : IsNondeg (Q.comp A.subtype) := by
  have hAU : A ≤ U := hAB ▸ le_sup_left
  refine (isNondeg_iff _).2 fun x hx => Subtype.ext (hU x (hAU x.2) fun y hy => ?_)
  rw [← hAB] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add, horth _ x.2 _ hb, add_zero]
  have := hx ⟨a, ha⟩
  rwa [bform_comp_subtype] at this

/-- A subspace `U` with `IsNondeg (Q|_U)` has no radical. -/
theorem radical_free_of_isNondeg {U : Submodule K V} (hU : IsNondeg (Q.comp U.subtype)) :
    ∀ x ∈ U, (∀ y ∈ U, bform Q x y = 0) → x = 0 := fun x hx h => by
  have := (isNondeg_iff _).1 hU ⟨x, hx⟩ fun y => by rw [bform_comp_subtype]; exact h y y.2
  exact congrArg Subtype.val this

/-- `A ⊔ B ≅ A ⊥ B` for orthogonal `A, B` with `A ⊓ B = 0`. -/
def orthSupIso {A B : Submodule K V} (hd : Disjoint A B)
    (horth : ∀ a ∈ A, ∀ b ∈ B, bform Q a b = 0) :
    ((Q.comp A.subtype).prod (Q.comp B.subtype)).IsometryEquiv (Q.comp (A ⊔ B).subtype) where
  toLinearEquiv := LinearEquiv.ofBijective
    ((Submodule.inclusion le_sup_left).coprod (Submodule.inclusion le_sup_right)) ⟨by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      rintro ⟨a, b⟩ h
      rw [LinearMap.mem_ker, LinearMap.coprod_apply] at h
      have h' : (a : V) + b = 0 := congrArg Subtype.val h
      have hb : (b : V) ∈ A := by
        rw [eq_neg_of_add_eq_zero_right h']
        exact A.neg_mem a.2
      have hb0 : (b : V) = 0 := (Submodule.disjoint_def.1 hd) _ hb b.2
      have ha0 : (a : V) = 0 := by rw [eq_neg_of_add_eq_zero_left h', hb0, neg_zero]
      exact Prod.ext (Subtype.ext ha0) (Subtype.ext hb0), by
      rintro ⟨x, hx⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩⟩
  map_app' p := by
    change Q ((p.1 : V) + (p.2 : V)) = Q p.1 + Q p.2
    rw [QuadraticMap.map_add Q, polar_eq_two_mul_bform, horth _ p.1.2 _ p.2.2, mul_zero, add_zero]

/-- Equal subspaces carry isometric forms. -/
def isoOfEq {A B : Submodule K V} (h : A = B) :
    (Q.comp A.subtype).IsometryEquiv (Q.comp B.subtype) where
  toLinearEquiv := LinearEquiv.ofEq A B h
  map_app' _ := rfl

/-- Lines spanned by vectors of the same length are isometric. -/
def lineIso {e e' : V} (he : e ≠ 0) (he' : e' ≠ 0) (hQ : Q e = Q e') :
    (Q.comp (K ∙ e).subtype).IsometryEquiv (Q.comp (K ∙ e').subtype) where
  toLinearEquiv := (LinearEquiv.toSpanNonzeroSingleton K V e he).symm.trans
    (LinearEquiv.toSpanNonzeroSingleton K V e' he')
  map_app' x := by
    set c := (LinearEquiv.toSpanNonzeroSingleton K V e he).symm x
    have hx : x = LinearEquiv.toSpanNonzeroSingleton K V e he c := by
      rw [LinearEquiv.apply_symm_apply]
    change Q ((LinearEquiv.toSpanNonzeroSingleton K V e' he' c : K ∙ e') : V) = Q (x : V)
    rw [hx, LinearEquiv.toSpanNonzeroSingleton_apply, LinearEquiv.toSpanNonzeroSingleton_apply]
    simp only [QuadraticMap.map_smul, hQ]

/-- Nondegenerate split forms of the same even dimension are isometric (both are `H^k`). -/
theorem nonempty_isometryEquiv_of_split {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁]
    [FiniteDimensional K V₁] [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
    {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} (h₁ : IsNondeg Q₁) (h₂ : IsNondeg Q₂)
    (hs₁ : IsSplitQF Q₁) (hs₂ : IsSplitQF Q₂) (hd : finrank K V₁ = finrank K V₂)
    (he : Even (finrank K V₁)) : Nonempty (Q₁.IsometryEquiv Q₂) := by
  obtain ⟨k₁, Qa₁, -, ⟨I₁⟩, hk₁⟩ := witt_decomposition Q₁ h₁
  obtain ⟨k₂, Qa₂, -, ⟨I₂⟩, hk₂⟩ := witt_decomposition Q₂ h₂
  unfold IsSplitQF at hs₁ hs₂
  obtain ⟨t, ht⟩ := he
  have h1 : k₁ = 0 := by omega
  have h2 : k₂ = 0 := by omega
  have hw : wittIndex Q₂ = wittIndex Q₁ := by omega
  subst h1 h2
  rw [hw] at I₂
  have : Qa₁ = Qa₂ := by
    ext x
    rw [Subsingleton.elim x 0, QuadraticMap.map_zero, QuadraticMap.map_zero]
  subst this
  exact ⟨I₁.trans I₂.symm⟩

end Orth

section OrbitNuAux

variable [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
/-- `x ∈ (K e)^⊥` iff `b(e, x) = 0`. -/
theorem mem_orthogonal_span_singleton {e x : V} :
    x ∈ (bform Q).orthogonal (K ∙ e) ↔ bform Q e x = 0 := by
  rw [LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]; rfl

omit [FiniteDimensional K V] in
/-- An anisotropic vector `e ∈ U` splits `U = K e ⊥ (U ∩ e^⊥)`. -/
theorem span_sup_inf_orthogonal {U : Submodule K V} {e : V} (he : e ∈ U) (hQe : Q e ≠ 0) :
    (K ∙ e) ⊔ (U ⊓ (bform Q).orthogonal (K ∙ e)) = U ∧
      Disjoint (K ∙ e) (U ⊓ (bform Q).orthogonal (K ∙ e)) ∧
      ∀ a ∈ K ∙ e, ∀ b ∈ U ⊓ (bform Q).orthogonal (K ∙ e), bform Q a b = 0 := by
  have horth : ∀ a ∈ K ∙ e, ∀ b ∈ U ⊓ (bform Q).orthogonal (K ∙ e), bform Q a b = 0 := by
    intro a ha b hb
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
    rw [LinearMap.map_smul₂, mem_orthogonal_span_singleton.1 hb.2, smul_zero]
  have hc := LinearMap.BilinForm.isCompl_span_singleton_orthogonal (B := bform Q) (x := e)
    (by rw [QuadraticMap.associated_eq_self_apply]; exact hQe)
  have hle : K ∙ e ≤ U := (Submodule.span_singleton_le_iff_mem _ _).2 he
  refine ⟨?_, hc.disjoint.mono_right inf_le_right, horth⟩
  rw [inf_comm, ← sup_inf_assoc_of_le _ hle, hc.sup_eq_top, top_inf_eq]

omit [Invertible (2 : K)] in
/-- `finrank (A ⊔ B) = finrank A + finrank B` for `A ⊓ B = 0`. -/
theorem finrank_sup_of_disjoint {A B : Submodule K V} (hd : Disjoint A B) :
    finrank K ↥(A ⊔ B) = finrank K A + finrank K B := by
  have := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hd.eq_bot, finrank_bot, add_zero] at this
  exact this

omit [FiniteDimensional K V] in
/-- The restriction of a skew map to an invariant subspace is skew. -/
theorem skew_restrict {N : Module.End K V} (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w))
    {U : Submodule K V} (hNU : ∀ u ∈ U, N u ∈ U) :
    ∀ u w : U, bform (Q.comp U.subtype) (N.restrict hNU u) w =
      -bform (Q.comp U.subtype) u (N.restrict hNU w) := fun u w => by
  simp only [bform_comp_subtype, LinearMap.coe_restrict_apply]
  exact hN u w

end OrbitNuAux

end GSpinGGP
