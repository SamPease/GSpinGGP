/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TwistMoved

/-!
# Twisting `W` into a given form along `S_y`

`exists_isTwistBy_torusBar_of_isometry`: for `y ∈ Γ(G,H)` and a nondegenerate form `Q'` of the
discriminant of `W` into which `W'_y` embeds isometrically, `Q'` is the twist of `W` by a cocycle
with values in `S_y(F̄)`.  In block coordinates for `W = W''_y ⊥ W'_y`, twist the block `W''_y` into
the transported form of `ι(W'_y)^⊥ ⊆ Q'` (`TwistPlane.exists_blockTwist_core`); the result is
isometric to `Q'` (Witt-type assembly, `orthIsometry`), the cocycle lies in `SO(W)_{W'_y}(F̄)`
(`conj_blockDiagGL_mem_fixerBar`), and Kottwitz 1986, Lemma 10.2
(`exists_isTwistBy_torusBar_of_fixerBar`) moves it into `S_y(F̄)`.  Used for Thesis Prop. 6.6.1(i).
-/

noncomputable section

open Module Matrix

namespace GSpinGGP

section Orth

variable {K V : Type*} [Field K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]

/-- **An orthogonal decomposition is an orthogonal sum**: `V = U ⊕ U'` with `U ⊥ U'` gives
`Q|_U ⊥ Q|_{U'} ≅ Q` (for any complement `U'` orthogonal for `bform Q`; Tau Ceti
`QuadraticMap.IsometryEquiv.prodRestrictOrthogonal` is the case `U' = U^⊥` for the polar form). -/
def orthIsometry (Q : QuadraticForm K V) {U U' : Submodule K V} (hc : IsCompl U U')
    (horth : ∀ u ∈ U, ∀ u' ∈ U', bform Q u u' = 0) :
    ((Q.comp U.subtype).prod (Q.comp U'.subtype)).IsometryEquiv Q where
  toLinearEquiv := Submodule.prodEquivOfIsCompl U U' hc
  map_app' p := by
    change Q ((p.1 : V) + p.2) = Q p.1 + Q p.2
    rw [QuadraticMap.map_add Q (p.1 : V) p.2, polar_eq_two_mul_bform, horth _ p.1.2 _ p.2.2, mul_zero, add_zero]

/-- `V = A ⊥ A^⊥` when `Q|_A` is nondegenerate (finite dimension). -/
theorem isCompl_orthogonal_of_isNondeg [FiniteDimensional K V] {Q : QuadraticForm K V}
    {A : Submodule K V} (hA : IsNondeg (Q.comp A.subtype)) :
    IsCompl A ((bform Q).orthogonal A) := by
  have e : bform (Q.comp A.subtype) = (bform Q).restrict A := by
    ext a b; exact bform_comp_subtype Q A a b
  have hA' : ((bform Q).restrict A).Nondegenerate := by rw [← e]; exact hA
  exact (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
    (LinearMap.IsSymm.isRefl (QuadraticForm.associated_isSymm (S := K) Q))).1 hA'

/-- The form of `U` transported to `K^{dim U}` along `finBasis` is isometric to `Q|_U`
(Mathlib `QuadraticMap.isometryEquivOfCompLinearEquiv`). -/
def finBasisIso [FiniteDimensional K V] (Q : QuadraticForm K V) (U : Submodule K V) :
    ((Q.comp U.subtype).comp (finBasis K U).equivFun.symm.toLinearMap).IsometryEquiv
      (Q.comp U.subtype) :=
  (QuadraticMap.isometryEquivOfCompLinearEquiv _ (finBasis K U).equivFun.symm).symm

end Orth

namespace QuadClassify

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V₁ V₂ V₃ V₄ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃] [AddCommGroup V₄] [Module K V₄]
  [FiniteDimensional K V₁] [FiniteDimensional K V₂] [FiniteDimensional K V₃]
  [FiniteDimensional K V₄]

omit [FiniteDimensional K V₂] [FiniteDimensional K V₄] in
/-- **Cancellation of discriminants**: `disc(Q₁ ⊥ Q₂) = disc(Q₃ ⊥ Q₄)` and
`disc Q₂ = disc Q₄ ≠ 0` give `disc Q₁ = disc Q₃`, for `dim V₁ = dim V₃`. -/
theorem DiscRel.cancel_right {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    {Q₃ : QuadraticForm K V₃} {Q₄ : QuadraticForm K V₄} (h : DiscRel (Q₁.prod Q₂) (Q₃.prod Q₄))
    (h₂ : DiscRel Q₂ Q₄) (hnd : IsNondeg Q₂) (hdim : finrank K V₁ = finrank K V₃) :
    DiscRel Q₁ Q₃ := by
  obtain ⟨n, c₂, c₄, c', hc', h'⟩ := h₂
  set b₁ := finBasis K V₁
  set b₃ := (finBasis K V₃).reindex (finCongr hdim.symm)
  obtain ⟨c, hc, hc4⟩ := DiscRel.bases h (b₁.prod c₂) (b₃.prod c₄)
  rw [gdet_prod, gdet_prod, h'] at hc4
  have h20 : gdet Q₂ c₂ ≠ 0 := (isNondeg_iff_gdet_ne_zero Q₂ c₂).1 hnd
  refine ⟨_, b₁, b₃, c / c', div_ne_zero hc hc', ?_⟩
  have : gdet Q₃ b₃ * (c' ^ 2 * gdet Q₂ c₂) = (c / c') ^ 2 * gdet Q₁ b₁ * (c' ^ 2 * gdet Q₂ c₂) := by
    rw [hc4]; field_simp
  exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 hc') h20) this

end QuadClassify

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- **Twisting `W` into a given form along `S_y`**: for `y ∈ Γ(G,H)`, a nondegenerate `Q'` of the
discriminant of `W`, and an isometric embedding `ι : W'_y ↪ Q'`, some cocycle with values in
`S_y(F̄)` twists `W` into `Q'`. -/
theorem exists_isTwistBy_torusBar_of_isometry {d : GGPData F} {y : ↥(GSpin d.QW)}
    (hy : d.IsGammaElt y) {Q' : QuadraticForm F (Fin d.m → F)} (hsd : SameDisc d.QW Q')
    (ι : (d.QW.comp (fixedSub y).subtype) →qᵢ Q') (hι : Function.Injective ι) :
    ∃ a : GalCocycle (d.torusBarFbar y), IsTwistBy d.QW Q' a.toFun := by
  classical
  set U := (bform d.QW).orthogonal (fixedSub y) with hUdef
  have hdisj := fixedSub_inf_movedSub_of_isSS y hy.1
  have hcW : IsCompl (fixedSub y) U := isCompl_fixedSub_orthogonal d.nondeg y hdisj
  have horth : ∀ u ∈ U, ∀ a ∈ (fixedSub y), bform d.QW u a = 0 := fun u hu a ha => by
    rw [QuadraticMap.associated_isSymm]
    exact hu a ha
  obtain ⟨e, B, hB, hfix⟩ := TwistPlane.exists_blockCoords d.QW hcW.symm horth
  -- the target decomposition `Q' = ι((fixedSub y))^⊥ ⊥ ι((fixedSub y))`
  set V' := LinearMap.range ι.toLinearMap with hV'def
  let jι : (d.QW.comp (fixedSub y).subtype).IsometryEquiv (Q'.comp V'.subtype) :=
    { toLinearEquiv := LinearEquiv.ofInjective ι.toLinearMap hι
      map_app' := fun a => ι.map_app a }
  have hAnd : IsNondeg (d.QW.comp (fixedSub y).subtype) := isNondeg_comp_subtype_of_isCompl hcW
  have hV'nd : IsNondeg (Q'.comp V'.subtype) :=
    (QuadClassify.DiscRel.of_isometryEquiv jι).isNondeg hAnd
  have hcV := isCompl_orthogonal_of_isNondeg hV'nd
  set U'' := (bform Q').orthogonal V' with hU''def
  have horth2 : ∀ u ∈ U'', ∀ v ∈ V', bform Q' u v = 0 := fun u hu v hv => by
    rw [QuadraticMap.associated_isSymm]
    exact hu v hv
  -- dimensions
  have hdimA : finrank F (fixedSub y) = finrank F V' := jι.toLinearEquiv.finrank_eq
  have hdimU : finrank F U = finrank F U'' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hcW
    have h2 := Submodule.finrank_add_eq_of_isCompl hcV
    omega
  -- the blocks
  set Q₂ := (d.QW.comp U.subtype).comp (finBasis F U).equivFun.symm.toLinearMap with hQ₂def
  set P'' := (Q'.comp U''.subtype).comp (finBasis F U'').equivFun.symm.toLinearMap with hP''def
  let L : (Fin (finrank F U) → F) ≃ₗ[F] (Fin (finrank F U'') → F) :=
    LinearEquiv.funCongrLeft F F (finCongr hdimU.symm)
  set Q₂' : QuadraticForm F (Fin (finrank F U) → F) := P''.comp L.toLinearMap with hQ₂'def
  let iL : Q₂'.IsometryEquiv P'' := { toLinearEquiv := L, map_app' := fun _ => rfl }
  set GA := (d.QW.comp (fixedSub y).subtype).comp (finBasis F (fixedSub y)).equivFun.symm.toLinearMap with hGAdef
  set G₃ := QuadraticForm.toMatrix' GA with hG₃def
  have hG₃ : G₃.IsSymm := QuadraticForm.isSymm_toMatrix' _
  have hG₃QF : G₃.toQuadraticForm' = GA := QuadraticForm.toMatrix'_toQuadraticForm' GA
  -- `W ≅ Q₂ ⊥ G_A`
  have isoW : d.QW.IsometryEquiv (Q₂.prod GA) := by
    have h0 : d.QW = ((B : Matrix (Fin d.m) (Fin d.m) F)ᵀ *
        TwistPlane.blockDiag e (QuadraticForm.toMatrix' Q₂) G₃ * B).toQuadraticForm' := by
      rw [← hB, QuadraticForm.toMatrix'_toQuadraticForm']
    have i1 := TwistPlane.blockFormIso e B (QuadraticForm.toMatrix' Q₂) G₃
    rw [QuadraticForm.toMatrix'_toQuadraticForm', hG₃QF, ← h0] at i1
    exact i1
  have hQ₂ : IsNondeg Q₂ := TwistPlane.isNondeg_of_blockDiag d.nondeg e B hB
  have hGA : IsNondeg GA :=
    (QuadClassify.DiscRel.of_isometryEquiv (finBasisIso d.QW (fixedSub y)).symm).isNondeg hAnd
  -- `disc Q₂ = disc Q₂'`
  have hdr : QuadClassify.DiscRel Q₂ Q₂' := by
    have h1 : QuadClassify.DiscRel (Q₂.prod GA) (Q₂'.prod (Q'.comp V'.subtype)) :=
      (QuadClassify.DiscRel.of_isometryEquiv isoW.symm).trans
        (((QuadClassify.sameDisc_iff_discRel _ _).1 hsd).trans
          (QuadClassify.DiscRel.of_isometryEquiv
            ((orthIsometry Q' hcV.symm horth2).symm.trans
              (((finBasisIso Q' U'').symm.trans iL.symm).prod
                (QuadraticMap.IsometryEquiv.refl _)))))
    exact QuadClassify.DiscRel.cancel_right h1
      (QuadClassify.DiscRel.of_isometryEquiv ((finBasisIso d.QW (fixedSub y)).trans jι)) hGA rfl
  have hnd' : IsNondeg Q₂' := hdr.isNondeg hQ₂
  obtain ⟨-, -, a, ha⟩ := exists_isTwistBy_torusBar_of_blockCoords hy e B hnd' hdr hG₃ hB hfix
  -- the twisted form is `≅ Q'`
  have isoC : ((B : Matrix (Fin d.m) (Fin d.m) F)ᵀ * TwistPlane.blockDiag e (QuadraticForm.toMatrix' Q₂') G₃ *
      B).toQuadraticForm'.IsometryEquiv Q' := by
    have i1 := TwistPlane.blockFormIso e B (QuadraticForm.toMatrix' Q₂') G₃
    rw [QuadraticForm.toMatrix'_toQuadraticForm', hG₃QF] at i1
    exact i1.trans (((iL.trans (finBasisIso Q' U'')).prod
      ((finBasisIso d.QW (fixedSub y)).trans jι)).trans (orthIsometry Q' hcV.symm horth2))
  exact ⟨a, TwistDescent.isTwistBy_of_isometryEquiv isoC ha⟩

end GSpinGGP
