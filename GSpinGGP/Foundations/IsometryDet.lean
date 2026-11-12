import GSpinGGP.Foundations.IsometryCentralizer
import TauCeti.LinearAlgebra.Eigenspace.BaseChange
import TauCeti.LinearAlgebra.BilinearForm.BaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Determinants of isometries on paired subspaces

If a bilinear form `B` pairs two subspaces `E`, `E'` perfectly and an isometry `h` of `B`
preserves both, then `h` acts on `E'` as the inverse transpose of its action on `E`, so
`det (h|_E) * det (h|_{E'}) = 1` (`IsomCent.det_mul_det_of_pairing`).
-/

open Module

namespace GSpinGGP

namespace IsomCent

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V}

/-- **Paired subspaces.** If `B` pairs `E` and `E'` perfectly and the isometry `h` preserves
both, then `det (h|_E) * det (h|_{E'}) = 1`. -/
theorem det_mul_det_of_pairing [FiniteDimensional K V] {E E' : Submodule K V}
    {h : V →ₗ[K] V} (hi : B.IsOrthogonal h) (hE : Set.MapsTo h E E) (hE' : Set.MapsTo h E' E')
    (hl : ∀ w ∈ E', (∀ u ∈ E, B u w = 0) → w = 0)
    (hr : ∀ u ∈ E, (∀ w ∈ E', B u w = 0) → u = 0) :
    LinearMap.det (h.restrict hE) * LinearMap.det (h.restrict hE') = 1 := by
  set A := h.restrict hE
  set A' := h.restrict hE'
  -- `A` is injective, hence an automorphism of `E`
  have hAinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    refine Subtype.ext (hr u u.2 fun w hw => ?_)
    have := hi u w
    have hu' : h u = 0 := congrArg Subtype.val hu
    rw [hu', map_zero, LinearMap.zero_apply] at this
    exact this.symm
  let eA : E ≃ₗ[K] E := LinearEquiv.ofInjectiveEndo A hAinj
  -- the pairing map `E' → E*`
  let φ : E' →ₗ[K] Module.Dual K E :=
    { toFun := fun w => (B.flip (w : V)).comp E.subtype
      map_add' := fun w w' => by ext u; simp
      map_smul' := fun c w => by ext u; simp }
  let ψ : E →ₗ[K] Module.Dual K E' :=
    { toFun := fun u => (B (u : V)).comp E'.subtype
      map_add' := fun u u' => by ext w; simp
      map_smul' := fun c u => by ext w; simp }
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine Subtype.ext (hl w w.2 fun u hu => ?_)
    have := LinearMap.congr_fun hw ⟨u, hu⟩
    simpa [φ] using this
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    refine Subtype.ext (hr u u.2 fun w hw => ?_)
    have := LinearMap.congr_fun hu ⟨w, hw⟩
    simpa [ψ] using this
  have hdim : finrank K E' = finrank K (Module.Dual K E) := by
    apply le_antisymm (LinearMap.finrank_le_finrank_of_injective hφ)
    rw [Subspace.dual_finrank_eq]
    calc finrank K E ≤ finrank K (Module.Dual K E') := LinearMap.finrank_le_finrank_of_injective hψ
      _ = finrank K E' := Subspace.dual_finrank_eq
  let eφ : E' ≃ₗ[K] Module.Dual K E := LinearEquiv.ofInjectiveOfFinrankEq φ hφ hdim
  -- `φ ∘ A' = (A⁻¹)ᵀ ∘ φ`
  have hconj : (eφ : E' →ₗ[K] Module.Dual K E) ∘ₗ A' =
      (eA.symm : E →ₗ[K] E).dualMap ∘ₗ (eφ : E' →ₗ[K] Module.Dual K E) := by
    ext w u
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.dualMap_apply]
    change B (u : V) (h w) = B ((eA.symm u : E) : V) (w : V)
    have hu : u = eA (eA.symm u) := (eA.apply_symm_apply u).symm
    conv_lhs => rw [hu]
    change B (h (eA.symm u : V)) (h w) = _
    exact hi _ _
  have hA' : A' = (eφ.symm : Module.Dual K E →ₗ[K] E') ∘ₗ (eA.symm : E →ₗ[K] E).dualMap ∘ₗ
      (eφ : E' →ₗ[K] Module.Dual K E) := by
    rw [← hconj]
    ext w
    simp
  have hdetA' : LinearMap.det A' = (LinearMap.det A)⁻¹ := by
    have hc := LinearMap.det_conj ((eA.symm : E →ₗ[K] E).dualMap) eφ.symm
    rw [LinearEquiv.symm_symm] at hc
    rw [hA', hc, LinearMap.det_dualMap]
    have : LinearMap.det (eA.symm : E →ₗ[K] E) * LinearMap.det A = 1 := by
      rw [← LinearMap.det_comp]
      have : (eA.symm : E →ₗ[K] E) ∘ₗ A = LinearMap.id := by
        ext u; exact congrArg Subtype.val (eA.symm_apply_apply u)
      rw [this, LinearMap.det_id]
    exact eq_inv_of_mul_eq_one_left this
  have hdet0 : LinearMap.det A ≠ 0 := by
    have he : (eA : E →ₗ[K] E) = A := LinearMap.ext fun _ => rfl
    rw [← he]
    exact (LinearEquiv.isUnit_det' eA).ne_zero
  rw [hdetA', mul_inv_cancel₀ hdet0]

section Eigen

open Module.End

variable {X : Module.End K V}

/-- Eigenspaces `E_μ` and `E_{μ⁻¹}` of a semisimple isometry `X` are paired perfectly by a
nondegenerate symmetric `B`. -/
theorem pairing_eigenspace [IsAlgClosed K] [FiniteDimensional K V] (hB : B.IsSymm)
    (hnd : B.Nondegenerate) (hX : B.IsOrthogonal X)
    (hss : X.IsSemisimple) (μ : K) :
    (∀ w ∈ X.eigenspace μ⁻¹, (∀ u ∈ X.eigenspace μ, B u w = 0) → w = 0) ∧
      (∀ u ∈ X.eigenspace μ, (∀ w ∈ X.eigenspace μ⁻¹, B u w = 0) → u = 0) := by
  constructor
  · intro w hw h0
    refine hnd.1 w fun v => ?_
    obtain ⟨u, hu, huv⟩ := exists_eigen_pair hX hss hw v
    rw [inv_inv] at hu
    rw [← huv, ← hB.eq u w]
    exact h0 u hu
  · intro u hu h0
    refine hnd.1 u fun v => ?_
    obtain ⟨w, hw, hwv⟩ := exists_eigen_pair hX hss hu v
    rw [← hwv]
    exact h0 w hw

variable [CharZero K] [IsAlgClosed K] [FiniteDimensional K V]

/-- **`det h = det (h|_{E₁}) · det (h|_{E₋₁})`** for an isometry `h` commuting with a semisimple
isometry `X` (algebraically closed field of characteristic `0`): the other eigenspaces pair off
as `E_μ, E_{μ⁻¹}` and contribute `det · det = 1` (`det_mul_det_of_pairing`). -/
theorem det_eq_det_one_mul_det_neg_one (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (hX : B.IsOrthogonal X) (hss : X.IsSemisimple) {h : Module.End K V} (hi : B.IsOrthogonal h)
    (hc : Commute X h) :
    LinearMap.det h = LinearMap.det (h.restrict (mapsTo_eigenspace_of_commute hc 1)) *
      LinearMap.det (h.restrict (mapsTo_eigenspace_of_commute hc (-1))) := by
  classical
  set g : K → K := fun k => LinearMap.det (h.restrict (mapsTo_eigenspace_of_commute hc k))
    with hg_def
  have hg1 : ∀ k, ¬ X.HasEigenvalue k → g k = 1 := fun k hk => by
    have hbot : X.eigenspace k = ⊥ := by rwa [hasEigenvalue_iff, not_not] at hk
    exact LinearMap.det_eq_one_of_finrank_eq_zero (Submodule.finrank_eq_zero.2 hbot) _
  have hprod : LinearMap.det h = ∏ μ : X.Eigenvalues, g μ :=
    det_eq_prod_det_restrict (isInternal_eigenspace hss) h
      (fun μ => mapsTo_eigenspace_of_commute hc (μ : K))
  set T : Finset K := Finset.univ.image (fun μ : X.Eigenvalues => (μ : K)) with hT_def
  have hmemT : ∀ k, k ∈ T ↔ X.HasEigenvalue k := fun k => by
    simp only [hT_def, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨μ, hμ⟩ => hμ ▸ μ.2, fun hk => ⟨⟨k, hk⟩, rfl⟩⟩
  have hT : ∏ μ : X.Eigenvalues, g μ = ∏ k ∈ T, g k :=
    (Finset.prod_image (fun a _ b _ hab => Subtype.ext hab)).symm
  set U : Finset K := T ∪ {1, -1} with hU_def
  have hTU : ∏ k ∈ T, g k = ∏ k ∈ U, g k := by
    refine Finset.prod_subset Finset.subset_union_left fun k hkU hkT => hg1 k ?_
    rwa [← hmemT]
  have h1 : (1 : K) ≠ -1 := by
    intro h; have : (2 : K) = 0 := by linear_combination h
    exact two_ne_zero this
  have hsplit := Finset.prod_filter_mul_prod_filter_not U (fun k => k = 1 ∨ k = -1) g
  have hfilt : U.filter (fun k => k = 1 ∨ k = -1) = {1, -1} := by
    ext k; simp only [hU_def, Finset.mem_filter, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton]; tauto
  have hrest : ∏ k ∈ U.filter (fun k => ¬ (k = 1 ∨ k = -1)), g k = 1 := by
    refine Finset.prod_involution (fun k _ => k⁻¹) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, hU_def, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at hk
      have hkT : k ∈ T := by tauto
      have hpair := pairing_eigenspace hB hnd hX hss k
      exact det_mul_det_of_pairing hi (mapsTo_eigenspace_of_commute hc k)
        (mapsTo_eigenspace_of_commute hc k⁻¹) hpair.1 hpair.2
    · intro k hk _ heq
      simp only [Finset.mem_filter, hU_def, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at hk
      have hkT : k ∈ T := by tauto
      have hk0 : k ≠ 0 := ne_zero_of_hasEigenvalue hnd hX ((hmemT k).1 hkT)
      have : (k - 1) * (k + 1) = 0 := by
        have h2 : k * k = 1 := by
          calc k * k = k * k⁻¹ := by rw [heq]
            _ = 1 := mul_inv_cancel₀ hk0
        linear_combination h2
      rcases mul_eq_zero.1 this with h0 | h0
      · exact hk.2 (Or.inl (by linear_combination h0))
      · exact hk.2 (Or.inr (by linear_combination h0))
    · intro k hk
      simp only [Finset.mem_filter, hU_def, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at hk ⊢
      have hkT : k ∈ T := by tauto
      refine ⟨Or.inl ((hmemT _).2 (hasEigenvalue_inv hnd hX hss ((hmemT k).1 hkT))), ?_⟩
      rintro (h' | h')
      · exact hk.2 (Or.inl (by rw [← inv_inv k, h', inv_one]))
      · exact hk.2 (Or.inr (by rw [← inv_inv k, h', inv_neg, inv_one]))
    · intro k _
      exact inv_inv k
  rw [hprod, hT, hTU, ← hsplit, hfilt, hrest, mul_one, Finset.prod_pair h1]

end Eigen

section BaseChange

open TensorProduct

/-- The determinant of a restriction commutes with extension of scalars to a field. -/
theorem det_restrict_baseChange {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K V]
    (f : V →ₗ[K] V) {E : Submodule K V} (hf : Set.MapsTo f E E)
    (hf' : Set.MapsTo (f.baseChange L) (E.baseChange L) (E.baseChange L)) :
    LinearMap.det ((f.baseChange L).restrict hf') =
      algebraMap K L (LinearMap.det (f.restrict hf)) := by
  have hinj : Function.Injective (E.subtype.baseChange L) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := L) E.subtype E.injective_subtype
  let e : L ⊗[K] E ≃ₗ[L] E.baseChange L := LinearEquiv.ofInjective _ hinj
  have hcomm : (f.baseChange L).restrict hf' =
      (e : L ⊗[K] E →ₗ[L] E.baseChange L) ∘ₗ (f.restrict hf).baseChange L ∘ₗ
        (e.symm : E.baseChange L →ₗ[L] L ⊗[K] E) := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨z, rfl⟩ := e.surjective y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    change f.baseChange L (E.subtype.baseChange L z) =
      E.subtype.baseChange L ((f.restrict hf).baseChange L z)
    rw [← LinearMap.comp_apply (f.baseChange L), ← LinearMap.baseChange_comp,
      ← LinearMap.comp_apply (E.subtype.baseChange L), ← LinearMap.baseChange_comp]
    rfl
  rw [hcomm, LinearMap.det_conj, LinearMap.det_baseChange]

theorem det_restrict_congr {W : Type*} [AddCommGroup W] [Module K W] (f : W →ₗ[K] W)
    {E E' : Submodule K W} (h : E = E') (hf : Set.MapsTo f E E) (hf' : Set.MapsTo f E' E') :
    LinearMap.det (f.restrict hf) = LinearMap.det (f.restrict hf') := by
  subst h; rfl

/-- Over a perfect field, semisimplicity survives extension of scalars to the algebraic closure
(squarefree polynomials stay squarefree). -/
theorem isSemisimple_baseChange_algebraicClosure [PerfectField K] [FiniteDimensional K V]
    {f : Module.End K V} (hf : f.IsSemisimple) :
    Module.End.IsSemisimple (f.baseChange (AlgebraicClosure K)) := by
  have hsep : (minpoly K f).Separable :=
    PerfectField.separable_iff_squarefree.2 hf.minpoly_squarefree
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (hsep.map (f := algebraMap K (AlgebraicClosure K))).squarefree ?_
  rw [Polynomial.aeval_map_algebraMap]
  have : f.baseChange (AlgebraicClosure K) =
      Module.End.baseChangeHom K (AlgebraicClosure K) V f := rfl
  rw [this, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]

open Module.End in
/-- **`det h = det (h|_{E₁}) · det (h|_{E₋₁})`** over any field of characteristic `0`, for an
isometry `h` commuting with a semisimple isometry `X` of a nondegenerate symmetric form: base
change to `K̄` and `det_eq_det_one_mul_det_neg_one`. -/
theorem det_eq_det_one_mul_det_neg_one_of_charZero [CharZero K] [FiniteDimensional K V]
    (hB : B.IsSymm) (hnd : B.Nondegenerate) {X : Module.End K V} (hX : B.IsOrthogonal X)
    (hss : X.IsSemisimple) {h : Module.End K V} (hi : B.IsOrthogonal h) (hc : Commute X h) :
    LinearMap.det h = LinearMap.det (h.restrict (mapsTo_eigenspace_of_commute hc 1)) *
      LinearMap.det (h.restrict (mapsTo_eigenspace_of_commute hc (-1))) := by
  set L := AlgebraicClosure K
  have hcL : Commute (X.baseChange L) (h.baseChange L) := by
    change X.baseChange L * h.baseChange L = h.baseChange L * X.baseChange L
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_comp]
    exact congrArg (LinearMap.baseChange L) hc.eq
  have key := det_eq_det_one_mul_det_neg_one (B := B.baseChange L)
    (LinearMap.BilinForm.isSymm_iff.2
      (LinearMap.BilinForm.IsSymm.baseChange L (LinearMap.BilinForm.isSymm_iff.1 hB)))
    (LinearMap.BilinForm.Nondegenerate.baseChange (A := L) hnd) (hX.baseChange L) (isSemisimple_baseChange_algebraicClosure hss)
    (hi.baseChange L) hcL
  have hE : ∀ μ : K, (X.eigenspace μ).baseChange L =
      Module.End.eigenspace (X.baseChange L) (algebraMap K L μ) :=
    fun μ => (eigenspace_baseChange_of_flat X μ).symm
  apply (algebraMap K L).injective
  rw [map_mul, ← LinearMap.det_baseChange, key,
    ← det_restrict_baseChange h (mapsTo_eigenspace_of_commute hc 1)
      (by rw [hE, map_one]; exact mapsTo_eigenspace_of_commute hcL 1),
    ← det_restrict_baseChange h (mapsTo_eigenspace_of_commute hc (-1))
      (by rw [hE, map_neg, map_one]; exact mapsTo_eigenspace_of_commute hcL (-1))]
  congr 1
  · exact det_restrict_congr _ (by rw [hE, map_one]) _ _
  · exact det_restrict_congr _ (by rw [hE, map_neg, map_one]) _ _

end BaseChange

end IsomCent

end GSpinGGP
