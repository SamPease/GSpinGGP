/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TwistPlane

/-!
# Block coordinates for an orthogonal decomposition

For an orthogonal decomposition `F^m = U ⊕ U'` of a quadratic space, `exists_blockCoords` gives
rational coordinates `B` (from a basis adapted to the decomposition) in which the Gram matrix is
block diagonal, `Q = Bᵀ (Q_U ⊕ G') B`, with `Q_U` the form of `U` on `F^{dim U}` and the
`U`-coordinates of every vector of `U'` equal to `0`: the input of `TwistPlane.exists_blockTwist`.
-/

noncomputable section

open Matrix Module

namespace GSpinGGP

namespace TwistPlane

variable {F : Type*} [Field F] [Invertible (2 : F)] {m : ℕ}

/-- **Block coordinates.**  If `F^m = U ⊕ U'` with `U ⊥ U'`, there are coordinates `B` with
`Q = Bᵀ (Q_U ⊕ G') B`, where `Q_U` is the form of `U` transported to `F^{dim U}` along a basis, and
in which the vectors of `U'` have vanishing `U`-coordinates. -/
theorem exists_blockCoords (Q : QuadraticForm F (Fin m → F)) {U U' : Submodule F (Fin m → F)}
    (hc : IsCompl U U') (horth : ∀ u ∈ U, ∀ u' ∈ U', bform Q u u' = 0) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (e : Fin (finrank F U) ⊕ κ ≃ Fin m)
      (B : GL (Fin m) F) (G₃ : Matrix κ κ F),
      G₃.IsSymm ∧
      Q.toMatrix' = (B : Matrix (Fin m) (Fin m) F)ᵀ *
        blockDiag e (QuadraticForm.toMatrix' ((Q.comp U.subtype).comp (finBasis F U).equivFun.symm.toLinearMap))
          G₃ * B ∧
      ∀ v ∈ U', ∀ i, ((B : Matrix (Fin m) (Fin m) F) *ᵥ v) (e (Sum.inl i)) = 0 := by
  classical
  set bU := finBasis F U
  set bU' := finBasis F U'
  let c : Basis (Fin (finrank F U) ⊕ Fin (finrank F U')) F (Fin m → F) :=
    (bU.prod bU').map (Submodule.prodEquivOfIsCompl U U' hc)
  let e : Fin (finrank F U) ⊕ Fin (finrank F U') ≃ Fin m := c.indexEquiv (Pi.basisFun F (Fin m))
  set c' := c.reindex e
  set b := Pi.basisFun F (Fin m)
  let B : GL (Fin m) F :=
    { val := c'.toMatrix b
      inv := b.toMatrix c'
      val_inv := Basis.toMatrix_mul_toMatrix_flip c' b
      inv_val := Basis.toMatrix_mul_toMatrix_flip b c' }
  let G₃ : Matrix (Fin (finrank F U')) (Fin (finrank F U')) F :=
    fun i j => bform Q (bU' i) (bU' j)
  refine ⟨Fin (finrank F U'), inferInstance, inferInstance, e, B, G₃, ?_, ?_, ?_⟩
  · ext i j
    exact QuadraticMap.associated_isSymm F Q _ _
  · have hb : Q.toMatrix' = LinearMap.BilinForm.toMatrix b (QuadraticMap.associated Q) := by
      rw [LinearMap.BilinForm.toMatrix_basisFun]; rfl
    have hD : LinearMap.BilinForm.toMatrix c' (QuadraticMap.associated Q) =
        blockDiag e (QuadraticForm.toMatrix' ((Q.comp U.subtype).comp
          (finBasis F U).equivFun.symm.toLinearMap)) G₃ := by
      ext i j
      rw [LinearMap.BilinForm.toMatrix_apply]
      simp only [blockDiag, Matrix.coe_reindexAlgEquiv, reindex_apply, submatrix_apply]
      have hc' : ∀ k, c' k = c (e.symm k) := fun k => Basis.reindex_apply _ _ _
      rw [hc', hc']
      generalize e.symm i = a
      generalize e.symm j = a'
      rcases a with a | a <;> rcases a' with a' | a'
      · simp [c, QuadraticForm.toMatrix', LinearMap.toMatrix₂'_apply, QuadraticMap.associated_comp,
          bU]
      · simpa [c] using horth _ (bU a).2 _ (bU' a').2
      · have := horth _ (bU a').2 _ (bU' a).2
        rw [QuadraticMap.associated_isSymm] at this
        simpa [c] using this
      · simp only [c, Basis.map_apply, Basis.prod_apply, Sum.elim_inr, LinearMap.coe_inr,
          Function.comp_apply]
        rw [Matrix.fromBlocks_apply₂₂]
        rw [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl']
        simp [G₃]
    rw [hb, ← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix c' b, hD]
  · intro v hv i
    have h1 : (B : Matrix (Fin m) (Fin m) F) *ᵥ v = c'.repr v := by
      have := Basis.toMatrix_mulVec_repr b c' v
      rwa [show b.repr v = v from rfl] at this
    rw [h1, Basis.repr_reindex_apply, Equiv.symm_apply_apply, Basis.map_repr]
    have h2 := Submodule.prodEquivOfIsCompl_symm_apply_right U U' hc (⟨v, hv⟩ : U')
    simp [h2]

end TwistPlane

end GSpinGGP
