/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TwistDescent
import GSpinGGP.GGP.WittParity
import GSpinGGP.GGP.Hilbert90
import TauCeti.LinearAlgebra.Matrix.ToQuadraticForm

/-!
# Twisting an anisotropic plane

The plane case of the argument for Thesis Prop. 6.5.1(iv) (twisting `W''_x` along the anisotropic
torus `S_x`).  Let `Q` be a nondegenerate quadratic form on `F^m` (`F` a `p`-adic field) that is, in
rational coordinates, the orthogonal sum of an anisotropic binary form `Q₂` and a form with Gram
matrix `G₃` (`Q.toMatrix' = Bᵀ (Q₂ ⊕ G₃) B`).  `exists_planeTwist`: there is a form `Q'` of the same
discriminant that is *not* isometric to `Q`, and an `F̄`-isometry `Q_{F̄} ≃ Q'_{F̄}` with matrix `X`
whose cocycle `X⁻¹ σ(X)` is `B⁻¹ (R_σ ⊕ 1) B` with `R_σ ∈ SO(Q₂)(F̄)`, depending only on the
restriction of `σ` to a finite extension.

`Q'` twists the plane into the other binary form of its discriminant
(`WittParity.exists_other_class_plane`); non-isometry is Witt cancellation.  Forms of matrices are
Mathlib's `Matrix.toQuadraticForm'`, with Tau Ceti's isometries `Matrix.isometryEquivCongr`,
`isometryEquivReindex`, `isometryEquivFromBlocks`.
-/

noncomputable section

open Matrix

namespace GSpinGGP

namespace TwistPlane

section Block

variable {R : Type*} [CommRing R] {κ : Type*} [Fintype κ] [DecidableEq κ] {m n : ℕ}
  (e : Fin n ⊕ κ ≃ Fin m)

/-- The block-diagonal matrix `A ⊕ C` in the coordinates `e : Fin n ⊕ κ ≃ Fin m`. -/
def blockDiag (A : Matrix (Fin n) (Fin n) R) (C : Matrix κ κ R) : Matrix (Fin m) (Fin m) R :=
  Matrix.reindexAlgEquiv R R e (fromBlocks A 0 0 C)

theorem blockDiag_mul (A A' : Matrix (Fin n) (Fin n) R) (C C' : Matrix κ κ R) :
    blockDiag e A C * blockDiag e A' C' = blockDiag e (A * A') (C * C') := by
  simp [blockDiag, fromBlocks_multiply]

theorem blockDiag_transpose (A : Matrix (Fin n) (Fin n) R) (C : Matrix κ κ R) :
    (blockDiag e A C)ᵀ = blockDiag e Aᵀ Cᵀ := by
  simp [blockDiag, Matrix.coe_reindexAlgEquiv, fromBlocks_transpose]

theorem blockDiag_one : blockDiag e (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix κ κ R) = 1 := by
  simp [blockDiag, fromBlocks_one]

theorem det_blockDiag (A : Matrix (Fin n) (Fin n) R) (C : Matrix κ κ R) :
    (blockDiag e A C).det = A.det * C.det := by
  simp [blockDiag, Matrix.coe_reindexAlgEquiv, det_fromBlocks_zero₂₁]

theorem blockDiag_map {S : Type*} [CommRing S] (f : R →+* S) (A : Matrix (Fin n) (Fin n) R)
    (C : Matrix κ κ R) : (blockDiag e A C).map f = blockDiag e (A.map f) (C.map f) := by
  ext i j
  simp only [blockDiag, Matrix.coe_reindexAlgEquiv, map_apply, reindex_apply, submatrix_apply]
  rcases e.symm i with a | a <;> rcases e.symm j with b | b <;> simp

/-- The block-diagonal matrix acts blockwise. -/
theorem blockDiag_mulVec_inl (A : Matrix (Fin n) (Fin n) R) (C : Matrix κ κ R)
    (y : Fin m → R) (i : Fin n) :
    (blockDiag e A C *ᵥ y) (e (Sum.inl i)) = (A *ᵥ fun j => y (e (Sum.inl j))) i := by
  rw [blockDiag, Matrix.coe_reindexAlgEquiv, reindex_apply, submatrix_mulVec_equiv]
  simp [fromBlocks_mulVec, Function.comp_def]

theorem blockDiag_mulVec_inr (A : Matrix (Fin n) (Fin n) R) (C : Matrix κ κ R)
    (y : Fin m → R) (j : κ) :
    (blockDiag e A C *ᵥ y) (e (Sum.inr j)) = (C *ᵥ fun k => y (e (Sum.inr k))) j := by
  rw [blockDiag, Matrix.coe_reindexAlgEquiv, reindex_apply, submatrix_mulVec_equiv]
  simp [fromBlocks_mulVec, Function.comp_def]

/-- `blockDiag e N 1` as a unit. -/
def blockDiagGL (N : GL (Fin n) R) : GL (Fin m) R where
  val := blockDiag e N 1
  inv := blockDiag e (N⁻¹ : GL (Fin n) R) 1
  val_inv := by rw [blockDiag_mul, Units.mul_inv, one_mul, blockDiag_one]
  inv_val := by rw [blockDiag_mul, Units.inv_mul, one_mul, blockDiag_one]

theorem coe_blockDiagGL (N : GL (Fin n) R) :
    ((blockDiagGL e N : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) = blockDiag e N 1 := rfl

theorem blockDiagGL_mul (N N' : GL (Fin n) R) :
    blockDiagGL e (N * N') = blockDiagGL e N * blockDiagGL e N' := by
  ext1; simp [coe_blockDiagGL, blockDiag_mul]

theorem blockDiagGL_inv (N : GL (Fin n) R) : blockDiagGL e N⁻¹ = (blockDiagGL e N)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← blockDiagGL_mul, inv_mul_cancel]
  ext1; simp [coe_blockDiagGL, blockDiag_one]

end Block


section PAdic

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

/-- In block coordinates, `Bᵀ (A ⊕ C) B ≅ A ⊥ C` (Tau Ceti `Matrix.isometryEquivCongr`,
`isometryEquivReindex`, `isometryEquivFromBlocks`). -/
def blockFormIso {m n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ] (e : Fin n ⊕ κ ≃ Fin m)
    (B : GL (Fin m) F) (A : Matrix (Fin n) (Fin n) F) (C : Matrix κ κ F) :
    ((B : Matrix (Fin m) (Fin m) F)ᵀ * blockDiag e A C * B).toQuadraticForm'.IsometryEquiv
      (A.toQuadraticForm'.prod C.toQuadraticForm') :=
  have hBt : IsUnit (B : Matrix (Fin m) (Fin m) F)ᵀ.det := by
    rw [det_transpose]; exact (Matrix.isUnits_det_units B)
  ((Matrix.transpose_transpose (B : Matrix (Fin m) (Fin m) F)) ▸
    Matrix.isometryEquivCongr hBt (blockDiag e A C)).trans
    ((Matrix.isometryEquivReindex e _).trans (Matrix.isometryEquivFromBlocks _ _))

/-- The first block of a nondegenerate form in block coordinates is nondegenerate. -/
theorem isNondeg_of_blockDiag {m n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    {Q : QuadraticForm F (Fin m → F)} (hQ : IsNondeg Q) (e : Fin n ⊕ κ ≃ Fin m) (B : GL (Fin m) F)
    {Q₂ : QuadraticForm F (Fin n → F)} {G₃ : Matrix κ κ F}
    (hB : Q.toMatrix' = (B : Matrix (Fin m) (Fin m) F)ᵀ * blockDiag e Q₂.toMatrix' G₃ * B) :
    IsNondeg Q₂ := by
  have hd := (PAdicQuadAux.isNondeg_iff_discr'_ne_zero Q).1 hQ
  rw [QuadraticForm.discr', hB, det_mul, det_mul, det_transpose, det_blockDiag] at hd
  refine (PAdicQuadAux.isNondeg_iff_discr'_ne_zero _).2 fun h0 => hd ?_
  rw [QuadraticForm.discr'] at h0
  rw [h0]; ring

/-- **Witt cancellation in block coordinates**: replacing the first block `Q₂` by a form `Q₂'` not
isometric to it gives a form not isometric to `Q`. -/
theorem not_nonempty_isometryEquiv_blockForm {m n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    {Q : QuadraticForm F (Fin m → F)} (e : Fin n ⊕ κ ≃ Fin m) (B : GL (Fin m) F)
    {Q₂ Q₂' : QuadraticForm F (Fin n → F)} {G₃ : Matrix κ κ F}
    (hB : Q.toMatrix' = (B : Matrix (Fin m) (Fin m) F)ᵀ * blockDiag e Q₂.toMatrix' G₃ * B)
    (hniso : ¬ Nonempty (Q₂.IsometryEquiv Q₂')) :
    ¬ Nonempty (Q.IsometryEquiv
      ((B : Matrix (Fin m) (Fin m) F)ᵀ * blockDiag e Q₂'.toMatrix' G₃ * B).toQuadraticForm') := by
  rintro ⟨f⟩
  have e₁ : Q.IsometryEquiv (Q₂.toMatrix'.toQuadraticForm'.prod G₃.toQuadraticForm') := by
    have h0 : Q = ((B : Matrix (Fin m) (Fin m) F)ᵀ * blockDiag e Q₂.toMatrix' G₃ *
        B).toQuadraticForm' := by
      rw [← hB, QuadraticForm.toMatrix'_toQuadraticForm']
    exact h0 ▸ blockFormIso e B _ _
  have e₃ := ((((QuadraticMap.IsometryEquiv.prodComm _ _).trans e₁.symm).trans f).trans
    (blockFormIso e B Q₂'.toMatrix' G₃)).trans (QuadraticMap.IsometryEquiv.prodComm _ _)
  obtain ⟨g⟩ := witt_cancellation G₃.toQuadraticForm' _ _ ⟨e₃⟩
  rw [QuadraticForm.toMatrix'_toQuadraticForm', QuadraticForm.toMatrix'_toQuadraticForm'] at g
  exact hniso ⟨g⟩

/-- **Twisting a block, explicitly.**  Suppose that in rational coordinates `B`, `Q` is the orthogonal
sum of a form `Q₂` on `F^n` and a form with Gram matrix `G₃`, and that `Q₂'` has the discriminant of
`Q₂`.  Then `Q' = Bᵀ (Q₂' ⊕ G₃) B` has the discriminant of `Q`, and there is an `F̄`-isometry
`Q_{F̄} ≃ Q'_{F̄}`
with matrix `X` whose cocycle `X⁻¹ σ(X)` is `B⁻¹ (R_σ ⊕ 1) B` with `R_σ ∈ SO(Q₂)(F̄)`, and which
only depends on the restriction of `σ` to a finite extension. -/
theorem exists_blockTwist_core {m : ℕ} {Q : QuadraticForm F (Fin m → F)} (hQ : IsNondeg Q)
    {κ : Type*} [Fintype κ] [DecidableEq κ] {n : ℕ} (e : Fin n ⊕ κ ≃ Fin m) (B : GL (Fin m) F)
    {Q₂ : QuadraticForm F (Fin n → F)} (hQ₂ : IsNondeg Q₂) {Q₂' : QuadraticForm F (Fin n → F)}
    (hnd' : IsNondeg Q₂') (hdr : QuadClassify.DiscRel Q₂ Q₂')
    (G₃ : Matrix κ κ F) (hG₃ : G₃.IsSymm)
    (hB : Q.toMatrix' = (B : Matrix (Fin m) (Fin m) F)ᵀ * blockDiag e Q₂.toMatrix' G₃ * B) :
    ∃ X : GL (Fin m) Kb,
      IsNondeg ((B : Matrix (Fin m) (Fin m) F)ᵀ * blockDiag e Q₂'.toMatrix' G₃ * B).toQuadraticForm' ∧
      SameDisc Q ((B : Matrix (Fin m) (Fin m) F)ᵀ * blockDiag e Q₂'.toMatrix' G₃ *
        B).toQuadraticForm' ∧
      (X : Matrix (Fin m) (Fin m) Kb)ᵀ * ((B : Matrix (Fin m) (Fin m) F)ᵀ *
        blockDiag e Q₂'.toMatrix' G₃ * B).toQuadraticForm'.toMatrix'.map (algebraMap F Kb) * X =
        Q.toMatrix'.map (algebraMap F Kb) ∧
      (∀ σ : GalF F, ∃ R : GL (Fin n) Kb,
        (R : Matrix (Fin n) (Fin n) Kb)ᵀ * Q₂.toMatrix'.map (algebraMap F Kb) * R =
          Q₂.toMatrix'.map (algebraMap F Kb) ∧ (R : Matrix (Fin n) (Fin n) Kb).det = 1 ∧
        X⁻¹ * galGL m σ X = (Units.map (algebraMap F Kb).mapMatrix.toMonoidHom B)⁻¹ *
          blockDiagGL e R * Units.map (algebraMap F Kb).mapMatrix.toMonoidHom B) ∧
      ∃ E : IntermediateField F Kb, FiniteDimensional F E ∧
        ∀ σ τ : GalF F, (∀ x ∈ E, σ x = τ x) → galGL m σ X = galGL m τ X := by
  classical
  have hsd' := (QuadClassify.sameDisc_iff_discRel _ _).2 hdr
  obtain ⟨τ, rfl⟩ := exists_innerTwist_of_sameDisc hQ₂ hnd' hsd'
  set N : GL (Fin n) Kb := TwistDescent.glOf τ.φ with hNdef
  have hN := TwistDescent.gram_glOf τ.φ
  set Bb : GL (Fin m) Kb := Units.map (algebraMap F Kb).mapMatrix.toMonoidHom B with hBbdef
  set D := blockDiag e Q₂.toMatrix' G₃ with hDdef
  set D' := blockDiag e τ.Q'.toMatrix' G₃ with hD'def
  have hsym₂ : (Q₂.toMatrix')ᵀ = Q₂.toMatrix' := QuadraticForm.isSymm_toMatrix' Q₂
  have hsym₂' : (τ.Q'.toMatrix')ᵀ = τ.Q'.toMatrix' := QuadraticForm.isSymm_toMatrix' τ.Q'
  have hD'sym : D'ᵀ = D' := by rw [hD'def, blockDiag_transpose, hsym₂', hG₃.eq]
  set M' := (B : Matrix (Fin m) (Fin m) F)ᵀ * D' * B with hM'def
  have hM'sym : M'ᵀ = M' := by
    rw [hM'def, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hD'sym,
      Matrix.mul_assoc]
  obtain ⟨c, hc0, hc⟩ := hsd'
  have hdisc : M'.toQuadraticForm'.discr' = c ^ 2 * Q.discr' := by
    rw [QuadraticForm.discr', Matrix.toMatrix'_toQuadraticForm' hM'sym, QuadraticForm.discr', hB,
      hM'def, det_mul, det_mul, det_mul,
      det_mul, det_transpose, hD'def, hDdef, det_blockDiag, det_blockDiag]
    rw [QuadraticForm.discr', QuadraticForm.discr'] at hc
    rw [hc]; ring
  have hQd : Q.discr' ≠ 0 := (PAdicQuadAux.isNondeg_iff_discr'_ne_zero Q).1 hQ
  have hgalBb : ∀ σ : GalF F, galGL m σ Bb = Bb := fun σ => by
    ext i j; simp [coe_galGL, hBbdef]
  have hgalbd : ∀ σ : GalF F, galGL m σ (blockDiagGL e N) = blockDiagGL e (galGL n σ N) :=
    fun σ => by
      ext1
      rw [coe_galGL, coe_blockDiagGL, coe_blockDiagGL, coe_galGL]
      exact (blockDiag_map e (σ : Kb →+* Kb) _ _).trans (by
        rw [Matrix.map_one _ (map_zero _) (map_one _)]; rfl)
  refine ⟨Bb⁻¹ * blockDiagGL e N * Bb,
    (PAdicQuadAux.isNondeg_iff_discr'_ne_zero _).2
      (by rw [hdisc]; exact mul_ne_zero (pow_ne_zero 2 hc0) hQd),
    ⟨c, hc0, hdisc⟩, ?_, ?_, ?_⟩
  · -- the Gram relation
    have hBb : (Bb : Matrix (Fin m) (Fin m) Kb) =
        (B : Matrix (Fin m) (Fin m) F).map (algebraMap F Kb) :=
      rfl
    have hinv : ((Bb⁻¹ : GL (Fin m) Kb) : Matrix (Fin m) (Fin m) Kb)ᵀ * (Bb : Matrix _ _ Kb)ᵀ = 1 :=
        by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    have hblk : ((blockDiagGL e N : GL (Fin m) Kb) : Matrix (Fin m) (Fin m) Kb)ᵀ *
        D'.map (algebraMap F Kb) * (blockDiagGL e N : GL (Fin m) Kb) = D.map (algebraMap F Kb) := by
      rw [coe_blockDiagGL, hD'def, hDdef, blockDiag_map, blockDiag_map, blockDiag_transpose,
        blockDiag_mul, blockDiag_mul, hN]
      simp
    rw [Matrix.toMatrix'_toQuadraticForm' hM'sym, hM'def, hB, Matrix.map_mul, Matrix.map_mul,
      Matrix.map_mul,
      Matrix.map_mul, Matrix.transpose_map, ← hBb]
    simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    have hinv' : (Bb : Matrix (Fin m) (Fin m) Kb) * ((Bb⁻¹ : GL (Fin m) Kb) : Matrix _ _ Kb) = 1 :=
      Units.mul_inv Bb
    rw [← Matrix.mul_assoc (((Bb⁻¹ : GL (Fin m) Kb) : Matrix (Fin m) (Fin m) Kb)ᵀ), hinv,
      Matrix.one_mul, ← Matrix.mul_assoc (Bb : Matrix (Fin m) (Fin m) Kb), hinv', Matrix.one_mul,
      ← hblk]
    simp only [Matrix.mul_assoc]
  · -- the cocycle
    intro σ
    refine ⟨N⁻¹ * galGL n σ N, ?_, TwistDescent.det_glOf_inv_mul_galGL τ σ, ?_⟩
    · have hσ : ((galGL n σ N : GL (Fin n) Kb) : Matrix (Fin n) (Fin n) Kb)ᵀ *
          τ.Q'.toMatrix'.map (algebraMap F Kb) * (galGL n σ N : GL (Fin n) Kb) =
          Q₂.toMatrix'.map (algebraMap F Kb) := by
        have := congrArg (Matrix.map · σ) hN
        simp only [TwistDescent.map_galF_mul, Matrix.transpose_map,
          TwistDescent.map_algebraMap_fixed] at this
        rw [coe_galGL]; exact this
      have hN' : ((N⁻¹ : GL (Fin n) Kb) : Matrix (Fin n) (Fin n) Kb)ᵀ *
          Q₂.toMatrix'.map (algebraMap F Kb) * (N⁻¹ : GL (Fin n) Kb) =
          τ.Q'.toMatrix'.map (algebraMap F Kb) := by
        have h1 : ((N⁻¹ : GL (Fin n) Kb) : Matrix (Fin n) (Fin n) Kb)ᵀ *
            (N : Matrix (Fin n) (Fin n) Kb)ᵀ = 1 := by
          rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
        have h2 : (N : Matrix (Fin n) (Fin n) Kb) * ((N⁻¹ : GL (Fin n) Kb) : Matrix _ _ Kb) = 1 :=
          Units.mul_inv N
        rw [← hN]
        calc _ = (((N⁻¹ : GL (Fin n) Kb) : Matrix (Fin n) (Fin n) Kb)ᵀ *
              (N : Matrix (Fin n) (Fin n) Kb)ᵀ) * τ.Q'.toMatrix'.map (algebraMap F Kb) *
              ((N : Matrix (Fin n) (Fin n) Kb) * ((N⁻¹ : GL (Fin n) Kb) : Matrix _ _ Kb)) := by
                simp only [Matrix.mul_assoc]; rfl
          _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
      rw [Units.val_mul, Matrix.transpose_mul]
      calc _ = ((galGL n σ N : GL (Fin n) Kb) : Matrix (Fin n) (Fin n) Kb)ᵀ *
            (((N⁻¹ : GL (Fin n) Kb) : Matrix (Fin n) (Fin n) Kb)ᵀ *
              Q₂.toMatrix'.map (algebraMap F Kb) * (N⁻¹ : GL (Fin n) Kb)) *
            (galGL n σ N : GL (Fin n) Kb) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hN', hσ]
    · rw [map_mul, map_mul, map_inv, hgalBb, hgalbd, blockDiagGL_mul, blockDiagGL_inv]
      group
  · obtain ⟨E, hE, hEf⟩ := exists_finite_fixing_matrix (N : Matrix (Fin n) (Fin n) Kb)
    refine ⟨E, hE, fun σ τ' h => ?_⟩
    have hNστ : galGL n σ N = galGL n τ' N :=
      Units.ext (by rw [coe_galGL, coe_galGL]; exact hEf σ τ' h)
    rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hgalBb, hgalBb, hgalbd, hgalbd,
      hNστ]


/-- **Twisting a block.**  Suppose that in rational coordinates `B`, `Q` is the orthogonal sum of a
form `Q₂` on `F^n` and a form with Gram matrix `G₃`, and that `Q₂'` has the discriminant of `Q₂` but
is not isometric to it.  Then there is
a form `Q'` of the same discriminant, not isometric to `Q`, and an `F̄`-isometry `Q_{F̄} ≃ Q'_{F̄}`
with matrix `X` whose cocycle `X⁻¹ σ(X)` is `B⁻¹ (R_σ ⊕ 1) B` with `R_σ ∈ SO(Q₂)(F̄)`, and which
only depends on the restriction of `σ` to a finite extension. -/
theorem exists_blockTwist {m : ℕ} {Q : QuadraticForm F (Fin m → F)} (hQ : IsNondeg Q)
    {κ : Type*} [Fintype κ] [DecidableEq κ] {n : ℕ} (e : Fin n ⊕ κ ≃ Fin m) (B : GL (Fin m) F)
    {Q₂ : QuadraticForm F (Fin n → F)} (hQ₂ : IsNondeg Q₂) {Q₂' : QuadraticForm F (Fin n → F)}
    (hnd' : IsNondeg Q₂') (hdr : QuadClassify.DiscRel Q₂ Q₂') (hniso : ¬ Nonempty (Q₂.IsometryEquiv Q₂'))
    (G₃ : Matrix κ κ F) (hG₃ : G₃.IsSymm)
    (hB : Q.toMatrix' = (B : Matrix (Fin m) (Fin m) F)ᵀ * blockDiag e Q₂.toMatrix' G₃ * B) :
    ∃ (Q' : QuadraticForm F (Fin m → F)) (X : GL (Fin m) Kb),
      IsNondeg Q' ∧ SameDisc Q Q' ∧ ¬ Nonempty (Q.IsometryEquiv Q') ∧
      (X : Matrix (Fin m) (Fin m) Kb)ᵀ * Q'.toMatrix'.map (algebraMap F Kb) * X =
        Q.toMatrix'.map (algebraMap F Kb) ∧
      (∀ σ : GalF F, ∃ R : GL (Fin n) Kb,
        (R : Matrix (Fin n) (Fin n) Kb)ᵀ * Q₂.toMatrix'.map (algebraMap F Kb) * R =
          Q₂.toMatrix'.map (algebraMap F Kb) ∧ (R : Matrix (Fin n) (Fin n) Kb).det = 1 ∧
        X⁻¹ * galGL m σ X = (Units.map (algebraMap F Kb).mapMatrix.toMonoidHom B)⁻¹ *
          blockDiagGL e R * Units.map (algebraMap F Kb).mapMatrix.toMonoidHom B) ∧
      ∃ E : IntermediateField F Kb, FiniteDimensional F E ∧
        ∀ σ τ : GalF F, (∀ x ∈ E, σ x = τ x) → galGL m σ X = galGL m τ X := by
  obtain ⟨X, hnd, hsd, hgram, hcoc, hE⟩ := exists_blockTwist_core hQ e B hQ₂ hnd' hdr G₃ hG₃ hB
  exact ⟨_, X, hnd, hsd, not_nonempty_isometryEquiv_blockForm e B hB hniso, hgram, hcoc, hE⟩

/-- **Twisting an anisotropic plane.**  Suppose that in rational coordinates `B`, `Q` is the
orthogonal sum of an anisotropic binary form `Q₂` and a form with Gram matrix `G₃`.  Then there is
a form `Q'` of the same discriminant, not isometric to `Q`, and an `F̄`-isometry `Q_{F̄} ≃ Q'_{F̄}`
with matrix `X` whose cocycle `X⁻¹ σ(X)` is `B⁻¹ (R_σ ⊕ 1) B` with `R_σ ∈ SO(Q₂)(F̄)`, and which
only depends on the restriction of `σ` to a finite extension. -/
theorem exists_planeTwist {m : ℕ} {Q : QuadraticForm F (Fin m → F)} (hQ : IsNondeg Q)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (e : Fin 2 ⊕ κ ≃ Fin m) (B : GL (Fin m) F)
    {Q₂ : QuadraticForm F (Fin 2 → F)} (hQ₂ : IsNondeg Q₂) (haniso : ∀ v, Q₂ v = 0 → v = 0)
    (G₃ : Matrix κ κ F) (hG₃ : G₃.IsSymm)
    (hB : Q.toMatrix' = (B : Matrix (Fin m) (Fin m) F)ᵀ * blockDiag e Q₂.toMatrix' G₃ * B) :
    ∃ (Q' : QuadraticForm F (Fin m → F)) (X : GL (Fin m) Kb),
      IsNondeg Q' ∧ SameDisc Q Q' ∧ ¬ Nonempty (Q.IsometryEquiv Q') ∧
      (X : Matrix (Fin m) (Fin m) Kb)ᵀ * Q'.toMatrix'.map (algebraMap F Kb) * X =
        Q.toMatrix'.map (algebraMap F Kb) ∧
      (∀ σ : GalF F, ∃ R : GL (Fin 2) Kb,
        (R : Matrix (Fin 2) (Fin 2) Kb)ᵀ * Q₂.toMatrix'.map (algebraMap F Kb) * R =
          Q₂.toMatrix'.map (algebraMap F Kb) ∧ (R : Matrix (Fin 2) (Fin 2) Kb).det = 1 ∧
        X⁻¹ * galGL m σ X = (Units.map (algebraMap F Kb).mapMatrix.toMonoidHom B)⁻¹ *
          blockDiagGL e R * Units.map (algebraMap F Kb).mapMatrix.toMonoidHom B) ∧
      ∃ E : IntermediateField F Kb, FiniteDimensional F E ∧
        ∀ σ τ : GalF F, (∀ x ∈ E, σ x = τ x) → galGL m σ X = galGL m τ X := by
  obtain ⟨Q₂', hnd', hdr, hniso⟩ := WittParity.exists_other_class_plane hQ₂ haniso
  exact exists_blockTwist hQ e B hQ₂ hnd' hdr hniso G₃ hG₃ hB

end PAdic

end TwistPlane

end GSpinGGP
