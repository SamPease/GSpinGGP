/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TwistDescent
import GSpinGGP.Foundations.PAdicQuadraticForms

/-!
# Twisting an anisotropic plane

Let `Q` be a nondegenerate quadratic form on `F^m` (`F` a `p`-adic field) that splits, in a
rational basis, as `Q₂ ⊥ Q₃` with `Q₂` an anisotropic binary form.  There is a form `Q*` of the
same discriminant that is *not* isometric to `Q`, together with an `F̄`-isometry `Q_{F̄} ≃ Q*_{F̄}`
whose cocycle `σ ↦ X⁻¹ σ(X)` acts on the plane by elements of `SO(Q₂)(F̄)` and trivially on its
orthogonal (Thesis Prop. 6.5.1(iv): twisting `W''_x` along the anisotropic torus `S_x`).

* `exists_isotropic_of_isSquare_neg_discr`: a binary form whose `−det` is a square is isotropic.
* `exists_nonisometric_plane`: an anisotropic binary form has a non-isometric form of the same
  discriminant (`padic_quadratic_classes`, `m = 2`).
-/

noncomputable section

open Matrix

namespace GSpinGGP

section Binary

variable {K : Type*} [Field K] [Invertible (2 : K)]

/-- The quadratic form `v ↦ vᵀ N v`. -/
def formOf {n : Type*} [Fintype n] [DecidableEq n] (N : Matrix n n K) : QuadraticForm K (n → K) :=
  LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' K N)

omit [Invertible (2 : K)] in
theorem formOf_apply {n : Type*} [Fintype n] [DecidableEq n] (N : Matrix n n K) (v : n → K) :
    formOf N v = v ⬝ᵥ (N *ᵥ v) := by
  simp [formOf, Matrix.toLinearMap₂'_apply']

theorem formOf_toMatrix' {n : Type*} [Fintype n] [DecidableEq n] (Q : QuadraticForm K (n → K)) :
    formOf Q.toMatrix' = Q := by
  rw [formOf, QuadraticForm.toMatrix',
    show Matrix.toLinearMap₂' K (LinearMap.toMatrix₂' K (QuadraticMap.associated Q)) =
      QuadraticMap.associated Q from (LinearMap.toMatrix₂' K).symm_apply_apply _,
    QuadraticMap.toQuadraticMap_associated]

theorem apply_eq_dotProduct_toMatrix' {n : Type*} [Fintype n] [DecidableEq n]
    (Q : QuadraticForm K (n → K)) (v : n → K) : Q v = v ⬝ᵥ (Q.toMatrix' *ᵥ v) := by
  conv_lhs => rw [← formOf_toMatrix' Q]
  exact formOf_apply _ v

theorem toMatrix'_formOf {n : Type*} [Fintype n] [DecidableEq n] {N : Matrix n n K}
    (hN : Nᵀ = N) : (formOf N).toMatrix' = N := by
  have hsym : ∀ x y : n → K, Matrix.toLinearMap₂' K N x y = Matrix.toLinearMap₂' K N y x := by
    intro x y
    rw [Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_apply', Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hN, dotProduct_comm]
  rw [formOf, QuadraticForm.toMatrix', QuadraticMap.associated_left_inverse K hsym]
  exact (LinearMap.toMatrix₂' K).apply_symm_apply N

/-- A binary form whose `−det` is a square is isotropic. -/
theorem exists_isotropic_of_isSquare_neg_discr {Q : QuadraticForm K (Fin 2 → K)}
    (h : IsSquare (-Q.discr')) : ∃ v ≠ 0, Q v = 0 := by
  obtain ⟨s, hs⟩ := h
  set G := Q.toMatrix'
  have hsym : G 1 0 = G 0 1 := (QuadraticForm.isSymm_toMatrix' Q).apply 0 1
  have hdet : Q.discr' = G 0 0 * G 1 1 - G 0 1 * G 1 0 := by
    rw [QuadraticForm.discr', Matrix.det_fin_two]
  have hQ : ∀ v : Fin 2 → K, Q v = v 0 * v 0 * G 0 0 + v 0 * v 1 * (G 0 1 + G 1 0) +
      v 1 * v 1 * G 1 1 := fun v => by
    rw [apply_eq_dotProduct_toMatrix']
    simp only [dotProduct, mulVec, Fin.sum_univ_two]
    ring
  by_cases ha : G 0 0 = 0
  · refine ⟨![1, 0], by simp [funext_iff], ?_⟩
    rw [hQ]; simp [ha]
  · refine ⟨![s - G 0 1, G 0 0], fun h0 => ha (by simpa using congrFun h0 1), ?_⟩
    rw [hQ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [hsym] at hdet ⊢
    linear_combination (-G 0 0) * hs - G 0 0 * hdet

end Binary

section Block

variable {R : Type*} [CommRing R] {κ : Type*} [Fintype κ] [DecidableEq κ] {m : ℕ}
  (e : Fin 2 ⊕ κ ≃ Fin m)

/-- The block-diagonal matrix `A ⊕ C` in the coordinates `e : Fin 2 ⊕ κ ≃ Fin m`. -/
def blockDiag (A : Matrix (Fin 2) (Fin 2) R) (C : Matrix κ κ R) : Matrix (Fin m) (Fin m) R :=
  Matrix.reindexAlgEquiv R R e (fromBlocks A 0 0 C)

theorem blockDiag_mul (A A' : Matrix (Fin 2) (Fin 2) R) (C C' : Matrix κ κ R) :
    blockDiag e A C * blockDiag e A' C' = blockDiag e (A * A') (C * C') := by
  simp [blockDiag, fromBlocks_multiply]

theorem blockDiag_transpose (A : Matrix (Fin 2) (Fin 2) R) (C : Matrix κ κ R) :
    (blockDiag e A C)ᵀ = blockDiag e Aᵀ Cᵀ := by
  simp [blockDiag, Matrix.coe_reindexAlgEquiv, fromBlocks_transpose]

theorem blockDiag_one : blockDiag e (1 : Matrix (Fin 2) (Fin 2) R) (1 : Matrix κ κ R) = 1 := by
  simp [blockDiag, fromBlocks_one]

theorem det_blockDiag (A : Matrix (Fin 2) (Fin 2) R) (C : Matrix κ κ R) :
    (blockDiag e A C).det = A.det * C.det := by
  simp [blockDiag, Matrix.coe_reindexAlgEquiv, det_fromBlocks_zero₂₁]

theorem blockDiag_map {S : Type*} [CommRing S] (f : R →+* S) (A : Matrix (Fin 2) (Fin 2) R)
    (C : Matrix κ κ R) : (blockDiag e A C).map f = blockDiag e (A.map f) (C.map f) := by
  ext i j
  simp only [blockDiag, Matrix.coe_reindexAlgEquiv, map_apply, reindex_apply, submatrix_apply]
  rcases e.symm i with a | a <;> rcases e.symm j with b | b <;> simp

/-- `blockDiag e N 1` as a unit. -/
def blockDiagGL (N : GL (Fin 2) R) : GL (Fin m) R where
  val := blockDiag e N 1
  inv := blockDiag e (N⁻¹ : GL (Fin 2) R) 1
  val_inv := by rw [blockDiag_mul, Units.mul_inv, one_mul, blockDiag_one]
  inv_val := by rw [blockDiag_mul, Units.inv_mul, one_mul, blockDiag_one]

theorem coe_blockDiagGL (N : GL (Fin 2) R) :
    ((blockDiagGL e N : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) = blockDiag e N 1 := rfl

theorem blockDiagGL_mul (N N' : GL (Fin 2) R) :
    blockDiagGL e (N * N') = blockDiagGL e N * blockDiagGL e N' := by
  ext1; simp [coe_blockDiagGL, blockDiag_mul]

theorem blockDiagGL_inv (N : GL (Fin 2) R) : blockDiagGL e N⁻¹ = (blockDiagGL e N)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← blockDiagGL_mul, inv_mul_cancel]
  ext1; simp [coe_blockDiagGL, blockDiag_one]

end Block

section FormOf

variable {K : Type*} [Field K] [Invertible (2 : K)]

omit [Invertible (2 : K)] in
theorem formOf_mul {n : Type*} [Fintype n] [DecidableEq n] (N P : Matrix n n K) (v : n → K) :
    formOf (Pᵀ * N * P) v = formOf N (P *ᵥ v) := by
  rw [formOf_apply, formOf_apply, ← mulVec_mulVec, ← mulVec_mulVec, Matrix.dotProduct_mulVec,
    vecMul_transpose]

theorem discr'_formOf {n : Type*} [Fintype n] [DecidableEq n] {N : Matrix n n K} (hN : Nᵀ = N) :
    (formOf N).discr' = N.det := by
  rw [QuadraticForm.discr', toMatrix'_formOf hN]

/-- A change of coordinates by an invertible matrix is an isometry `formOf (Pᵀ N P) ≃ formOf N`. -/
def formOfMulEquiv {n : Type*} [Fintype n] [DecidableEq n] (N : Matrix n n K) (P : GL n K) :
    (formOf ((P : Matrix n n K)ᵀ * N * (P : Matrix n n K))).IsometryEquiv (formOf N) where
  toLinearEquiv := Matrix.toLinearEquiv' (P : Matrix n n K) (Units.isUnit P).invertible
  map_app' v := by
    rw [formOf_mul]
    rfl

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {m : ℕ} (e : Fin 2 ⊕ κ ≃ Fin m)

/-- A block-diagonal form is the orthogonal sum of its blocks. -/
def formOfBlockDiagEquiv (A : Matrix (Fin 2) (Fin 2) K) (C : Matrix κ κ K) :
    (formOf (blockDiag e A C)).IsometryEquiv ((formOf A).prod (formOf C)) where
  toLinearEquiv :=
    (LinearEquiv.funCongrLeft K K e).trans (LinearEquiv.sumArrowLequivProdArrow _ _ K K)
  map_app' v := by
    have h : v ⬝ᵥ (blockDiag e A C *ᵥ v) = (v ∘ e) ⬝ᵥ (fromBlocks A 0 0 C *ᵥ (v ∘ e)) := by
      rw [blockDiag, Matrix.coe_reindexAlgEquiv, reindex_apply, submatrix_mulVec_equiv,
        dotProduct_comp_equiv_symm, Equiv.symm_symm]
    rw [formOf_apply, h, fromBlocks_mulVec, ← Sum.elim_comp_inl_inr (v ∘ e),
      sumElim_dotProduct_sumElim]
    simp only [QuadraticMap.prod_apply, formOf_apply, zero_mulVec, add_zero, zero_add]
    rfl

end FormOf

section PAdic

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- An anisotropic binary form over a `p`-adic field has a non-isometric form of the same
discriminant (`padic_quadratic_classes`: for `m = 2` there are two classes iff `−det` is not a
square). -/
theorem exists_nonisometric_plane {Q : QuadraticForm F (Fin 2 → F)} (hQ : IsNondeg Q)
    (haniso : ∀ v, Q v = 0 → v = 0) :
    ∃ Q' : QuadraticForm F (Fin 2 → F), IsNondeg Q' ∧ SameDisc Q Q' ∧
      ¬ Nonempty (Q.IsometryEquiv Q') := by
  obtain ⟨n, R, i₀, hR0, hRnd, huniq, -, -, h2, hn2⟩ := padic_quadratic_classes Q hQ
  have hsq : ¬ IsSquare (-Q.discr') := fun h => by
    obtain ⟨v, hv, hQv⟩ := exists_isotropic_of_isSquare_neg_discr h
    exact hv (haniso v hQv)
  have hn : n = 2 := by
    have h1 : n ≠ 1 := fun h => hsq ((h2 rfl).1 h)
    have := i₀.2
    omega
  subst hn
  set i : Fin 2 := if i₀ = 0 then 1 else 0 with hi
  have hii : i ≠ i₀ := by fin_cases i₀ <;> simp [hi]
  refine ⟨R i, (hRnd i).1, (hRnd i).2, fun ⟨e⟩ => hii ?_⟩
  have hself : SameDisc Q Q := hR0 ▸ (hRnd i₀).2
  obtain ⟨j, -, hj⟩ := huniq Q hQ hself
  rw [hj i ⟨e⟩, hj i₀ ⟨hR0 ▸ QuadraticMap.IsometryEquiv.refl _⟩]

local notation "Kb" => AlgebraicClosure F

omit [PAdicField F] in
/-- The entries of a matrix over `F̄` lie in a finite extension, so `σ ↦ σ(X)` only depends on
the restriction of `σ` to it (continuity for the Krull topology). -/
theorem exists_finite_fixing_matrix {n : Type*} [Finite n] (X : Matrix n n Kb) :
    ∃ E : IntermediateField F Kb, FiniteDimensional F E ∧
      ∀ σ τ : GalF F, (∀ x ∈ E, σ x = τ x) → X.map σ = X.map τ := by
  refine ⟨IntermediateField.adjoin F (Set.range fun p : n × n => X p.1 p.2),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x,
    fun σ τ h => ?_⟩
  ext i j
  exact h _ (IntermediateField.subset_adjoin _ _ ⟨(i, j), rfl⟩)

/-- The determinant cocycle of an inner twist, in matrices. -/
theorem det_glOf_inv_mul_galGL {m : ℕ} {Q : QuadraticForm F (Fin m → F)} (τ : InnerTwist Q)
    (σ : GalF F) :
    (((TwistDescent.glOf τ.φ)⁻¹ * galGL m σ (TwistDescent.glOf τ.φ) : GL (Fin m) Kb) :
      Matrix (Fin m) (Fin m) Kb).det = 1 := by
  have h := τ.cocycle σ
  rw [← LinearMap.det_toMatrix (bcBasis F m), LinearMap.toMatrix_comp _ (bcBasis F m),
    TwistDescent.toMatrix_galoisConj] at h
  rw [Units.val_mul, coe_galGL, TwistDescent.coe_glOf, TwistDescent.coe_glOf_inv]
  exact h

/-- **Twisting an anisotropic plane.**  Suppose that in rational coordinates `B`, `Q` is the
orthogonal sum of an anisotropic binary form `Q₂` and a form with Gram matrix `G₃`.  Then there is
a form `Q'` of the same discriminant, not isometric to `Q`, and an `F̄`-isometry `Q_{F̄} ≃ Q'_{F̄}`
with matrix `X` whose cocycle `X⁻¹ σ(X)` is `B⁻¹ (R_σ ⊕ 1) B` with `R_σ ∈ SO(Q₂)(F̄)`, and which
only depends on the restriction of `σ` to a finite extension. -/
theorem exists_planeTwist {m : ℕ} {Q : QuadraticForm F (Fin m → F)} (hQ : IsNondeg Q)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (e : Fin 2 ⊕ κ ≃ Fin m) (B : GL (Fin m) F)
    {Q₂ : QuadraticForm F (Fin 2 → F)} (hQ₂ : IsNondeg Q₂) (haniso : ∀ v, Q₂ v = 0 → v = 0)
    (G₃ : Matrix κ κ F) (hG₃ : G₃ᵀ = G₃)
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
  classical
  obtain ⟨Q₂', hnd', hsd', hniso⟩ := exists_nonisometric_plane hQ₂ haniso
  obtain ⟨τ, rfl⟩ := exists_innerTwist_of_sameDisc hQ₂ hnd' hsd'
  set N : GL (Fin 2) Kb := TwistDescent.glOf τ.φ with hNdef
  have hN := TwistDescent.gram_glOf τ.φ
  set Bb : GL (Fin m) Kb := Units.map (algebraMap F Kb).mapMatrix.toMonoidHom B with hBbdef
  set D := blockDiag e Q₂.toMatrix' G₃ with hDdef
  set D' := blockDiag e τ.Q'.toMatrix' G₃ with hD'def
  have hsym₂ : (Q₂.toMatrix')ᵀ = Q₂.toMatrix' := QuadraticForm.isSymm_toMatrix' Q₂
  have hsym₂' : (τ.Q'.toMatrix')ᵀ = τ.Q'.toMatrix' := QuadraticForm.isSymm_toMatrix' τ.Q'
  have hD'sym : D'ᵀ = D' := by rw [hD'def, blockDiag_transpose, hsym₂', hG₃]
  set M' := (B : Matrix (Fin m) (Fin m) F)ᵀ * D' * B with hM'def
  have hM'sym : M'ᵀ = M' := by
    rw [hM'def, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hD'sym,
      Matrix.mul_assoc]
  obtain ⟨c, hc0, hc⟩ := hsd'
  have hdisc : (formOf M').discr' = c ^ 2 * Q.discr' := by
    rw [discr'_formOf hM'sym, QuadraticForm.discr', hB, hM'def, det_mul, det_mul, det_mul,
      det_mul, det_transpose, hD'def, hDdef, det_blockDiag, det_blockDiag]
    rw [QuadraticForm.discr', QuadraticForm.discr'] at hc
    rw [hc]; ring
  have hQd : Q.discr' ≠ 0 := (PAdicQuadAux.isNondeg_iff_discr'_ne_zero Q).1 hQ
  have hgalBb : ∀ σ : GalF F, galGL m σ Bb = Bb := fun σ => by
    ext i j; simp [coe_galGL, hBbdef]
  have hgalbd : ∀ σ : GalF F, galGL m σ (blockDiagGL e N) = blockDiagGL e (galGL 2 σ N) :=
    fun σ => by
      ext1
      rw [coe_galGL, coe_blockDiagGL, coe_blockDiagGL, coe_galGL]
      exact (blockDiag_map e (σ : Kb →+* Kb) _ _).trans (by
        rw [Matrix.map_one _ (map_zero _) (map_one _)]; rfl)
  refine ⟨formOf M', Bb⁻¹ * blockDiagGL e N * Bb,
    (PAdicQuadAux.isNondeg_iff_discr'_ne_zero _).2
      (by rw [hdisc]; exact mul_ne_zero (pow_ne_zero 2 hc0) hQd),
    ⟨c, hc0, hdisc⟩, ?_, ?_, ?_, ?_⟩
  · -- not isometric: Witt cancellation
    rintro ⟨f⟩
    have e₁ : (Q.IsometryEquiv ((formOf Q₂.toMatrix').prod (formOf G₃))) := by
      have h0 : Q = formOf ((B : Matrix (Fin m) (Fin m) F)ᵀ * D * (B : Matrix (Fin m) (Fin m) F)) :=
          by
        rw [← hB, formOf_toMatrix']
      exact h0 ▸ (formOfMulEquiv D B).trans (formOfBlockDiagEquiv e _ _)
    have e₂ : ((formOf M').IsometryEquiv ((formOf τ.Q'.toMatrix').prod (formOf G₃))) :=
      (formOfMulEquiv D' B).trans (formOfBlockDiagEquiv e _ _)
    have e₃ := ((((QuadraticMap.IsometryEquiv.prodComm _ _).trans e₁.symm).trans f).trans
      e₂).trans (QuadraticMap.IsometryEquiv.prodComm _ _)
    obtain ⟨g⟩ := witt_cancellation (formOf G₃) _ _ ⟨e₃⟩
    rw [formOf_toMatrix', formOf_toMatrix'] at g
    exact hniso ⟨g⟩
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
    rw [toMatrix'_formOf hM'sym, hM'def, hB, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
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
    refine ⟨N⁻¹ * galGL 2 σ N, ?_, det_glOf_inv_mul_galGL τ σ, ?_⟩
    · have hσ : ((galGL 2 σ N : GL (Fin 2) Kb) : Matrix (Fin 2) (Fin 2) Kb)ᵀ *
          τ.Q'.toMatrix'.map (algebraMap F Kb) * (galGL 2 σ N : GL (Fin 2) Kb) =
          Q₂.toMatrix'.map (algebraMap F Kb) := by
        have := congrArg (Matrix.map · σ) hN
        simp only [TwistDescent.map_galF_mul, Matrix.transpose_map,
          TwistDescent.map_algebraMap_fixed] at this
        rw [coe_galGL]; exact this
      have hN' : ((N⁻¹ : GL (Fin 2) Kb) : Matrix (Fin 2) (Fin 2) Kb)ᵀ *
          Q₂.toMatrix'.map (algebraMap F Kb) * (N⁻¹ : GL (Fin 2) Kb) =
          τ.Q'.toMatrix'.map (algebraMap F Kb) := by
        have h1 : ((N⁻¹ : GL (Fin 2) Kb) : Matrix (Fin 2) (Fin 2) Kb)ᵀ *
            (N : Matrix (Fin 2) (Fin 2) Kb)ᵀ = 1 := by
          rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
        have h2 : (N : Matrix (Fin 2) (Fin 2) Kb) * ((N⁻¹ : GL (Fin 2) Kb) : Matrix _ _ Kb) = 1 :=
          Units.mul_inv N
        rw [← hN]
        calc _ = (((N⁻¹ : GL (Fin 2) Kb) : Matrix (Fin 2) (Fin 2) Kb)ᵀ *
              (N : Matrix (Fin 2) (Fin 2) Kb)ᵀ) * τ.Q'.toMatrix'.map (algebraMap F Kb) *
              ((N : Matrix (Fin 2) (Fin 2) Kb) * ((N⁻¹ : GL (Fin 2) Kb) : Matrix _ _ Kb)) := by
                simp only [Matrix.mul_assoc]; rfl
          _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
      rw [Units.val_mul, Matrix.transpose_mul]
      calc _ = ((galGL 2 σ N : GL (Fin 2) Kb) : Matrix (Fin 2) (Fin 2) Kb)ᵀ *
            (((N⁻¹ : GL (Fin 2) Kb) : Matrix (Fin 2) (Fin 2) Kb)ᵀ *
              Q₂.toMatrix'.map (algebraMap F Kb) * (N⁻¹ : GL (Fin 2) Kb)) *
            (galGL 2 σ N : GL (Fin 2) Kb) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hN', hσ]
    · rw [map_mul, map_mul, map_inv, hgalBb, hgalbd, blockDiagGL_mul, blockDiagGL_inv]
      group
  · obtain ⟨E, hE, hEf⟩ := exists_finite_fixing_matrix (N : Matrix (Fin 2) (Fin 2) Kb)
    refine ⟨E, hE, fun σ τ' h => ?_⟩
    have hNστ : galGL 2 σ N = galGL 2 τ' N :=
      Units.ext (by rw [coe_galGL, coe_galGL]; exact hEf σ τ' h)
    rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hgalBb, hgalBb, hgalbd, hgalbd,
      hNστ]


end PAdic

end GSpinGGP
