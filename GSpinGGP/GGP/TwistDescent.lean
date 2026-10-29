/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.Kottwitz
import GSpinGGP.Literature.GSpin

/-!
# Galois descent for twisted quadratic forms

Own work (standard descent; Serre, *Cohomologie galoisienne*, III §1; Serre, *Local Fields*,
X §2), used for `Main.existsUnique_twistIdx` (the map
`q_x : H¹(F, S_x) → H¹(F, SO(W))` is well defined).  Everything is in the rational basis
`bcBasis` of `F̄ ⊗ F^m`, where an `F̄`-isometry `Q_{F̄} ≃ Q'_{F̄}` is a matrix `X` with
`Xᵀ G' X = G` (`isometry_iff_matrix`) and the cocycle of `IsTwistBy` is `σ ↦ X⁻¹ σ(X)`
(`isTwistBy_iff`).

* `nonempty_isometryEquiv_of_rel`: cohomologous `O(Q)`-valued cocycles twist `Q` into isometric
  forms (the comparison isometry is Galois-invariant, hence rational).
* `exists_twist_of_split`: an `SO(Q)`-valued cocycle `a_σ = M⁻¹ σ(M)` that splits in `GL_m(F̄)`
  is the cocycle of a rational form of the discriminant of `Q` (Gram matrix `M⁻ᵀ G M⁻¹`).
  The splitting is Hilbert 90 for `GL_m` (`Literature/Hilbert90.lean`).
* `isTwistBy_of_isometryEquiv`: `IsTwistBy` only depends on the rational class of the target.

The fixed field of `Aut(F̄/F)` is `F` because `F` has characteristic `0`
(Mathlib `InfiniteGalois.mem_range_algebraMap_iff_fixed`, `IsAlgClosure.isGalois`).
-/

noncomputable section
open scoped Classical TensorProduct
open Matrix
set_option linter.unusedSectionVars false

namespace GSpinGGP
namespace TwistDescent

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

/-- A quadratic form on `R^n` (`2` invertible) is determined by its matrix. -/
theorem toMatrix'_injective {R : Type*} [CommRing R] [Invertible (2 : R)] {n : ℕ}
    {Q₁ Q₂ : QuadraticForm R (Fin n → R)} (h : Q₁.toMatrix' = Q₂.toMatrix') : Q₁ = Q₂ := by
  have h' : QuadraticMap.associated (R := R) Q₁ = QuadraticMap.associated (R := R) Q₂ :=
    (LinearMap.toMatrix₂' R).injective h
  rw [← QuadraticMap.toQuadraticMap_associated R Q₁, ← QuadraticMap.toQuadraticMap_associated R Q₂]
  exact congrArg _ h'

/-- The matrix in `bcBasis` of an endomorphism is the `toMatrix'` of its coordinate version. -/
theorem toMatrix_bc {m : ℕ} (f : (Kb ⊗[F] (Fin m → F)) →ₗ[Kb] (Kb ⊗[F] (Fin m → F))) :
    LinearMap.toMatrix (bcBasis F m) (bcBasis F m) f =
      LinearMap.toMatrix' ((InnerTwistAux.bcE m).toLinearMap ∘ₗ f ∘ₗ
        (InnerTwistAux.bcE (K := F) m).symm.toLinearMap) := rfl

/-- **Isometries in matrix form.** An endomorphism `f` of `F̄ ⊗ F^m` is an isometry
`Q_{F̄} → Q'_{F̄}` iff its matrix `X` in the rational basis satisfies `Xᵀ G' X = G`
(`G, G'` the Gram matrices of `Q, Q'`). -/
theorem isometry_iff_matrix {m : ℕ} (Q Q' : QuadraticForm F (Fin m → F))
    (f : (Kb ⊗[F] (Fin m → F)) →ₗ[Kb] (Kb ⊗[F] (Fin m → F))) :
    (∀ v, Q'.baseChange Kb (f v) = Q.baseChange Kb v) ↔
      (LinearMap.toMatrix (bcBasis F m) (bcBasis F m) f)ᵀ * Q'.toMatrix'.map (algebraMap F Kb) *
        LinearMap.toMatrix (bcBasis F m) (bcBasis F m) f = Q.toMatrix'.map (algebraMap F Kb) := by
  set e := InnerTwistAux.bcE (K := F) m
  set g := e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap
  rw [toMatrix_bc, ← InnerTwistAux.toMatrix'_qbar, ← InnerTwistAux.toMatrix'_qbar,
    ← QuadraticForm.toMatrix'_comp]
  constructor
  · intro h
    congr 1
    ext w
    simp only [InnerTwistAux.qbar, QuadraticMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, h]
  · intro h v
    have h2 := toMatrix'_injective h
    have := congrArg (fun q : QuadraticForm Kb (Fin m → Kb) => q (e v)) h2
    have he : (InnerTwistAux.bcE (K := F) m).symm (e v) = v := e.symm_apply_apply v
    simpa only [g, InnerTwistAux.qbar, QuadraticMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, he] using this

/-- The matrix of a Galois conjugate is the entrywise conjugate. -/
theorem toMatrix_galoisConj {m : ℕ} (σ : GalF F)
    (f : (Kb ⊗[F] (Fin m → F)) →ₗ[Kb] (Kb ⊗[F] (Fin m → F))) :
    LinearMap.toMatrix (bcBasis F m) (bcBasis F m) (galoisConj σ f) =
      (LinearMap.toMatrix (bcBasis F m) (bcBasis F m) f).map σ :=
  LinearMap.toMatrix_toLin _ _ _

/-- The matrix (in the rational basis) of an `F̄`-isometry, as an element of `GL_m(F̄)`. -/
def glOf {m : ℕ} {Q Q' : QuadraticForm F (Fin m → F)}
    (φ : (Q.baseChange Kb).IsometryEquiv (Q'.baseChange Kb)) : GL (Fin m) Kb where
  val := LinearMap.toMatrix (bcBasis F m) (bcBasis F m) φ.toLinearEquiv.toLinearMap
  inv := LinearMap.toMatrix (bcBasis F m) (bcBasis F m) φ.toLinearEquiv.symm.toLinearMap
  val_inv := by
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id (bcBasis F m)]
    congr 1
    ext v
    simp
  inv_val := by
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id (bcBasis F m)]
    congr 1
    ext v
    simp

theorem coe_glOf {m : ℕ} {Q Q' : QuadraticForm F (Fin m → F)}
    (φ : (Q.baseChange Kb).IsometryEquiv (Q'.baseChange Kb)) :
    ((glOf φ : GL (Fin m) Kb) : Matrix (Fin m) (Fin m) Kb) =
      LinearMap.toMatrix (bcBasis F m) (bcBasis F m) φ.toLinearEquiv.toLinearMap := rfl

theorem coe_glOf_inv {m : ℕ} {Q Q' : QuadraticForm F (Fin m → F)}
    (φ : (Q.baseChange Kb).IsometryEquiv (Q'.baseChange Kb)) :
    (((glOf φ)⁻¹ : GL (Fin m) Kb) : Matrix (Fin m) (Fin m) Kb) =
      LinearMap.toMatrix (bcBasis F m) (bcBasis F m) φ.toLinearEquiv.symm.toLinearMap := rfl

/-- The Gram relation satisfied by the matrix of an isometry. -/
theorem gram_glOf {m : ℕ} {Q Q' : QuadraticForm F (Fin m → F)}
    (φ : (Q.baseChange Kb).IsometryEquiv (Q'.baseChange Kb)) :
    ((glOf φ : GL (Fin m) Kb) : Matrix (Fin m) (Fin m) Kb)ᵀ * Q'.toMatrix'.map (algebraMap F Kb) *
      (glOf φ : GL (Fin m) Kb) = Q.toMatrix'.map (algebraMap F Kb) :=
  (isometry_iff_matrix Q Q' φ.toLinearEquiv.toLinearMap).1 fun v => φ.map_app v

/-- `IsTwistBy` in terms of `glOf`: `a_σ = Φ⁻¹ σ(Φ)`. -/
theorem isTwistBy_iff {m : ℕ} (Q Q' : QuadraticForm F (Fin m → F))
    (a : GalF F → GL (Fin m) Kb) :
    IsTwistBy Q Q' a ↔ ∃ φ : (Q.baseChange Kb).IsometryEquiv (Q'.baseChange Kb),
      ∀ σ, a σ = (glOf φ)⁻¹ * galGL m σ (glOf φ) := by
  have key : ∀ (φ : (Q.baseChange Kb).IsometryEquiv (Q'.baseChange Kb)) (σ : GalF F),
      LinearMap.toMatrix (bcBasis F m) (bcBasis F m)
        (φ.toLinearEquiv.symm.toLinearMap ∘ₗ galoisConj σ φ.toLinearEquiv.toLinearMap) =
      (((glOf φ)⁻¹ * galGL m σ (glOf φ) : GL (Fin m) Kb) : Matrix (Fin m) (Fin m) Kb) := by
    intro φ σ
    rw [LinearMap.toMatrix_comp _ (bcBasis F m), toMatrix_galoisConj, Units.val_mul, coe_galGL,
      coe_glOf, coe_glOf_inv]
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, fun σ => Units.ext ((hφ σ).symm.trans (key φ σ))⟩
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, fun σ => (key φ σ).trans (by rw [hφ σ])⟩

/-- The `F̄`-isometry with a given matrix `X` satisfying the Gram relation. -/
def isoOfGL {m : ℕ} (Q Q' : QuadraticForm F (Fin m → F)) (X : GL (Fin m) Kb)
    (hX : (X : Matrix (Fin m) (Fin m) Kb)ᵀ * Q'.toMatrix'.map (algebraMap F Kb) * X =
      Q.toMatrix'.map (algebraMap F Kb)) :
    (Q.baseChange Kb).IsometryEquiv (Q'.baseChange Kb) where
  toLinearEquiv := LinearEquiv.ofLinearMap (Matrix.toLin (bcBasis F m) (bcBasis F m) X)
    (Matrix.toLin (bcBasis F m) (bcBasis F m) (X⁻¹ : GL (Fin m) Kb))
    (by rw [← Matrix.toLin_mul, Units.mul_inv, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, Units.inv_mul, Matrix.toLin_one])
  map_app' v := (isometry_iff_matrix Q Q' (Matrix.toLin (bcBasis F m) (bcBasis F m) X)).2
    (by rw [LinearMap.toMatrix_toLin]; exact hX) v

theorem glOf_isoOfGL {m : ℕ} (Q Q' : QuadraticForm F (Fin m → F)) (X : GL (Fin m) Kb)
    (hX : (X : Matrix (Fin m) (Fin m) Kb)ᵀ * Q'.toMatrix'.map (algebraMap F Kb) * X =
      Q.toMatrix'.map (algebraMap F Kb)) : glOf (isoOfGL Q Q' X hX) = X :=
  Units.ext (LinearMap.toMatrix_toLin _ _ _)

section Galois

/-- Galois descent for elements: the elements of `F̄` fixed by `Aut(F̄/F)` are those of `F`
(char 0, so `F̄/F` is Galois; Mathlib `InfiniteGalois.mem_range_algebraMap_iff_fixed`). -/
theorem exists_eq_of_fixed (x : Kb) (h : ∀ σ : GalF F, σ x = x) :
    ∃ c : F, algebraMap F Kb c = x :=
  (InfiniteGalois.mem_range_algebraMap_iff_fixed x).2 h

/-- Galois descent for matrices. -/
theorem exists_map_of_fixed {n : ℕ} (X : Matrix (Fin n) (Fin n) Kb)
    (h : ∀ σ : GalF F, X.map σ = X) :
    ∃ N : Matrix (Fin n) (Fin n) F, N.map (algebraMap F Kb) = X := by
  have : ∀ i j, ∃ c : F, algebraMap F Kb c = X i j := fun i j =>
    exists_eq_of_fixed _ fun σ => by simpa using congrFun (congrFun (h σ) i) j
  choose N hN using this
  exact ⟨N, by ext i j; exact hN i j⟩

end Galois

theorem map_algebraMap_fixed {n : ℕ} (N : Matrix (Fin n) (Fin n) F) (σ : GalF F) :
    (N.map (algebraMap F Kb)).map σ = N.map (algebraMap F Kb) := by
  ext i j
  simp

theorem map_galF_mul {n : ℕ} (σ : GalF F) (A B : Matrix (Fin n) (Fin n) Kb) :
    (A * B).map σ = A.map σ * B.map σ :=
  Matrix.map_mul (f := (σ : Kb →+* Kb))


/-- A rational matrix `N` with `Nᵀ G₂ N = G₁` and `det N ≠ 0` gives an `F`-isometry
`Q₁ ≃ Q₂`. -/
theorem nonempty_isometryEquiv_of_matrix {m : ℕ} {Q₁ Q₂ : QuadraticForm F (Fin m → F)}
    (N : Matrix (Fin m) (Fin m) F) (hdet : N.det ≠ 0)
    (hN : Nᵀ * Q₂.toMatrix' * N = Q₁.toMatrix') : Nonempty (Q₁.IsometryEquiv Q₂) := by
  have hcomp : Q₂.comp (Matrix.toLin' N) = Q₁ := by
    apply toMatrix'_injective
    rw [QuadraticForm.toMatrix'_comp, LinearMap.toMatrix'_toLin', hN]
  have hu : IsUnit (LinearMap.toMatrix (Pi.basisFun F (Fin m)) (Pi.basisFun F (Fin m))
      (Matrix.toLin' N)).det := by
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    exact Ne.isUnit hdet
  refine ⟨{ toLinearEquiv := LinearEquiv.ofIsUnitDet hu, map_app' := fun v => ?_ }⟩
  have := congrArg (fun q : QuadraticForm F (Fin m → F) => q v) hcomp
  simpa [LinearEquiv.ofIsUnitDet] using this

/-- **Uniqueness of the twisted form** (Galois descent).  Let `S ⊆ O(Q)(F̄)` and let `a, b` be
cohomologous `S`-valued cocycles, `a` the cocycle of an `F̄`-isometry `Q ≃ Q₁` and `b` that of
`Q ≃ Q₂`.  Then `Q₁ ≅ Q₂` over `F`: with `b_σ = c⁻¹ a_σ σ(c)` the isometry
`φ₂ c⁻¹ φ₁⁻¹ : Q₁ ≃ Q₂` over `F̄` is Galois-invariant, hence rational. -/
theorem nonempty_isometryEquiv_of_rel {m : ℕ} {Q : QuadraticForm F (Fin m → F)}
    {S : Subgroup (GL (Fin m) Kb)}
    (hS : ∀ s ∈ S, (s : Matrix (Fin m) (Fin m) Kb)ᵀ * Q.toMatrix'.map (algebraMap F Kb) * s =
      Q.toMatrix'.map (algebraMap F Kb))
    {a b : GalCocycle S} (hab : GalCocycle.Rel a b) {Q₁ Q₂ : QuadraticForm F (Fin m → F)}
    (h₁ : IsTwistBy Q Q₁ a.toFun) (h₂ : IsTwistBy Q Q₂ b.toFun) :
    Nonempty (Q₁.IsometryEquiv Q₂) := by
  obtain ⟨φ₁, hφ₁⟩ := (isTwistBy_iff Q Q₁ _).1 h₁
  obtain ⟨φ₂, hφ₂⟩ := (isTwistBy_iff Q Q₂ _).1 h₂
  obtain ⟨c, hc, hb⟩ := hab
  set g₁ := glOf φ₁
  set g₂ := glOf φ₂
  set Ψ : GL (Fin m) Kb := g₂ * c⁻¹ * g₁⁻¹ with hΨ
  have hfix : ∀ σ : GalF F, galGL m σ Ψ = Ψ := by
    intro σ
    have e1 : galGL m σ g₁ = g₁ * a.toFun σ := by rw [hφ₁ σ]; group
    have e2 : galGL m σ g₂ = g₂ * b.toFun σ := by rw [hφ₂ σ]; group
    rw [hΨ, map_mul, map_mul, map_inv, map_inv, e1, e2, hb σ]
    group
  obtain ⟨N, hN⟩ := exists_map_of_fixed (Ψ : Matrix (Fin m) (Fin m) Kb) fun σ => by
    rw [← coe_galGL, hfix σ]
  set G := Q.toMatrix'.map (algebraMap F Kb)
  set G₁ := Q₁.toMatrix'.map (algebraMap F Kb)
  set G₂ := Q₂.toMatrix'.map (algebraMap F Kb)
  have r₁ : (g₁ : Matrix (Fin m) (Fin m) Kb)ᵀ * G₁ * g₁ = G := gram_glOf φ₁
  have r₂ : (g₂ : Matrix (Fin m) (Fin m) Kb)ᵀ * G₂ * g₂ = G := gram_glOf φ₂
  have rc : ((c⁻¹ : GL (Fin m) Kb) : Matrix (Fin m) (Fin m) Kb)ᵀ * G * (c⁻¹ : GL (Fin m) Kb) = G :=
    hS _ (S.inv_mem hc)
  set A₁ : Matrix (Fin m) (Fin m) Kb := (g₁ : Matrix (Fin m) (Fin m) Kb)
  set A₁i : Matrix (Fin m) (Fin m) Kb := ((g₁⁻¹ : GL (Fin m) Kb) : Matrix (Fin m) (Fin m) Kb)
  set A₂ : Matrix (Fin m) (Fin m) Kb := (g₂ : Matrix (Fin m) (Fin m) Kb)
  set C : Matrix (Fin m) (Fin m) Kb := ((c⁻¹ : GL (Fin m) Kb) : Matrix (Fin m) (Fin m) Kb)
  have hg₁ : A₁ * A₁i = 1 := Units.mul_inv g₁
  have hΨm : (Ψ : Matrix (Fin m) (Fin m) Kb) = A₂ * C * A₁i := by
    simp only [hΨ, Units.val_mul, A₂, C, A₁i]
  have hΨG : (Ψ : Matrix (Fin m) (Fin m) Kb)ᵀ * G₂ * Ψ = G₁ := by
    have : (Ψ : Matrix (Fin m) (Fin m) Kb)ᵀ * G₂ * Ψ = A₁iᵀ * (Cᵀ * (A₂ᵀ * G₂ * A₂) * C) * A₁i := by
      rw [hΨm]
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, r₂, rc, ← r₁]
    calc A₁iᵀ * (A₁ᵀ * G₁ * A₁) * A₁i = (A₁ * A₁i)ᵀ * G₁ * (A₁ * A₁i) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = G₁ := by rw [hg₁, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hNG : Nᵀ * Q₂.toMatrix' * N = Q₁.toMatrix' := by
    apply Matrix.map_injective (algebraMap F Kb).injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hN]
    exact hΨG
  have hdet : N.det ≠ 0 := by
    intro h0
    have h1 := (algebraMap F Kb).map_det N
    rw [h0, map_zero] at h1
    have h2 : ((algebraMap F Kb).mapMatrix N) = (Ψ : Matrix (Fin m) (Fin m) Kb) := hN
    rw [h2] at h1
    exact (Matrix.isUnits_det_units Ψ).ne_zero h1.symm
  exact nonempty_isometryEquiv_of_matrix N hdet hNG

/-- The quadratic form `v ↦ vᵀ N v` of a symmetric matrix has Gram matrix `N`. -/
theorem toMatrix'_ofSymm {n : ℕ} (N : Matrix (Fin n) (Fin n) F) (hN : Nᵀ = N) :
    QuadraticForm.toMatrix' (LinearMap.BilinMap.toQuadraticMap
      (Matrix.toLinearMap₂' F N : (Fin n → F) →ₗ[F] (Fin n → F) →ₗ[F] F)) = N := by
  have hsym : ∀ x y : Fin n → F, (Matrix.toLinearMap₂' F N : (Fin n → F) →ₗ[F] (Fin n → F) →ₗ[F] F) x y =
      (Matrix.toLinearMap₂' F N : (Fin n → F) →ₗ[F] (Fin n → F) →ₗ[F] F) y x := by
    intro x y
    rw [Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_apply', Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hN, dotProduct_comm]
  rw [QuadraticForm.toMatrix', QuadraticMap.associated_left_inverse F hsym]
  exact (LinearMap.toMatrix₂' F).apply_symm_apply N

/-- **Existence of the twisted form** (Galois descent, given a splitting of the cocycle in
`GL_m(F̄)`).  Let `S ⊆ SO(Q)(F̄)` and `a` an `S`-valued cocycle with `a_σ = M⁻¹ σ(M)`.  Then the
form with Gram matrix `M⁻ᵀ G M⁻¹` is rational, nondegenerate, of the discriminant of `Q`, and `a`
is the cocycle of the `F̄`-isometry with matrix `M`. -/
theorem exists_twist_of_split {m : ℕ} {Q : QuadraticForm F (Fin m → F)}
    (hQ : IsNondeg Q) {S : Subgroup (GL (Fin m) Kb)}
    (hS : ∀ s ∈ S, (s : Matrix (Fin m) (Fin m) Kb)ᵀ * Q.toMatrix'.map (algebraMap F Kb) * s =
      Q.toMatrix'.map (algebraMap F Kb))
    (hSdet : ∀ s ∈ S, (s : Matrix (Fin m) (Fin m) Kb).det = 1)
    (a : GalCocycle S) (M : GL (Fin m) Kb) (hM : ∀ σ, a.toFun σ = M⁻¹ * galGL m σ M) :
    ∃ Q'' : QuadraticForm F (Fin m → F), IsNondeg Q'' ∧ SameDisc Q Q'' ∧
      IsTwistBy Q Q'' a.toFun := by
  set G := Q.toMatrix'.map (algebraMap F Kb) with hG
  set Y : GL (Fin m) Kb := M⁻¹
  have hY : ∀ σ, galGL m σ Y = (a.toFun σ)⁻¹ * Y := by
    intro σ
    rw [hM σ]
    simp only [Y, map_inv]
    group
  have hYσ : ∀ σ : GalF F, (Y : Matrix (Fin m) (Fin m) Kb).map σ =
      (((a.toFun σ)⁻¹ : GL (Fin m) Kb) : Matrix (Fin m) (Fin m) Kb) * Y := by
    intro σ
    rw [← coe_galGL, hY σ, Units.val_mul]
  have hfix : ∀ σ : GalF F,
      ((Y : Matrix (Fin m) (Fin m) Kb)ᵀ * G * Y).map σ = (Y : Matrix (Fin m) (Fin m) Kb)ᵀ * G * Y := by
    intro σ
    rw [map_galF_mul, map_galF_mul, Matrix.transpose_map, hYσ σ, hG,
      map_algebraMap_fixed, ← hG]
    have := hS _ (S.inv_mem (a.mem' σ))
    set Ai : Matrix (Fin m) (Fin m) Kb := (((a.toFun σ)⁻¹ : GL (Fin m) Kb) : Matrix (Fin m) (Fin m) Kb)
    set Ym : Matrix (Fin m) (Fin m) Kb := (Y : Matrix (Fin m) (Fin m) Kb)
    calc (Ai * Ym)ᵀ * G * (Ai * Ym) = Ymᵀ * (Aiᵀ * G * Ai) * Ym := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [this]
  obtain ⟨N, hN⟩ := exists_map_of_fixed _ hfix
  have hGs : Gᵀ = G := by rw [hG, ← Matrix.transpose_map, (QuadraticForm.isSymm_toMatrix' Q).eq]
  have hNs : Nᵀ = N := by
    apply Matrix.map_injective (algebraMap F Kb).injective
    dsimp only
    rw [Matrix.transpose_map, hN, Matrix.transpose_mul, Matrix.transpose_mul, hGs,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  set Q'' : QuadraticForm F (Fin m → F) := LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' F N : (Fin _ → F) →ₗ[F] (Fin _ → F) →ₗ[F] F)
  have hQ'' : Q''.toMatrix' = N := toMatrix'_ofSymm N hNs
  obtain ⟨c, hc⟩ := exists_eq_of_fixed (Y : Matrix (Fin m) (Fin m) Kb).det fun σ => by
    have h1 := (σ : Kb →+* Kb).map_det (Y : Matrix (Fin m) (Fin m) Kb)
    have h2 : (σ : Kb →+* Kb).mapMatrix (Y : Matrix (Fin m) (Fin m) Kb) =
        (Y : Matrix (Fin m) (Fin m) Kb).map σ := rfl
    rw [h2, hYσ σ, Matrix.det_mul, hSdet _ (S.inv_mem (a.mem' σ)), one_mul] at h1
    exact h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact (Matrix.isUnits_det_units Y).ne_zero hc.symm
  have hdisc : Q''.discr' = c ^ 2 * Q.discr' := by
    apply (algebraMap F Kb).injective
    have h1 := (algebraMap F Kb).map_det N
    have h2 : (algebraMap F Kb).mapMatrix N = N.map (algebraMap F Kb) := rfl
    rw [h2, hN, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← hc, hG] at h1
    have h3 := (algebraMap F Kb).map_det Q.toMatrix'
    have h4 : (algebraMap F Kb).mapMatrix Q.toMatrix' = Q.toMatrix'.map (algebraMap F Kb) := rfl
    rw [h4] at h3
    rw [QuadraticForm.discr', QuadraticForm.discr', hQ'', h1, map_mul, map_pow, h3]
    ring
  have hnd : IsNondeg Q'' := by
    rw [InnerTwistAux.isNondeg_iff_discr'_ne_zero, hdisc]
    exact mul_ne_zero (pow_ne_zero 2 hc0) ((InnerTwistAux.isNondeg_iff_discr'_ne_zero Q).1 hQ)
  refine ⟨Q'', hnd, ⟨c, hc0, hdisc⟩, ?_⟩
  have hgram : (M : Matrix (Fin m) (Fin m) Kb)ᵀ * Q''.toMatrix'.map (algebraMap F Kb) * M = G := by
    rw [hQ'', hN]
    have hYM : (Y : Matrix (Fin m) (Fin m) Kb) * M = 1 := Units.inv_mul M
    set Ym : Matrix (Fin m) (Fin m) Kb := (Y : Matrix (Fin m) (Fin m) Kb)
    set Mm : Matrix (Fin m) (Fin m) Kb := (M : Matrix (Fin m) (Fin m) Kb)
    calc Mmᵀ * (Ymᵀ * G * Ym) * Mm = (Ym * Mm)ᵀ * G * (Ym * Mm) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = G := by rw [hYM, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  refine (isTwistBy_iff Q Q'' _).2 ⟨isoOfGL Q Q'' M hgram, fun σ => ?_⟩
  rw [glOf_isoOfGL, hM σ]

/-- Twisting is compatible with `F`-isometries of the target. -/
theorem isTwistBy_of_isometryEquiv {m : ℕ} {Q Q₁ Q₂ : QuadraticForm F (Fin m → F)}
    (ψ : Q₁.IsometryEquiv Q₂) {a : GalF F → GL (Fin m) Kb} (h : IsTwistBy Q Q₁ a) :
    IsTwistBy Q Q₂ a := by
  obtain ⟨φ, hφ⟩ := (isTwistBy_iff Q Q₁ a).1 h
  set N := LinearMap.toMatrix' ψ.toLinearEquiv.toLinearMap
  set Ni := LinearMap.toMatrix' ψ.toLinearEquiv.symm.toLinearMap
  have hNNi : N * Ni = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1; ext v; simp
  have hNiN : Ni * N = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1; ext v; simp
  set P : GL (Fin m) Kb := Units.map (RingHom.mapMatrix (algebraMap F Kb)).toMonoidHom
    ⟨N, Ni, hNNi, hNiN⟩
  have hP : (P : Matrix (Fin m) (Fin m) Kb) = N.map (algebraMap F Kb) := rfl
  have hPσ : ∀ σ, galGL m σ P = P := fun σ => Units.ext (by
    rw [coe_galGL, hP, map_algebraMap_fixed])
  have hNG : Nᵀ * Q₂.toMatrix' * N = Q₁.toMatrix' := by
    have : Q₂.comp (Matrix.toLin' N) = Q₁ := by
      ext v
      simp [N, Matrix.toLin'_toMatrix']
    rw [← this, QuadraticForm.toMatrix'_comp, LinearMap.toMatrix'_toLin']
  have hgram : ((P * glOf φ : GL (Fin m) Kb) : Matrix (Fin m) (Fin m) Kb)ᵀ *
      Q₂.toMatrix'.map (algebraMap F Kb) * (P * glOf φ : GL (Fin m) Kb) =
        Q.toMatrix'.map (algebraMap F Kb) := by
    rw [← gram_glOf φ, ← hNG, Units.val_mul, hP, Matrix.map_mul, Matrix.map_mul,
      Matrix.transpose_map]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  refine (isTwistBy_iff Q Q₂ a).2 ⟨isoOfGL Q Q₂ (P * glOf φ) hgram, fun σ => ?_⟩
  rw [glOf_isoOfGL, hφ σ, map_mul, hPσ σ]
  group

/-- The matrix of `P(g)` (`g ∈ GSpin(W)(F̄)`) is a Gram isometry of `W`. -/
theorem gram_specMatFbar {m : ℕ} (Q : QuadraticForm F (Fin m → F)) (g : GSpin (Q.baseChange Kb)) :
    ((specMatFbar Q g : GL (Fin m) Kb) : Matrix (Fin m) (Fin m) Kb)ᵀ *
      Q.toMatrix'.map (algebraMap F Kb) * (specMatFbar Q g : GL (Fin m) Kb) =
        Q.toMatrix'.map (algebraMap F Kb) := by
  rw [coe_specMatFbar]
  exact (isometry_iff_matrix Q Q _).1 fun v => specP_isometry g v

/-- The matrix of `P(g)` has determinant `1`. -/
theorem det_specMatFbar {m : ℕ} (Q : QuadraticForm F (Fin m → F)) (g : GSpin (Q.baseChange Kb)) :
    ((specMatFbar Q g : GL (Fin m) Kb) : Matrix (Fin m) (Fin m) Kb).det = 1 := by
  rw [coe_specMatFbar, LinearMap.det_toMatrix]
  exact det_specP g

/-- `S_x(F̄) ⊆ O(W)(F̄)`, in matrix form. -/
theorem gram_mem_torusBarFbar (d : GGPData F) (x : GSpin d.QW) :
    ∀ s ∈ d.torusBarFbar x, (s : Matrix (Fin d.m) (Fin d.m) Kb)ᵀ *
      d.QW.toMatrix'.map (algebraMap F Kb) * s = d.QW.toMatrix'.map (algebraMap F Kb) := by
  rintro s ⟨g, -, rfl⟩
  exact gram_specMatFbar d.QW g

/-- `S_x(F̄) ⊆ SL_m(F̄)`. -/
theorem det_mem_torusBarFbar (d : GGPData F) (x : GSpin d.QW) :
    ∀ s ∈ d.torusBarFbar x, (s : Matrix (Fin d.m) (Fin d.m) Kb).det = 1 := by
  rintro s ⟨g, -, rfl⟩
  exact det_specMatFbar d.QW g

end TwistDescent
end GSpinGGP
