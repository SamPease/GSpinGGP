/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.Hilbert90
import GSpinGGP.Foundations.SimpleAlgebraModule

/-!
# Hilbert 90 for the units of a simple algebra

Let `Ā` be an `F̄`-algebra with a semilinear action of `Γ_F` by ring automorphisms, and let
`ι : A → Ā` be an `F`-algebra map from a simple `F`-algebra `A` sending an `F`-basis of `A` to a
Galois-fixed `F̄`-basis of `Ā` (`Ā = F̄ ⊗ A`). Then every continuous `1`-cocycle `v` with values in
`Āˣ` is a coboundary: `v_σ = u⁻¹ σ(u)` (`exists_units_eq_inv_mul_act`).

Proof (own work, standard): the twisted fixed vectors `B = {z : σ(z) = z v_σ}` form a left
`A`-module; in coordinates, Hilbert 90 for `GL_N` (`hilbert90_GL`, applied to the matrices of right
multiplication by `v_σ⁻¹`) shows that `B` has `F`-dimension `N = dim A` and spans `Ā` over `F̄`.
Since `A` is simple, `B ≅ A` (`nonempty_linearEquiv_of_finrank_eq`), so `B = A u`; then `Ā = Ā u`,
`u` is a unit, and `σ(u) = u v_σ`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Matrix

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]



/-- A semilinear action of `Γ_F` on an `F̄`-algebra by ring automorphisms, fixing a basis. -/
structure GalAlgAction (F : Type) [NontriviallyNormedField F] [PAdicField F] (Ā : Type*) [Ring Ā]
    [Algebra (AlgebraicClosure F) Ā] {N : ℕ} (e : Module.Basis (Fin N) (AlgebraicClosure F) Ā) where
  /-- `σ` acting on `Ā` -/
  act : GalF F → Ā →+* Ā
  act_mul : ∀ σ τ z, act (σ * τ) z = act σ (act τ z)
  act_smul : ∀ σ (c : AlgebraicClosure F) z, act σ (c • z) = σ c • act σ z
  act_basis : ∀ σ i, act σ (e i) = e i

variable {Ā : Type*} [Ring Ā] [Algebra (AlgebraicClosure F) Ā] [Algebra F Ā] [IsScalarTower F (AlgebraicClosure F) Ā] {N : ℕ} {e : Module.Basis (Fin N) (AlgebraicClosure F) Ā}
  {A : Type*} [Ring A] [Algebra F A] [IsSimpleRing A] [IsArtinianRing A]

namespace GalAlgAction

variable (G : GalAlgAction F Ā e)

/-- `σ` acts on coordinates. -/
theorem repr_act (σ : GalF F) (z : Ā) (i : Fin N) : e.repr (G.act σ z) i = σ (e.repr z i) := by
  conv_lhs => rw [← e.sum_repr z]
  simp only [map_sum, G.act_smul, G.act_basis]
  rw [← map_sum (e.repr), e.repr_sum_self]

/-- The matrix of right multiplication by `w`. -/
def rmat (w : Ā) : Matrix (Fin N) (Fin N) (AlgebraicClosure F) :=
  LinearMap.toMatrix e e (LinearMap.mulRight (AlgebraicClosure F) w)

theorem rmat_mul (w₁ w₂ : Ā) : rmat (e := e) (w₁ * w₂) = rmat (e := e) w₂ * rmat (e := e) w₁ := by
  rw [rmat, rmat, rmat, ← LinearMap.toMatrix_mul]
  congr 1
  ext z
  simp [mul_assoc]

theorem rmat_one : rmat (e := e) 1 = 1 := by
  rw [rmat, ← LinearMap.toMatrix_id e]
  congr 1
  ext z
  simp

theorem rmat_act (σ : GalF F) (w : Ā) : rmat (e := e) (G.act σ w) = (rmat (e := e) w).map σ := by
  ext i j
  simp only [rmat, LinearMap.toMatrix_apply, LinearMap.mulRight_apply, Matrix.map_apply]
  rw [show e j * G.act σ w = G.act σ (e j * w) by rw [map_mul, G.act_basis], G.repr_act]

theorem repr_mul (z w : Ā) : ⇑(e.repr (z * w)) = rmat (e := e) w *ᵥ ⇑(e.repr z) := by
  rw [rmat, LinearMap.toMatrix_mulVec_repr]
  rfl

end GalAlgAction

/-- **Hilbert 90 for `Āˣ`.** -/
theorem exists_units_eq_inv_mul_act (G : GalAlgAction F Ā e) (ι : A →ₐ[F] Ā)
    (b : Module.Basis (Fin N) F A) (hb : ∀ i, ι (b i) = e i)
    (v : GalF F → Āˣ) (hv : ∃ E : IntermediateField F (AlgebraicClosure F), FiniteDimensional F E ∧
      ∀ σ τ : GalF F, (∀ x ∈ E, σ x = τ x) → v σ = v τ)
    (hcoc : ∀ σ τ, (v (σ * τ) : Ā) = v σ * G.act σ (v τ)) :
    ∃ u : Āˣ, ∀ σ, (v σ : Ā) = (u⁻¹ : Āˣ) * G.act σ u := by
  classical
  -- the `GL_N` cocycle `a_σ = ρ(v_σ⁻¹)`
  have hinv : ∀ σ τ, (((v (σ * τ))⁻¹ : Āˣ) : Ā) =
      G.act σ (((v τ)⁻¹ : Āˣ) : Ā) * (((v σ)⁻¹ : Āˣ) : Ā) := fun σ τ => by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hcoc, mul_assoc, ← mul_assoc (G.act σ _), ← map_mul, Units.mul_inv, map_one, one_mul,
      Units.mul_inv]
  let a : GalF F → GL (Fin N) (AlgebraicClosure F) := fun σ =>
    ⟨GalAlgAction.rmat (e := e) (((v σ)⁻¹ : Āˣ) : Ā), GalAlgAction.rmat (e := e) (v σ : Ā),
      by rw [← GalAlgAction.rmat_mul, Units.mul_inv, GalAlgAction.rmat_one],
      by rw [← GalAlgAction.rmat_mul, Units.inv_mul, GalAlgAction.rmat_one]⟩
  let c : GalCocycle (⊤ : Subgroup (GL (Fin N) (AlgebraicClosure F))) :=
    { toFun := a
      mem' := fun _ => trivial
      cocycle' := fun σ τ => Units.ext (by
        show GalAlgAction.rmat _ = GalAlgAction.rmat _ * (GalAlgAction.rmat _).map σ
        rw [hinv, GalAlgAction.rmat_mul, ← G.rmat_act])
      continuous' := by
        obtain ⟨E, hE, h⟩ := hv
        exact ⟨E, hE, fun σ τ hστ => by simp only [a, h σ τ hστ]⟩ }
  obtain ⟨M, hM⟩ := hilbert90_GL c
  -- `ρ(v_σ) = σ(M)⁻¹ M`
  have hrv : ∀ σ, GalAlgAction.rmat (e := e) (v σ : Ā) =
      (((M⁻¹ : GL (Fin N) (AlgebraicClosure F)) : Matrix (Fin N) (Fin N) (AlgebraicClosure F)).map σ) * (M : Matrix (Fin N) (Fin N) (AlgebraicClosure F)) := by
    intro σ
    have h := congrArg (fun g : GL (Fin N) (AlgebraicClosure F) =>
      ((g⁻¹ : GL (Fin N) (AlgebraicClosure F)) : Matrix (Fin N) (Fin N) (AlgebraicClosure F))) (hM σ)
    simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← map_inv, coe_galGL] at h
    exact h
  have hMM : (M : Matrix (Fin N) (Fin N) (AlgebraicClosure F)) *
      ((M⁻¹ : GL (Fin N) (AlgebraicClosure F)) : Matrix (Fin N) (Fin N) (AlgebraicClosure F)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMM' : ((M⁻¹ : GL (Fin N) (AlgebraicClosure F)) : Matrix (Fin N) (Fin N) (AlgebraicClosure F)) *
      (M : Matrix (Fin N) (Fin N) (AlgebraicClosure F)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set Mi : Matrix (Fin N) (Fin N) (AlgebraicClosure F) := ((M⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) (AlgebraicClosure F))
  set Mm : Matrix (Fin N) (Fin N) (AlgebraicClosure F) := (M : Matrix (Fin N) (Fin N) (AlgebraicClosure F))
  -- the twisted-fixed vectors `β_j` (coordinates: the columns of `M⁻¹`)
  let β : Fin N → Ā := fun j => e.equivFun.symm (Mi *ᵥ Pi.single j 1)
  have hβc : ∀ j, e.equivFun (β j) = Mi *ᵥ Pi.single j 1 := fun j =>
    e.equivFun.apply_symm_apply _
  have hcoords : ∀ z, ⇑(e.repr z) = e.equivFun z := fun z => rfl
  have hβB : ∀ σ j, G.act σ (β j) = β j * v σ := by
    intro σ j
    apply e.equivFun.injective
    have L : e.equivFun (G.act σ (β j)) = fun i => σ (e.equivFun (β j) i) :=
      funext fun i => G.repr_act σ _ i
    have R : e.equivFun (β j * v σ) = GalAlgAction.rmat (e := e) (v σ : Ā) *ᵥ e.equivFun (β j) :=
      GalAlgAction.repr_mul (e := e) _ _
    rw [L, R, hβc, hrv, Matrix.mulVec_mulVec, Matrix.mul_assoc, hMM, Matrix.mul_one]
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
    congr 1; ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]
  -- the `β_j` span `Ā` over `F̄`
  have hcomb : ∀ y : Fin N → AlgebraicClosure F, ∑ j, y j • (Mi *ᵥ Pi.single j 1) = Mi *ᵥ y := by
    intro y; ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hspan : ∀ z : Ā, z = ∑ j, (Mm *ᵥ e.equivFun z) j • β j := by
    intro z
    apply e.equivFun.injective
    rw [map_sum]
    simp only [map_smul, hβc]
    rw [hcomb, Matrix.mulVec_mulVec, hMM', Matrix.one_mulVec]
  -- twisted-fixed vectors have rational coordinates in the basis `β`
  have hrat : ∀ z, (∀ σ, G.act σ z = z * v σ) → ∀ j, ∃ f : F,
      algebraMap F (AlgebraicClosure F) f = (Mm *ᵥ e.equivFun z) j := by
    intro z hz j
    refine (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 fun σ => ?_
    have hx : (fun i => σ (e.equivFun z i)) = Mi.map σ *ᵥ (Mm *ᵥ e.equivFun z) := by
      rw [Matrix.mulVec_mulVec, ← hrv]
      have h1 := GalAlgAction.repr_mul (e := e) z (v σ : Ā)
      rw [← hz σ] at h1
      funext i
      exact (G.repr_act σ z i).symm.trans (congrFun h1 i)
    have h3 : σ ((Mm *ᵥ e.equivFun z) j) =
        (Mm.map σ *ᵥ (fun i => σ (e.equivFun z i))) j := by
      simp [Matrix.mulVec, dotProduct, map_sum]
    rw [h3, hx, Matrix.mulVec_mulVec, ← Matrix.map_mul, hMM,
      Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.one_mulVec]
  sorry

end GSpinGGP
