/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.Kottwitz

/-!
# Hilbert's Theorem 90 for `GL_m`

`H¹(F, GL_m) = 1`: every continuous `1`-cocycle of `Γ_F` with values in `GL_m(F̄)` is a
coboundary (`hilbert90_GL`).  Used in `Main.existsUnique_twistIdx` (existence half: an
`S_x`-valued cocycle is the cocycle of a rational quadratic form,
`TwistDescent.exists_twist_of_split`).  Proved here by Speiser's averaging argument from Mathlib's
linear independence of characters (`linearIndependent_monoidHom`); Mathlib and Tau Ceti have only
the case `m = 1`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace GSpinGGP

open IntermediateField Matrix

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

variable {m : ℕ} {S : Subgroup (GL (Fin m) (AlgebraicClosure F))}

/-- The identity of `Γ_F` acts trivially on `GL_m(F̄)`. -/
theorem galGL_one (g : GL (Fin m) (AlgebraicClosure F)) : galGL m (1 : GalF F) g = g := by
  ext i j
  simp [coe_galGL]

/-- `a_1 = 1` for a cocycle (from `a_1 = a_1 · 1(a_1)`). -/
theorem GalCocycle.toFun_one (a : GalCocycle S) : a.toFun 1 = 1 := by
  have h := a.cocycle' 1 1
  rw [mul_one, galGL_one] at h
  exact (mul_eq_left.mp h.symm)

/-- **Hilbert's Theorem 90 for `GL_m`** (Serre, *Local Fields*, GTM 67, Ch. X §1, Prop. 3;
Serre, *Cohomologie galoisienne*, Ch. III §1.1, Lemme 1).  A continuous cocycle
`σ ↦ a_σ ∈ GL_m(F̄)` of `Γ_F = Aut(F̄/F)` (cocycle rule `a_{στ} = a_σ σ(a_τ)`) is a coboundary:
`a_σ = M⁻¹ σ(M)` for some `M ∈ GL_m(F̄)`.

Proof (Speiser's argument).  Let `E/F` be a finite extension through which `a` factors, and `L` its
normal closure in `F̄`.  For `v ∈ L^m` set `b(v) = Σ_{ρ ∈ Gal(L/F)} a_{ρ̃} ρ(v)` with `ρ̃` any lift of
`ρ` to `F̄`.  The cocycle rule gives `a_σ σ(b(v)) = b(v)` for every `σ`.  The values `b(v)` span
`F̄^m`: a linear form `f` killing them gives `Σ_ρ ρ(x) f(a_{ρ̃} ρ(v)) = 0` for all `x ∈ L`, so every
coefficient vanishes by Dedekind's independence of characters, and the coefficient at `ρ = 1` is
`f(v)`.  Choosing `v_1, …, v_m` with `b(v_j)` a basis, the matrix `B` with columns `b(v_j)` is
invertible and `a_σ σ(B) = B`, i.e. `a_σ = M⁻¹ σ(M)` with `M = B⁻¹`.  The subgroup `S` plays no
role. -/
theorem hilbert90_GL (a : GalCocycle S) :
    ∃ M : GL (Fin m) (AlgebraicClosure F), ∀ σ : GalF F, a.toFun σ = M⁻¹ * galGL m σ M := by
  obtain ⟨E, hEfin, hE⟩ := a.continuous'
  set L := normalClosure F E (AlgebraicClosure F) with hL
  have : FiniteDimensional F L := normalClosure.is_finiteDimensional F E (AlgebraicClosure F)
  let lift : (L ≃ₐ[F] L) → GalF F := fun ρ => ρ.liftNormal (AlgebraicClosure F)
  have lift_apply : ∀ ρ (x : L), lift ρ (x : (AlgebraicClosure F)) = (ρ x : (AlgebraicClosure F)) := fun ρ x =>
    AlgEquiv.liftNormal_commutes ρ (AlgebraicClosure F) x
  let res : GalF F →* (L ≃ₐ[F] L) := AlgEquiv.restrictNormalHom L
  have res_apply : ∀ σ (x : L), ((res σ x : L) : (AlgebraicClosure F)) = σ x := fun σ x =>
    AlgEquiv.restrictNormalHom_apply L σ x
  have agreeL : ∀ σ τ : GalF F, (∀ x : L, σ x = τ x) → a.toFun σ = a.toFun τ :=
    fun σ τ h => hE σ τ (fun e he => h ⟨e, le_normalClosure E he⟩)
  -- the averaging map
  let A : (L ≃ₐ[F] L) → Matrix (Fin m) (Fin m) (AlgebraicClosure F) := fun ρ => (a.toFun (lift ρ) : _)
  let b : (Fin m → L) → (Fin m → (AlgebraicClosure F)) := fun v =>
    ∑ ρ : L ≃ₐ[F] L, A ρ *ᵥ (fun i => (ρ (v i) : (AlgebraicClosure F)))
  -- key relation
  have key : ∀ (σ : GalF F) (v : Fin m → L),
      (a.toFun σ : Matrix (Fin m) (Fin m) (AlgebraicClosure F)) *ᵥ (fun i => σ (b v i)) = b v := by
    intro σ v
    have h1 : (fun i => σ (b v i)) = ∑ ρ : L ≃ₐ[F] L,
        (A ρ).map (σ : (AlgebraicClosure F) →+* (AlgebraicClosure F)) *ᵥ (fun i => σ (ρ (v i) : (AlgebraicClosure F))) := by
      funext i
      simp only [b, Finset.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      exact RingHom.map_mulVec (σ : (AlgebraicClosure F) →+* (AlgebraicClosure F)) (A ρ) _ i
    rw [h1, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_mulVec]
    have h2 : ∀ ρ : L ≃ₐ[F] L,
        ((a.toFun σ : Matrix (Fin m) (Fin m) (AlgebraicClosure F)) * (A ρ).map (σ : (AlgebraicClosure F) →+* (AlgebraicClosure F))) *ᵥ
            (fun i => σ (ρ (v i) : (AlgebraicClosure F))) =
          A (res σ * ρ) *ᵥ (fun i => ((res σ * ρ) (v i) : (AlgebraicClosure F))) := by
      intro ρ
      have hc := a.cocycle' σ (lift ρ)
      have hag : a.toFun (σ * lift ρ) = a.toFun (lift (res σ * ρ)) := by
        apply agreeL
        intro x
        rw [AlgEquiv.mul_apply, lift_apply, lift_apply, AlgEquiv.mul_apply, res_apply]
      have hmat : (a.toFun σ : Matrix (Fin m) (Fin m) (AlgebraicClosure F)) * (A ρ).map (σ : (AlgebraicClosure F) →+* (AlgebraicClosure F)) =
          A (res σ * ρ) := by
        simp only [A]
        rw [← hag, hc, Units.val_mul, coe_galGL]
        rfl
      rw [hmat]
      congr 1
      funext i
      rw [AlgEquiv.mul_apply, res_apply]
    simp only [h2]
    exact Fintype.sum_equiv (Equiv.mulLeft (res σ)) _ _ (fun ρ => rfl)
  -- the values of `b` span
  have hspan : Submodule.span (AlgebraicClosure F) (Set.range b) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hfb : ∀ v, f (b v) = 0 := fun v =>
      LinearMap.mem_ker.mp (hle (Submodule.subset_span ⟨v, rfl⟩))
    -- characters of `L`
    let χ : (L ≃ₐ[F] L) → (L →* AlgebraicClosure F) := fun ρ =>
      (algebraMap L (AlgebraicClosure F) : L →* AlgebraicClosure F).comp
        (ρ : L →* L)
    have hχ : Function.Injective χ := by
      intro ρ₁ ρ₂ h
      ext x
      have := DFunLike.congr_fun h x
      simpa [χ] using this
    have hli := (linearIndependent_monoidHom L (AlgebraicClosure F)).comp χ hχ
    have hzero : ∀ v : Fin m → L, f (fun i => (v i : AlgebraicClosure F)) = 0 := by
      intro v
      have hsum := Fintype.linearIndependent_iff.mp hli
        (fun ρ => f (A ρ *ᵥ (fun i => (ρ (v i) : AlgebraicClosure F)))) ?_ 1
      · have h1 : A 1 = 1 := by
          simp only [A]
          rw [agreeL (lift 1) 1 (fun x => by rw [lift_apply]; rfl), GalCocycle.toFun_one]
          rfl
        simpa [h1] using hsum
      · funext x
        have := hfb (fun i => x * v i)
        simp only [b, map_sum] at this
        simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
          Pi.zero_apply]
        rw [← this]
        refine Finset.sum_congr rfl fun ρ _ => ?_
        have : (fun i => ((ρ (x * v i) : L) : AlgebraicClosure F)) =
            (ρ x : AlgebraicClosure F) • (fun i => (ρ (v i) : AlgebraicClosure F)) := by
          funext i; simp
        rw [this, Matrix.mulVec_smul, map_smul, smul_eq_mul, mul_comm]
        rfl
    apply hf0
    apply (Pi.basisFun (AlgebraicClosure F) (Fin m)).ext
    intro i
    have := hzero (Pi.single i 1)
    rw [LinearMap.zero_apply, ← this]
    congr 1
    funext j
    simp only [Pi.basisFun_apply, Pi.single_apply]
    split_ifs <;> simp
  -- extract a basis among the values of `b`
  classical
  obtain ⟨s, hs, hsspan, hsli⟩ := exists_linearIndependent (AlgebraicClosure F) (Set.range b)
  rw [hspan] at hsspan
  let B0 : Module.Basis s (AlgebraicClosure F) (Fin m → AlgebraicClosure F) :=
    Module.Basis.mk hsli (by rw [Subtype.range_coe, hsspan])
  let e : s ≃ Fin m := B0.indexEquiv (Pi.basisFun (AlgebraicClosure F) (Fin m))
  let B1 := B0.reindex e
  have hmem : ∀ j, ∃ v, b v = B1 j := fun j => by
    have h : B1 j ∈ s := by
      simp only [B1, B0, Module.Basis.reindex_apply, Module.Basis.mk_apply]
      exact Subtype.mem _
    exact hs h
  choose c hc using hmem
  let P := (Pi.basisFun (AlgebraicClosure F) (Fin m)).toMatrix B1
  let _ := (Pi.basisFun (AlgebraicClosure F) (Fin m)).invertibleToMatrix B1
  let U : GL (Fin m) (AlgebraicClosure F) := unitOfInvertible P
  have hP : ∀ i j, P i j = b (c j) i := by
    intro i j
    simp [P, Module.Basis.toMatrix_apply, hc]
  have hrel : ∀ σ, a.toFun σ * galGL m σ U = U := by
    intro σ
    ext i j
    rw [Units.val_mul, coe_galGL]
    change ((a.toFun σ : Matrix (Fin m) (Fin m) (AlgebraicClosure F)) *
      P.map (σ : AlgebraicClosure F →+* AlgebraicClosure F)) i j = P i j
    have := congrFun (key σ (c j)) i
    rw [Matrix.mul_apply, hP]
    rw [← this]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hP]
    rfl
  refine ⟨U⁻¹, fun σ => ?_⟩
  rw [inv_inv, map_inv]
  exact eq_mul_inv_of_mul_eq (hrel σ)

end GSpinGGP
