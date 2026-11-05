/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.Hilbert90
import TauCeti.RingTheory.Semisimple.SimpleArtinian

/-!
# Hilbert 90 for the units of a simple algebra

Let `Ā` be an `F̄`-algebra with a semilinear action of `Γ_F` by ring automorphisms, and let
`ι : A → Ā` be an `F`-algebra map from a simple `F`-algebra `A` sending an `F`-basis of `A` to a
Galois-fixed `F̄`-basis of `Ā` (`Ā = F̄ ⊗ A`). Then every continuous `1`-cocycle `v` with values in
`Āˣ` is a coboundary: `v_σ = u⁻¹ σ(u)` (`exists_units_eq_inv_mul_act`).

Proof (own work, standard): the twisted fixed vectors `B = {z : σ(z) = z v_σ}` form a left
`A`-module; in coordinates, Hilbert 90 for `GL_N` (`hilbert90_GL`, applied to the matrices of right
multiplication by `v_σ⁻¹`) shows that `B` has `F`-dimension `N = dim A` and spans `Ā` over `F̄`.
(`exists_rmat_eq`, `exists_twisted_basis`)
Since `A` is simple, `B ≅ A` (Tau Ceti `IsSimpleRing.nonempty_linearEquiv_of_finrank_eq`), so
`B = A u`; then `Ā = Ā u`,
`u` is a unit, and `σ(u) = u v_σ`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Matrix

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]



/-- `t : Γ_F → X` is continuous: it factors through `Gal(E/F)` for a finite extension `E`. -/
def IsGalContinuous {X : Type*} (t : GalF F → X) : Prop :=
  ∃ E : IntermediateField F (AlgebraicClosure F), FiniteDimensional F E ∧
    ∀ σ τ : GalF F, (∀ e ∈ E, σ e = τ e) → t σ = t τ

theorem IsGalContinuous.mul {G : Type*} [Mul G] {t s : GalF F → G} (ht : IsGalContinuous t)
    (hs : IsGalContinuous s) : IsGalContinuous (t * s) := by
  obtain ⟨E₁, h₁, he₁⟩ := ht
  obtain ⟨E₂, h₂, he₂⟩ := hs
  refine ⟨E₁ ⊔ E₂, inferInstance, fun σ τ h => ?_⟩
  simp only [Pi.mul_apply]
  rw [he₁ σ τ fun e he => h e (le_sup_left (a := E₁) he),
    he₂ σ τ fun e he => h e (le_sup_right (a := E₁) he)]

theorem IsGalContinuous.inv {G : Type*} [Inv G] {t : GalF F → G} (ht : IsGalContinuous t) :
    IsGalContinuous t⁻¹ := by
  obtain ⟨E, hE, h⟩ := ht
  exact ⟨E, hE, fun σ τ hστ => by simp only [Pi.inv_apply, h σ τ hστ]⟩

/-- A semilinear action of `Γ_F` on an `F̄`-algebra by ring automorphisms, fixing a basis. -/
structure GalAlgAction (F : Type) [NontriviallyNormedField F] [PAdicField F] (Ā : Type*) [Ring Ā]
    [Algebra (AlgebraicClosure F) Ā] {N : ℕ} (e : Module.Basis (Fin N) (AlgebraicClosure F) Ā) where
  /-- `σ` acting on `Ā` -/
  act : GalF F → Ā →+* Ā
  act_mul : ∀ σ τ z, act (σ * τ) z = act σ (act τ z)
  act_smul : ∀ σ (c : AlgebraicClosure F) z, act σ (c • z) = σ c • act σ z
  act_basis : ∀ σ i, act σ (e i) = e i

set_option hygiene false in
local notation "Kb" => AlgebraicClosure F

variable {Ā : Type*} [Ring Ā] [Algebra Kb Ā] [Algebra F Ā] [IsScalarTower F Kb Ā] {N : ℕ}
  {e : Module.Basis (Fin N) Kb Ā}
  {A : Type*} [Ring A] [Algebra F A] [IsSimpleRing A]

namespace GalAlgAction

variable (G : GalAlgAction F Ā e)

/-- `σ` acts on coordinates. -/
theorem repr_act (σ : GalF F) (z : Ā) (i : Fin N) : e.repr (G.act σ z) i = σ (e.repr z i) := by
  conv_lhs => rw [← e.sum_repr z]
  simp only [map_sum, G.act_smul, G.act_basis]
  rw [← map_sum (e.repr), e.repr_sum_self]

/-- The matrix of right multiplication by `w`. -/
def rmat (w : Ā) : Matrix (Fin N) (Fin N) Kb :=
  LinearMap.toMatrix e e (LinearMap.mulRight Kb w)

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

/-- Hilbert 90 for `GL_N` applied to the matrices of right multiplication by `v_σ⁻¹`:
`ρ(v_σ) = σ(M)⁻¹ M`. -/
theorem exists_rmat_eq (G : GalAlgAction F Ā e) (v : GalF F → Āˣ) (hv : IsGalContinuous v)
    (hcoc : ∀ σ τ, (v (σ * τ) : Ā) = v σ * G.act σ (v τ)) :
    ∃ M : GL (Fin N) Kb, ∀ σ, GalAlgAction.rmat (e := e) (v σ : Ā) =
      (((M⁻¹ : GL (Fin N) Kb) : Matrix (Fin N) (Fin N) Kb).map σ) *
        (M : Matrix (Fin N) (Fin N) Kb) := by
  classical
  -- the `GL_N` cocycle `a_σ = ρ(v_σ⁻¹)`
  have hinv : ∀ σ τ, (((v (σ * τ))⁻¹ : Āˣ) : Ā) =
      G.act σ (((v τ)⁻¹ : Āˣ) : Ā) * (((v σ)⁻¹ : Āˣ) : Ā) := fun σ τ => by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hcoc, mul_assoc, ← mul_assoc (G.act σ _), ← map_mul, Units.mul_inv, map_one, one_mul,
      Units.mul_inv]
  let a : GalF F → GL (Fin N) Kb := fun σ =>
    ⟨GalAlgAction.rmat (e := e) (((v σ)⁻¹ : Āˣ) : Ā), GalAlgAction.rmat (e := e) (v σ : Ā),
      by rw [← GalAlgAction.rmat_mul, Units.mul_inv, GalAlgAction.rmat_one],
      by rw [← GalAlgAction.rmat_mul, Units.inv_mul, GalAlgAction.rmat_one]⟩
  let c : GalCocycle (⊤ : Subgroup (GL (Fin N) Kb)) :=
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
  refine ⟨M, fun σ => ?_⟩
  have h := congrArg (fun g : GL (Fin N) Kb =>
    ((g⁻¹ : GL (Fin N) Kb) : Matrix (Fin N) (Fin N) Kb)) (hM σ)
  simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← map_inv, coe_galGL] at h
  exact h

/-- **The twisted-fixed basis.** There is an `F̄`-basis `β` of `Ā` of vectors with
`σ(β_j) = β_j v_σ`, in which every twisted-fixed vector has coordinates in `F`. -/
theorem exists_twisted_basis (G : GalAlgAction F Ā e) (v : GalF F → Āˣ) (hv : IsGalContinuous v)
    (hcoc : ∀ σ τ, (v (σ * τ) : Ā) = v σ * G.act σ (v τ)) :
    ∃ (β : Fin N → Ā) (c : Ā → Fin N → Kb), (∀ σ j, G.act σ (β j) = β j * v σ) ∧
      (∀ z, z = ∑ j, c z j • β j) ∧
      (∀ z, (∀ σ, G.act σ z = z * v σ) → ∀ j, ∃ f : F, algebraMap F Kb f = c z j) ∧
      (∀ y : Fin N → Kb, ∑ j, y j • β j = 0 → y = 0) := by
  classical
  obtain ⟨M, hrv⟩ := exists_rmat_eq G v hv hcoc
  have hMM : (M : Matrix (Fin N) (Fin N) Kb) *
      ((M⁻¹ : GL (Fin N) Kb) : Matrix (Fin N) (Fin N) Kb) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMM' : ((M⁻¹ : GL (Fin N) Kb) : Matrix (Fin N) (Fin N) Kb) *
      (M : Matrix (Fin N) (Fin N) Kb) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set Mi : Matrix (Fin N) (Fin N) Kb := ((M⁻¹ : GL (Fin N) Kb) : Matrix (Fin N) (Fin N) Kb)
  set Mm : Matrix (Fin N) (Fin N) Kb := (M : Matrix (Fin N) (Fin N) Kb)
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
      algebraMap F Kb f = (Mm *ᵥ e.equivFun z) j := by
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
  refine ⟨β, fun z => Mm *ᵥ e.equivFun z, hβB, hspan, hrat, fun y hy => ?_⟩
  have h1 := congrArg e.equivFun hy
  rw [map_sum, map_zero] at h1
  simp only [map_smul, hβc] at h1
  rw [hcomb] at h1
  rw [← Matrix.one_mulVec y, ← hMM, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]

/-- **Hilbert 90 for `Āˣ`.** -/
theorem exists_units_eq_inv_mul_act (G : GalAlgAction F Ā e) (ι : A →ₐ[F] Ā)
    (b : Module.Basis (Fin N) F A) (hb : ∀ i, ι (b i) = e i)
    (v : GalF F → Āˣ) (hv : IsGalContinuous v)
    (hcoc : ∀ σ τ, (v (σ * τ) : Ā) = v σ * G.act σ (v τ)) :
    ∃ u : Āˣ, ∀ σ, (v σ : Ā) = (u⁻¹ : Āˣ) * G.act σ u := by
  classical
  obtain ⟨β, c, hβB, hspan, hrat, hind⟩ := exists_twisted_basis G v hv hcoc
  -- `ι(A)` is Galois-fixed
  have hιfix : ∀ σ a, G.act σ (ι a) = ι a := by
    intro σ a
    rw [← b.sum_repr a, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hb, ← algebraMap_smul Kb (b.repr a i) (e i), G.act_smul,
      G.act_basis, AlgEquiv.commutes]
  -- `B = {z : σ(z) = z v_σ}` as a left `A`-module
  let _ : Module A Ā := Module.compHom Ā ι.toRingHom
  have : IsScalarTower F A Ā := ⟨fun c a z => by
    change ι (c • a) * z = c • (ι a * z)
    rw [map_smul, smul_mul_assoc]⟩
  let B : Submodule A Ā :=
    { carrier := {z | ∀ σ, G.act σ z = z * v σ}
      add_mem' := fun {x y} hx hy σ => by rw [map_add, hx σ, hy σ, add_mul]
      zero_mem' := fun σ => by rw [map_zero, zero_mul]
      smul_mem' := fun a z hz σ => by
        change G.act σ (ι a * z) = ι a * z * v σ
        rw [map_mul, hιfix, hz σ, mul_assoc] }
  let βB : Fin N → B := fun j => ⟨β j, fun σ => hβB σ j⟩
  have hli : LinearIndependent F βB := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : ∑ j, (algebraMap F Kb (g j)) • β j = 0 := by
      have := congrArg Subtype.val hg
      simpa [βB, algebraMap_smul] using this
    have h2 := hind _ h0
    intro j
    exact (algebraMap F Kb).injective (by simpa using congrFun h2 j)
  have hsp : ⊤ ≤ Submodule.span F (Set.range βB) := by
    rintro ⟨z, hz⟩ -
    choose f hf using hrat z hz
    have : (⟨z, hz⟩ : B) = ∑ j, f j • βB j := by
      apply Subtype.ext
      show z = ((∑ j, f j • βB j : B) : Ā)
      conv_lhs => rw [hspan z]
      simp only [Submodule.coe_sum, βB]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hf, algebraMap_smul]
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let bB := Module.Basis.mk hli hsp
  have : FiniteDimensional F B := Module.Finite.of_basis bB
  have : FiniteDimensional F A := Module.Finite.of_basis b
  obtain ⟨f⟩ := IsSimpleRing.nonempty_linearEquiv_of_finrank_eq F (R := A) (M := A) (N := B)
    (by rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis bB])
  -- `u = f(1)`, `B = A u`
  set u : Ā := (f 1 : Ā)
  have hfu : ∀ x : A, (f x : Ā) = ι x * u := fun x => by
    have : f x = x • f 1 := by rw [← map_smul, smul_eq_mul, mul_one]
    rw [this]
    rfl
  -- a left inverse of `u`
  set y : Ā := ∑ j, c 1 j • ι (f.symm (βB j))
  have hyu : y * u = 1 := by
    rw [Finset.sum_mul]
    conv_rhs => rw [hspan 1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, ← hfu, LinearEquiv.apply_symm_apply]
  -- so `u` is a unit (`Ā` is finite-dimensional over `F̄`, hence Dedekind-finite)
  have : FiniteDimensional Kb Ā := Module.Finite.of_basis e
  have : IsArtinianRing Ā := IsArtinianRing.of_finite Kb Ā
  have huy : u * y = 1 := mul_eq_one_symm hyu
  refine ⟨⟨u, y, huy, hyu⟩, fun σ => ?_⟩
  show (v σ : Ā) = y * G.act σ u
  rw [(f 1).2 σ, ← mul_assoc, hyu, one_mul]

end GSpinGGP
