/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TorusFrame
import GSpinGGP.GGP.StableCocycle

/-!
# The connecting map `H¹(F, S_x) → H²(F, F̄^×)`, concretely

For `x ∈ Γ(G,H)` the exact sequence `1 → F̄^× → T_x(F̄) → S_x(F̄) → 1` has a commutative middle term
(`GGPData.torusFbar_commute`). For a cocycle `a` in `S_x` with lifts `t_σ ∈ T_x(F̄)`, the scalars
`t_σ σ(t_τ) t_{στ}⁻¹` form the obstruction to lifting `a` to a cocycle in `T_x`. We never form
`H²`: two cocycles are related (`GalCocycle.DRel`) when they have lifts with *equal* obstructions.

* `GalCocycle.DRel` is an equivalence relation, compatible with products and with cohomology in
  `S_x`.
* `DRel.of_isometryEquiv`: if `a`, `b` are the cocycles of twists `W_α`, `W_β` with `W_α ≅ W_β` over
  `F`, then `DRel a b` (`h⁻¹ t_σ σ(h)` is a lift of `b` with the same obstruction, `h` a lift of
  `φ_a⁻¹ ι⁻¹ φ_b`).
* `DRel.isometryEquiv`: conversely `DRel a b` gives `W_α ≅ W_β`, from
  `nonempty_isometryEquiv_of_gspinCocycle` (a twist whose cocycle lifts to a `1`-cocycle in
  `GSpin(U)(F̄)` is trivial; own work, by descent of the Clifford algebra and the classification of
  quadratic forms over `F` by rank, discriminant and Clifford invariant).
-/

noncomputable section

open QuadraticMap
open scoped TensorProduct

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

/-- `t : Γ_F → X` is continuous: it factors through `Gal(E/F)` for a finite extension `E`. -/
def IsGalContinuous {X : Type*} (t : GalF F → X) : Prop :=
  ∃ E : IntermediateField F Kb, FiniteDimensional F E ∧
    ∀ σ τ : GalF F, (∀ e ∈ E, σ e = τ e) → t σ = t τ

section Generic

variable {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)

/-- The obstruction `t_σ σ(t_τ) t_{στ}⁻¹` of a family `t` in `GSpin(V)(F̄)` to being a cocycle. -/
def galObstruction (t : GalF F → GSpin (Q.baseChange Kb)) (σ τ : GalF F) :
    GSpin (Q.baseChange Kb) :=
  t σ * galGS Q σ (t τ) * (t (σ * τ))⁻¹

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]

/-- **A twist whose cocycle lifts to `GSpin` is trivial.** If `ψ : U_{F̄} ≅ U'_{F̄}` and its cocycle
`σ ↦ ψ⁻¹ ∘ σψ` is `P(v_σ)` for a continuous `1`-cocycle `v` in `GSpin(U)(F̄)`, then `U ≅ U'` over
`F`. (Own work: `v` twists `C(U)` into `C(U')` by inner automorphisms; Hilbert 90 for the units of
`C(U)` or `C⁺(U)` shows the twisted algebra is isomorphic to the untwisted one, so `U`, `U'` have the
same Clifford invariant; they have the same rank and discriminant, so they are isometric by the
classification of quadratic forms over `F`.) -/
theorem nonempty_isometryEquiv_of_gspinCocycle [FiniteDimensional F V₁] {Q₁ : QuadraticForm F V₁}
    {Q₂ : QuadraticForm F V₂} (hQ₁ : IsNondeg Q₁)
    (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb))
    (v : GalF F → GSpin (Q₁.baseChange Kb)) (hv : IsGalContinuous v)
    (hcoc : ∀ σ τ, v (σ * τ) = v σ * galGS Q₁ σ (v τ))
    (hlift : ∀ σ w, specP _ (v σ) w = ψ.symm (galIso σ ψ w)) :
    Nonempty (Q₁.IsometryEquiv Q₂) :=
  sorry

end Generic

namespace GalCocycle

variable {d : GGPData F} {x : ↥(GSpin d.QW)}

/-- `t` is a continuous lift of the cocycle `a` to `T_x(F̄)`. -/
def IsLift (a : GalCocycle (d.torusBarFbar x)) (t : GalF F → GSpin (d.QW.baseChange Kb)) :
    Prop :=
  IsGalContinuous t ∧ ∀ σ, t σ ∈ d.torusFbar x ∧ specMatFbar d.QW (t σ) = a.toFun σ

/-- Two cocycles in `S_x` have lifts to `T_x(F̄)` with equal obstructions. -/
def DRel (a b : GalCocycle (d.torusBarFbar x)) : Prop :=
  ∃ t s, IsLift a t ∧ IsLift b s ∧ galObstruction d.QW t = galObstruction d.QW s

theorem exists_isLift (a : GalCocycle (d.torusBarFbar x)) : ∃ t, IsLift a t :=
  sorry

theorem DRel.of_toFun_eq {a b : GalCocycle (d.torusBarFbar x)} (h : a.toFun = b.toFun) :
    DRel a b := by
  obtain ⟨t, ht⟩ := exists_isLift a
  exact ⟨t, t, ht, ⟨ht.1, fun σ => ⟨(ht.2 σ).1, (ht.2 σ).2.trans (congrFun h σ)⟩⟩, rfl⟩

theorem DRel.refl (a : GalCocycle (d.torusBarFbar x)) : DRel a a := DRel.of_toFun_eq rfl

theorem DRel.symm {a b : GalCocycle (d.torusBarFbar x)} (h : DRel a b) : DRel b a := by
  obtain ⟨t, s, ht, hs, he⟩ := h
  exact ⟨s, t, hs, ht, he.symm⟩

theorem DRel.trans {a b e : GalCocycle (d.torusBarFbar x)} (h₁ : DRel a b) (h₂ : DRel b e) :
    DRel a e :=
  sorry

theorem DRel.mul_right (hx : d.IsGammaElt x) {a b : GalCocycle (d.torusBarFbar x)}
    (h : DRel a b) (e : GalCocycle (d.torusBarFbar x)) :
    DRel (mulOf (torusBarFbar_commute x hx) (fun σ => galGL_mem_torusBarFbar x σ) a e)
      (mulOf (torusBarFbar_commute x hx) (fun σ => galGL_mem_torusBarFbar x σ) b e) :=
  sorry

/-- The inverse `σ ↦ a_σ⁻¹` of a cocycle with values in the commutative, Galois-stable `S_x`. -/
def invOf (hx : d.IsGammaElt x) (a : GalCocycle (d.torusBarFbar x)) :
    GalCocycle (d.torusBarFbar x) where
  toFun σ := (a.toFun σ)⁻¹
  mem' σ := Subgroup.inv_mem _ (a.mem' σ)
  cocycle' σ τ := by
    rw [a.cocycle', map_inv, mul_inv_rev]
    exact (torusBarFbar_commute x hx _ (galGL_mem_torusBarFbar x σ _ (a.mem' τ)) _
      (a.mem' σ)).inv_inv.eq
  continuous' := by
    obtain ⟨E, hE, h⟩ := a.continuous'
    exact ⟨E, hE, fun σ τ hστ => by rw [h σ τ hστ]⟩

theorem DRel.of_rel {a b : GalCocycle (d.torusBarFbar x)} (h : Rel a b) : DRel a b :=
  sorry

theorem DRel.of_isometryEquiv {Q₁ Q₂ : QuadraticForm F (Fin d.m → F)}
    {a b : GalCocycle (d.torusBarFbar x)} (ha : IsTwistBy d.QW Q₁ a.toFun)
    (hb : IsTwistBy d.QW Q₂ b.toFun) (h : Nonempty (Q₁.IsometryEquiv Q₂)) : DRel a b :=
  sorry

theorem DRel.isometryEquiv {Q₁ Q₂ : QuadraticForm F (Fin d.m → F)}
    {a b : GalCocycle (d.torusBarFbar x)} (ha : IsTwistBy d.QW Q₁ a.toFun)
    (hb : IsTwistBy d.QW Q₂ b.toFun) (h : DRel a b) : Nonempty (Q₁.IsometryEquiv Q₂) :=
  sorry

end GalCocycle

end GSpinGGP
