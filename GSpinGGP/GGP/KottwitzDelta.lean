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

omit [PAdicField F] in
theorem IsGalContinuous.mul {G : Type*} [Mul G] {t s : GalF F → G} (ht : IsGalContinuous t)
    (hs : IsGalContinuous s) : IsGalContinuous (t * s) := by
  obtain ⟨E₁, h₁, he₁⟩ := ht
  obtain ⟨E₂, h₂, he₂⟩ := hs
  refine ⟨E₁ ⊔ E₂, inferInstance, fun σ τ h => ?_⟩
  simp only [Pi.mul_apply]
  rw [he₁ σ τ fun e he => h e (le_sup_left (a := E₁) he),
    he₂ σ τ fun e he => h e (le_sup_right (a := E₁) he)]

omit [PAdicField F] in
theorem IsGalContinuous.inv {G : Type*} [Inv G] {t : GalF F → G} (ht : IsGalContinuous t) :
    IsGalContinuous t⁻¹ := by
  obtain ⟨E, hE, h⟩ := ht
  exact ⟨E, hE, fun σ τ hστ => by simp only [Pi.inv_apply, h σ τ hστ]⟩

section Generic

variable {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)

/-- The obstruction `t_σ σ(t_τ) t_{στ}⁻¹` of a family `t` in `GSpin(V)(F̄)` to being a cocycle. -/
def galObstruction (t : GalF F → GSpin (Q.baseChange Kb)) (σ τ : GalF F) :
    GSpin (Q.baseChange Kb) :=
  t σ * galGS Q σ (t τ) * (t (σ * τ))⁻¹


theorem galGS_mul (σ : GalF F) (g h : GSpin (Q.baseChange Kb)) :
    galGS Q σ (g * h) = galGS Q σ g * galGS Q σ h :=
  Subtype.ext (map_mul (galCU Q σ) _ _)

theorem galGS_inv (σ : GalF F) (g : GSpin (Q.baseChange Kb)) :
    galGS Q σ g⁻¹ = (galGS Q σ g)⁻¹ :=
  Subtype.ext (map_inv (galCU Q σ) _)

theorem galGS_scalarGSpin (σ : GalF F) (c : Kbˣ) :
    galGS Q σ (scalarGSpin _ c) = scalarGSpin _ (Units.map (σ : Kb →* Kb) c) := by
  apply Subtype.ext; apply Units.ext
  show galC Q σ (algebraMap Kb _ (c : Kb)) = algebraMap Kb _ (σ c)
  exact galC_algebraMap Q σ c

/-- Central factors of a family split off its obstruction. -/
theorem galGS_one (σ : GalF F) : galGS Q σ 1 = 1 :=
  Subtype.ext (map_one (galCU Q σ))

theorem galObstruction_one (σ τ : GalF F) :
    galObstruction Q (1 : GalF F → GSpin (Q.baseChange Kb)) σ τ = 1 := by
  simp [galObstruction, galGS_one]

theorem galObstruction_mul_central (t μ : GalF F → GSpin (Q.baseChange Kb))
    (hμ : ∀ σ, μ σ ∈ (scalarGSpin (Q.baseChange Kb)).range) (σ τ : GalF F) :
    galObstruction Q (t * μ) σ τ = galObstruction Q t σ τ * galObstruction Q μ σ τ := by
  have hZ : ∀ σ, ∀ z ∈ (scalarGSpin (Q.baseChange Kb)).range,
      galGS Q σ z ∈ Subgroup.center (GSpin (Q.baseChange Kb)) := by
    rintro σ _ ⟨c, rfl⟩
    rw [galGS_scalarGSpin]; exact scalarGSpin_mem_center _ _
  have hc : ∀ z ∈ (scalarGSpin (Q.baseChange Kb)).range,
      z ∈ Subgroup.center (GSpin (Q.baseChange Kb)) := by
    rintro _ ⟨c, rfl⟩; exact scalarGSpin_mem_center _ _
  have ha := hc _ (hμ σ)
  have hb := hZ σ _ (hμ τ)
  have hk : μ σ * galGS Q σ (μ τ) * (μ (σ * τ))⁻¹ ∈ Subgroup.center (GSpin (Q.baseChange Kb)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ (hc _ (hμ (σ * τ))))
  simp only [galObstruction, Pi.mul_apply, galGS_mul]
  have e1 := Subgroup.mem_center_iff.1 ha (galGS Q σ (t τ))
  have e2 := Subgroup.mem_center_iff.1 hk (t (σ * τ))⁻¹
  calc t σ * μ σ * (galGS Q σ (t τ) * galGS Q σ (μ τ)) * (t (σ * τ) * μ (σ * τ))⁻¹
      = t σ * (μ σ * galGS Q σ (t τ)) * galGS Q σ (μ τ) * ((μ (σ * τ))⁻¹ * (t (σ * τ))⁻¹) := by
        group
    _ = t σ * galGS Q σ (t τ) * ((μ σ * galGS Q σ (μ τ) * (μ (σ * τ))⁻¹) * (t (σ * τ))⁻¹) := by
        rw [← e1]; group
    _ = _ := by rw [← e2]; group

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

theorem scalarGSpin_mem_torusFbar (c : Kbˣ) : scalarGSpin _ c ∈ d.torusFbar x :=
  ⟨Units.ext (Algebra.commutes (c : Kb) _), fun w _ => by rw [specP_scalarGSpin_eq_one]; rfl⟩

theorem specMatFbar_scalarGSpin (c : Kbˣ) : specMatFbar d.QW (scalarGSpin _ c) = 1 := by
  rw [GGPData.specMatFbar_eq_matGL_comp, MonoidHom.comp_apply, specP_scalarGSpin_eq_one, map_one]

/-- `ker P = F̄^×`, in matrices. -/
theorem mem_range_scalarGSpin_of_specMatFbar {g : GSpin (d.QW.baseChange Kb)}
    (hg : specMatFbar d.QW g = 1) : g ∈ (scalarGSpin (d.QW.baseChange Kb)).range := by
  rw [← ker_specP (isNondeg_baseChange _ d.nondeg), MonoidHom.mem_ker]
  apply GGPData.matGL_injective (d := d)
  rw [map_one, ← MonoidHom.comp_apply, ← GGPData.specMatFbar_eq_matGL_comp, hg]

theorem exists_isLift (a : GalCocycle (d.torusBarFbar x)) : ∃ t, IsLift a t := by
  classical
  let L : GL (Fin d.m) Kb → GSpin (d.QW.baseChange Kb) := fun s =>
    if h : ∃ g ∈ d.torusFbar x, specMatFbar d.QW g = s then h.choose else 1
  refine ⟨fun σ => L (a.toFun σ), ?_, fun σ => ?_⟩
  · obtain ⟨E, hE, h⟩ := a.continuous'
    exact ⟨E, hE, fun σ τ hστ => by simp only [h σ τ hστ]⟩
  · have h : ∃ g ∈ d.torusFbar x, specMatFbar d.QW g = a.toFun σ := a.mem' σ
    simp only [L, h, ↓reduceDIte]
    exact h.choose_spec

/-- The obstruction of a lift is a scalar. -/
theorem IsLift.obstruction_mem {a : GalCocycle (d.torusBarFbar x)}
    {t : GalF F → GSpin (d.QW.baseChange Kb)} (ht : IsLift a t) (σ τ : GalF F) :
    galObstruction d.QW t σ τ ∈ (scalarGSpin (d.QW.baseChange Kb)).range := by
  apply mem_range_scalarGSpin_of_specMatFbar
  simp only [galObstruction, map_mul, map_inv, specMatFbar_galGS, (ht.2 _).2, a.cocycle',
    mul_inv_cancel]

/-- Two lifts of one cocycle differ by scalars. -/
theorem IsLift.mem_range_inv_mul {a : GalCocycle (d.torusBarFbar x)}
    {t s : GalF F → GSpin (d.QW.baseChange Kb)} (ht : IsLift a t) (hs : IsLift a s) (σ : GalF F) :
    (t σ)⁻¹ * s σ ∈ (scalarGSpin (d.QW.baseChange Kb)).range := by
  apply mem_range_scalarGSpin_of_specMatFbar
  rw [map_mul, map_inv, (ht.2 σ).2, (hs.2 σ).2, inv_mul_cancel]

/-- Changing a lift by a continuous scalar family. -/
theorem IsLift.mul_scalar {a : GalCocycle (d.torusBarFbar x)}
    {t μ : GalF F → GSpin (d.QW.baseChange Kb)} (ht : IsLift a t) (hμc : IsGalContinuous μ)
    (hμ : ∀ σ, μ σ ∈ (scalarGSpin (d.QW.baseChange Kb)).range) : IsLift a (t * μ) := by
  refine ⟨ht.1.mul hμc, fun σ => ?_⟩
  obtain ⟨c, hc⟩ := hμ σ
  refine ⟨Subgroup.mul_mem _ (ht.2 σ).1 (hc ▸ scalarGSpin_mem_torusFbar c), ?_⟩
  rw [Pi.mul_apply, map_mul, ← hc, specMatFbar_scalarGSpin, mul_one, (ht.2 σ).2]

theorem DRel.of_toFun_eq {a b : GalCocycle (d.torusBarFbar x)} (h : a.toFun = b.toFun) :
    DRel a b := by
  obtain ⟨t, ht⟩ := exists_isLift a
  exact ⟨t, t, ht, ⟨ht.1, fun σ => ⟨(ht.2 σ).1, (ht.2 σ).2.trans (congrFun h σ)⟩⟩, rfl⟩

theorem DRel.refl (a : GalCocycle (d.torusBarFbar x)) : DRel a a := DRel.of_toFun_eq rfl

theorem DRel.symm {a b : GalCocycle (d.torusBarFbar x)} (h : DRel a b) : DRel b a := by
  obtain ⟨t, s, ht, hs, he⟩ := h
  exact ⟨s, t, hs, ht, he.symm⟩

theorem DRel.trans {a b e : GalCocycle (d.torusBarFbar x)} (h₁ : DRel a b) (h₂ : DRel b e) :
    DRel a e := by
  obtain ⟨t, s, ht, hs, he₁⟩ := h₁
  obtain ⟨s', r, hs', hr, he₂⟩ := h₂
  -- `s' = s λ` with `λ` scalar; use `r λ⁻¹`
  set μ : GalF F → GSpin (d.QW.baseChange Kb) := s⁻¹ * s'
  have hμ : ∀ σ, μ σ ∈ (scalarGSpin (d.QW.baseChange Kb)).range := hs.mem_range_inv_mul hs'
  have hμc : IsGalContinuous μ := hs.1.inv.mul hs'.1
  have hμi : ∀ σ, μ⁻¹ σ ∈ (scalarGSpin (d.QW.baseChange Kb)).range := fun σ =>
    Subgroup.inv_mem _ (hμ σ)
  have hs's : s' = s * μ := by ext1 σ; simp [μ]
  refine ⟨t, r * μ⁻¹, ht, hr.mul_scalar hμc.inv hμi, ?_⟩
  ext1 σ; ext1 τ
  rw [he₁, galObstruction_mul_central _ _ _ hμi]
  have h2 := congrFun (congrFun he₂ σ) τ
  rw [hs's, galObstruction_mul_central _ _ _ hμ] at h2
  rw [← h2, mul_assoc, ← galObstruction_mul_central _ _ _ hμi, mul_inv_cancel,
    galObstruction_one, mul_one]

/-- Obstructions are multiplicative on families in the commutative `T_x(F̄)`. -/
theorem galObstruction_mul_of_mem (hx : d.IsGammaElt x) {t u : GalF F → GSpin (d.QW.baseChange Kb)}
    (ht : ∀ σ, t σ ∈ d.torusFbar x) (hu : ∀ σ, u σ ∈ d.torusFbar x) (σ τ : GalF F) :
    galObstruction d.QW (t * u) σ τ = galObstruction d.QW t σ τ * galObstruction d.QW u σ τ := by
  have hc := fun {p q} (hp : p ∈ d.torusFbar x) (hq : q ∈ d.torusFbar x) =>
    GGPData.torusFbar_commute x hx hp hq
  have hC := galGS_mem_torusFbar x σ (ht τ)
  have hD := galGS_mem_torusFbar x σ (hu τ)
  have hBC := hc (hu σ) hC
  have hK : Commute (u σ * galGS d.QW σ (u τ) * (u (σ * τ))⁻¹) (t (σ * τ))⁻¹ :=
    (((hc (hu σ) (ht _)).mul_left (hc hD (ht _))).mul_left (hc (hu _) (ht _)).inv_left).inv_right
  simp only [galObstruction, Pi.mul_apply, galGS_mul]
  calc t σ * u σ * (galGS d.QW σ (t τ) * galGS d.QW σ (u τ)) * (t (σ * τ) * u (σ * τ))⁻¹
      = t σ * (u σ * galGS d.QW σ (t τ)) * galGS d.QW σ (u τ) *
          ((u (σ * τ))⁻¹ * (t (σ * τ))⁻¹) := by group
    _ = t σ * galGS d.QW σ (t τ) *
          ((u σ * galGS d.QW σ (u τ) * (u (σ * τ))⁻¹) * (t (σ * τ))⁻¹) := by rw [hBC.eq]; group
    _ = _ := by rw [hK.eq]; group

theorem DRel.mul_right (hx : d.IsGammaElt x) {a b : GalCocycle (d.torusBarFbar x)}
    (h : DRel a b) (e : GalCocycle (d.torusBarFbar x)) :
    DRel (mulOf (torusBarFbar_commute x hx) (fun σ => galGL_mem_torusBarFbar x σ) a e)
      (mulOf (torusBarFbar_commute x hx) (fun σ => galGL_mem_torusBarFbar x σ) b e) := by
  obtain ⟨t, s, ht, hs, he⟩ := h
  obtain ⟨u, hu⟩ := exists_isLift e
  have hmul : ∀ {c : GalCocycle (d.torusBarFbar x)} {r : GalF F → GSpin (d.QW.baseChange Kb)},
      IsLift c r → IsLift (mulOf (torusBarFbar_commute x hx)
        (fun σ => galGL_mem_torusBarFbar x σ) c e) (r * u) := fun {c r} hr =>
    ⟨hr.1.mul hu.1, fun σ => ⟨Subgroup.mul_mem _ (hr.2 σ).1 (hu.2 σ).1, by
      rw [Pi.mul_apply, map_mul, (hr.2 σ).2, (hu.2 σ).2]; rfl⟩⟩
  refine ⟨t * u, s * u, hmul ht, hmul hs, ?_⟩
  ext1 σ; ext1 τ
  rw [galObstruction_mul_of_mem hx (fun σ => (ht.2 σ).1) (fun σ => (hu.2 σ).1),
    galObstruction_mul_of_mem hx (fun σ => (hs.2 σ).1) (fun σ => (hu.2 σ).1), he]

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
