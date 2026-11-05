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

open TwistDescent

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
variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]

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

omit [PAdicField F] in
/-- An element of `F̄ ⊗ M` is moved the same way by Galois elements agreeing on a finite
extension. -/
theorem exists_finite_map_tensor {M : Type*} [AddCommGroup M] [Module F M] (z : Kb ⊗[F] M) :
    ∃ E : IntermediateField F Kb, FiniteDimensional F E ∧ ∀ σ τ : GalF F, (∀ e ∈ E, σ e = τ e) →
      TensorProduct.map (σ : Kb →ₗ[F] Kb) LinearMap.id z =
        TensorProduct.map (τ : Kb →ₗ[F] Kb) LinearMap.id z := by
  induction z using TensorProduct.inductionOn with
  | tmul k m =>
    refine ⟨IntermediateField.adjoin F {k}, IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral k), fun σ τ h => ?_⟩
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    congr 1
    exact h k (IntermediateField.mem_adjoin_simple_self F k)
  | add z w hz hw =>
    obtain ⟨E₁, h₁, he₁⟩ := hz
    obtain ⟨E₂, h₂, he₂⟩ := hw
    refine ⟨E₁ ⊔ E₂, inferInstance, fun σ τ h => ?_⟩
    rw [map_add, map_add, he₁ σ τ fun e he => h e (le_sup_left (a := E₁) he),
      he₂ σ τ fun e he => h e (le_sup_right (a := E₁) he)]

/-- `σ ↦ σ(g)` is continuous for a fixed `g ∈ GSpin(V)(F̄)`. -/
theorem isGalContinuous_galGS (g : GSpin (Q.baseChange Kb)) :
    IsGalContinuous (fun σ => galGS Q σ g) := by
  obtain ⟨E, hE, h⟩ := exists_finite_map_tensor
    (CliffordAlgebra.toBaseChange Kb Q
      ((g : (CliffordAlgebra (Q.baseChange Kb))ˣ) : CliffordAlgebra (Q.baseChange Kb)))
  refine ⟨E, hE, fun σ τ hστ => Subtype.ext (Units.ext ?_)⟩
  show galC Q σ _ = galC Q τ _
  simp only [galC, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  congr 1
  exact h σ τ hστ

theorem galGS_galGS (σ τ : GalF F) (g : GSpin (Q.baseChange Kb)) :
    galGS Q σ (galGS Q τ g) = galGS Q (σ * τ) g :=
  Subtype.ext (Units.ext (galC_galC Q σ τ _))

/-- Conjugating a family by a fixed `h`, twisted by the Galois action: `h⁻¹ t_σ σ(h)`. -/
def galConj (h : GSpin (Q.baseChange Kb)) (t : GalF F → GSpin (Q.baseChange Kb)) (σ : GalF F) :
    GSpin (Q.baseChange Kb) :=
  h⁻¹ * t σ * galGS Q σ h

/-- The obstruction of `h⁻¹ t_σ σ(h)` is the conjugate of that of `t`. -/
theorem galObstruction_galConj (h : GSpin (Q.baseChange Kb)) (t : GalF F → GSpin (Q.baseChange Kb))
    (σ τ : GalF F) :
    galObstruction Q (galConj Q h t) σ τ = h⁻¹ * galObstruction Q t σ τ * h := by
  simp only [galObstruction, galConj, galGS_mul, galGS_inv, galGS_galGS]
  group

theorem isGalContinuous_galConj (h : GSpin (Q.baseChange Kb)) {t : GalF F → GSpin (Q.baseChange Kb)}
    (ht : IsGalContinuous t) : IsGalContinuous (galConj Q h t) :=
  IsGalContinuous.mul (IsGalContinuous.mul
    (⟨⊥, inferInstance, fun _ _ _ => rfl⟩ : IsGalContinuous (fun _ : GalF F => h⁻¹)) ht)
    (isGalContinuous_galGS Q h)

theorem galGS_one (σ : GalF F) : galGS Q σ 1 = 1 :=
  Subtype.ext (map_one (galCU Q σ))

theorem galObstruction_one (σ τ : GalF F) :
    galObstruction Q (1 : GalF F → GSpin (Q.baseChange Kb)) σ τ = 1 := by
  simp [galObstruction, galGS_one]

/-- Central factors of a family split off its obstruction. -/
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

/-- **Twists with equal obstructions are isometric.** Let `φᵢ : U_{F̄} ≅ Uᵢ_{F̄}` (`i = 1, 2`) and
let `t`, `s` be continuous lifts to `GSpin(U)(F̄)` of their cocycles `σ ↦ φᵢ⁻¹ ∘ σφᵢ` with equal
obstructions `t_σ σ(t_τ) t_{στ}⁻¹ = s_σ σ(s_τ) s_{στ}⁻¹`. Then `U₁ ≅ U₂` over `F`.

Own work (the injectivity of the connecting map `H¹(F, SO(U)) → H²(F, F̄^×)` of
`1 → F̄^× → GSpin(U) → SO(U) → 1` on twists, without `H²`): `σ ↦ s_σ t_σ⁻¹`, transported by
`C(φ₁)`, is a `1`-cocycle in `GSpin(U₁)(F̄)` lifting the cocycle of `φ₂ φ₁⁻¹`; Hilbert 90 for the
units of the Clifford algebra `C(U₁)` (or of `C⁺(U₁)`, whichever is central simple) shows the twisted
algebra, which is `C(U₂)` (resp. `C⁺(U₂)`), is isomorphic to `C(U₁)` (resp. `C⁺(U₁)`). So `U₁`, `U₂`
have the same rank, discriminant and Clifford invariant, and are isometric by the classification of
quadratic forms over `p`-adic fields (Tau Ceti's
`RegularFormClass.eq_iff_rank_eq_and_signedDiscr_eq_and_cliffordInvariant_eq`). -/
theorem nonempty_isometryEquiv_of_galObstruction_eq [FiniteDimensional F V] (hQ : IsNondeg Q)
    {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}
    (φ₁ : (Q.baseChange Kb).IsometryEquiv (Q₁.baseChange Kb))
    (φ₂ : (Q.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb))
    (t s : GalF F → GSpin (Q.baseChange Kb)) (ht : IsGalContinuous t) (hs : IsGalContinuous s)
    (hta : ∀ σ w, specP _ (t σ) w = φ₁.symm (galIso σ φ₁ w))
    (hsb : ∀ σ w, specP _ (s σ) w = φ₂.symm (galIso σ φ₂ w))
    (hobs : galObstruction Q t = galObstruction Q s) :
    Nonempty (Q₁.IsometryEquiv Q₂) :=
  sorry

end Generic

section Reflection


variable {V : Type*} [AddCommGroup V] [Module F V]

theorem polar_baseChange_galV (Q : QuadraticForm F V) (σ : GalF F) (a b : Kb ⊗[F] V) :
    polar (Q.baseChange Kb) (galV σ a) (galV σ b) = σ (polar (Q.baseChange Kb) a b) := by
  simp only [polar, ← map_add, baseChange_galV, map_sub]

/-- A nondegenerate form on a nonzero space has an anisotropic vector. -/
theorem exists_apply_ne_zero_of_isNondeg {m : ℕ} {Q : QuadraticForm F (Fin m → F)} (hQ : IsNondeg Q)
    (hm : m ≠ 0) : ∃ u, Q u ≠ 0 := by
  by_contra h
  push Not at h
  have h0 := hQ.1 (Pi.single ⟨0, Nat.pos_of_ne_zero hm⟩ 1) fun b => by
    have h2 := polar_eq_two_mul_bform Q (Pi.single ⟨0, Nat.pos_of_ne_zero hm⟩ 1) b
    rw [QuadraticMap.polar, h, h, h, sub_zero, sub_zero] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left two_ne_zero
  exact one_ne_zero (congrFun h0 ⟨0, Nat.pos_of_ne_zero hm⟩ ▸ (Pi.single_eq_same _ _).symm)

/-- **A rational reflection, over `F̄`**: an isometry of `Q_{F̄}` of determinant `−1` whose matrix
is Galois-fixed. -/
theorem exists_galFixed_det_neg_one {m : ℕ} {Q : QuadraticForm F (Fin m → F)} (hQ : IsNondeg Q)
    (hm : m ≠ 0) :
    ∃ r : (Q.baseChange Kb).IsometryEquiv (Q.baseChange Kb),
      (∀ σ, galGL m σ (glOf r) = glOf r) ∧ (glOf r : Matrix (Fin m) (Fin m) Kb).det = -1 := by
  obtain ⟨u, hu⟩ := exists_apply_ne_zero_of_isNondeg hQ hm
  set v : Kb ⊗[F] (Fin m → F) := (1 : Kb) ⊗ₜ u
  have hv : Q.baseChange Kb v = algebraMap F Kb (Q u) := by
    simp [v, QuadraticForm.baseChange_tmul, Algebra.algebraMap_eq_smul_one]
  have hv0 : Q.baseChange Kb v ≠ 0 := by
    rw [hv]; exact (map_ne_zero _).2 hu
  have := invertibleOfNonzero hv0
  let R := TauCeti.QuadraticMap.reflection (Q.baseChange Kb) v
  let r : (Q.baseChange Kb).IsometryEquiv (Q.baseChange Kb) :=
    ⟨R, fun w => TauCeti.QuadraticMap.reflection_mem_orthogonalGroup _ v w⟩
  have hR : ∀ w, R w = w - (⅟(Q.baseChange Kb v) * polar (Q.baseChange Kb) v w) • v :=
    TauCeti.QuadraticMap.reflection_apply _ v
  have hgalv : ∀ σ : GalF F, galV σ v = v := fun σ => by simp [v, galV_tmul]
  refine ⟨r, fun σ => ?_, ?_⟩
  · rw [← glOf_galIso]
    refine glOf_congr fun w => ?_
    show galV σ (R (galV σ⁻¹ w)) = R w
    have hpol : σ (polar (Q.baseChange Kb) v (galV σ⁻¹ w)) = polar (Q.baseChange Kb) v w := by
      rw [← polar_baseChange_galV, hgalv, galV_galV_inv]
    have hinv : σ (⅟(Q.baseChange Kb v)) = ⅟(Q.baseChange Kb v) := by
      rw [invOf_eq_inv, map_inv₀, hv, AlgEquiv.commutes]
    rw [hR, hR, map_sub, galV_smul, galV_galV_inv, hgalv, map_mul, hpol, hinv]
  · rw [coe_glOf, LinearMap.det_toMatrix]
    show LinearMap.det (R : (Kb ⊗[F] (Fin m → F)) →ₗ[Kb] _) = -1
    rw [← LinearEquiv.coe_det, TauCeti.QuadraticMap.det_reflection]
    rfl

end Reflection

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

/-- A conjugate `h⁻¹ t_σ σ(h)` of a lift of `a` is a lift of the cocycle `P(h)⁻¹ a_σ σ(P(h))`, with
the same obstruction. -/
theorem IsLift.conj {a b : GalCocycle (d.torusBarFbar x)} {t : GalF F → GSpin (d.QW.baseChange Kb)}
    (ht : IsLift a t) {h : GSpin (d.QW.baseChange Kb)}
    (hb : ∀ σ, b.toFun σ = (specMatFbar d.QW h)⁻¹ * a.toFun σ * galGL d.m σ (specMatFbar d.QW h))
    (hbmem : ∀ σ, galConj d.QW h t σ ∈ d.torusFbar x) :
    IsLift b (galConj d.QW h t) ∧
      galObstruction d.QW (galConj d.QW h t) = galObstruction d.QW t := by
  refine ⟨⟨isGalContinuous_galConj d.QW h ht.1, fun σ => ⟨hbmem σ, ?_⟩⟩, ?_⟩
  · rw [hb, GSpinGGP.galConj, map_mul, map_mul, map_inv, specMatFbar_galGS, (ht.2 σ).2]
  · ext1 σ; ext1 τ
    rw [galObstruction_galConj]
    obtain ⟨c, hc⟩ := ht.obstruction_mem σ τ
    rw [← hc, Subgroup.mem_center_iff.1 (scalarGSpin_mem_center _ c) h⁻¹, inv_mul_cancel_right]

theorem DRel.of_rel {a b : GalCocycle (d.torusBarFbar x)} (h : Rel a b) : DRel a b := by
  obtain ⟨c, hc, hb⟩ := h
  obtain ⟨g, hg, rfl⟩ := hc
  obtain ⟨t, ht⟩ := exists_isLift a
  have := ht.conj hb fun σ => Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg)
    (ht.2 σ).1) (galGS_mem_torusFbar x σ hg)
  exact ⟨t, _, ht, this.1, this.2.symm⟩

/-- An element of `GSpin(W)(F̄)` whose image lies in `S_x(F̄)` lies in `T_x(F̄)`. -/
theorem mem_torusFbar_of_specMatFbar_mem {g : GSpin (d.QW.baseChange Kb)}
    (hg : specMatFbar d.QW g ∈ d.torusBarFbar x) : g ∈ d.torusFbar x := by
  obtain ⟨s, hs, hsg⟩ := hg
  obtain ⟨c, hc⟩ := mem_range_scalarGSpin_of_specMatFbar (d := d)
    (g := s⁻¹ * g) (by rw [map_mul, map_inv, hsg, inv_mul_cancel])
  have : g = s * scalarGSpin _ c := by rw [hc, mul_inv_cancel_left]
  rw [this]
  exact Subgroup.mul_mem _ hs (scalarGSpin_mem_torusFbar c)

/-- The determinant of an `F̄`-isometry of `W` is `±1`. -/
theorem det_glOf_eq_one_or {e : (d.QW.baseChange Kb).IsometryEquiv (d.QW.baseChange Kb)} :
    ((glOf e : Matrix (Fin d.m) (Fin d.m) Kb).det = 1) ∨
      ((glOf e : Matrix (Fin d.m) (Fin d.m) Kb).det = -1) := by
  have hQL := isNondeg_baseChange d.QW d.nondeg
  have hB : (bform (d.QW.baseChange Kb)).SeparatingLeft := fun w hw => hQL.1 w hw
  have hi : TauCeti.BilinForm.IsIsometry (bform (d.QW.baseChange Kb))
      (e.toLinearEquiv : (Kb ⊗[F] (Fin d.m → F)) →ₗ[Kb] _) :=
    fun u v => bform_isometry (e.toIsometry) u v
  have hsq := hi.det_sq_eq_one (Module.Free.chooseBasis Kb _)
    (mem_nonZeroDivisors_of_ne_zero ((LinearMap.separatingLeft_iff_det_ne_zero _).mp hB))
  rw [coe_glOf, LinearMap.det_toMatrix]
  exact mul_self_eq_one_iff.1 ((_root_.sq _).symm.trans hsq)

/-- **(A)**: cocycles of isometric twists are `DRel`-related. With `ψ_a, ψ_b` the isometries of the
twists (one of them corrected by a rational reflection so that `ψ_a⁻¹ ψ_b` is proper), a lift `h` of
`ψ_a⁻¹ ψ_b` to `GSpin(W)(F̄)` conjugates any lift of `a` to a lift of `b` with the same
obstruction. -/
theorem DRel.of_isometryEquiv {Q₁ Q₂ : QuadraticForm F (Fin d.m → F)} (hQ₂ : IsNondeg Q₂)
    {a b : GalCocycle (d.torusBarFbar x)} (ha : IsTwistBy d.QW Q₁ a.toFun)
    (hb : IsTwistBy d.QW Q₂ b.toFun) (h : Nonempty (Q₁.IsometryEquiv Q₂)) : DRel a b := by
  obtain ⟨e⟩ := h
  obtain ⟨φ₁, hφ₁⟩ := (isTwistBy_iff _ _ _).1 (isTwistBy_of_isometryEquiv e ha)
  obtain ⟨φ₂, hφ₂⟩ := (isTwistBy_iff _ _ _).1 hb
  -- arrange `det (ψ_a⁻¹ ψ_b) = 1`
  obtain ⟨ψ, hψb, hdet⟩ : ∃ ψ : (d.QW.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb),
      (∀ σ, b.toFun σ = (glOf ψ)⁻¹ * galGL d.m σ (glOf ψ)) ∧
        (glOf (ψ.trans φ₁.symm) : Matrix (Fin d.m) (Fin d.m) Kb).det = 1 := by
    rcases det_glOf_eq_one_or (e := φ₂.trans φ₁.symm) with h1 | h1
    · exact ⟨φ₂, hφ₂, h1⟩
    have hm : d.m ≠ 0 := by
      rintro hm0
      rw [Matrix.det_eq_one_of_card_eq_zero (by simp [hm0])] at h1
      exact absurd h1 (by norm_num)
    obtain ⟨r, hr, hrdet⟩ := exists_galFixed_det_neg_one hQ₂ hm
    refine ⟨φ₂.trans r, fun σ => ?_, ?_⟩
    · rw [hφ₂, glOf_trans, mul_inv_rev, map_mul, hr, mul_assoc, inv_mul_cancel_left]
    · have e1 : glOf ((φ₂.trans r).trans φ₁.symm) = (glOf φ₁)⁻¹ * (glOf r * glOf φ₂) := by
        rw [glOf_trans, glOf_trans, glOf_symm]
      have e2 : glOf (φ₂.trans φ₁.symm) = (glOf φ₁)⁻¹ * glOf φ₂ := by rw [glOf_trans, glOf_symm]
      rw [e2, Units.val_mul, Matrix.det_mul] at h1
      rw [e1, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hrdet]
      linear_combination -h1
  -- lift `c = ψ_a⁻¹ ψ` to `GSpin(W)(F̄)`
  set c := ψ.trans φ₁.symm
  have hcdet : LinearMap.det (c.toLinearEquiv : (Kb ⊗[F] (Fin d.m → F)) →ₗ[Kb] _) = 1 := by
    rw [← LinearMap.det_toMatrix (bcBasis F d.m), ← coe_glOf, hdet]
  obtain ⟨k, hk⟩ := gspin_specP_surjective_SO _ (isNondeg_baseChange _ d.nondeg) c.toLinearEquiv
    c.map_app hcdet
  have hkM : specMatFbar d.QW k = (glOf φ₁)⁻¹ * glOf ψ := by
    rw [← glOf_specPIso, glOf_congr (e' := c) (fun w => by
      show specP _ k w = c w
      rw [hk]; rfl), glOf_trans, glOf_symm]
  obtain ⟨t, ht⟩ := exists_isLift a
  have hbk : ∀ σ, b.toFun σ =
      (specMatFbar d.QW k)⁻¹ * a.toFun σ * galGL d.m σ (specMatFbar d.QW k) := fun σ => by
    rw [hψb, hkM, hφ₁, map_mul, map_inv]
    group
  have hmem : ∀ σ, galConj d.QW k t σ ∈ d.torusFbar x := fun σ =>
    mem_torusFbar_of_specMatFbar_mem (by
      rw [galConj, map_mul, map_mul, map_inv, specMatFbar_galGS, (ht.2 σ).2, ← hbk]
      exact b.mem' σ)
  have hl := ht.conj hbk hmem
  exact ⟨t, _, ht, hl.1, hl.2.symm⟩

/-- A lift of the cocycle `σ ↦ φ⁻¹ σ(φ)`, in matrices, acts as `φ⁻¹ ∘ σφ`. -/
theorem specP_apply_of_specMatFbar_eq {Q' : QuadraticForm F (Fin d.m → F)} {σ : GalF F}
    {g : GSpin (d.QW.baseChange Kb)} {φ : (d.QW.baseChange Kb).IsometryEquiv (Q'.baseChange Kb)}
    (h : specMatFbar d.QW g = (glOf φ)⁻¹ * galGL d.m σ (glOf φ)) (w : Kb ⊗[F] (Fin d.m → F)) :
    specP _ g w = φ.symm (galIso σ φ w) :=
  apply_eq_of_glOf_eq (e := specPIso g) (e' := (galIso σ φ).trans φ.symm)
    (by rw [glOf_specPIso, h, glOf_trans, glOf_symm, glOf_galIso]) w

/-- **(B)**: `DRel`-related cocycles are cocycles of isometric twists
(`nonempty_isometryEquiv_of_galObstruction_eq`). -/
theorem DRel.isometryEquiv {Q₁ Q₂ : QuadraticForm F (Fin d.m → F)}
    {a b : GalCocycle (d.torusBarFbar x)} (ha : IsTwistBy d.QW Q₁ a.toFun)
    (hb : IsTwistBy d.QW Q₂ b.toFun) (h : DRel a b) : Nonempty (Q₁.IsometryEquiv Q₂) := by
  obtain ⟨t, s, ht, hs, he⟩ := h
  obtain ⟨φ₁, hφ₁⟩ := (isTwistBy_iff _ _ _).1 ha
  obtain ⟨φ₂, hφ₂⟩ := (isTwistBy_iff _ _ _).1 hb
  exact nonempty_isometryEquiv_of_galObstruction_eq d.QW d.nondeg φ₁ φ₂ t s ht.1 hs.1
    (fun σ => specP_apply_of_specMatFbar_eq ((ht.2 σ).2.trans (hφ₁ σ)))
    (fun σ => specP_apply_of_specMatFbar_eq ((hs.2 σ).2.trans (hφ₂ σ))) he

end GalCocycle

end GSpinGGP
