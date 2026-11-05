/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.StableCocycle
import GSpinGGP.GGP.Descent
import GSpinGGP.Foundations.IsometryDet

/-!
# Changing the witness of a stable conjugacy

Let `C(ψ)` carry `x` to `y` (`ψ : V_{1,F̄} ≃ V_{2,F̄}` an isometry, `x`, `y` rational, `x` semisimple),
and let `θ : W'_x → W'_y` be an `F`-rational isometric map of the fixed spaces.  The endomorphism
`R = ψ⁻¹ ∘ θ ⊕ id` of `V_{1,F̄} = W'_{x,F̄} ⊕ W''_{x,F̄}` (`WitnessChange.rmap`) is an isometry
commuting with `P(x)` and trivial on the `-1`-eigenspace of `P(x)`; if `det R = 1` it is `P(k)` for some
`k ∈ GSpin(V₁)(F̄)` commuting with `x` (Steinberg, `exists_gspin_rmap`), and `ψ ∘ P(k)` is rational on
`W'_x`, so its cocycle is trivial there (`galIso_trans_symm_eq_self_of_tmul`).  Composing `θ` with a
reflection of `W'_x` fixes the sign of `det R`.

`GGPData.exists_isStableIso_of_isometry`: if `y` is stably conjugate to `x` and `W'_x ≅ W'_y` over `F`,
then some `ψ` computes the class of `y` in `H¹(F, S_x)` (a step toward the map `y ↦ [a]` of Thesis
Prop. 6.6.1(iii)).  Own work, elementary.
-/

noncomputable section

namespace GSpinGGP

open CliffordAlgebra TwistDescent TorusTransfer IsomCent
open scoped TensorProduct

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F


namespace WitnessChange

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
  {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}

/-- If `C(ψ)` carries `x` to `y`, then `ψ` intertwines `P(x)` and `P(y)`. -/
theorem apply_specP_bcGSpin (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb))
    {x : GSpin Q₁} {y : GSpin Q₂}
    (h : CliffordAlgebra.map ψ.toIsometry (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra _) =
      bcUnits Q₂ (y : (CliffordAlgebra Q₂)ˣ)) (w : Kb ⊗[F] V₁) :
    ψ (specP _ (bcGSpin Q₁ x) w) = specP _ (bcGSpin Q₂ y) (ψ w) := by
  set X := bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ)
  set Y := bcUnits Q₂ (y : (CliffordAlgebra Q₂)ˣ)
  have hinv : CliffordAlgebra.map ψ.toIsometry ((X⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) =
      ((Y⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) := by
    have h1 : CliffordAlgebra.map ψ.toIsometry ((X⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) *
        (Y : CliffordAlgebra _) = 1 := by
      rw [← h, ← map_mul, Units.inv_mul, map_one]
    calc _ = CliffordAlgebra.map ψ.toIsometry ((X⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) *
          (Y : CliffordAlgebra _) * ((Y⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]
  apply ι_injective (Q₂.baseChange Kb)
  have hι : ∀ z, ι (Q₂.baseChange Kb) (ψ z) = CliffordAlgebra.map ψ.toIsometry (ι _ z) :=
    fun z => by rw [CliffordAlgebra.map_apply_ι]; rfl
  rw [ι_specP, hι, ι_specP, hι]
  change CliffordAlgebra.map ψ.toIsometry ((X : CliffordAlgebra _) * ι _ w *
    ((X⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _)) = (Y : CliffordAlgebra _) *
      CliffordAlgebra.map ψ.toIsometry (ι _ w) * ((Y⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _)
  rw [map_mul, map_mul, h, hinv]

section Rmap

variable {x : GSpin Q₁} (hc : IsCompl (fixedSub x) (movedSub x))

/-- The projection of `V₁ = W'_x ⊕ W''_x` onto `W'_x` is `P(x)`-invariant. -/
theorem projectionOnto_specP (v : V₁) :
    (fixedSub x).projectionOnto (movedSub x) hc (specP Q₁ x v) =
      (fixedSub x).projectionOnto (movedSub x) hc v := by
  have h := (Submodule.projectionOnto_apply_eq_zero_iff hc).2 (sub_mem_movedSub (x := x) v)
  rwa [map_sub, sub_eq_zero] at h

theorem projection_specP (v : V₁) :
    (fixedSub x).projection (movedSub x) hc (specP Q₁ x v) =
      (fixedSub x).projection (movedSub x) hc v := by
  rw [← Submodule.coe_projectionOnto_apply, ← Submodule.coe_projectionOnto_apply,
    projectionOnto_specP]

theorem specP_projection (v : V₁) :
    specP Q₁ x ((fixedSub x).projection (movedSub x) hc v) =
      (fixedSub x).projection (movedSub x) hc v :=
  (mem_fixedSub_iff x _).1 (Submodule.projection_apply_mem hc v)

/-- `R = ψ⁻¹ ∘ θ ⊕ id` on `F̄ ⊗ V₁ = F̄ ⊗ W'_x ⊕ F̄ ⊗ W''_x`. -/
def rmap (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) (θ : fixedSub x →ₗ[F] V₂) :
    (Kb ⊗[F] V₁) →ₗ[Kb] (Kb ⊗[F] V₁) :=
  ψ.symm.toLinearEquiv.toLinearMap ∘ₗ
      (θ ∘ₗ (fixedSub x).projectionOnto (movedSub x) hc).baseChange Kb +
    (LinearMap.id - ((fixedSub x).projection (movedSub x) hc).baseChange Kb)

theorem rmap_tmul (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) (θ : fixedSub x →ₗ[F] V₂)
    (v : V₁) :
    rmap hc ψ θ (1 ⊗ₜ v) = ψ.symm (1 ⊗ₜ θ ((fixedSub x).projectionOnto (movedSub x) hc v)) +
      1 ⊗ₜ (v - (fixedSub x).projection (movedSub x) hc v) := by
  simp [rmap, TensorProduct.tmul_sub]

theorem rmap_tmul_of_mem (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) (θ : fixedSub x →ₗ[F] V₂)
    {a : V₁} (ha : a ∈ fixedSub x) :
    rmap hc ψ θ (1 ⊗ₜ a) = ψ.symm (1 ⊗ₜ θ ⟨a, ha⟩) := by
  rw [rmap_tmul, Submodule.projectionOnto_apply_of_mem_left hc ha,
    Submodule.projection_apply_of_mem_left hc ha, sub_self, TensorProduct.tmul_zero, add_zero]

/-- `ψ⁻¹` carries rational fixed vectors of `P(y)` to fixed vectors of `P(x)`. -/
theorem specP_symm_tmul_of_mem (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb))
    {x : GSpin Q₁} {y : GSpin Q₂}
    (h : CliffordAlgebra.map ψ.toIsometry (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra _) =
      (bcUnits Q₂ (y : (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra _)) {u : V₂} (hu : u ∈ fixedSub y) :
    specP _ (bcGSpin Q₁ x) (ψ.symm (1 ⊗ₜ u)) = ψ.symm (1 ⊗ₜ u) := by
  have hPy : specP _ (bcGSpin Q₂ y) ((1 : Kb) ⊗ₜ[F] u) = (1 : Kb) ⊗ₜ[F] specP Q₂ y u := by
    rw [← LinearEquiv.coe_coe, specP_bcGSpin]; rfl
  have e := apply_specP_bcGSpin ψ h (ψ.symm (1 ⊗ₜ u))
  rw [ψ.apply_symm_apply, hPy, show specP Q₂ y u = u from (mem_fixedSub_iff y _).1 hu] at e
  calc _ = ψ.symm (ψ (specP _ (bcGSpin Q₁ x) (ψ.symm (1 ⊗ₜ u)))) := (ψ.symm_apply_apply _).symm
    _ = _ := by rw [e]

/-- `R` commutes with `P(x)`. -/
theorem rmap_comp_specP (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) (θ : fixedSub x →ₗ[F] V₂)
    {y : GSpin Q₂}
    (h : CliffordAlgebra.map ψ.toIsometry (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra _) =
      (bcUnits Q₂ (y : (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra _)) (hθ : ∀ a, θ a ∈ fixedSub y) :
    rmap hc ψ θ ∘ₗ (specP _ (bcGSpin Q₁ x) : (Kb ⊗[F] V₁) →ₗ[Kb] _) =
      (specP _ (bcGSpin Q₁ x) : (Kb ⊗[F] V₁) →ₗ[Kb] _) ∘ₗ rmap hc ψ θ := by
  refine baseChange_hom_ext fun v => ?_
  have hP : ∀ u : V₁, specP _ (bcGSpin Q₁ x) ((1 : Kb) ⊗ₜ[F] u) = (1 : Kb) ⊗ₜ[F] specP Q₁ x u :=
    fun u => by rw [← LinearEquiv.coe_coe, specP_bcGSpin]; rfl
  have hfix : ∀ a, specP _ (bcGSpin Q₁ x) (ψ.symm (1 ⊗ₜ θ a)) = ψ.symm (1 ⊗ₜ θ a) :=
    fun a => specP_symm_tmul_of_mem ψ h (hθ a)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hP,
    rmap_tmul, rmap_tmul, map_add, hfix, projectionOnto_specP, TensorProduct.tmul_sub,
    TensorProduct.tmul_sub, map_sub, hP, hP, specP_projection, projection_specP]

/-- `R` is the identity on the `-1`-eigenspace of `P(x)`. -/
theorem rmap_of_neg (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) (θ : fixedSub x →ₗ[F] V₂)
    {w : Kb ⊗[F] V₁} (hw : specP _ (bcGSpin Q₁ x) w = -w) : rmap hc ψ θ w = w := by
  have hP : (specP _ (bcGSpin Q₁ x) : (Kb ⊗[F] V₁) →ₗ[Kb] _) =
      (specP Q₁ x : V₁ →ₗ[F] V₁).baseChange Kb := specP_bcGSpin Q₁ x
  have hw' : (specP Q₁ x : V₁ →ₗ[F] V₁).baseChange Kb w = -w := by rw [← hP]; exact hw
  have h1 := baseChange_apply_eq_zero_of_neg hw' (θ ∘ₗ (fixedSub x).projectionOnto (movedSub x) hc)
    (LinearMap.ext fun v => by simp [projectionOnto_specP])
  have h2 := baseChange_apply_eq_zero_of_neg hw' ((fixedSub x).projection (movedSub x) hc) (LinearMap.ext fun v => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ← Submodule.coe_projectionOnto_apply,
      projectionOnto_specP])
  simp [rmap, h1, h2]

/-- `R` is an isometry. -/
theorem rmap_isometry (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) (θ : fixedSub x →ₗ[F] V₂)
    {y : GSpin Q₂}
    (h : CliffordAlgebra.map ψ.toIsometry (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra _) =
      (bcUnits Q₂ (y : (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra _)) (hθ : ∀ a, θ a ∈ fixedSub y)
    (hθQ : ∀ a, Q₂ (θ a) = Q₁ a) (w : Kb ⊗[F] V₁) :
    Q₁.baseChange Kb (rmap hc ψ θ w) = Q₁.baseChange Kb w := by
  suffices e : (Q₁.baseChange Kb).comp (rmap hc ψ θ) = Q₁.baseChange Kb from
    congrArg (fun Q : QuadraticForm Kb (Kb ⊗[F] V₁) => Q w) e
  refine _root_.baseChange_ext fun v => ?_
  rw [QuadraticMap.comp_apply, rmap_tmul]
  set a := (fixedSub x).projectionOnto (movedSub x) hc v
  set b := v - (fixedSub x).projection (movedSub x) hc v
  have hv : v = (a : V₁) + b := by
    simp only [a, b, Submodule.coe_projectionOnto_apply, add_sub_cancel]
  have hb : b ∈ movedSub x := by
    simp only [b, ← Submodule.projection_eq_self_sub_projection hc]
    exact Submodule.projection_apply_mem hc.symm v
  obtain ⟨c, hcb⟩ := hb
  -- the two pieces are orthogonal
  have hfix := specP_symm_tmul_of_mem ψ h (hθ a)
  have hmov : (1 : Kb) ⊗ₜ[F] b ∈ movedSub (bcGSpin Q₁ x) := by
    refine ⟨1 ⊗ₜ c, ?_⟩
    rw [LinearMap.sub_apply, LinearMap.id_apply, ← hcb, LinearMap.sub_apply, LinearMap.id_apply,
      TensorProduct.tmul_sub, LinearEquiv.coe_coe, ← LinearEquiv.coe_coe, specP_bcGSpin]
    rfl
  have h0 := fixedSub_orthogonal_movedSub (bcGSpin Q₁ x) _
    ((mem_fixedSub_iff _ _).2 hfix) _ hmov
  have h0' := fixedSub_orthogonal_movedSub x a a.2 b ⟨c, hcb⟩
  rw [QuadraticMap.map_add (Q₁.baseChange Kb), polar_eq_two_mul_bform, h0, mul_zero, add_zero,
    ψ.symm.map_app,
    QuadraticForm.baseChange_tmul, QuadraticForm.baseChange_tmul, QuadraticForm.baseChange_tmul, hθQ,
    hv, QuadraticMap.map_add Q₁, polar_eq_two_mul_bform, h0', mul_zero, add_zero, add_smul]

/-- The reflection in `u ∈ W'_x`, restricted to `W'_x`. -/
def reflFix {u : V₁} (hu : u ∈ fixedSub x) : fixedSub x →ₗ[F] fixedSub x :=
  (quadReflection Q₁ u).restrict fun _ hv => quadReflection_mem hu hv

theorem projection_quadReflection {u : V₁} (hu : u ∈ fixedSub x) (v : V₁) :
    (fixedSub x).projection (movedSub x) hc (quadReflection Q₁ u v) =
      quadReflection Q₁ u ((fixedSub x).projection (movedSub x) hc v) := by
  have hb : v - (fixedSub x).projection (movedSub x) hc v ∈ movedSub x := by
    rw [← Submodule.projection_eq_self_sub_projection hc]
    exact Submodule.projection_apply_mem hc.symm v
  have e : quadReflection Q₁ u v = quadReflection Q₁ u ((fixedSub x).projection (movedSub x) hc v) +
      (v - (fixedSub x).projection (movedSub x) hc v) := by
    rw [← Steinberg.quadReflection_of_mem_movedSub hu hb, ← map_add, add_sub_cancel]
  rw [e, map_add, Submodule.projection_apply_of_mem_left hc
      (quadReflection_mem hu (Submodule.projection_apply_mem hc v)),
    Submodule.projection_apply_of_mem_right hc hb, add_zero]

/-- Replacing `θ` by `θ ∘ s_u` (`u ∈ W'_x`) replaces `R` by `R ∘ s_u`. -/
theorem rmap_comp_reflFix (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb))
    (θ : fixedSub x →ₗ[F] V₂) {u : V₁} (hu : u ∈ fixedSub x) :
    rmap hc ψ (θ ∘ₗ reflFix hu) = rmap hc ψ θ ∘ₗ (quadReflection Q₁ u).baseChange Kb := by
  refine baseChange_hom_ext fun v => ?_
  have hb : v - (fixedSub x).projection (movedSub x) hc v ∈ movedSub x := by
    rw [← Submodule.projection_eq_self_sub_projection hc]
    exact Submodule.projection_apply_mem hc.symm v
  have hpo : reflFix hu ((fixedSub x).projectionOnto (movedSub x) hc v) =
      (fixedSub x).projectionOnto (movedSub x) hc (quadReflection Q₁ u v) := Subtype.ext (by
    rw [Submodule.coe_projectionOnto_apply, projection_quadReflection hc hu]
    rfl)
  rw [LinearMap.comp_apply, LinearMap.baseChange_tmul, rmap_tmul, rmap_tmul, LinearMap.comp_apply,
    hpo, projection_quadReflection hc hu, ← map_sub, Steinberg.quadReflection_of_mem_movedSub hu hb]

/-- **The lift `k` of `R`**: if `det R = 1`, then `R = P(k)` with `k ∈ GSpin(V₁)(F̄)` commuting with `x`
(Steinberg: `R` commutes with `P(x)` and is trivial on its `-1`-eigenspace). -/
theorem exists_gspin_rmap [FiniteDimensional F V₁] (hQ₁ : IsNondeg Q₁)
    (hxss : Module.End.IsSemisimple (specP Q₁ x : V₁ →ₗ[F] V₁))
    (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) (θ : fixedSub x →ₗ[F] V₂)
    {y : GSpin Q₂}
    (h : CliffordAlgebra.map ψ.toIsometry (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra _) =
      (bcUnits Q₂ (y : (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra _)) (hθ : ∀ a, θ a ∈ fixedSub y)
    (hθQ : ∀ a, Q₂ (θ a) = Q₁ a) (hdet : LinearMap.det (rmap hc ψ θ) = 1) :
    ∃ k : GSpin (Q₁.baseChange Kb), (∀ w, specP _ k w = rmap hc ψ θ w) ∧ Commute k (bcGSpin Q₁ x) := by
  have hQL : IsNondeg (Q₁.baseChange Kb) := isNondeg_baseChange Q₁ hQ₁
  have hiso := rmap_isometry hc ψ θ h hθ hθQ
  obtain ⟨e, he⟩ : ∃ e : (Kb ⊗[F] V₁) ≃ₗ[Kb] (Kb ⊗[F] V₁), ∀ w, e w = rmap hc ψ θ w :=
    ⟨LinearEquiv.ofInjectiveEndo _ (TauCeti.BilinForm.IsIsometry.injective (fun w hw => hQL.1 w hw)
      (fun u v => bform_isometry (⟨rmap hc ψ θ, hiso⟩ : Q₁.baseChange Kb →qᵢ Q₁.baseChange Kb) u v)), fun _ => rfl⟩
  have he' : (e : (Kb ⊗[F] V₁) →ₗ[Kb] (Kb ⊗[F] V₁)) = rmap hc ψ θ := LinearMap.ext he
  obtain ⟨k, hk⟩ := gspin_specP_surjective_SO (Q₁.baseChange Kb) hQL e
    (fun w => by rw [he]; exact hiso w) (by rw [he']; exact hdet)
  have hkw : ∀ w, specP _ k w = rmap hc ψ θ w := fun w => by rw [hk]; exact he w
  refine ⟨k, hkw, ?_⟩
  have hsemiL : Module.End.IsSemisimple
      (specP (Q₁.baseChange Kb) (bcGSpin Q₁ x) : Kb ⊗[F] V₁ →ₗ[Kb] _) := by
    rw [specP_bcGSpin]; exact isSemisimple_baseChange_algebraicClosure hxss
  have hcomm : Commute (specP _ k) (specP _ (bcGSpin Q₁ x)) := by
    refine LinearEquiv.ext fun w => ?_
    change specP _ k (specP _ (bcGSpin Q₁ x) w) = specP _ (bcGSpin Q₁ x) (specP _ k w)
    rw [hkw, hkw]
    exact LinearMap.congr_fun (rmap_comp_specP hc ψ θ h hθ) w
  refine (Steinberg.commute_iff_det_negFixedSub hQL (bcGSpin Q₁ x) hsemiL k hcomm).2 ?_
  have hid : (specP _ k : Kb ⊗[F] V₁ →ₗ[Kb] _).restrict
      (mapsTo_eigenspace_of_commute (Steinberg.commute_toLinearMap hcomm) (-1)) = LinearMap.id := by
    ext w
    change specP _ k (w : Kb ⊗[F] V₁) = w
    rw [hkw]
    refine rmap_of_neg hc ψ θ ?_
    have hw := Module.End.mem_eigenspace_iff.1 w.2
    rw [neg_one_smul] at hw
    exact hw
  exact (congrArg LinearMap.det hid).trans LinearMap.det_id

end Rmap

end WitnessChange

namespace GGPData

open WitnessChange

variable {d : GGPData F}

/-- **Change of witness** (a step toward the map `y ↦ [a]` of Thesis Prop. 6.6.1(iii), for the case
where `a_σ` is not known to be trivial on `W'_x`): if `y` is stably conjugate to `x` (on the `W`-factor)
through `ψ = P(g) ∘ φ_α` and `W'_x ≅ W'_y` over `F`,
then `ψ' = ψ ∘ P(k)` for a suitable `k ∈ GSpin(W)(F̄)` commuting with `x` is rational on `W'_x`, so its
cocycle lies in `S_x`.  (`P(k) = ψ⁻¹ ∘ θ` on `W'_x ⊗ F̄`, identity on `W''_x ⊗ F̄`, after composing `θ`
with a reflection of `W'_x` if needed to make `det P(k) = 1`.) -/
theorem exists_isStableIso_of_isometry (τ : InnerTwist d.QW) {x : GSpin d.QW} (hx : d.IsGammaElt x)
    {y : GSpin (d.twist τ).QW}
    (hxy : StablyConjVia τ.φ (x : (CliffordAlgebra d.QW)ˣ) (y : (CliffordAlgebra τ.Q')ˣ))
    (θ : (d.QW.comp (fixedSub x).subtype).IsometryEquiv (τ.Q'.comp (fixedSub y).subtype)) :
    ∃ ψ, d.IsStableIso τ x y ψ := by
  obtain ⟨g, hg, hconj⟩ := hxy
  set g' : GSpin (τ.Q'.baseChange Kb) := ⟨g, hg⟩
  have hmap : CliffordAlgebra.map (τ.φ.trans (specPIso g')).toIsometry
      (bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra _) =
      bcUnits τ.Q' (y : (CliffordAlgebra τ.Q')ˣ) := by
    rw [← psiA_eq_map]
    exact congrArg Units.val hconj
  obtain ⟨ψ, hψ⟩ : ∃ ψ, τ.φ.trans (specPIso g') = ψ := ⟨_, rfl⟩
  have hdetψ := det_glOf_trans_specPIso τ g'
  rw [hψ] at hmap hdetψ
  have hxss := isSemisimple_specP_of_isSS d.QW x hx.1
  have hc := isCompl_fixedSub_movedSub x (fixedSub_inf_movedSub_of_isSS x hx.1)
  set θ₀ : fixedSub x →ₗ[F] (Fin d.m → F) := (fixedSub y).subtype ∘ₗ θ.toLinearEquiv.toLinearMap
  have hθ : ∀ a, θ₀ a ∈ fixedSub y := fun a => (θ a).2
  have hθQ : ∀ a, τ.Q' (θ₀ a) = d.QW a := fun a => θ.map_app a
  have hQL := isNondeg_baseChange d.QW d.nondeg
  -- choose `θ₁` with `det R = 1`
  obtain ⟨θ₁, hθ₁, hθ₁Q, hdet⟩ : ∃ θ₁ : fixedSub x →ₗ[F] (Fin d.m → F), (∀ a, θ₁ a ∈ fixedSub y) ∧
      (∀ a, τ.Q' (θ₁ a) = d.QW a) ∧ LinearMap.det (rmap hc ψ θ₁) = 1 := by
    by_cases h1 : LinearMap.det (rmap hc ψ θ₀) = 1
    · exact ⟨θ₀, hθ, hθQ, h1⟩
    have hsq : LinearMap.det (rmap hc ψ θ₀) ^ 2 = 1 := by
      have hB : (bform (d.QW.baseChange Kb)).SeparatingLeft := fun w hw => hQL.1 w hw
      have hi : TauCeti.BilinForm.IsIsometry (bform (d.QW.baseChange Kb)) (rmap hc ψ θ₀) :=
        fun u v => bform_isometry (⟨_, rmap_isometry hc ψ θ₀ hmap hθ hθQ⟩ :
          d.QW.baseChange Kb →qᵢ d.QW.baseChange Kb) u v
      exact hi.det_sq_eq_one (Module.Free.chooseBasis Kb _)
        (mem_nonZeroDivisors_of_ne_zero ((LinearMap.separatingLeft_iff_det_ne_zero _).mp hB))
    have hm1 : LinearMap.det (rmap hc ψ θ₀) = -1 :=
      (mul_self_eq_one_iff.1 ((sq _).symm.trans hsq)).resolve_left h1
    -- `W'_x ≠ 0` (else `R = id`), so it has an anisotropic vector
    obtain ⟨u, hu, hQu⟩ : ∃ u ∈ fixedSub x, d.QW u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hnd := isNondeg_fixedSub_of_isSS d.nondeg x hx.1
      have hzero : ∀ a : fixedSub x, a = 0 :=
        eq_zero_of_isNondeg_of_forall_eq_zero hnd fun a => hcon _ a.2
      apply h1
      have hid : rmap hc ψ θ₀ = LinearMap.id := by
        refine baseChange_hom_ext fun v => ?_
        change rmap hc ψ θ₀ (1 ⊗ₜ v) = 1 ⊗ₜ v
        rw [rmap_tmul, hzero ((fixedSub x).projectionOnto (movedSub x) hc v), map_zero,
          TensorProduct.tmul_zero, map_zero, zero_add, ← Submodule.coe_projectionOnto_apply,
          hzero ((fixedSub x).projectionOnto (movedSub x) hc v), Submodule.coe_zero, sub_zero]
      rw [hid, LinearMap.det_id]
    refine ⟨θ₀ ∘ₗ reflFix hu, fun a => hθ _, fun a => ?_, ?_⟩
    · rw [LinearMap.comp_apply, hθQ]
      exact quadReflection_isometry hQu a
    · rw [rmap_comp_reflFix, LinearMap.det_comp, hm1, LinearMap.det_baseChange,
        det_quadReflection hQu]
      simp
  obtain ⟨k, hk, hkx⟩ := exists_gspin_rmap hc d.nondeg hxss ψ θ₁ hmap hθ₁ hθ₁Q hdet
  -- `ψ' = ψ ∘ P(k)`
  have hkX : ((k : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra (d.QW.baseChange Kb)) *
      (bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra (d.QW.baseChange Kb)) *
      (((k : (CliffordAlgebra (d.QW.baseChange Kb))ˣ)⁻¹ : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra (d.QW.baseChange Kb)) =
      bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ) := by
    have e : ((k : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra (d.QW.baseChange Kb)) *
        (bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra (d.QW.baseChange Kb)) =
        (bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra (d.QW.baseChange Kb)) *
          ((k : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra (d.QW.baseChange Kb)) :=
      congrArg (fun z : GSpin (d.QW.baseChange Kb) => ((z : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra (d.QW.baseChange Kb)))
        hkx.eq
    rw [e, mul_assoc, Units.mul_inv, mul_one]
  have hmap' : CliffordAlgebra.map ((specPIso k).trans ψ).toIsometry
      (bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra _) =
      bcUnits τ.Q' (y : (CliffordAlgebra τ.Q')ˣ) := by
    rw [map_trans_apply, map_specPIso_apply, hkX, hmap]
  have hrat : ∀ a : fixedSub x, (specPIso k).trans ψ (1 ⊗ₜ (a : Fin d.m → F)) = 1 ⊗ₜ θ₁ a := by
    intro a
    change ψ (specP _ k (1 ⊗ₜ (a : Fin d.m → F))) = _
    rw [hk, rmap_tmul_of_mem hc ψ θ₁ a.2, ψ.apply_symm_apply]
  refine ⟨(specPIso k).trans ψ, hmap', fun σ => ?_, by
    rw [det_glOf_specPIso_trans, ← hψ, det_glOf_trans_specPIso_eq]⟩
  refine inv_mul_galGL_glOf_mem_torusBarFbar d x _ hmap' σ ?_ fun w hw =>
    galIso_trans_symm_eq_self_of_tmul _ (fun a => θ₁ a) hrat σ hw
  rw [glOf_trans, glOf_specPIso, det_inv_mul_galGL_mul_right σ _ _ (det_specMatFbar _ k)]
  exact hdetψ σ

end GGPData

end GSpinGGP
