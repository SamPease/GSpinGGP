/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.StableCocycleClass
import GSpinGGP.GGP.TorusCentral
import GSpinGGP.GGP.TwistIncl

/-!
# Every class over `α` comes from some `y` (surjectivity in Thesis Prop. 6.6.1(iii))

If the cocycle `a_σ = ψ⁻¹ ∘ σψ` of an isometry `ψ = P(g) ∘ φ` is `P(t_σ)` with `t_σ` in the torus of `x`
(commuting with `x` and trivial on `ker (P(x) − 1)`), then `Ad(g) ∘ C(φ)` is Galois-equivariant on the
centralizer of `x` (`TorusTransfer.ratAt_of_torus`), because the torus is central in the centralizer
(`Steinberg.commute_of_fixes_eigenspace_one`).  Own work, elementary.
-/

noncomputable section

namespace GSpinGGP

open CliffordAlgebra TwistDescent TorusTransfer
open scoped TensorProduct

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

namespace TorusTransfer

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [FiniteDimensional F V₁]
  [AddCommGroup V₂] [Module F V₂] {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}

/-- **The rationality clause from a torus-valued cocycle.** -/
theorem ratAt_of_torus (hQ₁ : IsNondeg Q₁) {x : GSpin Q₁}
    (hss : Module.End.IsSemisimple (specP _ (bcGSpin Q₁ x) : Kb ⊗[F] V₁ →ₗ[Kb] _))
    (hL : IsomCent.LieAbelian (bform (Q₁.baseChange Kb))
      (specP _ (bcGSpin Q₁ x) : Kb ⊗[F] V₁ →ₗ[Kb] _))
    (φ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) (g : GSpin (Q₂.baseChange Kb))
    (htor : ∀ σ : GalF F, ∃ t : GSpin (Q₁.baseChange Kb), Commute t (bcGSpin Q₁ x) ∧
      (∀ w ∈ Module.End.eigenspace (specP _ (bcGSpin Q₁ x) : Kb ⊗[F] V₁ →ₗ[Kb] _) 1,
        specP _ t w = w) ∧
      ∀ v, (galIso σ (φ.trans (specPIso g))).trans (φ.trans (specPIso g)).symm v = specP _ t v) :
    RatAt φ (g : (CliffordAlgebra (Q₂.baseChange Kb))ˣ) (x : (CliffordAlgebra Q₁)ˣ) := by
  intro σ z hz hzx
  obtain ⟨t, htx, htW, ht⟩ := htor σ
  obtain ⟨ψ, hψ⟩ : ∃ ψ, φ.trans (specPIso g) = ψ := ⟨_, rfl⟩
  rw [hψ] at ht
  set w := galCU Q₁ σ z
  have hw : w ∈ GSpin (Q₁.baseChange Kb) := galCU_mem_GSpin Q₁ σ hz
  have hwx : Commute w (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ)) := by
    have h1 := hzx.map (galCU Q₁ σ)
    have h2 : galCU Q₁ σ (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ)) = bcUnits Q₁ x :=
      Units.ext (galC_bcHom Q₁ σ (x : CliffordAlgebra Q₁))
    rwa [h2] at h1
  -- `t` commutes with `w`
  have hcw : Commute (⟨w, hw⟩ : GSpin (Q₁.baseChange Kb)) t :=
    Steinberg.commute_of_fixes_eigenspace_one (isNondeg_baseChange Q₁ hQ₁) hss hL htx htW
      (Subtype.ext hwx)
  have key : CliffordAlgebra.map (galIso σ ψ).toIsometry (w : CliffordAlgebra _) =
      CliffordAlgebra.map ψ.toIsometry (w : CliffordAlgebra _) := by
    have e : ∀ c, CliffordAlgebra.map (galIso σ ψ).toIsometry c =
        CliffordAlgebra.map ψ.toIsometry
          (CliffordAlgebra.map ((galIso σ ψ).trans ψ.symm).toIsometry c) := fun c => by
      rw [map_trans_apply (galIso σ ψ) ψ.symm, map_map_symm]
    rw [e, map_isometryEquiv_congr (e' := specPIso t) ht, map_specPIso_apply]
    congr 1
    have hc : ((t : (CliffordAlgebra (Q₁.baseChange Kb))ˣ) : CliffordAlgebra (Q₁.baseChange Kb)) *
        (w : CliffordAlgebra (Q₁.baseChange Kb)) = (w : CliffordAlgebra (Q₁.baseChange Kb)) *
          ((t : (CliffordAlgebra (Q₁.baseChange Kb))ˣ) : CliffordAlgebra (Q₁.baseChange Kb)) :=
      (congrArg (fun u : GSpin (Q₁.baseChange Kb) =>
        ((u : (CliffordAlgebra (Q₁.baseChange Kb))ˣ) : CliffordAlgebra (Q₁.baseChange Kb)))
          hcw.eq).symm
    rw [hc, mul_assoc, Units.mul_inv, mul_one]
  change galC Q₂ σ (psiA φ (g : (CliffordAlgebra _)ˣ) z) =
    psiA φ (g : (CliffordAlgebra _)ˣ) (galC Q₁ σ (z : CliffordAlgebra _))
  rw [psiA_eq_map, psiA_eq_map, galC_map, hψ]
  exact key

end TorusTransfer

namespace GGPData

variable (d : GGPData F)

/-- `Z_{F̄} ↪ V_{F̄}`. -/
abbrev inrF : (Kb ⊗[F] d.Z) →ₗ[Kb] (Kb ⊗[F] d.V) :=
  (LinearMap.inr F (Fin d.m → F) d.Z).baseChange Kb

theorem prodBaseChange_inlF (w : Kb ⊗[F] (Fin d.m → F)) :
    prodBaseChange d.QW d.QZ (d.inlF w) = (w, 0) := by
  induction w using TensorProduct.inductionOn with
  | tmul a v =>
    change TensorProduct.prodRight F Kb Kb _ _ (a ⊗ₜ (v, 0)) = _
    rw [TensorProduct.prodRight_tmul, TensorProduct.tmul_zero]
  | add u w hu hw => rw [map_add, map_add, hu, hw, Prod.mk_add_mk, add_zero]

theorem prodBaseChange_inrF (z : Kb ⊗[F] d.Z) :
    prodBaseChange d.QW d.QZ (d.inrF z) = (0, z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a v =>
    change TensorProduct.prodRight F Kb Kb _ _ (a ⊗ₜ (0, v)) = _
    rw [TensorProduct.prodRight_tmul, TensorProduct.tmul_zero]
  | add u w hu hw => rw [map_add, map_add, hu, hw, Prod.mk_add_mk, add_zero]

theorem inlF_add_inrF (v : Kb ⊗[F] d.V) :
    d.inlF ((prodBaseChange d.QW d.QZ v).1) + d.inrF ((prodBaseChange d.QW d.QZ v).2) = v := by
  apply (prodBaseChange d.QW d.QZ).toLinearEquiv.injective
  change prodBaseChange d.QW d.QZ (_ + _) = prodBaseChange d.QW d.QZ v
  rw [map_add, prodBaseChange_inlF, prodBaseChange_inrF, Prod.mk_add_mk, add_zero, zero_add]

/-- `W_{F̄} ↪ V_{F̄}` as an isometry. -/
def inlW : d.QW.baseChange Kb →qᵢ d.QV.baseChange Kb where
  toLinearMap := d.inlF
  map_app' w := by
    have h := (prodBaseChange d.QW d.QZ).map_app (d.inlF w)
    rw [prodBaseChange_inlF] at h
    change d.QV.baseChange Kb (d.inlF w) = _
    rw [← h]
    simp

theorem polar_inlF_inrF (w : Kb ⊗[F] (Fin d.m → F)) (z : Kb ⊗[F] d.Z) :
    QuadraticMap.polar (d.QV.baseChange Kb) (d.inlF w) (d.inrF z) = 0 := by
  have h : ∀ a b, QuadraticMap.polar (d.QV.baseChange Kb) a b = QuadraticMap.polar
      ((d.QW.baseChange Kb).prod (d.QZ.baseChange Kb)) (prodBaseChange d.QW d.QZ a)
        (prodBaseChange d.QW d.QZ b) := fun a b => by
    simp only [QuadraticMap.polar, ← map_add, QuadraticMap.IsometryEquiv.map_app]
  rw [h, prodBaseChange_inlF, prodBaseChange_inrF, QuadraticMap.polar_prod]
  simp

end GGPData

/-- The Galois action commutes with the base change of a rational map. -/
theorem galV_baseChange {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂]
    [Module F V₂] (f : V₁ →ₗ[F] V₂) (σ : GalF F) (w : Kb ⊗[F] V₁) :
    galV σ (f.baseChange Kb w) = f.baseChange Kb (galV σ w) := by
  induction w using TensorProduct.inductionOn with
  | tmul a v => rfl
  | add u w hu hw => rw [map_add, map_add, hu, hw, map_add, map_add]

namespace GGPData

variable {d : GGPData F}

theorem polar_prodBaseChange_symm {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂]
    [Module F V₂] (Q₁ : QuadraticForm F V₁) (Q₂ : QuadraticForm F V₂) (a b : _ × _) :
    QuadraticMap.polar (QuadraticForm.baseChange Kb (Q₁.prod Q₂)) ((prodBaseChange Q₁ Q₂).symm a)
      ((prodBaseChange Q₁ Q₂).symm b) =
      QuadraticMap.polar ((Q₁.baseChange Kb).prod (Q₂.baseChange Kb)) a b := by
  simp only [QuadraticMap.polar, ← map_add, QuadraticMap.IsometryEquiv.map_app]

theorem twistV_inlF (τ : InnerTwist d.QW) (w : Kb ⊗[F] (Fin d.m → F)) :
    d.twistV τ (d.inlF w) = inlBC d τ (τ.φ w) := by
  change (prodBaseChange τ.Q' d.QZ).symm ((τ.φ.prod (QuadraticMap.IsometryEquiv.refl _))
    (prodBaseChange d.QW d.QZ (d.inlF w))) = _
  rw [prodBaseChange_inlF]
  rfl

theorem twistV_inrF (τ : InnerTwist d.QW) (z : Kb ⊗[F] d.Z) :
    d.twistV τ (d.inrF z) = (prodBaseChange τ.Q' d.QZ).symm (0, z) := by
  change (prodBaseChange τ.Q' d.QZ).symm ((τ.φ.prod (QuadraticMap.IsometryEquiv.refl _))
    (prodBaseChange d.QW d.QZ (d.inrF z))) = _
  rw [prodBaseChange_inrF]
  congr 1
  exact Prod.ext (map_zero τ.φ) rfl

theorem galV_inlF (σ : GalF F) (w : Kb ⊗[F] (Fin d.m → F)) :
    galV σ (d.inlF w) = d.inlF (galV σ w) :=
  galV_baseChange _ σ w

theorem galV_inrF (σ : GalF F) (z : Kb ⊗[F] d.Z) :
    galV σ (d.inrF z) = d.inrF (galV σ z) :=
  galV_baseChange _ σ z

theorem galV_inlBC (τ : InnerTwist d.QW) (σ : GalF F) (u : Kb ⊗[F] (Fin d.m → F)) :
    galV σ (inlBC d τ u) = inlBC d τ (galV σ u) := by
  change galV σ ((prodBaseChange τ.Q' d.QZ).symm (u, 0)) = (prodBaseChange τ.Q' d.QZ).symm _
  rw [galV_prodBaseChange_symm, map_zero]
  rfl

/-- The witness on `V` induced by `g ∈ GSpin(W_α)(F̄)`. -/
abbrev gV (τ : InnerTwist d.QW) (g : GSpin (τ.Q'.baseChange Kb)) :
    GSpin ((d.twist τ).QV.baseChange Kb) :=
  GSpin.map (inlBC d τ) (isNondeg_baseChange _ τ.nondeg') g

theorem psiV_inlF (τ : InnerTwist d.QW) (g : GSpin (τ.Q'.baseChange Kb))
    (w : Kb ⊗[F] (Fin d.m → F)) :
    (d.twistV τ).trans (specPIso (gV τ g)) (d.inlF w) =
      inlBC d τ ((τ.φ.trans (specPIso g)) w) := by
  change specP _ (gV τ g) (d.twistV τ (d.inlF w)) = _
  rw [twistV_inlF, specP_map_apply]
  rfl

theorem psiV_inrF (τ : InnerTwist d.QW) (g : GSpin (τ.Q'.baseChange Kb)) (z : Kb ⊗[F] d.Z) :
    (d.twistV τ).trans (specPIso (gV τ g)) (d.inrF z) = (prodBaseChange τ.Q' d.QZ).symm (0, z) := by
  change specP _ (gV τ g) (d.twistV τ (d.inrF z)) = _
  rw [twistV_inrF]
  refine specP_map_apply_of_orth _ _ _ fun u => ?_
  change QuadraticMap.polar (QuadraticForm.baseChange Kb (τ.Q'.prod d.QZ))
    ((prodBaseChange τ.Q' d.QZ).symm (u, 0)) ((prodBaseChange τ.Q' d.QZ).symm (0, z)) = 0
  rw [polar_prodBaseChange_symm, QuadraticMap.polar_prod]
  simp

/-- **The cocycle on `V`** of `ψ_V = P(g_V) ∘ (φ_α ⊕ 1)` is `a_σ ⊕ 1`: if `a_σ = P(t)`, it is `P` of the
image of `t` in `GSpin(V)(F̄)`. -/
theorem galIso_psiV_trans_symm (τ : InnerTwist d.QW) (g : GSpin (τ.Q'.baseChange Kb))
    (σ : GalF F) (t : GSpin (d.QW.baseChange Kb))
    (ht : ∀ v, (galIso σ (τ.φ.trans (specPIso g))).trans (τ.φ.trans (specPIso g)).symm v =
      specP _ t v) (v : Kb ⊗[F] d.V) :
    (galIso σ ((d.twistV τ).trans (specPIso (gV τ g)))).trans
        ((d.twistV τ).trans (specPIso (gV τ g))).symm v =
      specP _ (GSpin.map d.inlW (isNondeg_baseChange _ d.nondeg) t) v := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ, τ.φ.trans (specPIso g) = ψ := ⟨_, rfl⟩
  obtain ⟨ψV, hψV⟩ : ∃ ψV, (d.twistV τ).trans (specPIso (gV τ g)) = ψV := ⟨_, rfl⟩
  rw [hψ] at ht
  have hl : ∀ w, ψV (d.inlF w) = inlBC d τ (ψ w) := fun w => by rw [← hψV, ← hψ]; exact psiV_inlF τ g w
  have hr : ∀ z, ψV (d.inrF z) = (prodBaseChange τ.Q' d.QZ).symm (0, z) := fun z => by
    rw [← hψV]; exact psiV_inrF τ g z
  have hls : ∀ u, ψV.symm (inlBC d τ u) = d.inlF (ψ.symm u) := fun u => by
    rw [ψV.symm_apply_eq, hl, ψ.apply_symm_apply]
  have hrs : ∀ z, ψV.symm ((prodBaseChange τ.Q' d.QZ).symm (0, z)) = d.inrF z := fun z => by
    rw [ψV.symm_apply_eq, hr]
  have hPl : ∀ w, specP _ (GSpin.map d.inlW (isNondeg_baseChange _ d.nondeg) t) (d.inlF w) =
      d.inlF (specP _ t w) := fun w => specP_map_apply d.inlW _ t w
  have hPr : ∀ z, specP _ (GSpin.map d.inlW (isNondeg_baseChange _ d.nondeg) t) (d.inrF z) =
      d.inrF z := fun z => specP_map_apply_of_orth _ _ _ fun w => polar_inlF_inrF d w z
  have hR : ∀ z : Kb ⊗[F] d.Z, ψV.symm (galV σ (ψV (galV σ⁻¹ (d.inrF z)))) = d.inrF z := by
    intro z
    rw [galV_inrF, hr, galV_prodBaseChange_symm, LinearMap.map_zero (galV σ), galV_galV_inv, hrs]
  have hL : ∀ w : Kb ⊗[F] (Fin d.m → F),
      ψV.symm (galV σ (ψV (galV σ⁻¹ (d.inlF w)))) = d.inlF (specP _ t w) := by
    intro w
    rw [galV_inlF, hl, galV_inlBC, hls, ← ht]
    rfl
  rw [hψV, ← d.inlF_add_inrF v, map_add, map_add, hPl, hPr]
  exact congrArg₂ (· + ·) (hL _) (hR _)

end GGPData

end GSpinGGP
