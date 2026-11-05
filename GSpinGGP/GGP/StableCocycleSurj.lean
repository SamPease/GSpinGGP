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


theorem specP_inlW_inlF (t : GSpin (d.QW.baseChange Kb)) (w : Kb ⊗[F] (Fin d.m → F)) :
    specP _ (GSpin.map d.inlW (isNondeg_baseChange _ d.nondeg) t) (d.inlF w) =
      d.inlF (specP _ t w) :=
  specP_map_apply d.inlW _ t w

theorem specP_inlW_inrF (t : GSpin (d.QW.baseChange Kb)) (z : Kb ⊗[F] d.Z) :
    specP _ (GSpin.map d.inlW (isNondeg_baseChange _ d.nondeg) t) (d.inrF z) = d.inrF z :=
  specP_map_apply_of_orth _ _ _ fun w => d.polar_inlF_inrF w z

end GGPData

omit [PAdicField F] in
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
  have hPl := specP_inlW_inlF (d := d) t
  have hPr := specP_inlW_inrF (d := d) t
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

namespace GGPData

variable {d : GGPData F}

theorem bcHom_map_inl (a : CliffordAlgebra d.QW) :
    bcHom d.QV (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ) a) =
      CliffordAlgebra.map d.inlW (bcHom d.QW a) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes, bcHom_algebraMap]
  | ι w =>
    rw [CliffordAlgebra.map_apply_ι, bcHom_ι, bcHom_ι, CliffordAlgebra.map_apply_ι]
    rfl
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The image in `GSpin(V)(F̄)` of an element of `T_x(F̄)` commutes with `x` and fixes `V'_x ⊗ F̄`. -/
theorem inlW_mem_torus {x : GSpin d.QW} {t : GSpin (d.QW.baseChange Kb)} (ht : t ∈ d.torusFbar x) :
    Commute (GSpin.map d.inlW (isNondeg_baseChange _ d.nondeg) t) (bcGSpin d.QV (d.incl x)) ∧
      ∀ w ∈ Module.End.eigenspace (specP _ (bcGSpin d.QV (d.incl x)) : Kb ⊗[F] d.V →ₗ[Kb] _) 1,
        specP _ (GSpin.map d.inlW (isNondeg_baseChange _ d.nondeg) t) w = w := by
  refine ⟨Subtype.ext (Units.ext ?_), fun v hv => ?_⟩
  · have hx : ((bcGSpin d.QV (d.incl x) : GSpin _) : (CliffordAlgebra (d.QV.baseChange Kb))ˣ) =
        (CliffordAlgebra.map d.inlW
          (bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra _) : CliffordAlgebra _) :=
      bcHom_map_inl _
    change CliffordAlgebra.map d.inlW _ * _ = _ * CliffordAlgebra.map d.inlW _
    rw [hx, ← map_mul, ← map_mul]
    exact congrArg _ (congrArg Units.val ht.1.eq)
  · rw [GGPData.eigenspace_bc_one] at hv
    refine eqOn_baseChange_of_tmul (g := LinearMap.id) (fun a ha => ?_) hv
    obtain ⟨w, z⟩ := a
    have hw : w ∈ fixedSub x := (d.mem_fixedSub_incl_iff x w z).1 ha
    have e : ((1 : Kb) ⊗ₜ[F] ((w, z) : d.V)) = d.inlF (1 ⊗ₜ w) + d.inrF (1 ⊗ₜ z) := by
      change _ = 1 ⊗ₜ (w, 0) + 1 ⊗ₜ (0, z)
      rw [← TensorProduct.tmul_add, Prod.mk_add_mk, add_zero, zero_add]
    change specP _ _ _ = _
    rw [e, map_add, specP_inlW_inlF, specP_inlW_inrF,
      ht.2 _ (Submodule.tmul_mem_baseChange_of_mem 1 hw)]
    rfl

end GGPData

omit [PAdicField F] in
theorem det_map_algebraMap {n : ℕ} (N : Matrix (Fin n) (Fin n) F) :
    (N.map (algebraMap F Kb)).det = algebraMap F Kb N.det :=
  (RingHom.map_det (algebraMap F Kb) N).symm

/-- A rational matrix of determinant `-1` preserving a nondegenerate form in dimension `m > 0` (the
matrix of a rational reflection), viewed in `GL_m(F̄)`. -/
theorem exists_galFixed_gram_det_neg {m : ℕ} {Q : QuadraticForm F (Fin m → F)} (hQ : IsNondeg Q)
    (hm : 0 < m) :
    ∃ X : GL (Fin m) Kb, (∀ σ : GalF F, galGL m σ X = X) ∧
      (X : Matrix (Fin m) (Fin m) Kb).transpose * Q.toMatrix'.map (algebraMap F Kb) * X =
        Q.toMatrix'.map (algebraMap F Kb) ∧ (X : Matrix (Fin m) (Fin m) Kb).det = -1 := by
  -- an anisotropic vector
  obtain ⟨u, hu⟩ : ∃ u, Q u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hb : ∀ v w, bform Q v w = 0 := fun v w => by
      have h2 := polar_eq_two_mul_bform Q v w
      rw [QuadraticMap.polar, hcon, hcon, hcon, sub_zero, sub_zero] at h2
      exact (mul_eq_zero.1 h2.symm).resolve_left two_ne_zero
    have h0 := hQ.1 (Pi.single ⟨0, hm⟩ 1) fun w => hb _ w
    simpa using congrFun h0 ⟨0, hm⟩
  set N := LinearMap.toMatrix' (quadReflection Q u)
  have hNdet : N.det = -1 := by rw [LinearMap.det_toMatrix', det_quadReflection hu]
  have hNg : N.transpose * Q.toMatrix' * N = Q.toMatrix' := by
    rw [← QuadraticForm.toMatrix'_comp]
    congr 1
    ext v
    exact quadReflection_isometry hu v
  have hdet : IsUnit (N.map (algebraMap F Kb)).det := by
    rw [det_map_algebraMap, hNdet]; exact (isUnit_one.neg).map _
  obtain ⟨X, hX⟩ : ∃ X : GL (Fin m) Kb, (X : Matrix (Fin m) (Fin m) Kb) = N.map (algebraMap F Kb) :=
    ⟨Matrix.nonsingInvUnit _ hdet, rfl⟩
  refine ⟨X, fun σ => Units.ext ?_, ?_, ?_⟩
  · rw [coe_galGL, hX, map_algebraMap_fixed]
  · rw [hX, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hNg]
  · rw [hX, det_map_algebraMap, hNdet, map_neg, map_one]

namespace GGPData

open WitnessChange

variable {d : GGPData F}


/-- **`y` lies in `Γ(G_α, H_α)`**: if `Ad(g) ∘ C(φ_α)` carries `x ∈ Γ(G,H)` to `y` and satisfies the
rationality clause, then `y` is semisimple and the torus isomorphism `T_x(F) ≃ T_y(F)`
(`TorusTransfer.transportEquiv`, a homeomorphism fixing the scalars) carries commutativity of `T_x(F)`
and compactness of `T_x(F)/A(F)` over. -/
theorem isGammaElt_of_ratAt (τ : InnerTwist d.QW) {x : GSpin d.QW} (hx : d.IsGammaElt x)
    {y : GSpin (d.twist τ).QW} {g : (CliffordAlgebra (τ.Q'.baseChange Kb))ˣ}
    (hg : g ∈ GSpin (τ.Q'.baseChange Kb)) (hrat : RatAt τ.φ g (x : (CliffordAlgebra d.QW)ˣ))
    (hconj : psiU τ.φ g (bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ)) =
      bcUnits τ.Q' (y : (CliffordAlgebra τ.Q')ˣ)) :
    (d.twist τ).IsGammaElt y := by
  let e : ↥(d.torusOf x) ≃* ↥((d.twist τ).torusOf y) := transportEquiv hg hrat hconj
  have he : ∀ t : ↥(d.torusOf x), bcUnits τ.Q'
      (((e t : ↥((d.twist τ).torusOf y)) : GSpin τ.Q') : (CliffordAlgebra τ.Q')ˣ) =
        psiU τ.φ g (bcUnits d.QW ((t : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ)) :=
    bcUnits_transportEquiv hg hrat hconj
  have c1 : Continuous e := continuous_of_bcUnits_eq e.toMonoidHom he
  refine ⟨?_, fun a ha b hb => ?_, ?_⟩
  · exact isSS_of_psiA τ.φ g (t := ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
      (congrArg Units.val hconj).symm hx.1
  · have hc := hx.2.1 _ (e.symm ⟨a, ha⟩).2 _ (e.symm ⟨b, hb⟩).2
    have hc' : Commute (e.symm ⟨a, ha⟩) (e.symm ⟨b, hb⟩) := Subtype.ext hc
    have := (hc'.map e.toMonoidHom)
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at this
    exact congrArg Subtype.val this.eq
  · -- the induced map of quotients is a continuous surjection
    have hsc : ∀ c : Fˣ, ((e ⟨scalarGSpin d.QW c, d.scalar_mem_torusOf x c⟩ :
        ↥((d.twist τ).torusOf y)) : GSpin τ.Q') = scalarGSpin τ.Q' c := fun c => by
      apply bcUnits_GSpin_injective
      change bcUnits _ _ = bcUnits _ _
      rw [he]
      exact psiU_bcUnits_scalar _ _ c
    have hle : d.scalarsIn (d.torusOf x) ≤ ((d.twist τ).scalarsIn ((d.twist τ).torusOf y)).comap
        e.toMonoidHom := by
      rintro ⟨t, ht⟩ ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have e1 : (⟨t, ht⟩ : ↥(d.torusOf x)) = ⟨scalarGSpin d.QW c, d.scalar_mem_torusOf x c⟩ :=
        Subtype.ext hc.symm
      change scalarGSpin τ.Q' c = ((e ⟨t, ht⟩ : ↥((d.twist τ).torusOf y)) : GSpin τ.Q')
      rw [e1, hsc]
    have : ((d.twist τ).scalarsIn ((d.twist τ).torusOf y)).Normal :=
      GGPData.scalarsIn_normal _ _
    let f := QuotientGroup.map (d.scalarsIn (d.torusOf x))
      ((d.twist τ).scalarsIn ((d.twist τ).torusOf y)) e.toMonoidHom hle
    have hf : Continuous f := by
      refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_
      have h : ⇑f ∘ QuotientGroup.mk = QuotientGroup.mk ∘ ⇑e := rfl
      rw [h]
      exact QuotientGroup.continuous_mk.comp c1
    have hsurj : Function.Surjective f := by
      intro q
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨QuotientGroup.mk (e.symm s), by simp [f]⟩
    have := hx.2.2
    refine ⟨?_⟩
    rw [← Set.range_eq_univ.2 hsurj]
    exact isCompact_range hf

/-- The rationality clause on `W` and on `V` for `ψ = P(g) ∘ φ_α` with cocycle in `S_x(F̄)`. -/
theorem ratAt_of_torusFbar (τ : InnerTwist d.QW) {x : GSpin d.QW} (hx : d.IsGammaElt x)
    (g : GSpin (τ.Q'.baseChange Kb))
    (htor : ∀ σ : GalF F, ∃ t : GSpin (d.QW.baseChange Kb), t ∈ d.torusFbar x ∧
      ∀ v, (galIso σ (τ.φ.trans (specPIso g))).trans (τ.φ.trans (specPIso g)).symm v =
        specP _ t v) :
    RatAt τ.φ (g : (CliffordAlgebra (τ.Q'.baseChange Kb))ˣ) (x : (CliffordAlgebra d.QW)ˣ) ∧
      RatAt (d.twistV τ) ((gV τ g : GSpin _) : (CliffordAlgebra ((d.twist τ).QV.baseChange Kb))ˣ)
        ((d.incl x : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) := by
  have hss : Module.End.IsSemisimple
      (specP _ (bcGSpin d.QW x) : Kb ⊗[F] (Fin d.m → F) →ₗ[Kb] _) := by
    rw [specP_bcGSpin]; exact isSemisimple_specP_baseChange x hx.1
  have hL : IsomCent.LieAbelian (bform (d.QW.baseChange Kb))
      (specP _ (bcGSpin d.QW x) : Kb ⊗[F] (Fin d.m → F) →ₗ[Kb] _) := by
    rw [specP_bcGSpin]; exact lieAbelian_specP_baseChange x hx
  have hssV : Module.End.IsSemisimple
      (specP _ (bcGSpin d.QV (d.incl x)) : Kb ⊗[F] d.V →ₗ[Kb] _) := by
    rw [specP_bcGSpin]
    exact IsomCent.isSemisimple_baseChange_algebraicClosure
      (isSemisimple_specP_of_isSS d.QV (d.incl x) (d.isSS_incl hx.1))
  have hLV : IsomCent.LieAbelian (bform (d.QV.baseChange Kb))
      (specP _ (bcGSpin d.QV (d.incl x)) : Kb ⊗[F] d.V →ₗ[Kb] _) := by
    rw [specP_bcGSpin]
    refine d.lieAbelian_incl x ?_ (lieAbelian_specP_baseChange x hx)
    rw [← specP_bcGSpin]; exact hssV
  refine ⟨ratAt_of_torus d.nondeg hss hL τ.φ g fun σ => ?_,
    ratAt_of_torus d.nondeg_QV hssV hLV (d.twistV τ) (gV τ g) fun σ => ?_⟩
  · obtain ⟨t, ht, htv⟩ := htor σ
    exact ⟨t, Subtype.ext ht.1, fun w hw => ht.2 w (by rwa [GGPData.eigenspace_bc_one] at hw), htv⟩
  · obtain ⟨t, ht, htv⟩ := htor σ
    obtain ⟨hcV, hfV⟩ := inlW_mem_torus ht
    exact ⟨_, hcV, hfV, galIso_psiV_trans_symm τ g σ t htv⟩

/-- **Surjectivity** (Thesis Prop. 6.6.1(iii)): every cocycle `a` in `S_x` twisting `W` into `W_α`
is the cocycle of some `y` strongly stably conjugate to `x`.  Normalize the `F̄`-isometry `φ` of the
twist so that `det φ = det φ_α` (a rational reflection of `W_α`), write `φ = P(g) ∘ φ_α`; since
`φ⁻¹ ∘ σφ = a_σ ∈ S_x(F̄)` is central in the centralizer of `x` (on `W` and, through `W ⊆ V`, on `V`),
`Ad(g) ∘ C(φ_α)` and `Ad(g_V) ∘ C(φ_α ⊕ 1)` satisfy the rationality clause, and `y` is the rational
element `g C(φ_α)(x) g⁻¹` (`TorusTransfer.exists_transport`). -/
theorem exists_stronglyStablyConj_of_isTwistBy (τ : InnerTwist d.QW) {x : GSpin d.QW}
    (hx : d.IsGammaElt x) (a : GalCocycle (d.torusBarFbar x)) (ha : IsTwistBy d.QW τ.Q' a.toFun) :
    ∃ y : GSpin (d.twist τ).QW, d.StronglyStablyConjW τ x y ∧
      ∃ ψ, ∃ h : d.IsStableIso τ x y ψ, ∀ σ, h.cocycle.toFun σ = a.toFun σ := by
  obtain ⟨φ, hφ⟩ := (isTwistBy_iff _ _ _).1 ha
  -- normalize `det φ`
  obtain ⟨φ₁, hdet₁, hφ₁⟩ : ∃ φ₁ : (d.QW.baseChange Kb).IsometryEquiv (τ.Q'.baseChange Kb),
      ((glOf φ₁ : GL (Fin d.m) Kb) : Matrix (Fin d.m) (Fin d.m) Kb).det =
        ((glOf τ.φ : GL (Fin d.m) Kb) : Matrix (Fin d.m) (Fin d.m) Kb).det ∧
      ∀ σ, a.toFun σ = (glOf φ₁)⁻¹ * galGL d.m σ (glOf φ₁) := by
    have hsq : ((glOf φ : GL (Fin d.m) Kb) : Matrix (Fin d.m) (Fin d.m) Kb).det *
        ((glOf φ : GL (Fin d.m) Kb) : Matrix (Fin d.m) (Fin d.m) Kb).det =
        ((glOf τ.φ : GL (Fin d.m) Kb) : Matrix (Fin d.m) (Fin d.m) Kb).det *
        ((glOf τ.φ : GL (Fin d.m) Kb) : Matrix (Fin d.m) (Fin d.m) Kb).det := by
      have h1 := congrArg Matrix.det (gram_glOf φ)
      have h2 := congrArg Matrix.det (gram_glOf τ.φ)
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1 h2
      have hG : (τ.Q'.toMatrix'.map (algebraMap F Kb)).det ≠ 0 := by
        rw [det_map_algebraMap]
        exact (map_ne_zero _).2 ((InnerTwistAux.isNondeg_iff_discr'_ne_zero τ.Q').1 τ.nondeg')
      have := h1.trans h2.symm
      exact mul_right_cancel₀ hG (by linear_combination this)
    by_cases h : ((glOf φ : GL (Fin d.m) Kb) : Matrix (Fin d.m) (Fin d.m) Kb).det =
        ((glOf τ.φ : GL (Fin d.m) Kb) : Matrix (Fin d.m) (Fin d.m) Kb).det
    · exact ⟨φ, h, hφ⟩
    have hneg : ((glOf φ : GL (Fin d.m) Kb) : Matrix (Fin d.m) (Fin d.m) Kb).det =
        -((glOf τ.φ : GL (Fin d.m) Kb) : Matrix (Fin d.m) (Fin d.m) Kb).det :=
      (mul_self_eq_mul_self_iff.1 hsq).resolve_left h
    have hm : 0 < d.m := by
      by_contra h0
      have hm0 : d.m = 0 := by omega
      apply h
      have e : ∀ M : Matrix (Fin d.m) (Fin d.m) Kb, M.det = 1 := fun M => by
        have : IsEmpty (Fin d.m) := by rw [hm0]; infer_instance
        exact Matrix.det_isEmpty
      rw [e, e]
    obtain ⟨X, hXσ, hXg, hXdet⟩ := exists_galFixed_gram_det_neg τ.nondeg' hm
    refine ⟨φ.trans (isoOfGL τ.Q' τ.Q' X hXg), ?_, fun σ => ?_⟩
    · rw [glOf_trans, glOf_isoOfGL, Units.val_mul, Matrix.det_mul, hXdet, hneg]; ring
    · rw [glOf_trans, glOf_isoOfGL, hφ σ, _root_.mul_inv_rev, map_mul, hXσ]; group
  -- `φ₁ = P(g) ∘ φ_α`
  obtain ⟨χ, hχdef⟩ : ∃ χ, τ.φ.symm.trans φ₁ = χ := ⟨_, rfl⟩
  have hdetχ : LinearMap.det (χ.toLinearEquiv : Kb ⊗[F] (Fin d.m → F) →ₗ[Kb] _) = 1 := by
    have h1 : ((((glOf τ.φ)⁻¹ : GL (Fin d.m) Kb)) : Matrix (Fin d.m) (Fin d.m) Kb).det *
        ((glOf τ.φ : GL (Fin d.m) Kb) : Matrix (Fin d.m) (Fin d.m) Kb).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    rw [← LinearMap.det_toMatrix (bcBasis F d.m), ← coe_glOf, ← hχdef, glOf_trans, glOf_symm,
      Units.val_mul, Matrix.det_mul, hdet₁, mul_comm, h1]
  obtain ⟨g, hg⟩ := gspin_specP_surjective_SO _ (isNondeg_baseChange τ.Q' τ.nondeg')
    χ.toLinearEquiv χ.map_app hdetχ
  obtain ⟨ψ, hψdef⟩ : ∃ ψ, τ.φ.trans (specPIso g) = ψ := ⟨_, rfl⟩
  have hψφ : ∀ w, ψ w = φ₁ w := fun w => by
    rw [← hψdef]
    change specP _ g (τ.φ w) = _
    rw [hg]
    change χ (τ.φ w) = _
    rw [← hχdef]
    exact congrArg φ₁ (τ.φ.symm_apply_apply w)
  have hcoc : ∀ σ, (glOf ψ)⁻¹ * galGL d.m σ (glOf ψ) = a.toFun σ := fun σ => by
    rw [glOf_congr hψφ, hφ₁ σ]
  -- the cocycle is torus-valued
  have htor : ∀ σ : GalF F, ∃ t : GSpin (d.QW.baseChange Kb), t ∈ d.torusFbar x ∧
      ∀ v, (galIso σ (τ.φ.trans (specPIso g))).trans (τ.φ.trans (specPIso g)).symm v =
        specP _ t v := fun σ => by
    obtain ⟨t, ht, hta⟩ := a.mem' σ
    refine ⟨t, ht, apply_eq_of_glOf_eq (e' := specPIso t) ?_⟩
    rw [glOf_trans, glOf_symm, glOf_galIso, hψdef, hcoc, glOf_specPIso, hta]
  obtain ⟨hrat, hratV⟩ := ratAt_of_torusFbar τ hx g htor
  -- the rational `y`
  obtain ⟨y, hy⟩ := exists_transport g.2 hrat x (Commute.refl _)
  refine ⟨y, ⟨⟨g, g.2, hy.symm, hrat⟩, ⟨gV τ g, (gV τ g).2, conj_gV τ g.2 x y hy, hratV⟩⟩,
    ψ, ⟨?_, fun σ => (hcoc σ) ▸ a.mem' σ, ?_⟩, fun σ => hcoc σ⟩
  · rw [← hψdef, ← psiA_eq_map]
    exact (congrArg Units.val hy).symm
  · rw [← hψdef]; exact det_glOf_trans_specPIso_eq _ _

/-- **Surjectivity of `y ↦ [a]`** (Thesis Prop. 6.6.1(iii)): every class `β ∈ H¹(F, S_x)` over `α` is
the class of some `y ∈ Γ(G_α, H_α)` strongly stably conjugate to `x`. -/
theorem exists_of_twistIdx (IF : InnerFormSystem d) {α : IF.Idx} {x : GSpin d.QW}
    (hx : d.IsGammaElt x) {β : H1 (d.torusBarFbar x)} (hβ : TwistIdx IF x β α) :
    ∃ y : GSpin (IF.data α).QW, (IF.data α).IsGammaElt y ∧ d.StronglyStablyConjW (IF.twist α) x y ∧
      ∃ ψ, ∃ h : d.IsStableIso (IF.twist α) x y ψ, H1.mk h.cocycle = β := by
  obtain ⟨a, ha, htw⟩ := hβ
  obtain ⟨y, hst, ψ, h, hco⟩ := exists_stronglyStablyConj_of_isTwistBy (IF.twist α) hx a htw
  obtain ⟨g, hg, hconj, hrat⟩ := hst.1
  refine ⟨y, isGammaElt_of_ratAt (IF.twist α) hx hg hrat hconj, hst, ψ, h, ?_⟩
  rw [← ha]
  exact H1.mk_eq_mk.2 ⟨1, (d.torusBarFbar x).one_mem, fun σ => by
    rw [← hco σ, inv_one, one_mul, map_one, mul_one]⟩

end GGPData

end GSpinGGP
