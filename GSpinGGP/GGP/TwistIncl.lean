/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TorusTransport
import GSpinGGP.GGP.Descent

/-!
# `W_{α,F̄} ⊆ V_{α,F̄}` and the transport on `V`

The inclusion `W_{α,F̄} ↪ V_{α,F̄}` (`inlBC`) intertwines `C(φ_α)` and `C(φ_α ⊕ 1)`; conjugating by the
image of `g` transports stable conjugacy from `W` to `V` (`stablyConjG_diag_of_psiU`, `conj_gV`).
-/

noncomputable section

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

variable {d : GGPData F}

section TwistIncl

open CliffordAlgebra
open scoped TensorProduct

/-- `W_{α,F̄} ↪ V_{α,F̄}`. -/
def inlBC (d : GGPData F) (τ : InnerTwist d.QW) :
    (τ.Q'.baseChange (AlgebraicClosure F)) →qᵢ ((d.twist τ).QV.baseChange (AlgebraicClosure F)) :=
  (prodBaseChange τ.Q' d.QZ).symm.toIsometry.comp
    (QuadraticMap.Isometry.inl (τ.Q'.baseChange (AlgebraicClosure F)) (d.QZ.baseChange (AlgebraicClosure F)))

theorem map_twistV_bcHom_incl (τ : InnerTwist d.QW) (a : CliffordAlgebra d.QW) :
    CliffordAlgebra.map (d.twistV τ).toIsometry
        (bcHom d.QV (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ) a)) =
      CliffordAlgebra.map (inlBC d τ) (CliffordAlgebra.map τ.φ.toIsometry (bcHom d.QW a)) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes, bcHom_algebraMap]
  | ι w =>
    rw [map_apply_ι, bcHom_ι, bcHom_ι, map_apply_ι, map_apply_ι, map_apply_ι]
    congr 1
    simp only [GGPData.twistV, inlBC, prodBaseChange]
    show (prodBaseChange τ.Q' d.QZ).symm ((τ.φ.prod (QuadraticMap.IsometryEquiv.refl _))
      (TensorProduct.prodRight F (AlgebraicClosure F) (AlgebraicClosure F) _ _ (1 ⊗ₜ (w, 0)))) = _
    rw [TensorProduct.prodRight_tmul, TensorProduct.tmul_zero]
    have e : (τ.φ.prod (QuadraticMap.IsometryEquiv.refl (d.QZ.baseChange (AlgebraicClosure F))))
        ((1 : AlgebraicClosure F) ⊗ₜ[F] w, 0) = (τ.φ (1 ⊗ₜ w), 0) := Prod.ext rfl rfl
    rw [e]
    rfl
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem bcHom_incl_twist (τ : InnerTwist d.QW) (a : CliffordAlgebra τ.Q') :
    bcHom (d.twist τ).QV (CliffordAlgebra.map (QuadraticMap.Isometry.inl τ.Q' d.QZ) a) =
      CliffordAlgebra.map (inlBC d τ) (bcHom τ.Q' a) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes, bcHom_algebraMap]
  | ι w =>
    rw [map_apply_ι, bcHom_ι, bcHom_ι, map_apply_ι]
    simp only [inlBC, QuadraticMap.Isometry.comp_apply, QuadraticMap.Isometry.inl_apply]
    have e : ((1 : AlgebraicClosure F) ⊗ₜ[F] w, (0 : AlgebraicClosure F ⊗[F] d.Z)) =
        prodBaseChange τ.Q' d.QZ (1 ⊗ₜ (w, 0)) := by
      show _ = TensorProduct.prodRight F (AlgebraicClosure F) (AlgebraicClosure F) _ _ _
      rw [TensorProduct.prodRight_tmul, TensorProduct.tmul_zero]
    rw [e]
    congr 1
    exact ((prodBaseChange τ.Q' d.QZ).symm_apply_apply _).symm
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **Stable conjugacy in `G` from a transport on `W`**: if `ē = Ad(g) C(φ_α)(t̄)` with
`g ∈ GSpin(W_α)(F̄)`, then `diag t` and `diag e` are stably conjugate in `G` through `ψ_α`, the
`V`-component conjugating by the image of `g` under `W_{α,F̄} ⊆ V_{α,F̄}`. -/
theorem stablyConjG_diag_of_psiU (τ : InnerTwist d.QW)
    {g : (CliffordAlgebra (τ.Q'.baseChange (AlgebraicClosure F)))ˣ}
    (hg : g ∈ GSpin (τ.Q'.baseChange (AlgebraicClosure F))) (t : GSpin d.QW)
    (s : GSpin (d.twist τ).QW)
    (hs : bcUnits τ.Q' (s : (CliffordAlgebra τ.Q')ˣ) =
      TorusTransfer.psiU τ.φ g (bcUnits d.QW (t : (CliffordAlgebra d.QW)ˣ))) :
    d.StablyConjG τ (d.diag t) ((d.twist τ).diag s) := by
  refine ⟨⟨g, hg, hs.symm⟩, ?_⟩
  let gV : GSpin ((d.twist τ).QV.baseChange (AlgebraicClosure F)) :=
    GSpin.map (inlBC d τ) (isNondeg_baseChange _ τ.nondeg') ⟨g, hg⟩
  refine ⟨gV, gV.2, Units.ext ?_⟩
  have hs' := congrArg Units.val hs
  rw [TorusTransfer.coe_psiU] at hs'
  rw [Units.val_mul, Units.val_mul, GSpin.coe_map_inv]
  show CliffordAlgebra.map (inlBC d τ) (g : CliffordAlgebra _) *
      CliffordAlgebra.map (d.twistV τ).toIsometry
        (bcHom d.QV (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
          ((t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))) *
      CliffordAlgebra.map (inlBC d τ) ((g⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) =
    bcHom (d.twist τ).QV (CliffordAlgebra.map (QuadraticMap.Isometry.inl τ.Q' d.QZ)
      ((s : (CliffordAlgebra τ.Q')ˣ) : CliffordAlgebra τ.Q'))
  rw [map_twistV_bcHom_incl, bcHom_incl_twist, ← map_mul, ← map_mul]
  congr 1
  exact hs'.symm


/-- The `V`-component of the transport: conjugation by the image `g_V` of `g` under
`W_{α,F̄} ⊆ V_{α,F̄}` sends `C(φ_α ⊕ 1)(incl t̄)` to `incl s̄` when `s̄ = Ad(g) C(φ_α)(t̄)`. -/
theorem conj_gV (τ : InnerTwist d.QW)
    {g : (CliffordAlgebra (τ.Q'.baseChange (AlgebraicClosure F)))ˣ}
    (hg : g ∈ GSpin (τ.Q'.baseChange (AlgebraicClosure F))) (t : GSpin d.QW)
    (s : GSpin (d.twist τ).QW)
    (hs : bcUnits τ.Q' (s : (CliffordAlgebra τ.Q')ˣ) =
      TorusTransfer.psiU τ.φ g (bcUnits d.QW (t : (CliffordAlgebra d.QW)ˣ))) :
    ((GSpin.map (inlBC d τ) (isNondeg_baseChange _ τ.nondeg') ⟨g, hg⟩ : GSpin _) :
        (CliffordAlgebra _)ˣ) *
      cliffUnits (d.twistV τ) (bcUnits d.QV ((d.incl t : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ)) *
      ((GSpin.map (inlBC d τ) (isNondeg_baseChange _ τ.nondeg') ⟨g, hg⟩ : GSpin _) :
        (CliffordAlgebra _)ˣ)⁻¹ =
      bcUnits (d.twist τ).QV (((d.twist τ).incl s : GSpin _) : (CliffordAlgebra _)ˣ) := by
  apply Units.ext
  have hs' := congrArg Units.val hs
  rw [TorusTransfer.coe_psiU] at hs'
  rw [Units.val_mul, Units.val_mul, GSpin.coe_map_inv]
  show CliffordAlgebra.map (inlBC d τ) (g : CliffordAlgebra _) *
      CliffordAlgebra.map (d.twistV τ).toIsometry
        (bcHom d.QV (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
          ((t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))) *
      CliffordAlgebra.map (inlBC d τ) ((g⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) =
    bcHom (d.twist τ).QV (CliffordAlgebra.map (QuadraticMap.Isometry.inl τ.Q' d.QZ)
      ((s : (CliffordAlgebra τ.Q')ˣ) : CliffordAlgebra τ.Q'))
  rw [map_twistV_bcHom_incl, bcHom_incl_twist, ← map_mul, ← map_mul]
  congr 1
  exact hs'.symm

end TwistIncl

end GSpinGGP
