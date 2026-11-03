/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.GaloisTorus
import GSpinGGP.GGP.TwistDescent
import GSpinGGP.GGP.TorusTransport

/-!
# The cocycle of a strongly stably conjugate element

For an `F̄`-isometry `ψ : W_{F̄} ≃ W'_{F̄}`, its Galois conjugate `σψ = σ ∘ ψ ∘ σ⁻¹` (`galIso`) is again an
isometry, with matrix `σ(Ψ)` (`glOf_galIso`), and `C(ψ)` intertwines the Galois actions on the Clifford
algebras up to replacing `ψ` by `σψ` (`galC_map`).  Own work, elementary.
-/

noncomputable section

namespace GSpinGGP

open CliffordAlgebra TwistDescent
open scoped TensorProduct

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

section GalIso

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]

/-- `C(ψ)` intertwines the Galois actions when `ψ'` is the Galois conjugate of `ψ`. -/
theorem galC_map_of_galV {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂} (σ : GalF F)
    (ψ ψ' : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb))
    (h : ∀ w, galV σ (ψ w) = ψ' (galV σ w)) (a : CliffordAlgebra (Q₁.baseChange Kb)) :
    galC Q₂ σ (CliffordAlgebra.map ψ.toIsometry a) =
      CliffordAlgebra.map ψ'.toIsometry (galC Q₁ σ a) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes, galC_algebraMap]
  | ι x => rw [map_apply_ι, galC_ι, galC_ι, map_apply_ι]; exact congrArg _ (h x)
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- `q_{F̄}(σ w) = σ(q_{F̄}(w))`. -/
theorem baseChange_galV (Q : QuadraticForm F V₁) (σ : GalF F) (w : Kb ⊗[F] V₁) :
    Q.baseChange Kb (galV σ w) = σ (Q.baseChange Kb w) := by
  apply (algebraMap Kb (CliffordAlgebra (Q.baseChange Kb))).injective
  rw [← ι_sq_scalar, ← galC_algebraMap Q σ, ← ι_sq_scalar, map_mul, galC_ι]

/-- The Galois conjugate `σψ = σ ∘ ψ ∘ σ⁻¹` of an `F̄`-isometry, as an `F̄`-isometry. -/
def galIso {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂} (σ : GalF F)
    (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) :
    (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb) where
  toFun w := galV σ (ψ (galV σ⁻¹ w))
  invFun w := galV σ (ψ.symm (galV σ⁻¹ w))
  left_inv w := by simp only [galV_inv_galV, QuadraticMap.IsometryEquiv.symm_apply_apply,
    galV_galV_inv]
  right_inv w := by simp only [galV_inv_galV, QuadraticMap.IsometryEquiv.apply_symm_apply,
    galV_galV_inv]
  map_add' w w' := by simp only [map_add]
  map_smul' c w := by
    rw [galV_smul, map_smul, galV_smul, RingHom.id_apply]
    congr 1
    exact AlgEquiv.apply_symm_apply σ c
  map_app' w := by
    change Q₂.baseChange Kb (galV σ (ψ (galV σ⁻¹ w))) = _
    rw [baseChange_galV, QuadraticMap.IsometryEquiv.map_app, ← baseChange_galV, galV_galV_inv]

theorem galIso_apply {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂} (σ : GalF F)
    (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) (w : Kb ⊗[F] V₁) :
    galIso σ ψ w = galV σ (ψ (galV σ⁻¹ w)) := rfl

theorem galIso_galV {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂} (σ : GalF F)
    (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) (w : Kb ⊗[F] V₁) :
    galIso σ ψ (galV σ w) = galV σ (ψ w) := by
  rw [galIso_apply, galV_inv_galV]

/-- `σ(C(ψ) a) = C(σψ)(σ a)`. -/
theorem galC_map {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂} (σ : GalF F)
    (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb))
    (a : CliffordAlgebra (Q₁.baseChange Kb)) :
    galC Q₂ σ (CliffordAlgebra.map ψ.toIsometry a) =
      CliffordAlgebra.map (galIso σ ψ).toIsometry (galC Q₁ σ a) :=
  galC_map_of_galV σ ψ _ (fun w => (galIso_galV σ ψ w).symm) a

/-- The matrix of `σψ` is `σ` applied to the matrix of `ψ`. -/
theorem glOf_galIso {m : ℕ} {Q₁ Q₂ : QuadraticForm F (Fin m → F)} (σ : GalF F)
    (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) :
    glOf (galIso σ ψ) = galGL m σ (glOf ψ) :=
  Units.ext (toMatrix_of_galV_comm σ _ _ (fun w => galIso_galV σ ψ w))

end GalIso

section Strong

open TorusTransfer

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
  {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}

/-- `Ad(g) ∘ C(φ) = C(P(g) ∘ φ)`. -/
theorem psiA_eq_map (φ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb))
    (g : GSpin (Q₂.baseChange Kb)) (a : CliffordAlgebra (Q₁.baseChange Kb)) :
    psiA φ (g : (CliffordAlgebra _)ˣ) a = CliffordAlgebra.map (φ.trans (specPIso g)).toIsometry a := by
  rw [psiA, ← map_specPIso_apply]
  show _ = CliffordAlgebra.map ((specPIso g).toIsometry.comp φ.toIsometry) a
  rw [← CliffordAlgebra.map_comp_map]
  rfl

/-- **The strong condition as a fixed-point condition**: if `Ad(g) ∘ C(φ)` is defined over `F` on
the centralizer of `x`, then with `ψ = P(g) ∘ φ` the isometry `a_σ = ψ⁻¹ ∘ σψ` acts trivially (through
`C(a_σ)`) on every element of `GSpin(Q₁)(F̄)` commuting with `x`. -/
theorem map_galIso_trans_symm_of_ratAt (φ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb))
    (g : GSpin (Q₂.baseChange Kb)) {x : (CliffordAlgebra Q₁)ˣ}
    (hrat : RatAt φ (g : (CliffordAlgebra _)ˣ) x) (σ : GalF F)
    {w : (CliffordAlgebra (Q₁.baseChange Kb))ˣ} (hw : w ∈ GSpin (Q₁.baseChange Kb))
    (hwx : Commute w (bcUnits Q₁ x)) :
    CliffordAlgebra.map ((galIso σ (φ.trans (specPIso g))).trans
      (φ.trans (specPIso g)).symm).toIsometry (w : CliffordAlgebra _) = w := by
  set ψ := φ.trans (specPIso g)
  set z := galCU Q₁ σ⁻¹ w
  have hz : z ∈ GSpin (Q₁.baseChange Kb) := galCU_mem_GSpin Q₁ σ⁻¹ hw
  have hzx : Commute z (bcUnits Q₁ x) := by
    have h1 := hwx.map (galCU Q₁ σ⁻¹)
    have h2 : galCU Q₁ σ⁻¹ (bcUnits Q₁ x) = bcUnits Q₁ x :=
      Units.ext (galC_bcHom Q₁ σ⁻¹ (x : CliffordAlgebra Q₁))
    rwa [h2] at h1
  have hσz : galC Q₁ σ (z : CliffordAlgebra _) = w := by
    rw [coe_galCU, galC_galC, mul_inv_cancel, galC_one]
  have key : galC Q₂ σ (psiA φ (g : (CliffordAlgebra _)ˣ) z) =
      psiA φ (g : (CliffordAlgebra _)ˣ) (galC Q₁ σ (z : CliffordAlgebra _)) := hrat σ z hz hzx
  rw [psiA_eq_map, psiA_eq_map, galC_map, hσz] at key
  calc CliffordAlgebra.map ((galIso σ ψ).trans ψ.symm).toIsometry (w : CliffordAlgebra _)
      = CliffordAlgebra.map ψ.symm.toIsometry
          (CliffordAlgebra.map (galIso σ ψ).toIsometry (w : CliffordAlgebra _)) := by
        rw [← AlgHom.comp_apply, CliffordAlgebra.map_comp_map]; rfl
    _ = w := by rw [key, map_symm_map]

end Strong

end GSpinGGP
