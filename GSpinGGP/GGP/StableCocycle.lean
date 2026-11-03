/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.GaloisTorus
import GSpinGGP.GGP.TwistDescent

/-!
# The cocycle of a strongly stably conjugate element

For an `F̄`-isometry `ψ : W_{F̄} ≃ W'_{F̄}`, its Galois conjugate `σψ = σ ∘ ψ ∘ σ⁻¹` (`galIso`) is again an
isometry, with matrix `σ(Ψ)` (`glOf_galIso`), and `C(ψ)` intertwines the Galois actions on the Clifford
algebras up to replacing `ψ` by `σψ` (`galC_map`).  Conjugation by `g ∈ GSpin(V)` is `C(P(g))`
(`map_specPIso_apply`).  Own work, elementary.
-/

noncomputable section

namespace GSpinGGP

open CliffordAlgebra TwistDescent
open scoped TensorProduct

section SpecPIso

variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]

/-- `P(g)` as an isometry of `(V, q)`. -/
def specPIso {Q : QuadraticForm K V} (g : GSpin Q) : Q.IsometryEquiv Q where
  toLinearEquiv := specP Q g
  map_app' := specP_isometry g

@[simp]
theorem specPIso_apply {Q : QuadraticForm K V} (g : GSpin Q) (v : V) :
    specPIso g v = specP Q g v := rfl

/-- `C(P(g))` is conjugation by `g`. -/
theorem map_specPIso_apply {Q : QuadraticForm K V} (g : GSpin Q) (a : CliffordAlgebra Q) :
    CliffordAlgebra.map (specPIso g).toIsometry a =
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * a *
        (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => simp [Algebra.commutes, mul_assoc]
  | ι x => rw [map_apply_ι]; exact ι_specP g x
  | mul a b ha hb => rw [map_mul, ha, hb]; simp only [mul_assoc, Units.inv_mul_cancel_left]
  | add a b ha hb => rw [map_add, ha, hb, mul_add, add_mul]

end SpecPIso

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

end GSpinGGP
