/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.StableCocycleEven

/-!
# The cocycle of `y` when `dim W'_x` is even

On the `V`-factor `dim V'_x = dim W'_x + dim Z` is odd, so the witness `ψ_V` of strong stable
conjugacy on `V` is rational on `V'_x` (`galIso_trans_symm_eq_self_of_odd`), and gives an `F`-isometry
`W'_x ⊕ Z ≅ W'_y ⊕ Z`; Witt cancellation gives `W'_x ≅ W'_y`, and the change of witness
(`exists_isStableIso_of_isometry`) gives the cocycle.  With the odd case (`exists_isStableIso_of_odd`)
this defines the map `y ↦ [a] ∈ H¹(F, S_x)` of Thesis Prop. 6.6.1(iii) (`exists_isStableIso`).
Own work, elementary.
-/

noncomputable section

namespace GSpinGGP

open CliffordAlgebra TwistDescent TorusTransfer
open scoped TensorProduct

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

section Det

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
  {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}

/-- `ψ = P(g) ∘ e` and `e` have cocycles of the same determinant. -/
theorem det_galIso_trans_specPIso [FiniteDimensional F V₁] [FiniteDimensional F V₂]
    (e : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) (g : GSpin (Q₂.baseChange Kb))
    (σ : GalF F) :
    LinearMap.det ((galIso σ (e.trans (specPIso g))).trans (e.trans (specPIso g)).symm :
        Kb ⊗[F] V₁ →ₗ[Kb] Kb ⊗[F] V₁) =
      LinearMap.det ((galIso σ e).trans e.symm : Kb ⊗[F] V₁ →ₗ[Kb] Kb ⊗[F] V₁) := by
  set M : (Kb ⊗[F] V₂) →ₗ[Kb] (Kb ⊗[F] V₂) := (specP _ (g⁻¹ * galGS Q₂ σ g)).toLinearMap
  have key : ((galIso σ (e.trans (specPIso g))).trans (e.trans (specPIso g)).symm :
      Kb ⊗[F] V₁ →ₗ[Kb] Kb ⊗[F] V₁) =
      ((e.symm.toLinearEquiv : (Kb ⊗[F] V₂) →ₗ[Kb] _) ∘ₗ M ∘ₗ
        (e.toLinearEquiv : (Kb ⊗[F] V₁) →ₗ[Kb] _)) ∘ₗ
        ((galIso σ e).trans e.symm : Kb ⊗[F] V₁ →ₗ[Kb] Kb ⊗[F] V₁) := by
    refine LinearMap.ext fun w => ?_
    change (e.trans (specPIso g)).symm (galV σ (specP _ g (e (galV σ⁻¹ w)))) =
      e.symm (specP _ (g⁻¹ * galGS Q₂ σ g) (e (e.symm (galV σ (e (galV σ⁻¹ w))))))
    rw [e.apply_symm_apply, map_mul, LinearEquiv.mul_apply, ← specP_galGS]
    change e.symm (specP _ g⁻¹ _) = _
    rfl
  have hc : LinearMap.det ((e.symm.toLinearEquiv : (Kb ⊗[F] V₂) →ₗ[Kb] _) ∘ₗ M ∘ₗ
      (e.toLinearEquiv : (Kb ⊗[F] V₁) →ₗ[Kb] _)) = LinearMap.det M :=
    LinearMap.det_conj M e.symm.toLinearEquiv
  have hM : LinearMap.det M = 1 := det_specP _
  rw [key, LinearMap.det_comp, hc, hM, one_mul]

end Det

end GSpinGGP
