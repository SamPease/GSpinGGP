/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TorusTransport
import GSpinGGP.GGP.TwistDescent

/-!
# The inverse inner twist, and symmetry of strong stable conjugacy

* `InnerTwist.symm`: for an inner twist `(W', φ)` of a nondegenerate `W`, the inner twist `(W, φ⁻¹)`
  of `W'`.  For a GGP datum `d` and `τ = (W_α, φ_α)`, the twist of `d_α = d.twist τ` by `τ.symm` is
  `d` itself (definitionally: same `m`, `QW`, `r`, `ν`).
* `StronglyStablyConjVia.of_symm`: strong stable conjugacy through `φ⁻¹` from `y` to `x` gives it
  through `φ` from `x` to `y` (`TorusTransfer.ratAt_symm`).
* `GGPData.stronglyStablyConjW_of_symm`: `d_α`-strong stable conjugacy of `y ∈ GSpin(W_α)` with
  `x ∈ GSpin(W)` through `τ.symm` is `d`-strong stable conjugacy of `x` with `y` through `τ`.
-/

noncomputable section

open CliffordAlgebra
open scoped TensorProduct

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

open TwistDescent in
/-- **The inverse inner twist** `(W, φ⁻¹)` of `W'`, for an inner twist `τ = (W', φ)` of a
nondegenerate `W`.  The cocycle condition: `φ ∘ σ(φ⁻¹)` is conjugate to `(φ⁻¹ ∘ σφ)⁻¹`. -/
def InnerTwist.symm {m : ℕ} {Q : QuadraticForm F (Fin m → F)} (hQ : IsNondeg Q)
    (τ : InnerTwist Q) : InnerTwist τ.Q' where
  Q' := Q
  nondeg' := hQ
  sameDisc := by
    obtain ⟨c, hc, h⟩ := τ.sameDisc
    refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
    rw [h, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hc, one_pow, one_mul]
  φ := τ.φ.symm
  cocycle σ := by
    have h := det_glOf_inv_mul_galGL τ σ
    set X := glOf τ.φ
    have key : LinearMap.toMatrix (bcBasis F m) (bcBasis F m)
        (τ.φ.symm.toLinearEquiv.symm.toLinearMap ∘ₗ
          galoisConj σ τ.φ.symm.toLinearEquiv.toLinearMap) =
        ((X * (galGL m σ X)⁻¹ : GL (Fin m) Kb) : Matrix (Fin m) (Fin m) Kb) := by
      rw [LinearMap.toMatrix_comp _ (bcBasis F m), toMatrix_galoisConj, Units.val_mul, ← map_inv,
        coe_galGL]
      rfl
    rw [← LinearMap.det_toMatrix (bcBasis F m), key]
    have hconj : X * (galGL m σ X)⁻¹ = X * (X⁻¹ * galGL m σ X)⁻¹ * X⁻¹ := by group
    rw [hconj, Units.val_mul, Units.val_mul, Matrix.det_units_conj]
    have h1 := congrArg Matrix.det (congrArg Units.val (mul_inv_cancel (X⁻¹ * galGL m σ X)))
    rw [Units.val_mul, Matrix.det_mul, h, one_mul, Units.val_one, Matrix.det_one] at h1
    exact h1

/-- The twist of `d_α = d.twist τ` by `τ.symm` is `d`. -/
theorem GGPData.twist_symm (d : GGPData F) (τ : InnerTwist d.QW) :
    (d.twist τ).twist (τ.symm d.nondeg) = d := rfl

omit [NontriviallyNormedField F] [PAdicField F] in
/-- Isometries with the same values are equal. -/
theorem isometryEquiv_ext {R V₁ V₂ : Type*} [CommRing R] [AddCommGroup V₁] [Module R V₁]
    [AddCommGroup V₂] [Module R V₂] {Q₁ : QuadraticForm R V₁} {Q₂ : QuadraticForm R V₂}
    {e e' : Q₁.IsometryEquiv Q₂} (h : ∀ v, e v = e' v) : e = e' := by
  obtain ⟨e, he⟩ := e
  obtain ⟨e', he'⟩ := e'
  have : e = e' := LinearEquiv.ext h
  subst this
  rfl

/-- **Symmetry of strong stable conjugacy**: strong stable conjugacy of `y ∈ GSpin(Q₂)(F)` with `x`
through `φ⁻¹` gives strong stable conjugacy of `x` with `y` through `φ` (witness `C(φ)(g⁻¹)`;
`TorusTransfer.ratAt_symm`). -/
theorem StronglyStablyConjVia.of_symm {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁]
    [AddCommGroup V₂] [Module F V₂] {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}
    (φ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) {x : (CliffordAlgebra Q₁)ˣ}
    {y : GSpin Q₂} (h : StronglyStablyConjVia φ.symm (y : (CliffordAlgebra Q₂)ˣ) x) :
    StronglyStablyConjVia φ x (y : (CliffordAlgebra Q₂)ˣ) := by
  obtain ⟨g, hg, hconj, hrat⟩ := h
  have hrat' : TorusTransfer.RatAt φ.symm g (y : (CliffordAlgebra Q₂)ˣ) := hrat
  have hconj' : TorusTransfer.psiU φ.symm g (bcUnits Q₂ (y : (CliffordAlgebra Q₂)ˣ)) =
      bcUnits Q₁ x := hconj
  refine ⟨cliffUnits φ.symm.symm g⁻¹, TorusTransfer.mem_GSpin_symm hg, ?_,
    TorusTransfer.ratAt_symm hg hrat' hconj'⟩
  have := TorusTransfer.psiU_symm_psiU (φ := φ.symm) (g := g) (bcUnits Q₂ (y : (CliffordAlgebra Q₂)ˣ))
  rw [hconj'] at this
  exact this

/-- The extension to `V` of the inverse twist is the inverse of the extension (pointwise, hence
equal). -/
theorem GGPData.twistV_symm (d : GGPData F) (τ : InnerTwist d.QW) :
    (d.twist τ).twistV (τ.symm d.nondeg) = (d.twistV τ).symm :=
  isometryEquiv_ext fun _ => rfl

/-- **Strong stable conjugacy through the inverse twist**: if `y ∈ GSpin(W_α)` is strongly stably
conjugate to `x ∈ GSpin(W)` in the datum `d_α` through `τ.symm`, then `x` is strongly stably
conjugate to `y` in `d` through `τ`. -/
theorem GGPData.stronglyStablyConjW_of_symm (d : GGPData F) (τ : InnerTwist d.QW)
    {x : GSpin d.QW} {y : GSpin (d.twist τ).QW}
    (h : (d.twist τ).StronglyStablyConjW (τ.symm d.nondeg) y x) :
    d.StronglyStablyConjW τ x y := by
  obtain ⟨hW, hV⟩ := h
  refine ⟨StronglyStablyConjVia.of_symm τ.φ hW, ?_⟩
  rw [GGPData.twistV_symm] at hV
  exact StronglyStablyConjVia.of_symm (d.twistV τ) hV

end GSpinGGP
