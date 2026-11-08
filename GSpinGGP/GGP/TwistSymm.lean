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
  DFunLike.ext _ _ fun _ => rfl

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


section Compose

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
  {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}

/-- **Rational conjugation of the target**: if `x ∼ y` through `φ`, then `x ∼ k y k⁻¹` for
rational `k ∈ GSpin(Q₂)(F)` (witness `k g`). -/
theorem StronglyStablyConjVia.conj_right {φ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)}
    {x : (CliffordAlgebra Q₁)ˣ} {y : (CliffordAlgebra Q₂)ˣ} (h : StronglyStablyConjVia φ x y)
    (k : GSpin Q₂) :
    StronglyStablyConjVia φ x ((k : (CliffordAlgebra Q₂)ˣ) * y * (k : (CliffordAlgebra Q₂)ˣ)⁻¹) := by
  obtain ⟨g, hg, hconj, hrat⟩ := h
  refine ⟨bcUnits Q₂ (k : (CliffordAlgebra Q₂)ˣ) * g,
    Subgroup.mul_mem _ (TorusTransfer.bcUnits_mem_GSpin Q₂ k) hg, ?_, fun σ z hz hzx => ?_⟩
  · rw [map_mul, map_mul, map_inv, ← hconj]; group
  · have hk : ∀ u : (CliffordAlgebra Q₂)ˣ, galC Q₂ σ (bcUnits Q₂ u).val = (bcUnits Q₂ u).val :=
      fun u => TorusTransfer.galC_bcHom' Q₂ σ (u : CliffordAlgebra Q₂)
    have e : ((bcUnits Q₂ (k : (CliffordAlgebra Q₂)ˣ) * g) * cliffUnits φ z *
        (bcUnits Q₂ (k : (CliffordAlgebra Q₂)ˣ) * g)⁻¹).val =
        (bcUnits Q₂ (k : (CliffordAlgebra Q₂)ˣ)).val * (g * cliffUnits φ z * g⁻¹).val *
          (bcUnits Q₂ ((k : (CliffordAlgebra Q₂)ˣ)⁻¹)).val := by
      simp only [map_inv, mul_inv_rev, Units.val_mul, mul_assoc]
    rw [e, map_mul, map_mul, hk, hk, hrat σ z hz hzx]
    simp only [map_inv, mul_inv_rev, Units.val_mul, mul_assoc]

/-- `φ ⊕ id_Z` for the trivial twist is the identity. -/
theorem GGPData.twistV_reflTwist_apply (d : GGPData F) (v : Kb ⊗[F] d.V) :
    d.twistV d.reflTwist v = v :=
  (prodBaseChange d.QW d.QZ).symm_apply_apply v

/-- **Strong stable conjugacy through the trivial twist is reflexive** (witness `1`). -/
theorem GGPData.stronglyStablyConjW_refl_self (d : GGPData F) (x : GSpin d.QW) :
    d.StronglyStablyConjW d.reflTwist x x := by
  have hW : CliffordAlgebra.map (d.reflTwist.φ).toIsometry = AlgHom.id _ _ :=
    CliffordAlgebra.map_id _
  have hV : CliffordAlgebra.map (d.twistV d.reflTwist).toIsometry = AlgHom.id _ _ := by
    rw [← CliffordAlgebra.map_id]
    congr 1
    ext v
    exact d.twistV_reflTwist_apply v
  have hcW : ∀ z, cliffUnits d.reflTwist.φ z = z := fun z => Units.ext (by
    simp only [cliffUnits, hW]; rfl)
  have hcV : ∀ z, cliffUnits (d.twistV d.reflTwist) z = z := fun z => Units.ext (by
    simp only [cliffUnits, hV]; rfl)
  refine ⟨⟨1, Subgroup.one_mem _, ?_, fun σ z _ _ => ?_⟩,
    ⟨1, Subgroup.one_mem _, ?_, fun σ z _ _ => ?_⟩⟩
  · rw [hcW, inv_one, mul_one]; exact one_mul _
  · rw [hcW, hW]
    show galC d.QW σ ((1 * z * 1⁻¹ : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) :
      CliffordAlgebra (d.QW.baseChange Kb)) = _
    simp only [mul_one, one_mul, inv_one, Units.val_one]
    rfl
  · rw [hcV, inv_one, mul_one]; exact one_mul _
  · rw [hcV, hV]
    show galC d.QV σ ((1 * z * 1⁻¹ : (CliffordAlgebra (d.QV.baseChange Kb))ˣ) :
      CliffordAlgebra (d.QV.baseChange Kb)) = _
    simp only [mul_one, one_mul, inv_one, Units.val_one]
    rfl

/-- **Rational conjugation of the target**: `x ∼_τ y` gives `x ∼_τ k y k⁻¹` for `k ∈ GSpin(W_τ)(F)`. -/
theorem GGPData.stronglyStablyConjW_conj_right (d : GGPData F) (τ : InnerTwist d.QW)
    {x : GSpin d.QW} {y : GSpin (d.twist τ).QW} (h : d.StronglyStablyConjW τ x y)
    (k : GSpin (d.twist τ).QW) : d.StronglyStablyConjW τ x (k * y * k⁻¹) := by
  obtain ⟨hW, hV⟩ := h
  refine ⟨hW.conj_right k, ?_⟩
  have e : (((d.twist τ).snd ((d.twist τ).diag (k * y * k⁻¹)) : GSpin (d.twist τ).QV) :
      (CliffordAlgebra (d.twist τ).QV)ˣ) = ((d.twist τ).incl k : (CliffordAlgebra (d.twist τ).QV)ˣ) *
        ((d.twist τ).snd ((d.twist τ).diag y) : (CliffordAlgebra (d.twist τ).QV)ˣ) *
        ((d.twist τ).incl k : (CliffordAlgebra (d.twist τ).QV)ˣ)⁻¹ := by
    change (((d.twist τ).incl (k * y * k⁻¹) : GSpin (d.twist τ).QV) :
      (CliffordAlgebra (d.twist τ).QV)ˣ) = _
    rw [map_mul, map_mul, map_inv]
    rfl
  change StronglyStablyConjVia _ _ ((((d.twist τ).snd ((d.twist τ).diag (k * y * k⁻¹)) :
    GSpin (d.twist τ).QV) : (CliffordAlgebra (d.twist τ).QV)ˣ))
  rw [e]
  exact hV.conj_right ((d.twist τ).incl k)

/-- **Rational conjugates are strongly stably conjugate** through the trivial twist. -/
theorem GGPData.stronglyStablyConjW_refl_conj (d : GGPData F) (x k : GSpin d.QW) :
    d.StronglyStablyConjW d.reflTwist x (k * x * k⁻¹) :=
  d.stronglyStablyConjW_conj_right d.reflTwist (d.stronglyStablyConjW_refl_self x) k

/-- **Composition with the trivial twist on the left**: `x ∼_1 z` and `z ∼_τ y` give `x ∼_τ y`. -/
theorem GGPData.stronglyStablyConjW_trans_refl (d : GGPData F) (τ : InnerTwist d.QW)
    {x z : GSpin d.QW} {y : GSpin (d.twist τ).QW} (h₁ : d.StronglyStablyConjW d.reflTwist x z)
    (h₂ : d.StronglyStablyConjW τ z y) : d.StronglyStablyConjW τ x y := by
  obtain ⟨hW₁, hV₁⟩ := h₁
  obtain ⟨hW₂, hV₂⟩ := h₂
  have hW₁' : StronglyStablyConjVia (Q₂ := d.QW) d.reflTwist.φ (x : (CliffordAlgebra d.QW)ˣ)
      (z : (CliffordAlgebra d.QW)ˣ) := hW₁
  have hV₁' : StronglyStablyConjVia (Q₂ := d.QV) (d.twistV d.reflTwist)
      (d.incl x : (CliffordAlgebra d.QV)ˣ) (d.incl z : (CliffordAlgebra d.QV)ˣ) := hV₁
  have hW₂' : StronglyStablyConjVia τ.φ (z : (CliffordAlgebra d.QW)ˣ)
      (y : (CliffordAlgebra τ.Q')ˣ) := hW₂
  have hV₂' : StronglyStablyConjVia (d.twistV τ) (d.incl z : (CliffordAlgebra d.QV)ˣ)
      ((d.twist τ).incl y : (CliffordAlgebra (d.twist τ).QV)ˣ) := hV₂
  have hW := TorusTransfer.StronglyStablyConjVia.trans hW₁' hW₂'
  have hV := TorusTransfer.StronglyStablyConjVia.trans hV₁' hV₂'
  have eW : d.reflTwist.φ.trans τ.φ = τ.φ := DFunLike.ext _ _ fun _ => rfl
  have eV : (d.twistV d.reflTwist).trans (d.twistV τ) = d.twistV τ :=
    DFunLike.ext _ _ fun v => congrArg (d.twistV τ) (d.twistV_reflTwist_apply v)
  exact ⟨eW ▸ hW, eV ▸ hV⟩

/-- **Two elements strongly stably conjugate to a common `y`** (through the same twist) are
strongly stably conjugate through the trivial twist. -/
theorem GGPData.stronglyStablyConjW_refl_of_common (d : GGPData F) (τ : InnerTwist d.QW)
    {x s : GSpin d.QW} {y : GSpin (d.twist τ).QW} (h₁ : d.StronglyStablyConjW τ x y)
    (h₂ : d.StronglyStablyConjW τ s y) : d.StronglyStablyConjW d.reflTwist x s := by
  obtain ⟨hW₁, hV₁⟩ := h₁
  obtain ⟨hW₂, hV₂⟩ := h₂
  have hW₁' : StronglyStablyConjVia τ.φ (x : (CliffordAlgebra d.QW)ˣ)
      (y : (CliffordAlgebra τ.Q')ˣ) := hW₁
  have hV₁' : StronglyStablyConjVia (d.twistV τ) (d.incl x : (CliffordAlgebra d.QV)ˣ)
      ((d.twist τ).incl y : (CliffordAlgebra (d.twist τ).QV)ˣ) := hV₁
  have hW₂' : StronglyStablyConjVia τ.φ.symm (y : (CliffordAlgebra τ.Q')ˣ)
      (s : (CliffordAlgebra d.QW)ˣ) := TorusTransfer.StronglyStablyConjVia.symm (x := s) hW₂
  have hV₂' : StronglyStablyConjVia (d.twistV τ).symm
      ((d.twist τ).incl y : (CliffordAlgebra (d.twist τ).QV)ˣ)
      (d.incl s : (CliffordAlgebra d.QV)ˣ) :=
    TorusTransfer.StronglyStablyConjVia.symm (x := d.incl s) hV₂
  have hW := TorusTransfer.StronglyStablyConjVia.trans hW₁' hW₂'
  have hV := TorusTransfer.StronglyStablyConjVia.trans hV₁' hV₂'
  have eW : τ.φ.trans τ.φ.symm = d.reflTwist.φ :=
    DFunLike.ext _ _ fun w => τ.φ.symm_apply_apply w
  have eV : (d.twistV τ).trans (d.twistV τ).symm = d.twistV d.reflTwist :=
    DFunLike.ext _ _ fun v => ((d.twistV τ).symm_apply_apply v).trans
      (d.twistV_reflTwist_apply v).symm
  exact ⟨eW ▸ hW, eV ▸ hV⟩

end Compose

end GSpinGGP
