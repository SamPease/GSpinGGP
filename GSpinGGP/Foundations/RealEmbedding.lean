/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Continuous embeddings of `ℝ`

For a semiring `F` with a topology, `RealEmbedding F` is the type of continuous ring homomorphisms
`ℝ →+* F`. It is the `ℝ`-structure used for the archimedean local fields: over `ℝ` it is the
identity and over `ℂ` the inclusion. We do not use `NormedAlgebra ℝ F`, since the norm of a local
field need not restrict to the absolute value of `ℝ`: the field `ℝ` with the norm `|x|^{1/2}`
(a type synonym of `ℝ` carrying this non-standard norm, not Mathlib's instance on `ℝ`) is a
local field on which `‖r • x‖ = |r| ‖x‖` fails. Only continuity is asked for.

## Main results

* `RealEmbedding.instSubsingleton`: a semiring with a Hausdorff topology has at most one real
  embedding, since two continuous ring homomorphisms agree on the dense subset `ℚ ⊆ ℝ`.
* `RealEmbedding.instIsEmpty`: an ultrametric normed division ring has no real embedding: the
  image of `(n : ℝ)⁻¹ → 0` would be `(n : F)⁻¹`, of norm `≥ 1` since `‖(n : F)‖ ≤ 1`.
-/

namespace GSpinGGP

/-- A *real embedding* of a semiring `F` with a topology: a continuous ring homomorphism
`ℝ →+* F`.

It is injective when `F` is nontrivial (for instance a division ring), since `ℝ` is a field; the
zero ring has one, which is not injective. This is not the notion of a real embedding of a number
field (`NumberField.ComplexEmbedding.IsReal`). -/
structure RealEmbedding (F : Type*) [NonAssocSemiring F] [TopologicalSpace F]
    extends ℝ →+* F where
  continuous_toFun : Continuous toFun

namespace RealEmbedding

section Basic

variable {F : Type*} [NonAssocSemiring F] [TopologicalSpace F]

instance : FunLike (RealEmbedding F) ℝ F where
  coe φ := φ.toFun
  coe_injective f g h := by
    obtain ⟨f, _⟩ := f
    obtain ⟨g, _⟩ := g
    congr
    exact DFunLike.coe_injective h

instance : RingHomClass (RealEmbedding F) ℝ F where
  map_mul φ := map_mul φ.toRingHom
  map_one φ := map_one φ.toRingHom
  map_add φ := map_add φ.toRingHom
  map_zero φ := map_zero φ.toRingHom

instance : ContinuousMapClass (RealEmbedding F) ℝ F where
  map_continuous φ := φ.continuous_toFun

@[simp] theorem coe_toRingHom (φ : RealEmbedding F) : ⇑φ.toRingHom = φ := rfl

@[simp] theorem coe_mk (φ : ℝ →+* F) (hφ : Continuous φ) : ⇑(mk φ hφ) = φ := rfl

@[continuity, fun_prop]
protected theorem continuous (φ : RealEmbedding F) : Continuous φ := map_continuous φ

@[ext] theorem ext {φ ψ : RealEmbedding F} (h : ∀ x, φ x = ψ x) : φ = ψ := DFunLike.ext _ _ h

end Basic

section Unique

variable {F : Type*} [Semiring F] [TopologicalSpace F] [T2Space F]

/-- A semiring with a Hausdorff topology has at most one real embedding: two continuous ring
homomorphisms `ℝ →+* F` agree on `ℚ`, which is dense in `ℝ`. -/
instance instSubsingleton : Subsingleton (RealEmbedding F) where
  allEq φ ψ := by
    have hq : φ.toRingHom.comp (Rat.castHom ℝ) = ψ.toRingHom.comp (Rat.castHom ℝ) :=
      RingHom.ext_rat _ _
    ext x
    refine congrFun (Rat.denseRange_cast.equalizer φ.continuous ψ.continuous ?_) x
    funext q
    exact congrArg (· q) (congrArg DFunLike.coe hq)

/-- Any continuous ring homomorphism `ℝ →+* F` is the real embedding `φ`. -/
theorem eq_of_continuous (φ : RealEmbedding F) {f : ℝ →+* F} (hf : Continuous f) :
    f = φ.toRingHom :=
  congrArg toRingHom (Subsingleton.elim (mk f hf) φ)

end Unique

section Ultrametric

variable {F : Type*} [NormedDivisionRing F] [IsUltrametricDist F]

/-- An ultrametric normed division ring has no real embedding. If `φ : ℝ →+* F` were continuous,
then `φ (n : ℝ)⁻¹ = (n : F)⁻¹` would tend to `0`; but `‖(n : F)‖ ≤ 1`, so `‖(n : F)⁻¹‖ ≥ 1` for
`n ≥ 1` (`(n : F) ≠ 0` since `φ` is injective). -/
instance instIsEmpty : IsEmpty (RealEmbedding F) where
  false φ := by
    have hlim : Filter.Tendsto (fun n : ℕ => ((n : F))⁻¹) Filter.atTop (nhds 0) := by
      simpa [Function.comp_def] using
        (φ.continuous.tendsto 0).comp tendsto_inv_atTop_nhds_zero_nat
    have hge : ∀ n : ℕ, 1 ≤ n → 1 ≤ ‖((n : F))⁻¹‖ := by
      intro n hn
      have hne : (n : F) ≠ 0 := by
        rw [← map_natCast φ n]
        exact (map_ne_zero φ).2 (Nat.cast_ne_zero.2 (by omega))
      rw [norm_inv]
      exact one_le_inv₀ (norm_pos_iff.2 hne) |>.2 (IsUltrametricDist.norm_natCast_le_one F n)
    have h := (tendsto_norm_zero.comp hlim).eventually (gt_mem_nhds one_pos)
    obtain ⟨n, hn⟩ := (h.and (Filter.eventually_ge_atTop 1)).exists
    exact absurd (hge n hn.2) (not_le.2 hn.1)

end Ultrametric

end RealEmbedding

end GSpinGGP
