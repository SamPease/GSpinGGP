/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Continuous embeddings of `ℝ`

For a semiring `F` with a topology, `RealEmbedding F` is the type of continuous ring homomorphisms
`ℝ →+* F`. It is the `ℝ`-structure used for the archimedean local fields: over `ℝ` it is the
identity and over `ℂ` the inclusion. We do not use `NormedAlgebra ℝ F`, since the norm of a local
field need not restrict to the absolute value of `ℝ` (for instance `|x|^{1/2}` on `ℝ`); only
continuity is asked for.

## Main results

* `RealEmbedding.instSubsingleton`: a semiring with a Hausdorff topology has at most one real
  embedding, since two continuous ring homomorphisms agree on the dense subset `ℚ ⊆ ℝ`.
* `RealEmbedding.instIsEmpty`: an ultrametric normed division ring has no real embedding: the
  image of `(n : ℝ)⁻¹ → 0` would be `(n : F)⁻¹`, of norm `≥ 1` since `‖(n : F)‖ ≤ 1`.
-/

namespace GSpinGGP

/-- A *real embedding* of a semiring `F` with a topology: a continuous ring homomorphism
`ℝ →+* F`. -/
def RealEmbedding (F : Type*) [NonAssocSemiring F] [TopologicalSpace F] : Type _ :=
  {φ : ℝ →+* F // Continuous φ}

namespace RealEmbedding

section Basic

variable {F : Type*} [NonAssocSemiring F] [TopologicalSpace F]

/-- The underlying ring homomorphism. -/
def toRingHom (φ : RealEmbedding F) : ℝ →+* F := Subtype.val φ

theorem toRingHom_injective : Function.Injective (toRingHom : RealEmbedding F → ℝ →+* F) :=
  Subtype.val_injective

/-- Build a real embedding from a continuous ring homomorphism. -/
def mk (φ : ℝ →+* F) (hφ : Continuous φ) : RealEmbedding F := ⟨φ, hφ⟩

instance : FunLike (RealEmbedding F) ℝ F where
  coe φ := φ.toRingHom
  coe_injective _ _ h := toRingHom_injective (DFunLike.coe_injective h)

instance : RingHomClass (RealEmbedding F) ℝ F where
  map_mul φ := map_mul φ.toRingHom
  map_one φ := map_one φ.toRingHom
  map_add φ := map_add φ.toRingHom
  map_zero φ := map_zero φ.toRingHom

instance : ContinuousMapClass (RealEmbedding F) ℝ F where
  map_continuous φ := Subtype.property φ

@[simp] theorem coe_toRingHom (φ : RealEmbedding F) : ⇑φ.toRingHom = φ := rfl

@[simp] theorem coe_mk (φ : ℝ →+* F) (hφ : Continuous φ) : ⇑(mk φ hφ) = φ := rfl

@[simp] theorem toRingHom_mk (φ : ℝ →+* F) (hφ : Continuous φ) : (mk φ hφ).toRingHom = φ := rfl

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
