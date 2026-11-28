/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.RealEmbedding
import GSpinGGP.Foundations.LocalGroups
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Sanity checks for `RealEmbedding`

`ℝ` and `ℂ` have a real embedding (the identity and the inclusion), and it is unique; `ℚ_[p]`, and
every ultrametric local field, has none.
-/

namespace GSpinGGP.Sanity.RealEmbeddingAudit

open GSpinGGP

/-- The identity is the real embedding of `ℝ`. -/
noncomputable def realId : RealEmbedding ℝ := .mk (RingHom.id ℝ) continuous_id

/-- The inclusion `ℝ → ℂ` is the real embedding of `ℂ`. -/
noncomputable def complexOfReal : RealEmbedding ℂ := .mk Complex.ofRealHom Complex.continuous_ofReal

example : Nonempty (RealEmbedding ℝ) := ⟨realId⟩

example : Nonempty (RealEmbedding ℂ) := ⟨complexOfReal⟩

/-- Uniqueness recovers Mathlib's `Real.RingHom.unique` for continuous ring endomorphisms. -/
example {f : ℝ →+* ℝ} (hf : Continuous f) : f = RingHom.id ℝ :=
  realId.eq_of_continuous hf

/-- Uniqueness recovers Mathlib's `Complex.ringHom_eq_ofReal_of_continuous`. -/
example {f : ℝ →+* ℂ} (hf : Continuous f) : f = Complex.ofRealHom :=
  complexOfReal.eq_of_continuous hf

example (φ : RealEmbedding ℂ) (x : ℝ) : φ x = x := by
  rw [Subsingleton.elim φ complexOfReal]; rfl

example (p : ℕ) [Fact p.Prime] : IsEmpty (RealEmbedding ℚ_[p]) := inferInstance

/-- No local-field hypothesis is needed: an ultrametric norm suffices. -/
example (F : Type*) [NontriviallyNormedField F] [IsUltrametricDist F] :
    IsEmpty (RealEmbedding F) := inferInstance

example (F : Type*) [NontriviallyNormedField F] [LocalField F] [IsUltrametricDist F] :
    IsEmpty (RealEmbedding F) := inferInstance

example (F : Type*) [NontriviallyNormedField F] [PAdicField F] : IsEmpty (RealEmbedding F) :=
  inferInstance

/-- Consistency with `not_isUltrametricDist_real`: the existence of a real embedding alone shows
that `ℝ` is not ultrametric. -/
example : ¬ IsUltrametricDist ℝ := fun _ => IsEmpty.false realId

example : ¬ IsUltrametricDist ℂ := fun _ => IsEmpty.false complexOfReal

end GSpinGGP.Sanity.RealEmbeddingAudit
