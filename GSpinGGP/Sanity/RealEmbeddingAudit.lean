/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.RealEmbedding
import GSpinGGP.Foundations.LocalGroups
import GSpinGGP.Foundations.RealEmbeddingClassification

/-!
# Sanity checks for `RealEmbedding`

`ℝ` and `ℂ` have a real embedding (the identity and the inclusion), and it is unique; `ℚ_[p]`, and
every ultrametric local field, has none. Conversely a non-ultrametric complete normed field has
one, and for `ℝ` and `ℂ` it is the known one; the cases `ℝ` (`-1` not a square) and `ℂ` (`-1` a
square) of the classification are realized.
-/

namespace GSpinGGP.Sanity.RealEmbeddingAudit

open GSpinGGP

/-- The identity is the real embedding of `ℝ`. -/
noncomputable def realId : RealEmbedding ℝ := .mk (RingHom.id ℝ) continuous_id

/-- The inclusion `ℝ → ℂ` is the real embedding of `ℂ`. -/
noncomputable def complexOfReal : RealEmbedding ℂ := .mk Complex.ofRealHom Complex.continuous_ofReal

example : Nonempty (RealEmbedding ℝ) := ⟨realId⟩

example : Nonempty (RealEmbedding ℂ) := ⟨complexOfReal⟩

/-- Uniqueness is consistent with Mathlib's `Real.RingHom.unique` (which needs no continuity). -/
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

/-! ### Existence and classification -/

/-- The real embedding of `ℝ` produced by Ostrowski's theorem is the identity. -/
example (x : ℝ) :
    (nonempty_realEmbedding_of_not_isUltrametricDist not_isUltrametricDist_real).some x = x := by
  rw [Subsingleton.elim
    (nonempty_realEmbedding_of_not_isUltrametricDist not_isUltrametricDist_real).some realId]
  rfl

/-- The real embedding of `ℂ` produced by Ostrowski's theorem is the inclusion. -/
example (x : ℝ) :
    (nonempty_realEmbedding_of_not_isUltrametricDist not_isUltrametricDist_complex).some x =
      (x : ℂ) := by
  rw [Subsingleton.elim (nonempty_realEmbedding_of_not_isUltrametricDist
    not_isUltrametricDist_complex).some complexOfReal]
  rfl

/-- The dichotomy at `ℚ_[p]`, `ℝ`, `ℂ`, each landing on the expected side. -/
example (p : ℕ) [Fact p.Prime] : ¬ Nonempty (RealEmbedding ℚ_[p]) :=
  fun h => (not_isUltrametricDist_iff_nonempty_realEmbedding _).2 h inferInstance

example : Nonempty (RealEmbedding ℝ) :=
  (not_isUltrametricDist_iff_nonempty_realEmbedding _).1 not_isUltrametricDist_real

example : Nonempty (RealEmbedding ℂ) :=
  (not_isUltrametricDist_iff_nonempty_realEmbedding _).1 not_isUltrametricDist_complex

example (F : Type*) [NontriviallyNormedField F] [LocalField F] :
    IsUltrametricDist F ∨ Nonempty (RealEmbedding F) :=
  isUltrametricDist_or_nonempty_realEmbedding F

/-! ### The archimedean cases at the binders later code uses -/

section LocalField

variable (F : Type*) [NontriviallyNormedField F] [LocalField F]

example : ¬ IsUltrametricDist F ↔ Nonempty (RealEmbedding F) :=
  not_isUltrametricDist_iff_nonempty_realEmbedding F

/-- A non-ultrametric local field in which `-1` is not a square is `ℝ`. -/
example (hu : ¬ IsUltrametricDist F) (h : ¬ IsSquare (-1 : F)) :
    ∃ e : ℝ ≃+* F, IsHomeomorph e := by
  obtain ⟨φ⟩ := nonempty_realEmbedding_of_not_isUltrametricDist hu
  obtain ⟨e, he, -⟩ := φ.exists_ringEquiv_real_of_not_isSquare_neg_one h
  exact ⟨e, he⟩

/-- A non-ultrametric local field in which `-1` is a square is `ℂ`. -/
example (hu : ¬ IsUltrametricDist F) (h : IsSquare (-1 : F)) :
    ∃ e : ℂ ≃+* F, IsHomeomorph e := by
  obtain ⟨φ⟩ := nonempty_realEmbedding_of_not_isUltrametricDist hu
  obtain ⟨e, he, -⟩ := φ.exists_ringEquiv_complex_of_isSquare_neg_one h
  exact ⟨e, he⟩

end LocalField

/-- `ℂ` has characteristic zero by the non-ultrametric criterion, consistent with Mathlib. -/
example : CharZero ℂ := charZero_of_not_isUltrametricDist not_isUltrametricDist_complex

/-- `-1` is not a square in `ℝ`, so the case `ℝ` is the identity, a homeomorphism. -/
example : IsHomeomorph realId :=
  realId.isHomeomorph_of_not_isSquare_neg_one fun ⟨r, hr⟩ => by nlinarith [mul_self_nonneg r]

/-- `-1 = i * i` in `ℂ`, so the case `ℂ` applies to `ℂ` itself. -/
example : ∃ e : ℂ ≃+* ℂ, IsHomeomorph e ∧ ∀ r : ℝ, e r = r :=
  complexOfReal.exists_ringEquiv_complex_of_isSquare_neg_one ⟨Complex.I, Complex.I_mul_I.symm⟩

/-- The two cases exclude each other: in `ℂ` the real embedding is not surjective. -/
example : ¬ Function.Surjective complexOfReal := fun h => by
  obtain ⟨r, hr⟩ := h Complex.I
  simpa [complexOfReal] using congrArg Complex.im hr

end GSpinGGP.Sanity.RealEmbeddingAudit
