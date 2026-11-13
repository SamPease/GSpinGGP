/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Recovering coefficients from finitely many values

Let `f_i : S → K`, `i ∈ ι` (`ι` finite), be functions on a set `S`, and `i₀ ∈ ι` a coordinate that
is determined by the values: `∑ a_i f_i = 0` on `S` forces `a_{i₀} = 0` (true for every `i₀` when the
`f_i` are linearly independent). Then `a_{i₀}` is a fixed linear combination of the values of
`∑ a_i f_i` at finitely many points of `S`.

* `exists_finset_coord_eq_sum_eval`: `a_{i₀} = ∑_{s ∈ σ} β_s ∑_i a_i f_i(s)` for all `a`.
* `exists_bound_coord_of_eval`: over a normed field, `‖a_{i₀}‖ ≤ C · M` whenever
  `‖∑_i a_i f_i(s)‖ ≤ M` at the finitely many points `s ∈ σ`.

Used to bound one germ by finitely many values of a local expansion (Thesis Prop 12.1.1(i), proof
of (12.1.2)).
-/

open Module

namespace GSpinGGP

variable {K S ι : Type*} [Field K] [Fintype ι]

/-- **One coefficient is a combination of finitely many values.** Let `f_i : S → K`, `i ∈ ι` finite,
and `i₀ ∈ ι` be such that `∑_i a_i f_i = 0` on `S` forces `a_{i₀} = 0` (e.g. the `f_i` are linearly
independent). Then there are a finite set `σ ⊆ S` and weights `β` with
`a_{i₀} = ∑_{s ∈ σ} β_s ∑_i a_i f_i(s)` for every `a : ι → K`: the coordinate functional `a ↦ a_{i₀}`
vanishes on the common kernel of the evaluations, so it lies in their span
(`FiniteDimensional.mem_span_of_iInf_ker_le_ker`). -/
theorem exists_finset_coord_eq_sum_eval (f : ι → S → K) (i₀ : ι)
    (hf : ∀ a : ι → K, (∀ s, ∑ i, a i * f i s = 0) → a i₀ = 0) :
    ∃ (σ : Finset S) (β : S → K), ∀ a : ι → K, a i₀ = ∑ s ∈ σ, β s * ∑ i, a i * f i s := by
  classical
  let Φ : S → (ι → K) →ₗ[K] K := fun s => ∑ i, f i s • LinearMap.proj i
  have hmem : (LinearMap.proj i₀ : (ι → K) →ₗ[K] K) ∈ Submodule.span K (Set.range Φ) :=
    FiniteDimensional.mem_span_of_iInf_ker_le_ker fun a ha => by
      simp only [Submodule.mem_iInf, LinearMap.mem_ker] at ha
      exact hf a fun s => by simpa [Φ, mul_comm] using ha s
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
  refine ⟨c.support, c, fun a => ?_⟩
  have := congrArg (fun φ : (ι → K) →ₗ[K] K => φ a) hc
  simp only [LinearMap.proj_apply] at this
  rw [← this, Finsupp.sum, LinearMap.sum_apply]
  simp [Φ, mul_comm]

/-- **Bounding one coefficient by finitely many values.** Over a normed field, under the
hypotheses of `exists_finset_coord_eq_sum_eval` there are a finite set `σ ⊆ S` and a constant `C`
such that `‖a_{i₀}‖ ≤ C · M` whenever `‖∑_i a_i f_i(s)‖ ≤ M` for all `s ∈ σ`. -/
theorem exists_bound_coord_of_eval {K : Type*} [NormedField K] (f : ι → S → K) (i₀ : ι)
    (hf : ∀ a : ι → K, (∀ s, ∑ i, a i * f i s = 0) → a i₀ = 0) :
    ∃ (σ : Finset S) (C : ℝ), 0 ≤ C ∧ ∀ (a : ι → K) (M : ℝ),
      (∀ s ∈ σ, ‖∑ i, a i * f i s‖ ≤ M) → ‖a i₀‖ ≤ C * M := by
  obtain ⟨σ, β, hβ⟩ := exists_finset_coord_eq_sum_eval f i₀ hf
  refine ⟨σ, ∑ s ∈ σ, ‖β s‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun a M hM => ?_⟩
  rw [hβ a, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM s hs) (norm_nonneg _)

end GSpinGGP
