/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Recovering coefficients from finitely many values

Let `f_i : S → K`, `i ∈ ι` (`ι` finite), be linearly independent functions on a set `S`. Then each
coefficient of a combination `∑ a_i f_i` is a fixed linear combination of its values at finitely
many points of `S`: the evaluation functionals `a ↦ ∑ a_i f_i(s)` on `K^ι` have zero common kernel,
so they span the (finite-dimensional) dual.

* `exists_finset_coord_eq_sum_eval`: `a_{i₀} = ∑_{s ∈ σ} β_s ∑_i a_i f_i(s)` for all `a`.
* `exists_bound_coord_of_eval`: over a normed field, `‖a_{i₀}‖ ≤ C · M` whenever
  `‖∑_i a_i f_i(s)‖ ≤ M` at the finitely many points `s ∈ σ`.

Used to bound one germ by finitely many values of a local expansion (Thesis Prop 12.1.1(i), proof
of (12.1.2)).
-/

open Module

namespace GSpinGGP

variable {K S ι : Type*} [Field K] [Fintype ι]

/-- **One coefficient is a combination of finitely many values.** If the functions `f_i : S → K`,
`i ∈ ι` finite, are linearly independent (`∑_i a_i f_i = 0` on `S` forces `a = 0`), then for each
`i₀` there are a finite set `σ ⊆ S` and weights `β` with `a_{i₀} = ∑_{s ∈ σ} β_s ∑_i a_i f_i(s)` for
every `a : ι → K`. -/
theorem exists_finset_coord_eq_sum_eval (f : ι → S → K)
    (hf : ∀ a : ι → K, (∀ s, ∑ i, a i * f i s = 0) → a = 0) (i₀ : ι) :
    ∃ (σ : Finset S) (β : S → K), ∀ a : ι → K, a i₀ = ∑ s ∈ σ, β s * ∑ i, a i * f i s := by
  classical
  let Φ : S → Dual K (ι → K) := fun s =>
    { toFun := fun a => ∑ i, a i * f i s
      map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [Finset.mul_sum, mul_assoc] }
  let W : Subspace K (Dual K (ι → K)) := Submodule.span K (Set.range Φ)
  have hco : W.dualCoannihilator = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun a ha => hf a fun s => ?_
    exact (Submodule.mem_dualCoannihilator a).mp ha (Φ s) (Submodule.subset_span ⟨s, rfl⟩)
  have hW : W = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hco,
      Submodule.dualAnnihilator_bot]
  have hmem : (LinearMap.proj i₀ : (ι → K) →ₗ[K] K) ∈ W := hW ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
  refine ⟨c.support, c, fun a => ?_⟩
  have := congrArg (fun φ : Dual K (ι → K) => φ a) hc
  simp only [LinearMap.proj_apply] at this
  rw [← this, Finsupp.sum, LinearMap.sum_apply]
  rfl

/-- **Bounding one coefficient by finitely many values.** Over a normed field, under the
hypotheses of `exists_finset_coord_eq_sum_eval` there are a finite set `σ ⊆ S` and a constant `C`
such that `‖a_{i₀}‖ ≤ C · M` whenever `‖∑_i a_i f_i(s)‖ ≤ M` for all `s ∈ σ`. -/
theorem exists_bound_coord_of_eval {K : Type*} [NormedField K] (f : ι → S → K)
    (hf : ∀ a : ι → K, (∀ s, ∑ i, a i * f i s = 0) → a = 0) (i₀ : ι) :
    ∃ (σ : Finset S) (C : ℝ), 0 ≤ C ∧ ∀ (a : ι → K) (M : ℝ),
      (∀ s ∈ σ, ‖∑ i, a i * f i s‖ ≤ M) → ‖a i₀‖ ≤ C * M := by
  obtain ⟨σ, β, hβ⟩ := exists_finset_coord_eq_sum_eval f hf i₀
  refine ⟨σ, ∑ s ∈ σ, ‖β s‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun a M hM => ?_⟩
  rw [hβ a, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM s hs) (norm_nonneg _)

end GSpinGGP
