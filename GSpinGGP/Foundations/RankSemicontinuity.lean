/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Semicontinuity of rank and kernel dimension

For a family `x ↦ f x` of linear maps `M → N` between finite-dimensional spaces over a complete
nontrivially normed field, depending continuously on `x` pointwise (`x ↦ f x v` continuous for
each `v`), the rank is lower semicontinuous and the kernel dimension upper semicontinuous.  If
moreover `ker f x₀ ⊆ ker f x` near `x₀`, the kernels agree near `x₀`.

This is the form of `isOpen_setOfPred_nat_le_rank` used for families of the shape
`x ↦ (v ↦ x v − v x)` in an algebra with its module topology.
-/

open Filter Topology Module

namespace GSpinGGP

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {X : Type*} [TopologicalSpace X]
  {M : Type*} [AddCommGroup M] [Module 𝕜 M]
  {N : Type*} [AddCommGroup N] [Module 𝕜 N] [FiniteDimensional 𝕜 N] [TopologicalSpace N]
  [IsModuleTopology 𝕜 N]

/-- **Lower semicontinuity of the rank**: near `x₀`, `rk f x ≥ rk f x₀`. -/
theorem eventually_finrank_range_le (f : X → M →ₗ[𝕜] N) (hf : ∀ v, Continuous fun x => f x v)
    (x₀ : X) :
    ∀ᶠ x in 𝓝 x₀, finrank 𝕜 (LinearMap.range (f x₀)) ≤ finrank 𝕜 (LinearMap.range (f x)) := by
  let e : N ≃ₗ[𝕜] (Fin (finrank 𝕜 N) → 𝕜) := (Module.finBasis 𝕜 N).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  let c := Module.finBasis 𝕜 (LinearMap.range (f x₀))
  choose v hv using fun i => (c i).2
  have hli : LinearIndependent 𝕜 (fun i => e (f x₀ (v i))) := by
    have h1 : LinearIndependent 𝕜 (fun i => (LinearMap.range (f x₀)).subtype (c i)) :=
      c.linearIndependent.map' _ (Submodule.ker_subtype _)
    have h2 := h1.map' e.toLinearMap e.ker
    convert h2 using 2 with i
    simp [hv]
  have hcont : Continuous fun x => fun i => e (f x (v i)) :=
    continuous_pi fun i => he.comp (hf (v i))
  filter_upwards [(hcont.tendsto x₀).eventually hli.eventually] with x hx
  have h3 : LinearIndependent 𝕜 (fun i => f x (v i)) :=
    LinearIndependent.of_comp e.toLinearMap hx
  have h4 : LinearIndependent 𝕜
      (fun i => (⟨f x (v i), LinearMap.mem_range_self _ _⟩ : LinearMap.range (f x))) :=
    LinearIndependent.of_comp (LinearMap.range (f x)).subtype h3
  simpa using h4.fintype_card_le_finrank

variable [FiniteDimensional 𝕜 M]

/-- **Upper semicontinuity of the kernel dimension**: near `x₀`, `dim ker f x ≤ dim ker f x₀`. -/
theorem eventually_finrank_ker_le (f : X → M →ₗ[𝕜] N) (hf : ∀ v, Continuous fun x => f x v)
    (x₀ : X) :
    ∀ᶠ x in 𝓝 x₀, finrank 𝕜 (LinearMap.ker (f x)) ≤ finrank 𝕜 (LinearMap.ker (f x₀)) := by
  filter_upwards [eventually_finrank_range_le f hf x₀] with x hx
  have h1 := LinearMap.finrank_range_add_finrank_ker (f x)
  have h2 := LinearMap.finrank_range_add_finrank_ker (f x₀)
  omega

/-- If `ker f x₀ ⊆ ker f x` near `x₀`, then `ker f x = ker f x₀` near `x₀`. -/
theorem eventually_ker_eq_of_le (f : X → M →ₗ[𝕜] N) (hf : ∀ v, Continuous fun x => f x v)
    (x₀ : X) (hle : ∀ᶠ x in 𝓝 x₀, LinearMap.ker (f x₀) ≤ LinearMap.ker (f x)) :
    ∀ᶠ x in 𝓝 x₀, LinearMap.ker (f x) = LinearMap.ker (f x₀) := by
  filter_upwards [eventually_finrank_ker_le f hf x₀, hle] with x h1 h2
  exact (Submodule.eq_of_le_of_finrank_le h2 h1).symm

end GSpinGGP
