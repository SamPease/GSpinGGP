/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Sanity.Witnesses
import GSpinGGP.Literature.InvariantSets

/-!
# Degenerate check of the two axioms of `Literature/InvariantSets.lean`

At the smallest triple `toyD` (`W = 0`, `V` a line) the split centre is everything
(`toyD_AG_eq_top`), and both conclusions are proved here *without* the axioms, with `Ω = G(F)`:
the instances are consistent.  (Hyperbolic-plane triples, where `G(F)` is a split torus: see the
module docstring of `Literature/InvariantSets.lean`.)
-/

noncomputable section

open Topology

namespace GSpinGGP

namespace Sanity

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝕋" => (toyD (F := F))

/-- `hc_exists_invariantClopen_superset` at `toyD`, without the axiom. -/
theorem toyD_exists_invariantClopen_superset {C : Set ↥(𝕋).G} (_hC : IsCompact C) :
    ∃ Ω : Set ↥(𝕋).G, IsInvariantClopen (𝕋) Ω ∧ C ⊆ Ω ∧
      ∃ C' : Set ↥(𝕋).G, IsCompact C' ∧
        ∀ g ∈ Ω, ∃ (a : ↥(𝕋).AG) (x c : ↥(𝕋).G), c ∈ C' ∧ g = (a : ↥(𝕋).G) * (x * c * x⁻¹) := by
  refine ⟨Set.univ, isInvariantClopen_univ _, Set.subset_univ _, {1}, isCompact_singleton,
    fun g _ => ⟨⟨g, by rw [toyD_AG_eq_top]; trivial⟩, 1, 1, rfl, by simp⟩⟩

/-- `hc_exists_invariantClopen_nearCentral` at `toyD`, without the axiom. -/
theorem toyD_exists_invariantClopen_nearCentral {U : Set ↥(𝕋).G} (hU : U ∈ 𝓝 (1 : ↥(𝕋).G)) :
    ∃ Ω : Set ↥(𝕋).G, IsInvariantClopen (𝕋) Ω ∧
      (∀ c : ↥(𝕋).G, (∀ V ∈ 𝓝 (1 : ↥(𝕋).G), ∃ (a : ↥(𝕋).AG) (x : ↥(𝕋).G),
          ((a : ↥(𝕋).G))⁻¹ * (x * c * x⁻¹) ∈ V) → c ∈ Ω) ∧
      ∀ g ∈ Ω, ∃ (a : ↥(𝕋).AG) (x : ↥(𝕋).G), ((a : ↥(𝕋).G))⁻¹ * (x * g * x⁻¹) ∈ U := by
  refine ⟨Set.univ, isInvariantClopen_univ _, fun _ _ => trivial, fun g _ =>
    ⟨⟨g, by rw [toyD_AG_eq_top]; trivial⟩, 1, ?_⟩⟩
  simpa using mem_of_mem_nhds hU

end Sanity

end GSpinGGP
