/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.HarishChandra
import GSpinGGP.Literature.SmoothRepresentations
import GSpinGGP.Foundations.VanDantzig

/-!
# Characters of irreducible unitary representations

The character theorems of Harish-Chandra and Beuzart-Plessis are cited for irreducible admissible
smooth representations (`hc_character_exists_admissible`,
`hc_character_isQuasiCharacter_admissible`). This file derives the forms used by the proof, for an
irreducible tempered unitary representation `π` of `G(F)`, through its smooth part `π^∞`:

* `smoothRep_isIrreducible_isAdmissible`: `π^∞` is irreducible and admissible (Cartier's
  Corollary 2.3 gives density and admissibility; irreducibility is `isIrreducible_smoothRep`);
  stated for `F : Type*`, like `emoryTakeda_mult_le_one`;
* `hc_character_exists` (`F : Type`, as the cited axioms of `Literature/HarishChandra`): `θ_π` exists and is continuous on `G' = {D ≠ 0}`;
* `hc_character_isQuasiCharacter`: `θ_π` is a quasi-character.

The characters of `π^∞` and `π` coincide (`isCharacterOf_smoothRep`, `characterOn_smoothRep`).
-/

open MeasureTheory Topology

noncomputable section

namespace GSpinGGP

open HarishChandra

section Smooth

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- The smooth vectors of a nonzero unitary representation are nonzero when they are dense. -/
theorem smoothVectors_ne_bot_of_dense {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {π : UnitaryRep G} [Nontrivial π.H]
    (hdense : Dense (smoothVectors π : Set π.H)) : smoothVectors π ≠ ⊥ := by
  intro h0
  obtain ⟨x, hx⟩ := exists_ne (0 : π.H)
  have : x ∈ closure (smoothVectors π : Set π.H) := hdense x
  rw [h0, Submodule.bot_coe, closure_singleton] at this
  exact hx this

/-- **`π^∞` is irreducible and admissible** for every irreducible unitary representation `π` of
`G(F)`: Cartier's Corollary 2.3 (density and admissibility) and `isIrreducible_smoothRep`, with
van Dantzig's theorem for `G(F)` (`exists_compactOpenSubgroup_subset`). -/
theorem smoothRep_isIrreducible_isAdmissible (d : GGPData F) {π : UnitaryRep ↥d.G}
    (hπ : π.IsIrreducible) : (smoothRep π).IsIrreducible ∧ (smoothRep π).IsAdmissible := by
  obtain ⟨hdense, hadm⟩ := cartier_smoothVectors_dense_admissible d π hπ
  have := subgroup_t2Space F d.ambient d.G
  have := subgroup_locallyCompactSpace_of_isClosed F d.ambient d.G d.isClosed_G
  have := totallyDisconnectedSpace_subgroup F d.ambient d.G
  have := hπ.1
  refine ⟨isIrreducible_smoothRep exists_compactOpenSubgroup_subset hπ
    (smoothVectors_ne_bot_of_dense hdense) fun K hKo hKc => ?_, hadm⟩
  have := hadm.2 K hKo hKc
  exact (invariantsSmoothEquiv π hKo).finiteDimensional

end Smooth

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **(b) for unitary representations.** For an irreducible tempered representation `π` of `G(F)`,
the character `θ_π` exists and is continuous on Harish-Chandra's `G' = {D ≠ 0}`: Harish-Chandra's
theorem (`hc_character_exists_admissible`) applied to the irreducible admissible `π^∞`, whose
character is that of `π`. -/
theorem hc_character_exists (d : GGPData F) (π : UnitaryRep ↥d.G) (hπ : IsTempered π) :
    ∃ θ : ↥d.G → ℂ, IsCharacterOf π θ ∧ ContinuousOn θ {x : ↥d.G | hcDisc d x ≠ 0} := by
  obtain ⟨hirr, hadm⟩ := smoothRep_isIrreducible_isAdmissible d hπ.1
  rw [← isCharacterOf_smoothRep]
  exact hc_character_exists_admissible d (smoothRep π) hirr hadm

/-- **(c) for unitary representations.** For `π` irreducible tempered, `θ_π` is a quasi-character
(`hc_character_isQuasiCharacter_admissible` applied to `π^∞`). -/
theorem hc_character_isQuasiCharacter (d : GGPData F) (ψ : NontrivialAddChar F)
    (π : UnitaryRep ↥d.G) (hπ : IsTempered π) :
    IsQuasiCharacter d.G d.lie d.bilin ψ (characterOn π (regularSet d.G d.lie)) := by
  obtain ⟨hirr, hadm⟩ := smoothRep_isIrreducible_isAdmissible d hπ.1
  rw [← characterOn_smoothRep]
  exact hc_character_isQuasiCharacter_admissible d ψ (smoothRep π) hirr hadm

end GSpinGGP
