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
* `hc_character_exists`: `θ_π` exists and is continuous on `G' = {D ≠ 0}`;
* `hc_character_isQuasiCharacter`: `θ_π` is a quasi-character.

The characters of `π^∞` and `π` coincide (`isCharacterOf_smoothRep`, `characterOn_smoothRep`).
-/

open MeasureTheory Topology

noncomputable section

namespace GSpinGGP

open HarishChandra

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- Compact open subgroups form a basis of neighbourhoods of `1` in `G(F)` (van Dantzig). -/
theorem GGPData.exists_compactOpen_subgroup_le (d : GGPData F) :
    ∀ U ∈ 𝓝 (1 : ↥d.G), ∃ K : Subgroup ↥d.G,
      IsOpen (K : Set ↥d.G) ∧ IsCompact (K : Set ↥d.G) ∧ (K : Set ↥d.G) ⊆ U := by
  have := totallyDisconnectedSpace_subgroup F d.ambient d.G
  intro U hU
  obtain ⟨K, hKc, hKU⟩ :=
    NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup.mem_iff.1 hU
  exact ⟨K, K.isOpen, hKc, hKU⟩

/-- **`π^∞` is irreducible and admissible** for every irreducible unitary representation `π` of
`G(F)`: Cartier's Corollary 2.3 (density and admissibility) and `isIrreducible_smoothRep`. -/
theorem smoothRep_isIrreducible_isAdmissible (d : GGPData F) {π : UnitaryRep ↥d.G}
    (hπ : π.IsIrreducible) : (smoothRep π).IsIrreducible ∧ (smoothRep π).IsAdmissible := by
  obtain ⟨hdense, hadm⟩ := cartier_smoothVectors_dense_admissible d π hπ
  refine ⟨isIrreducible_smoothRep d.exists_compactOpen_subgroup_le hπ hdense fun K hKo hKc => ?_,
    hadm⟩
  have := hadm.2 K hKo hKc
  exact (invariantsSmoothEquiv π hKo).finiteDimensional

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
