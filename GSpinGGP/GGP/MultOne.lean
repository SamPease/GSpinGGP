/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.RepresentationTheory.Intertwining
import GSpinGGP.Literature.GSpin
import GSpinGGP.GGP.UnitaryCharacters

/-!
# Multiplicity at most one for tempered unitary representations

`emoryTakeda_mult_le_one`: `m(π) ≤ 1` for every irreducible tempered unitary representation `π` of
`G(F) = GSpin(W) × GSpin(V)` (Thesis Thm 5.5.1). The cited result, Pan Yan's Theorem 1.1
(`panYan_mult_le_one`), is about `ρ₀ ⊗ ρ` for irreducible admissible representations `ρ₀` of
`GSpin(W)` and `ρ` of `GSpin(V)`. The steps:

1. `π^∞` is irreducible admissible (`smoothRep_isIrreducible_isAdmissible`), and
   `m(π) = dim Hom_H(π^∞, ξ)` by definition (`multiplicity_smoothRep`);
2. pulled back along the isomorphism of topological groups `GSpin(W) × GSpin(V) ≃ₜ* G`
   (`GGPData.pairEquiv`), `π^∞` is an irreducible admissible representation of the product
   (`Representation.IsAdmissible.comp_continuousMulEquiv`);
3. by Flath's Theorem 1 (`flath_tensor_decomposition`) it is `ρ₀ ⊗ ρ`, and multiplicities are
   invariant under equivalence (`Representation.multiplicity_eq_of_equiv`).

`F : Type*`, as when `emoryTakeda_mult_le_one` was an axiom.
-/

open MeasureTheory Topology

noncomputable section


namespace GSpinGGP

open HarishChandra

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]


/-- **Multiplicity at most one** (Thesis Thm. 5.5.1). For every GGP datum `d`, nontrivial additive
character `ψ`, and irreducible tempered unitary representation `π` of `G(F)`,
`m(π) = dim Hom_{H(F)}(π^∞, ξ) ≤ 1`. From Pan Yan's Theorem 1.1 (`panYan_mult_le_one`), with
Cartier's Corollary 2.3 and Flath's Theorem 1 (see the module docstring). -/
theorem emoryTakeda_mult_le_one (d : GGPData F) (ψ : NontrivialAddChar F) (π : UnitaryRep ↥d.G) :
    haveI := subgroup_isTopologicalGroup F d.ambient d.G
    haveI := subgroup_t2Space F d.ambient d.G
    haveI := subgroup_locallyCompactSpace_of_isClosed F d.ambient d.G d.isClosed_G
    IsTempered π → multiplicity π d.H (d.xi ψ.toAddChar) ≤ 1 := by
  intro hπ
  obtain ⟨hirr, hadm⟩ := smoothRep_isIrreducible_isAdmissible d hπ.1
  have hirr' : Representation.IsIrreducible ((smoothRep π).comp d.pair) :=
    (d.pair.isIrreducible_comp_surjective_iff d.surjective_pair _).2 hirr
  have hadm' : Representation.IsAdmissible ((smoothRep π).comp d.pair) :=
    hadm.comp_continuousMulEquiv d.pairEquiv
  have := subgroup_isTopologicalGroup F (CliffordAlgebra d.QW) (GSpin d.QW)
  have := subgroup_isTopologicalGroup F (CliffordAlgebra d.QV) (GSpin d.QV)
  have := subgroup_locallyCompactSpace_of_isClosed F _ _ (isClosed_GSpin d.QW)
  have := subgroup_locallyCompactSpace_of_isClosed F _ _ (isClosed_GSpin d.QV)
  have := totallyDisconnectedSpace_subgroup F (CliffordAlgebra d.QW) (GSpin d.QW)
  have := totallyDisconnectedSpace_subgroup F (CliffordAlgebra d.QV) (GSpin d.QV)
  obtain ⟨V₁, V₂, _, _, _, _, ρ₀, ρ, h₀, h₀', h₁, h₁', ⟨e⟩⟩ :=
    flath_tensor_decomposition _ hirr' hadm'
  rw [← multiplicity_smoothRep]
  have hcomp : (smoothRep π) = ((smoothRep π).comp d.pair).comp (d.fst.prod d.snd) := by
    rw [MonoidHom.comp_assoc, d.pair_comp_prod, MonoidHom.comp_id]
  rw [hcomp, Representation.multiplicity_eq_of_equiv (e.res (d.fst.prod d.snd))]
  exact panYan_mult_le_one d ψ ρ₀ ρ h₀ h₀' h₁ h₁'

end GSpinGGP
