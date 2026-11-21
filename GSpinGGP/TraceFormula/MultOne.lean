/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Basic
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
2. pulled back along the topological isomorphism `GSpin(W) × GSpin(V) → G`, `(a, b) ↦ (a, b)`
   (`GGPData.pair`), `π^∞` is an irreducible admissible representation of the product
   (`isAdmissible_comp_pair`);
3. by Flath's Theorem 1 (`flath_tensor_decomposition`) it is `ρ₀ ⊗ ρ`, and multiplicities are
   invariant under equivalence (`Representation.multiplicity_eq_of_linearEquiv`).
-/

open MeasureTheory Topology

noncomputable section

namespace Representation

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Multiplicities are invariant under an equivariant linear isomorphism. -/
theorem multiplicity_eq_of_linearEquiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : V ≃ₗ[ℂ] W) (he : ∀ g v, e (ρ g v) = σ g (e v)) (S : Subgroup G) (ξ : ↥S → ℂ) :
    multiplicity ρ S ξ = multiplicity σ S ξ := by
  have hmem : ∀ ℓ, ℓ ∈ equivariantForms ρ S ξ ↔ e.symm.dualMap ℓ ∈ equivariantForms σ S ξ := by
    intro ℓ
    change (∀ s : ↥S, ∀ v, ℓ (ρ s v) = ξ s * ℓ v) ↔
      ∀ s : ↥S, ∀ w, ℓ (e.symm (σ s w)) = ξ s * ℓ (e.symm w)
    constructor
    · intro h s w
      have := h s (e.symm w)
      have hs : e.symm (σ s w) = ρ s (e.symm w) := by
        rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
      rwa [hs]
    · intro h s v
      have := h s (e v)
      rwa [← he, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at this
  have h := congrArg Cardinal.toENat (GSpinGGP.equivOfForallMemIff e.symm.dualMap hmem).lift_rank_eq
  rwa [Cardinal.toENat_lift, Cardinal.toENat_lift] at h

end Representation

namespace GSpinGGP

open HarishChandra

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

theorem pair_comp_prod : d.pair.comp (d.fst.prod d.snd) = MonoidHom.id _ :=
  MonoidHom.ext fun g => d.pair_fst_snd g

theorem prod_comp_pair : (d.fst.prod d.snd).comp d.pair = MonoidHom.id _ :=
  MonoidHom.ext fun _ => rfl

theorem surjective_pair : Function.Surjective d.pair := fun g => ⟨_, d.pair_fst_snd g⟩

/-- A representation of `G = GSpin(W) × GSpin(V)` pulled back to the product group: it is admissible
when the original one is (`pair` is a homeomorphism, so compact open subgroups correspond). -/
theorem isAdmissible_comp_pair {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ ↥d.G V} (h : ρ.IsAdmissible) : Representation.IsAdmissible (ρ.comp d.pair) := by
  refine ⟨h.1.comp d.continuous_pair, fun K hKo hKc => ?_⟩
  have hmap : ((K.map d.pair : Subgroup ↥d.G) : Set ↥d.G) =
      (d.fst.prod d.snd) ⁻¹' (K : Set _) := by
    ext g
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hg
      exact ⟨_, hg, d.pair_fst_snd g⟩
  have hco : IsOpen ((K.map d.pair : Subgroup ↥d.G) : Set ↥d.G) := by
    rw [hmap]
    exact hKo.preimage (d.continuous_fst.prodMk d.continuous_snd)
  have hcc : IsCompact ((K.map d.pair : Subgroup ↥d.G) : Set ↥d.G) := by
    rw [Subgroup.coe_map]
    exact hKc.image d.continuous_pair
  have := h.2 _ hco hcc
  have heq : Representation.invariants ((ρ.comp d.pair).comp K.subtype) =
      Representation.invariants (ρ.comp (K.map d.pair).subtype) := by
    ext v
    rw [Representation.mem_invariants, Representation.mem_invariants]
    constructor
    · intro h' g
      obtain ⟨p, hp, hpg⟩ := Subgroup.mem_map.1 g.property
      change ρ (g : ↥d.G) v = v
      rw [← hpg]
      exact h' ⟨p, hp⟩
    · intro h' p
      exact h' ⟨d.pair p, Subgroup.mem_map_of_mem _ p.2⟩
  rw [heq]
  exact this

end GGPData

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
  have hadm' := d.isAdmissible_comp_pair hadm
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
  rw [hcomp, Representation.multiplicity_eq_of_linearEquiv
    (σ := (ρ₀.externalTensor ρ).comp (d.fst.prod d.snd)) e.toLinearEquiv
    (fun g v => LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' ((d.fst.prod d.snd) g)) v)]
  exact panYan_mult_le_one d ψ ρ₀ ρ h₀ h₀' h₁ h₁'

end GSpinGGP
