/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.Representations
import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Basic

/-!
# Schur's lemma for irreducible unitary representations

For a strongly continuous unitary representation `π` whose only closed `π(G)`-stable subspaces
are `0` and `H`, every bounded operator commuting with `π(G)` is a scalar (Dixmier, *Les
C\*-algèbres et leurs représentations*, 13.1.4 (i) ⇒ (ii); the same for involutive algebras is
2.3.1).

The proof uses the spectral theorem for bounded normal operators (Tau Ceti's Borel functional
calculus). If `T` commutes with `π(G)`, so does `T*`, because `π(g)* = π(g⁻¹)`; hence so do the
real and imaginary parts of `T`. Every operator commuting with a normal operator `A` commutes
with all its spectral projections (`ContinuousLinearMap.forall_commute_spectralPVM_proj_iff`), so
the range of each spectral projection of `A` is a closed `π(G)`-stable subspace, and each spectral
projection is `0` or `1`. Two points of the spectrum would have disjoint open neighbourhoods with
nonzero, hence identity, spectral projections whose product is `0`; so the spectrum of `A` is a
single point, and `A` is a scalar.

## Main results

* `ContinuousLinearMap.IsIdempotentElem.eq_zero_or_eq_one_of_forall_commute`: an idempotent
  commuting with an irreducible family of operators is `0` or `1`.
* `ContinuousLinearMap.exists_eq_smul_one_of_isStarNormal_of_forall_commute`: a normal operator
  commuting with an irreducible family of operators is a scalar.
* `UnitaryRep.star_ρ`: `π(g)* = π(g⁻¹)`.
* `dixmier_commutant_scalar`: Schur's lemma for irreducible unitary representations.
* `schur_central`: the centre acts by scalars.
-/

open scoped ComplexStarModule

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} {S : ι → H →L[ℂ] H}

omit [CompleteSpace H] in
/-- An idempotent operator commuting with a family `S` of operators whose only closed common
invariant subspaces are `⊥` and `⊤` is `0` or `1`: its range is closed and `S`-stable. -/
theorem IsIdempotentElem.eq_zero_or_eq_one_of_forall_commute {P : H →L[ℂ] H}
    (hP : IsIdempotentElem P) (hS : ∀ W : Submodule ℂ H, IsClosed (W : Set H) →
      (∀ i, ∀ v ∈ W, S i v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hc : ∀ i, Commute P (S i)) : P = 0 ∨ P = 1 := by
  refine (hS P.range (IsIdempotentElem.isClosed_range hP)
    fun i v hv => ((IsIdempotentElem.commute_iff hP).1 (hc i)).1 hv).imp
    (fun h => coe_injective (by simpa using LinearMap.range_eq_bot.1 h)) fun h => ?_
  ext v
  exact (LinearMap.IsIdempotentElem.mem_range_iff (IsIdempotentElem.toLinearMap hP)).1
    (h ▸ Submodule.mem_top)

/-- A normal operator commuting with a family `S` of operators on a nonzero Hilbert space whose
only closed common invariant subspaces are `⊥` and `⊤` is a scalar: its spectral projections are
`0` or `1`, so its spectrum is a point. -/
theorem exists_eq_smul_one_of_isStarNormal_of_forall_commute [Nontrivial H]
    (hS : ∀ W : Submodule ℂ H, IsClosed (W : Set H) →
      (∀ i, ∀ v ∈ W, S i v ∈ W) → W = ⊥ ∨ W = ⊤)
    (A : H →L[ℂ] H) [IsStarNormal A] (hA : ∀ i, Commute A (S i)) :
    ∃ c : ℂ, A = c • (1 : H →L[ℂ] H) := by
  have hproj : ∀ B hB, A.spectralPVM.proj B hB = 0 ∨ A.spectralPVM.proj B hB = 1 :=
    fun B hB => IsIdempotentElem.eq_zero_or_eq_one_of_forall_commute
      (A.spectralPVM.proj_idem B hB) hS fun i =>
        (((A.forall_commute_spectralPVM_proj_iff (S i)).2 (hA i).symm) B hB).symm
  obtain ⟨z, hz⟩ := spectrum.nonempty A
  have hsub : spectrum ℂ A ⊆ {z} := by
    intro w hw
    by_contra hne
    have hzw : (⟨z, hz⟩ : spectrum ℂ A) ≠ ⟨w, hw⟩ := fun h =>
      hne (congrArg Subtype.val h).symm
    obtain ⟨U, V, hU, hV, hzU, hwV, hUV⟩ := t2_separation hzw
    have h1 : ∀ {T : Set (spectrum ℂ A)} (hT : IsOpen T), T.Nonempty →
        A.spectralPVM.proj T hT.measurableSet = 1 := fun hT hne =>
      (hproj _ _).resolve_left (A.spectralPVM_proj_ne_zero hT hne)
    have h0 := A.spectralPVM.proj_mul_eq_zero_of_disjoint hU.measurableSet hV.measurableSet hUV
    rw [h1 hU ⟨_, hzU⟩, h1 hV ⟨_, hwV⟩, one_mul] at h0
    exact one_ne_zero h0
  exact ⟨z, (CFC.eq_algebraMap_of_spectrum_subset_singleton A z hsub).trans
    (Algebra.algebraMap_eq_smul_one z)⟩

end ContinuousLinearMap

namespace GSpinGGP

namespace UnitaryRep

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- `π(g)* = π(g⁻¹)`. -/
theorem star_ρ (π : UnitaryRep G) (g : G) : star (π.ρ g) = π.ρ g⁻¹ :=
  left_inv_eq_right_inv (Unitary.star_mul_self_of_mem (π.unitary_ρ g))
    (by rw [← map_mul, mul_inv_cancel, map_one])

end UnitaryRep

/-- **Schur's lemma for unitary representations** (Dixmier, *Les C\*-algèbres et leurs
représentations*, Gauthier-Villars 1964, 13.1.4, p. 250, (i) ⇒ (ii); the same for involutive
algebras is 2.3.1): for a continuous unitary representation `π` of a topological group `G` whose
only closed `π(G)`-stable subspaces are `0` and `H`, the commutant of `π(G)` in `L(H)` consists of
the scalars. Proved from the spectral theorem (see the module docstring); continuity of `π` is not
used. -/
theorem dixmier_commutant_scalar {G : Type*} [Group G] [TopologicalSpace G] (π : UnitaryRep G)
    (hπ : π.IsIrreducible) (T : π.H →L[ℂ] π.H) (hT : ∀ g, T * π.ρ g = π.ρ g * T) :
    ∃ c : ℂ, T = c • (1 : π.H →L[ℂ] π.H) := by
  have : Nontrivial π.H := hπ.1
  have hT' : ∀ g, Commute T (π.ρ g) := hT
  -- `T*` commutes with `π(G)`, since `π(g)* = π(g⁻¹)`
  have hTs : ∀ g, Commute (star T) (π.ρ g) := fun g => by
    have h := (hT' g⁻¹).star_star
    rwa [π.star_ρ, inv_inv] at h
  have hre : ∀ g, Commute (ℜ T : π.H →L[ℂ] π.H) (π.ρ g) := fun g => by
    rw [realPart_apply_coe]
    exact ((hT' g).add_left (hTs g)).smul_left _
  have him : ∀ g, Commute (ℑ T : π.H →L[ℂ] π.H) (π.ρ g) := fun g => by
    rw [imaginaryPart_apply_coe]
    exact (((hT' g).sub_left (hTs g)).smul_left _).smul_left _
  have : IsStarNormal (ℜ T : π.H →L[ℂ] π.H) := (ℜ T).property.isStarNormal
  have : IsStarNormal (ℑ T : π.H →L[ℂ] π.H) := (ℑ T).property.isStarNormal
  obtain ⟨a, ha⟩ :=
    ContinuousLinearMap.exists_eq_smul_one_of_isStarNormal_of_forall_commute hπ.2 _ hre
  obtain ⟨b, hb⟩ :=
    ContinuousLinearMap.exists_eq_smul_one_of_isStarNormal_of_forall_commute hπ.2 _ him
  refine ⟨a + Complex.I * b, ?_⟩
  rw [← realPart_add_I_smul_imaginaryPart T, ha, hb, smul_smul, add_smul]

/-- **The centre acts by scalars** in an irreducible unitary representation (used for the central
character of tempered representations, Thesis §3.1.2): `π(z)` commutes with `π(G)` for `z` central,
so it is a scalar by `dixmier_commutant_scalar`. -/
theorem schur_central {G : Type*} [Group G] [TopologicalSpace G] (π : UnitaryRep G)
    (hπ : π.IsIrreducible) :
    ∃ χ : ↥(Subgroup.center G) → ℂ, HasCentralChar π (Subgroup.center G) χ := by
  choose χ hχ using fun z : ↥(Subgroup.center G) =>
    dixmier_commutant_scalar π hπ (π.ρ z) fun g => by
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 z.property g).symm]
  exact ⟨χ, hχ⟩

end GSpinGGP
