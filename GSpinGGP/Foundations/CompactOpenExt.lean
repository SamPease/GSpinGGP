/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.VanDantzig

/-!
# Measures on totally disconnected spaces are determined by compact open sets

In a locally compact, second countable, totally disconnected Hausdorff space `X` (for example the
`F`-points of a `p`-adic group), the compact open sets form a topological basis
(`isTopologicalBasis_isCompact_isOpen`) and a π-system (`isPiSystem_isCompact_isOpen`), so they
generate the Borel σ-algebra; `X` is covered by countably many of them.  Hence two Borel measures
that agree on compact open sets, and are finite there, are equal
(`measure_ext_of_isCompact_isOpen`; the π–λ theorem, Mathlib's
`MeasureTheory.ext_of_generateFrom_of_iUnion`).

This is how an identity `∫ f dν = ∫ f dμ` known for the locally constant compactly supported
functions `f = 1_U` extends to every integrable `f`.
-/

open MeasureTheory Topology Set

namespace GSpinGGP

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]

/-- In a locally compact, totally disconnected Hausdorff space the compact open sets form a
topological basis (`exists_isCompact_isClopen_between`). -/
theorem isTopologicalBasis_isCompact_isOpen :
    TopologicalSpace.IsTopologicalBasis {U : Set X | IsCompact U ∧ IsOpen U} := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun U hU => hU.2) ?_
  intro x V hx hV
  obtain ⟨U, hUc, hUo, hxU, hUV⟩ :=
    exists_isCompact_isClopen_between isCompact_singleton hV (singleton_subset_iff.2 hx)
  exact ⟨U, ⟨hUc, hUo.isOpen⟩, singleton_subset_iff.1 hxU, hUV⟩

/-- In a Hausdorff space the compact open sets form a π-system. -/
theorem isPiSystem_isCompact_isOpen {Y : Type*} [TopologicalSpace Y] [T2Space Y] :
    IsPiSystem {U : Set Y | IsCompact U ∧ IsOpen U} :=
  fun _ hU _ hV _ => ⟨hU.1.inter_right hV.1.isClosed, hU.2.inter hV.2⟩

variable [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

/-- **Two measures that agree on compact open sets, and are finite there, are equal**, on a
locally compact, second countable, totally disconnected Hausdorff space. -/
theorem measure_ext_of_isCompact_isOpen {μ ν : Measure X}
    (hfin : ∀ U : Set X, IsCompact U → IsOpen U → μ U ≠ ⊤)
    (h : ∀ U : Set X, IsCompact U → IsOpen U → μ U = ν U) : μ = ν := by
  have hgen : (‹MeasurableSpace X›) = MeasurableSpace.generateFrom
      {U : Set X | IsCompact U ∧ IsOpen U} := by
    rw [BorelSpace.measurable_eq (α := X)]
    exact isTopologicalBasis_isCompact_isOpen.borel_eq_generateFrom
  have hB : ∀ n, ∃ B : Set X, IsCompact B ∧ IsOpen B ∧ compactCovering X n ⊆ B := fun n => by
    obtain ⟨B, hBc, hBo, hKB, -⟩ := exists_isCompact_isClopen_between
      (isCompact_compactCovering X n) isOpen_univ (subset_univ _)
    exact ⟨B, hBc, hBo.isOpen, hKB⟩
  choose B hBc hBo hKB using hB
  refine MeasureTheory.Measure.ext_of_generateFrom_of_iUnion _ B hgen isPiSystem_isCompact_isOpen ?_
    (fun n => ⟨hBc n, hBo n⟩) (fun n => hfin _ (hBc n) (hBo n)) (fun U hU => h U hU.1 hU.2)
  exact eq_univ_of_subset (iUnion_mono hKB) (iUnion_compactCovering X)

end GSpinGGP
