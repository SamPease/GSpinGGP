/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.Representations

/-!
# Audit: `UnitaryRep` as a unitary `ContRepresentation`

`UnitaryRep G` is a Mathlib `ContRepresentation ℂ G H` on a complex Hilbert space `H` that is
unitary (Tau Ceti's `ContRepresentation.IsUnitary`) and strongly continuous. This file checks that
the bundled data are exactly those of a strongly continuous unitary representation given as a
homomorphism `ρ : G →* (H →L[ℂ] H)` into the unitary operators with continuous orbits:

* `UnitaryRepAudit.Data G`: that data, as a structure;
* `UnitaryRepAudit.equivData`: `UnitaryRep G ≃ Data G`, preserving `H` and `ρ` (both directions
  are `rfl`);
* `isIrreducible_iff`, `isEquivalent_iff`: irreducibility and unitary equivalence, read through
  `equivData`, are the same conditions on `(H, ρ)` (`Iff.rfl`);
* `leftRegular_ρ`: the left regular representation acts by
  `Lp.compMeasurePreservingₗᵢ ℂ (g⁻¹ * ·)` (`rfl`), so `WeaklyContainedIn _ (leftRegular G)` and
  `IsTempered` are conditions on the same operators.
-/

open MeasureTheory

namespace GSpinGGP.UnitaryRepAudit

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A strongly continuous unitary representation given by its homomorphism into the unitary
operators of a complex Hilbert space. -/
structure Data (G : Type u) [Group G] [TopologicalSpace G] where
  /-- The Hilbert space. -/
  H : Type u
  [normed : NormedAddCommGroup H]
  [inner : InnerProductSpace ℂ H]
  [complete : CompleteSpace H]
  /-- The action. -/
  ρ : G →* (H →L[ℂ] H)
  /-- Each `ρ g` is unitary. -/
  unitary_ρ : ∀ g, ρ g ∈ unitary (H →L[ℂ] H)
  /-- Strong continuity. -/
  strongCont : ∀ v : H, Continuous fun g => ρ g v

attribute [instance] Data.normed Data.inner Data.complete

/-- `UnitaryRep G` is equivalent to `Data G`. -/
def equivData : UnitaryRep G ≃ Data G where
  toFun π :=
    { H := π.H, ρ := π.ρ, unitary_ρ := π.isUnitary.mem_unitary, strongCont := π.strongCont }
  invFun D := .ofMonoidHom D.H D.ρ D.unitary_ρ D.strongCont
  left_inv _ := rfl
  right_inv _ := rfl

theorem equivData_ρ (π : UnitaryRep G) : (equivData π).ρ = π.ρ := rfl

theorem equivData_symm_ρ (D : Data G) : (equivData.symm D).ρ = D.ρ := rfl

/-- Irreducibility, stated on the data `(H, ρ)`. -/
theorem isIrreducible_iff (π : UnitaryRep G) :
    π.IsIrreducible ↔
      Nontrivial (equivData π).H ∧
        ∀ W : Submodule ℂ (equivData π).H, IsClosed (W : Set (equivData π).H) →
          (∀ g, ∀ v ∈ W, (equivData π).ρ g v ∈ W) → W = ⊥ ∨ W = ⊤ :=
  Iff.rfl

/-- Unitary equivalence, stated on the data `(H, ρ)`. -/
theorem isEquivalent_iff (π π' : UnitaryRep G) :
    π.IsEquivalent π' ↔
      ∃ U : (equivData π).H ≃ₗᵢ[ℂ] (equivData π').H,
        ∀ g v, U ((equivData π).ρ g v) = (equivData π').ρ g (U v) :=
  Iff.rfl

/-- The left regular representation acts by left translation `f ↦ f(g⁻¹ ·)` on `L²(G, haar)`. -/
theorem leftRegular_ρ [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (g : G) :
    (leftRegular G).ρ g =
      (Lp.compMeasurePreservingₗᵢ ℂ (fun x : G => g⁻¹ * x)
        (measurePreserving_mul_left (Measure.haar : Measure G) g⁻¹)).toContinuousLinearMap :=
  rfl

end GSpinGGP.UnitaryRepAudit
