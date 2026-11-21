/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Sanity.AxiomRedTeam.HarishChandra
import GSpinGGP.TraceFormula.MultOne

/-!
# Checks of the axioms on smooth admissible representations

Each conclusion is verified *without* the axiom, for the trivial representation (on `toyD` for the
axioms about `G(F)`, on an arbitrary product of groups for Flath's theorem); the hypotheses are
shown to hold there, so the checks are not vacuous.

* `cartier_smoothVectors_dense_admissible`: for `π = 1` on `toyD`, `π^∞ = π` is dense and admissible
  (`toyD_cartier_check`).
* `hc_character_exists_admissible`, `hc_character_isQuasiCharacter_admissible`: for `ρ = 1^∞` on
  `toyD`, which is irreducible and admissible (`toyD_smoothRep_trivial_irr_adm`), `θ_ρ = 1` is a
  quasi-character (`toyD_hc_character_exists_admissible_check`,
  `toyD_hc_isQuasiCharacter_admissible_check`).
* `panYan_mult_le_one`: for `ρ₀ = 1`, `ρ = 1`, the multiplicity is at most `1`
  (`toyD_panYan_check`); the hypotheses hold (`trivial_isIrreducible`, `trivial_isAdmissible`).
* `flath_tensor_decomposition`: the trivial representation of any `G₁ × G₂` is `1 ⊗ 1`
  (`flath_trivial_check`).

Not covered: infinite-dimensional representations (none can be built here without the axioms).
-/

open MeasureTheory Topology GSpinGGP GSpinGGP.Sanity
open scoped TensorProduct

noncomputable section

namespace GSpinGGP.AxiomRedTeam

set_option linter.unusedSectionVars false

section General

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The trivial representation on `ℂ` is irreducible (a line). -/
theorem trivial_isIrreducible : (Representation.trivial ℂ G ℂ).IsIrreducible :=
  Representation.isIrreducible_of_finrank_eq_one _ (Module.finrank_self ℂ)

/-- The trivial representation on `ℂ` is admissible. -/
theorem trivial_isAdmissible : (Representation.trivial ℂ G ℂ).IsAdmissible :=
  ⟨inferInstance, fun _ _ _ => inferInstance⟩

/-- **Flath's conclusion for the trivial representation** of a product: it is `1 ⊗ 1`. -/
theorem flath_trivial_check {G₁ G₂ : Type*} [Group G₁] [TopologicalSpace G₁] [Group G₂]
    [TopologicalSpace G₂] :
    ∃ (V₁ V₂ : Type) (_ : AddCommGroup V₁) (_ : Module ℂ V₁) (_ : AddCommGroup V₂)
      (_ : Module ℂ V₂) (ρ₁ : Representation ℂ G₁ V₁) (ρ₂ : Representation ℂ G₂ V₂),
      ρ₁.IsIrreducible ∧ ρ₁.IsAdmissible ∧ ρ₂.IsIrreducible ∧ ρ₂.IsAdmissible ∧
        Nonempty (Representation.Equiv (Representation.trivial ℂ (G₁ × G₂) ℂ)
          (ρ₁.externalTensor ρ₂)) :=
  ⟨ℂ, ℂ, _, _, _, _, Representation.trivial ℂ G₁ ℂ, Representation.trivial ℂ G₂ ℂ,
    trivial_isIrreducible, trivial_isAdmissible, trivial_isIrreducible, trivial_isAdmissible,
    ⟨(Representation.externalTensorLid (σ := Representation.trivial ℂ G₂ ℂ)).symm⟩⟩

end General

section Toy

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝕋" => (toyD (F := F))

theorem smoothVectors_trivialRep_eq_top (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : smoothVectors (trivialRep G) = ⊤ :=
  eq_top_iff.2 fun _ _ => (mem_smoothVectors_iff _).2 ⟨⊤, isOpen_univ, fun _ _ => rfl⟩

/-- **Cartier's conclusion for `π = 1` on `toyD`**: `π^∞` is dense and admissible. -/
theorem toyD_cartier_check :
    Dense (smoothVectors (trivialRep ↥(𝕋).G) : Set (trivialRep ↥(𝕋).G).H) ∧
      (smoothRep (trivialRep ↥(𝕋).G)).IsAdmissible := by
  have : FiniteDimensional ℂ (trivialRep ↥(𝕋).G).H := inferInstanceAs (FiniteDimensional ℂ ℂ)
  refine ⟨?_, (inferInstance : Representation.IsSmooth
    (trivialRep ↥(𝕋).G).toRepresentation.smoothVectors.toRepresentation), fun _ _ _ => inferInstance⟩
  rw [smoothVectors_trivialRep_eq_top, Submodule.top_coe]
  exact dense_univ

/-- `1^∞` on `toyD` is irreducible and admissible (without Cartier's axiom). -/
theorem toyD_smoothRep_trivial_irr_adm :
    (smoothRep (trivialRep ↥(𝕋).G)).IsIrreducible ∧
      (smoothRep (trivialRep ↥(𝕋).G)).IsAdmissible := by
  refine ⟨Representation.isIrreducible_of_finrank_eq_one _ ?_, toyD_cartier_check.2⟩
  rw [smoothVectors_trivialRep_eq_top, finrank_top]
  exact Module.finrank_self ℂ

/-- **Conclusion of `hc_character_exists_admissible` for `(toyD, 1^∞)`**. -/
theorem toyD_hc_character_exists_admissible_check :
    ∃ θ : ↥(𝕋).G → ℂ, (smoothRep (trivialRep ↥(𝕋).G)).IsCharacterOf θ ∧
      ContinuousOn θ {x : ↥(𝕋).G | hcDisc (𝕋) x ≠ 0} := by
  rw [isCharacterOf_smoothRep]
  exact toyD_hc_character_exists_check

/-- **Conclusion of `hc_character_isQuasiCharacter_admissible` for `(toyD, 1^∞)`**. -/
theorem toyD_hc_isQuasiCharacter_admissible_check (ψ : NontrivialAddChar F) :
    IsQuasiCharacter (𝕋).G (𝕋).lie (𝕋).bilin ψ
      ((smoothRep (trivialRep ↥(𝕋).G)).characterOn (regularSet (𝕋).G (𝕋).lie)) := by
  rw [characterOn_smoothRep]
  exact toyD_hc_isQuasiCharacter_check ψ

/-- **Conclusion of `panYan_mult_le_one` for `ρ₀ = 1`, `ρ = 1` on `toyD`**: `ℂ ⊗ ℂ` is a line, so
its dual has dimension `1`. -/
theorem toyD_panYan_check (ψ : NontrivialAddChar F) :
    Representation.multiplicity (((Representation.trivial ℂ (GSpin (𝕋).QW) ℂ).externalTensor
      (Representation.trivial ℂ (GSpin (𝕋).QV) ℂ)).comp ((𝕋).fst.prod (𝕋).snd)) (𝕋).H
      ((𝕋).xi ψ.toAddChar) ≤ 1 := by
  have h1 : Module.finrank ℂ (ℂ ⊗[ℂ] ℂ) = 1 := by
    rw [Module.finrank_tensorProduct, Module.finrank_self, mul_one]
  have hD : Module.finrank ℂ (Module.Dual ℂ (ℂ ⊗[ℂ] ℂ)) ≤ 1 := by
    rw [Subspace.dual_finrank_eq, h1]
  have hE : Module.rank ℂ ↥(Representation.equivariantForms (((Representation.trivial ℂ
      (GSpin (𝕋).QW) ℂ).externalTensor (Representation.trivial ℂ (GSpin (𝕋).QV) ℂ)).comp
      ((𝕋).fst.prod (𝕋).snd)) (𝕋).H ((𝕋).xi ψ.toAddChar)) ≤ 1 := by
    refine (Submodule.rank_le _).trans ?_
    rw [← Module.finrank_eq_rank]
    exact_mod_cast hD
  unfold Representation.multiplicity
  calc Cardinal.toENat (Module.rank ℂ _) ≤ Cardinal.toENat 1 := Cardinal.toENat.monotone' hE
    _ = 1 := by simp

/-- The axiom's instance at `toyD` for `ρ₀ = ρ = 1` (agrees with `toyD_panYan_check`). -/
example (ψ : NontrivialAddChar F) :
    Representation.multiplicity (((Representation.trivial ℂ (GSpin (𝕋).QW) ℂ).externalTensor
      (Representation.trivial ℂ (GSpin (𝕋).QV) ℂ)).comp ((𝕋).fst.prod (𝕋).snd)) (𝕋).H
      ((𝕋).xi ψ.toAddChar) ≤ 1 :=
  panYan_mult_le_one (𝕋) ψ _ _ trivial_isIrreducible trivial_isAdmissible trivial_isIrreducible
    trivial_isAdmissible

end Toy

end GSpinGGP.AxiomRedTeam
