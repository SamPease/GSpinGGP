import GSpinGGP.Foundations.LocalGroups

/-!
# A `p`-adic field is a nonarchimedean local field

`PAdicField F` (Thesis §2.1) is stated analytically: a complete, locally compact, ultrametric,
nontrivially normed field of characteristic zero. Mathlib's `IsNonarchimedeanLocalField` (used by
the local-field results of Mathlib and Tau Ceti) is stated for a field with a valuative relation
and a compatible topology. This file connects the two: the norm defines a valuative relation
(`normValuativeRel`), whose valuative topology is the norm topology, and with it every
`PAdicField` is an `IsNonarchimedeanLocalField`.

`normValuativeRel` is a definition, not a global instance, because particular fields (such as
`ℚ_[p]`) carry their own valuative relation; the two agree as relations but not definitionally.
Use it as a local instance.
-/

noncomputable section

open ValuativeRel

namespace GSpinGGP

variable (F : Type*) [NontriviallyNormedField F] [IsUltrametricDist F]

/-- The valuative relation of an ultrametric norm: `x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖`. -/
abbrev normValuativeRel : ValuativeRel F :=
  .ofValuation (NormedField.valuation (K := F))

namespace NormValuativeRel

attribute [local instance] normValuativeRel

instance : (NormedField.valuation (K := F)).Compatible := .ofValuation _

/-- The valuative topology of the norm's valuative relation is the norm topology. -/
theorem isValuativeTopology : IsValuativeTopology F :=
  IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := F))
    (fun {s} => (NormedField.toValued (K := F)).is_topological_valuation s)

theorem isNontrivial : ValuativeRel.IsNontrivial F where
  condition := by
    obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm F
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx; linarith
    refine ⟨ValuativeRel.valuation F x, ?_, ?_⟩
    · simpa [(isEquiv (ValuativeRel.valuation F) (NormedField.valuation (K := F))).eq_zero]
        using hx0
    · rw [Ne,
        (isEquiv (ValuativeRel.valuation F) (NormedField.valuation (K := F))).eq_one_iff_eq_one]
      intro h
      have : ‖x‖ = 1 := by simpa [← NNReal.coe_inj] using h
      linarith

/-- **A `p`-adic field is a nonarchimedean local field**, for the valuative relation of its
norm. -/
theorem isNonarchimedeanLocalField [PAdicField F] : IsNonarchimedeanLocalField F :=
  have := isValuativeTopology F
  have := isNontrivial F
  ⟨⟩

end NormValuativeRel

end GSpinGGP
