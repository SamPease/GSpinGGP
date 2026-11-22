/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.Unramified
import GSpinGGP.Sanity.Witnesses

/-!
# Sanity checks for unramified characters and twists (`GGP/Unramified.lean`)

For every reduced Levi datum `L` (so `a_M ≠ 0`: `Coord` always has the two `GSpin`-coordinates),
take the central element `m = (c, 1)`, `0 < ‖c‖ < 1`, of `M(F)`.  Its `H_M` has
`GSpin(W)`-coordinate `2^{dim W} log ‖c‖ ≠ 0` (`detChar` is `c ↦ c^{dim C(W)}` on scalars).

1. **Unramified characters are not all trivial** (`exists_unitaryUnramChar_apply_eq_exp_pi`,
   `exists_unitaryUnramChar_ne_one`): `ν` the
   coordinate vector with value `π / (2^{dim W} log ‖c‖)` gives `χ_{iν}(m) = e^{iπ} = −1`; so
   `𝒜^∨_{M,F} ≠ a*_M` and `i a*_{M,F}` is not a point (`dualLattice_ne_top`).
2. **The unitarity criterion is not vacuous** (`exists_unramChar_not_unitary`): for real
   `λ ≠ 0` on that coordinate, `|χ_λ(m)| ≠ 1`.
3. **Twisting changes the representation** (`unramTwist_ρ_ne`): on any nonzero vector,
   `σ_{iν}(m) v = −σ(m) v ≠ σ(m) v`.
4. **The stabilizer is not everything** (`twistStab_trivialRep`, `twistStab_trivialRep_ne_top`):
   for the trivial representation on `ℂ` (`Sanity.trivialRep`), `i a^∨_{M,σ} = 𝒜^∨_{M,F} ≠ a*_M`.
5. **`i a*_{M,F}` is a genuine torus** (`dualLattice_ne_bot_ne_top`): `0 ≠ 𝒜^∨_{M,F} ≠ a*_M`,
   and the unitarity criterion `Re λ = 0` rejects the real `λ` above
   (`not_re_eq_zero_of_not_unitary`).
-/

noncomputable section

open Module
open scoped Real

namespace GSpinGGP

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] {d : GGPData F}

namespace ReducedLeviDatum

variable (L : d.ReducedLeviDatum)

/-- The `GSpin(W)`-coordinate of `a_M`. -/
private abbrev cW : L.Coord := Sum.inl (Sum.inr ())

/-- A central element `(c, 1)` of `M(F)` with `H_M` nonzero on the `GSpin(W)`-coordinate. -/
theorem exists_HM_cW_ne_zero : ∃ m : ↥L.M, L.HM m L.cW ≠ 0 := by
  obtain ⟨τ, hτ0, hτ1⟩ := NormedField.exists_norm_lt_one F
  have hτ : τ ≠ 0 := norm_pos_iff.1 hτ0
  set c : Fˣ := Units.mk0 τ hτ
  have hlog : Real.log ‖τ‖ ≠ 0 := (Real.log_neg hτ0 hτ1).ne
  have hN : (finrank F (CliffordAlgebra d.QW) : ℝ) ≠ 0 := by
    rw [finrank_cliffordAlgebra]; positivity
  refine ⟨⟨d.pair (scalarGSpin d.QW c, 1), scalarGSpin_mem_flagLevi (Q := d.QW) L.bW L.wtW c,
    (flagLevi (Q := d.QV) L.bV L.wtV).one_mem⟩, ?_⟩
  have : L.HM ⟨d.pair (scalarGSpin d.QW c, 1), scalarGSpin_mem_flagLevi (Q := d.QW) L.bW L.wtW c,
      (flagLevi (Q := d.QV) L.bV L.wtV).one_mem⟩ L.cW =
      (finrank F (CliffordAlgebra d.QW) : ℝ) * Real.log ‖τ‖ := by
    simp [HM, char, fst_pair, detChar_scalarGSpin, c, norm_pow, Real.log_pow]
  rw [this]
  exact mul_ne_zero hN hlog

/-- A unitary unramified character of `M(F)` with a value `e^{iπ} = −1`. -/
theorem exists_unitaryUnramChar_apply_eq_exp_pi : ∃ ν : L.aMDual, ∃ m : ↥L.M,
    L.unitaryUnramChar ν m = Circle.exp π := by
  classical
  obtain ⟨m, hm⟩ := L.exists_HM_cW_ne_zero
  refine ⟨Pi.single L.cW (π / L.HM m L.cW), m, ?_⟩
  rw [unitaryUnramChar_apply]
  congr 1
  simp only [dualPair, Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  field_simp

private theorem circle_exp_pi_ne_one : Circle.exp π ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Circle.exp_eq_one.1 h
  have h1 : (1 : ℝ) = 2 * n := by
    have := Real.pi_pos.ne'
    field_simp at hn
    linarith
  have h2 : (1 : ℤ) = 2 * n := by exact_mod_cast h1
  omega

/-- **Some unitary unramified character of `M(F)` is nontrivial.** -/
theorem exists_unitaryUnramChar_ne_one : ∃ ν : L.aMDual, L.unitaryUnramChar ν ≠ 1 := by
  obtain ⟨ν, m, hm⟩ := L.exists_unitaryUnramChar_apply_eq_exp_pi
  refine ⟨ν, fun h => circle_exp_pi_ne_one ?_⟩
  rw [← hm, h]
  rfl

/-- **`𝒜^∨_{M,F} ≠ a*_M`**: the torus `i a*_{M,F}` is not a point. -/
theorem dualLattice_ne_top : L.dualLattice ≠ ⊤ := by
  obtain ⟨ν, hν⟩ := L.exists_unitaryUnramChar_ne_one
  intro h
  exact hν ((L.unitaryUnramChar_eq_one_iff ν).2 (h ▸ AddSubgroup.mem_top ν))

/-- **`i a*_{M,F}` is neither a point nor all of `a*_M`.** -/
theorem dualLattice_ne_bot_ne_top : L.dualLattice ≠ ⊥ ∧ L.dualLattice ≠ ⊤ :=
  ⟨L.dualLattice_ne_bot, L.dualLattice_ne_top⟩

/-- **A real `λ` gives a non-unitary `χ_λ`**: the criterion `norm_unramChar_eq_one_iff` has
content. -/
theorem exists_unramChar_not_unitary : ∃ μ : L.aMDualC, ∃ m : ↥L.M,
    ‖(L.unramChar μ m : ℂ)‖ ≠ 1 := by
  classical
  obtain ⟨m, hm⟩ := L.exists_HM_cW_ne_zero
  refine ⟨Pi.single L.cW 1, m, ?_⟩
  rw [norm_unramChar]
  have : L.dualPair (fun c => ((Pi.single L.cW (1 : ℂ) : L.aMDualC) c).re) (L.HM m) =
      L.HM m L.cW := by
    simp only [dualPair, Pi.single_apply]
    simp [apply_ite Complex.re]
  rw [this, Ne, Real.exp_eq_one_iff]
  exact hm

/-- **The criterion `Re λ = 0` is consistent with the non-unitary `χ_λ` above**: some coordinate
of that `λ` has nonzero real part. -/
theorem not_re_eq_zero_of_not_unitary : ∃ μ : L.aMDualC, ¬ ∀ c, (μ c).re = 0 := by
  obtain ⟨μ, m, hm⟩ := L.exists_unramChar_not_unitary
  exact ⟨μ, fun h => hm ((L.norm_unramChar_eq_one_iff μ).2 h m)⟩

/-- **Twisting changes the action**: `σ_{iν}(m) v = −σ(m) v` for the `ν`, `m` above. -/
theorem unramTwist_ρ_ne (σ : UnitaryRep ↥L.M) (v : σ.H) (hv : v ≠ 0) :
    ∃ ν : L.aMDual, ∃ m : ↥L.M, (L.unramTwist σ ν).ρ m v ≠ σ.ρ m v := by
  obtain ⟨ν, m, hm⟩ := L.exists_unitaryUnramChar_apply_eq_exp_pi
  refine ⟨ν, m, ?_⟩
  change ((L.unitaryUnramChar ν m : Circle) : ℂ) • σ.ρ m v ≠ σ.ρ m v
  rw [hm, Circle.coe_exp, Complex.exp_pi_mul_I, neg_one_smul, Ne, neg_eq_iff_add_eq_zero,
    ← two_smul ℂ, smul_eq_zero]
  rintro (h | h)
  · norm_num at h
  · exact hv ((σ.isUnitary.injective m) (h.trans (map_zero _).symm))

/-- **For the trivial representation, `i a^∨_{M,σ} = 𝒜^∨_{M,F}`**: `σ_{iν} ≅ σ` forces
`χ_{iν} = 1`. -/
theorem twistStab_trivialRep : L.twistStab (Sanity.trivialRep ↥L.M) = L.dualLattice := by
  refine le_antisymm (fun ν hν => ?_) (L.dualLattice_le_twistStab _)
  obtain ⟨U, hU⟩ :=
    (hν : (L.unramTwist (Sanity.trivialRep ↥L.M) ν).IsEquivalent (Sanity.trivialRep ↥L.M))
  rw [← unitaryUnramChar_eq_one_iff]
  ext m
  set c : ℂ := ((L.unitaryUnramChar ν m : Circle) : ℂ)
  have e1 : (L.unramTwist (Sanity.trivialRep ↥L.M) ν).ρ m (1 : ℂ) = c • (1 : ℂ) :=
    congrArg (c • ·) (Sanity.trivialRep_ρ_apply _ m (1 : ℂ))
  have h : U (c • (1 : ℂ)) = U (1 : ℂ) :=
    (congrArg U e1).symm.trans ((hU m (1 : ℂ)).trans (Sanity.trivialRep_ρ_apply _ m _))
  have h2 : c • U (1 : ℂ) = (1 : ℂ) • U (1 : ℂ) :=
    (U.map_smul c (1 : ℂ)).symm.trans (h.trans (one_smul ℂ _).symm)
  have hU1 : U (1 : ℂ) ≠ 0 := by
    have := U.norm_map (1 : ℂ)
    rw [← norm_ne_zero_iff, this]
    exact (norm_one (α := ℂ)).symm ▸ one_ne_zero
  exact smul_left_injective ℂ hU1 h2

/-- **The stabilizer of the trivial representation is a proper subgroup.** -/
theorem twistStab_trivialRep_ne_top : L.twistStab (Sanity.trivialRep ↥L.M) ≠ ⊤ := by
  rw [twistStab_trivialRep]
  exact L.dualLattice_ne_top

end ReducedLeviDatum

end GGPData

end GSpinGGP
