/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Volumes of convex hulls, for the Haar measure normalized by a lattice

General measure theory for Arthur's weight `v_M(g)` (`GGP/WeightVM.lean`): `v_M(g)` is the volume
of a convex hull of points in `a_M^G`, for the Haar measure giving the quotient of `a_M^G` by a
lattice the volume `1` (Waldspurger, *Une formule intégrale reliée à la conjecture locale de
Gross-Prasad*, Compos. Math. 146 (2010), §1.2; Beuzart-Plessis, Astérisque 418, §1.6, §1.10).

## Main definitions

* `MeasureTheory.Measure.latticeHaar Λ`: `addHaar / covol(Λ)` on a finite-dimensional real normed
  space `E`, for an additive subgroup `Λ`.  When `Λ` has a fundamental domain `D` of finite positive
  `addHaar` measure (e.g. `Λ` a lattice) it is the Haar measure with `μ(D) = 1`
  (`latticeHaar_fundamentalDomain`), so it does not depend on the choice of `addHaar`.
* `MeasureTheory.Measure.hullVolume Λ S`: the `latticeHaar Λ`-volume of the convex hull of `S`.

## Main results

* `hullVolume_vadd`, `hullVolume_neg`: invariance under translating and negating the points.
* `hullVolume_of_subsingleton`: in the zero space the hull of a nonempty set has volume `1`.
-/

noncomputable section

open Pointwise ENNReal

namespace MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The Haar measure normalized by `Λ`**: `addHaar / covol(Λ)`, where `covol(Λ)` is the
`addHaar`-volume of a fundamental domain of `Λ` (Mathlib's `addCovolume`, `0` if there is none).
For a lattice `Λ` this is the unique Haar measure for which `E/Λ` has volume `1`
(`latticeHaar_fundamentalDomain`, `latticeHaar_fundamentalDomain_of_isZLattice`); it does not
depend on the choice of `addHaar` (`latticeHaar_eq`).  Junk value: if `Λ` has no fundamental
domain, `addCovolume = 0` and `latticeHaar Λ = ⊤ • addHaar`. -/
def latticeHaar (Λ : AddSubgroup E) : Measure E :=
  (addCovolume Λ E addHaar)⁻¹ • addHaar

/-- **`latticeHaar` gives a fundamental domain the volume `1`.** -/
theorem latticeHaar_fundamentalDomain {Λ : AddSubgroup E} [Countable Λ] {D : Set E}
    (hD : IsAddFundamentalDomain Λ D addHaar) (h0 : addHaar D ≠ 0) (hfin : addHaar D ≠ ⊤) :
    latticeHaar Λ D = 1 := by
  rw [latticeHaar, smul_apply, smul_eq_mul, hD.covolume_eq_volume, ENNReal.inv_mul_cancel h0 hfin]

/-- **`latticeHaar` does not depend on the Haar measure**: for any Haar measure `μ` and any
fundamental domain `D` of `Λ` for `μ`, `latticeHaar Λ = μ(D)⁻¹ • μ`. -/
theorem latticeHaar_eq {Λ : AddSubgroup E} [Countable Λ] (μ : Measure E) [μ.IsAddHaarMeasure]
    {D : Set E} (hD : IsAddFundamentalDomain Λ D μ) : latticeHaar Λ = (μ D)⁻¹ • μ := by
  set c := addHaarScalarFactor (addHaar : Measure E) μ
  have hμ : (addHaar : Measure E) = c • μ := isAddLeftInvariant_eq_smul_of_innerRegular _ _
  have hc : (c : ℝ≥0∞) ≠ 0 := by
    intro h0
    have : (addHaar : Measure E) = 0 := by
      rw [hμ, show c = 0 by exact_mod_cast h0, zero_smul]
    exact (NeZero.ne _ : (addHaar : Measure E) ≠ 0) this
  have hD' : IsAddFundamentalDomain Λ D addHaar :=
    hD.mono (by rw [hμ]; exact smul_absolutelyContinuous)
  rw [latticeHaar, hD'.covolume_eq_volume, hμ]
  ext s hs
  simp only [smul_apply, smul_eq_mul, ENNReal.smul_def]
  rw [ENNReal.mul_inv (Or.inl hc) (Or.inl ENNReal.coe_ne_top),
    show (c : ℝ≥0∞)⁻¹ * (μ D)⁻¹ * (c * μ s) = ((c : ℝ≥0∞)⁻¹ * c) * ((μ D)⁻¹ * μ s) by ring,
    ENNReal.inv_mul_cancel hc ENNReal.coe_ne_top, one_mul]

/-- **For a `ℤ`-lattice, `latticeHaar` gives every fundamental domain the volume `1`.** -/
theorem latticeHaar_fundamentalDomain_of_isZLattice (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] {D : Set E} (hD : IsAddFundamentalDomain L D addHaar) :
    latticeHaar L.toAddSubgroup D = 1 := by
  have h := ZLattice.covolume_ne_zero L addHaar
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L addHaar hD, measureReal_def,
    ENNReal.toReal_ne_zero] at h
  have : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
  exact latticeHaar_fundamentalDomain hD h.1 h.2

/-- **The volume of the convex hull of `S`** for the Haar measure normalized by `Λ`. -/
def hullVolume (Λ : AddSubgroup E) (S : Set E) : ℝ :=
  (latticeHaar Λ (convexHull ℝ S)).toReal

instance (Λ : AddSubgroup E) : (latticeHaar Λ).IsAddLeftInvariant := by
  rw [latticeHaar]; infer_instance

/-- Translating all points does not change the volume of their hull. -/
theorem hullVolume_vadd (Λ : AddSubgroup E) (x : E) (S : Set E) :
    hullVolume Λ (x +ᵥ S) = hullVolume Λ S := by
  rw [hullVolume, hullVolume, convexHull_vadd, measure_vadd]

/-- Negating all points does not change the volume of their hull (`addHaar` is invariant under
`x ↦ −x`); so the conventions "hull of `H_P(g)`" and "hull of `−H_P(g)`" give the same weight. -/
theorem hullVolume_neg (Λ : AddSubgroup E) (S : Set E) : hullVolume Λ (-S) = hullVolume Λ S := by
  rw [hullVolume, hullVolume, convexHull_neg, latticeHaar, smul_apply, smul_apply,
    measure_neg]

/-- **In the zero space the hull of a nonempty set has volume `1`.** -/
theorem hullVolume_of_subsingleton [Subsingleton E] (Λ : AddSubgroup E) {S : Set E}
    (hS : S.Nonempty) : hullVolume Λ S = 1 := by
  have hS' : convexHull ℝ S = Set.univ := by
    obtain ⟨x, hx⟩ := hS
    exact Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ subset_convexHull ℝ S hx
  have : Subsingleton Λ := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have hD : IsAddFundamentalDomain Λ (Set.univ : Set E) addHaar :=
    IsAddFundamentalDomain.mk' nullMeasurableSet_univ fun x =>
      ⟨0, Set.mem_univ _, fun _ _ => Subsingleton.elim _ _⟩
  have h0 : addHaar (Set.univ : Set E) ≠ 0 := (NeZero.ne _ : (addHaar : Measure E) ≠ 0) ∘
    measure_univ_eq_zero.1
  rw [hullVolume, hS', latticeHaar_fundamentalDomain hD h0 (measure_ne_top _ _), ENNReal.toReal_one]

end MeasureTheory.Measure
