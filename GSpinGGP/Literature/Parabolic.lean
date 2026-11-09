/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The integration formula for `G = P K`

This file imports only Mathlib.

* **axiom** `integral_eq_mul_integral_compact_integral`: for a locally compact, second countable
  group `G = P K` with `P` closed and `K` compact, `∫_G f = c ∫_K ∫_P f(p k) dp dk` for left Haar
  measures and some constant `c > 0`;
* `integral_eq_mul_integral_compact_integral_of_subsingleton` (sanity, no axiom): the conclusion
  holds, with `c = 1`, for the trivial group, the degenerate instance where every Haar measure is
  the unit point mass.

Used for the unitarity of normalized parabolic induction (`GGPData.ParIndData.preInner_rightTrans`
in `GGP/Levi.lean`): with `G` unimodular, it makes `φ ↦ ∫_K φ(k) dk` a right-`G`-invariant form on
the functions with `φ(p x) = δ_P(p) φ(x)`.
-/

open MeasureTheory

noncomputable section

namespace GSpinGGP

/-- **The integration formula for `G = P K`** (Bourbaki, *Integration* II, Ch. VII §2 no. 9,
Prop. 13 and its Corollary, formula (23), p. VII.49: for closed subgroups `X`, `Y` of `G` with `XY`
open, `X ∩ Y` compact and `X × Y → XY` open, `∫_{XY} f dμ_G = a ∫_{X × Y} f(xy) Δ_G(y) Δ_Y(y)⁻¹
dμ_X dμ_Y`; checked). Here `X = P`, `Y = K` compact, so `Δ_G = Δ_K = 1` on `K` and `P ∩ K` is
compact; `XY = G`, and second countability gives the openness hypothesis (Bourbaki's hypothesis
that `(X × Y)/Z₀ → XY` is a homeomorphism, App. I, Lemma 2, p. VII.75, for σ-compact groups). So the statement below is
Bourbaki's in its generality (not an adaptation).

Let `G` be a locally compact, Hausdorff, second countable group, `P` a closed subgroup and `K` a
compact subgroup with `G = P K`.  Then for left Haar measures `dx`, `dp` on `G`, `P` and the Haar
measure `dk` on `K` there is `c > 0` with
`∫_G f(x) dx = c ∫_K ∫_P f(p k) dp dk` for every continuous compactly supported `f`.

Proof in the sources: `P × K` acts transitively on `G` by `(p, k)·x = p x k⁻¹`, with compact
stabilizer `{(s, s) : s ∈ P ∩ K}`, and the action map is open (σ-compactness); both sides are
`P × K`-invariant Radon measures on `G ≅ (P × K)/(P ∩ K)` (the left side because the modular
function of `G` is trivial on the compact `K`; the right side because a compact group is
unimodular), and such a measure is unique up to a positive scalar (the modular functions of
`P × K` and of the compact stabilizer agree on it).  No unimodularity of `G` or `P` is needed.

Only continuous compactly supported `f` are claimed (as for `weil_quotient`); the constant
absorbs the normalizations of the three Haar measures.  `dp` is *left* Haar measure on `P`; this
matters when `P` is not unimodular (checked by hand on `ℚ_p ⋊ ℚ_p^×` with `P = ℚ_p ⋊ p^ℤ`,
`K = ℤ_p^×`: `c = 1`). The instance `[LocallyCompactSpace ↥P]` is implied by `P` being closed; it is
kept as a binder for convenience and adds no hypothesis. -/
axiom integral_eq_mul_integral_compact_integral {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (P K : Subgroup G) (hP : IsClosed (P : Set G)) [LocallyCompactSpace ↥P] [CompactSpace ↥K]
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : G → ℂ, Continuous f → HasCompactSupport f →
      ∫ x, f x ∂(Measure.haar : Measure G) =
        c * ∫ k : ↥K, ∫ p : ↥P, f ((p : G) * (k : G)) ∂(Measure.haar : Measure ↥P)
          ∂(Measure.haar : Measure ↥K)

section Sanity

theorem haar_univ_eq_one_of_subsingleton' {X : Type*} [Group X] [TopologicalSpace X]
    [IsTopologicalGroup X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [Subsingleton X] : (Measure.haar : Measure X).real Set.univ = 1 := by
  set K₀ : TopologicalSpace.PositiveCompacts X := Classical.arbitrary _
  have hK : (K₀ : Set X) = Set.univ := K₀.nonempty.eq_univ
  have h : Measure.haarMeasure K₀ Set.univ = 1 := by
    rw [← hK]
    exact Measure.haarMeasure_self
  rw [measureReal_def]
  change (Measure.haarMeasure K₀ Set.univ).toReal = 1
  rw [h, ENNReal.toReal_one]

/-- **Consistency check of `integral_eq_mul_integral_compact_integral` at the trivial group**
(proved without the axiom): all three Haar measures are the unit point mass, and the formula holds
with `c = 1`. -/
theorem integral_eq_mul_integral_compact_integral_of_subsingleton {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [Subsingleton G]
    (P K : Subgroup G) [LocallyCompactSpace ↥P] [CompactSpace ↥K] :
    ∃ c : ℝ, 0 < c ∧ ∀ f : G → ℂ, Continuous f → HasCompactSupport f →
      ∫ x, f x ∂(Measure.haar : Measure G) =
        c * ∫ k : ↥K, ∫ p : ↥P, f ((p : G) * (k : G)) ∂(Measure.haar : Measure ↥P)
          ∂(Measure.haar : Measure ↥K) := by
  refine ⟨1, one_pos, fun f _ _ => ?_⟩
  have hc : ∀ x : G, f x = f 1 := fun x => congrArg f (Subsingleton.elim x 1)
  simp only [hc, integral_const, haar_univ_eq_one_of_subsingleton', one_smul, Complex.ofReal_one,
    one_mul]

end Sanity

end GSpinGGP
