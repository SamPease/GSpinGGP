/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.HarmonicAnalysis.PolynomialGrowth

/-!
# Sanity check: the hypotheses of the abstract BP Prop 6.7.1(iii) are satisfiable

A toy instance of `HarmonicAnalysis/RelativeXi.lean` and `HarmonicAnalysis/PolynomialGrowth.lean`:
`G = X = ℤ` (written multiplicatively for `G`), `π` the identity, `μ` the counting measure, the
log-norm `τ(n) = 1 + |n|`. Then `IsInvariantQuotient π μ` holds, `WeakCartanData π τ` is inhabited
(with `S = G`, `K = C_S = {1}`, growth `≤ 3(1 + R)`), `Ξ_{{1}} = 1`, and the abstract theorem gives
the (true) convergence of `∑_n (1 + |n|)^{-d}` for some `d > 0`. So none of these hypotheses is
vacuous.
-/

open MeasureTheory Set

noncomputable section

namespace GSpinGGP.Sanity.RelativeXiToy

/-- The projection `G = Multiplicative ℤ → X = ℤ`. -/
abbrev πZ : Multiplicative ℤ → ℤ := Multiplicative.toAdd

/-- The log-norm `1 + |n|` on `ℤ`. -/
def τZ (g : Multiplicative ℤ) : ℝ := 1 + |((Multiplicative.toAdd g : ℤ) : ℝ)|

theorem isLogNorm_τZ : IsLogNorm τZ :=
  IsLogNorm.of_continuous continuous_of_discreteTopology
    (fun g => le_add_of_nonneg_right (abs_nonneg _))
    (fun g h => by
      simp only [τZ, toAdd_mul, Int.cast_add]
      linarith [abs_add_le ((Multiplicative.toAdd g : ℤ) : ℝ) (Multiplicative.toAdd h : ℤ)])
    (fun g => by simp [τZ])

theorem isInvariantQuotient_πZ : IsInvariantQuotient πZ Measure.count where
  descends g g' h hg := by
    have : g = g' := hg
    rw [this]
  measure_image_mul_right S h := by
    have e : πZ '' ((· * h) '' S) = (· + Multiplicative.toAdd h) '' (πZ '' S) := by
      rw [image_image, image_image]; rfl
    rw [e, Measure.count_injective_image (add_left_injective _)]

theorem fiberInf_τZ (g : Multiplicative ℤ) : fiberInf τZ πZ (πZ g) = τZ g := by
  apply le_antisymm (isLogNorm_τZ.fiberInf_le πZ g)
  have : Nonempty {g' : Multiplicative ℤ // πZ g' = πZ g} := ⟨⟨g, rfl⟩⟩
  refine le_ciInf fun g' => ?_
  have : (g' : Multiplicative ℤ) = g := g'.2
  rw [this]

/-- The toy weak Cartan data on `ℤ`. -/
def weakCartanDataZ : WeakCartanData πZ τZ where
  S := univ
  K := {1}
  isCompact_K := isCompact_singleton
  exists_eq_mul g := ⟨g, trivial, 1, rfl, by simp⟩
  c := 1
  le_fiberInf s _ := by rw [one_mul, fiberInf_τZ]
  CS := {1}
  isCompact_CS := isCompact_singleton
  M := 3
  N := 1
  growth R hR := by
    refine ⟨(Finset.Icc (-⌈R⌉) ⌈R⌉).image Multiplicative.ofAdd, ?_, ?_⟩
    · have h1 : (((Finset.Icc (-⌈R⌉) ⌈R⌉).image Multiplicative.ofAdd).card : ℝ) ≤
          ((Finset.Icc (-⌈R⌉) ⌈R⌉).card : ℝ) := by exact_mod_cast Finset.card_image_le
      have h2 : ((Finset.Icc (-⌈R⌉) ⌈R⌉).card : ℝ) = 2 * ⌈R⌉ + 1 := by
        rw [Int.card_Icc]
        have h0 : (0 : ℤ) ≤ ⌈R⌉ + 1 - -⌈R⌉ := by
          have := Int.ceil_nonneg (show (0 : ℝ) ≤ R by linarith); omega
        rw [show ((⌈R⌉ + 1 - -⌈R⌉).toNat : ℝ) = ((⌈R⌉ + 1 - -⌈R⌉ : ℤ) : ℝ) by
          exact_mod_cast Int.toNat_of_nonneg h0]
        push_cast; ring
      have h3 := Int.ceil_lt_add_one R
      rw [pow_one]
      linarith
    · rintro _ ⟨s, ⟨-, hs⟩, rfl⟩
      have hs' : |((Multiplicative.toAdd s : ℤ) : ℝ)| < R := by simp only [τZ] at hs; linarith
      have hc := Int.le_ceil R
      have hlo : -⌈R⌉ ≤ Multiplicative.toAdd s := by
        have : -((⌈R⌉ : ℤ) : ℝ) ≤ ((Multiplicative.toAdd s : ℤ) : ℝ) := by
          linarith [neg_abs_le ((Multiplicative.toAdd s : ℤ) : ℝ)]
        exact_mod_cast this
      have hhi : Multiplicative.toAdd s ≤ ⌈R⌉ := by
        have : ((Multiplicative.toAdd s : ℤ) : ℝ) ≤ ((⌈R⌉ : ℤ) : ℝ) := by
          linarith [le_abs_self ((Multiplicative.toAdd s : ℤ) : ℝ)]
        exact_mod_cast this
      refine mem_iUnion₂.2 ⟨s, Finset.mem_image.2 ⟨Multiplicative.toAdd s,
        Finset.mem_Icc.2 ⟨hlo, hhi⟩, rfl⟩, s, ⟨1, rfl, mul_one s⟩, rfl⟩

/-- In the toy case `Ξ_{{1}} = 1`: every translate `x{1}` has counting measure `1`. -/
theorem relXi_one (g : Multiplicative ℤ) : relXi πZ Measure.count {1} g = 1 := by
  simp [relXi, relVol]

/-- **The abstract BP Prop 6.7.1(iii) applies to the toy data**: it gives the convergence of
`∑_n Ξ(n)² (1 + |n|)^{-d}` for some `d > 0` (here `Ξ = 1`). -/
example : ∃ d : ℝ, 0 < d ∧ Integrable (fun x : ℤ =>
    relXi πZ Measure.count {1} (Multiplicative.ofAdd x) ^ 2 * fiberInf τZ πZ x ^ (-d))
    Measure.count := by
  have hint : (interior ({1} : Set (Multiplicative ℤ))).Nonempty := by
    rw [(isOpen_discrete _).interior_eq]; exact singleton_nonempty _
  exact isInvariantQuotient_πZ.exists_integrable_of_hasPolynomialGrowth hint
    weakCartanDataZ.isCompact_CS_mul_K (fun g => rfl) (measurable_of_countable _).aestronglyMeasurable
    (isLogNorm_τZ.one_le_fiberInf_of_surjective _ Multiplicative.toAdd.surjective)
    (measurable_of_countable _)
    (weakCartanDataZ.hasPolynomialGrowth isLogNorm_τZ Multiplicative.toAdd.surjective
      isInvariantQuotient_πZ.descends)

end GSpinGGP.Sanity.RelativeXiToy
