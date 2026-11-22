/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.DcQuotient
import GSpinGGP.Sanity.ThetaFBPAudit
import GSpinGGP.Sanity.LieAudit

/-!
# Sanity check: with `dg / d_c a` on `G/A_G`, `θ_f` is Beuzart-Plessis' `θ_f` at `toyD`

At the toy datum `toyD` (`G = GL₁ × GL₁ = A_G`), `G(F)/A_G(F)` is a point.  Its mass for
`measGmodAG = dg / d_c a` is the `dg`-volume of the maximal compact subgroup
`A_G(𝒪) = {|c₁| = |c₂| = 1}` (`toyOneSet`), because `d_c a` gives `A_G(𝒪)` mass `1`
(`toyD_dcScaleAG`).  So the orbital-pairing `θ_f` (`thetaF`, `θ_f = c f` by `toyD_thetaF_eq`)
equals the `θ_f` of Beuzart-Plessis' formula (`thetaFBP`, `θ_f = c f` by `toyD_thetaFBP`):
`toyD_thetaF_eq_thetaFBP`.  With `Measure.haar` on the point (mass `1`) instead, the two would
differ by the factor `c`.  No new axioms; `weil_quotient_radon` is used (through
`isDcQuotientAG_measGmodAG`).
-/

noncomputable section

open MeasureTheory GSpinGGP.Sanity GSpinGGP.AxiomRedTeam
open scoped ENNReal NNReal

namespace GSpinGGP.GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝕋" => (toyD (F := F))

/-- At `toyD`, `A_G(F) ∩ ker H_G` is `toyOneSet` (neither factor is a hyperbolic plane, so `H_G`
records `log |N(g_W)|`, `log |N(g_V)|`). -/
theorem toyD_mem_ker_hcA_iff (a : ↥(𝕋).AG) :
    a ∈ (𝕋).hcA.ker ↔ (a : ↥(𝕋).G) ∈ toyOneSet := by
  classical
  have hW : ¬ IsHypPlane (𝕋).QW := toyD_not_isHypPlane_QW
  have hV : ¬ IsHypPlane (𝕋).QV := toyD_not_isHypPlane_QV
  rw [MonoidHom.mem_ker, hcA_apply]
  change ((hcMap (𝕋).QW ((𝕋).fst a), hcMap (𝕋).QV ((𝕋).snd a)) = 1) ↔ _
  rw [Prod.mk_eq_one, hcMap_eq_one_iff, hcMap_eq_one_iff]
  simp only [gspinChar₁, gspinChar₂, hW, hV, dite_false, MonoidHom.one_apply, Units.val_one,
    norm_one, and_true, toyOneSet, Set.mem_ofPred_eq]

/-- **At `toyD`, `dcScaleAG` is the `dg`-volume of `A_G(𝒪)`**: `G/A_G` is a point, and
`∫_G φ dg = haar(A_G(𝒪)) ∫_{A_G} φ d_c a` because `d_c a` (transported to `G = A_G`) is the Haar
measure of `G` giving `A_G(𝒪)` mass `1`. -/
theorem toyD_dcScaleAG :
    (𝕋).dcScaleAG = (Measure.haar : Measure ↥(𝕋).G) toyOneSet := by
  set S := toyOneSet (F := F)
  set ι : ↥(𝕋).AG → ↥(𝕋).G := Subtype.val
  have hemb : Topology.IsClosedEmbedding ι := (𝕋).isClosed_AG.isClosedEmbedding_subtypeVal
  have hsurj : ∀ g : ↥(𝕋).G, ∃ a : ↥(𝕋).AG, ι a = g := fun g =>
    ⟨⟨g, by rw [toyD_AG_eq_top]; trivial⟩, rfl⟩
  set ν : Measure ↥(𝕋).G := (𝕋).dcA.map ι
  have hνS : ν S = 1 := by
    rw [Measure.map_apply hemb.continuous.measurable isClosed_toyOneSet.measurableSet]
    have e : ι ⁻¹' S = ((𝕋).hcA.ker : Set ↥(𝕋).AG) := by
      ext a; exact (toyD_mem_ker_hcA_iff a).symm
    rw [e, dcA_ker]
  have hνL : ν.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    obtain ⟨a, rfl⟩ := hsurj g
    have hcomm : (fun x : ↥(𝕋).G => ι a * x) ∘ ι = ι ∘ fun b => a * b := rfl
    show ((𝕋).dcA.map ι).map _ = (𝕋).dcA.map ι
    rw [Measure.map_map (measurable_const_mul _) hemb.continuous.measurable, hcomm,
      ← Measure.map_map hemb.continuous.measurable (measurable_const_mul _),
      map_mul_left_eq_self]
  have hνK : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply hemb.continuous.measurable hK.isClosed.measurableSet]
    exact (hemb.isCompact_preimage hK).measure_lt_top
  -- `ν = t • dg` with `t · dg(S) = 1`
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, ν = (t : ℝ≥0∞) • (Measure.haar : Measure ↥(𝕋).G) :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul ν Measure.haar⟩
  have hS0 : (Measure.haar : Measure ↥(𝕋).G) S ≠ 0 :=
    (isOpen_toyOneSet.measure_pos _ ⟨1, one_mem_toyOneSet⟩).ne'
  have hStop : (Measure.haar : Measure ↥(𝕋).G) S ≠ ⊤ := isCompact_toyOneSet.measure_lt_top.ne
  have htS : (t : ℝ≥0∞) * (Measure.haar : Measure ↥(𝕋).G) S = 1 := by
    rw [← hνS, ht, smul_apply, smul_eq_mul]
  have htS' : (t : ℝ) * ((Measure.haar : Measure ↥(𝕋).G) S).toReal = 1 := by
    have := congrArg ENNReal.toReal htS
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_one] at this
  refine dcScaleAG_eq (𝕋) hStop ⟨(𝕋).dcA, isDcMeasureAG_dcA (𝕋), fun φ hφ hφc => ?_⟩
  have := toy_subsingleton_GmodAG (F := F)
  rw [integral_of_subsingleton
    (((Measure.haar : Measure ↥(𝕋).G) S) • (Measure.haar : Measure (𝕋).GmodAG)) _ 1]
  have h1 := haar_real_univ_of_subsingleton (X := (𝕋).GmodAG)
  simp only [Measure.real] at h1 ⊢
  rw [smul_apply, smul_eq_mul, smul_eq_mul, ENNReal.toReal_mul, h1, mul_one]
  set o : ↥(𝕋).G := Quotient.out (1 : (𝕋).GmodAG)
  have hI : ∫ a, φ (o * (a : ↥(𝕋).G)) ∂(𝕋).dcA =
      (t : ℝ) * ∫ g, φ g ∂(Measure.haar : Measure ↥(𝕋).G) := by
    have e1 : ∫ a, φ (o * (a : ↥(𝕋).G)) ∂(𝕋).dcA = ∫ g, φ (o * g) ∂ν :=
      (hemb.measurableEmbedding.integral_map (fun g => φ (o * g))).symm
    rw [e1, integral_mul_left_eq_self φ o, ht, integral_smul_measure, smul_eq_mul,
      ENNReal.coe_toReal]
  rw [hI, ← mul_assoc, mul_comm _ (t : ℝ), htS', one_mul]

/-- **`thetaF = thetaFBP` at `toyD`**: for the Levi datum `M = G` and good compact subgroup of
`toyD_thetaFBP`, the `θ_f` defined by the orbital pairing for `dg / d_c a` on `G/A_G` agrees with
Beuzart-Plessis' formula, for every continuous `f`: both are `haar(A_G(𝒪)) · f`
(`toyD_thetaF_eq`, `toyD_dcScaleAG`, `toyD_thetaFBP`). -/
theorem toyD_thetaF_eq_thetaFBP :
    ∃ (L : (𝕋).ReducedLeviDatum) (K : (𝕋).GoodK L.toFlagLeviDatum), (∀ x, L.IsMx x) ∧
      ∀ f : ↥(𝕋).G → ℂ, Continuous f → thetaF (𝕋) f = L.thetaFBP K f := by
  obtain ⟨L, K, hMx, -, -, hBP⟩ := toyD_thetaFBP (F := F)
  refine ⟨L, K, hMx, fun f hf => funext fun x => ?_⟩
  rw [toyD_thetaF_eq hf, hBP x f, Pi.smul_apply, smul_eq_mul, toyD_dcScaleAG, Measure.real]

end GSpinGGP.GGPData
