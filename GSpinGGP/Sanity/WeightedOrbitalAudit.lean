/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.WeightedOrbital
import GSpinGGP.Sanity.WeightAudit

/-!
# Sanity checks for orbital and weighted orbital integrals

At the toy datum `toyD` (`G = GL₁ × GL₁`, commutative) every centralizer is `G_x(F) = G(F)`, so
`G_x(F)\G(F)` is a point, `D^G = 1`, and the orbital integral is evaluation at `x` times a
positive constant (the mass of the point for the quotient measure `dg/dμ`):
`J_G(x, f) = c f(x)` with `c > 0` (`toyD_orbitalIntegral`).  For the reduced Levi datum with
`M = G` of `toyD_vM_eq_one`, `J_M = J_G` (`toyD_weightedOrbitalIntegral`).  So the definitions are
not degenerate: the quotient measure is nonzero and the integrals see `f`.  The integrability
statement is not used.
-/

noncomputable section

open MeasureTheory GSpinGGP.Sanity GSpinGGP.AxiomRedTeam

namespace GSpinGGP.GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝕋" => (toyD (F := F))

/-- At `toyD`, `G_x(F) = G(F)` (`G` is commutative). -/
theorem toyD_centG_eq_top (x : ↥(𝕋).G) : (𝕋).centG x = ⊤ :=
  eq_top_iff.2 fun _ _ => Subgroup.mem_centralizer_singleton_iff.2 (toyD_G_comm _ _)

/-- At `toyD`, `G_x(F)\G(F)` is a point. -/
instance toyD_subsingleton_centQuot (x : ↥(𝕋).G) : Subsingleton ((𝕋).CentQuot x) := by
  refine ⟨fun a b => ?_⟩
  induction a using CosetSpace.ind with | h a => ?_
  induction b using CosetSpace.ind with | h b => ?_
  rw [CosetSpace.mk_eq_mk_iff, CosetSpace.rel_iff]
  refine ⟨⟨b * a⁻¹, by simp [toyD_centG_eq_top]⟩, ?_⟩
  simp

/-- The Haar measure of the commutative group `G_x(F)` is right invariant. -/
instance toyD_isMulRightInvariant_haar_centG (x : ↥(𝕋).G) :
    (Measure.haar : Measure ↥((𝕋).centG x)).IsMulRightInvariant :=
  ⟨fun g => by
    have : (· * g) = (g * ·) := funext fun h => Subtype.ext (toyD_G_comm _ _)
    rw [this]
    exact map_mul_left_eq_self _ _⟩

/-- **`J_G(x, f) = c f(x)` at `toyD`, with `c > 0`**: the quotient `G_x(F)\G(F)` is a point of
positive finite mass for `dg/dμ`, `D^G = 1`, and `g⁻¹ x g = x`. -/
theorem toyD_orbitalIntegral (x : ↥(𝕋).G) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ↥(𝕋).G → ℂ,
      (𝕋).orbitalIntegral x Measure.haar f = c * f x := by
  have hW := (𝕋).orbQuotMeasure_spec (x := x) Measure.haar
  set m := (𝕋).orbQuotMeasure x Measure.haar
  set ι := ((𝕋).centG x).subtype
  have hfin : m Set.univ ≠ ⊤ := (Set.finite_univ.isCompact).measure_lt_top.ne
  -- the mass of the point is positive: test the Weil formula on a bump at `1`
  have hpos : m Set.univ ≠ 0 := by
    intro h0
    have hm : m = 0 := Measure.measure_univ_eq_zero.1 h0
    obtain ⟨φ, hφ1, -, hφc, hφ01⟩ := exists_continuous_one_zero_of_isCompact
      (isCompact_singleton (x := (1 : ↥(𝕋).G))) isClosed_empty (Set.disjoint_empty _)
    have hpos : 0 < ∫ g, φ g ∂(Measure.haar : Measure ↥(𝕋).G) :=
      φ.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero hφc
        (fun g => (hφ01 g).1) (x := 1) (by rw [hφ1 rfl]; exact one_ne_zero)
    rw [hW φ φ.continuous hφc, hm, integral_zero_measure] at hpos
    exact lt_irrefl _ hpos
  refine ⟨m.real Set.univ, ENNReal.toReal_pos hpos hfin, fun f => ?_⟩
  have hD : weylDisc (𝕋).lie (x : (𝕋).ambientˣ) = 1 := toyD_weylDisc _
  have hpt : ∀ q : (𝕋).CentQuot x,
      f ((CosetSpace.out ι q)⁻¹ * x * CosetSpace.out ι q) = f x := fun q => by
    rw [mul_assoc, toyD_G_comm x, inv_mul_cancel_left]
  rw [orbitalIntegral_eq]
  rw [hD, Real.sqrt_one]
  simp_rw [ι] at hpt; simp_rw [hpt]
  rw [integral_const, Complex.real_smul]
  simp [m]

/-- **`J_M = J_G` at `toyD` for `M = G`**, and so `J_M(x, f) = c f(x)` with `c > 0`. -/
theorem toyD_weightedOrbitalIntegral :
    ∃ (L : (𝕋).ReducedLeviDatum) (K : (𝕋).GoodK L.toFlagLeviDatum), L.M = ⊤ ∧
      ∀ x : ↥(𝕋).G, ∃ c : ℝ, 0 < c ∧ ∀ f : ↥(𝕋).G → ℂ,
        (𝕋).weightedOrbitalIntegral L K x Measure.haar f = c * f x := by
  obtain ⟨L, K, hM, hG, -, -⟩ := toyD_vM_eq_one (F := F)
  refine ⟨L, K, hM, fun x => ?_⟩
  obtain ⟨c, hc, h⟩ := toyD_orbitalIntegral x
  exact ⟨c, hc, fun f => by
    rw [weightedOrbitalIntegral_eq_orbitalIntegral_of_aG_eq_top hG, h]⟩

end GSpinGGP.GGPData
