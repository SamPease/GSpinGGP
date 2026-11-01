/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.MGeom

/-!
# The limit `s → 0⁺` of `m_{geom,s}` from integrability at `s = 0`

Thesis Prop 12.1.1(i), (12.1.4) asserts that `lim_{s → 0⁺} m_{geom,s}(θ)` exists for a
quasi-character `θ`; the thesis proves it by an induction on `dim G`.  This file records a
shorter route: if, for every torus `T`, the integrand of `m_{geom,s}(θ)` is already integrable on
`T(F)/A_{G,H}(F)` at `s = 0` and `Δ` is bounded on `T_♮`, then dominated convergence gives
`m_{geom,s}(θ) → m_{geom,0}(θ)`.

The integrability at `s = 0` is, for the special orthogonal pair, the local integrability of
`t ↦ c_θ(t) c_τ(t) D^H(t) Δ(t)^r` on `T(F)` in Waldspurger, *Une formule intégrale reliée à la
conjecture locale de Gross–Prasad*, Compositio Math. 146 (2010), Prop. 7.3(ii), since
`D^G(t)^{1/2} Δ(t)^{-1/2} = D^H(t) Δ(t)^r` (from `so(V) = Λ²W ⊕ W ⊗ (D ⊕ Z) ⊕ Λ²(D ⊕ Z)`,
`dim Z = 2r`).  Its transfer to `GSpin(W) × GSpin(V)` and to quasi-characters of the product
group that are not tensor products is not stated there, so it is a hypothesis here, not an axiom.
The bound on `Δ` holds (`Δ ≤ 1`: the eigenvalues of `t` on `W''` have absolute value `1`), but is
also left as a hypothesis.

* `norm_gammaIntegrand_le_of_delta_le`: the pointwise domination for `0 ≤ s < 1/2`;
* `tendsto_torusIntegral_of_integrable_zero`: the limit torus by torus;
* `tendsto_mGeomS_of_integrable_zero`: the limit of `m_{geom,s}(θ)`, with value `m_{geom,0}(θ)`.

Status: proved, no new axiom; not used by the main theorem (its hypotheses are not proved).
-/

noncomputable section

open MeasureTheory Topology Filter

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
variable (ψ : NontrivialAddChar F) (d : GGPData F)

/-- **Pointwise domination** of the integrand of `m_{geom,s}` by the one at `s = 0`, for
`0 ≤ s < 1/2`, when `Δ ≤ B` on `T_♮`: `Δ^{s - 1/2} = Δ^s Δ^{-1/2} ≤ max(1, B)^s Δ^{-1/2}`
(both sides vanish where `Δ = 0`, since `s - 1/2 ≠ 0`). -/
theorem norm_gammaIntegrand_le_of_delta_le {θ : ↥d.G → ℂ} {T : Subgroup ↥(GSpin d.QW)}
    {B : ℝ} (hB : ∀ t : ↥(GSpin d.QW), d.IsGammaElt t → d.torusOf t = T → deltaGGP d t ≤ B)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1 / 2) (t : ↥(GSpin d.QW)) :
    ‖gammaIntegrand ψ d θ T s t‖ ≤ max 1 B ^ s * ‖gammaIntegrand ψ d θ T 0 t‖ := by
  unfold gammaIntegrand
  split_ifs with h
  · set a : ℂ := (Real.sqrt (weylDisc d.lie (d.diag t : d.ambientˣ)) : ℂ) *
      germ d.G d.lie d.bilin ψ θ (d.diag t) (orbitChoice d t)
    have hΔ0 : 0 ≤ deltaGGP d t := absF_nonneg _
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hΔ0 _)]
    rw [mul_left_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg a)
    rcases hΔ0.eq_or_lt with h0 | hpos
    · rw [← h0, Real.zero_rpow (by linarith), Real.zero_rpow (by norm_num), mul_zero]
    · rw [show s - 1 / 2 = s + (0 - 1 / 2) by ring, Real.rpow_add hpos]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hΔ0 _)
      exact Real.rpow_le_rpow hΔ0 ((hB t h.1 h.2).trans (le_max_right _ _)) hs0
  · simp

/-- **The limit `s → 0⁺` torus by torus**: if the integrand of `m_{geom,s}(θ)` is integrable on
`T(F)/A_{G,H}(F)` at `s = 0` and `Δ` is bounded on `T_♮`, then
`∫_{T(F)/A} D^G(t)^{1/2} c_{θ,O_t}(t) Δ(t)^{s-1/2} dt → ∫_{T(F)/A} … Δ(t)^{-1/2} dt` as `s → 0⁺`
(dominated convergence with the bound `max(1, B) · |integrand at 0|`). -/
theorem tendsto_torusIntegral_of_integrable_zero {χ : CentralCharOn d} {θ : ↥d.G → ℂ}
    (hθ : θ ∈ QC d χ) (T : Subgroup ↥(GSpin d.QW)) (h0 : IsTorusIntegrable ψ d θ T 0)
    (hB : ∃ B : ℝ, ∀ t : ↥(GSpin d.QW), d.IsGammaElt t → d.torusOf t = T → deltaGGP d t ≤ B) :
    Tendsto (fun s => torusIntegral ψ d θ T s) (𝓝[>] (0 : ℝ))
      (𝓝 (torusIntegral ψ d θ T 0)) := by
  obtain ⟨B, hB⟩ := hB
  let _ : MeasurableSpace (d.TorusQuot T) := borel _
  have : BorelSpace (d.TorusQuot T) := ⟨rfl⟩
  unfold torusIntegral
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Set.Ioo (0 : ℝ) (1 / 2) :=
    Ioo_mem_nhdsGT (by norm_num)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun q => max 1 B * ‖gammaIntegrand ψ d θ T 0 ((Quotient.out q : ↥T) : ↥(GSpin d.QW))‖)
    (Eventually.of_forall fun s => aestronglyMeasurable_torusFn_of_mem_QC ψ d hθ T s)
    ?_ (h0.norm.const_mul _) ?_
  · filter_upwards [hev] with s hs
    refine Eventually.of_forall fun q => ?_
    refine (norm_gammaIntegrand_le_of_delta_le ψ d hB hs.1.le hs.2 _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have h1 : (1 : ℝ) ≤ max 1 B := le_max_left _ _
    calc max 1 B ^ s ≤ max 1 B ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hs.2])
      _ = max 1 B := Real.rpow_one _
  · refine Eventually.of_forall fun q => ?_
    set t : ↥(GSpin d.QW) := ((Quotient.out q : ↥T) : ↥(GSpin d.QW))
    unfold gammaIntegrand
    split_ifs with h
    · refine Tendsto.const_mul _ (Complex.continuous_ofReal.continuousAt.tendsto.comp ?_)
      rcases (show (0 : ℝ) ≤ deltaGGP d t from absF_nonneg _).eq_or_lt with hz | hpos
      · rw [← hz, Real.zero_rpow (by norm_num)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with s hs
        rw [Real.zero_rpow (by linarith [hs.2])]
      · have hc : Continuous fun s : ℝ => deltaGGP d t ^ (s - 1 / 2) :=
          (Real.continuous_const_rpow hpos.ne').comp (continuous_id.sub continuous_const)
        exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · exact tendsto_const_nhds

/-- **`lim_{s → 0⁺} m_{geom,s}(θ) = m_{geom,0}(θ)`** for `θ ∈ QC(G(F), χ)`, given integrability of
the integrand at `s = 0` on every `T(F)/A_{G,H}(F)` and boundedness of `Δ` on every `T_♮`.
This gives the conclusion of `tendsto_mGeomS_of_mem_QC` (Thesis (12.1.4)) without the thesis's
induction on `dim G`; the integrability hypothesis is, for the special orthogonal pair,
Waldspurger 2010 Prop. 7.3(ii) (see the module docstring). -/
theorem tendsto_mGeomS_of_integrable_zero {χ : CentralCharOn d} {θ : ↥d.G → ℂ}
    (hθ : θ ∈ QC d χ) (h0 : ∀ T : Subgroup ↥(GSpin d.QW), IsTorusIntegrable ψ d θ T 0)
    (hB : ∀ T : Subgroup ↥(GSpin d.QW), ∃ B : ℝ,
      ∀ t : ↥(GSpin d.QW), d.IsGammaElt t → d.torusOf t = T → deltaGGP d t ≤ B) :
    Tendsto (mGeomS ψ d θ) (𝓝[>] (0 : ℝ)) (𝓝 (mGeomS ψ d θ 0)) := by
  have := finite_gammaClass d
  have : Fintype (GammaClass d) := Fintype.ofFinite _
  unfold mGeomS
  simp only [tsum_fintype]
  exact tendsto_finsetSum _ fun c _ => (tendsto_torusIntegral_of_integrable_zero ψ d hθ
    (Quot.out c).1 (h0 _) (hB _)).const_mul _

end GSpinGGP
