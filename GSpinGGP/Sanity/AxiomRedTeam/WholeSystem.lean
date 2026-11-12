/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Sanity.AxiomRedTeam.Common
import GSpinGGP.Sanity.LieAudit
import GSpinGGP.Literature.HarishChandra
import GSpinGGP.Literature.GSpin
import GSpinGGP.TraceFormula.MGeom
import GSpinGGP.TraceFormula.Analytic
import GSpinGGP.TraceFormula.Spectral

/-!
# Whole-system checks on the toy datum

On `toyD` (`W = 0`, `V` a line, `G ≅ F^× × F^×`) several axioms and several `sorry` statements on
the path of the main theorem meet the definitions in one instance.

* **The multiplicity formula for `π = 1`**, both sides computed separately
  (`toyD_multFormula_trivialRep`): `m(1) = 1` from the definition and `emoryTakeda_mult_le_one`;
  `θ_1(1) = 1` from `rodier_germ_one` and `hc_character_isQuasiCharacter`; `m_geom(θ) = θ(1)` for
  every `θ ∈ QC(χ)` from the definitions.
* **`sorry` statements, conclusions proved at `toyD`** without them:
  `tendsto_mGeomS_of_mem_QC` and `germ_bound_of_mem_QC` for every `θ ∈ QC(χ)`
  (`toyD_tendsto_mGeomS_of_mem_QC`, `toyD_germ_bound_of_mem_QC`) and for `θ = θ_f`
  (`toyD_tendsto_mGeomS_thetaF`, `toyD_germ_bound_thetaF`); `kernelK_bound_scusp` for every
  Iwasawa datum (`toyD_kernelK_bound_scusp`; on the way `Ξ^G ≡ 1`, `Ξ^{H\G} ≡ 1`);
  `bp_integrable_deltaGGP_rpow` (`toyD_bp_integrable`); `prop_6_7_1_iii`
  (`toyD_prop_6_7_1_iii`); `exists_lie_descent` with `Ω = G` (`toyD_exists_lie_descent`).
  `exists_good_nhd_of_not_nearCentral` and `mult_parInd_eq_mGeom` are vacuous there
  (`toyD_isNearCentral`, `toyD_not_isTempIndData`).

Not covered: anything that needs a nonzero nilpotent orbit, a proper parabolic or a nontrivial
torus.
-/

noncomputable section
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
open MeasureTheory Topology Filter GSpinGGP GSpinGGP.Sanity

namespace GSpinGGP.AxiomRedTeam

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝕋" => (toyD (F := F))

/-! ## `m_geom` on `toyD` -/

/-- `m_{geom,s}(θ) = θ(1)` on `toyD` when the germs of `θ` are its values and `θ` is invariant
under the (central) torus. -/
theorem toyD_mGeomS_eq (ψ : NontrivialAddChar F) {θ : ↥(𝕋).G → ℂ}
    (hg : ∀ x O, germ (𝕋).G (𝕋).lie (𝕋).bilin ψ θ x O = θ x)
    (hθ1 : ∀ t : GSpin (𝕋).QW, θ ((𝕋).diag t) = θ 1) (s : ℝ) : mGeomS ψ (𝕋) θ s = θ 1 := by
  unfold mGeomS
  have hsingle := tsum_eq_single (L := SummationFilter.unconditional (GammaClass (𝕋)))
    (f := fun c : GammaClass (𝕋) =>
    ((weylCard (𝕋) c : ℂ))⁻¹ * torusIntegral ψ (𝕋) θ (Quot.out c).1 s)
    (toyD_gammaClass (F := F)) fun c hc => (hc (Subsingleton.elim _ _)).elim
  rw [hsingle, show weylCard (𝕋) (toyD_gammaClass (F := F)) = 1 from toyD_weylCardOf _,
    Nat.cast_one, inv_one, one_mul]
  unfold torusIntegral
  have hT : (Quot.out (toyD_gammaClass (F := F))).1 = ⊤ := toyD_gammaTorus_val _
  letI : MeasurableSpace ((𝕋).TorusQuot (Quot.out (toyD_gammaClass (F := F))).1) := borel _
  haveI : BorelSpace ((𝕋).TorusQuot (Quot.out (toyD_gammaClass (F := F))).1) := ⟨rfl⟩
  rw [integral_of_subsingleton _ _ 1, probHaar_real_univ, one_smul]
  unfold gammaIntegrand
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨toyD_isGammaElt _, by rw [toyD_torusOf, hT]⟩),
    toyD_weylDisc, hg, toyD_deltaGGP, hθ1, Real.sqrt_one, Real.one_rpow]
  simp

theorem toyD_tendsto_mGeomS (ψ : NontrivialAddChar F) {θ : ↥(𝕋).G → ℂ}
    (hg : ∀ x O, germ (𝕋).G (𝕋).lie (𝕋).bilin ψ θ x O = θ x)
    (hθ1 : ∀ t : GSpin (𝕋).QW, θ ((𝕋).diag t) = θ 1) :
    Tendsto (mGeomS ψ (𝕋) θ) (𝓝[>] (0 : ℝ)) (𝓝 (θ 1)) := by
  rw [show mGeomS ψ (𝕋) θ = fun _ => θ 1 from funext (toyD_mGeomS_eq ψ hg hθ1)]
  exact tendsto_const_nhds

theorem toyD_germ_bound (ψ : NontrivialAddChar F) {θ : ↥(𝕋).G → ℂ}
    (hg : ∀ x O, germ (𝕋).G (𝕋).lie (𝕋).bilin ψ θ x O = θ x)
    (hθ1 : ∀ t : GSpin (𝕋).QW, θ ((𝕋).diag t) = θ 1) (T : Subgroup ↥(GSpin (𝕋).QW)) :
    ∃ C : ℝ, ∀ t : ↥(GSpin (𝕋).QW), (𝕋).IsGammaElt t → (𝕋).torusOf t = T →
      ‖(Real.sqrt (weylDisc (𝕋).lie ((𝕋).diag t : (𝕋).ambientˣ)) : ℂ) *
        germ (𝕋).G (𝕋).lie (𝕋).bilin ψ θ ((𝕋).diag t) (orbitChoice (𝕋) t)‖ ≤ C := by
  refine ⟨‖θ 1‖, fun t _ _ => ?_⟩
  rw [toyD_weylDisc, hg, hθ1, Real.sqrt_one]
  simp

theorem toyD_diag_mem_AGH (t : GSpin (𝕋).QW) : (𝕋).diag t ∈ (𝕋).AGH := by
  obtain ⟨c, hc⟩ := toy_gspinW_mem_range (K := F) t
  exact ⟨c, by rw [← hc]; rfl⟩

/-- `θ(diag t) = θ(1)` for `θ ∈ QC(χ)` (`χ` is trivial on `A_{G,H}`). -/
theorem toyD_QC_diag {χ : CentralCharOn (𝕋)} {θ : ↥(𝕋).G → ℂ} (hθ : θ ∈ QC (𝕋) χ)
    (t : GSpin (𝕋).QW) : θ ((𝕋).diag t) = θ 1 := by
  have h := hθ.2 ⟨(𝕋).diag t, (𝕋).AGH_le_AG (toyD_diag_mem_AGH t)⟩ 1
    (by rw [toy_regularSet_eq_univ]; trivial)
  rw [mul_one, χ.trivial_AGH _ (toyD_diag_mem_AGH t)] at h
  simpa using h

/-- Conclusion of `tendsto_mGeomS_of_mem_QC` at `toyD`, for every `θ ∈ QC(χ)`. -/
theorem toyD_tendsto_mGeomS_of_mem_QC (ψ : NontrivialAddChar F) {χ : CentralCharOn (𝕋)}
    {θ : ↥(𝕋).G → ℂ} (hθ : θ ∈ QC (𝕋) χ) :
    ∃ L : ℂ, Tendsto (mGeomS ψ (𝕋) θ) (𝓝[>] (0 : ℝ)) (𝓝 L) :=
  ⟨θ 1, toyD_tendsto_mGeomS ψ (toyD_germ_of_isQC ψ (hθ.1 ψ)) (toyD_QC_diag hθ)⟩

theorem toyD_mGeom_of_QC (ψ : NontrivialAddChar F) {χ : CentralCharOn (𝕋)}
    {θ : ↥(𝕋).G → ℂ} (hθ : θ ∈ QC (𝕋) χ) : mGeom ψ (𝕋) θ = θ 1 :=
  (toyD_tendsto_mGeomS ψ (toyD_germ_of_isQC ψ (hθ.1 ψ)) (toyD_QC_diag hθ)).limUnder_eq

/-- Conclusion of `germ_bound_of_mem_QC` at `toyD`, for every `θ ∈ QC(χ)`. -/
theorem toyD_germ_bound_of_mem_QC (ψ : NontrivialAddChar F) {χ : CentralCharOn (𝕋)}
    {θ : ↥(𝕋).G → ℂ} (hθ : θ ∈ QC (𝕋) χ) (T : Subgroup ↥(GSpin (𝕋).QW)) :
    ∃ C : ℝ, ∀ t : ↥(GSpin (𝕋).QW), (𝕋).IsGammaElt t → (𝕋).torusOf t = T →
      ‖(Real.sqrt (weylDisc (𝕋).lie ((𝕋).diag t : (𝕋).ambientˣ)) : ℂ) *
        germ (𝕋).G (𝕋).lie (𝕋).bilin ψ θ ((𝕋).diag t) (orbitChoice (𝕋) t)‖ ≤ C :=
  toyD_germ_bound ψ (toyD_germ_of_isQC ψ (hθ.1 ψ)) (toyD_QC_diag hθ) T

/-- Conclusion of `tendsto_mGeomS_of_mem_QC` at `toyD` for `θ = θ_f`. -/
theorem toyD_tendsto_mGeomS_thetaF (ψ : NontrivialAddChar F) (χ : CentralCharOn (𝕋))
    {f : ↥(𝕋).G → ℂ} (hf : f ∈ ScuspTestFn (𝕋) χ) :
    ∃ L : ℂ, Tendsto (mGeomS ψ (𝕋) (thetaF (𝕋) f)) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  rw [toyD_thetaF_eq hf.1.continuous]
  exact ⟨f 1, toyD_tendsto_mGeomS ψ (toyD_germ ψ hf.1) (toyD_apply_diag χ hf.2.1)⟩

/-- Conclusion of `germ_bound_of_mem_QC` at `toyD` for `θ = θ_f`. -/
theorem toyD_germ_bound_thetaF (ψ : NontrivialAddChar F) (χ : CentralCharOn (𝕋))
    {f : ↥(𝕋).G → ℂ} (hf : f ∈ ScuspTestFn (𝕋) χ) (T : Subgroup ↥(GSpin (𝕋).QW)) :
    ∃ C : ℝ, ∀ t : ↥(GSpin (𝕋).QW), (𝕋).IsGammaElt t → (𝕋).torusOf t = T →
      ‖(Real.sqrt (weylDisc (𝕋).lie ((𝕋).diag t : (𝕋).ambientˣ)) : ℂ) *
        germ (𝕋).G (𝕋).lie (𝕋).bilin ψ (thetaF (𝕋) f) ((𝕋).diag t) (orbitChoice (𝕋) t)‖ ≤ C := by
  rw [toyD_thetaF_eq hf.1.continuous]
  exact toyD_germ_bound ψ (toyD_germ ψ hf.1) (toyD_apply_diag χ hf.2.1) T

/-! ## The multiplicity formula for `π = 1` -/

theorem hasCentralChar_trivialRep {G : Type} [Group G] [TopologicalSpace G] (A : Subgroup G) :
    HasCentralChar (trivialRep G) A (fun _ => 1) := fun a => by
  rw [one_smul]
  exact MonoidHom.one_apply _

theorem toyD_trivialRep_isTempCC :
    IsTempCC (𝕋) (CentralCharOn.one (𝕋)) (trivialRep ↥(𝕋).G) := by
  have e : (fun a : ↥(𝕋).AG => (((CentralCharOn.one (𝕋)).toHom a : Circle) : ℂ)) =
      fun _ => 1 :=
    funext fun a => by rw [CentralCharOn.one_toHom, MonoidHom.one_apply, Circle.coe_one]
  refine ⟨toyD_trivialRep_isTempered, ?_⟩
  rw [e]
  exact hasCentralChar_trivialRep _

/-- `m(1) = 1`, from the definition and `emoryTakeda_mult_le_one`. -/
theorem toyD_mult_trivialRep (ψ : NontrivialAddChar F) :
    mult ψ (𝕋) (trivialRep ↥(𝕋).G) = 1 := by
  have hle := emoryTakeda_mult_le_one (𝕋) ψ (trivialRep ↥(𝕋).G) toyD_trivialRep_isTempered
  have hne : multiplicity (trivialRep ↥(𝕋).G) (𝕋).H ((𝕋).xi ψ.toAddChar) ≠ 0 :=
    (hasModel_iff_multiplicity_ne_zero _ _ _).1
      (trivialRep_hasModel _ _ _ fun h => (𝕋).xi_eq_one_of_mem_AGH' ψ.toAddChar h
        (toyD_mem_AGH_of_mem_H h.2))
  unfold mult
  generalize multiplicity (trivialRep ↥(𝕋).G) (𝕋).H ((𝕋).xi ψ.toAddChar) = m at hle hne ⊢
  rcases lt_or_eq_of_le hle with h | h
  · exact absurd (Order.lt_one_iff.mp h) hne
  · exact h

/-- `θ_1(1) = 1`, from `rodier_germ_one` (the germ at the regular orbit `0` is `1`, since `1` has
a model for every Whittaker datum of `toyD`) and `hc_character_isQuasiCharacter`. -/
theorem toyD_charG_trivialRep_one (ψ : NontrivialAddChar F) :
    charG (𝕋) (trivialRep ↥(𝕋).G) 1 = 1 := by
  have hQC := hc_character_isQuasiCharacter (𝕋) ψ _ toyD_trivialRep_isTempered
  obtain ⟨w, hw⟩ := rodier_germ_one (𝕋) toyData_isQuasiSplit ψ 1 rfl (zeroOrbit _ _)
    (toyD_mem_nilReg _ _ _)
  have h1 := (hw _ toyD_trivialRep_isTempered).1 (toy_hasModel_trivial w)
  rw [toyD_germ_of_isQC ψ hQC] at h1
  exact h1

/-- **The multiplicity formula for `π = 1` on `toyD`**, both sides computed separately:
`m(1) = 1 = m_geom(θ_1)`. -/
theorem toyD_multFormula_trivialRep (ψ : NontrivialAddChar F) :
    ((mult ψ (𝕋) (trivialRep ↥(𝕋).G)).toNat : ℂ) =
      mGeom ψ (𝕋) (charG (𝕋) (trivialRep ↥(𝕋).G)) := by
  rw [toyD_mGeom_of_QC ψ (charG_mem_QC (𝕋) toyD_trivialRep_isTempCC),
    toyD_charG_trivialRep_one ψ, toyD_mult_trivialRep ψ]
  simp

/-! ## `kernelK_bound_scusp` -/

theorem toyD_xiHC (IW : (𝕋).IwasawaDatum) (g : ↥(𝕋).G) : IW.xiHC g = 1 := by
  have hδ : ∀ p : ↥IW.P0, IW.deltaP0 p = 1 := fun p => by
    unfold GGPData.IwasawaDatum.deltaP0
    rw [modularCharacter_eq_one_of_central p fun y => Subtype.ext (by
      simp only [Subgroup.coe_mul]; exact toyD_G_comm _ _)]
    rfl
  unfold GGPData.IwasawaDatum.xiHC
  simp_rw [hδ, Real.sqrt_one]
  rw [integral_const, smul_eq_mul, mul_one, measureReal_def]
  have h0 : (Measure.haar : Measure ↥IW.K) Set.univ ≠ 0 :=
    isOpen_univ.measure_ne_zero Measure.haar Set.univ_nonempty
  have ht : (Measure.haar : Measure ↥IW.K) Set.univ ≠ ⊤ := measure_ne_top _ _
  exact inv_mul_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨h0, ht⟩)

theorem toyD_xiHG (C₀ : Set ↥(𝕋).G) (hC₀ : C₀.Nonempty) (q : (𝕋).HGQuot) :
    (𝕋).xiHG C₀ q = 1 := by
  unfold GGPData.xiHG
  have hU : ((fun c => (𝕋).mkHG ((𝕋).repHG q * c)) '' C₀) = Set.univ := by
    obtain ⟨c, hc⟩ := hC₀
    exact Set.eq_univ_of_forall fun y => ⟨c, hc, Subsingleton.elim _ _⟩
  rw [hU, ← measureReal_def, toy_weilMeasureHG_real_univ, Real.one_rpow]

/-- Conclusion of `kernelK_bound_scusp` at `toyD`, for every Iwasawa datum. -/
theorem toyD_kernelK_bound_scusp (ψ : NontrivialAddChar F) (χ : CentralCharOn (𝕋))
    (IW : (𝕋).IwasawaDatum) (C₀ : Set ↥(𝕋).G) (hC₀' : (interior C₀).Nonempty) (d₀ : ℝ)
    (K' : Subgroup ↥(𝕋).G) :
    ∃ (C : ℝ) (n : ℕ), ∀ f ∈ (𝕋).ScuspSchwartz χ IW, (𝕋).IsBiInvariant K' f → ∀ x : ↥(𝕋).G,
      ‖kernelK (𝕋) ψ f x‖ ≤
        C * (𝕋).schwartzSeminorm IW n f * (𝕋).xiHG C₀ ((𝕋).mkHG x) ^ 2 *
          (𝕋).logNormHG ((𝕋).mkHG x) ^ (-d₀) := by
  set σ := (𝕋).logNormHG ((𝕋).mkHG 1)
  haveI : Nonempty {g : ↥(𝕋).G // (𝕋).mkHG g = (𝕋).mkHG 1} := ⟨⟨1, rfl⟩⟩
  have hσ : 1 ≤ σ := le_ciInf fun g => (𝕋).one_le_logNormG _
  refine ⟨σ ^ d₀, 0, fun f hf _ x => ?_⟩
  have hx : (𝕋).mkHG x = (𝕋).mkHG 1 := Subsingleton.elim _ _
  rw [hx, toyD_xiHG C₀ (hC₀'.mono interior_subset), toyD_kernelK χ ψ hf.1.2.1]
  have hν : ‖f 1‖ ≤ (𝕋).schwartzSeminorm IW 0 f := by
    have hb := hf.1.2.2 0
    unfold GGPData.schwartzSeminorm
    refine le_trans ?_ (le_ciSup hb 1)
    simp [toyD_xiHC]
  have hσ0 : 0 < σ := lt_of_lt_of_le one_pos hσ
  calc ‖f 1‖ ≤ (𝕋).schwartzSeminorm IW 0 f := hν
    _ = σ ^ d₀ * (𝕋).schwartzSeminorm IW 0 f * 1 ^ 2 * σ ^ (-d₀) := by
      rw [Real.rpow_neg hσ0.le]
      field_simp

/-! ## Other path `sorry` statements at `toyD` -/

/-- `exists_good_nhd_of_not_nearCentral` is vacuous at `toyD`: every element is near-central. -/
theorem toyD_isNearCentral (c : ↥(𝕋).G) : IsNearCentral (𝕋) c := by
  intro U hU
  refine ⟨⟨c, by rw [toyD_AG_eq_top]; trivial⟩, 1, ?_⟩
  simpa using mem_of_mem_nhds hU

/-- `mult_parInd_eq_mGeom` is vacuous at `toyD`: there is no proper parabolic. -/
theorem toyD_not_isTempIndData (η : CentralCharOn (𝕋)) (D : (𝕋).ParIndData) :
    ¬ (𝕋).IsTempIndData η D := fun h => toyD_not_isProperFlagPair _ _ h.proper

/-- Conclusion of `bp_integrable_deltaGGP_rpow` at `toyD`, for every `x` and `s`. -/
theorem toyD_bp_integrable (x : ↥(GSpin (𝕋).QW)) (s : ℝ) :
    letI : MeasurableSpace ((𝕋).TorusQuot ((𝕋).torusOf x)) := borel _
    haveI : BorelSpace ((𝕋).TorusQuot ((𝕋).torusOf x)) := ⟨rfl⟩
    Integrable (fun q : (𝕋).TorusQuot ((𝕋).torusOf x) =>
      Set.indicator {t : ↥(GSpin (𝕋).QW) | (𝕋).IsGammaElt t ∧ (𝕋).torusOf t = (𝕋).torusOf x}
        (fun t => deltaGGP (𝕋) t ^ (s - 1 / 2))
        ((Quotient.out q : ↥((𝕋).torusOf x)) : ↥(GSpin (𝕋).QW)))
      (probHaar ((𝕋).TorusQuot ((𝕋).torusOf x))) := by
  letI : MeasurableSpace ((𝕋).TorusQuot ((𝕋).torusOf x)) := borel _
  haveI : BorelSpace ((𝕋).TorusQuot ((𝕋).torusOf x)) := ⟨rfl⟩
  haveI : CompactSpace ((𝕋).TorusQuot ((𝕋).torusOf x)) := Finite.compactSpace
  haveI : IsFiniteMeasure (probHaar ((𝕋).TorusQuot ((𝕋).torusOf x))) := by
    unfold probHaar
    rw [dite_eq_left_of_eq_true (eq_true ‹_›)]
    infer_instance
  set f := fun q : (𝕋).TorusQuot ((𝕋).torusOf x) =>
      Set.indicator {t : ↥(GSpin (𝕋).QW) | (𝕋).IsGammaElt t ∧ (𝕋).torusOf t = (𝕋).torusOf x}
        (fun t => deltaGGP (𝕋) t ^ (s - 1 / 2))
        ((Quotient.out q : ↥((𝕋).torusOf x)) : ↥(GSpin (𝕋).QW))
  have hf : f = fun _ => f 1 := funext fun q => congrArg f (Subsingleton.elim _ _)
  rw [hf]
  exact integrable_const _

/-- Conclusion of `prop_6_7_1_iii` at `toyD` (`H\G` is a point of finite measure). -/
theorem toyD_prop_6_7_1_iii (C₀ : Set ↥(𝕋).G) :
    ∃ d₀ : ℝ, 0 < d₀ ∧
      Integrable (fun q : (𝕋).HGQuot => (𝕋).xiHG C₀ q ^ 2 * (𝕋).logNormHG q ^ (-d₀))
        (𝕋).weilMeasureHG := by
  haveI : IsFiniteMeasure (𝕋).weilMeasureHG := by
    constructor
    have h := toy_weilMeasureHG_real_univ (F := F)
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [measureReal_def, hc] at h
    simp at h
  refine ⟨1, one_pos, ?_⟩
  set g := fun q : (𝕋).HGQuot => (𝕋).xiHG C₀ q ^ 2 * (𝕋).logNormHG q ^ (-(1:ℝ))
  obtain ⟨q₀⟩ : Nonempty (𝕋).HGQuot := ⟨(𝕋).mkHG 1⟩
  have hg : g = fun _ => g q₀ := funext fun q => congrArg g (Subsingleton.elim _ _)
  rw [hg]
  exact integrable_const _

/-- Conclusion of `exists_lie_descent` at `toyD`, with `Ω = G`. -/
theorem toyD_exists_lie_descent (ψ : NontrivialAddChar F) (χ : CentralCharOn (𝕋)) :
    ∃ Ω : Set ↥(𝕋).G, IsInvariantClopen (𝕋) Ω ∧ (1 : ↥(𝕋).G) ∈ Ω ∧
      ∀ f ∈ ScuspTestFn (𝕋) χ, Function.support f ⊆ Ω →
        ∃ F' : ↥(𝕋).lieZero → ℂ, (𝕋).IsLieScusp F' ∧
          distribJ (𝕋) ψ f = (𝕋).distribJLie ψ F' ∧
          mGeom ψ (𝕋) (thetaF (𝕋) f) = (𝕋).mGeomLie ψ ((𝕋).thetaFLie ψ F') := by
  refine ⟨Set.univ, isInvariantClopen_univ _, trivial, fun f hf _ => ?_⟩
  refine ⟨fun _ => f 1, toyD_isLieScusp _, ?_, ?_⟩
  · rw [toyD_distribJ χ ψ hf.2.1, toyD_distribJLie]
  · rw [toyD_thetaFLie, toyD_mGeomLie, toyD_thetaF_eq hf.1.continuous,
      toyD_mGeom ψ hf.1 (toyD_apply_diag χ hf.2.1)]

end GSpinGGP.AxiomRedTeam
