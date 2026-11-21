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
import GSpinGGP.TraceFormula.Scusp
import GSpinGGP.TraceFormula.Spectral
import GSpinGGP.GGP.MultOne

/-!
# Whole-system checks on the toy datum

On `toyD` (`W = 0`, `V` a line, `G ≅ F^× × F^×`) several axioms and several `sorry` statements on
the path of the main theorem meet the definitions in one instance.

* **The multiplicity formula for `π = 1`**, both sides computed separately
  (`toyD_multFormula_trivialRep`): `m(1) = 1` from the definition and `emoryTakeda_mult_le_one`;
  `θ_1(1) = 1` from `rodier_germ_one` and `hc_character_isQuasiCharacter`; `m_geom(θ) = θ(1)` for
  every `θ ∈ QC(χ)` from the definitions.  In all it uses the axioms `panYan_mult_le_one`,
  `flath_tensor_decomposition`, `cartier_smoothVectors_dense_admissible` (through the theorem
  `emoryTakeda_mult_le_one`), `rodier_germ_one`, `hc_character_exists_admissible`,
  `hc_character_isQuasiCharacter_admissible`, `hc_regular_open_dense_conull`,
  `jantzen_finrank_soCentMat_ge` (the last three through
  `charG_mem_QC`) and `exists_isSelfDual`.
* **`sorry` statements, conclusions proved at `toyD`** without them:
  `tendsto_mGeomS_of_mem_QC` and `germ_bound_of_mem_QC` for every `θ ∈ QC(χ)`
  (`toyD_tendsto_mGeomS_of_mem_QC`, `toyD_germ_bound_of_mem_QC`) and for `θ = θ_f`
  (`toyD_tendsto_mGeomS_thetaF`, `toyD_germ_bound_thetaF`); `kernelK_bound_scusp` for every
  Iwasawa datum (`toyD_kernelK_bound_scusp`; on the way `Ξ^G ≡ 1`, `Ξ^{H\G} ≡ 1`);
  `locallyIntegrable_absF_det_adV_rpow` at `a = 0` for every `d` (`locallyIntegrable_det_adV_rpow_zero`;
  the conclusion of `bp_integrable_deltaGGP_rpow`, now proved from it, is also checked at `toyD`:
  `toyD_bp_integrable`); `exists_lie_descent` with `Ω = G` (`toyD_exists_lie_descent`).
  `exists_good_nhd_of_not_nearCentral` and `mult_parInd_eq_mGeom` are vacuous there
  (`toyD_isNearCentral`, `toyD_not_isTempIndData`).
  The conclusion of `prop_6_7_1_iii` (now proved) is also checked
  there (`toyD_prop_6_7_1_iii`).
  `LitTF.exists_isCompact_ellRegSet_modConjAG` and `LitTF.exists_scuspSurjOn_nhd_ell` (the two
  `sorry` statements behind `bp_scusp_surj_ell`): conclusions proved at `toyD`
  (`toyD_exists_isCompact_ellRegSet_modConjAG`, `toyD_exists_scuspSurjOn_nhd_ell`, via
  `toyD_isLocallyConstant_of_isQC`), and both shown to follow from the conclusion of
  `bp_scusp_surj_ell` for every `d` (so they are no stronger than it).

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
`m(1) = 1 = m_geom(θ_1)`.  Axioms used: `panYan_mult_le_one`, `flath_tensor_decomposition`,
`cartier_smoothVectors_dense_admissible`, `rodier_germ_one`, `hc_character_exists_admissible`,
`hc_character_isQuasiCharacter_admissible`, `hc_regular_open_dense_conull`,
`jantzen_finrank_soCentMat_ge`, `exists_isSelfDual`. -/
theorem toyD_multFormula_trivialRep (ψ : NontrivialAddChar F) :
    ((mult ψ (𝕋) (trivialRep ↥(𝕋).G)).toNat : ℂ) =
      mGeom ψ (𝕋) (charG (𝕋) (trivialRep ↥(𝕋).G)) := by
  rw [toyD_mGeom_of_QC ψ (charG_mem_QC (𝕋) toyD_trivialRep_isTempCC),
    toyD_charG_trivialRep_one ψ, toyD_mult_trivialRep ψ]
  simp

/-! ## `kernelK_bound_scusp` -/

theorem toyD_xiHC (IW : (𝕋).IwasawaDatum) (g : ↥(𝕋).G) : IW.xiHC g = 1 := by
  have hδ : ∀ x : ↥(𝕋).G, IW.toIwasawaPair.rho x = 1 := fun x =>
    IW.toIwasawaPair.delta_eq_one_of_central _ fun y => Subtype.ext (by
      simp only [Subgroup.coe_mul]; exact toyD_G_comm _ _)
  unfold GGPData.IwasawaDatum.xiHC IwasawaPair.xi
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

/-- Conclusion of `locallyIntegrable_absF_det_adV_rpow` at `a = 0`, for every `d`, `x` and
`t₀ ∈ T_x` (the function is `≡ 1`), proved directly (it was a `sorry` statement when this check
was added). -/
theorem locallyIntegrable_det_adV_rpow_zero (d : GGPData F) {x t₀ : ↥(GSpin d.QW)}
    (ht₀ : t₀ ∈ d.torusOf x) (μ : Measure ↥(d.lieTorus (d.torusOf x))) [μ.IsAddHaarMeasure] :
    LocallyIntegrable (fun X : ↥(d.lieTorus (d.torusOf x)) =>
      absF (LinearMap.det ((adV d.QW (X : CliffordAlgebra d.QW)).restrict
        (d.adV_mapsTo_movedSub_inf_ker ht₀ X))) ^ (0 : ℝ)) μ := by
  letI := isTopologicalRing_of_moduleTopology F (CliffordAlgebra d.QW)
  haveI := t2Space_of_moduleTopology F (CliffordAlgebra d.QW)
  haveI := submodule_isTopologicalAddGroup (d.lieTorus (d.torusOf x))
  obtain ⟨_, _, _, _, _⟩ := submodule_topology (d.lieTorus (d.torusOf x))
  simp only [Real.rpow_zero]
  exact locallyIntegrable_const 1

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

/-! ## `bp_scusp_surj_ell` and its two `sorry` statements at `toyD` -/

/-- On `toyD` every quasi-character is locally constant. -/
theorem toyD_isLocallyConstant_of_isQC (ψ : NontrivialAddChar F) {θ : ↥(𝕋).G → ℂ}
    (hθ : IsQuasiCharacter (𝕋).G (𝕋).lie (𝕋).bilin ψ θ) : IsLocallyConstant θ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hss : IsSS F ((x : (𝕋).ambientˣ) : (𝕋).ambient) :=
    (show x ∈ regularSet (𝕋).G (𝕋).lie by rw [toy_regularSet_eq_univ]; trivial).1
  obtain ⟨c, hc⟩ := hθ.2 x hss
  have hcx := toyD_expansion_coeff ψ θ x c hc
  have hL : (lieCentralizer (𝕋).lie ((x : (𝕋).ambientˣ) : (𝕋).ambient)) ≤ (𝕋).lie := inf_le_left
  haveI : Subsingleton (NilOrbit (grpCentralizer (𝕋).G (x : (𝕋).ambientˣ))
      (lieCentralizer (𝕋).lie ((x : (𝕋).ambientˣ) : (𝕋).ambient))) :=
    ⟨fun a b => (toyD_nilOrbit_eq_zero _ _ hL a).trans (toyD_nilOrbit_eq_zero _ _ hL b).symm⟩
  have hsd : ∃ μ, IsSelfDual μ (restrictForm (lieCentralizer (𝕋).lie
      ((x : (𝕋).ambientˣ) : (𝕋).ambient)) (𝕋).bilin) ψ := by
    rw [toy_lieCentralizer_eq]
    exact exists_isSelfDual_toyLie ψ
  obtain ⟨-, ω, hω, hexp⟩ := hc
  obtain ⟨log, hlc, hl1, hle⟩ := exists_logA F (A := (𝕋).ambient)
  set u : ↥(𝕋).G → (𝕋).ambient := fun y =>
    (((x : (𝕋).ambientˣ)⁻¹ : (𝕋).ambientˣ) : (𝕋).ambient) * ((y : (𝕋).ambientˣ) : (𝕋).ambient)
    with hu
  have hucont : Continuous u :=
    continuous_const.mul (Units.continuous_val.comp continuous_subtypeVal)
  have hu1 : Tendsto u (𝓝 x) (𝓝 1) := by
    have : u x = 1 := by simp [hu]
    simpa [this] using hucont.tendsto x
  have hlog0 : Tendsto (fun y => log (u y)) (𝓝 x) (𝓝 0) := by
    have := hlc.tendsto.comp hu1
    rwa [hl1] at this
  filter_upwards [hu1.eventually hle, hlog0.eventually hω,
    hlog0.eventually (eventually_mem_lie_of_expA_mem (F := F) (𝕋))] with y hy1 hy2 hy3
  have hgu : (((x⁻¹ * y : ↥(𝕋).G) : (𝕋).ambientˣ) : (𝕋).ambient) = expA F (log (u y)) := by
    rw [hy1]; simp [hu]
  have hYlie : log (u y) ∈ (𝕋).lie := hy3 _ hgu
  have hYc : log (u y) ∈ lieCentralizer (𝕋).lie ((x : (𝕋).ambientˣ) : (𝕋).ambient) := by
    rw [toy_lieCentralizer_eq]; exact hYlie
  have hyx : ((y : (𝕋).ambientˣ) : (𝕋).ambient) =
      ((x : (𝕋).ambientˣ) : (𝕋).ambient) * expA F (log (u y)) := by
    rw [hy1]; simp [hu]
  have h := hexp _ hy2 hYc (toyD_isRegularSS _ hL ⟨_, hYc⟩) y hyx
  rw [h, finsum_eq_single _ (zeroOrbit _ _) (fun O' hO' => (hO' (Subsingleton.elim _ _)).elim),
    jHat_zeroOrbit_eq_one _ _ _ ψ hsd (toyD_isRegularSS _ hL) hYc, mul_one, hcx]

/-- **The conclusion of `exists_scuspSurjOn_nhd_ell` holds at `toyD`** (with `U = G`). -/
theorem toyD_exists_scuspSurjOn_nhd_ell (g : ↥(𝕋).G) :
    ∃ U : Set ↥(𝕋).G, IsOpen U ∧ IsClosed U ∧ (∀ x y : ↥(𝕋).G, y ∈ U → x * y * x⁻¹ ∈ U) ∧
      (∀ (a : ↥(𝕋).AG) (y : ↥(𝕋).G), y ∈ U → (a : ↥(𝕋).G) * y ∈ U) ∧ g ∈ U ∧
      (∃ C : Set ↥(𝕋).G, IsCompact C ∧
        ∀ y ∈ U, ∃ (a : ↥(𝕋).AG) (x c : ↥(𝕋).G), c ∈ C ∧ y = (a : ↥(𝕋).G) * (x * c * x⁻¹)) ∧
      LitTF.ScuspSurjOn (𝕋) U := by
  refine ⟨Set.univ, isOpen_univ, isClosed_univ, fun _ _ _ => trivial, fun _ _ _ => trivial,
    trivial, ⟨{1}, isCompact_singleton, fun y _ => ⟨⟨y, by rw [toyD_AG_eq_top]; trivial⟩, 1, 1,
      rfl, by simp⟩⟩, ?_⟩
  rintro θ₀ hq ⟨C₀, hC₀, -, hsupp⟩
  obtain ⟨ψ₀⟩ := nonempty_nontrivialAddChar (F := F)
  have hlc := toyD_isLocallyConstant_of_isQC ψ₀ (hq ψ₀)
  have hsub : Function.support θ₀ ⊆ C₀ := fun y hy => by
    obtain ⟨x, c, hc, rfl⟩ :=
      hsupp y (by rw [toy_regularSet_eq_univ]; trivial) hy
    rwa [toyD_G_comm x c, mul_inv_cancel_right]
  have hcs : HasCompactSupport θ₀ := by
    refine IsCompact.of_isClosed_subset hC₀ (isClosed_tsupport _) ?_
    have hcl : IsClosed (Function.support θ₀) :=
      isOpen_compl_iff.1 (by rw [Function.compl_support]; exact hlc {0})
    rw [tsupport, hcl.closure_eq]
    exact hsub
  refine ⟨θ₀, ⟨hlc, hcs⟩, fun FW FV hP => (toyD_not_isProperFlagPair FW FV hP).elim,
    Set.subset_univ _, θ₀, ?_⟩
  obtain ⟨h1, h2, h3⟩ := toyD_isThetaF (F := F) hlc.continuous
  exact ⟨h1, h2, fun _ _ => rfl, h3⟩


/-- The conclusion of `exists_isCompact_ellRegSet_modConjAG` holds at `toyD`, with `K = {1}`. -/
theorem toyD_exists_isCompact_ellRegSet_modConjAG :
    ∃ K : Set ↥(𝕋).G, IsCompact K ∧ K ⊆ closure (ellipticRegularSet (𝕋).G (𝕋).lie (𝕋).AG) ∧
      ∀ g ∈ ellipticRegularSet (𝕋).G (𝕋).lie (𝕋).AG,
        ∃ (a : ↥(𝕋).AG) (x c : ↥(𝕋).G), c ∈ K ∧ g = (a : ↥(𝕋).G) * (x * c * x⁻¹) := by
  have hAG : ∀ g : ↥(𝕋).G, g ∈ (𝕋).AG := fun g => by
    rw [toyD_AG_eq_top]; exact Subgroup.mem_top g
  refine ⟨{1}, isCompact_singleton, ?_, fun g _ => ⟨⟨g, hAG g⟩, 1, 1, rfl, by simp⟩⟩
  rintro _ rfl
  have he : (1 : ↥(𝕋).G) ∈ (𝕋).ellRegSet := by
    rw [toyD_ellRegSet]; trivial
  exact subset_closure he

/-- The two `sorry` statements behind `bp_scusp_surj_ell` are no stronger than that theorem
(whose statement is unchanged): its conclusion implies `exists_scuspSurjOn_nhd_ell` (take
`U = Ω`, closed, so it contains the closure of the elliptic set). -/
example (d : GGPData F) (h : type_of% (LitTF.bp_scusp_surj_ell d)) {g : ↥d.G}
    (hg : g ∈ closure (ellipticRegularSet d.G d.lie d.AG)) :
    type_of% (LitTF.exists_scuspSurjOn_nhd_ell d hg) := by
  obtain ⟨Ω, ho, hc, hconj, hAG, hell, hC, hs⟩ := h
  exact ⟨Ω, ho, hc, hconj, hAG, closure_minimal hell hc hg, hC, hs⟩

/-- ... and implies `exists_isCompact_ellRegSet_modConjAG` (`K = C ∩ cl(G_ell,reg)`, using the
stability of `G_ell,reg(F)` under conjugation and `A_G(F)`). -/
example (d : GGPData F) (h : type_of% (LitTF.bp_scusp_surj_ell d)) :
    type_of% (LitTF.exists_isCompact_ellRegSet_modConjAG d) := by
  obtain ⟨Ω, -, hc, -, -, hell, ⟨C, hC, hCov⟩, -⟩ := h
  refine ⟨C ∩ closure (ellipticRegularSet d.G d.lie d.AG), hC.inter_right isClosed_closure,
    Set.inter_subset_right, fun g hg => ?_⟩
  obtain ⟨a, x, c, hcC, rfl⟩ := hCov g (hell hg)
  refine ⟨a, x, c, ⟨hcC, subset_closure ?_⟩, rfl⟩
  have h2 := conj_mem_ellRegSet d x⁻¹ (mul_mem_ellRegSet_of_mem_AG d a⁻¹ hg)
  have e : x⁻¹ * (((a⁻¹ : ↥d.AG) : ↥d.G) * ((a : ↥d.G) * (x * c * x⁻¹))) * x⁻¹⁻¹ = c := by
    rw [Subgroup.coe_inv]; group
  rw [e] at h2
  exact h2

end GSpinGGP.AxiomRedTeam
