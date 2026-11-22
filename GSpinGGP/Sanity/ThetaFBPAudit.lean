/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.ThetaFBP
import GSpinGGP.Sanity.WeightedOrbitalAudit

/-!
# Sanity checks for `thetaFBP`

At the toy datum `toyD` (`G = GL₁ × GL₁`, commutative) take the reduced Levi datum with empty flags
(`M = G`).  Then `A_M(F) = G(F)` (`P(g) = 1`), every `x` is regular with `G_x(F) = G(F)`, so
`IsMx L x` holds for every `x` (`x` is elliptic in `M = G`); `A_M(F) ∩ ker H_M` is
`{(c₁, c₂) : |c₁| = |c₂| = 1}`, compact and open, so `d_c t` exists (`exists_isDcMeasure`) and is
the Haar measure giving `O^× × O^×` measure `1`.  The sign is `1`, `D^G = 1`, `v_M = 1`, and
`θ_f(x) = c f(x)` with `c > 0` (`toyD_thetaFBP`): `c` is the mass of the point `G_x(F)\G(F)` for
`dg / d_c t`, i.e. the `Measure.haar`-volume of `O^× × O^×`.  So `IsMx`, `IsDcMeasure` and
`thetaFBP` are not vacuous.  Nothing here uses an axiom.
-/

noncomputable section

open MeasureTheory GSpinGGP.Sanity GSpinGGP.AxiomRedTeam
open scoped ENNReal NNReal

namespace GSpinGGP.GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝕋" => (toyD (F := F))

section Toy

/-- At `toyD`, `A_M(F) = G(F)` for every Levi datum: `P(g) = 1` (`W = 0`, `toyD_specP_snd`). -/
theorem toyD_AMF_eq_top (L : (𝕋).ReducedLeviDatum) : L.AMF = ⊤ := by
  refine eq_top_iff.2 fun g _ => (ReducedLeviDatum.mem_AMF_iff L).2
    ⟨⟨1, rfl, fun j => ?_⟩, ⟨1, rfl, fun j => ?_⟩⟩
  · exact Subsingleton.elim _ _
  · rw [toyD_specP_snd, Pi.one_apply, one_smul]; rfl

theorem toyD_mem_AGx (L : (𝕋).ReducedLeviDatum) (x : ↥(𝕋).G) (a : ↥((𝕋).centG x)) :
    a ∈ L.AGx x := by
  rw [ReducedLeviDatum.mem_AGx, toyD_AMF_eq_top L]; trivial

/-- At `toyD`, `A_{G_x}(F)\G_x(F)` is a point. -/
instance toyD_subsingleton_quot (L : (𝕋).ReducedLeviDatum) (x : ↥(𝕋).G) :
    Subsingleton (CosetSpace (L.AGx x).subtype) := by
  refine ⟨fun a b => ?_⟩
  induction a using CosetSpace.ind with | h a => ?_
  induction b using CosetSpace.ind with | h b => ?_
  rw [CosetSpace.mk_eq_mk_iff, CosetSpace.rel_iff]
  exact ⟨⟨b * a⁻¹, toyD_mem_AGx L x _⟩, by simp⟩

/-- **`L.M = M(x)` at `toyD`** for the datum with `M = G`: every `x` is regular and `G_x(F)/A_M(F)`
is a point. -/
theorem toyD_isMx (L : (𝕋).ReducedLeviDatum) (hM : L.M = ⊤) (x : ↥(𝕋).G) : L.IsMx x where
  regular := by rw [toy_regularSet_eq_univ]; trivial
  mem := by rw [hM]; trivial
  compact := inferInstance

/-- The norm of `detChar` on a scalar: `N(c) = c^n`, `n = dim C(V) > 0`. -/
theorem norm_detChar_eq_one_iff {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {Q : QuadraticForm F V} (g : GSpin Q) {c : F}
    (hc : ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = algebraMap F _ c) :
    ‖((detChar Q g : Fˣ) : F)‖ = 1 ↔ ‖c‖ = 1 := by
  rw [detChar_apply, hc, Algebra.norm_algebraMap, norm_pow]
  exact pow_eq_one_iff_of_nonneg (norm_nonneg _) Module.finrank_pos.ne'

/-- The set `{g ∈ G(F) : |N(g_W)| = |N(g_V)| = 1}`, i.e. `|c₁| = |c₂| = 1`. -/
def toyOneSet : Set ↥(𝕋).G :=
  {g | ‖((detChar (𝕋).QW ((𝕋).fst g) : Fˣ) : F)‖ = 1 ∧
    ‖((detChar (𝕋).QV ((𝕋).snd g) : Fˣ) : F)‖ = 1}

theorem mem_toyOneSet_iff (g : ↥(𝕋).G) :
    g ∈ toyOneSet ↔ ‖(toyScal g).1‖ = 1 ∧ ‖(toyScal g).2‖ = 1 := by
  have h := toyScal_spec g
  rw [Prod.ext_iff] at h
  exact and_congr (norm_detChar_eq_one_iff _ h.1) (norm_detChar_eq_one_iff _ h.2)

theorem isOpen_toyOneSet : IsOpen (toyOneSet (F := F)) := by
  have h := ((IsUltrametricDist.isOpen_sphere (0 : F) one_ne_zero).preimage
      ((continuous_detChar _).comp (𝕋).continuous_fst)).inter
    ((IsUltrametricDist.isOpen_sphere (0 : F) one_ne_zero).preimage
      ((continuous_detChar _).comp (𝕋).continuous_snd))
  convert h using 1
  ext g
  simp [toyOneSet]

theorem isCompact_toyOneSet : IsCompact (toyOneSet (F := F)) := by
  have hcl : IsClosed (toyOneSet (F := F)) :=
    (isClosed_eq (continuous_norm.comp ((continuous_detChar _).comp (𝕋).continuous_fst))
      continuous_const).inter
    (isClosed_eq (continuous_norm.comp ((continuous_detChar _).comp (𝕋).continuous_snd))
      continuous_const)
  set T := LinearMap.toContinuousLinearMap (toyL (F := F))
  refine (isCompact_logNorm_le (F := F) (𝕋).isClosed_G
    (1 + Real.log (max 1 ‖T‖))).of_isClosed_subset hcl fun g hg => ?_
  have hb : ∀ h : ↥(𝕋).G, ‖(toyScal h).1‖ = 1 → ‖(toyScal h).2‖ = 1 →
      ‖toyL (toyScal h)‖ ≤ max 1 ‖T‖ := by
    intro h h1 h2
    have : ‖toyScal h‖ = 1 := by rw [Prod.norm_def, h1, h2, max_self]
    calc ‖toyL (toyScal h)‖ = ‖T (toyScal h)‖ := rfl
      _ ≤ ‖T‖ * ‖toyScal h‖ := T.le_opNorm _
      _ = ‖T‖ := by rw [this, mul_one]
      _ ≤ max 1 ‖T‖ := le_max_right _ _
  obtain ⟨h1, h2⟩ := (mem_toyOneSet_iff g).1 hg
  have i1 : ‖(toyScal g⁻¹).1‖ = 1 := by
    have := toyScal_inv g 0
    simp only [Matrix.cons_val_zero] at this
    rw [this, norm_inv, h1, inv_one]
  have i2 : ‖(toyScal g⁻¹).2‖ = 1 := by
    have := toyScal_inv g 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
    rw [this, norm_inv, h2, inv_one]
  change logNorm F (𝕋).G g ≤ _
  unfold logNorm
  rw [maxNorm_toyD]
  have hle : max 1 (max ‖toyL (toyScal g)‖ ‖toyL (toyScal g⁻¹)‖) ≤ max 1 ‖T‖ :=
    max_le (le_max_left _ _) (max_le (hb g h1 h2) (hb g⁻¹ i1 i2))
  have := Real.log_le_log (zero_lt_one.trans_le (le_max_left _ _)) hle
  linarith

/-- The embedding `A_{G_x}(F) → G(F)`. -/
def toyEmb (L : (𝕋).ReducedLeviDatum) (x : ↥(𝕋).G) : ↥(L.AGx x) → ↥(𝕋).G :=
  fun a => ((a : ↥((𝕋).centG x)) : ↥(𝕋).G)

theorem isClosedEmbedding_toyEmb (L : (𝕋).ReducedLeviDatum) (x : ↥(𝕋).G) :
    Topology.IsClosedEmbedding (toyEmb L x) :=
  ((𝕋).isClosedEmbedding_centG x).comp (L.isClosedEmbedding_AGx x)

/-- For empty flags, `A_M(F) ∩ ker H_M` is `{|c₁| = |c₂| = 1}`. -/
theorem toyD_AGxOne_eq (L : (𝕋).ReducedLeviDatum) (hW : L.FW.len = 0) (hV : L.FV.len = 0)
    (x : ↥(𝕋).G) :
    (L.AGxOne x : Set ↥(L.AGx x)) = toyEmb L x ⁻¹' toyOneSet := by
  ext a
  simp only [SetLike.mem_coe, ReducedLeviDatum.mem_AGxOne, Set.mem_preimage, toyOneSet,
    Set.mem_ofPred_eq]
  rw [funext_iff]
  simp only [ReducedLeviDatum.HM, Pi.zero_apply]
  have hpos : ∀ y : Fˣ, Real.log ‖(y : F)‖ = 0 ↔ ‖(y : F)‖ = 1 := fun y => by
    rw [Real.log_eq_zero]
    have := norm_pos_iff.2 y.ne_zero
    constructor
    · rintro (h | h | h) <;> [linarith; exact h; linarith]
    · intro h; exact Or.inr (Or.inl h)
  constructor
  · intro h
    exact ⟨(hpos _).1 (h (Sum.inl (Sum.inr ()))), (hpos _).1 (h (Sum.inr (Sum.inr ())))⟩
  · rintro ⟨h1, h2⟩ c
    rcases c with (i | _) | (i | _)
    · exact absurd (i.isLt.trans_eq hW) (Nat.not_lt_zero _)
    · exact (hpos _).2 h1
    · exact absurd (i.isLt.trans_eq hV) (Nat.not_lt_zero _)
    · exact (hpos _).2 h2

theorem toyD_exists_isDcMeasure (L : (𝕋).ReducedLeviDatum) (hM : L.M = ⊤) (hW : L.FW.len = 0)
    (hV : L.FV.len = 0) (x : ↥(𝕋).G) : ∃ μ, L.IsDcMeasure x μ := by
  have := (toyD_isMx L hM x).compact
  refine ReducedLeviDatum.exists_isDcMeasure (toyD_isMx L hM x).regular ?_ ?_
  · rw [toyD_AGxOne_eq L hW hV]
    exact isOpen_toyOneSet.preimage (isClosedEmbedding_toyEmb L x).continuous
  · rw [toyD_AGxOne_eq L hW hV]
    exact (isClosedEmbedding_toyEmb L x).isCompact_preimage isCompact_toyOneSet

end Toy

/-- **`θ_f(x) = c f(x)` at `toyD`, with `c > 0`**, for the datum with `M = G` (empty flags), which
is `M(x)` for every `x`; `d_c t` exists at every `x`. -/
theorem toyD_thetaFBP :
    ∃ (L : (𝕋).ReducedLeviDatum) (K : (𝕋).GoodK L.toFlagLeviDatum),
      (∀ x, L.IsMx x) ∧ (∀ x, L.IsDcMeasure x (L.dcMeasure x)) ∧
      ∀ x : ↥(𝕋).G, ∃ c : ℝ, 0 < c ∧ ∀ f : ↥(𝕋).G → ℂ, L.thetaFBP K f x = c * f x := by
  classical
  obtain ⟨ιW, _, _, bW, wtW, hsW⟩ := exists_flagSplitting (𝕋).nondeg (emptyFlag (𝕋).QW)
  obtain ⟨ιV, _, _, bV, wtV, hsV⟩ := exists_flagSplitting (𝕋).nondeg_QV (emptyFlag (𝕋).QV)
  have hW1 : Module.finrank F (Fin (𝕋).m → F) ≤ 1 := by
    rw [Module.finrank_fin_fun]; simp [toyD]
  have hV1 : Module.finrank F (𝕋).V ≤ 1 := by
    simp only [GGPData.V]
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]; simp [toyD]
  let L : (𝕋).ReducedLeviDatum :=
    { FW := emptyFlag _, FV := emptyFlag _, ιW := ιW, ιV := ιV, bW := bW, wtW := wtW, bV := bV,
      wtV := wtV, hsW := hsW, hsV := hsV
      reducedW := not_isHypPlane_comp_of_finrank_le _ _ hW1
      reducedV := not_isHypPlane_comp_of_finrank_le _ _ hV1 }
  have hM := L.M_eq_top_of_len_eq_zero rfl rfl
  have hG := L.aG_eq_top_of_len_eq_zero rfl rfl
  let K : (𝕋).GoodK L.toFlagLeviDatum := GoodK.ofEqTop hM toyXiPair.K toyXiPair.isOpen_K
    toyXiPair.isCompact_K (toyD_stabilizesSplitLattice _ _).1 (toyD_stabilizesSplitLattice _ _).2
  have hdc : ∀ x, L.IsDcMeasure x (L.dcMeasure x) := fun x =>
    ReducedLeviDatum.isDcMeasure_dcMeasure (toyD_exists_isDcMeasure L hM rfl rfl x)
  refine ⟨L, K, toyD_isMx L hM, hdc, fun x => ?_⟩
  have := (hdc x).1
  -- `d_c t = s • Measure.haar`
  have e := Measure.isMulLeftInvariant_eq_smul (L.dcMeasure x) Measure.haar
  rw [ENNReal.smul_def] at e
  set s : ℝ≥0∞ := (Measure.haarScalarFactor (L.dcMeasure x) Measure.haar : ℝ≥0∞)
  have hs0 : s ≠ 0 := ENNReal.coe_ne_zero.2
    (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  have hs : s ≠ ⊤ := ENNReal.coe_ne_top
  obtain ⟨c, hc, hJ⟩ := toyD_orbitalIntegral x
  refine ⟨(s⁻¹).toReal * c, mul_pos (ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 hs)
    (ENNReal.inv_ne_top.2 hs0)) hc, fun f => ?_⟩
  have : Subsingleton L.aMG := Submodule.Quotient.subsingleton_iff.2 hG
  unfold ReducedLeviDatum.thetaFBP
  rw [Module.finrank_zero_of_subsingleton, pow_zero, one_mul, toyD_weylDisc, Real.sqrt_one,
    Complex.ofReal_one, inv_one, one_mul, e, weightedOrbitalIntegral_smul_measure _ hs0 hs,
    weightedOrbitalIntegral_eq_orbitalIntegral_of_aG_eq_top hG, hJ]
  push_cast
  ring

end GSpinGGP.GGPData
