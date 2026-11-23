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
`{(c₁, c₂) : |c₁| = |c₂| = 1}` (`toyD_AGxOne_eq`), so `d_c t` exists (`IsMx.exists_isDcMeasure`) and is
the Haar measure giving `O^× × O^×` measure `1`.  The sign is `1`, `D^G = 1`, `v_M = 1`, and
`θ_f(x) = c f(x)` with `c = Measure.haar(O^× × O^×) > 0` (`toyD_thetaFBP`): `c` is the mass of the
point `G_x(F)\G(F)` for `dg / d_c t` (`toyD_orbQuotMeasure_dc`), which tests the normalization
`d_c a(A¹) = 1`.  So `IsMx`, `IsDcMeasure` and `thetaFBP` are not vacuous.  No new axioms; the
literature axiom `weil_quotient_radon` is used (existence of the quotient measures).
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

theorem isClosed_toyOneSet : IsClosed (toyOneSet (F := F)) :=
  (isClosed_eq (continuous_norm.comp ((continuous_detChar _).comp (𝕋).continuous_fst))
    continuous_const).inter
  (isClosed_eq (continuous_norm.comp ((continuous_detChar _).comp (𝕋).continuous_snd))
    continuous_const)

theorem isCompact_toyOneSet : IsCompact (toyOneSet (F := F)) := by
  have hcl := isClosed_toyOneSet (F := F)
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

theorem toyD_exists_isDcMeasure (L : (𝕋).ReducedLeviDatum) (hM : L.M = ⊤) (x : ↥(𝕋).G) :
    ∃ μ, L.IsDcMeasure x μ :=
  (toyD_isMx L hM x).exists_isDcMeasure

end Toy

/-- The indicator of a compact clopen set is continuous with compact support. -/
theorem continuous_indicator_one_of_isClopen {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsClopen S) : Continuous (S.indicator (1 : X → ℝ)) := by
  classical
  refine continuous_def.2 fun U _ => ?_
  have : S.indicator (1 : X → ℝ) ⁻¹' U = (if (1 : ℝ) ∈ U then S else ∅) ∪
      (if (0 : ℝ) ∈ U then Sᶜ else ∅) := by
    ext y
    by_cases hy : y ∈ S <;> by_cases h1 : (1 : ℝ) ∈ U <;> by_cases h0 : (0 : ℝ) ∈ U <;>
      simp [hy, h1, h0]
  rw [this]
  refine IsOpen.union ?_ ?_ <;> split_ifs
  exacts [hS.isOpen, isOpen_empty, hS.compl.isOpen, isOpen_empty]

theorem hasCompactSupport_indicator_one {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsCompact S) (hc : IsClosed S) : HasCompactSupport (S.indicator (1 : X → ℝ)) :=
  HasCompactSupport.intro' hS hc fun _ hy => Set.indicator_of_notMem hy _

theorem one_mem_toyOneSet : (1 : ↥(𝕋).G) ∈ toyOneSet := by
  simp [toyOneSet]

/-- **At `toyD`, `d_c t` and the quotient measure are pinned down**: for `x ∈ G(F)`,
`d_c t` gives `{t ∈ G_x(F) : |c₁(t)| = |c₂(t)| = 1}` measure `1` (the quotient `A\G_x` is a point
of mass `1` and `d_c a(A¹) = 1`), and the point `G_x(F)\G(F)` has `dg/d_c t`-mass
`Measure.haar(toyOneSet)`. -/
theorem toyD_orbQuotMeasure_dc (L : (𝕋).ReducedLeviDatum) (hW : L.FW.len = 0)
    (hV : L.FV.len = 0) (x : ↥(𝕋).G) (hdc : L.IsDcMeasure x (L.dcMeasure x)) :
    ((𝕋).orbQuotMeasure x (L.dcMeasure x)).real Set.univ =
      (Measure.haar : Measure ↥(𝕋).G).real toyOneSet := by
  classical
  have hx : x ∈ regularSet (𝕋).G (𝕋).lie := by rw [toy_regularSet_eq_univ]; trivial
  obtain ⟨hμ, μA, mW, hA, hA1, hW', hm1⟩ := hdc
  have := isMulRightInvariant_of_le_centG hx (L.AGx x) μA
  have := isMulRightInvariant_of_mem_regularSet hx (L.dcMeasure x)
  set S : Set ↥(𝕋).G := toyOneSet
  have hSc : IsClopen S := ⟨isClosed_toyOneSet, isOpen_toyOneSet⟩
  set ST : Set ↥((𝕋).centG x) := (fun t => (t : ↥(𝕋).G)) ⁻¹' S
  have hSTc : IsClopen ST := hSc.preimage continuous_subtypeVal
  have hSTk : IsCompact ST := ((𝕋).isClosedEmbedding_centG x).isCompact_preimage isCompact_toyOneSet
  -- step 1: `d_c t (ST) = 1`
  have hA1' : μA.real ((fun a : ↥(L.AGx x) => (a : ↥((𝕋).centG x))) ⁻¹' ST) = 1 := by
    have e : ((fun a : ↥(L.AGx x) => (a : ↥((𝕋).centG x))) ⁻¹' ST) =
        (L.AGxOne x : Set ↥(L.AGx x)) := by
      rw [toyD_AGxOne_eq L hW hV x]; rfl
    rw [e, Measure.real, hA1, ENNReal.toReal_one]
  have hT1 : (L.dcMeasure x).real ST = 1 := by
    have h := hW' (ST.indicator (1 : ↥((𝕋).centG x) → ℝ))
      (continuous_indicator_one_of_isClopen hSTc)
      (hasCompactSupport_indicator_one hSTk hSTc.isClosed)
    rw [integral_indicator_one hSTc.isClosed.measurableSet] at h
    rw [h]
    have hin : ∀ q : CosetSpace (L.AGx x).subtype,
        ∫ a, ST.indicator (1 : ↥((𝕋).centG x) → ℝ) ((L.AGx x).subtype a * CosetSpace.out _ q)
          ∂μA = 1 := by
      intro q
      set o : ↥(L.AGx x) := ⟨CosetSpace.out _ q, toyD_mem_AGx L x _⟩
      have e : ∀ a : ↥(L.AGx x), ST.indicator (1 : ↥((𝕋).centG x) → ℝ) ((L.AGx x).subtype a *
          CosetSpace.out _ q) = ((fun a : ↥(L.AGx x) => (a : ↥((𝕋).centG x))) ⁻¹' ST).indicator
          (1 : ↥(L.AGx x) → ℝ) (a * o) := fun a => rfl
      simp_rw [e]
      rw [integral_mul_right_eq_self (fun a => ((fun a : ↥(L.AGx x) =>
        (a : ↥((𝕋).centG x))) ⁻¹' ST).indicator (1 : ↥(L.AGx x) → ℝ) a) o,
        integral_indicator_one ((hSTc.isClosed.preimage continuous_subtypeVal).measurableSet),
        hA1']
    simp_rw [hin]
    rw [integral_const, smul_eq_mul, mul_one, Measure.real, hm1, ENNReal.toReal_one]
  -- step 2: the mass of the point `G_x(F)\G(F)`
  have hW2 := (𝕋).orbQuotMeasure_spec (x := x) (L.dcMeasure x)
  have h := hW2 (S.indicator (1 : ↥(𝕋).G → ℝ)) (continuous_indicator_one_of_isClopen hSc)
    (hasCompactSupport_indicator_one isCompact_toyOneSet hSc.isClosed)
  rw [integral_indicator_one hSc.isClosed.measurableSet] at h
  rw [h]
  have hin : ∀ q : (𝕋).CentQuot x,
      ∫ t, S.indicator (1 : ↥(𝕋).G → ℝ) (((𝕋).centG x).subtype t * CosetSpace.out _ q)
        ∂(L.dcMeasure x) = 1 := by
    intro q
    set o : ↥((𝕋).centG x) := ⟨CosetSpace.out _ q, by simp [toyD_centG_eq_top]⟩
    have e : ∀ t : ↥((𝕋).centG x), S.indicator (1 : ↥(𝕋).G → ℝ) (((𝕋).centG x).subtype t *
        CosetSpace.out _ q) = ST.indicator (1 : ↥((𝕋).centG x) → ℝ) (t * o) := fun t => rfl
    simp_rw [e]
    rw [integral_mul_right_eq_self (fun t => ST.indicator (1 : ↥((𝕋).centG x) → ℝ) t) o,
      integral_indicator_one hSTc.isClosed.measurableSet, hT1]
  simp_rw [hin]
  rw [integral_const, smul_eq_mul, mul_one]

/-- **`θ_f(x) = c f(x)` at `toyD`, with `c = Measure.haar({|c₁| = |c₂| = 1}) > 0`**, for the datum
with `M = G` (empty flags), which is `M(x)` for every `x`; `d_c t` exists at every `x`.  The
constant is the `dg`-volume of the maximal compact subgroup `A_G(O)`, as `d_c t` gives it mass
`1`: so `θ_f` depends on the normalization of `dg` exactly as stated in `thetaFBP`'s docstring. -/
theorem toyD_thetaFBP :
    ∃ (L : (𝕋).ReducedLeviDatum) (K : (𝕋).GoodK L.toFlagLeviDatum),
      (∀ x, L.IsMx x) ∧ (∀ x, L.IsDcMeasure x (L.dcMeasure x)) ∧
      0 < (Measure.haar : Measure ↥(𝕋).G).real toyOneSet ∧
      ∀ (x : ↥(𝕋).G) (f : ↥(𝕋).G → ℂ),
        L.thetaFBP K f x = (Measure.haar : Measure ↥(𝕋).G).real toyOneSet * f x := by
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
    ReducedLeviDatum.isDcMeasure_dcMeasure (toyD_exists_isDcMeasure L hM x)
  refine ⟨L, K, toyD_isMx L hM, hdc, ?_, fun x f => ?_⟩
  · exact ENNReal.toReal_pos (isOpen_toyOneSet.measure_pos _ ⟨1, one_mem_toyOneSet⟩).ne'
      isCompact_toyOneSet.measure_lt_top.ne
  have := (hdc x).1
  have := isMulRightInvariant_of_mem_regularSet
    (show x ∈ regularSet (𝕋).G (𝕋).lie by rw [toy_regularSet_eq_univ]; trivial) (L.dcMeasure x)
  have : Subsingleton L.aMG := Submodule.Quotient.subsingleton_iff.2 hG
  have hpt : ∀ q : (𝕋).CentQuot x,
      f ((CosetSpace.out _ q)⁻¹ * x * CosetSpace.out _ q) = f x := fun q => by
    rw [mul_assoc, toyD_G_comm x, inv_mul_cancel_left]
  rw [ReducedLeviDatum.thetaFBP_of_aG_eq_top_eq_integral hG]
  simp_rw [hpt]
  rw [integral_const, toyD_orbQuotMeasure_dc L rfl rfl x (hdc x), Complex.real_smul]

end GSpinGGP.GGPData
