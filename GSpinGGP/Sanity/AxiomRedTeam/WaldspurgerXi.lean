/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Sanity.AxiomRedTeam.Tits
import GSpinGGP.Literature.WaldspurgerXi
import GSpinGGP.HarmonicAnalysis.PolynomialGrowth
import GSpinGGP.HarmonicAnalysis.LatticeGrowth
import GSpinGGP.Foundations.LogNormCompact

/-!
# Check of `exists_iwasawaPair_xi_sq_integrable`

(V) at the toy datum `toyD` (`W = 0`, `V` a line, `G ≅ F^× × F^×`): the hypotheses hold (the empty
flags are full, `toyD_xi_sq_integrable_hyps`) and the conclusion is proved without the axiom
(`toyD_exists_iwasawaPair_xi_sq_integrable`):

* `G` is abelian, so `δ_P = 1` and `Ξ ≡ 1` for the Iwasawa pair `(G, K)`, `K` a lattice stabilizer
  (`toyXiPair_xi_eq_one`);
* every `g ∈ G` is a pair of scalars `(c₁, c₂)`, and `|log |cᵢ|| ≤ σ(g) + C`; two elements with the
  same coordinates `⌊log |cᵢ|⌋` differ by an element of a fixed log-norm ball. So `G` has polynomial
  growth of degree `2` (`exists_finset_cover_of_intCoord`), and `σ^{-d}` is integrable for `d > 3`
  (`IsInvariantQuotient.integrable_relXi_sq_rpow_neg` for `π = id`);
* `1 + log entryMaxNorm b ≥ σ / C'` (`logNorm_equiv_entryMaxNorm`).

Not covered: nonabelian `G`, proper `P₀`, where `Ξ` is not constant.
-/

noncomputable section

open MeasureTheory GSpinGGP.Sanity

namespace GSpinGGP.AxiomRedTeam

set_option linter.unusedSectionVars false

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝕋" => (toyD (F := F))

/-- Every element of `G` at `toyD` is a pair of scalars. -/
theorem toyD_exists_scalar (g : ↥(𝕋).G) : ∃ c : F × F,
    ((g : (𝕋).ambientˣ) : (𝕋).ambient) =
      (algebraMap F (CliffordAlgebra (𝕋).QW) c.1, algebraMap F (CliffordAlgebra (𝕋).QV) c.2) := by
  obtain ⟨c₁, h₁⟩ := toy_cliffW_scalar (K := F)
    (((g : (𝕋).ambientˣ) : (𝕋).ambient).1)
  obtain ⟨c₂, h₂⟩ := toy_cliffV_even_scalar (K := F)
    (((g : (𝕋).ambientˣ) : (𝕋).ambient).2)
    (mem_evenOdd_zero_of_mem_GSpin ((𝕋).snd g))
  exact ⟨(c₁, c₂), Prod.ext h₁ h₂⟩

/-- The scalars of `g`. -/
def toyScal (g : ↥(𝕋).G) : F × F := (toyD_exists_scalar g).choose

theorem toyScal_spec (g : ↥(𝕋).G) : ((g : (𝕋).ambientˣ) : (𝕋).ambient) =
    (algebraMap F (CliffordAlgebra (𝕋).QW) (toyScal g).1,
      algebraMap F (CliffordAlgebra (𝕋).QV) (toyScal g).2) :=
  (toyD_exists_scalar g).choose_spec

/-- `c ↦ (c₁, c₂)` as a linear map `F × F → C(W) × C(V)`. -/
def toyIota : F × F →ₗ[F] (𝕋).ambient :=
  (Algebra.linearMap F (CliffordAlgebra (𝕋).QW)).prodMap
    (Algebra.linearMap F (CliffordAlgebra (𝕋).QV))

theorem toyIota_apply (c : F × F) : toyIota c =
    (algebraMap F (CliffordAlgebra (𝕋).QW) c.1, algebraMap F (CliffordAlgebra (𝕋).QV) c.2) := rfl

theorem toyIota_injective : Function.Injective (toyIota (F := F)) := by
  intro a b h
  rw [toyIota_apply, toyIota_apply, Prod.ext_iff] at h
  exact Prod.ext (algebraMap_cliff_injective _ h.1) (algebraMap_cliff_injective _ h.2)

theorem toyScal_spec' (g : ↥(𝕋).G) :
    ((g : (𝕋).ambientˣ) : (𝕋).ambient) = toyIota (toyScal g) := toyScal_spec g

/-- `c ↦ L_{(c₁, c₂)}`. -/
def toyL : F × F →ₗ[F] ((Fin (Module.finrank F (toyD (F := F)).ambient) → F) →L[F]
    (Fin (Module.finrank F (toyD (F := F)).ambient) → F)) := (lmulPiₗ F).comp toyIota

theorem toyL_apply (c : F × F) : toyL c = lmulPi F (toyIota c) := rfl

theorem toyL_injective : Function.Injective (toyL (F := F)) := by
  intro a b h
  apply toyIota_injective
  have := congrArg (lmulPiInv F) h
  rwa [toyL_apply, toyL_apply, lmulPiInv_lmulPi, lmulPiInv_lmulPi] at this

theorem toyIota_mul (a b : F × F) : toyIota (a * b) = toyIota a * toyIota b := by
  simp only [toyIota_apply, Prod.fst_mul, Prod.snd_mul, map_mul, Prod.mk_mul_mk]

theorem toyIota_one : toyIota (1 : F × F) = 1 := by
  simp only [toyIota_apply, Prod.fst_one, Prod.snd_one, map_one, Prod.mk_one_one]

theorem toyScal_mul (g h : ↥(𝕋).G) : toyScal (g * h) = toyScal g * toyScal h := by
  apply toyIota_injective
  rw [toyIota_mul, ← toyScal_spec', ← toyScal_spec', ← toyScal_spec']
  rfl

theorem toyScal_one : toyScal (1 : ↥(𝕋).G) = 1 := by
  apply toyIota_injective
  rw [toyIota_one, ← toyScal_spec']
  rfl

theorem toyScal_inv_mul (g : ↥(𝕋).G) : toyScal g⁻¹ * toyScal g = 1 := by
  rw [← toyScal_mul, inv_mul_cancel, toyScal_one]

theorem toyScal_ne_zero (g : ↥(𝕋).G) (i : Fin 2) : ![(toyScal g).1, (toyScal g).2] i ≠ 0 := by
  have h := toyScal_inv_mul g
  rw [Prod.ext_iff] at h
  fin_cases i
  · exact right_ne_zero_of_mul_eq_one h.1
  · exact right_ne_zero_of_mul_eq_one h.2

theorem toyScal_inv (g : ↥(𝕋).G) (i : Fin 2) :
    ![(toyScal g⁻¹).1, (toyScal g⁻¹).2] i = (![(toyScal g).1, (toyScal g).2] i)⁻¹ := by
  have h := toyScal_inv_mul g
  rw [Prod.ext_iff] at h
  fin_cases i
  · exact eq_inv_of_mul_eq_one_left h.1
  · exact eq_inv_of_mul_eq_one_left h.2

/-- The coordinates `(c₁, c₂)` of `g`, indexed by `Fin 2`. -/
def toyCoord (g : ↥(𝕋).G) (i : Fin 2) : F := ![(toyScal g).1, (toyScal g).2] i

theorem norm_toyCoord_le (g : ↥(𝕋).G) (i : Fin 2) : ‖toyCoord g i‖ ≤ ‖toyScal g‖ := by
  fin_cases i
  · exact norm_fst_le _
  · exact norm_snd_le _

theorem maxNorm_toyD (g : ↥(𝕋).G) : maxNorm F (𝕋).G g =
    max 1 (max ‖toyL (toyScal g)‖ ‖toyL (toyScal g⁻¹)‖) := by
  rw [toyL_apply, toyL_apply, ← toyScal_spec', ← toyScal_spec']
  rfl

/-- `|cᵢ(g)|`, `|cᵢ(g)|⁻¹ ≤ K max(1, ‖g‖, ‖g⁻¹‖)`. -/
theorem exists_toyCoord_le : ∃ K : ℝ, 1 ≤ K ∧ ∀ g i,
    ‖toyCoord g i‖ ≤ K * maxNorm F (𝕋).G g ∧ ‖(toyCoord g i)⁻¹‖ ≤ K * maxNorm F (𝕋).G g := by
  obtain ⟨K₁, hK₁0, hK₁⟩ :=
    LinearMap.exists_norm_le_mul_norm_of_injective (𝕜 := F) (toyL (F := F))
      (LinearMap.id : F × F →ₗ[F] F × F) toyL_injective
  refine ⟨max 1 K₁, le_max_left _ _, fun g i => ?_⟩
  have hK : 0 ≤ max 1 K₁ := zero_le_one.trans (le_max_left _ _)
  have key : ∀ h : ↥(𝕋).G, ‖toyCoord h i‖ ≤ max 1 K₁ * maxNorm F (𝕋).G h := by
    intro h
    refine (norm_toyCoord_le h i).trans ((hK₁ _).trans ?_)
    rw [maxNorm_toyD]
    exact mul_le_mul (le_max_right _ _) (le_max_of_le_right (le_max_left _ _)) (norm_nonneg _) hK
  refine ⟨key g, ?_⟩
  have := key g⁻¹
  rwa [maxNorm_inv, toyCoord, toyScal_inv] at this

/-- `‖L_{(c₁, c₂)}‖ ≤ K ‖(c₁, c₂)‖`. -/
theorem exists_norm_toyL_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ c : F × F, ‖toyL c‖ ≤ K * ‖c‖ := by
  obtain ⟨K, hK, h⟩ := LinearMap.exists_norm_le_mul_norm_of_injective (𝕜 := F)
    (LinearMap.id : F × F →ₗ[F] F × F) (toyL (F := F)) Function.injective_id
  exact ⟨K, hK, fun c => h c⟩

theorem toyCoord_mul (g h : ↥(𝕋).G) (i : Fin 2) :
    toyCoord (g * h) i = toyCoord g i * toyCoord h i := by
  simp only [toyCoord, toyScal_mul]
  fin_cases i <;> rfl

theorem toyCoord_inv (g : ↥(𝕋).G) (i : Fin 2) : toyCoord g⁻¹ i = (toyCoord g i)⁻¹ :=
  toyScal_inv g i

/-- **Polynomial growth of `G(F)` at `toyD`**, degree `2`, with a log-norm ball `E` containing a
neighbourhood of `1`. -/
theorem toyD_growth : ∃ (R₀ M : ℝ), logNorm F (𝕋).G 1 < R₀ ∧ ∀ R : ℝ, 1 ≤ R →
    ∃ t : Finset ↥(𝕋).G, (t.card : ℝ) ≤ M * (1 + R) ^ 2 ∧
      {x | logNorm F (𝕋).G x < R} ⊆
        ⋃ g ∈ t, id '' ((g * ·) '' {x | logNorm F (𝕋).G x ≤ R₀}) := by
  obtain ⟨K, hK1, hK⟩ := exists_toyCoord_le (F := F)
  obtain ⟨K₂, hK₂, hL⟩ := exists_norm_toyL_le (F := F)
  set R₀ : ℝ := max (logNorm F (𝕋).G 1 + 1) (1 + Real.log (max 1 (K₂ * Real.exp 1)))
  set v : ↥(𝕋).G → Fin 2 → ℤ := fun g i => ⌊Real.log ‖toyCoord g i‖⌋
  have hv : ∀ a ∈ (Set.univ : Set ↥(𝕋).G), ∀ i, 1 * |(v a i : ℝ)| ≤
      logNorm F (𝕋).G a + Real.log K := by
    intro a _ i
    have hne : toyCoord a i ≠ 0 := toyScal_ne_zero a i
    have hM := one_le_maxNorm (F := F) (𝕋).G a
    have hl := abs_log_norm_le_log hne (hK a i).1 (hK a i).2
    rw [Real.log_mul (by linarith) (by linarith)] at hl
    have hf := abs_floor_le_abs_add_one (Real.log ‖toyCoord a i‖)
    simp only [one_mul, v, logNorm]
    linarith
  -- elements with the same coordinates differ by an element of the ball
  have hE : ∀ a ∈ (Set.univ : Set ↥(𝕋).G), ∀ a' ∈ (Set.univ : Set ↥(𝕋).G), v a = v a' →
      ∃ z ∈ ({1} : Set ↥(𝕋).G), ∃ e ∈ {x | logNorm F (𝕋).G x ≤ R₀}, a' = z * (a * e) := by
    intro a _ a' _ hvv
    refine ⟨1, rfl, a⁻¹ * a', ?_, by group⟩
    have hq : ∀ (x y : ↥(𝕋).G), v x = v y → ‖toyScal (x⁻¹ * y)‖ ≤ Real.exp 1 := by
      intro x y hxy
      have hc : ∀ i, ‖toyCoord (x⁻¹ * y) i‖ ≤ Real.exp 1 := by
        intro i
        rw [toyCoord_mul, toyCoord_inv, inv_mul_eq_div]
        exact (norm_div_lt_exp_of_floor_log_norm_eq (toyScal_ne_zero y i) (toyScal_ne_zero x i)
          (congrFun hxy i).symm).le
      exact norm_prod_le_iff.2 ⟨hc 0, hc 1⟩
    have h1 := hq a a' hvv
    have h2 : ‖toyScal (a⁻¹ * a')⁻¹‖ ≤ Real.exp 1 := by
      rw [show (a⁻¹ * a')⁻¹ = a'⁻¹ * a by group]
      exact hq a' a hvv.symm
    have hmax : maxNorm F (𝕋).G (a⁻¹ * a') ≤ max 1 (K₂ * Real.exp 1) := by
      rw [maxNorm_toyD]
      refine max_le (le_max_left _ _) (max_le ?_ ?_)
      · exact ((hL _).trans (mul_le_mul_of_nonneg_left h1 hK₂)).trans (le_max_right _ _)
      · exact ((hL _).trans (mul_le_mul_of_nonneg_left h2 hK₂)).trans (le_max_right _ _)
    change logNorm F (𝕋).G (a⁻¹ * a') ≤ R₀
    refine le_trans ?_ (le_max_right _ _)
    unfold logNorm
    gcongr
    exact zero_lt_one.trans_le (one_le_maxNorm (F := F) _ _)
  obtain ⟨M, hM⟩ := exists_finset_cover_of_intCoord v one_pos hv hE
  refine ⟨R₀, M, (lt_add_one _).trans_le (le_max_left _ _), fun R hR => ?_⟩
  obtain ⟨t, -, hcard, hcov⟩ := hM R hR
  refine ⟨t, by simpa using hcard, fun x hx => ?_⟩
  obtain ⟨z, hz, j, hj, e, he, rfl⟩ := hcov x trivial hx
  rw [Set.mem_singleton_iff.1 hz, one_mul]
  exact Set.mem_biUnion hj ⟨j * e, ⟨e, he, rfl⟩, rfl⟩

theorem isInvariantQuotient_id_toyD :
    IsInvariantQuotient (id : ↥(𝕋).G → ↥(𝕋).G) (Measure.haar : Measure ↥(𝕋).G) where
  descends _ _ _ h := by simp only [id] at h ⊢; rw [h]
  measure_image_mul_right S h := by
    rw [Set.image_id, Set.image_id, Set.image_mul_right]
    exact measure_preimage_mul_right _ _ _

/-- **`σ^{-d}` is integrable on `G(F)` at `toyD`** for `d > 3`, without any axiom. -/
theorem toyD_integrable_logNorm_rpow_neg {d : ℝ} (hd : (2 : ℝ) + 1 < d) :
    Integrable (fun g : ↥(𝕋).G => logNorm F (𝕋).G g ^ (-d)) (Measure.haar : Measure ↥(𝕋).G) := by
  obtain ⟨R₀, M, h1, hg⟩ := toyD_growth (F := F)
  set E : Set ↥(𝕋).G := {x | logNorm F (𝕋).G x ≤ R₀}
  have hcont : Continuous fun g : ↥(𝕋).G => logNorm F (𝕋).G g := (𝕋).continuous_logNormG
  have hEc : IsCompact E := isCompact_logNorm_le (𝕋).isClosed_G R₀
  have hEo : IsOpen {x : ↥(𝕋).G | logNorm F (𝕋).G x < R₀} := isOpen_lt hcont continuous_const
  have hsub : {x : ↥(𝕋).G | logNorm F (𝕋).G x < R₀} ⊆ E := fun x hx =>
    show logNorm F (𝕋).G x ≤ R₀ from le_of_lt hx
  have hEi : (interior E).Nonempty :=
    ⟨1, interior_maximal hsub hEo (show (1 : ↥(𝕋).G) ∈ {x | logNorm F (𝕋).G x < R₀} from h1)⟩
  set μ : Measure ↥(𝕋).G := Measure.haar
  have hπ := isInvariantQuotient_id_toyD (F := F)
  -- `Ξ_E` is the constant `μ(E)^{-1/2}`
  have hvol : ∀ g : ↥(𝕋).G, relVol id μ E g = μ E := by
    intro g
    simp only [relVol, Set.image_id, Set.image_mul_left]
    exact measure_preimage_mul _ _ _
  have hint := hπ.integrable_relXi_sq_rpow_neg hEi hEc (ξ := fun g => relXi id μ E g)
    (fun _ => rfl) (by simp only [relXi, hvol]; exact aestronglyMeasurable_const)
    (fun g => one_le_logNorm _ g) hcont.measurable hg hd
  have hμ0 : 0 < (μ E).toReal :=
    ENNReal.toReal_pos (fun h => (hEo.measure_pos μ ⟨1, h1⟩).ne'
      (measure_mono_null hsub h)) hEc.measure_lt_top.ne
  have hξ : ∀ g : ↥(𝕋).G, relXi id μ E g ^ 2 = ((μ E).toReal)⁻¹ := by
    intro g
    rw [relXi_sq, hvol, ENNReal.toReal_inv]
  simp only [hξ] at hint
  have := hint.const_mul (μ E).toReal
  refine this.congr (Filter.Eventually.of_forall fun g => ?_)
  simp only
  rw [← mul_assoc, mul_inv_cancel₀ hμ0.ne', one_mul]

/-- The Iwasawa pair `(G, K)` at `toyD`, `K` the stabilizer of the unit ball of `C(W) × C(V)`. -/
def toyXiPair : IwasawaPair ↥(𝕋).G where
  P := ⊤
  K := (latticeStab F (A := (𝕋).ambient)).subgroupOf (𝕋).G
  isClosed_P := isClosed_univ
  isOpen_K := (isOpen_latticeStab F).preimage continuous_subtypeVal
  isCompact_K := (𝕋).isClosed_G.isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_latticeStab F)
  mul_eq g := ⟨g, trivial, 1, one_mem _, (mul_one g).symm⟩

/-- `Ξ ≡ 1` at `toyD`: `G` is abelian, so `δ_P = 1`. -/
theorem toyXiPair_xi_eq_one (g : ↥(𝕋).G) : (toyXiPair (F := F)).xi g = 1 :=
  (toyXiPair (F := F)).xi_eq_one_of_comm toyD_G_comm g

/-- The hypotheses of `exists_iwasawaPair_xi_sq_integrable` hold at `toyD`: the empty flags are
full, and `whittB` of them is `G`. -/
theorem toyD_xi_sq_integrable_hyps :
    (emptyFlag (𝕋).QW).IsFull ∧ (emptyFlag (𝕋).QV).IsFull ∧
      (𝕋).whittB (emptyFlag _) (emptyFlag _) = ⊤ :=
  ⟨emptyFlag_isFull toyData_wittIndex_QW, emptyFlag_isFull toyData_wittIndex_QV,
    whittB_eq_top_of_wittIndex_zero _ _ _ (emptyFlag_isFull toyData_wittIndex_QW)
      (emptyFlag_isFull toyData_wittIndex_QV) toyData_wittIndex_QW toyData_wittIndex_QV⟩

/-- **(V) The conclusion of `exists_iwasawaPair_xi_sq_integrable` at `toyD`**, without the axiom,
with `b = Module.finBasis` and `D = 4` (the same proof works for any basis). -/
theorem toyD_exists_iwasawaPair_xi_sq_integrable :
    ∃ (I : IwasawaPair ↥(𝕋).G) (_ : I.P = (𝕋).whittB (emptyFlag _) (emptyFlag _))
      (b : Module.Basis (Fin (Module.finrank F (𝕋).ambient)) F (𝕋).ambient) (D : ℕ),
      Integrable (fun g : ↥(𝕋).G =>
          I.xi g ^ 2 * ((1 + Real.log (entryMaxNorm b (𝕋).G g)) ^ D)⁻¹)
        (Measure.haar : Measure ↥(𝕋).G) := by
  set b := Module.finBasis F (𝕋).ambient
  refine ⟨toyXiPair, toyD_xi_sq_integrable_hyps.2.2.symm, b, 4, ?_⟩
  obtain ⟨C', hC', hσ⟩ := logNorm_equiv_entryMaxNorm b (𝕋).G
  have hint := (toyD_integrable_logNorm_rpow_neg (F := F) (d := 4) (by norm_num)).const_mul
    (C' ^ 4)
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun g => ?_)
  · have hc : Continuous fun g : ↥(𝕋).G => 1 + Real.log (entryMaxNorm b (𝕋).G g) :=
      continuous_const.add ((continuous_entryMaxNorm b (𝕋).G).log fun g =>
        (zero_lt_one.trans_le (one_le_entryMaxNorm b (𝕋).G g)).ne')
    exact (((toyXiPair (F := F)).continuous_xi.pow 2).mul ((hc.pow 4).inv₀ fun g =>
      (pow_pos (by linarith [Real.log_nonneg (one_le_entryMaxNorm b (𝕋).G g)]) 4).ne'))
      |>.aestronglyMeasurable
  · have hσ1 := one_le_logNorm (F := F) (𝕋).G g
    have hE1 : 1 ≤ 1 + Real.log (entryMaxNorm b (𝕋).G g) := by
      linarith [Real.log_nonneg (one_le_entryMaxNorm b (𝕋).G g)]
    have h4 : logNorm F (𝕋).G g ^ (4 : ℝ) = logNorm F (𝕋).G g ^ (4 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (logNorm F (𝕋).G g) 4
    rw [toyXiPair_xi_eq_one, one_pow, one_mul, Real.rpow_neg (by linarith), h4,
      Real.norm_of_nonneg (by positivity)]
    have hle : logNorm F (𝕋).G g ^ 4 ≤ C' ^ 4 * (1 + Real.log (entryMaxNorm b (𝕋).G g)) ^ 4 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (hσ g).1 4
    have hp : 0 < logNorm F (𝕋).G g ^ 4 := by positivity
    have hq : 0 < (1 + Real.log (entryMaxNorm b (𝕋).G g)) ^ 4 := by positivity
    calc ((1 + Real.log (entryMaxNorm b (𝕋).G g)) ^ 4)⁻¹
        = ((1 + Real.log (entryMaxNorm b (𝕋).G g)) ^ 4)⁻¹ *
            (logNorm F (𝕋).G g ^ 4 * (logNorm F (𝕋).G g ^ 4)⁻¹) := by
          rw [mul_inv_cancel₀ hp.ne', mul_one]
      _ ≤ ((1 + Real.log (entryMaxNorm b (𝕋).G g)) ^ 4)⁻¹ *
            (C' ^ 4 * (1 + Real.log (entryMaxNorm b (𝕋).G g)) ^ 4 *
              (logNorm F (𝕋).G g ^ 4)⁻¹) := by gcongr
      _ = C' ^ 4 * (logNorm F (𝕋).G g ^ 4)⁻¹ := by field_simp

end GSpinGGP.AxiomRedTeam
