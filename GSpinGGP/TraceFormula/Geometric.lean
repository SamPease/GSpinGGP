/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.MGeom
import GSpinGGP.TraceFormula.Scusp
import GSpinGGP.TraceFormula.Spectral
import GSpinGGP.TraceFormula.Analytic
import GSpinGGP.GGP.Descent
import GSpinGGP.Literature.Localization
import GSpinGGP.Literature.InvariantSets
import Mathlib.Algebra.Module.CharacterModule

/-!
# `J_qc` and localization away from `1`

The statements `exists_isJqc` and `geomAt_away` are the
interface; `geomAt_away` is consumed by `Spine.lean`, `distribJ_eq_of_thetaF_eqOn` is available
to `Lie.lean`.

* §0 **The topology of `QC(G, χ⁻¹)`** (Thesis §4.1.1, `p`-adic case; BP §4.1, §4.4), in the
  `χ`-equivariant setting: `QC_c(Ω)` carries its finest locally convex topology and
  `QC = lim_Ω QC_c(Ω)` the projective limit topology, `Ω` running over the open, closed,
  invariant, `A_G(F)`-stable sets that are compact modulo conjugation and `A_G(F)` (`IsQCCutoff`),
  through `θ ↦ 1_Ω θ`.  As a seminorm topology (`qcTopology`): the seminorms `q(1_{Ω ∩ G_reg} θ)`,
  `q` any seminorm on functions.  In this topology a linear form is continuous iff it only sees
  `θ` on `Ω ∩ G_reg(F)` for one such `Ω` (`continuous_qc_of_local`, `exists_local_of_continuous`).
* §1 `IsJqc`, `jqc` (Thesis Prop 12.2.3): with the
  fields `continuous` and `eq_mGeom_of_eqOn_ell` (`Supp(J_qc − m_geom) ⊆ G_ell`, in place of the
  thesis's `Supp(J_qc) ⊆ G_ell`; see the docstring of `IsJqc`).
  `IsJqc.unique`: under these fields `J_qc` is unique (BP Cor 5.7.2(i)).
* §2 `exists_isJqc`, proved: `J_qc(θ) = m_geom(θ) + (J(f) − m_geom(θ_f))` for any `f` with
  `θ_f = θ` on `G_ell,reg(F)`, well defined by Thesis Prop 7.4.1(ii) (`Spectral.lean`); this is
  the elliptic-sum formula for `J_qc`, since `∫_{Γ_ell} D^G θ θ_π = θ̂_f(π)` for such `f`.
* §3 `geomAt_away` (Thesis Prop 12.3.1), in test-function form,
  proved from a partition of unity over a compact set (`geomAt_glue`) and two local statements:
  near `A_G(F)` (`exists_null_nhd_of_nearCentral`) and away from it, where semisimple descent and
  (HYP) for `restrictFix` enter (`exists_good_nhd_of_not_nearCentral`).
-/

noncomputable section

open MeasureTheory Topology Filter

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
variable (ψ : NontrivialAddChar F) (d : GGPData F)

/-! ## 0. The topology of `QC(G(F), χ⁻¹)` -/

section Topology

/-- `Ω ⊆ G(F)` is **compact modulo conjugation and `A_G(F)`**: `Ω ⊆ A_G(F) · C^{G(F)}` for a
compact `C` (Thesis §4.1.1, in the `χ`-equivariant setting). -/
def IsCompactModConjAG (Ω : Set ↥d.G) : Prop :=
  ∃ C : Set ↥d.G, IsCompact C ∧ ∀ g ∈ Ω, ∃ (a : ↥d.AG) (x c : ↥d.G), c ∈ C ∧
    g = (a : ↥d.G) * (x * c * x⁻¹)

/-- The index sets of the projective limit `QC = lim QC_c(Ω)` (Thesis §4.1.1): `Ω` open, closed,
invariant, `A_G(F)`-stable, and compact modulo conjugation and `A_G(F)`. -/
def IsQCCutoff (Ω : Set ↥d.G) : Prop :=
  IsInvariantClopen d Ω ∧ IsCompactModConjAG d Ω

theorem isQCCutoff_empty : IsQCCutoff d ∅ :=
  ⟨⟨isOpen_empty, isClosed_empty, fun _ _ h => h.elim, fun _ _ h => h.elim⟩,
    ⟨∅, isCompact_empty, fun _ h => h.elim⟩⟩

theorem isQCCutoff_union {Ω₁ Ω₂ : Set ↥d.G} (h₁ : IsQCCutoff d Ω₁) (h₂ : IsQCCutoff d Ω₂) :
    IsQCCutoff d (Ω₁ ∪ Ω₂) := by
  obtain ⟨⟨o₁, c₁, i₁, a₁⟩, C₁, hC₁, s₁⟩ := h₁
  obtain ⟨⟨o₂, c₂, i₂, a₂⟩, C₂, hC₂, s₂⟩ := h₂
  refine ⟨⟨o₁.union o₂, c₁.union c₂, fun x g hg => ?_, fun a g hg => ?_⟩,
    C₁ ∪ C₂, hC₁.union hC₂, fun g hg => ?_⟩
  · rcases hg with h | h
    · exact Or.inl (i₁ x g h)
    · exact Or.inr (i₂ x g h)
  · rcases hg with h | h
    · exact Or.inl (a₁ a g h)
    · exact Or.inr (a₂ a g h)
  · rcases hg with h | h
    · obtain ⟨a, x, c, hc, e⟩ := s₁ g h
      exact ⟨a, x, c, Or.inl hc, e⟩
    · obtain ⟨a, x, c, hc, e⟩ := s₂ g h
      exact ⟨a, x, c, Or.inr hc, e⟩

theorem isQCCutoff_biUnion {ι : Type*} (s : Finset ι) (Ω : ι → Set ↥d.G)
    (h : ∀ i ∈ s, IsQCCutoff d (Ω i)) : IsQCCutoff d (⋃ i ∈ s, Ω i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isQCCutoff_empty d
  | insert i s _ ih =>
    rw [Finset.set_biUnion_insert]
    exact isQCCutoff_union d (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- A quasi-character cut off by a set compact modulo conjugation and `A_G(F)` has compact
support modulo conjugation and `A_G(F)`. -/
theorem hasCompactSupportModConjAG_indicator {Ω : Set ↥d.G} (hΩ : IsCompactModConjAG d Ω)
    (θ : ↥d.G → ℂ) : HasCompactSupportModConjAG d (Ω.indicator θ) := by
  obtain ⟨C, hC, hs⟩ := hΩ
  refine ⟨C, hC, fun g _ hne => hs g ?_⟩
  by_contra hg
  exact hne (Set.indicator_of_notMem hg θ)

/-- The index type of the projective system. -/
def QCCutoff : Type := {Ω : Set ↥d.G // IsQCCutoff d Ω}

instance : Nonempty (QCCutoff d) := ⟨⟨∅, isQCCutoff_empty d⟩⟩

/-- `θ ↦ 1_{Ω ∩ G_reg(F)} θ`, the restriction map `QC → QC_c(Ω)` (quasi-characters are functions
on `G_reg(F)`, so values off the regular set are discarded). -/
def regRestrict (Ω : Set ↥d.G) : (↥d.G → ℂ) →ₗ[ℂ] (↥d.G → ℂ) where
  toFun θ := (Ω ∩ regularSet d.G d.lie).indicator θ
  map_add' θ θ' := by
    ext g
    by_cases hg : g ∈ Ω ∩ regularSet d.G d.lie <;> simp [Set.indicator, hg]
  map_smul' c θ := by
    ext g
    by_cases hg : g ∈ Ω ∩ regularSet d.G d.lie <;> simp [Set.indicator, hg]

theorem regRestrict_apply (Ω : Set ↥d.G) (θ : ↥d.G → ℂ) :
    regRestrict d Ω θ = (Ω ∩ regularSet d.G d.lie).indicator θ := rfl

variable (χ : CentralCharOn d)

/-- The seminorms of the projective limit topology (Thesis §4.1.1, `p`-adic case; BP §4.4): for
`Ω` in the projective system and `q` any seminorm, `θ ↦ q(1_{Ω ∩ G_reg} θ)`.  (Every seminorm on
`QC_c(Ω)` extends to all functions, so these are exactly the seminorms of the finest locally
convex topology on `QC_c(Ω)`, pulled back along `θ ↦ 1_Ω θ`.) -/
def qcSeminormFamily : SeminormFamily ℂ ↥(QC d χ) (QCCutoff d × Seminorm ℂ (↥d.G → ℂ)) :=
  fun i => i.2.comp ((regRestrict d i.1.1).comp (QC d χ).subtype)

set_option warn.classDefReducibility false in
/-- **The topology of `QC(G(F), χ⁻¹)`** (Lean: on `QC d χ`; Thesis §4.1.1, BP §4.4): the
projective limit of the finest locally convex topologies on the `QC_c(Ω)`. -/
def qcTopology : TopologicalSpace ↥(QC d χ) := (qcSeminormFamily d χ).moduleFilterBasis.topology

theorem withSeminorms_qcTopology :
    @WithSeminorms ℂ ↥(QC d χ) _ _ _ _ (qcSeminormFamily d χ) (qcTopology d χ) := by
  let _ := qcTopology d χ
  exact ⟨rfl⟩

/-- **A linear form that only sees `Ω ∩ G_reg(F)`, for one `Ω` of the projective system, is
continuous** (every linear form on `QC_c(Ω)` is continuous for the finest locally convex
topology). -/
theorem continuous_qc_of_local (J : ↥(QC d χ) →ₗ[ℂ] ℂ) {Ω : Set ↥d.G} (hΩ : IsQCCutoff d Ω)
    (hJ : ∀ θ : ↥(QC d χ), Set.EqOn (θ : ↥d.G → ℂ) 0 (Ω ∩ regularSet d.G d.lie) → J θ = 0) :
    @Continuous _ _ (qcTopology d χ) _ J := by
  let _ := qcTopology d χ
  set R : ↥(QC d χ) →ₗ[ℂ] (↥d.G → ℂ) := (regRestrict d Ω).comp (QC d χ).subtype with hR
  have hker : LinearMap.ker R ≤ LinearMap.ker J := by
    intro θ hθ
    rw [LinearMap.mem_ker] at hθ ⊢
    refine hJ θ fun g hg => ?_
    have := congrFun hθ g
    simpa [R, regRestrict_apply, Set.indicator_of_mem hg] using this
  let g₀ : ↥(LinearMap.range R) →ₗ[ℂ] ℂ :=
    ((LinearMap.ker R).liftQ J hker).comp R.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g, hg⟩ := LinearMap.exists_extend g₀
  have hfac : ∀ θ, J θ = g (R θ) := by
    intro θ
    have h1 : g (R θ) = g₀ ⟨R θ, LinearMap.mem_range_self R θ⟩ := by
      rw [← hg]; rfl
    rw [h1]
    simp only [g₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  refine WithSeminorms.continuous_normedSpace_rng ℂ (withSeminorms_qcTopology d χ) J
    ⟨{(⟨Ω, hΩ⟩, (normSeminorm ℂ ℂ).comp g)}, 1, fun θ => ?_⟩
  simp [qcSeminormFamily, hfac θ, R]

/-- **Conversely, a continuous linear form only sees `Ω ∩ G_reg(F)` for one `Ω`**: a continuous
seminorm is bounded by finitely many of the defining seminorms (`Seminorm.bound_of_continuous`). -/
theorem exists_local_of_continuous (J : ↥(QC d χ) →ₗ[ℂ] ℂ)
    (hJ : @Continuous _ _ (qcTopology d χ) _ J) :
    ∃ Ω, IsQCCutoff d Ω ∧ ∀ θ : ↥(QC d χ),
      Set.EqOn (θ : ↥d.G → ℂ) 0 (Ω ∩ regularSet d.G d.lie) → J θ = 0 := by
  classical
  let _ := qcTopology d χ
  have hq : Continuous ((normSeminorm ℂ ℂ).comp J) := continuous_norm.comp hJ
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (withSeminorms_qcTopology d χ) _ hq
  refine ⟨⋃ i ∈ s, i.1.1, isQCCutoff_biUnion d s _ (fun i _ => i.1.2), fun θ hθ => ?_⟩
  have h0 : ∀ i ∈ s, qcSeminormFamily d χ i θ ≤ 0 := by
    intro i hi
    have : regRestrict d i.1.1 (θ : ↥d.G → ℂ) = 0 := by
      ext g
      by_cases hg : g ∈ i.1.1 ∩ regularSet d.G d.lie
      · rw [regRestrict_apply, Set.indicator_of_mem hg]
        exact hθ ⟨Set.mem_biUnion hi hg.1, hg.2⟩
      · rw [regRestrict_apply, Set.indicator_of_notMem hg]; rfl
    simp [qcSeminormFamily, this]
  have hs : (s.sup (qcSeminormFamily d χ)) θ ≤ 0 :=
    Seminorm.finset_sup_apply_le le_rfl h0
  have h1 := hC θ
  have h2 : ‖J θ‖ ≤ 0 := by
    calc ‖J θ‖ = ((normSeminorm ℂ ℂ).comp J) θ := rfl
      _ ≤ (C • s.sup (qcSeminormFamily d χ)) θ := h1
      _ = C * (s.sup (qcSeminormFamily d χ)) θ := rfl
      _ ≤ C * 0 := mul_le_mul_of_nonneg_left hs C.2
      _ = 0 := mul_zero _
  exact norm_le_zero_iff.mp h2

/-- A continuous linear form only sees the regular set. -/
theorem congr_regularSet_of_continuous (J : ↥(QC d χ) →ₗ[ℂ] ℂ)
    (hJ : @Continuous _ _ (qcTopology d χ) _ J) (θ θ' : ↥(QC d χ))
    (he : Set.EqOn (θ : ↥d.G → ℂ) θ' (regularSet d.G d.lie)) : J θ = J θ' := by
  obtain ⟨Ω, -, hΩ⟩ := exists_local_of_continuous d χ J hJ
  have := hΩ (θ - θ') fun g hg => by
    simp [he hg.2]
  rwa [map_sub, sub_eq_zero] at this

end Topology

/-! ## 1. The extension `J_qc` of `J` to quasi-characters -/

/-- `J : QC(G, χ⁻¹) → ℂ` (Lean: on `QC d χ`) extends the distribution `J` (Thesis
Prop 12.2.3): it depends only on values on `G_reg(F)`, `J(f) = J(θ_f)` for every
`f ∈ ScuspTestFn d χ`, it is continuous for `qcTopology`, and `J − m_geom` is supported in the
elliptic set.

**On the support condition.**  This differs from Thesis Prop 12.2.3, which has
`Supp(J_qc) ⊆ G(F)_ell`: here `Γ(G,H)` need not be contained in `Γ_ell(G)` (an `x ∈ Γ(G,H)` whose fixed
space `W'_x` or `V'_x` is a hyperbolic plane is not elliptic), and `m_geom` sees such `x`.  The
field used is `Supp(J_qc − m_geom) ⊆ G_ell` (`eq_mGeom_of_eqOn_ell`); continuity already gives
compact support modulo conjugation. -/
structure IsJqc (χ : CentralCharOn d) (J : ↥(QC d χ) →ₗ[ℂ] ℂ) : Prop where
  /-- `J` only sees the regular set (quasi-characters are functions on `G_reg(F)`). -/
  congr_regularSet : ∀ θ θ' : ↥(QC d χ),
    Set.EqOn (θ : ↥d.G → ℂ) θ' (regularSet d.G d.lie) → J θ = J θ'
  /-- `J(f) = J_qc(θ_f)`. -/
  distribJ_eq : ∀ (f : ↥d.G → ℂ) (hf : f ∈ ScuspTestFn d χ),
    distribJ d ψ f = J ⟨thetaF d f, thetaF_mem_QC d χ hf⟩
  /-- `J_qc` is continuous for the topology of `QC(G, χ⁻¹)` (Thesis §4.1.1, BP §4.4). -/
  continuous : @Continuous _ _ (qcTopology d χ) _ J
  /-- `Supp(J_qc − m_geom) ⊆ G(F)_ell`: `J_qc(θ) = m_geom(θ)` when `θ = 0` on `G_ell,reg(F)`. -/
  eq_mGeom_of_eqOn_ell : ∀ θ : ↥(QC d χ),
    Set.EqOn (θ : ↥d.G → ℂ) 0 d.ellRegSet → J θ = mGeom ψ d θ

open Classical in
/-- **`J_qc`** (Thesis Prop 12.2.3): the linear form with `IsJqc` (chosen; `0` if none).
Under (HYP) it exists (`exists_isJqc`) and is unique (`IsJqc.unique`). -/
def jqc (χ : CentralCharOn d) : ↥(QC d χ) →ₗ[ℂ] ℂ :=
  if h : ∃ J, IsJqc ψ d χ J then h.choose else 0

/-! ## 2. Existence of `J_qc` (Thesis Prop 12.2.3) -/

section Existence

variable (χ : CentralCharOn d)

/-- **An invariant clopen neighbourhood of the elliptic set, compact modulo conjugation and
`A_G(F)`** (BP Lemma 4.2.3 in the `p`-adic case, cf. Thesis §4.8).
Proof route: there are finitely many `G(F)`-conjugacy classes of maximal tori `T` of `G` with
`T/A_G` anisotropic, each `T(F)/A_G(F)` is compact, and `G_ell,reg(F) ⊆ ⋃_T A_G(F) T(F)^{G(F)}`; the
preimage, under the characteristic-polynomial map of `(W, V)`, of a compact open neighbourhood of
the image of `⋃_T T(F)` (modulo the scalars) is open, closed, invariant and `A_G(F)`-stable, and it
is compact modulo conjugation and `A_G(F)` by Harish-Chandra's compactness lemma.
Status: proved: the set `Ω` of BP Cor 5.7.2(i) (axiom
`bp_scusp_surj_ell`, via `exists_scusp_of_qc_bp`, `Scusp.lean`) has these properties. -/
theorem exists_qcCutoff_ellRegSet : ∃ Ω, IsQCCutoff d Ω ∧ d.ellRegSet ⊆ Ω := by
  obtain ⟨Ω, hΩ, hell, hcpt, -⟩ := exists_scusp_of_qc_bp d
  exact ⟨Ω, ⟨hΩ, hcpt⟩, hell⟩

/-- **A germ vanishes where `θ` vanishes near the point** (uniqueness of the local expansion,
BP §4.1, §4.5): if `θ = 0` on the regular elements of an open `Ω ∋ x`, `x` semisimple, then
`c_{θ,O}(x) = 0`.  (`θ` agrees on `G_reg(F)` with `θ' = 1_{G ∖ Ω} θ`, which vanishes near `x` and so
has the zero expansion at `x`.) -/
theorem germ_eq_zero_of_eqOn_zero_of_mem {Ω : Set ↥d.G} (hΩ : IsOpen Ω) {θ : ↥d.G → ℂ}
    (h0 : Set.EqOn θ 0 (Ω ∩ regularSet d.G d.lie)) {x : ↥d.G} (hxΩ : x ∈ Ω)
    (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    (O : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))) :
    germ d.G d.lie d.bilin ψ θ x O = 0 := by
  classical
  let θ' : ↥d.G → ℂ := fun g => if g ∈ Ω then 0 else θ g
  have heq : Set.EqOn θ θ' (regularSet d.G d.lie) := fun g hg => by
    by_cases hgΩ : g ∈ Ω
    · simpa [θ', hgΩ] using h0 ⟨hgΩ, hg⟩
    · simp [θ', hgΩ]
  rw [germ_congr_regularSet ψ d heq hx O]
  by_cases hO : O ∈ NilReg (grpCentralizer d.G x)
      (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))
  · have hev : ∀ᶠ y in 𝓝 x, θ' y = θ' x := by
      filter_upwards [hΩ.mem_nhds hxΩ] with y hy
      simp [θ', hy, hxΩ]
    obtain ⟨ω, hω, hloc⟩ := exists_nhds_zero_mul_expA_of_eventually (F := F) hev
    have hexp : HasGermExpansion d.G d.lie d.bilin ψ θ' x 0 := by
      refine ⟨by simp, ω, hω, fun X hX _ _ y hy => ?_⟩
      rw [hloc X hX y hy]
      simp [θ', hxΩ]
    rw [germ_eq_of_hasGermExpansion d ψ hx hexp hO]
    rfl
  · exact germ_of_not_mem hO

/-- **A torus of `Γ(G,H)` is compact modulo `A_G(F)` in `G(F)`**: for `T = T_x`, `x ∈ Γ(G,H)`
(`T(F)/A_{G,H}(F)` compact, part of `IsGammaElt`), there is a compact `K ⊆ G(F)` with
`diag(T(F)) ⊆ A_G(F) · K` (the image of `T(F)/A_{G,H}(F)` in `G(F)/A_G(F)` is compact, and compact
subsets of `G(F)/A_G(F)` lift, `G(F)` being locally compact). -/
theorem exists_compact_diag_gammaTorus (T : d.GammaTorus) :
    ∃ K : Set ↥d.G, IsCompact K ∧
      ∀ t : ↥T.1, ∃ (a : ↥d.AG) (k : ↥d.G), k ∈ K ∧ d.diag (t : ↥(GSpin d.QW)) = (a : ↥d.G) * k := by
  obtain ⟨x, hx, hxT⟩ := T.2
  have : CompactSpace (d.TorusQuot T.1) := by rw [← hxT]; exact hx.2.2
  have hdiag : Continuous d.diag :=
    d.continuous_pair.comp (continuous_id.prodMk d.continuous_incl)
  let φ : ↥T.1 → d.GmodAG := fun t => QuotientGroup.mk (d.diag (t : ↥(GSpin d.QW)))
  have hφ : Continuous φ :=
    QuotientGroup.continuous_mk.comp (hdiag.comp continuous_subtype_val)
  have hφr : ∀ t s : ↥T.1, (QuotientGroup.leftRel (d.scalarsIn T.1)) t s → φ t = φ s := by
    intro t s hts
    rw [QuotientGroup.leftRel_apply] at hts
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hts
    change (QuotientGroup.mk _ : d.GmodAG) = QuotientGroup.mk _
    rw [QuotientGroup.eq, ← map_inv, ← map_mul]
    have : ((t : ↥(GSpin d.QW)))⁻¹ * (s : ↥(GSpin d.QW)) = scalarGSpin d.QW c := by
      rw [hc]; simp
    rw [this]
    exact d.AGH_le_AG ⟨c, rfl⟩
  let φbar : d.TorusQuot T.1 → d.GmodAG := Quotient.lift φ hφr
  have hφbar : Continuous φbar := continuous_quot_lift _ hφ
  have hrange : IsCompact (Set.range φbar) := isCompact_range hφbar
  -- lift the compact set `range φbar` to `G(F)`
  have hopen : IsOpenMap (QuotientGroup.mk : ↥d.G → d.GmodAG) := QuotientGroup.isOpenMap_coe
  choose N hNc hN using fun q : d.GmodAG => exists_compact_mem_nhds (Quotient.out q)
  obtain ⟨u, hu⟩ := hrange.elim_finite_subcover
    (fun q => (QuotientGroup.mk : ↥d.G → d.GmodAG) '' interior (N q))
    (fun q => hopen _ isOpen_interior) fun q _ => Set.mem_iUnion.2
      ⟨q, Quotient.out q, mem_interior_iff_mem_nhds.2 (hN q), Quotient.out_eq q⟩
  refine ⟨⋃ q ∈ u, N q, u.isCompact_biUnion fun q _ => hNc q, fun t => ?_⟩
  have htr : φ t ∈ Set.range φbar := ⟨QuotientGroup.mk t, rfl⟩
  obtain ⟨q, hq, k, hk, hkt⟩ : ∃ q ∈ u, φ t ∈
      (QuotientGroup.mk : ↥d.G → d.GmodAG) '' interior (N q) := by
    simpa using hu htr
  rw [QuotientGroup.eq] at hkt
  refine ⟨⟨_, hkt⟩, k, Set.mem_biUnion hq (interior_subset hk), ?_⟩
  have hcent := Subgroup.mem_center_iff.mp (d.AG_le_center hkt) k
  simp only
  rw [← hcent, mul_inv_cancel_left]

/-- **`m_geom` is supported in a set compact modulo conjugation and `A_G(F)`** (Thesis
Prop 12.1.1(i), continuity of `m_geom`, `p`-adic case).
Proof route: `Γ(G,H)` is a finite union of the images of the `T(F)`, `T ∈ 𝒯`, each compact modulo
`A_{G,H}(F) ⊆ A_G(F)` (`IsGammaElt`); take `Ω ⊇ ⋃_T diag(T(F))` as in `exists_qcCutoff_ellRegSet`.
The germ `c_{θ,O_t}(t)` only depends on `θ` on the regular elements near `t`
(`hasGermExpansion_congr_regularSet`, uniqueness of the expansion), so it vanishes when `θ = 0` on
`Ω ∩ G_reg(F)`; then every `m_{geom,s}(θ)` vanishes.
Status: **proved** from `finite_gammaClass` (`MGeom.lean`, SORRY), the compactness of `T(F)/A_{G,H}(F)`
(part of `IsGammaElt`), the cited `hc_exists_invariantClopen_superset` and germ uniqueness
(`germ_eq_zero_of_eqOn_zero_of_mem`).  Only the representatives `T = (Quot.out c).1` of the
finitely many classes enter `m_{geom,s}`, so no conjugation is needed. -/
theorem exists_qcCutoff_mGeom : ∃ Ω, IsQCCutoff d Ω ∧ ∀ (χ : CentralCharOn d) (θ : ↥d.G → ℂ),
    θ ∈ QC d χ → Set.EqOn θ 0 (Ω ∩ regularSet d.G d.lie) → mGeom ψ d θ = 0 := by
  classical
  have := finite_gammaClass d
  choose K hK hKT using fun c : GammaClass d => exists_compact_diag_gammaTorus d (Quot.out c)
  obtain ⟨Ω, hΩ, hCΩ, C', hC', hΩC'⟩ :=
    hc_exists_invariantClopen_superset d (isCompact_iUnion hK)
  refine ⟨Ω, ⟨hΩ, C', hC', hΩC'⟩, fun χ θ _ h0 => ?_⟩
  -- every `diag t`, `t ∈ T_c`, lies in `Ω`
  have hdiag : ∀ (c : GammaClass d) (t : ↥(Quot.out c).1), d.diag (t : ↥(GSpin d.QW)) ∈ Ω := by
    intro c t
    obtain ⟨a, k, hk, e⟩ := hKT c t
    rw [e]
    exact hΩ.2.2.2 a k (hCΩ (Set.mem_iUnion.2 ⟨c, hk⟩))
  have hS : mGeomS ψ d θ = fun _ => 0 := by
    funext s
    unfold mGeomS torusIntegral
    refine (tsum_congr fun c => ?_).trans tsum_zero
    have hint : ∀ t : ↥(Quot.out c).1,
        gammaIntegrand ψ d θ (Quot.out c).1 s (t : ↥(GSpin d.QW)) = 0 := by
      intro t
      unfold gammaIntegrand
      split_ifs with h
      · rw [germ_eq_zero_of_eqOn_zero_of_mem ψ d hΩ.1 h0 (hdiag c _)
          (isSS_diag_of_isGammaElt d h.1)]
        ring
      · rfl
    simp only [hint, integral_zero, mul_zero]
  unfold mGeom
  rw [hS]
  exact tendsto_const_nhds.limUnder_eq

private theorem distribJ_zero : distribJ d ψ (0 : ↥d.G → ℂ) = 0 := by
  have := GGPData.distribJ_smul d ψ 0 (0 : ↥d.G → ℂ)
  simpa using this

private theorem mGeom_zero : mGeom ψ d (0 : ↥d.G → ℂ) = 0 := by
  have := mGeom_smul ψ d 0 (Submodule.zero_mem (QCfin d))
  simpa using this

/-- **Elliptic isolation for quasi-characters** (BP Cor 5.7.2(i) with an elliptic cutoff): every
`θ ∈ QC(G, χ⁻¹)` agrees on `G_ell,reg(F)` with some `θ_f`, `f ∈ ScuspTestFn d χ`.
Proved from `exists_scusp_of_qc_bp` (`Scusp.lean`; axiom `bp_scusp_surj_ell`). -/
theorem exists_scusp_eqOn_ell {θ : ↥d.G → ℂ} (hθ : θ ∈ QC d χ) :
    ∃ f ∈ ScuspTestFn d χ, Set.EqOn (thetaF d f) θ d.ellRegSet := by
  obtain ⟨Ω, hΩ, hell, hcpt, htr⟩ := exists_scusp_of_qc_bp d
  obtain ⟨f, hf, -, he⟩ := htr χ (indicator_mem_QC d χ hΩ hθ)
    (hasCompactSupportModConjAG_indicator d hcpt θ) (fun g _ hg => Set.indicator_of_notMem hg θ)
  exact ⟨f, hf, fun g hg =>
    (he (d.ellRegSet_subset_regularSet hg)).trans (Set.indicator_of_mem (hell hg) θ)⟩

/-- **`J(f) − m_geom(θ_f)` only depends on `θ_f` on `G_ell,reg(F)`** (Thesis Prop 7.4.1(ii)):
both sides are the defect of a virtual representation with character `θ_f` on the elliptic set
(`exists_virtual_spectral_ell`), and the defect vanishes on characters vanishing there
(`defect_eq_zero_of_vChar_eq_zero_ell`). -/
theorem distribJ_sub_mGeom_eq_of_eqOn_ell (h : HYP ψ d) {f f' : ↥d.G → ℂ}
    (hf : f ∈ ScuspTestFn d χ) (hf' : f' ∈ ScuspTestFn d χ)
    (he : Set.EqOn (thetaF d f) (thetaF d f') d.ellRegSet) :
    distribJ d ψ f - mGeom ψ d (thetaF d f) = distribJ d ψ f' - mGeom ψ d (thetaF d f') := by
  have hf₁ : f ∈ ScuspTestFn d χ.inv.inv := by rwa [CentralCharOn.inv_inv]
  have hf₁' : f' ∈ ScuspTestFn d χ.inv.inv := by rwa [CentralCharOn.inv_inv]
  obtain ⟨P, hP, hJ⟩ := exists_virtual_spectral_ell ψ d h χ.inv hf₁
  obtain ⟨P', hP', hJ'⟩ := exists_virtual_spectral_ell ψ d h χ.inv hf₁'
  have h0 := defect_eq_zero_of_vChar_eq_zero_ell ψ d h χ.inv (P - P') fun x hx => by
    rw [map_sub, Pi.sub_apply, hP x hx, hP' x hx, he hx, sub_self]
  rw [hJ, hJ', ← sub_eq_zero, ← map_sub, h0]

/-- The value `m_geom(θ) + (J(f_θ) − m_geom(θ_{f_θ}))`, for a chosen `f_θ` with `θ_{f_θ} = θ` on
`G_ell,reg(F)` (the formula for `J_qc` of Prop 12.2.3: the elliptic sum
`Σ_π D(π)(m(π̄) − m_geom(π̄)) ∫_{Γ_ell} D^G θ θ_π` is the defect of `θ_f` by Prop 7.4.1(ii)). -/
def jqcFun (θ : ↥(QC d χ)) : ℂ :=
  mGeom ψ d θ + (distribJ d ψ (exists_scusp_eqOn_ell d χ θ.2).choose -
    mGeom ψ d (thetaF d (exists_scusp_eqOn_ell d χ θ.2).choose))

/-- `jqcFun` may be computed with any `f` with `θ_f = θ` on `G_ell,reg(F)`. -/
theorem jqcFun_eq (h : HYP ψ d) (θ : ↥(QC d χ)) {f : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d χ)
    (he : Set.EqOn (thetaF d f) θ d.ellRegSet) :
    jqcFun ψ d χ θ = mGeom ψ d θ + (distribJ d ψ f - mGeom ψ d (thetaF d f)) := by
  obtain ⟨hf₀, he₀⟩ := (exists_scusp_eqOn_ell d χ θ.2).choose_spec
  unfold jqcFun
  rw [distribJ_sub_mGeom_eq_of_eqOn_ell ψ d χ h hf₀ hf fun x hx => (he₀ hx).trans (he hx).symm]

theorem jqcFun_add (h : HYP ψ d) (θ₁ θ₂ : ↥(QC d χ)) :
    jqcFun ψ d χ (θ₁ + θ₂) = jqcFun ψ d χ θ₁ + jqcFun ψ d χ θ₂ := by
  obtain ⟨f₁, hf₁, e₁⟩ := exists_scusp_eqOn_ell d χ θ₁.2
  obtain ⟨f₂, hf₂, e₂⟩ := exists_scusp_eqOn_ell d χ θ₂.2
  have hf := add_mem_scuspTestFn d χ hf₁ hf₂
  have hθ := thetaF_add d χ hf₁ hf₂
  have e : Set.EqOn (thetaF d (f₁ + f₂)) ((θ₁ + θ₂ : ↥(QC d χ)) : ↥d.G → ℂ) d.ellRegSet := by
    intro x hx
    rw [hθ (d.ellRegSet_subset_regularSet hx)]
    simp [e₁ hx, e₂ hx]
  -- rewrite the sum first: matching `jqcFun θ₁` against `jqcFun (θ₁ + θ₂)` is an expensive failure
  rw [jqcFun_eq ψ d χ h (θ₁ + θ₂) hf e, jqcFun_eq ψ d χ h θ₁ hf₁ e₁,
    jqcFun_eq ψ d χ h θ₂ hf₂ e₂]
  have h1 := GGPData.distribJ_add d χ ψ f₁ f₂ hf₁ hf₂
  have h2 : mGeom ψ d (thetaF d (f₁ + f₂)) =
      mGeom ψ d (thetaF d f₁) + mGeom ψ d (thetaF d f₂) :=
    (mGeom_congr_regularSet ψ d hθ).trans (mGeom_add ψ d
      (mem_QCfin_of_mem_QC d (thetaF_mem_QC d χ hf₁))
      (mem_QCfin_of_mem_QC d (thetaF_mem_QC d χ hf₂)))
  have h3 : mGeom ψ d ((θ₁ + θ₂ : ↥(QC d χ)) : ↥d.G → ℂ) = mGeom ψ d θ₁ + mGeom ψ d θ₂ :=
    mGeom_add ψ d (mem_QCfin_of_mem_QC d θ₁.2) (mem_QCfin_of_mem_QC d θ₂.2)
  linear_combination h1 - h2 + h3

theorem jqcFun_smul (h : HYP ψ d) (c : ℂ) (θ : ↥(QC d χ)) :
    jqcFun ψ d χ (c • θ) = c * jqcFun ψ d χ θ := by
  obtain ⟨f, hf, e⟩ := exists_scusp_eqOn_ell d χ θ.2
  have hcf := smul_mem_scuspTestFn d χ c hf
  have hθ := thetaF_smul d χ c hf
  have e' : Set.EqOn (thetaF d (c • f)) ((c • θ : ↥(QC d χ)) : ↥d.G → ℂ) d.ellRegSet := by
    intro x hx
    rw [hθ (d.ellRegSet_subset_regularSet hx), Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply,
      e hx]
  have h2 : mGeom ψ d (thetaF d (c • f)) = c * mGeom ψ d (thetaF d f) :=
    (mGeom_congr_regularSet ψ d hθ).trans
      (mGeom_smul ψ d c (mem_QCfin_of_mem_QC d (thetaF_mem_QC d χ hf)))
  have h3 : mGeom ψ d ((c • θ : ↥(QC d χ)) : ↥d.G → ℂ) = c * mGeom ψ d θ :=
    mGeom_smul ψ d c (mem_QCfin_of_mem_QC d θ.2)
  rw [jqcFun_eq ψ d χ h (c • θ) hcf e', jqcFun_eq ψ d χ h θ hf e, GGPData.distribJ_smul d ψ c f,
    h2, h3]
  ring

/-- `J_qc` as a linear map (Thesis Prop 12.2.3; linear by `distribJ_add`, `thetaF_add`,
`mGeom_add` and their scalar versions). -/
def jqcLin (h : HYP ψ d) : ↥(QC d χ) →ₗ[ℂ] ℂ where
  toFun := jqcFun ψ d χ
  map_add' := jqcFun_add ψ d χ h
  map_smul' := jqcFun_smul ψ d χ h

/-- **Thesis Prop 12.2.3, existence**.
Assume (HYP).  Then `J` extends to a continuous linear form on `QC(G, χ⁻¹)` (Lean: `QC d χ`) with
`Supp(J_qc − m_geom) ⊆ G_ell` (see `IsJqc` for why not `Supp J_qc ⊆ G_ell`).
Formula: `J_qc(θ) = m_geom(θ) + Σ_{π ∈ 𝒳_ell(G,χ)} D(π)(m(π̄) − m_geom(π̄)) ∫_{Γ_ell(G)} D^G θ θ_π`.
Here: `J_qc(θ) = m_geom(θ) + (J(f) − m_geom(θ_f))` for any `f` with `θ_f = θ` on `G_ell,reg(F)`
(`jqcLin`), which is the same by Prop 7.4.1(ii); it avoids BP Cor 5.7.2(ii), Prop 4.8.1(ii) and
(2.7.2).  Continuity in the `p`-adic topology is compact support (`continuous_qc_of_local`).
Status: **proved** from `exists_qcCutoff_ellRegSet`, `exists_scusp_eqOn_ell` (both from BP Cor 5.7.2(i)),
`exists_qcCutoff_mGeom` (proved from the `InvariantSets` axioms and `finite_gammaClass`),
`exists_virtual_spectral_ell`, `defect_eq_zero_of_vChar_eq_zero_ell`, and the linearity of
`m_geom`. -/
theorem exists_isJqc (h : HYP ψ d) (χ : CentralCharOn d) : ∃ J, IsJqc ψ d χ J := by
  refine ⟨jqcLin ψ d χ h, ⟨fun θ θ' he => ?_, fun f hf => ?_, ?_, fun θ hθ => ?_⟩⟩
  · obtain ⟨f, hf, e⟩ := exists_scusp_eqOn_ell d χ θ.2
    change jqcFun ψ d χ θ = jqcFun ψ d χ θ'
    rw [jqcFun_eq ψ d χ h θ hf e,
      jqcFun_eq ψ d χ h θ' hf fun x hx => (e hx).trans (he (d.ellRegSet_subset_regularSet hx)),
      mGeom_congr_regularSet ψ d he]
  · change distribJ d ψ f = jqcFun ψ d χ ⟨thetaF d f, thetaF_mem_QC d χ hf⟩
    rw [jqcFun_eq ψ d χ h _ hf fun _ _ => rfl]
    ring
  · obtain ⟨Ωe, hΩe, hell⟩ := exists_qcCutoff_ellRegSet d
    obtain ⟨Ωm, hΩm, hm⟩ := exists_qcCutoff_mGeom ψ d
    refine continuous_qc_of_local d χ _ (isQCCutoff_union d hΩe hΩm) fun θ hθ => ?_
    change jqcFun ψ d χ θ = 0
    rw [jqcFun_eq ψ d χ h θ (zero_mem_scuspTestFn d χ) fun x hx => by
        rw [thetaF_zero d (d.ellRegSet_subset_regularSet hx)]
        exact (hθ ⟨Or.inl (hell hx), d.ellRegSet_subset_regularSet hx⟩).symm,
      hm χ θ θ.2 (fun g hg => hθ ⟨Or.inr hg.1, hg.2⟩),
      mGeom_congr_regularSet ψ d (thetaF_zero d), mGeom_zero, distribJ_zero]
    ring
  · change jqcFun ψ d χ θ = mGeom ψ d θ
    rw [jqcFun_eq ψ d χ h θ (zero_mem_scuspTestFn d χ) fun x hx =>
        (thetaF_zero d (d.ellRegSet_subset_regularSet hx)).trans (hθ hx).symm,
      mGeom_congr_regularSet ψ d (thetaF_zero d), mGeom_zero, distribJ_zero]
    ring

end Existence

set_option maxHeartbeats 400000 in
/-- **Uniqueness of `J_qc`** (Thesis Prop 12.2.3, unicity; BP Cor 5.7.2(i)).  Two linear forms
with `IsJqc` agree: since `J − m_geom` only sees `θ` on `G_ell,reg(F)` (`eq_mGeom_of_eqOn_ell`),
`J(θ) = m_geom(θ) + J(f) − m_geom(θ_f)` for any `f` with `θ_f = θ` there (`exists_scusp_eqOn_ell`).
(Continuity gives a second proof, by cutting `θ` with a set of the projective system.) -/
theorem IsJqc.unique {χ : CentralCharOn d} {J J' : ↥(QC d χ) →ₗ[ℂ] ℂ} (hJ : IsJqc ψ d χ J)
    (hJ' : IsJqc ψ d χ J') : J = J' := by
  ext θ
  obtain ⟨f, hf, e⟩ := exists_scusp_eqOn_ell d χ θ.2
  obtain ⟨θf, hθf⟩ : ∃ θf : ↥(QC d χ), θf = ⟨thetaF d f, thetaF_mem_QC d χ hf⟩ := ⟨_, rfl⟩
  have hθfv : (θf : ↥d.G → ℂ) = thetaF d f := by rw [hθf]
  have hm : mGeom ψ d ((θ - θf : ↥(QC d χ)) : ↥d.G → ℂ) = mGeom ψ d θ - mGeom ψ d θf := by
    have e1 : ((θ - θf : ↥(QC d χ)) : ↥d.G → ℂ) = (θ : ↥d.G → ℂ) + (-1 : ℂ) • (θf : ↥d.G → ℂ) := by
      rw [Submodule.coe_sub, neg_one_smul, sub_eq_add_neg]
    have hq : (θf : ↥d.G → ℂ) ∈ QCfin d := mem_QCfin_of_mem_QC d θf.2
    rw [e1, mGeom_add ψ d (mem_QCfin_of_mem_QC d θ.2) (Submodule.smul_mem _ _ hq),
      mGeom_smul ψ d (-1) hq]
    ring
  have h0 : Set.EqOn ((θ - θf : ↥(QC d χ)) : ↥d.G → ℂ) 0 d.ellRegSet := fun x hx => by
    rw [Submodule.coe_sub, Pi.sub_apply, hθfv, e hx, sub_self, Pi.zero_apply]
  -- (`rw` would try to close goals by `rfl`, an expensive failing unfolding of `mGeom`)
  have k : J θ - J θf = mGeom ψ d θ - mGeom ψ d θf :=
    (map_sub J θ θf).symm.trans ((hJ.eq_mGeom_of_eqOn_ell _ h0).trans hm)
  have k' : J' θ - J' θf = mGeom ψ d θ - mGeom ψ d θf :=
    (map_sub J' θ θf).symm.trans ((hJ'.eq_mGeom_of_eqOn_ell _ h0).trans hm)
  have d1 : J θf = J' θf := by
    subst hθf
    exact (hJ.distribJ_eq f hf).symm.trans (hJ'.distribJ_eq f hf)
  rw [eq_add_of_sub_eq k, eq_add_of_sub_eq k', d1]

theorem isJqc_jqc (h : HYP ψ d) (χ : CentralCharOn d) : IsJqc ψ d χ (jqc ψ d χ) := by
  classical
  have hex := exists_isJqc ψ d h χ
  unfold jqc
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact hex.choose_spec

/-- **Under (HYP), `J(f)` depends only on `θ_f|_{G_reg}`** (Thesis Prop 12.2.3). -/
theorem distribJ_eq_of_thetaF_eqOn (h : HYP ψ d) (χ : CentralCharOn d) {f f' : ↥d.G → ℂ}
    (hf : f ∈ ScuspTestFn d χ) (hf' : f' ∈ ScuspTestFn d χ)
    (he : Set.EqOn (thetaF d f) (thetaF d f') (regularSet d.G d.lie)) :
    distribJ d ψ f = distribJ d ψ f' := by
  have hJ := isJqc_jqc ψ d h χ
  rw [hJ.distribJ_eq f hf, hJ.distribJ_eq f' hf']
  exact hJ.congr_regularSet _ _ he

/-! ## 3. Localization away from `1` (Thesis Prop 12.3.1) -/

section Away

variable (χ : CentralCharOn d)

/-- `Ω` is **good**: the geometric expansion `J(f) = m_geom(θ_f)` holds for every
`f ∈ ScuspTestFn d χ` supported in `Ω`. -/
def IsGeomGood (Ω : Set ↥d.G) : Prop :=
  ∀ f ∈ ScuspTestFn d χ, Function.support f ⊆ Ω → distribJ d ψ f = mGeom ψ d (thetaF d f)

/-- `c` is **near-central**: `1` lies in the closure of `A_G(F) · c^{G(F)}`; equivalently (Jordan
decomposition) the semisimple part of `c` lies in `A_G(F)`, i.e. its image in
`SO(W) × SO(V)` is `1`.  These are the points where (HYP) cannot be used for the descended triple
(`restrictFix` needs `x̄ ≠ 1`, `dimG_restrictFix_lt`). -/
def IsNearCentral (c : ↥d.G) : Prop :=
  ∀ U ∈ 𝓝 (1 : ↥d.G), ∃ (a : ↥d.AG) (x : ↥d.G), ((a : ↥d.G))⁻¹ * (x * c * x⁻¹) ∈ U

/-- **A `p`-adic field has a nontrivial continuous additive character** (Thesis §2.4 fixes one; here
it is constructed, so that the quasi-character conditions `∀ ψ, IsQuasiCharacter … ψ θ` are not
vacuous).  `O = {‖x‖ < 1}` is an open subgroup (ultrametric), `F/O` is a nonzero discrete abelian
group (`‖a‖ > 1` for some `a`), a character `F/O → ℚ/ℤ` nonzero at `a` exists (`ℚ/ℤ` is divisible,
`CharacterModule.exists_character_apply_ne_zero_of_ne_zero`), and `q ↦ e^{2πiq}` embeds `ℚ/ℤ` in
the circle. -/
theorem nonempty_nontrivialAddChar : Nonempty (NontrivialAddChar F) := by
  classical
  let O : OpenAddSubgroup F := IsUltrametricDist.ball_openAddSubgroup F (r := 1) one_pos
  obtain ⟨a, ha⟩ := NormedField.exists_lt_norm F 1
  have haO : (QuotientAddGroup.mk a : F ⧸ O.toAddSubgroup) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    intro h
    have h' : a ∈ Metric.ball (0 : F) 1 := h
    rw [mem_ball_zero_iff] at h'
    linarith
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero haO
  let φ : ℚ →+ Additive Circle :=
    { toFun := fun q => Additive.ofMul (Circle.exp (2 * Real.pi * q))
      map_zero' := by simp
      map_add' := fun q r => by
        rw [← ofMul_mul, ← Circle.exp_add]
        push_cast; ring_nf }
  have hφ : ∀ q ∈ AddSubgroup.zmultiples (1 : ℚ), φ q = 0 := by
    rintro q ⟨n, rfl⟩
    change Additive.ofMul (Circle.exp (2 * Real.pi * ((n • (1 : ℚ) : ℚ) : ℝ))) = 0
    simp only [zsmul_eq_mul, mul_one, Rat.cast_intCast]
    rw [Circle.exp_two_pi_mul_int]; rfl
  let e : AddCircle (1 : ℚ) →+ Additive Circle := QuotientAddGroup.lift _ φ hφ
  let f : F → Circle := fun x => Additive.toMul (e (c (QuotientAddGroup.mk x)))
  have hcont : Continuous f := by
    have : Continuous (fun y : F ⧸ O.toAddSubgroup => Additive.toMul (e (c y))) :=
      continuous_of_discreteTopology
    exact this.comp QuotientAddGroup.continuous_mk
  refine ⟨⟨{ toFun := f, map_zero_eq_one' := ?_, map_add_eq_mul' := ?_ }, hcont, ?_⟩⟩
  · simp [f]
  · intro x y
    simp only [f, QuotientAddGroup.mk_add, map_add, toMul_add]
  · intro h1
    apply hc
    obtain ⟨q, hq⟩ := QuotientAddGroup.mk_surjective (c (QuotientAddGroup.mk a))
    have hfa : f a = 1 := by
      have := congrArg (fun ψ : AddChar F Circle => ψ a) h1
      simpa using this
    have hq' : Circle.exp (2 * Real.pi * q) = 1 := by
      have : f a = Additive.toMul (φ q) := by
        simp only [f, ← hq]; rfl
      rw [hfa] at this
      exact this.symm
    obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp hq'
    have hqn : (q : ℝ) = n := by
      have hpi : (2 * Real.pi) ≠ 0 := by positivity
      field_simp at hn
      linarith
    have hqn' : q = n := by exact_mod_cast hqn
    rw [← hq, hqn']
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨n, by simp⟩

/-- **Near `A_G(F)` a quasi-character vanishing near `1` vanishes** (the
separate argument for `x̄ = 1`).  If `θ ∈ QC(G, χ⁻¹)` vanishes on the regular elements of a
neighbourhood `U` of `1` and `c` is near-central, then `θ` vanishes on the regular elements of an
invariant clopen neighbourhood of `c`.
Proof route: `θ` is invariant and `A_G(F)`-equivariant on `G_reg(F)` (and `G_reg(F)` is stable under
conjugation and `A_G(F)`), so it vanishes on the regular elements of
`V = {g | ∃ a x, a⁻¹ x g x⁻¹ ∈ U}`, an open invariant `A_G(F)`-stable set containing `c`, and
containing the closure of `A_G(F) c^{G(F)}` (all `a u`, `u` unipotent); inside `V` take
`Ω = A_G(F) · a₀ exp(ω)` with `c ∈ a₀ exp(ω)` and `ω` a small `G(F)`-excellent compact open
neighbourhood of `0` in `𝔤(F)` (BP §3.3), which is open and closed.
Status: **proved** from the cited `hc_exists_invariantClopen_nearCentral`
(`Literature/InvariantSets.lean`: an invariant clopen `Ω` containing the near-central set, every
element of which is conjugate into `U` modulo `A_G(F)`) and the invariance and `A_G(F)`-equivariance
of `θ` on `G_reg(F)` (the invariance is part of the quasi-character property, for some `ψ`:
`nonempty_nontrivialAddChar`). -/
theorem exists_null_nhd_of_nearCentral {θ : ↥d.G → ℂ} (hθ : θ ∈ QC d χ)
    (h1 : VanishesNearOne d θ) {c : ↥d.G} (hc : IsNearCentral d c) :
    ∃ Ω, IsInvariantClopen d Ω ∧ c ∈ Ω ∧ ∀ g ∈ Ω, g ∈ regularSet d.G d.lie → θ g = 0 := by
  obtain ⟨U, hU, h0⟩ := h1
  obtain ⟨Ω, hΩ, hnc, hΩU⟩ := hc_exists_invariantClopen_nearCentral d hU
  refine ⟨Ω, hΩ, hnc c hc, fun g hgΩ hg => ?_⟩
  obtain ⟨ψ₀⟩ := nonempty_nontrivialAddChar (F := F)
  obtain ⟨a, x, hax⟩ := hΩU g hgΩ
  have hreg : x * g * x⁻¹ ∈ regularSet d.G d.lie := conj_mem_regularSet d x g hg
  have e := h0 _ hax (by simpa using mul_mem_regularSet_of_mem_AG d a⁻¹ hreg)
  have e' : θ ((a⁻¹ : ↥d.AG) * (x * g * x⁻¹)) = 0 := by simpa using e
  rw [hθ.2 a⁻¹ _ hreg, mul_eq_zero] at e'
  rcases e' with e' | e'
  · exact absurd e' (Circle.coe_ne_zero _)
  · rwa [(hθ.1 ψ₀).1 x g hg] at e'

/-- **`θ_f` vanishes off an invariant clopen set containing `supp f`** (BP §5.2, §5.5: `θ_f(x)` is,
up to sign and `D^G(x)^{1/2}`, a weighted orbital integral of `f` at `x`, which vanishes when the
conjugacy class of `x` misses `supp f`).  Route from `IsThetaF`: for a test function `f'` supported
in the open invariant set `G(F) ∖ Ω`, the orbital pairing `∫∫ f(y⁻¹ x y) f'(x)` vanishes, so
`∫ θ_f f' = 0`; hence `θ_f = 0` almost everywhere on `G(F) ∖ Ω`, and everywhere on its regular
points by local constancy of `θ_f` on `G_reg(F)`.
Status: **proved**: `1_Ω f = f`, so `θ_f = θ_{1_Ω f} = 1_Ω θ_f` on `G_reg(F)` (`isThetaF_indicator`
and uniqueness `eqOn_thetaF`); no literature input. -/
theorem thetaF_eq_zero_of_support_subset {f : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d χ)
    {Ω : Set ↥d.G} (hΩ : IsInvariantClopen d Ω) (hs : Function.support f ⊆ Ω) :
    ∀ g ∈ regularSet d.G d.lie, g ∉ Ω → thetaF d f g = 0 := by
  intro g hg hgΩ
  have hθ : IsThetaF d f (Ω.indicator (thetaF d f)) := by
    have := isThetaF_indicator d (thetaF_spec d χ hf).1 hΩ
    rwa [Set.indicator_eq_self.2 hs] at this
  exact (eqOn_thetaF d hθ hg).trans (Set.indicator_of_notMem hgΩ _)

/-- **Away from the elliptic set the expansion is free** (the case of non-elliptic
points): if the invariant clopen `Ω` contains no
elliptic regular element, then `θ_f = 0` on `G_ell,reg(F)` for `f` supported in `Ω`, and
`J(f) = J_qc(θ_f) = m_geom(θ_f)` by `Supp(J_qc − m_geom) ⊆ G_ell` (`IsJqc.eq_mGeom_of_eqOn_ell`). -/
theorem isGeomGood_of_disjoint_ell (h : HYP ψ d) {Ω : Set ↥d.G} (hΩ : IsInvariantClopen d Ω)
    (hell : ∀ g ∈ Ω, g ∉ d.ellRegSet) : IsGeomGood ψ d χ Ω := by
  intro f hf hs
  have hJ := isJqc_jqc ψ d h χ
  rw [hJ.distribJ_eq f hf]
  refine hJ.eq_mGeom_of_eqOn_ell _ fun g hg => ?_
  exact thetaF_eq_zero_of_support_subset d χ hf hΩ hs g (d.ellRegSet_subset_regularSet hg)
    fun hgΩ => hell g hgΩ hg

/-- **Thesis Prop 12.3.1, local form at a point that is not near-central** (BP Prop 11.6.1).  Assume (HYP).  Every `c` whose semisimple part `x` is not in
`A_G(F)` has an invariant clopen neighbourhood `Ω` that either contains no elliptic regular element
(the case `x` not elliptic, handled by `isGeomGood_of_disjoint_ell`) or on which the geometric
expansion holds (the case `x` elliptic).

Proof route for elliptic `x`.  Take `Ω = A_G(F) Ω_x^{G(F)}` for a small
`G`-good compact open `Ω_x ∋ x` in `G_x(F)`, so `1 ∉ Ω`.
* If `x` is not conjugate into `H_ss(F)`, then (BP (11.1.2)) `Ω ∩ H(F)^{G(F)} = ∅`, so `J(f) = 0`
  (`distribJ_eq_zero_of_conj_notMem`) and `m_geom(θ_f) = 0` (`Γ(G,H) ⊆ Γ(H)`).
* Otherwise `x ∈ GSpin(W)_ss(F)`, `x̄ ≠ 1`, and `G_x = G'_x · G''_x` (`centralizer_diag_eq`) with
  `(G'_x, H'_x, ξ'_x)` the GGP triple `restrictFix x` of the fixed space `W'_x`, of smaller
  dimension (`dimG_restrictFix_lt`); **(HYP)** gives `J^{G'_x} = m_geom^{G'_x}` there.  On
  `G''_x = H''_x × H''_x` (centre compact modulo `A_{G,H}`, as `x` is elliptic) the distribution is
  Arthur's `J^{A,H''_x}` (Thesis Thm 4.7.1; Arthur, Publ. IHÉS 73
  (1991); Waldspurger 1995), computed by the elliptic integral.  The identity
  `J(f) = J^{G'_x}(f'_x) J^{A,H''_x}((η_{x,G}^H)^{1/2} f''_{x,1}, f''_{x,2})` (Thesis (12.3.3)) uses
  BP (3.2.5), (11.1.2), Prop 5.7.1 and Thesis Thm 10.1.1(ii); the density of tensor products uses
  BP Cor 5.7.2(i) and Prop 4.4.1(v); the comparison with `m_geom` is Thesis Prop 12.1.1(ii).
Status: SORRY (own work; the analytic heart of Prop 12.3.1). -/
theorem exists_good_nhd_of_not_nearCentral (h : HYP ψ d) {c : ↥d.G} (hc : ¬ IsNearCentral d c) :
    ∃ Ω, IsInvariantClopen d Ω ∧ c ∈ Ω ∧ ((∀ g ∈ Ω, g ∉ d.ellRegSet) ∨ IsGeomGood ψ d χ Ω) := by
  sorry

/-- The good neighbourhoods of points that are not near-central (both cases). -/
theorem exists_isGeomGood_of_not_nearCentral (h : HYP ψ d) {c : ↥d.G}
    (hc : ¬ IsNearCentral d c) : ∃ Ω, IsInvariantClopen d Ω ∧ c ∈ Ω ∧ IsGeomGood ψ d χ Ω := by
  obtain ⟨Ω, hΩ, hcΩ, hor⟩ := exists_good_nhd_of_not_nearCentral ψ d χ h hc
  rcases hor with hell | hg
  · exact ⟨Ω, hΩ, hcΩ, isGeomGood_of_disjoint_ell ψ d χ h hΩ hell⟩
  · exact ⟨Ω, hΩ, hcΩ, hg⟩

/-- **`J(f) = 0` when `f` vanishes on all `G(F)`-conjugates of `H(F)`** (the first case of Thesis
Prop 12.3.1: `K(f, x) = ∫ f(x⁻¹ h x) ξ(h) dh = 0`). -/
theorem distribJ_eq_zero_of_conj_notMem {f : ↥d.G → ℂ}
    (hf : ∀ (x : ↥d.G) (h : ↥d.H), f (x⁻¹ * (h : ↥d.G) * x) = 0) : distribJ d ψ f = 0 := by
  have hK : ∀ x, kernelK d ψ f x = 0 := by
    intro x
    unfold kernelK kernelIntegrand
    simp [hf]
  unfold distribJ
  simp [hK]

/-- If `θ_f = 0` on `G_reg(F)`, the geometric expansion holds for `f` (both sides vanish; uses
(HYP) through `distribJ_eq_of_thetaF_eqOn`). -/
theorem geomAt_of_thetaF_eqOn_zero (h : HYP ψ d) {f : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d χ)
    (h0 : Set.EqOn (thetaF d f) 0 (regularSet d.G d.lie)) :
    distribJ d ψ f = mGeom ψ d (thetaF d f) := by
  rw [distribJ_eq_of_thetaF_eqOn ψ d h χ hf (zero_mem_scuspTestFn d χ)
      (fun g hg => (h0 hg).trans (thetaF_zero d hg).symm),
    distribJ_zero, mGeom_congr_regularSet ψ d h0, mGeom_zero]

/-- **The partition of unity of Thesis Prop 12.3.1** (BP §11.6): if every `Ω i` is invariant clopen
and either good or a set where `θ` vanishes, and `θ_f` is supported (on `G_reg(F)`) in
`⋃_{i ∈ s} Ω i` and inside the support of `θ`, then `J(f) = m_geom(θ_f)`.  Induction on `s`,
cutting `f` by `Ω i` (`exists_scusp_cut`). -/
theorem geomAt_glue (h : HYP ψ d) {ι : Type*} (Ω : ι → Set ↥d.G)
    (hΩ : ∀ i, IsInvariantClopen d (Ω i)) (θ : ↥d.G → ℂ)
    (hgood : ∀ i, IsGeomGood ψ d χ (Ω i) ∨ ∀ g ∈ Ω i, g ∈ regularSet d.G d.lie → θ g = 0)
    (s : Finset ι) : ∀ f ∈ ScuspTestFn d χ,
      (∀ g ∈ regularSet d.G d.lie, thetaF d f g ≠ 0 → θ g ≠ 0 ∧ g ∈ ⋃ i ∈ s, Ω i) →
      distribJ d ψ f = mGeom ψ d (thetaF d f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f hf hs
    refine geomAt_of_thetaF_eqOn_zero ψ d χ h hf fun g hg => ?_
    by_contra hne
    simpa using (hs g hg hne).2
  | insert i s _ ih =>
    intro f hf hs
    obtain ⟨f₁, hf₁, hsupp, hθ₁⟩ := exists_scusp_cut d χ hf (hΩ i)
    have hf₂ : f - f₁ ∈ ScuspTestFn d χ := sub_mem_scuspTestFn d χ hf hf₁
    have hsum : f₁ + (f - f₁) = f := add_sub_cancel f₁ f
    have hθsum : Set.EqOn (thetaF d f) (thetaF d f₁ + thetaF d (f - f₁))
        (regularSet d.G d.lie) := by
      have e := thetaF_add d χ hf₁ hf₂
      rwa [hsum] at e
    -- `θ_{f − f₁} = 1_{(Ω i)ᶜ} θ_f` on the regular set
    have hθ₂ : ∀ g ∈ regularSet d.G d.lie,
        thetaF d (f - f₁) g = thetaF d f g - (Ω i).indicator (thetaF d f) g := by
      intro g hg
      have e₁ := hθsum hg
      have e₂ := hθ₁ hg
      simp only [Pi.add_apply] at e₁
      rw [← e₂]
      linear_combination -e₁
    -- the piece in `Ω i`
    have hJ₁ : distribJ d ψ f₁ = mGeom ψ d (thetaF d f₁) := by
      rcases hgood i with hg | hnull
      · exact hg f₁ hf₁ hsupp
      · refine geomAt_of_thetaF_eqOn_zero ψ d χ h hf₁ fun g hg => ?_
        rw [hθ₁ hg]
        by_cases hgi : g ∈ Ω i
        · rw [Set.indicator_of_mem hgi]
          by_contra hne
          exact (hs g hg hne).1 (hnull g hgi hg)
        · rw [Set.indicator_of_notMem hgi]; rfl
    -- the rest, by induction
    have hJ₂ : distribJ d ψ (f - f₁) = mGeom ψ d (thetaF d (f - f₁)) := by
      refine ih (f - f₁) hf₂ fun g hg hne => ?_
      rw [hθ₂ g hg] at hne
      by_cases hgi : g ∈ Ω i
      · rw [Set.indicator_of_mem hgi, sub_self] at hne
        exact absurd rfl hne
      · rw [Set.indicator_of_notMem hgi, sub_zero] at hne
        obtain ⟨hθg, hmem⟩ := hs g hg hne
        refine ⟨hθg, ?_⟩
        rw [Finset.set_biUnion_insert] at hmem
        exact hmem.resolve_left hgi
    have hJ := GGPData.distribJ_add d χ ψ f₁ (f - f₁) hf₁ hf₂
    rw [hsum] at hJ
    rw [hJ, hJ₁, hJ₂, mGeom_congr_regularSet ψ d hθsum,
      mGeom_add ψ d (mem_QCfin_of_mem_QC d (thetaF_mem_QC d χ hf₁))
        (mem_QCfin_of_mem_QC d (thetaF_mem_QC d χ hf₂))]

/-- **Thesis Prop 12.3.1, test-function form**.  Assume
(HYP).  If `f ∈ ScuspTestFn d χ` and `1 ∉ Supp θ_f`, then `J(f) = m_geom(θ_f)`.
Status: **proved** from the partition of unity `geomAt_glue`, the compact support of `θ_f`
modulo conjugation and `A_G(F)` (`thetaF_hasCompactSupportModConjAG`), the cut
`exists_scusp_cut`, and the two local statements `exists_null_nhd_of_nearCentral` (near `A_G(F)`)
and `exists_good_nhd_of_not_nearCentral` (semisimple descent with (HYP) for `restrictFix`, at
elliptic points; non-elliptic points by `isGeomGood_of_disjoint_ell`). -/
theorem geomAt_away (h : HYP ψ d) (χ : CentralCharOn d) {f : ↥d.G → ℂ}
    (hf : f ∈ ScuspTestFn d χ) (h1 : VanishesNearOne d (thetaF d f)) :
    distribJ d ψ f = mGeom ψ d (thetaF d f) := by
  classical
  obtain ⟨C, hC, hsupp⟩ := thetaF_hasCompactSupportModConjAG d χ hf
  have hloc : ∀ c : ↥d.G, ∃ Ω, IsInvariantClopen d Ω ∧ c ∈ Ω ∧ (IsGeomGood ψ d χ Ω ∨
      ∀ g ∈ Ω, g ∈ regularSet d.G d.lie → thetaF d f g = 0) := by
    intro c
    by_cases hc : IsNearCentral d c
    · obtain ⟨Ω, hΩ, hcΩ, h0⟩ :=
        exists_null_nhd_of_nearCentral d χ (thetaF_mem_QC d χ hf) h1 hc
      exact ⟨Ω, hΩ, hcΩ, Or.inr h0⟩
    · obtain ⟨Ω, hΩ, hcΩ, hg⟩ := exists_isGeomGood_of_not_nearCentral ψ d χ h hc
      exact ⟨Ω, hΩ, hcΩ, Or.inl hg⟩
  choose Ω hΩ hcΩ hgood using hloc
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun c : C => Ω c) (fun c => (hΩ c).1)
    (fun c hc => Set.mem_iUnion.2 ⟨⟨c, hc⟩, hcΩ c⟩)
  refine geomAt_glue ψ d χ h (fun c : C => Ω c) (fun c => hΩ c) (thetaF d f)
    (fun c => hgood c) t f hf fun g hg hne => ⟨hne, ?_⟩
  obtain ⟨a, x, c, hc, rfl⟩ := hsupp g hg hne
  obtain ⟨i, hi, hci⟩ := Set.mem_iUnion₂.1 (ht hc)
  exact Set.mem_biUnion hi ((hΩ i).2.2.2 a _ ((hΩ i).2.2.1 x c hci))

end Away

end GSpinGGP
