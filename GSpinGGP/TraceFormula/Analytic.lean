/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Basic
import GSpinGGP.Literature.Measure
import GSpinGGP.Literature.HarishChandra

/-!
# The local trace formula: analytic objects and estimates

This file states the analytic heart
of Thesis Ch. 8 and 10 and proves the bookkeeping around it.

## Definitions

* log-norms modulo a subgroup: `logNormModSub`, `logNormMod` (modulo `A_{G,H}`, Thesis
  §8.1–8.2), `logNormModAG` (modulo `A_G`, used in `𝒞(A_G(F)\G(F), χ⁻¹)`), and `logNormHG` on
  `H(F)\G(F)/A_G(F)` (Thesis §8.4, §10.1);
* `xiHG`: the function `Ξ^{H\G}_C(x) = vol(xC)^{-1/2}` (Thesis §8.4);
* `IwasawaDatum`: a minimal parabolic `P₀` (stabilizer of full isotropic flags), a compact open
  subgroup `K` and `G = P₀ K`; `deltaP0` (the modular character of `P₀`), `iwasawaP` and
  Harish-Chandra's function `xiHC` (`Ξ^G`, BP §1.5);
* the Harish-Chandra Schwartz space `HCSchwartzChi d χ IW` = `𝒞(A_G(F)\G(F), χ⁻¹)` (Thesis
  §2.3), its seminorms `schwartzSeminorm`, and the strongly cuspidal part `ScuspSchwartz`.

## Results

* Proved: `kernelK_integrable` (the integral defining `K(f,x)` converges for
  `f ∈ ScuspTestFn`), `kernelK_add`, `kernelK_smul`, `distribJ_add`, `distribJ_smul`,
  `scuspTestFn_subset_scuspSchwartz` (`C_c^∞` strongly cuspidal functions are Schwartz), and the
  supporting lemmas: continuity of `λ` and `ξ`, properties of `δ_{P₀}` and a lower bound for
  `Ξ^G` on compact sets, van Dantzig's theorem, uniform local constancy, log-norm lemmas.
* `sorry` (own work, Thesis Ch. 8 and 10, adapted from BP Ch. 6, 8): `kernelK_bound` (Thm 10.1.1(i)),
  `kernelK_bound_scusp` (Thm 10.1.1(ii)), `distribJ_convergent` (Thm 10.1.1 + BP Prop 6.7.1(iii)),
  `lemma_6_5_1_i/ii/iii` (Thesis Lemma 8.2.1), `exists_good_minimal_parabolic` (Thesis
  Prop 8.1.1(i)).

## Conventions on `H\G` (see the docstrings of `logNormHG`, `lemma_6_5_1_i`)

* All functions on `H(F)\G(F)` in Thesis Ch. 8 and 10 are used on `H(F)\G(F)/A_G(F)`; the log-norm
  `σ_{H\G}` there must be read as the log-norm of `H(F)\G(F)/A_G(F)` (the infimum over
  `H(F) x A_G(F)`), otherwise Thm 10.1.1(ii) forces `K(f,·) = 0`.
* Lemma 8.2.1(i) integrates over `H₀(F)/A_{G,H}(F)`, not `H₀(F)/A_{H₀}(F)` (they differ when `W`
  is a hyperbolic plane).
-/

open MeasureTheory Topology Filter
open scoped Pointwise

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-! ### The modular character on a group with a compact open subgroup -/

section ModularCharacter

variable {G₀ : Type*} [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀]
  [LocallyCompactSpace G₀]

/-- The modular character is trivial on a compact open subgroup `E` (right translation by
`k ∈ E` maps `E`, a set of finite positive Haar measure, to itself). -/
theorem modularCharacter_eq_one_of_mem (E : Subgroup G₀) (hEo : IsOpen (E : Set G₀))
    (hEc : IsCompact (E : Set G₀)) (k : G₀) (hk : k ∈ E) : Measure.modularCharacter k = 1 := by
  borelize G₀
  set μ : Measure G₀ := Measure.haar
  have hcl : closure (E : Set G₀) = E := (Subgroup.isClosed_of_isOpen E hEo).closure_eq
  have h := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure
    (Measure.map (· * k) μ) μ (s := (E : Set G₀)) (by rw [hcl]; exact hEc)
  have hpre : (· * k) ⁻¹' (E : Set G₀) = E := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact ⟨fun hx => by simpa using E.mul_mem hx (E.inv_mem hk), fun hx => E.mul_mem hx hk⟩
  rw [Measure.map_apply (measurable_mul_const k) hEo.measurableSet, hpre] at h
  have hpos : μ E ≠ 0 := (hEo.measure_pos μ ⟨1, E.one_mem⟩).ne'
  have htop : μ E ≠ ⊤ := hEc.measure_lt_top.ne
  have h1 : ((Measure.haarScalarFactor (Measure.map (· * k) μ) μ : NNReal) : ENNReal) = 1 := by
    rw [ENNReal.smul_def, smul_eq_mul] at h
    have h' : 1 * μ E = _ * μ E := (one_mul (μ E)).trans h
    exact ((ENNReal.mul_left_inj hpos htop).mp h').symm
  show Measure.modularCharacterFun k = 1
  rw [Measure.modularCharacterFun_eq_haarScalarFactor μ k]
  exact_mod_cast h1

/-- The modular character is trivial on central elements. -/
theorem modularCharacter_eq_one_of_central (a : G₀) (ha : ∀ y : G₀, y * a = a * y) :
    Measure.modularCharacter a = 1 := by
  borelize G₀
  have e : (fun y : G₀ => y * a) = fun y => a * y := funext ha
  have hmap : Measure.map (· * a) (Measure.haar : Measure G₀) = Measure.haar := by
    rw [e]
    exact map_mul_left_eq_self (Measure.haar : Measure G₀) a
  show Measure.modularCharacterFun a = 1
  rw [Measure.modularCharacterFun_eq_haarScalarFactor (Measure.haar : Measure G₀) a]
  simp only [hmap, Measure.haarScalarFactor_self]

/-- The modular character is locally constant if there is a compact open subgroup. -/
theorem isLocallyConstant_modularCharacter (E : Subgroup G₀) (hEo : IsOpen (E : Set G₀))
    (hEc : IsCompact (E : Set G₀)) :
    IsLocallyConstant (fun p : G₀ => (Measure.modularCharacter p : ℝ)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (E : Set G₀),
    hEo.preimage (continuous_const.mul continuous_id), by simp, fun y hy => ?_⟩
  have e : y = x * (x⁻¹ * y) := by group
  rw [e, map_mul, modularCharacter_eq_one_of_mem E hEo hEc _ hy, mul_one]

/-- On a compact set, the modular character is bounded below by a positive constant (if there
is a compact open subgroup). -/
theorem exists_lowerBound_modularCharacter (E : Subgroup G₀) (hEo : IsOpen (E : Set G₀))
    (hEc : IsCompact (E : Set G₀)) (S : Set G₀) (hS : IsCompact S) :
    ∃ m : ℝ, 0 < m ∧ ∀ p ∈ S, m ≤ (Measure.modularCharacter p : ℝ) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨p0, -, hmin⟩ :=
    hS.exists_isMinOn hne (isLocallyConstant_modularCharacter E hEo hEc).continuous.continuousOn
  exact ⟨_, by exact_mod_cast Measure.modularCharacterFun_pos p0, fun p hp => hmin hp⟩

/-- If `c ≤ φ` with `c > 0` on a finite nonzero measure space, then
`((μ X)⁻¹ ∫ φ dμ)⁻¹ ≤ c⁻¹` (the left side is `0` when `φ` is not integrable). -/
theorem inv_mul_integral_inv_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (hμ : μ ≠ 0) (φ : X → ℝ) (c : ℝ) (hc : 0 < c) (hφ : ∀ x, c ≤ φ x) :
    ((μ Set.univ).toReal⁻¹ * ∫ x, φ x ∂μ)⁻¹ ≤ c⁻¹ := by
  have hμ0 : 0 < (μ Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_pos.mpr hμ).ne' (measure_ne_top _ _)
  by_cases hint : Integrable φ μ
  · have hlow : c * (μ Set.univ).toReal ≤ ∫ x, φ x ∂μ := by
      calc c * (μ Set.univ).toReal = ∫ _x, c ∂μ := by
            rw [integral_const, smul_eq_mul, Measure.real_def, mul_comm]
        _ ≤ _ := integral_mono (integrable_const _) hint hφ
    have hxi : c ≤ (μ Set.univ).toReal⁻¹ * ∫ x, φ x ∂μ := by
      rw [le_inv_mul_iff₀ hμ0]
      linarith [hlow]
    exact inv_anti₀ hc hxi
  · rw [integral_undef hint, mul_zero, inv_zero]
    exact inv_nonneg.2 hc.le

end ModularCharacter

/-! ### van Dantzig's theorem and uniform local constancy -/

section VanDantzig

variable {G₀ : Type*} [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀]

/-- For a compact open `W`, some neighbourhood `T` of `1` satisfies `W T ⊆ W` (as in Mathlib's
`IsTopologicalGroup.exist_mul_closure_nhds`, which assumes `G` compact). -/
theorem exists_nhds_one_mul_subset {W : Set G₀} (hWc : IsCompact W) (hWo : IsOpen W) :
    ∃ T ∈ 𝓝 (1 : G₀), W * T ⊆ W := by
  apply hWc.induction_on (p := fun S ↦ ∃ T ∈ 𝓝 (1 : G₀), S * T ⊆ W)
    ⟨Set.univ, by simp only [Filter.univ_mem, Set.empty_mul, Set.empty_subset, and_self]⟩
    (fun _ _ huv ⟨T, hT, mem⟩ ↦ ⟨T, hT, (Set.mul_subset_mul_right huv).trans mem⟩)
    fun U V ⟨T₁, hT₁, mem1⟩ ⟨T₂, hT₂, mem2⟩ ↦ ⟨T₁ ∩ T₂, Filter.inter_mem hT₁ hT₂, by
      rw [Set.union_mul]
      exact Set.union_subset (Set.mul_subset_mul_left Set.inter_subset_left |>.trans mem1)
        (Set.mul_subset_mul_left Set.inter_subset_right |>.trans mem2)⟩
  intro x memW
  have : (x, 1) ∈ (fun p ↦ p.1 * p.2) ⁻¹' W := by simp [memW]
  rcases isOpen_prod_iff.mp (continuous_mul.isOpen_preimage W hWo) x 1 this with
    ⟨U, V, Uopen, Vopen, xmemU, onememV, prodsub⟩
  have h6 : U * V ⊆ W := Set.mul_subset_iff.mpr (fun _ hx _ hy ↦ prodsub (Set.mk_mem_prod hx hy))
  exact ⟨U ∩ W, ⟨U, Uopen.mem_nhds xmemU, W, fun _ a ↦ a, rfl⟩,
    V, IsOpen.mem_nhds Vopen onememV, fun _ a ↦ h6 ((Set.mul_subset_mul_right Set.inter_subset_left) a)⟩

/-- **van Dantzig's theorem**: in a totally disconnected locally compact Hausdorff group, every
neighbourhood of `1` contains a compact open subgroup. -/
theorem exists_compactOpenSubgroup_subset [T2Space G₀] [LocallyCompactSpace G₀]
    [TotallyDisconnectedSpace G₀] {U : Set G₀} (hU : IsOpen U) (h1 : (1 : G₀) ∈ U) :
    ∃ K : Subgroup G₀, IsOpen (K : Set G₀) ∧ IsCompact (K : Set G₀) ∧ (K : Set G₀) ⊆ U := by
  obtain ⟨W, hWc, hWcl, h1W, hWU⟩ :=
    exists_isCompact_isClopen_between isCompact_singleton hU (Set.singleton_subset_iff.2 h1)
  have h1W : (1 : G₀) ∈ W := h1W rfl
  obtain ⟨T, hT, hWT⟩ := exists_nhds_one_mul_subset hWc hWcl.isOpen
  obtain ⟨O, hOT, hOo, h1O⟩ := mem_nhds_iff.mp hT
  set V : Set G₀ := O ∩ O⁻¹
  have hVo : IsOpen V := hOo.inter hOo.inv
  have hV1 : (1 : G₀) ∈ V := ⟨h1O, by simpa using h1O⟩
  have hVinv : ∀ x ∈ V, x⁻¹ ∈ V := fun x hx => ⟨hx.2, by simpa using hx.1⟩
  have hWV : ∀ w ∈ W, ∀ x ∈ V, w * x ∈ W :=
    fun w hw x hx => hWT (Set.mul_mem_mul hw (hOT hx.1))
  -- the subgroup generated by `V` stays in `W`
  let P : G₀ → Prop := fun x => ∀ w ∈ W, w * x ∈ W
  have hP : ∀ x ∈ Subgroup.closure V, P x := by
    intro x hx
    induction hx using Subgroup.closure_induction'' with
    | mem x hx => exact fun w hw => hWV w hw x hx
    | inv_mem x hx => exact fun w hw => hWV w hw x⁻¹ (hVinv x hx)
    | one => exact fun w hw => by simpa using hw
    | mul x y _ _ hx hy => exact fun w hw => by simpa [mul_assoc] using hy _ (hx w hw)
  set K := Subgroup.closure V
  have hKW : (K : Set G₀) ⊆ W := fun x hx => by simpa using hP x hx 1 h1W
  have hKo : IsOpen (K : Set G₀) :=
    Subgroup.isOpen_of_mem_nhds K (Filter.mem_of_superset (hVo.mem_nhds hV1) Subgroup.subset_closure)
  exact ⟨K, hKo, hWc.of_isClosed_subset (Subgroup.isClosed_of_isOpen K hKo) hKW, hKW.trans hWU⟩

/-- **Uniform local constancy**: a locally constant function on a totally disconnected locally
compact Hausdorff group is, on a compact set `C`, invariant under left and right translation by
some compact open subgroup. -/
theorem exists_subgroup_biInvariant_on [T2Space G₀] [LocallyCompactSpace G₀]
    [TotallyDisconnectedSpace G₀] {β : Type*} (f : G₀ → β) (hf : IsLocallyConstant f)
    (C : Set G₀) (hC : IsCompact C) :
    ∃ K : Subgroup G₀, IsOpen (K : Set G₀) ∧ IsCompact (K : Set G₀) ∧
      ∀ c ∈ C, ∀ k ∈ K, ∀ k' ∈ K, f (k * c * k') = f c := by
  have hU : ∃ U ∈ 𝓝 (1 : G₀), ∀ c ∈ C, ∀ k ∈ U, ∀ k' ∈ U, f (k * c * k') = f c := by
    apply hC.induction_on (p := fun S ↦ ∃ U ∈ 𝓝 (1 : G₀), ∀ c ∈ S, ∀ k ∈ U, ∀ k' ∈ U,
      f (k * c * k') = f c)
    · exact ⟨Set.univ, Filter.univ_mem, by simp⟩
    · exact fun _ _ hst ⟨U, hU, h⟩ => ⟨U, hU, fun c hc => h c (hst hc)⟩
    · exact fun _ _ ⟨U₁, hU₁, h₁⟩ ⟨U₂, hU₂, h₂⟩ => ⟨U₁ ∩ U₂, Filter.inter_mem hU₁ hU₂,
        fun c hc k hk k' hk' => hc.elim (fun hc => h₁ c hc k hk.1 k' hk'.1)
          (fun hc => h₂ c hc k hk.2 k' hk'.2)⟩
    intro x _
    have hO : f ⁻¹' {f x} ∈ 𝓝 x := (hf.isOpen_fiber (f x)).mem_nhds rfl
    have hcont : Continuous fun p : G₀ × G₀ × G₀ => p.1 * p.2.1 * p.2.2 := by fun_prop
    have hpre : (fun p : G₀ × G₀ × G₀ => p.1 * p.2.1 * p.2.2) ⁻¹' (f ⁻¹' {f x}) ∈
        𝓝 ((1 : G₀), x, (1 : G₀)) :=
      hcont.continuousAt.preimage_mem_nhds (by simpa using hO)
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hpre
    obtain ⟨v₁, hv₁, v₂, hv₂, hv₁₂⟩ := mem_nhds_prod_iff.mp hv
    refine ⟨v₁, mem_nhdsWithin_of_mem_nhds hv₁, u ∩ v₂, Filter.inter_mem hu hv₂, ?_⟩
    intro c hc k hk k' hk'
    have e1 : f (k * c * k') = f x := huv (Set.mk_mem_prod hk.1 (hv₁₂ (Set.mk_mem_prod hc hk'.2)))
    have e2 : f ((1 : G₀) * c * 1) = f x :=
      huv (Set.mk_mem_prod (mem_of_mem_nhds hu) (hv₁₂ (Set.mk_mem_prod hc (mem_of_mem_nhds hv₂))))
    rw [e1, ← e2, one_mul, mul_one]
  obtain ⟨U, hU1, hUf⟩ := hU
  obtain ⟨O, hOU, hOo, h1O⟩ := mem_nhds_iff.mp hU1
  obtain ⟨K, hKo, hKc, hKO⟩ := exists_compactOpenSubgroup_subset hOo h1O
  exact ⟨K, hKo, hKc, fun c hc k hk k' hk' => hUf c hc k (hOU (hKO hk)) k' (hOU (hKO hk'))⟩

end VanDantzig

namespace GGPData

variable (d : GGPData F)

/-! ## 1. Log-norms modulo subgroups (BP §1.2) -/

/-- The log-norm `σ_G` of `G(F)` (BP §1.2, Thesis §2.2): `LocalGroups.logNorm`, built from the
operator norm of left multiplication on `C(W) × C(V)`. -/
def logNormG (g : ↥d.G) : ℝ := logNorm F d.G g

/-- The log-norm modulo a subgroup `S` (BP §1.2, Thesis §2.2): `σ_{S\G}(g) = inf_{a ∈ S} σ_G(a g)`. -/
def logNormModSub (S : Subgroup ↥d.G) (g : ↥d.G) : ℝ :=
  ⨅ a : S, d.logNormG ((a : ↥d.G) * g)

/-- `σ(g) = σ_{A_{G,H}\G}(g) = inf_{a ∈ A_{G,H}(F)} σ_G(a g)` (Thesis §8.1–8.2
"norms modulo `A_{G,H}`"). -/
def logNormMod (g : ↥d.G) : ℝ := d.logNormModSub d.AGH g

/-- `σ_{A_G\G}(g) = inf_{a ∈ A_G(F)} σ_G(a g)`: the log-norm in the definition of
`𝒞(A_G(F)\G(F), χ⁻¹)` (Thesis §2.3). -/
def logNormModAG (g : ↥d.G) : ℝ := d.logNormModSub d.AG g

theorem one_le_logNormG (g : ↥d.G) : 1 ≤ d.logNormG g := one_le_logNorm _ g

/-- `σ_G` is continuous. -/
theorem continuous_logNormG : Continuous d.logNormG := by
  have hv : Continuous fun g : ↥d.G => ((g : d.ambientˣ) : d.ambient) :=
    Units.continuous_val.comp continuous_subtype_val
  have h1 : Continuous fun g : ↥d.G => ‖lmulPi F ((g : d.ambientˣ) : d.ambient)‖ :=
    ((continuous_lmulPi F).comp hv).norm
  have h2 : Continuous fun g : ↥d.G => ‖lmulPi F (((g⁻¹ : ↥d.G) : d.ambientˣ) : d.ambient)‖ :=
    ((continuous_lmulPi F).comp (hv.comp continuous_inv)).norm
  have h3 : Continuous fun g : ↥d.G => maxNorm F d.G g := continuous_const.max (h1.max h2)
  exact continuous_const.add
    (h3.log fun g => (zero_lt_one.trans_le (one_le_maxNorm (F := F) d.G g)).ne')

theorem one_le_logNormModSub (S : Subgroup ↥d.G) (g : ↥d.G) : 1 ≤ d.logNormModSub S g :=
  le_ciInf fun _ => d.one_le_logNormG _

/-- `σ_{S\G}(a g) ≤ σ_G(g)` for `a ∈ S`. -/
theorem logNormModSub_mul_le (S : Subgroup ↥d.G) (a : ↥d.G) (ha : a ∈ S) (g : ↥d.G) :
    d.logNormModSub S (a * g) ≤ d.logNormG g := by
  have hb : BddBelow (Set.range fun b : S => d.logNormG ((b : ↥d.G) * (a * g))) :=
    ⟨1, by rintro _ ⟨b, rfl⟩; exact d.one_le_logNormG _⟩
  have := ciInf_le hb ⟨a⁻¹, S.inv_mem ha⟩
  simpa [logNormModSub] using this

/-- The class of `g ∈ G(F)` in `H(F)\G(F)/A_G(F)`. -/
def mkHG (g : ↥d.G) : d.HGQuot := CosetSpace.mk d.toGmodAG (QuotientGroup.mk g)

/-- A representative in `G(F)` of a class of `H(F)\G(F)/A_G(F)` (the one used in `distribJ`). -/
def repHG (q : d.HGQuot) : ↥d.G := Quotient.out (CosetSpace.out d.toGmodAG q : d.GmodAG)

/-- The log-norm on `H(F)\G(F)/A_G(F)` (BP §1.2; Thesis §8.4, §10.1, where it is written
`σ_{H\G}`): the infimum of `σ_G` over all representatives `h x a` (`h ∈ H(F)`, `a ∈ A_G(F)`).

It is `A_G(F)`-invariant by construction.  This is the reading under which Thesis Thm 10.1.1(ii)
is meaningful: with the log-norm of `H(F)\G(F)` itself, `σ_{H\G}(xa) → ∞` along
`A_G(F)/A_{G,H}(F)` while `K(f, xa) = K(f, x)` and `Ξ^{H\G}(xa) = Ξ^{H\G}(x)`, so the bound of
Thm 10.1.1(ii) would force `K(f,·) = 0`. -/
def logNormHG (q : d.HGQuot) : ℝ :=
  ⨅ g : {g : ↥d.G // d.mkHG g = q}, d.logNormG g

/-- `Ξ^{H\G}_C(x) = vol_{H\G}(xC)^{-1/2}` (Thesis §8.4), for a compact
`C ⊆ G(F)` with nonempty interior, the volume being taken for the Weil measure on
`H(F)\G(F)/A_G(F)` (`weilMeasureHG`).  The set `xC` is the image of `x̃ C` for a representative
`x̃`; it does not depend on the representative because `A_G(F)` is central.  Taking the volume in
`H\G/A_G` rather than in `H\G` changes `Ξ^{H\G}_C` only up to equivalence (the fibres of
`H\G → H\G/A_G` meet `xC` in sets of bounded, and for `C` with interior bounded-below, size),
and the thesis uses `Ξ^{H\G}` only up to equivalence. -/
def xiHG (C : Set ↥d.G) (q : d.HGQuot) : ℝ :=
  ((d.weilMeasureHG ((fun c => d.mkHG (d.repHG q * c)) '' C)).toReal) ^ (-(1 / 2 : ℝ))

/-! ## 2. Iwasawa data and Harish-Chandra's `Ξ` (BP §1.5) -/

/-- An Iwasawa datum (BP §1.5, Thesis §2.3): full isotropic flags `F_W`, `F_V` (so that
`P₀ = whittB F_W F_V` is a minimal parabolic subgroup), a compact open subgroup `K` of `G(F)`, and
the Iwasawa decomposition `G(F) = P₀(F) K`.  Its existence (with `K` a special maximal compact
subgroup) is Bruhat–Tits; it is not needed in this file, so no axiom is added.  Harish-Chandra's
`Ξ^G` built from different data are equivalent functions (they are matrix coefficients of
positive `K`-fixed vectors of `i_{P₀}^G 1`).  The field `AG_le_P0` is automatic and recorded only
for convenience (see its docstring). -/
structure IwasawaDatum where
  /-- full isotropic flag in `W` -/
  FW : IsotropicFlag d.QW
  /-- full isotropic flag in `V` -/
  FV : IsotropicFlag d.QV
  fullW : FW.IsFull
  fullV : FV.IsFull
  /-- the compact open subgroup -/
  K : Subgroup ↥d.G
  isOpen_K : IsOpen (K : Set ↥d.G)
  isCompact_K : IsCompact (K : Set ↥d.G)
  /-- the Iwasawa decomposition `G = P₀ K` -/
  mul_eq : ∀ g : ↥d.G, ∃ p ∈ d.whittB FW FV, ∃ k ∈ K, g = p * k
  /-- `A_G ⊆ P₀`.  Automatic (the centre of `G` lies in every parabolic subgroup); recorded as a
  field only to avoid the computation of `SO(1,1)` on a hyperbolic-plane factor, where `A_G`
  acts on `W` or `V` nontrivially but preserves both isotropic lines. -/
  AG_le_P0 : d.AG ≤ d.whittB FW FV

namespace IwasawaDatum

variable {d} (IW : d.IwasawaDatum)

/-- The minimal parabolic subgroup `P₀ = whittB F_W F_V`. -/
abbrev P0 : Subgroup ↥d.G := d.whittB IW.FW IW.FV

instance locallyCompactSpace_P0 : LocallyCompactSpace ↥IW.P0 :=
  (d.isClosed_whittB IW.FW IW.FV).locallyCompactSpace

instance compactSpace_K : CompactSpace ↥IW.K :=
  isCompact_iff_compactSpace.mp IW.isCompact_K

/-- The modular character `δ_{P₀}` of `P₀(F)` (BP §1.5): Mathlib's `modularCharacter`,
`μ(E p⁻¹) = δ(p) μ(E)` for a left Haar measure `μ`.  For `P₀ = M₀ U₀` this is
`|det Ad(p)|_{𝔲₀}|` (e.g. for `F^× ⋉ F`, `δ(a) = |a|`), the normalization in
`Ξ(g) = ∫_K δ_{P₀}(p(kg))^{1/2} dk`. -/
def deltaP0 (p : ↥IW.P0) : ℝ := (Measure.modularCharacter p : ℝ)

/-- A choice of `P₀`-component of `g = p k` (Iwasawa decomposition).  `δ_{P₀}` of it does not
depend on the choice, since `δ_{P₀}` is trivial on the compact open subgroup `P₀ ∩ K` of `P₀`. -/
def iwasawaP (g : ↥d.G) : ↥IW.P0 :=
  ⟨(IW.mul_eq g).choose, (IW.mul_eq g).choose_spec.1⟩

/-- **Harish-Chandra's function** `Ξ^G(g) = ∫_K δ_{P₀}(p(kg))^{1/2} dk` (BP §1.5, Thesis §2.3),
`dk` the probability Haar measure on `K`: the matrix coefficient of the spherical vector of
`i_{P₀}^G 1`. -/
def xiHC (g : ↥d.G) : ℝ :=
  ((Measure.haar : Measure ↥IW.K) Set.univ).toReal⁻¹ *
    ∫ k : ↥IW.K, Real.sqrt (IW.deltaP0 (IW.iwasawaP ((k : ↥d.G) * g))) ∂Measure.haar

end IwasawaDatum

/-! ### Properties of `δ_{P₀}` and a lower bound for `Ξ` -/

namespace IwasawaDatum

variable {d} (IW : d.IwasawaDatum)

/-- `P₀(F) ∩ K`, as a subgroup of `P₀(F)`. -/
abbrev KP0 : Subgroup ↥IW.P0 := IW.K.subgroupOf IW.P0

theorem isOpen_KP0 : IsOpen (IW.KP0 : Set ↥IW.P0) :=
  IW.isOpen_K.preimage continuous_subtype_val

theorem isCompact_KP0 : IsCompact (IW.KP0 : Set ↥IW.P0) :=
  (d.isClosed_whittB IW.FW IW.FV).isClosedEmbedding_subtypeVal.isCompact_preimage IW.isCompact_K

theorem deltaP0_pos (p : ↥IW.P0) : 0 < IW.deltaP0 p := by
  unfold deltaP0
  exact_mod_cast Measure.modularCharacterFun_pos p

theorem deltaP0_mul (p q : ↥IW.P0) : IW.deltaP0 (p * q) = IW.deltaP0 p * IW.deltaP0 q := by
  unfold deltaP0
  rw [map_mul, NNReal.coe_mul]

/-- `δ_{P₀}` is trivial on the compact open subgroup `P₀ ∩ K`. -/
theorem deltaP0_eq_one_of_mem_KP0 (k : ↥IW.P0) (hk : k ∈ IW.KP0) : IW.deltaP0 k = 1 := by
  unfold deltaP0
  rw [modularCharacter_eq_one_of_mem IW.KP0 IW.isOpen_KP0 IW.isCompact_KP0 k hk, NNReal.coe_one]

/-- `δ_{P₀}` is trivial on central elements of `P₀`. -/
theorem deltaP0_eq_one_of_central (a : ↥IW.P0) (ha : ∀ y : ↥IW.P0, y * a = a * y) :
    IW.deltaP0 a = 1 := by
  unfold deltaP0
  rw [modularCharacter_eq_one_of_central a ha, NNReal.coe_one]

/-- On a compact subset of `P₀(F)`, `δ_{P₀}` is bounded below by a positive constant. -/
theorem exists_lowerBound_deltaP0 (S : Set ↥IW.P0) (hS : IsCompact S) :
    ∃ m : ℝ, 0 < m ∧ ∀ p ∈ S, m ≤ IW.deltaP0 p :=
  exists_lowerBound_modularCharacter IW.KP0 IW.isOpen_KP0 IW.isCompact_KP0 S hS

theorem xiHC_nonneg (g : ↥d.G) : 0 ≤ IW.xiHC g :=
  mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
    (integral_nonneg fun _ => Real.sqrt_nonneg _)

/-- `Ξ^G` is bounded below on `A_G(F) C` for compact `C` (or vanishes there, which in Lean only
happens if its defining integrand were not integrable): `Ξ(g)⁻¹` is bounded on `A_G(F) C`. -/
theorem exists_xiHC_inv_le (C : Set ↥d.G) (hC : IsCompact C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ (d.AG : Set ↥d.G) * C, (IW.xiHC g)⁻¹ ≤ B := by
  let S : Set ↥IW.P0 :=
    Subtype.val ⁻¹' ((IW.K : Set ↥d.G) * C * (IW.K : Set ↥d.G))
  have hS : IsCompact S :=
    (d.isClosed_whittB IW.FW IW.FV).isClosedEmbedding_subtypeVal.isCompact_preimage
      ((IW.isCompact_K.mul hC).mul IW.isCompact_K)
  obtain ⟨m, hm, hmS⟩ := IW.exists_lowerBound_deltaP0 S hS
  refine ⟨(Real.sqrt m)⁻¹, inv_nonneg.2 (Real.sqrt_nonneg _), ?_⟩
  intro g hg
  obtain ⟨a, ha, c, hc, hg⟩ := Set.mem_mul.mp hg
  subst hg
  have hcent : ∀ y : ↥d.G, y * a = a * y :=
    fun y => Subgroup.mem_center_iff.mp (d.AG_le_center ha) y
  have alg : ∀ {G₀ : Type _} [Group G₀] (a c k p k1 : G₀), (∀ y, y * a = a * y) →
      k * (a * c) = p * k1 → a⁻¹ * p = k * c * k1⁻¹ := by
    intro G₀ _ a c k p k1 hca h
    have hp : p = k * (a * c) * k1⁻¹ := by rw [h]; group
    rw [hp, ← mul_assoc k a c, hca k]
    group
  -- pointwise lower bound for the integrand
  have hpt : ∀ k : ↥IW.K, Real.sqrt m ≤
      Real.sqrt (IW.deltaP0 (IW.iwasawaP ((k : ↥d.G) * (a * c)))) := by
    intro k
    apply Real.sqrt_le_sqrt
    let a' : ↥IW.P0 := ⟨a, IW.AG_le_P0 ha⟩
    have hca' : ∀ y : ↥IW.P0, y * a' = a' * y := fun y => Subtype.ext (hcent y)
    have hp : IW.iwasawaP ((k : ↥d.G) * (a * c)) =
        a' * (a'⁻¹ * IW.iwasawaP ((k : ↥d.G) * (a * c))) := by group
    rw [hp, deltaP0_mul, IW.deltaP0_eq_one_of_central a' hca', one_mul]
    apply hmS
    obtain ⟨k1, hk1, hkp⟩ := (IW.mul_eq ((k : ↥d.G) * (a * c))).choose_spec.2
    have hval : ((a'⁻¹ * IW.iwasawaP ((k : ↥d.G) * (a * c)) : ↥IW.P0) : ↥d.G) =
        a⁻¹ * (IW.mul_eq ((k : ↥d.G) * (a * c))).choose := rfl
    change ((a'⁻¹ * IW.iwasawaP ((k : ↥d.G) * (a * c)) : ↥IW.P0) : ↥d.G) ∈
      (IW.K : Set ↥d.G) * C * (IW.K : Set ↥d.G)
    rw [hval, alg a c (k : ↥d.G) _ k1 hcent hkp]
    exact ⟨(k : ↥d.G) * c, ⟨k, k.2, c, hc, rfl⟩, k1⁻¹, IW.K.inv_mem hk1, rfl⟩
  exact inv_mul_integral_inv_le (Measure.haar : Measure ↥IW.K) (NeZero.ne _) _ _
    (Real.sqrt_pos.2 hm) hpt

end IwasawaDatum

/-! ## 3. Harish-Chandra Schwartz spaces (Thesis §2.3) -/

variable (χ : CentralCharOn d)

/-- `f` is bi-invariant under the subgroup `K'`. -/
def IsBiInvariant (K' : Subgroup ↥d.G) (f : ↥d.G → ℂ) : Prop :=
  ∀ k ∈ K', ∀ k' ∈ K', ∀ g : ↥d.G, f (k * g * k') = f g

/-- The seminorm `sup_g |f(g)| Ξ^G(g)⁻¹ σ_{A_G\G}(g)^n` defining `𝒞(A_G(F)\G(F), χ⁻¹)` (`p`-adic
case). -/
def schwartzSeminorm (IW : d.IwasawaDatum) (n : ℕ) (f : ↥d.G → ℂ) : ℝ :=
  ⨆ g : ↥d.G, ‖f g‖ * (IW.xiHC g)⁻¹ * d.logNormModAG g ^ n

/-- **`𝒞(A_G(F)\G(F), χ⁻¹)`** (Thesis Ch. 1 and §2.3; BP §1.5 for the untwisted
space), `p`-adic case: functions `f` that are bi-invariant under some compact open subgroup,
satisfy `f(ag) = χ(a)⁻¹ f(g)` for `a ∈ A_G(F)`, and have all seminorms
`sup |f| Ξ⁻¹ σ_{A_G\G}^n` finite.  (Its LF topology is the inductive limit over `K'` of the
Fréchet spaces cut out by these seminorms.) -/
def HCSchwartzChi (IW : d.IwasawaDatum) : Set (↥d.G → ℂ) :=
  {f | (∃ K' : Subgroup ↥d.G, IsOpen (K' : Set ↥d.G) ∧ IsCompact (K' : Set ↥d.G) ∧
      d.IsBiInvariant K' f) ∧ IsChiEquivariant d χ f ∧
    ∀ n : ℕ, BddAbove (Set.range fun g : ↥d.G => ‖f g‖ * (IW.xiHC g)⁻¹ * d.logNormModAG g ^ n)}

/-- **`𝒞_scusp(A_G(F)\G(F), χ⁻¹)`** (Thesis §4.5): the strongly cuspidal
functions in `HCSchwartzChi`. -/
def ScuspSchwartz (IW : d.IwasawaDatum) : Set (↥d.G → ℂ) :=
  {f | f ∈ d.HCSchwartzChi χ IW ∧ IsStronglyCuspidal d f}

/-! ## 4a. Continuity of `ξ` -/

/-- `GSpin(W) → GSpin(V)` is continuous (it is induced by the linear map `C(W) → C(V)`). -/
theorem continuous_incl : Continuous d.incl := by
  have hmap : Continuous (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)) :=
    IsModuleTopology.continuous_of_linearMap
      (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)).toLinearMap
  apply continuous_induced_rng.2
  rw [Units.continuous_iff]
  constructor
  · exact hmap.comp (Units.continuous_val.comp continuous_subtype_val)
  · have e : ∀ a : GSpin d.QW, ((((d.incl a : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ))⁻¹ :
        (CliffordAlgebra d.QV)ˣ) = (((d.incl a⁻¹ : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ)) := by
      intro a
      rw [map_inv]
      rfl
    have e2 : ∀ a : GSpin d.QW, (((d.incl a⁻¹ : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) :
        CliffordAlgebra d.QV) = CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
          ((((a : (CliffordAlgebra d.QW)ˣ))⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) :=
      fun a => rfl
    have : (fun a : GSpin d.QW => ((((Subtype.val ∘ d.incl) a)⁻¹ : (CliffordAlgebra d.QV)ˣ) :
        CliffordAlgebra d.QV)) = fun a : GSpin d.QW =>
          CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
          ((((a : (CliffordAlgebra d.QW)ˣ))⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) := by
      funext a
      simp only [Function.comp_apply]
      rw [e a, e2 a]
    rw [this]
    refine hmap.comp ?_
    exact Units.continuous_coe_inv.comp continuous_subtype_val

/-- `g ↦ n(g) = g_W⁻¹ g_V` is continuous on `G(F)`. -/
theorem continuous_nPart : Continuous d.nPart := by
  unfold nPart
  exact ((d.continuous_incl.comp d.continuous_fst).inv).mul d.continuous_snd

/-- `g ↦ P(n(g)) v` is continuous on `G(F)`. -/
theorem continuous_specP_nPart (v : d.V) :
    Continuous fun g : ↥d.G => specP d.QV (d.nPart g) v := by
  have hn : Continuous fun g : ↥d.G => ((d.nPart g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) :=
    continuous_subtype_val.comp d.continuous_nPart
  simp only [specP_apply_eq]
  exact (IsModuleTopology.continuous_of_linearMap (ιInv d.QV)).comp
    ((Units.continuous_val.comp hn).mul (continuous_const.mul (Units.continuous_coe_inv.comp hn)))

/-- `λ : H(F) → F` is continuous (Thesis §5.2). -/
theorem continuous_lam : Continuous d.lam := by
  unfold lam
  refine continuous_finsetSum _ fun i _ => ?_
  exact (IsModuleTopology.continuous_of_linearMap (bform d.QV (d.zV (-(i : ℤ) - 1)))).comp
    ((d.continuous_specP_nPart _).comp continuous_subtype_val)

/-- `ξ = ψ ∘ λ` is continuous on `H(F)` (Thesis §5.2). -/
theorem continuous_xi (ψ : NontrivialAddChar F) : Continuous (d.xi ψ.toAddChar) := by
  unfold xi
  exact continuous_subtype_val.comp (ψ.continuous.comp d.continuous_lam)

/-! ## 4. The kernel `K(f,x)` and the distribution `J(f)` (Thesis §7.1, §10.1) -/

variable (ψ : NontrivialAddChar F)

/-- **The integral defining `K(f,x)` converges** for `f ∈ ScuspTestFn d χ` (Thesis §10.1;
for Schwartz `f` this is Lemma 8.2.1(ii), here it is elementary): the integrand
`h ↦ f(x⁻¹hx) ξ(h)` on `H(F)/A_{G,H}(F)` is continuous and supported in the image of
`H(F) ∩ x A_G(F) C x⁻¹`, which is compact modulo `A_{G,H}(F)` because
`H(F)/A_{G,H}(F) → G(F)/A_G(F)` is a closed embedding (`isClosedEmbedding_toGmodAG`). -/
theorem kernelK_integrable (f : ↥d.G → ℂ) (hf : f ∈ ScuspTestFn d χ) (x : ↥d.G) :
    Integrable (fun q : d.HmodAGH => kernelIntegrand d ψ f x (Quotient.out q)) Measure.haar := by
  obtain ⟨hlc, hchi, ⟨C, hC, hsupp⟩, -⟩ := hf
  -- the integrand on `H(F)` is continuous
  let φ : ↥d.H → ℂ := fun h => kernelIntegrand d ψ f x h
  have hφ : Continuous φ :=
    (hlc.continuous.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)).mul
      (d.continuous_xi ψ)
  -- it descends to `H(F)/A_{G,H}(F)`
  let φbar : d.HmodAGH → ℂ :=
    Quotient.lift φ (fun a b hab => kernelIntegrand_eq_of_mk_eq d χ ψ f hchi x (Quotient.sound hab))
  have hcont : Continuous φbar := continuous_quot_lift _ hφ
  have heq : (fun q : d.HmodAGH => kernelIntegrand d ψ f x (Quotient.out q)) = φbar := by
    funext q
    conv_rhs => rw [← Quotient.out_eq q]
    rfl
  -- its support lies in the preimage of the compact set `x C x⁻¹ A_G / A_G`
  let Kc : Set d.GmodAG := QuotientGroup.mk '' ((fun c => x * c * x⁻¹) '' C)
  have hKc : IsCompact Kc :=
    (hC.image ((continuous_const.mul continuous_id).mul continuous_const)).image
      QuotientGroup.continuous_mk
  have hS : IsCompact (d.toGmodAG ⁻¹' Kc) := d.isClosedEmbedding_toGmodAG.isCompact_preimage hKc
  have hzero : ∀ q ∉ d.toGmodAG ⁻¹' Kc, φbar q = 0 := by
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H h =>
      change f (x⁻¹ * (h : ↥d.G) * x) * d.xi ψ.toAddChar h = 0
      by_contra hne
      have hf0 : f (x⁻¹ * (h : ↥d.G) * x) ≠ 0 := left_ne_zero_of_mul hne
      obtain ⟨a, ha, c, hc, hac⟩ := Set.mem_mul.mp (hsupp hf0)
      apply hq
      refine ⟨x * c * x⁻¹, ⟨c, hc, rfl⟩, ?_⟩
      rw [toGmodAG_mk, QuotientGroup.eq]
      have hcent : ∀ y : ↥d.G, a * y = y * a :=
        fun y => (Subgroup.mem_center_iff.mp (d.AG_le_center ha) y).symm
      have key : ∀ {G₀ : Type _} [Group G₀] (a c x h : G₀), (∀ y, a * y = y * a) →
          a * c = x⁻¹ * h * x → (x * c * x⁻¹)⁻¹ * h = a := by
        intro G₀ _ a c x h hca hac
        have h' : h = a * (x * c * x⁻¹) := by
          have e1 : h = x * (a * c) * x⁻¹ := by rw [hac]; group
          rw [e1, ← mul_assoc x a c, ← hca x]
          group
        rw [h', ← mul_assoc, ← hca, mul_assoc, inv_mul_cancel, mul_one]
      rw [key a c x (h : ↥d.G) hcent hac]
      exact ha
  rw [heq]
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hS hzero)

theorem kernelIntegrand_add (f g : ↥d.G → ℂ) (x : ↥d.G) (h : ↥d.H) :
    kernelIntegrand d ψ (f + g) x h = kernelIntegrand d ψ f x h + kernelIntegrand d ψ g x h := by
  simp only [kernelIntegrand, Pi.add_apply, add_mul]

theorem kernelIntegrand_smul (c : ℂ) (f : ↥d.G → ℂ) (x : ↥d.G) (h : ↥d.H) :
    kernelIntegrand d ψ (c • f) x h = c * kernelIntegrand d ψ f x h := by
  simp only [kernelIntegrand, Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- `K(f + g, x) = K(f, x) + K(g, x)` for `f, g ∈ ScuspTestFn` (from `kernelK_integrable`). -/
theorem kernelK_add (f g : ↥d.G → ℂ) (hf : f ∈ ScuspTestFn d χ) (hg : g ∈ ScuspTestFn d χ)
    (x : ↥d.G) : kernelK d ψ (f + g) x = kernelK d ψ f x + kernelK d ψ g x := by
  unfold kernelK
  simp_rw [kernelIntegrand_add]
  exact integral_add (d.kernelK_integrable χ ψ f hf x) (d.kernelK_integrable χ ψ g hg x)

/-- `K(c f, x) = c K(f, x)` (no hypothesis: the Bochner integral is linear in the scalar). -/
theorem kernelK_smul (c : ℂ) (f : ↥d.G → ℂ) (x : ↥d.G) :
    kernelK d ψ (c • f) x = c * kernelK d ψ f x := by
  unfold kernelK
  simp_rw [kernelIntegrand_smul]
  exact integral_const_mul c _

/-- **`J(f)` converges** for `f ∈ ScuspTestFn d χ` (Thesis §10.1: Thm 10.1.1(ii)
(`kernelK_bound_scusp`) with BP Prop 6.7.1(iii) (Thesis Prop 8.4.1(iii)),
`∫_{H\G/A_G} Ξ^{H\G}(x)² σ_{H\G}(x)^{-d} dx < ∞` for `d` large; `ScuspTestFn` lies in
`ScuspSchwartz`).  Own work (adapted from BP Thm 8.1.1); not proved here. -/
theorem distribJ_convergent (f : ↥d.G → ℂ) (hf : f ∈ ScuspTestFn d χ) :
    Integrable (fun q : d.HGQuot => kernelK d ψ f (d.repHG q)) d.weilMeasureHG := by
  sorry

/-- `J` is additive on `ScuspTestFn d χ` (Thesis §10.1: `J` is a linear form). -/
theorem distribJ_add (f g : ↥d.G → ℂ) (hf : f ∈ ScuspTestFn d χ) (hg : g ∈ ScuspTestFn d χ) :
    distribJ d ψ (f + g) = distribJ d ψ f + distribJ d ψ g := by
  have e : ∀ q : d.HGQuot, kernelK d ψ (f + g) (d.repHG q) =
      kernelK d ψ f (d.repHG q) + kernelK d ψ g (d.repHG q) :=
    fun q => d.kernelK_add χ ψ f g hf hg _
  unfold distribJ
  change ∫ q, kernelK d ψ (f + g) (d.repHG q) ∂d.weilMeasureHG =
    ∫ q, kernelK d ψ f (d.repHG q) ∂d.weilMeasureHG +
      ∫ q, kernelK d ψ g (d.repHG q) ∂d.weilMeasureHG
  simp_rw [e]
  exact integral_add (d.distribJ_convergent χ ψ f hf) (d.distribJ_convergent χ ψ g hg)

/-- `J(c f) = c J(f)` (Thesis §10.1); no hypothesis needed. -/
theorem distribJ_smul (c : ℂ) (f : ↥d.G → ℂ) :
    distribJ d ψ (c • f) = c * distribJ d ψ f := by
  unfold distribJ
  simp_rw [kernelK_smul]
  exact integral_const_mul c _

/-! ## 5. The estimates of Thesis Ch. 8 and 10 (own work, adapted from BP Ch. 6, 8; stated, not proved) -/

/-- **Thesis Thm 10.1.1(i)** (adapted from BP Thm 8.1.1(i)): there is `d₀ > 0`
and a continuous seminorm `ν` on `𝒞(A_G(F)\G(F), χ⁻¹)` with
`|K(f,x)| ≤ ν(f) Ξ^{H\G}(x)² σ_{H\G}(x)^{d₀}`.

Formalization of "continuous seminorm on the LF space `𝒞 = lim_{K'} 𝒞_{K'}`": a seminorm is
continuous iff its restriction to each Fréchet step `𝒞_{K'}` (bi-`K'`-invariant functions) is
bounded by `C · schwartzSeminorm n` for some `C`, `n` (the seminorms increase with `n` since
`σ ≥ 1`).  Hence: `∃ d₀, ∀ K', ∃ C n, …`.  `C₀` is the compact set defining `Ξ^{H\G}`; any
compact set with nonempty interior gives an equivalent function (Thesis §8.4). -/
theorem kernelK_bound (IW : d.IwasawaDatum) (C₀ : Set ↥d.G) (hC₀ : IsCompact C₀)
    (hC₀' : (interior C₀).Nonempty) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ K' : Subgroup ↥d.G, IsOpen (K' : Set ↥d.G) → IsCompact (K' : Set ↥d.G) →
      ∃ (C : ℝ) (n : ℕ), ∀ f ∈ d.HCSchwartzChi χ IW, d.IsBiInvariant K' f → ∀ x : ↥d.G,
        ‖kernelK d ψ f x‖ ≤
          C * d.schwartzSeminorm IW n f * d.xiHG C₀ (d.mkHG x) ^ 2 * d.logNormHG (d.mkHG x) ^ d₀ := by
  sorry

/-- **Thesis Thm 10.1.1(ii)** (adapted from BP Thm 8.1.1(ii)): for every
`d₀ > 0` there is a continuous seminorm `ν_{d₀}` on `𝒞(A_G(F)\G(F), χ⁻¹)` with
`|K(f,x)| ≤ ν_{d₀}(f) Ξ^{H\G}(x)² σ_{H\G}(x)^{-d₀}` for strongly cuspidal `f`.
Continuous seminorms are encoded as in `kernelK_bound`.  `σ_{H\G}` is the log-norm of
`H(F)\G(F)/A_G(F)` (`logNormHG`). -/
theorem kernelK_bound_scusp (IW : d.IwasawaDatum) (C₀ : Set ↥d.G) (hC₀ : IsCompact C₀)
    (hC₀' : (interior C₀).Nonempty) (d₀ : ℝ) (hd₀ : 0 < d₀) (K' : Subgroup ↥d.G)
    (hK'o : IsOpen (K' : Set ↥d.G)) (hK'c : IsCompact (K' : Set ↥d.G)) :
    ∃ (C : ℝ) (n : ℕ), ∀ f ∈ d.ScuspSchwartz χ IW, d.IsBiInvariant K' f → ∀ x : ↥d.G,
      ‖kernelK d ψ f x‖ ≤
        C * d.schwartzSeminorm IW n f * d.xiHG C₀ (d.mkHG x) ^ 2 *
          d.logNormHG (d.mkHG x) ^ (-d₀) := by
  sorry

/-- **Thesis Lemma 8.2.1(i)** (adapted from BP Lemma 6.5.1(i) and
Waldspurger 2012 Lemma 4.9): there is `ε > 0` with
`∫_{H₀(F)/A_{G,H}(F)} Ξ^{G₀}(h₀) e^{ε σ(h₀)} dh₀ < ∞`.

Here `G₀ = GSpin(W) × GSpin(V₀)`, `H₀ = GSpin(W)`: these are `G`, `H` for a datum with `r = 0`,
so the lemma is stated for `d` with `d.r = 0` (no loss of generality, `d` being arbitrary).
This differs from Thesis Lemma 8.2.1(i), which integrates over `H₀(F)/A_{H₀}(F)`: when `W` is a
hyperbolic plane, `A_{H₀} = H₀ = GSpin(W)` (a split torus) is strictly bigger than
`A_{G,H} = A_{G₀,H₀}` (the scalars), and the integrand is not `A_{H₀}(F)`-invariant; the quotient
here is by `A_{G,H}`, which is also what Lemma 8.2.1(ii) needs (`H/A_{G,H} = H₀/A_{G,H} × N`).
In all other cases `A_{H₀} = A_{G,H}`. -/
theorem lemma_6_5_1_i (hr : d.r = 0) (IW : d.IwasawaDatum) :
    ∃ ε : ℝ, 0 < ε ∧ Integrable (fun q : d.HmodAGH =>
      IW.xiHC (Quotient.out q : ↥d.H) * Real.exp (ε * d.logNormMod (Quotient.out q : ↥d.H)))
      Measure.haar := by
  sorry

/-- **Thesis Lemma 8.2.1(ii)** (adapted from BP Lemma 6.5.1(ii)):
there is `d₀ > 0` with `∫_{H(F)/A_{G,H}(F)} Ξ^G(h) σ(h)^{-d₀} dh < ∞`. -/
theorem lemma_6_5_1_ii (IW : d.IwasawaDatum) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ Integrable (fun q : d.HmodAGH =>
      IW.xiHC (Quotient.out q : ↥d.H) * d.logNormMod (Quotient.out q : ↥d.H) ^ (-d₀))
      Measure.haar := by
  sorry

/-- **Thesis Lemma 8.2.1(iii)** (adapted from BP Lemma 6.5.1(iii)):
for every `δ > 0` there is `ε > 0` with
`∫_{H(F)/A_{G,H}(F)} Ξ^G(h) e^{ε σ(h)} (1 + |λ(h)|)^{-δ} dh < ∞`.  (`|·|` is the norm of `F`;
the normalized absolute value is a fixed power of it, which only rescales `δ`.) -/
theorem lemma_6_5_1_iii (IW : d.IwasawaDatum) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ Integrable (fun q : d.HmodAGH =>
      IW.xiHC (Quotient.out q : ↥d.H) * Real.exp (ε * d.logNormMod (Quotient.out q : ↥d.H)) *
        (1 + ‖d.lam (Quotient.out q)‖) ^ (-δ)) Measure.haar := by
  sorry

/-- **Thesis Prop 8.1.1(i), existence part** (adapted from BP Prop 6.4.1):
there is a good minimal parabolic subgroup `P̄_min = M_min Ū_min`, i.e. full isotropic flags
whose stabilizer `P̄ = whittB F_W F_V` satisfies `H ∩ Ū_min = {1}`, `H(F) P̄(F)` open in `G(F)`
and of Haar-null complement.

"Good" (`H P̄` Zariski open) is not expressible without algebraic geometry; it is replaced by
its two consequences used in the estimates (openness and conullity of `H(F) P̄(F)`).  The clause
`A_{G,H} ⊆ A_{M_min}` is automatic (`A_{G,H}` is a split torus central in `G`,
hence in every Levi subgroup) and is omitted. -/
theorem exists_good_minimal_parabolic :
    ∃ (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV), FW.IsFull ∧ FV.IsFull ∧
      d.H ⊓ d.whittU FW FV = ⊥ ∧
      IsOpen ((d.H : Set ↥d.G) * (d.whittB FW FV : Set ↥d.G)) ∧
      (Measure.haar : Measure ↥d.G) ((d.H : Set ↥d.G) * (d.whittB FW FV : Set ↥d.G))ᶜ = 0 := by
  sorry

/-- **`C_c^∞` strongly cuspidal functions are Harish-Chandra Schwartz**:
`ScuspTestFn d χ ⊆ 𝒞_scusp(A_G(F)\G(F), χ⁻¹)`.  A locally constant function compactly supported
modulo the centre is bi-invariant under a compact open subgroup (van Dantzig plus uniform local
constancy on a compact set), and on its support `A_G C` the functions `|f|`, `Ξ⁻¹` and
`σ_{A_G\G}` are bounded (`|χ| = 1`; `Ξ` is positive, continuous and `A_G`-invariant;
`σ_{A_G\G}(a c) = σ_{A_G\G}(c) ≤ σ_G(c)`). -/
theorem scuspTestFn_subset_scuspSchwartz (IW : d.IwasawaDatum) :
    ScuspTestFn d χ ⊆ d.ScuspSchwartz χ IW := by
  intro f hf
  obtain ⟨hlc, hchi, ⟨C, hC, hsupp⟩, hcusp⟩ := hf
  have hcentral : ∀ a ∈ d.AG, ∀ y : ↥d.G, y * a = a * y :=
    fun a ha y => Subgroup.mem_center_iff.mp (d.AG_le_center ha) y
  have hnorm : ∀ a ∈ d.AG, ∀ c : ↥d.G, ‖f (a * c)‖ = ‖f c‖ := by
    intro a ha c
    rw [show a * c = ((⟨a, ha⟩ : ↥d.AG) : ↥d.G) * c from rfl, hchi, norm_mul]
    simp
  refine ⟨⟨?_, hchi, ?_⟩, hcusp⟩
  · -- bi-invariance under a compact open subgroup
    have := totallyDisconnectedSpace_subgroup F d.ambient d.G
    obtain ⟨K', hK'o, hK'c, hK'⟩ := exists_subgroup_biInvariant_on f hlc C hC
    refine ⟨K', hK'o, hK'c, ?_⟩
    have alg : ∀ {G₀ : Type _} [Group G₀] (a c k k' : G₀), (∀ y, y * a = a * y) →
        k * (a * c) * k' = a * (k * c * k') := by
      intro G₀ _ a c k k' hca
      rw [← mul_assoc k a c, hca k]
      group
    have hAC : ∀ g ∈ (d.AG : Set ↥d.G) * C, ∀ k ∈ K', ∀ k' ∈ K', f (k * g * k') = f g := by
      intro g hg k hk k' hk'
      obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_mul.mp hg
      rw [alg a c k k' (hcentral a ha),
        show a * (k * c * k') = ((⟨a, ha⟩ : ↥d.AG) : ↥d.G) * (k * c * k') from rfl, hchi,
        hK' c hc k hk k' hk', show a * c = ((⟨a, ha⟩ : ↥d.AG) : ↥d.G) * c from rfl, hchi]
    intro k hk k' hk' g
    by_cases hg : g ∈ (d.AG : Set ↥d.G) * C
    · exact hAC g hg k hk k' hk'
    · have h0 : f g = 0 := by
        by_contra h
        exact hg (hsupp h)
      rw [h0]
      by_contra hne
      have h1 := hAC _ (hsupp hne) k⁻¹ (K'.inv_mem hk) k'⁻¹ (K'.inv_mem hk')
      have e : k⁻¹ * (k * g * k') * k'⁻¹ = g := by group
      rw [e, h0] at h1
      exact hne h1.symm
  · -- the seminorms are finite
    intro n
    obtain ⟨B, hB0, hB⟩ := IW.exists_xiHC_inv_le C hC
    obtain ⟨M, hM⟩ := (hC.image_of_continuousOn hlc.continuous.norm.continuousOn).isBounded.subset_closedBall 0
    obtain ⟨L, hL⟩ := (hC.image_of_continuousOn d.continuous_logNormG.continuousOn).bddAbove
    have hM' : ∀ c ∈ C, ‖f c‖ ≤ M := fun c hc => by
      have := hM ⟨c, hc, rfl⟩
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using this
    have hL' : ∀ c ∈ C, d.logNormG c ≤ L := fun c hc => hL ⟨c, hc, rfl⟩
    refine ⟨max M 0 * B * max L 0 ^ n, ?_⟩
    rintro _ ⟨g, rfl⟩
    have hpos : 0 ≤ max M 0 * B * max L 0 ^ n :=
      mul_nonneg (mul_nonneg (le_max_right _ _) hB0) (pow_nonneg (le_max_right _ _) _)
    by_cases hg : g ∈ (d.AG : Set ↥d.G) * C
    · have hBg := hB g hg
      obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_mul.mp hg
      have hxi0 : 0 ≤ (IW.xiHC (a * c))⁻¹ := inv_nonneg.2 (IW.xiHC_nonneg _)
      have hσ : d.logNormModAG (a * c) ≤ max L 0 :=
        (d.logNormModSub_mul_le d.AG a ha c).trans ((hL' c hc).trans (le_max_left _ _))
      have hσ0 : 0 ≤ d.logNormModAG (a * c) :=
        zero_le_one.trans (d.one_le_logNormModSub d.AG _)
      have hf' : ‖f (a * c)‖ ≤ max M 0 := (hnorm a ha c).trans_le ((hM' c hc).trans (le_max_left _ _))
      exact mul_le_mul (mul_le_mul hf' hBg hxi0 (le_max_right _ _))
        (pow_le_pow_left₀ hσ0 hσ n) (pow_nonneg hσ0 n)
        (mul_nonneg (le_max_right _ _) hB0)
    · have h0 : f g = 0 := by
        by_contra h
        exact hg (hsupp h)
      simp only [h0, norm_zero, zero_mul]
      exact hpos

end GGPData

end GSpinGGP
