/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.CentralizerIso
import GSpinGGP.Foundations.ExpLocal
import GSpinGGP.Foundations.ModuleTopologyPAdic
import GSpinGGP.TraceFormula.JHatSelfDual

/-!
# Transport of `ĵ(O, ·)` along an isomorphism of descent data

`ĵ(O, ·)` (`jHat`) is defined through two choices: the self-dual Haar measure (`selfDualMeasure`)
and the orbit measure (`orbitMeasure`). Along a `CentralizerIso` `ι : (G_x, 𝔤_x) ≃ (G'_y, 𝔤'_y)`:

* `isSelfDual_map_iff`, `isJHat_comp_iff`: the defining conditions are transported (change of
  variables; choice-free);
* `isSelfDual_unique`: a self-dual measure is unique (Weil);
* `selfDualMeasure_map`, `selfDualHaar_map`: hence the chosen self-dual measures correspond;
* `isOrbitMeasure_map_iff`: the defining conditions of orbit measures are transported (uses
  `selfDualMeasure_map` for the Kirillov forms on complements of centralizers);
* `orbitMeasure_map`: hence the chosen orbit measures correspond (given uniqueness);
* `jHat_map`: `ĵ(ι O, ι X) = ĵ(O, X)` for regular `X`, when `b'` is nondegenerate on `𝔤'_y`, the
  regular set of `𝔤'_y` is open, and orbit measures on `𝔤'_y` are unique.
-/

noncomputable section

open MeasureTheory Filter Topology

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- **Uniqueness of the self-dual measure.** Two Haar measures on `V` that are both self-dual for
`B` and `ψ` are equal: they differ by a constant `c > 0`, and Fourier inversion for `c μ` reads
`c² f = f`.

Source: Weil, *Basic Number Theory*, 3rd ed., Ch. VII §2, pp. 104–105 ("the" self-dual Haar
measure for a given identification of `G` with `G*`), together with the uniqueness of Haar measure.
Weil's identification `V ≅ V*` needs `B` nondegenerate; the argument below does not use this.

Proof: by uniqueness of Haar measure (`V` is locally compact and second countable),
`ν = c μ` with `c > 0`; then `f(0) = c² f(0)` for a test function `f` with `f(0) ≠ 0`
(`exists_isTestFn_ne_zero`), so `c = 1`. -/
theorem isSelfDual_unique {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V]
    {B : LinearMap.BilinForm F V} {ψ : NontrivialAddChar F} {μ ν : Measure V}
    (hμ : IsSelfDual μ B ψ) (hν : IsSelfDual ν B ψ) : μ = ν := by
  haveI := IsModuleTopology.isTopologicalAddGroup F V
  haveI := TauCeti.ModuleTopology.locallyCompactSpace (Module.finBasis F V)
  haveI := secondCountableTopology_of_finiteDimensional F V
  haveI := hμ.1
  haveI := hν.1
  have hc := Measure.isAddLeftInvariant_eq_smul ν μ
  set c := Measure.addHaarScalarFactor ν μ
  obtain ⟨f, hf, hf0⟩ := exists_isTestFn_ne_zero F V
  have h1 := hμ.2 f hf 0
  have h2 := hν.2 f hf 0
  have hfour : fourierWRT ν B ψ f = fun Y => (c : ℂ) * fourierWRT μ B ψ f Y := by
    funext Y
    rw [fourierWRT, fourierWRT, hc, integral_smul_nnreal_measure, NNReal.smul_def,
      Complex.real_smul]
  rw [hfour, hc, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul] at h2
  simp only [mul_assoc] at h2
  rw [integral_const_mul, h1, ← mul_assoc] at h2
  have hc2 : ((c : ℝ) : ℂ) * (c : ℂ) = 1 := mul_right_cancel₀ hf0 (h2.trans (one_mul _).symm)
  have hc1 : c = 1 := by
    have : (c : ℝ) * c = 1 := by exact_mod_cast hc2
    have hpos : (0 : ℝ) ≤ c := c.2
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  rw [hc, hc1, one_smul]

/-- One direction of `isSelfDual_map_iff`. -/
theorem IsSelfDual.map {V V' : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [Module F V']
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [MeasurableSpace V'] [BorelSpace V']
    (e : V ≃ₗ[F] V') (he : Continuous e) (he' : Continuous e.symm)
    {B : LinearMap.BilinForm F V} {B' : LinearMap.BilinForm F V'}
    (hB : ∀ u v, B' (e u) (e v) = B u v) {ψ : NontrivialAddChar F} {μ : Measure V}
    (hμ : IsSelfDual μ B ψ) : IsSelfDual (μ.map e) B' ψ := by
  let h : V ≃ₜ V' := ⟨e.toEquiv, he, he'⟩
  let em : V ≃ᵐ V' := h.toMeasurableEquiv
  have hem : (em : V → V') = e := rfl
  haveI := hμ.1
  refine ⟨e.toAddEquiv.isAddHaarMeasure_map μ he he', fun f hf Z' => ?_⟩
  have hf' : IsTestFn (f ∘ e) :=
    ⟨hf.1.comp_continuous he, hf.2.comp_homeomorph h⟩
  have hfour : ∀ Y, fourierWRT (μ.map e) B' ψ f (e Y) = fourierWRT μ B ψ (f ∘ e) Y := fun Y => by
    unfold fourierWRT
    rw [← hem, integral_map_equiv em]
    simp only [hem, Function.comp_apply, hB]
  calc ∫ Y', fourierWRT (μ.map e) B' ψ f Y' * ψ (-(B' Z' Y')) ∂(μ.map e)
      = ∫ Y, fourierWRT (μ.map e) B' ψ f (e Y) * ψ (-(B' Z' (e Y))) ∂μ := by
        rw [← hem, integral_map_equiv em]
    _ = ∫ Y, fourierWRT μ B ψ (f ∘ e) Y * ψ (-(B (e.symm Z') Y)) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
        simp only [hfour, ← hB, LinearEquiv.apply_symm_apply]
    _ = f Z' := by rw [hμ.2 _ hf' (e.symm Z'), Function.comp_apply, LinearEquiv.apply_symm_apply]

/-- **Self-duality is transported by isometries**: for a linear homeomorphism `e : V ≃ V'` with
`B'(e u, e v) = B(u, v)`, `e_* μ` is self-dual for `B'` iff `μ` is self-dual for `B`
(change of variables). -/
theorem isSelfDual_map_iff {V V' : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [Module F V']
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [MeasurableSpace V'] [BorelSpace V']
    (e : V ≃ₗ[F] V') (he : Continuous e) (he' : Continuous e.symm)
    {B : LinearMap.BilinForm F V} {B' : LinearMap.BilinForm F V'}
    (hB : ∀ u v, B' (e u) (e v) = B u v) (ψ : NontrivialAddChar F) (μ : Measure V) :
    IsSelfDual (μ.map e) B' ψ ↔ IsSelfDual μ B ψ := by
  refine ⟨fun h => ?_, IsSelfDual.map e he he' hB⟩
  have hB' : ∀ u v, B (e.symm u) (e.symm v) = B' u v := fun u v => by
    rw [← hB, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have := IsSelfDual.map e.symm he' he hB' h
  rwa [Measure.map_map he'.measurable he.measurable,
    show (⇑e.symm ∘ ⇑e) = id from funext e.symm_apply_apply, Measure.map_id] at this

/-- **The self-dual measures correspond** under a linear homeomorphism `e : V ≃ V'` with
`B'(e u, e v) = B(u, v)`: `selfDualMeasure B' ψ = e_* selfDualMeasure B ψ` (transport,
`isSelfDual_map_iff`, and uniqueness, `isSelfDual_unique`). -/
theorem selfDualMeasure_map {V V' : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [Module F V']
    [FiniteDimensional F V'] [TopologicalSpace V'] [IsTopologicalAddGroup V']
    [IsModuleTopology F V'] [MeasurableSpace V'] [BorelSpace V']
    (e : V ≃ₗ[F] V') (he : Continuous e) (he' : Continuous e.symm)
    {B : LinearMap.BilinForm F V} {B' : LinearMap.BilinForm F V'}
    (hB : ∀ u v, B' (e u) (e v) = B u v) (ψ : NontrivialAddChar F) :
    selfDualMeasure B' ψ = (selfDualMeasure B ψ).map e := by
  have key := fun μ => isSelfDual_map_iff e he he' hB ψ μ
  let em : V ≃ᵐ V' := (⟨e.toEquiv, he, he'⟩ : V ≃ₜ V').toMeasurableEquiv
  unfold selfDualMeasure
  by_cases h : ∃ μ, IsSelfDual μ B ψ
  · have h' : ∃ μ, IsSelfDual μ B' ψ := ⟨_, (key _).mpr h.choose_spec⟩
    rw [dif_pos h, dif_pos h']
    exact isSelfDual_unique h'.choose_spec ((key _).mpr h.choose_spec)
  · have h' : ¬ ∃ μ, IsSelfDual μ B' ψ := by
      rintro ⟨μ', hμ'⟩
      refine h ⟨μ'.map e.symm, (key _).mp ?_⟩
      rwa [show (μ'.map e.symm).map e = μ' from em.map_map_symm]
    rw [dif_neg h, dif_neg h', Measure.map_zero]

variable {A : Type*} [Ring A] [Algebra F A] [TopologicalSpace A] [Module.Finite F A]
  [IsModuleTopology F A]
  {A' : Type*} [Ring A'] [Algebra F A'] [TopologicalSpace A'] [Module.Finite F A']
  [IsModuleTopology F A']

namespace CentralizerIso

variable {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A} {b : LinearMap.BilinForm F A}
  {G' : Subgroup A'ˣ} {𝔤' : LieSubalgebra F A'} {b' : LinearMap.BilinForm F A'}
  {x : Aˣ} {y : A'ˣ} (ι : CentralizerIso G 𝔤 b G' 𝔤' b' x y)

theorem continuous_linEquiv : Continuous ι.linEquiv := by
  haveI := isModuleTopology_lieSubalgebra (lieCentralizer 𝔤 (x : A))
  haveI := isModuleTopology_lieSubalgebra (lieCentralizer 𝔤' (y : A'))
  haveI : ContinuousAdd ↥(lieCentralizer 𝔤 (x : A)) := IsModuleTopology.toContinuousAdd F _
  haveI : ContinuousAdd ↥(lieCentralizer 𝔤' (y : A')) := IsModuleTopology.toContinuousAdd F _
  exact IsModuleTopology.continuous_of_linearMap ι.linEquiv.toLinearMap

theorem continuous_linEquiv_symm : Continuous ι.linEquiv.symm := by
  haveI := isModuleTopology_lieSubalgebra (lieCentralizer 𝔤 (x : A))
  haveI := isModuleTopology_lieSubalgebra (lieCentralizer 𝔤' (y : A'))
  haveI : ContinuousAdd ↥(lieCentralizer 𝔤 (x : A)) := IsModuleTopology.toContinuousAdd F _
  haveI : ContinuousAdd ↥(lieCentralizer 𝔤' (y : A')) := IsModuleTopology.toContinuousAdd F _
  exact IsModuleTopology.continuous_of_linearMap ι.linEquiv.symm.toLinearMap

theorem restrictForm_linEquiv (X Y : ↥(lieCentralizer 𝔤 (x : A))) :
    restrictForm (lieCentralizer 𝔤' (y : A')) b' (ι.linEquiv X) (ι.linEquiv Y) =
      restrictForm (lieCentralizer 𝔤 (x : A)) b X Y :=
  ι.map_bilin X X.2 Y Y.2

/-- **The self-dual Haar measures correspond**: `selfDualHaar 𝔤'_y = ι_* selfDualHaar 𝔤_x`
(`selfDualMeasure_map`). -/
theorem selfDualHaar_map (ψ : NontrivialAddChar F) :
    selfDualHaar (lieCentralizer 𝔤' (y : A')) b' ψ =
      (selfDualHaar (lieCentralizer 𝔤 (x : A)) b ψ).map ι.linEquiv := by
  haveI := isModuleTopology_lieSubalgebra (lieCentralizer 𝔤 (x : A))
  haveI := isModuleTopology_lieSubalgebra (lieCentralizer 𝔤' (y : A'))
  haveI := isTopologicalAddGroup_lieSubalgebra (lieCentralizer 𝔤 (x : A))
  haveI := isTopologicalAddGroup_lieSubalgebra (lieCentralizer 𝔤' (y : A'))
  exact selfDualMeasure_map ι.linEquiv ι.continuous_linEquiv ι.continuous_linEquiv_symm
    ι.restrictForm_linEquiv ψ

variable (hG : ∀ g ∈ G, ∀ Y ∈ 𝔤, (g : A) * Y * (↑g⁻¹ : A) ∈ 𝔤)

/-- **Orbit measures are transported**: `ι_* μ` satisfies the defining conditions of the orbit
measure of `ι O` iff `μ` satisfies those of `O`. `ι` carries the orbit `O` onto `ι O`
(`linEquiv_mem_nilOrbitSet_iff`), the adjoint action of `G_x(F)` to that of `G'_y(F)`
(`preimage_conjAd_image`), the Kirillov forms `b(·, [X, ·])` to `b'(·, [ι X, ·])`
(`kirillovForm_linEquiv`), complements of `𝔤_{x,X}` to complements of `𝔤'_{y, ι X}`
(`ker_ad_linEquiv`), and the charts `Y ↦ e^Y X e^{-Y}` to the charts at `ι X`
(`preimage_orbitMap_image`; near `0` the chart stays in `𝔤_x`, `exists_nhds_expA_conj_mem`).
The self-dual measures on the complements correspond (`selfDualMeasure_map`, which rests on the
uniqueness `isSelfDual_unique`); neighbourhoods of `0` correspond since `ι` is a linear
homeomorphism of `𝔤_x(F)` onto `𝔤'_y(F)`. -/
theorem isOrbitMeasure_map_iff (ψ : NontrivialAddChar F)
    (O : NilOrbit (grpCentralizer G x) (lieCentralizer 𝔤 (x : A)))
    (μ : Measure ↥(lieCentralizer 𝔤 (x : A))) :
    IsOrbitMeasure (grpCentralizer G' y) (lieCentralizer 𝔤' (y : A')) b' ψ
        (ι.nilOrbitEquiv hG O) (μ.map ι.linEquiv) ↔
      IsOrbitMeasure (grpCentralizer G x) (lieCentralizer 𝔤 (x : A)) b ψ O μ := by
  -- instances on `𝔤_x`, `𝔤'_y` and their subspaces
  haveI := t2Space_of_moduleTopology F A
  haveI := t2Space_of_moduleTopology F A'
  haveI := isModuleTopology_lieSubalgebra (lieCentralizer 𝔤 (x : A))
  haveI := isModuleTopology_lieSubalgebra (lieCentralizer 𝔤' (y : A'))
  haveI := isTopologicalAddGroup_lieSubalgebra (lieCentralizer 𝔤 (x : A))
  haveI := isTopologicalAddGroup_lieSubalgebra (lieCentralizer 𝔤' (y : A'))
  let em := ι.linEquiv.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hem : (em : ↥(lieCentralizer 𝔤 (x : A)) → ↥(lieCentralizer 𝔤' (y : A'))) = ι.linEquiv :=
    rfl
  have hmap : ∀ T, (μ.map ι.linEquiv) T = μ (ι.linEquiv ⁻¹' T) := fun T => by
    rw [← hem]; exact em.map_apply T
  have hnil : ι.linEquiv ⁻¹' nilOrbitSet (ι.nilOrbitEquiv hG O) = nilOrbitSet O :=
    Set.ext fun X => ι.linEquiv_mem_nilOrbitSet_iff hG O X
  -- near `0`, the chart `Y ↦ e^Y X e^{-Y}` stays in `𝔤_x`
  obtain ⟨U₀, hU₀, hconj⟩ := exists_nhds_expA_conj_mem F (A := A)
  have hstay : ∀ X Y : ↥(lieCentralizer 𝔤 (x : A)), (Y : A) ∈ U₀ →
      orbitMap F (X : A) (Y : A) ∈ lieCentralizer 𝔤 (x : A) := fun X Y hY =>
    hconj _ hY (lieCentralizer 𝔤 (x : A)).toSubmodule (fun r hr => by
      have := (lieCentralizer 𝔤 (x : A)).lie_mem Y.2 hr
      rwa [Ring.lie_def] at this) _ X.2
  -- `ι` restricted to a subspace `C` of `𝔤_x` is a linear homeomorphism onto `ι C`
  have hcont : ∀ C : Submodule F ↥(lieCentralizer 𝔤 (x : A)),
      Measurable (ι.linEquiv.submoduleMap C) ∧ Measurable (ι.linEquiv.submoduleMap C).symm :=
    fun C => ⟨(ι.linEquiv.submoduleMap C).toContinuousLinearEquiv.continuous.measurable,
      (ι.linEquiv.submoduleMap C).toContinuousLinearEquiv.symm.continuous.measurable⟩
  -- the self-dual measures for the Kirillov forms on `C` and `ι C` correspond
  have hsd : ∀ (X : ↥(lieCentralizer 𝔤 (x : A))) (C : Submodule F ↥(lieCentralizer 𝔤 (x : A)))
      (T : Set ↥(C.map (ι.linEquiv :
        ↥(lieCentralizer 𝔤 (x : A)) →ₗ[F] ↥(lieCentralizer 𝔤' (y : A'))))),
      selfDualMeasure ((kirillovForm (lieCentralizer 𝔤' (y : A')) b' (ι.linEquiv X)).compl₁₂
          (C.map (ι.linEquiv : ↥(lieCentralizer 𝔤 (x : A)) →ₗ[F] ↥(lieCentralizer 𝔤' (y : A')))).subtype
          (C.map (ι.linEquiv :
            ↥(lieCentralizer 𝔤 (x : A)) →ₗ[F] ↥(lieCentralizer 𝔤' (y : A')))).subtype) ψ T =
        selfDualMeasure ((kirillovForm (lieCentralizer 𝔤 (x : A)) b X).compl₁₂ C.subtype
          C.subtype) ψ (ι.linEquiv.submoduleMap C ⁻¹' T) := by
    intro X C T
    haveI : IsModuleTopology F ↥(C.map (ι.linEquiv :
        ↥(lieCentralizer 𝔤 (x : A)) →ₗ[F] ↥(lieCentralizer 𝔤' (y : A')))) :=
      isModuleTopologyOfFiniteDimensional (𝕜 := F)
    set eC := (ι.linEquiv.submoduleMap C).toContinuousLinearEquiv
    rw [selfDualMeasure_map eC.toLinearEquiv eC.continuous eC.symm.continuous
      (B := (kirillovForm (lieCentralizer 𝔤 (x : A)) b X).compl₁₂ C.subtype C.subtype) (fun u v => by
        simp only [LinearMap.compl₁₂_apply, Submodule.subtype_apply, eC]
        exact ι.kirillovForm_linEquiv X u v) ψ]
    exact eC.toHomeomorph.toMeasurableEquiv.map_apply T
  unfold IsOrbitMeasure
  rw [hmap, Set.preimage_compl, hnil]
  refine and_congr Iff.rfl (and_congr ⟨fun h2' => ?_, fun h2 => ?_⟩ ⟨fun h3' => ?_, fun h3 => ?_⟩)
  · intro g hg S hS
    have hS' : MeasurableSet (ι.linEquiv.symm ⁻¹' S) := hS.preimage em.symm.measurable
    have hpre : ι.linEquiv ⁻¹' (ι.linEquiv.symm ⁻¹' S) = S := by ext; simp
    have := h2' (ι.grp g) (ι.grp_mapsTo hg) _ hS'
    rwa [hmap, hmap, ι.preimage_conjAd_image hG hg, hpre] at this
  · intro g' hg' S' hS'
    obtain ⟨g, hg, rfl⟩ := ι.grp_surjOn hg'
    rw [hmap, hmap, ι.preimage_conjAd_image hG hg]
    exact h2 g hg _ (hS'.preimage em.measurable)
  · intro X hX C hCX
    have hC' := Submodule.isCompl_map ι.linEquiv hCX
    rw [← ι.ker_ad_linEquiv] at hC'
    obtain ⟨U', hU', hUS'⟩ :=
      h3' (ι.linEquiv X) ((ι.linEquiv_mem_nilOrbitSet_iff hG O X).mpr hX) _ hC'
    haveI := IsModuleTopology.toContinuousAdd F A'
    have hlin : Continuous ι.lin := IsModuleTopology.continuous_of_linearMap ι.lin
    refine ⟨(U₀ ∩ ι.orbitNhd) ∩ ι.lin ⁻¹' U', Filter.inter_mem
      (Filter.inter_mem hU₀ ι.orbitNhd_mem_nhds)
      (hlin.continuousAt.preimage_mem_nhds (by rwa [map_zero])), fun S hS hSU => ?_⟩
    have hSm : MeasurableSet (ι.linEquiv.submoduleMap C '' S) := by
      rw [LinearEquiv.image_eq_preimage_symm]
      exact hS.preimage (hcont C).2
    have := hUS' (ι.linEquiv.submoduleMap C '' S) hSm (by
      rintro _ ⟨Y, hY, rfl⟩
      simpa using (hSU Y hY).2)
    rwa [hmap, ι.preimage_orbitMap_image X C S (fun Y hY => hstay X Y (hSU Y hY).1.1)
      (fun Y hY => (hSU Y hY).1.2), hsd,
      Set.preimage_image_eq _ (ι.linEquiv.submoduleMap C).injective] at this
  · intro X' hX' C' hC'
    obtain ⟨X, rfl⟩ := ι.linEquiv.surjective X'
    obtain ⟨C, rfl⟩ : ∃ C : Submodule F ↥(lieCentralizer 𝔤 (x : A)),
        C.map (ι.linEquiv :
          ↥(lieCentralizer 𝔤 (x : A)) →ₗ[F] ↥(lieCentralizer 𝔤' (y : A'))) = C' :=
      ⟨_, Submodule.map_comap_eq_of_surjective ι.linEquiv.surjective C'⟩
    rw [ι.ker_ad_linEquiv] at hC'
    have hX : X ∈ nilOrbitSet O := (ι.linEquiv_mem_nilOrbitSet_iff hG O X).mp hX'
    obtain ⟨U, hU, hUS⟩ :=
      h3 X hX C ((Submodule.orderIsoMapComap ι.linEquiv).isCompl_iff.mpr hC')
    obtain ⟨U', hU', hUU'⟩ := ι.exists_nhds_of_mem_nhds
      (Filter.inter_mem hU (Filter.inter_mem hU₀ ι.orbitNhd_mem_nhds))
    refine ⟨U', hU', fun S' hS' hS'U => ?_⟩
    obtain ⟨S, rfl⟩ : ∃ S, ι.linEquiv.submoduleMap C '' S = S' :=
      ⟨_, Set.image_preimage_eq S' (ι.linEquiv.submoduleMap C).surjective⟩
    have hSU : ∀ Y ∈ S, ((Y : ↥(lieCentralizer 𝔤 (x : A))) : A) ∈ U ∩ (U₀ ∩ ι.orbitNhd) :=
      fun Y hY =>
        hUU' _ (Y : ↥(lieCentralizer 𝔤 (x : A))).2 (by simpa using hS'U _ ⟨Y, hY, rfl⟩)
    have hSm : MeasurableSet S := by
      have := hS'.preimage (hcont C).1
      rwa [Set.preimage_image_eq _ (ι.linEquiv.submoduleMap C).injective] at this
    rw [hmap, ι.preimage_orbitMap_image X C S (fun Y hY => hstay X Y (hSU Y hY).2.1)
      (fun Y hY => (hSU Y hY).2.2),
      hUS S hSm (fun Y hY => (hSU Y hY).1), hsd,
      Set.preimage_image_eq _ (ι.linEquiv.submoduleMap C).injective]

/-- **The orbit measures correspond**, when orbit measures on `𝔤'_y` are unique (`hu'`). -/
theorem orbitMeasure_map (ψ : NontrivialAddChar F)
    (hu' : ∀ O' μ ν, IsOrbitMeasure (grpCentralizer G' y) (lieCentralizer 𝔤' (y : A')) b' ψ O' μ →
      IsOrbitMeasure (grpCentralizer G' y) (lieCentralizer 𝔤' (y : A')) b' ψ O' ν → μ = ν)
    (O : NilOrbit (grpCentralizer G x) (lieCentralizer 𝔤 (x : A))) :
    orbitMeasure (grpCentralizer G' y) (lieCentralizer 𝔤' (y : A')) b' ψ (ι.nilOrbitEquiv hG O) =
      (orbitMeasure (grpCentralizer G x) (lieCentralizer 𝔤 (x : A)) b ψ O).map ι.linEquiv := by
  have key := ι.isOrbitMeasure_map_iff hG ψ O
  unfold orbitMeasure
  by_cases h : ∃ μ, IsOrbitMeasure (grpCentralizer G x) (lieCentralizer 𝔤 (x : A)) b ψ O μ
  · have h' : ∃ μ, IsOrbitMeasure (grpCentralizer G' y) (lieCentralizer 𝔤' (y : A')) b' ψ
        (ι.nilOrbitEquiv hG O) μ := ⟨_, (key _).mpr h.choose_spec⟩
    rw [dif_pos h, dif_pos h']
    exact hu' _ _ _ h'.choose_spec ((key _).mpr h.choose_spec)
  · have h' : ¬ ∃ μ, IsOrbitMeasure (grpCentralizer G' y) (lieCentralizer 𝔤' (y : A')) b' ψ
        (ι.nilOrbitEquiv hG O) μ := by
      rintro ⟨μ', hμ'⟩
      refine h ⟨μ'.map ι.linEquiv.symm, (key _).mp ?_⟩
      rw [Measure.map_map ι.continuous_linEquiv.measurable ι.continuous_linEquiv_symm.measurable,
        show (⇑ι.linEquiv ∘ ⇑ι.linEquiv.symm) = id from funext ι.linEquiv.apply_symm_apply,
        Measure.map_id]
      exact hμ'
    rw [dif_neg h, dif_neg h', Measure.map_zero]

/-- **Representatives of `f ↦ μ_O(f̂)` are transported**, given that the orbit measures and the
self-dual measures correspond: `j'` represents it for `ι O` iff `j' ∘ ι` does for `O` (change of
variables `X' = ι X` in both integrals; `ι` preserves test functions and the regular sets). -/
theorem isJHat_comp_iff (ψ : NontrivialAddChar F)
    (O : NilOrbit (grpCentralizer G x) (lieCentralizer 𝔤 (x : A)))
    (hμO : orbitMeasure (grpCentralizer G' y) (lieCentralizer 𝔤' (y : A')) b' ψ
        (ι.nilOrbitEquiv hG O) =
      (orbitMeasure (grpCentralizer G x) (lieCentralizer 𝔤 (x : A)) b ψ O).map ι.linEquiv)
    (hμ : selfDualHaar (lieCentralizer 𝔤' (y : A')) b' ψ =
      (selfDualHaar (lieCentralizer 𝔤 (x : A)) b ψ).map ι.linEquiv)
    (j' : ↥(lieCentralizer 𝔤' (y : A')) → ℂ) :
    IsJHat (grpCentralizer G' y) (lieCentralizer 𝔤' (y : A')) b' ψ (ι.nilOrbitEquiv hG O) j' ↔
      IsJHat (grpCentralizer G x) (lieCentralizer 𝔤 (x : A)) b ψ O (j' ∘ ι.linEquiv) := by
  have hc := ι.continuous_linEquiv
  have hc' := ι.continuous_linEquiv_symm
  let h : ↥(lieCentralizer 𝔤 (x : A)) ≃ₜ ↥(lieCentralizer 𝔤' (y : A')) :=
    ⟨ι.linEquiv.toEquiv, hc, hc'⟩
  let em := h.toMeasurableEquiv
  have hem : (em : ↥(lieCentralizer 𝔤 (x : A)) → ↥(lieCentralizer 𝔤' (y : A'))) = ι.linEquiv :=
    rfl
  have hR : ∀ Z : ↥(lieCentralizer 𝔤 (x : A)),
      IsRegularSS (lieCentralizer 𝔤' (y : A')) ((ι.linEquiv Z : ↥(lieCentralizer 𝔤' (y : A'))) : A')
        ↔ IsRegularSS (lieCentralizer 𝔤 (x : A)) (Z : A) := fun Z => ι.isRegularSS_iff Z Z.2
  have htest : ∀ f : ↥(lieCentralizer 𝔤' (y : A')) → ℂ, IsTestFn f → IsTestFn (f ∘ ι.linEquiv) :=
    fun f hf => ⟨hf.1.comp_continuous hc, hf.2.comp_homeomorph h⟩
  have htest' : ∀ f : ↥(lieCentralizer 𝔤 (x : A)) → ℂ, IsTestFn f →
      IsTestFn (f ∘ ι.linEquiv.symm) :=
    fun f hf => ⟨hf.1.comp_continuous hc', hf.2.comp_homeomorph h.symm⟩
  have hfour : ∀ f Y, fourierLie (lieCentralizer 𝔤' (y : A')) b' ψ f (ι.linEquiv Y) =
      fourierLie (lieCentralizer 𝔤 (x : A)) b ψ (f ∘ ι.linEquiv) Y := fun f Y => by
    unfold fourierLie fourierWRT
    rw [hμ, ← hem, integral_map_equiv em]
    simp only [hem, Function.comp_apply, ι.restrictForm_linEquiv]
  have hint : ∀ f, ∫ X, fourierLie (lieCentralizer 𝔤' (y : A')) b' ψ f X ∂(orbitMeasure
      (grpCentralizer G' y) (lieCentralizer 𝔤' (y : A')) b' ψ (ι.nilOrbitEquiv hG O)) =
      ∫ X, fourierLie (lieCentralizer 𝔤 (x : A)) b ψ (f ∘ ι.linEquiv) X ∂(orbitMeasure
        (grpCentralizer G x) (lieCentralizer 𝔤 (x : A)) b ψ O) := fun f => by
    rw [hμO, ← hem, integral_map_equiv em]
    simp only [hem, hfour]
  have hint2 : ∀ f : ↥(lieCentralizer 𝔤' (y : A')) → ℂ,
      ∫ X, f X * j' X ∂(selfDualHaar (lieCentralizer 𝔤' (y : A')) b' ψ) =
      ∫ X, (f ∘ ι.linEquiv) X * (j' ∘ ι.linEquiv) X ∂(selfDualHaar (lieCentralizer 𝔤 (x : A)) b ψ) :=
    fun f => by rw [hμ, ← hem, integral_map_equiv em]; rfl
  have hli := locallyIntegrable_map_homeomorph h (f := j')
    (μ := selfDualHaar (lieCentralizer 𝔤 (x : A)) b ψ)
  refine ⟨fun ⟨h1, h2, h3⟩ => ⟨?_, ?_, fun f hf => ?_⟩, fun ⟨h1, h2, h3⟩ => ⟨?_, ?_, fun f hf => ?_⟩⟩
  · exact h1.comp hc.continuousOn fun Z hZ => (hR Z).mpr hZ
  · rw [hμ] at h2
    exact hli.mp h2
  · have := h3 _ (htest' f hf)
    rw [hint, hint2] at this
    have hff : (f ∘ ι.linEquiv.symm) ∘ ι.linEquiv = f := funext fun Z => by simp
    rwa [hff] at this
  · refine (h1.comp hc'.continuousOn fun Z' hZ' => ?_).congr fun Z' _ => by simp
    have := hR (ι.linEquiv.symm Z')
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.mp hZ'
  · rw [hμ]
    exact hli.mpr h2
  · rw [hint, hint2]
    exact h3 _ (htest f hf)

/-- **`ĵ(ι O, ι X) = ĵ(O, X)`** for `X ∈ 𝔤_x` regular semisimple, when `b'` is nondegenerate on
`𝔤'_y`, the regular semisimple set of `𝔤'_y` is open, and orbit measures on `𝔤'_y` are unique:
the chosen measures correspond (`selfDualHaar_map`, `orbitMeasure_map`), so representatives
correspond (`isJHat_comp_iff`), and two representatives agree on the open regular set
(`eqOn_of_isJHat`). -/
theorem jHat_map (ψ : NontrivialAddChar F)
    (hnd' : (restrictForm (lieCentralizer 𝔤' (y : A')) b').Nondegenerate)
    (hopen' : IsOpen {Z : ↥(lieCentralizer 𝔤' (y : A')) |
      IsRegularSS (lieCentralizer 𝔤' (y : A')) (Z : A')})
    (hu' : ∀ O' μ ν, IsOrbitMeasure (grpCentralizer G' y) (lieCentralizer 𝔤' (y : A')) b' ψ O' μ →
      IsOrbitMeasure (grpCentralizer G' y) (lieCentralizer 𝔤' (y : A')) b' ψ O' ν → μ = ν)
    (O : NilOrbit (grpCentralizer G x) (lieCentralizer 𝔤 (x : A)))
    (X : A) (hX : X ∈ lieCentralizer 𝔤 (x : A))
    (hXr : IsRegularSS (lieCentralizer 𝔤 (x : A)) X) :
    jHat (grpCentralizer G' y) (lieCentralizer 𝔤' (y : A')) b' ψ (ι.nilOrbitEquiv hG O)
        (ι.lin X) =
      jHat (grpCentralizer G x) (lieCentralizer 𝔤 (x : A)) b ψ O X := by
  have key := ι.isJHat_comp_iff hG ψ O (ι.orbitMeasure_map hG ψ hu' O) (ι.selfDualHaar_map ψ)
  have hX' : ι.lin X ∈ (lieCentralizer 𝔤' (y : A')) := ι.bijOn.mapsTo hX
  have he : ι.linEquiv ⟨X, hX⟩ = ⟨ι.lin X, hX'⟩ := rfl
  unfold jHat
  by_cases h : ∃ j, IsJHat (grpCentralizer G x) (lieCentralizer 𝔤 (x : A)) b ψ O j
  · have hj' : IsJHat (grpCentralizer G' y) (lieCentralizer 𝔤' (y : A')) b' ψ
        (ι.nilOrbitEquiv hG O) (h.choose ∘ ι.linEquiv.symm) := (key _).mpr (by
      have : (h.choose ∘ ι.linEquiv.symm) ∘ ι.linEquiv = h.choose := by
        funext Z; simp
      rw [this]; exact h.choose_spec)
    have h' : ∃ j, IsJHat (grpCentralizer G' y) (lieCentralizer 𝔤' (y : A')) b' ψ
        (ι.nilOrbitEquiv hG O) j := ⟨_, hj'⟩
    rw [dif_pos h, dif_pos h', dif_pos hX, dif_pos hX']
    -- the instances on `𝔤'_y` needed by `eqOn_of_isJHat`
    obtain ⟨_, _, _, _, _⟩ := lieSubalgebra_topology (lieCentralizer 𝔤' (y : A'))
    haveI := t2Space_of_moduleTopology F A'
    haveI := isTopologicalAddGroup_lieSubalgebra (lieCentralizer 𝔤' (y : A'))
    have hμ := isSelfDual_selfDualHaar_of_nondegenerate (lieCentralizer 𝔤' (y : A')) hnd' ψ
    haveI := hμ.1
    have hreg : (⟨ι.lin X, hX'⟩ : ↥(lieCentralizer 𝔤' (y : A'))) ∈
        {Z : ↥(lieCentralizer 𝔤' (y : A')) | IsRegularSS (lieCentralizer 𝔤' (y : A')) (Z : A')} :=
      (ι.isRegularSS_iff X hX).mpr hXr
    rw [eqOn_of_isJHat hμ h'.choose_spec hj' hopen' le_rfl hreg, Function.comp_apply, ← he,
      LinearEquiv.symm_apply_apply]
  · have h' : ¬ ∃ j, IsJHat (grpCentralizer G' y) (lieCentralizer 𝔤' (y : A')) b' ψ (ι.nilOrbitEquiv hG O) j :=
      fun ⟨j', hj'⟩ => h ⟨_, (key j').mp hj'⟩
    rw [dif_neg h, dif_neg h']

end CentralizerIso

end GSpinGGP
