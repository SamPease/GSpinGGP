/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalGroups
import GSpinGGP.Foundations.Representations
import GSpinGGP.Literature.Fourier

/-!
# Uniqueness of `ĵ(O, ·)` and its invariance under central translation

`ĵ(O, ·)` (`jHat`) is a chosen function representing the distribution `f ↦ μ_O(f̂)` (`IsJHat`).

* `eqOn_of_isJHat`: two such representatives agree on every open subset of the regular set
  (separation by locally constant functions, `ae_eq_zero_of_integral_isLocallyConstant`, and
  continuity on the regular set);
* `jHat_add_eq`: `ĵ(O, X + Y) = ĵ(O, X)` for `X` regular and `Y ∈ 𝔤` with `b(Y, N) = 0` for every
  nilpotent `N ∈ 𝔤` (e.g. `Y` central in `𝔤` and `b` a trace form), when `Z + Y` is regular
  iff `Z` is, at points `X` of an open set of regular elements.  Proof: `Z ↦ ĵ(O, Z + Y)` represents `f ↦ μ_O((f(· − Y))^)`, and
  `(f(· − Y))^ = ψ(b(Y, ·)) f̂` is `f̂` on the nilpotent orbit `O`.

* `jHat_add_eq_of_nondegenerate`: the same with the topological and measure-theoretic hypotheses
  discharged, for `b` nondegenerate on `𝔤`.

These hold over any `p`-adic field; the measure-theoretic hypotheses on `𝔤` (local compactness,
total disconnectedness, σ-compactness, outer regularity of the self-dual measure) are explicit.
-/

noncomputable section

open MeasureTheory Filter Topology

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
  {A : Type*} [Ring A] [Algebra F A] [TopologicalSpace A] [Module.Finite F A] [IsModuleTopology F A]

/-- **Uniqueness of `ĵ(O, ·)` on the regular set**: two functions representing
`f ↦ μ_O(f̂)` (`IsJHat`) agree on every open set of regular elements, when the self-dual measure
on `𝔤` is a genuine Haar measure. -/
theorem eqOn_of_isJHat {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A} {b : LinearMap.BilinForm F A}
    {ψ : NontrivialAddChar F} {O : NilOrbit G 𝔤} {j j' : ↥𝔤 → ℂ}
    [T2Space ↥𝔤] [IsTopologicalAddGroup ↥𝔤] [MeasurableAdd ↥𝔤]
    [LocallyCompactSpace ↥𝔤] [TotallyDisconnectedSpace ↥𝔤] [SigmaCompactSpace ↥𝔤]
    [BorelSpace ↥𝔤] (hμ : IsSelfDual (selfDualHaar 𝔤 b ψ) (restrictForm 𝔤 b) ψ)
    [(selfDualHaar 𝔤 b ψ).OuterRegular] (hj : IsJHat G 𝔤 b ψ O j) (hj' : IsJHat G 𝔤 b ψ O j')
    {U : Set ↥𝔤} (hU : IsOpen U) (hUreg : U ⊆ {X | IsRegularSS 𝔤 (X : A)}) :
    Set.EqOn j j' U := by
  have := hμ.1
  set μ := selfDualHaar 𝔤 b ψ
  have hint : ∀ {φ : ↥𝔤 → ℂ}, LocallyIntegrable φ μ → ∀ f : ↥𝔤 → ℂ, IsTestFn f →
      Integrable (fun X => f X * φ X) μ := by
    intro φ hφ f hf
    simpa [smul_eq_mul] using hφ.integrable_smul_left_of_hasCompactSupport hf.1.continuous hf.2
  have hae : (fun X => j X - j' X) =ᵐ[μ] 0 := by
    refine ae_eq_zero_of_integral_isLocallyConstant (hj.2.1.sub hj'.2.1) fun f hf hc => ?_
    have h1 := (hj.2.2 f ⟨hf, hc⟩).symm.trans (hj'.2.2 f ⟨hf, hc⟩)
    have e : (fun X => (j X - j' X) * f X) = fun X => f X * j X - f X * j' X := by
      funext X; ring
    rw [e, integral_sub (hint hj.2.1 f ⟨hf, hc⟩) (hint hj'.2.1 f ⟨hf, hc⟩), h1, sub_self]
  have hae' : j =ᵐ[μ] j' := by
    filter_upwards [hae] with X hX
    simpa [sub_eq_zero] using hX
  exact Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hae') hU (hj.1.mono hUreg) (hj'.1.mono hUreg)

omit [PAdicField F] in
/-- `ψ(a + b) = ψ(a) ψ(b)`. -/
theorem NontrivialAddChar.map_add (ψ : NontrivialAddChar F) (a c : F) : ψ (a + c) = ψ a * ψ c := by
  show ((ψ.toAddChar (a + c) : Circle) : ℂ) = ((ψ.toAddChar a : Circle) : ℂ) * (ψ.toAddChar c : Circle)
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

omit [PAdicField F] in
/-- `ψ(0) = 1`. -/
theorem NontrivialAddChar.map_zero (ψ : NontrivialAddChar F) : ψ 0 = 1 := by
  show ((ψ.toAddChar 0 : Circle) : ℂ) = 1
  rw [AddChar.map_zero_eq_one, Circle.coe_one]

/-- **`ĵ(O, ·)` is invariant under translation by `Y`** with `b(Y, N) = 0` for every nilpotent
`N ∈ 𝔤`, at every point `X` of an open set of regular elements, when `Z + Y` is regular iff `Z`
is. -/
theorem jHat_add_eq {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A} {b : LinearMap.BilinForm F A}
    {ψ : NontrivialAddChar F} (O : NilOrbit G 𝔤)
    [T2Space ↥𝔤] [IsTopologicalAddGroup ↥𝔤] [MeasurableAdd ↥𝔤]
    [LocallyCompactSpace ↥𝔤] [TotallyDisconnectedSpace ↥𝔤] [SigmaCompactSpace ↥𝔤]
    [BorelSpace ↥𝔤] (hμ : IsSelfDual (selfDualHaar 𝔤 b ψ) (restrictForm 𝔤 b) ψ)
    [(selfDualHaar 𝔤 b ψ).OuterRegular] (Y : ↥𝔤)
    (hbY : ∀ N : ↥𝔤, IsNilpotent (N : A) → b (Y : A) (N : A) = 0)
    (hreg : ∀ Z : ↥𝔤, IsRegularSS 𝔤 ((Z + Y : ↥𝔤) : A) ↔ IsRegularSS 𝔤 (Z : A))
    {U : Set ↥𝔤} (hU : IsOpen U) (hUreg : U ⊆ {X | IsRegularSS 𝔤 (X : A)}) {X : ↥𝔤} (hX : X ∈ U) :
    jHat G 𝔤 b ψ O ((X : A) + (Y : A)) = jHat G 𝔤 b ψ O (X : A) := by
  have := hμ.1
  set μ := selfDualHaar 𝔤 b ψ
  by_cases h : ∃ j, IsJHat G 𝔤 b ψ O j
  swap
  · simp [jHat, h]
  have hXY : (X : A) + (Y : A) ∈ 𝔤 := 𝔤.add_mem X.2 Y.2
  simp only [jHat, h, hXY, X.2, ↓reduceDIte]
  set j := h.choose
  have hj := h.choose_spec
  set j' : ↥𝔤 → ℂ := fun Z => j (Z + Y) with hj'def
  -- `j'` also represents `f ↦ μ_O(f̂)`
  have hj' : IsJHat G 𝔤 b ψ O j' := by
    refine ⟨?_, ?_, fun f hf => ?_⟩
    · exact hj.1.comp (continuous_id.add continuous_const).continuousOn fun Z hZ => (hreg Z).mpr hZ
    · have hloc := hj.2.1
      rw [locallyIntegrable_iff] at hloc ⊢
      intro K hK
      have hmp := measurePreserving_add_right μ Y
      have hemb : MeasurableEmbedding (fun Z : ↥𝔤 => Z + Y) :=
        (Homeomorph.addRight Y).measurableEmbedding
      have hK' : (fun Z : ↥𝔤 => Z + Y) ⁻¹' ((fun Z : ↥𝔤 => Z + Y) '' K) = K :=
        Set.preimage_image_eq K (add_left_injective Y)
      have := (hmp.integrableOn_comp_preimage hemb (f := j)
        (s := (fun Z : ↥𝔤 => Z + Y) '' K)).mpr (hloc _ (hK.image (continuous_id.add continuous_const)))
      rwa [hK'] at this
    · -- change of variables, then the Fourier transform of the translate
      set g : ↥𝔤 → ℂ := fun Z => f (Z - Y) with hgdef
      have hg : IsTestFn g := ⟨hf.1.comp_continuous (continuous_sub_right Y),
        hf.2.comp_homeomorph (Homeomorph.subRight Y)⟩
      have h1 : ∫ Z, f Z * j' Z ∂μ = ∫ Z, g Z * j Z ∂μ := by
        have := integral_add_right_eq_self (μ := μ) (fun Z => g Z * j Z) Y
        simpa [hgdef, hj'def] using this
      have h2 : ∀ W, fourierLie 𝔤 b ψ g W = ψ (restrictForm 𝔤 b Y W) * fourierLie 𝔤 b ψ f W := by
        intro W
        unfold fourierLie fourierWRT
        have := integral_add_right_eq_self (μ := μ)
          (fun Z => g Z * ψ (restrictForm 𝔤 b Z W)) Y
        rw [← this, ← integral_const_mul]
        congr 1
        funext Z
        simp only [hgdef, add_sub_cancel_right, map_add, LinearMap.add_apply,
          NontrivialAddChar.map_add]
        ring
      rw [h1, ← hj.2.2 g hg]
      simp_rw [h2]
      -- on the orbit `ψ(b(Y, ·)) = 1`
      by_cases hO : ∃ ν, IsOrbitMeasure G 𝔤 b ψ O ν
      · have hspec := hO.choose_spec
        have hνdef : orbitMeasure G 𝔤 b ψ O = hO.choose := by simp [orbitMeasure, hO]
        rw [hνdef]
        refine integral_congr_ae ?_
        have hnull : ∀ᵐ W ∂hO.choose, W ∈ nilOrbitSet O := by
          rw [ae_iff]
          exact hspec.1
        filter_upwards [hnull] with W hW
        obtain ⟨hWn, -⟩ := hW
        have : restrictForm 𝔤 b Y W = 0 := hbY W hWn
        rw [this, NontrivialAddChar.map_zero, one_mul]
      · have hνdef : orbitMeasure G 𝔤 b ψ O = 0 := by simp [orbitMeasure, hO]
        rw [hνdef, integral_zero_measure, integral_zero_measure]
  have hEq := eqOn_of_isJHat hμ hj' hj hU hUreg hX
  have hXY' : (⟨(X : A) + (Y : A), hXY⟩ : ↥𝔤) = X + Y := rfl
  rw [hXY']
  exact hEq

/-- **`ĵ(O, ·)` is invariant under translation by `Y`**, for a Lie subalgebra `𝔤` on which `b` is
nondegenerate: `jHat_add_eq` with its topological and measure-theoretic hypotheses discharged
(`𝔤` is linearly homeomorphic to `F^n`; the self-dual measure exists, `exists_isSelfDual`, and is
regular, being a Haar measure on a second-countable locally compact group). -/
theorem jHat_add_eq_of_nondegenerate {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A}
    {b : LinearMap.BilinForm F A} {ψ : NontrivialAddChar F} (O : NilOrbit G 𝔤)
    (hnd : (restrictForm 𝔤 b).Nondegenerate) (Y : ↥𝔤)
    (hbY : ∀ N : ↥𝔤, IsNilpotent (N : A) → b (Y : A) (N : A) = 0)
    (hreg : ∀ Z : ↥𝔤, IsRegularSS 𝔤 ((Z + Y : ↥𝔤) : A) ↔ IsRegularSS 𝔤 (Z : A))
    {U : Set ↥𝔤} (hU : IsOpen U) (hUreg : U ⊆ {X | IsRegularSS 𝔤 (X : A)}) {X : ↥𝔤} (hX : X ∈ U) :
    jHat G 𝔤 b ψ O ((X : A) + (Y : A)) = jHat G 𝔤 b ψ O (X : A) := by
  haveI := t2Space_of_moduleTopology F A
  haveI := isTopologicalRing_of_moduleTopology F A
  have hind : IsInducing (𝔤.incl.toLinearMap : ↥𝔤 → A) := IsInducing.subtypeVal
  haveI : IsTopologicalAddGroup ↥𝔤 := hind.isTopologicalAddGroup 𝔤.incl.toLinearMap
  haveI : ContinuousSMul F ↥𝔤 :=
    hind.continuousSMul continuous_id (fun {c x} => 𝔤.incl.toLinearMap.map_smul c x)
  -- `𝔤 ≅ F^n` as topological vector spaces
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let e : ↥𝔤 ≃L[F] (Fin (Module.finrank F ↥𝔤) → F) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  haveI : LocallyCompactSpace ↥𝔤 := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : TotallyDisconnectedSpace ↥𝔤 := e.toHomeomorph.symm.totallyDisconnectedSpace
  haveI : SigmaCompactSpace ↥𝔤 := e.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  haveI : SecondCountableTopology ↥𝔤 := e.toHomeomorph.isEmbedding.secondCountableTopology
  -- the self-dual measure
  have hex : ∃ μ, IsSelfDual μ (restrictForm 𝔤 b) ψ :=
    exists_isSelfDual_of_isInducing 𝔤.incl.toLinearMap hind Subtype.val_injective _ hnd ψ
  have hμ : IsSelfDual (selfDualHaar 𝔤 b ψ) (restrictForm 𝔤 b) ψ := by
    unfold selfDualHaar selfDualMeasure
    rw [dif_pos hex]
    exact hex.choose_spec
  haveI := hμ.1
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : ↥𝔤)
  haveI : (selfDualHaar 𝔤 b ψ).Regular :=
    Measure.regular_of_isAddLeftInvariant hK ⟨0, mem_interior_iff_mem_nhds.mpr hKn⟩
      hK.measure_lt_top.ne
  exact jHat_add_eq O hμ Y hbY hreg hU hUreg hX

end GSpinGGP
