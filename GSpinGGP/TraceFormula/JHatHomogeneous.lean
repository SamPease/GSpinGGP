/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.JHatScale
import GSpinGGP.Foundations.TorusIntegrability

/-!
# Homogeneity of `ĵ(O, ·)` (BP (1.8.5))

Beuzart-Plessis, Astérisque 418, (1.8.5) (p. 34; arXiv:1506.01452, p. 40):
`ĵ(O, λX) = |λ|^{-dim(O)/2} ĵ(λO, X)` for all nilpotent orbits `O`, regular `X` and `λ ∈ F^×`.
Here it is proved from the definitions (`jHat_smul`), for any `(G, 𝔤, b)` with `b` nondegenerate on
`𝔤`, open regular set and unique orbit measures (the hypotheses of `jHat_scale`).

* `integral_comp_smul_absF`: `∫ g(c Y) dμ(Y) = |c|_F^{-n} ∫ g dμ` for a Haar measure on an
  `n`-dimensional `F`-vector space.
* `selfDualMeasure_smul`: the self-dual measure of `c B` is `|c|_F^{n/2}` times that of `B`
  (`κ² |c|^{-n} = 1` in the inversion formula, and uniqueness of self-dual measures).
* `isOrbitMeasure_smul_iff`, `orbitMeasure_smul`: the orbit measure of `O` for `c b` is
  `|c|_F^{k/2}` times that for `b`, `k = dim O` (the Kirillov form of `c b` is `c` times that of
  `b`).
* `isJHat_smul`: if `j` represents `f ↦ μ_O(f̂)` for `b`, then `|c|_F^{k/2} j(c ·)` represents it
  for `c b` (change of variables `X ↦ c X`; the Haar constants `|c|^{±n}` cancel).
* `jHat_smul`: with `jHat_scale` (`ĵ_{c b}(O, ·) = ĵ_b(c O, ·)`) this gives (1.8.5).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped Pointwise

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- `|c|_F^{n/2}`, as a nonnegative real. -/
def absFHalfPow (c : F) (n : ℕ) : NNReal :=
  ⟨Real.sqrt (absF c ^ n), Real.sqrt_nonneg _⟩

theorem absFHalfPow_coe (c : F) (n : ℕ) : (absFHalfPow c n : ℝ) = Real.sqrt (absF c ^ n) := rfl

theorem absFHalfPow_ne_zero {c : F} (hc : c ≠ 0) (n : ℕ) : absFHalfPow c n ≠ 0 := by
  intro h
  have h' : Real.sqrt (absF c ^ n) = 0 := congrArg NNReal.toReal h
  rw [Real.sqrt_eq_zero (pow_nonneg (absF_nonneg _) _)] at h'
  exact (pow_pos (absF_pos hc) n).ne' h'

theorem absFHalfPow_sq (c : F) (n : ℕ) :
    (absFHalfPow c n : ℝ) * absFHalfPow c n = absF c ^ n := by
  rw [absFHalfPow_coe, Real.mul_self_sqrt (pow_nonneg (absF_nonneg _) _)]

theorem absF_inv_mul {c : F} (hc : c ≠ 0) : absF c⁻¹ * absF c = 1 := by
  rw [← absF_mul, inv_mul_cancel₀ hc, absF_one]

/-! ## Haar measures under scalar multiplication -/

section HaarScale

variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V]

/-- `μ(c • S) = |c|_F^{dim V} μ(S)` for a Haar measure on a finite-dimensional `F`-vector space
with its module topology (`addHaar_smul_absF`, transported from `F^n`). -/
theorem addHaar_smul_absF_of_isModuleTopology (μ : Measure V) [μ.IsAddHaarMeasure] {c : F}
    (hc : c ≠ 0) (S : Set V) :
    μ (c • S) = ENNReal.ofReal (absF c ^ Module.finrank F V) * μ S := by
  haveI := IsModuleTopology.isTopologicalAddGroup F V
  set n := Module.finrank F V
  letI : MeasurableSpace (Fin n → F) := borel _
  haveI : BorelSpace (Fin n → F) := ⟨rfl⟩
  let e : V ≃ₗ[F] (Fin n → F) := (Module.finBasis F V).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he' : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : V ≃ₜ (Fin n → F) := ⟨e.toEquiv, he, he'⟩
  let em := h.toMeasurableEquiv
  have hem : (em : V → Fin n → F) = e := rfl
  haveI : (μ.map em).IsAddHaarMeasure := by
    rw [hem]; exact e.toAddEquiv.isAddHaarMeasure_map μ he he'
  have key : ∀ T : Set V, μ T = (μ.map em) (e '' T) := fun T => by
    rw [em.map_apply, hem, Set.preimage_image_eq T e.injective]
  have himg : e '' (c • S) = c • (e '' S) := image_smul_set e c S
  rw [key, key S, himg, addHaar_smul_absF _ hc, Module.finrank_fin_fun]

/-- `μ.map (c • ·) = |c|_F^{-dim V} μ`. -/
theorem map_smul_addHaar (μ : Measure V) [μ.IsAddHaarMeasure] {c : F} (hc : c ≠ 0) :
    μ.map (fun Y : V => c • Y) =
      Real.toNNReal ((absF c ^ Module.finrank F V)⁻¹) • μ := by
  haveI := IsModuleTopology.isTopologicalAddGroup F V
  haveI : ContinuousConstSMul F V := inferInstance
  have hinv : absF c⁻¹ ^ Module.finrank F V = (absF c ^ Module.finrank F V)⁻¹ := by
    rw [← inv_pow]
    congr 1
    exact eq_inv_of_mul_eq_one_left (absF_inv_mul hc)
  ext S hS
  rw [Measure.map_apply (continuous_const_smul c).measurable hS, Set.preimage_smul₀ hc,
    addHaar_smul_absF_of_isModuleTopology μ (inv_ne_zero hc), Measure.smul_apply, hinv,
    ENNReal.smul_def, smul_eq_mul, ENNReal.ofReal]

/-- **Change of variables `Y ↦ c Y`**: `∫ g(c Y) dμ(Y) = |c|_F^{-dim V} ∫ g dμ`. -/
theorem integral_comp_smul_absF (μ : Measure V) [μ.IsAddHaarMeasure] {c : F} (hc : c ≠ 0)
    (g : V → ℂ) :
    ∫ Y, g (c • Y) ∂μ = (((absF c ^ Module.finrank F V)⁻¹ : ℝ) : ℂ) * ∫ Y, g Y ∂μ := by
  haveI := IsModuleTopology.isTopologicalAddGroup F V
  let h : V ≃ₜ V := Homeomorph.smulOfNeZero c hc
  let em := h.toMeasurableEquiv
  have hem : (em : V → V) = fun Y => c • Y := rfl
  have := integral_map_equiv em g (μ := μ)
  rw [hem, map_smul_addHaar μ hc, integral_smul_nnreal_measure, NNReal.smul_def,
    Real.coe_toNNReal _ (inv_nonneg.mpr (pow_nonneg (absF_nonneg _) _)),
    Complex.real_smul] at this
  exact this.symm

/-! ## Self-dual measures of a rescaled form -/

/-- **`|c|^{n/2} μ` is self-dual for `c B`** when `μ` is self-dual for `B`: the Fourier transform
for `(|c|^{n/2} μ, c B)` is `|c|^{n/2} f̂(c ·)`, and the inversion integral acquires
`|c|^{n/2} · |c|^{n/2} · |c|^{-n} = 1` (`integral_comp_smul_absF`). -/
theorem IsSelfDual.smul {B : LinearMap.BilinForm F V} {ψ : NontrivialAddChar F} {μ : Measure V}
    (hμ : IsSelfDual μ B ψ) {c : F} (hc : c ≠ 0) :
    IsSelfDual (absFHalfPow c (Module.finrank F V) • μ) (c • B) ψ := by
  haveI := hμ.1
  set κ := absFHalfPow c (Module.finrank F V)
  refine ⟨?_, fun f hf Z => ?_⟩
  · haveI := IsModuleTopology.isTopologicalAddGroup F V
    exact Measure.IsAddHaarMeasure.nnreal_smul μ (absFHalfPow_ne_zero hc _)
  have hfour : ∀ Y, fourierWRT (κ • μ) (c • B) ψ f Y =
      ((κ : ℝ) : ℂ) * fourierWRT μ B ψ f (c • Y) := fun Y => by
    unfold fourierWRT
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    simp [LinearMap.smul_apply, map_smul]
  have hB : ∀ Y, (c • B) Z Y = B Z (c • Y) := fun Y => by simp [map_smul]
  have hinv := hμ.2 f hf Z
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  simp only [hfour, hB, mul_assoc]
  rw [integral_const_mul,
    integral_comp_smul_absF μ hc (fun W => fourierWRT μ B ψ f W * ψ (-(B Z W))), hinv,
    ← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, absFHalfPow_sq, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (pow_pos (absF_pos hc) _).ne', Complex.ofReal_one, one_mul]

/-- **The self-dual measure of `c B` is `|c|_F^{dim V / 2}` times that of `B`** (both `0` when
none exists). -/
theorem selfDualMeasure_smul (B : LinearMap.BilinForm F V) (ψ : NontrivialAddChar F) {c : F}
    (hc : c ≠ 0) :
    selfDualMeasure (c • B) ψ = absFHalfPow c (Module.finrank F V) • selfDualMeasure B ψ := by
  unfold selfDualMeasure
  by_cases h : ∃ μ, IsSelfDual μ B ψ
  · have h' : ∃ μ, IsSelfDual μ (c • B) ψ := ⟨_, h.choose_spec.smul hc⟩
    rw [dite_eq_left h, dite_eq_left h']
    exact isSelfDual_unique h'.choose_spec (h.choose_spec.smul hc)
  · have h' : ¬ ∃ μ, IsSelfDual μ (c • B) ψ := by
      rintro ⟨μ, hμ⟩
      refine h ⟨absFHalfPow c⁻¹ (Module.finrank F V) • μ, ?_⟩
      have := hμ.smul (inv_ne_zero hc)
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    rw [dite_eq_right h, dite_eq_right h', smul_zero]

end HaarScale

/-! ## Orbit measures and `ĵ` for the rescaled form `c b` -/

section OrbitScale

variable {A : Type*} [Ring A] [Algebra F A] [TopologicalSpace A] [Module.Finite F A]
  [IsModuleTopology F A]
variable {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A} {b : LinearMap.BilinForm F A}

/-- `dim ker(ad X)|_𝔤 = dim 𝔤_X` for `X ∈ 𝔤`. -/
theorem finrank_ker_ad_eq (X : ↥𝔤) :
    Module.finrank F ↥(LinearMap.ker (LieAlgebra.ad F ↥𝔤 X)) =
      Module.finrank F ↥(lieCentralizer 𝔤 (X : A)) := by
  have hle : (lieCentralizer 𝔤 (X : A)).toSubmodule ≤ 𝔤.toSubmodule :=
    fun Z hZ => (mem_lieCentralizer.mp hZ).1
  have key : ∀ Z : ↥𝔤, ((⁅X, Z⁆ : ↥𝔤) : A) = (X : A) * Z - Z * X := fun Z => by
    simp [Ring.lie_def]
  have heq : LinearMap.ker (LieAlgebra.ad F ↥𝔤 X) =
      (lieCentralizer 𝔤 (X : A)).toSubmodule.comap 𝔤.toSubmodule.subtype := by
    ext Z
    rw [LinearMap.mem_ker, Submodule.mem_comap, LieSubalgebra.mem_toSubmodule,
      mem_lieCentralizer, LieAlgebra.ad_apply]
    constructor
    · intro h
      exact ⟨Z.2, sub_eq_zero.mp ((key Z).symm.trans (congrArg Subtype.val h))⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext (by rw [key]; exact sub_eq_zero.mpr h)
  rw [heq]
  exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq

theorem restrictForm_smul (c : F) : restrictForm 𝔤 (c • b) = c • restrictForm 𝔤 b := rfl

theorem kirillovForm_smul (c : F) (X : ↥𝔤) :
    kirillovForm 𝔤 (c • b) X = c • kirillovForm 𝔤 b X := rfl

/-- **Orbit measures for `c b`**: `|c|_F^{k/2} μ` is an orbit measure of `O` for `c b` iff `μ` is
one for `b`, where `k = dim 𝔤 − dim 𝔤_X` for `X ∈ O` (the dimension of the orbit): the Kirillov
form of `c b` is `c` times that of `b`, and its self-dual measure on a complement `C` of `𝔤_X`
(`dim C = k`) is `|c|_F^{k/2}` times (`selfDualMeasure_smul`). -/
theorem isOrbitMeasure_smul_iff (ψ : NontrivialAddChar F) {c : F} (hc : c ≠ 0)
    (O : NilOrbit G 𝔤) (k : ℕ)
    (hk : ∀ X ∈ nilOrbitSet O,
      Module.finrank F ↥(lieCentralizer 𝔤 (X : A)) + k = Module.finrank F ↥𝔤)
    (μ : Measure ↥𝔤) :
    IsOrbitMeasure G 𝔤 (c • b) ψ O (absFHalfPow c k • μ) ↔ IsOrbitMeasure G 𝔤 b ψ O μ := by
  haveI := isModuleTopology_lieSubalgebra 𝔤
  haveI := isTopologicalAddGroup_lieSubalgebra 𝔤
  haveI := t2Space_of_moduleTopology F A
  set κ := absFHalfPow c k
  have hκ : (κ : ENNReal) ≠ 0 := by exact_mod_cast absFHalfPow_ne_zero hc k
  have hsm : ∀ T, (κ • μ) T = (κ : ENNReal) * μ T := fun T => by
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hcancel : ∀ a a' : ENNReal, (κ : ENNReal) * a = (κ : ENNReal) * a' ↔ a = a' :=
    fun a a' => ⟨fun h => (ENNReal.mul_right_inj hκ ENNReal.coe_ne_top).mp h,
      fun h => by rw [h]⟩
  -- the self-dual measures on the chart
  have hsd : ∀ X ∈ nilOrbitSet O, ∀ C : Submodule F ↥𝔤,
      IsCompl C (LinearMap.ker (LieAlgebra.ad F ↥𝔤 X)) →
      selfDualMeasure ((kirillovForm 𝔤 (c • b) X).compl₁₂ C.subtype C.subtype) ψ =
        κ • selfDualMeasure ((kirillovForm 𝔤 b X).compl₁₂ C.subtype C.subtype) ψ := by
    intro X hX C hC
    haveI : IsModuleTopology F ↥C := isModuleTopologyOfFiniteDimensional (𝕜 := F)
    have hdim : Module.finrank F ↥C = k := by
      have h1 := Submodule.finrank_add_eq_of_isCompl hC
      have h2 := hk X hX
      rw [← finrank_ker_ad_eq] at h2
      omega
    have : (kirillovForm 𝔤 (c • b) X).compl₁₂ C.subtype C.subtype =
        c • (kirillovForm 𝔤 b X).compl₁₂ C.subtype C.subtype := rfl
    rw [this, selfDualMeasure_smul _ ψ hc, hdim]
  unfold IsOrbitMeasure
  refine and_congr ?_ (and_congr ?_ ?_)
  · rw [hsm, mul_eq_zero, or_iff_right hκ]
  · refine forall_congr' fun g => forall_congr' fun _ => forall_congr' fun S =>
      forall_congr' fun _ => ?_
    rw [hsm, hsm]
    exact hcancel _ _
  · refine forall_congr' fun X => forall_congr' fun hX => forall_congr' fun C =>
      forall_congr' fun hC => exists_congr fun U => and_congr Iff.rfl (forall_congr' fun S =>
        forall_congr' fun _ => forall_congr' fun _ => ?_)
    rw [hsm, hsd X hX C hC, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact hcancel _ _

/-- Uniqueness of orbit measures passes from `b` to `c b`. -/
theorem isOrbitMeasure_unique_smul (ψ : NontrivialAddChar F) {c : F} (hc : c ≠ 0)
    (O : NilOrbit G 𝔤)
    (hu : ∀ μ ν, IsOrbitMeasure G 𝔤 b ψ O μ → IsOrbitMeasure G 𝔤 b ψ O ν → μ = ν) (k : ℕ)
    (hk : ∀ X ∈ nilOrbitSet O,
      Module.finrank F ↥(lieCentralizer 𝔤 (X : A)) + k = Module.finrank F ↥𝔤)
    (μ ν : Measure ↥𝔤) (hμ : IsOrbitMeasure G 𝔤 (c • b) ψ O μ)
    (hν : IsOrbitMeasure G 𝔤 (c • b) ψ O ν) : μ = ν := by
  have hκ : absFHalfPow c k ≠ 0 := absFHalfPow_ne_zero hc k
  have key := isOrbitMeasure_smul_iff (G := G) (b := b) ψ hc O k hk
  have hμ' : IsOrbitMeasure G 𝔤 b ψ O ((absFHalfPow c k)⁻¹ • μ) :=
    (key _).mp (by rwa [smul_inv_smul₀ hκ])
  have hν' : IsOrbitMeasure G 𝔤 b ψ O ((absFHalfPow c k)⁻¹ • ν) :=
    (key _).mp (by rwa [smul_inv_smul₀ hκ])
  have := congrArg (fun m : Measure ↥𝔤 => absFHalfPow c k • m) (hu _ _ hμ' hν')
  simpa only [smul_inv_smul₀ hκ] using this

/-- **`μ_O` for `c b` is `|c|_F^{k/2}` times `μ_O` for `b`**, `k = dim O`. -/
theorem orbitMeasure_smul (ψ : NontrivialAddChar F) {c : F} (hc : c ≠ 0)
    (O : NilOrbit G 𝔤)
    (hu : ∀ μ ν, IsOrbitMeasure G 𝔤 b ψ O μ → IsOrbitMeasure G 𝔤 b ψ O ν → μ = ν) (k : ℕ)
    (hk : ∀ X ∈ nilOrbitSet O,
      Module.finrank F ↥(lieCentralizer 𝔤 (X : A)) + k = Module.finrank F ↥𝔤) :
    orbitMeasure G 𝔤 (c • b) ψ O = absFHalfPow c k • orbitMeasure G 𝔤 b ψ O := by
  have key := isOrbitMeasure_smul_iff (G := G) (b := b) ψ hc O k hk
  have hκ : absFHalfPow c k ≠ 0 := absFHalfPow_ne_zero hc k
  unfold orbitMeasure
  by_cases h : ∃ μ, IsOrbitMeasure G 𝔤 b ψ O μ
  · have h' : ∃ μ, IsOrbitMeasure G 𝔤 (c • b) ψ O μ := ⟨_, (key _).mpr h.choose_spec⟩
    rw [dite_eq_left h, dite_eq_left h']
    exact isOrbitMeasure_unique_smul ψ hc O hu k hk _ _ h'.choose_spec ((key _).mpr h.choose_spec)
  · have h' : ¬ ∃ μ, IsOrbitMeasure G 𝔤 (c • b) ψ O μ := by
      rintro ⟨μ, hμ⟩
      refine h ⟨(absFHalfPow c k)⁻¹ • μ, (key _).mp ?_⟩
      rwa [smul_inv_smul₀ hκ]
    rw [dite_eq_right h, dite_eq_right h', smul_zero]

/-- `c X` is regular semisimple iff `X` is, for `c ≠ 0`. -/
theorem isRegularSS_smul_iff {c : F} (hc : c ≠ 0) (X : A) :
    IsRegularSS 𝔤 (c • X) ↔ IsRegularSS 𝔤 X := by
  have hml : LinearMap.mulLeft F (c • X) = c • LinearMap.mulLeft F X :=
    LinearMap.ext fun Y => by simp
  have hcent : lieCentralizer 𝔤 (c • X) = lieCentralizer 𝔤 X := by
    ext Z
    rw [mem_lieCentralizer, mem_lieCentralizer, smul_mul_assoc, mul_smul_comm]
    exact and_congr_right fun _ => ⟨fun h => smul_right_injective A hc h, fun h => by rw [h]⟩
  unfold IsRegularSS IsSS
  rw [hml, Module.End.IsSemisimple_smul_iff hc, hcent]

/-- The Fourier transform for `c b` is `|c|_F^{dim 𝔤 / 2} f̂_b(c ·)`. -/
theorem fourierLie_smul (ψ : NontrivialAddChar F) {c : F} (hc : c ≠ 0) (f : ↥𝔤 → ℂ) (Y : ↥𝔤) :
    fourierLie 𝔤 (c • b) ψ f Y =
      ((absFHalfPow c (Module.finrank F ↥𝔤) : ℝ) : ℂ) * fourierLie 𝔤 b ψ f (c • Y) := by
  haveI := isModuleTopology_lieSubalgebra 𝔤
  unfold fourierLie selfDualHaar fourierWRT
  rw [restrictForm_smul, selfDualMeasure_smul _ ψ hc, integral_smul_nnreal_measure,
    NNReal.smul_def, Complex.real_smul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp [LinearMap.smul_apply, map_smul]

/-- `(f(c⁻¹ ·))^(Z) = |c|_F^{dim 𝔤} f̂(c Z)` (change of variables). -/
theorem fourierLie_comp_smul_inv (ψ : NontrivialAddChar F) {c : F} (hc : c ≠ 0)
    [(selfDualHaar 𝔤 b ψ).IsAddHaarMeasure] (f : ↥𝔤 → ℂ) (Z : ↥𝔤) :
    fourierLie 𝔤 b ψ (fun X => f (c⁻¹ • X)) Z =
      ((absF c ^ Module.finrank F ↥𝔤 : ℝ) : ℂ) * fourierLie 𝔤 b ψ f (c • Z) := by
  haveI := isModuleTopology_lieSubalgebra 𝔤
  have hpos : (absF c ^ Module.finrank F ↥𝔤 : ℝ) ≠ 0 := (pow_pos (absF_pos hc) _).ne'
  have h := integral_comp_smul_absF (selfDualHaar 𝔤 b ψ) hc
    (fun X => f (c⁻¹ • X) * ψ (restrictForm 𝔤 b X Z))
  have e : ∀ X : ↥𝔤, restrictForm 𝔤 b (c • X) Z = restrictForm 𝔤 b X (c • Z) := fun X => by
    simp only [map_smul, LinearMap.smul_apply]
  simp only [inv_smul_smul₀ hc, e] at h
  unfold fourierLie fourierWRT
  rw [h, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos, Complex.ofReal_one, one_mul]

theorem restrictForm_smul_nondegenerate {c : F} (hc : c ≠ 0)
    (hnd : (restrictForm 𝔤 b).Nondegenerate) : (restrictForm 𝔤 (c • b)).Nondegenerate := by
  rw [restrictForm_smul]
  refine ⟨fun Y hY => hnd.1 Y fun Z => ?_, fun Y hY => hnd.2 Y fun Z => ?_⟩
  · have := hY Z
    rwa [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_zero, or_iff_right hc] at this
  · have := hY Z
    rwa [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_zero, or_iff_right hc] at this

/-- **Representatives of `f ↦ μ_O(f̂)` for `c b`**: if `j` represents it for `b`, then
`|c|_F^{k/2} j(c ·)` represents it for `c b` (`k = dim O`). Change of variables `X ↦ c X`: the
constants `|c|^{n/2}` of the self-dual measure (`n = dim 𝔤`) appear on both sides, and the factors
`|c|^{∓n}` from `X ↦ c X` and from `(f(c⁻¹ ·))^ = |c|^n f̂(c ·)` cancel. -/
theorem isJHat_smul (ψ : NontrivialAddChar F) {c : F} (hc : c ≠ 0)
    (hnd : (restrictForm 𝔤 b).Nondegenerate)
    (O : NilOrbit G 𝔤)
    (hu : ∀ μ ν, IsOrbitMeasure G 𝔤 b ψ O μ → IsOrbitMeasure G 𝔤 b ψ O ν → μ = ν) (k : ℕ)
    (hk : ∀ X ∈ nilOrbitSet O,
      Module.finrank F ↥(lieCentralizer 𝔤 (X : A)) + k = Module.finrank F ↥𝔤)
    {j : ↥𝔤 → ℂ} (hj : IsJHat G 𝔤 b ψ O j) :
    IsJHat G 𝔤 (c • b) ψ O (fun Y => ((absFHalfPow c k : ℝ) : ℂ) * j (c • Y)) := by
  obtain ⟨_, _, _, _, _⟩ := lieSubalgebra_topology 𝔤
  haveI := t2Space_of_moduleTopology F A
  haveI := isTopologicalAddGroup_lieSubalgebra 𝔤
  haveI := isModuleTopology_lieSubalgebra 𝔤
  have hμ := isSelfDual_selfDualHaar_of_nondegenerate 𝔤 hnd ψ
  haveI := hμ.1
  set N := Module.finrank F ↥𝔤
  set μ := selfDualHaar 𝔤 b ψ
  have hsd : selfDualHaar 𝔤 (c • b) ψ = absFHalfPow c N • μ := by
    unfold μ selfDualHaar; rw [restrictForm_smul, selfDualMeasure_smul _ ψ hc]
  obtain ⟨hcont, hli, hid⟩ := hj
  have hsc : Continuous (fun Y : ↥𝔤 => c • Y) := continuous_const_smul c
  refine ⟨?_, ?_, fun f hf => ?_⟩
  · refine continuousOn_const.mul (hcont.comp hsc.continuousOn fun Y hY => ?_)
    exact (isRegularSS_smul_iff hc (Y : A)).mpr hY
  · rw [hsd]
    have hjc : LocallyIntegrable (fun Y => j (c • Y)) μ := by
      let h : ↥𝔤 ≃ₜ ↥𝔤 := Homeomorph.smulOfNeZero c hc
      have h1 : LocallyIntegrable j (μ.map h) := by
        rw [show (μ.map h) = μ.map (fun Y : ↥𝔤 => c • Y) from rfl, map_smul_addHaar μ hc]
        exact (locallyIntegrable_nnreal_smul_iff (by
          rw [Ne, Real.toNNReal_eq_zero, not_le]
          exact inv_pos.mpr (pow_pos (absF_pos hc) _))).mpr hli
      exact (locallyIntegrable_map_homeomorph h).mp h1
    exact (locallyIntegrable_nnreal_smul_iff (absFHalfPow_ne_zero hc N)).mpr
      (hjc.smul ((absFHalfPow c k : ℝ) : ℂ))
  · have hpos : (absF c ^ N : ℝ) ≠ 0 := (pow_pos (absF_pos hc) _).ne'
    have htest : IsTestFn (fun X : ↥𝔤 => f (c⁻¹ • X)) :=
      ⟨hf.1.comp_continuous (continuous_const_smul _),
        hf.2.comp_homeomorph (Homeomorph.smulOfNeZero c⁻¹ (inv_ne_zero hc))⟩
    have key : ∫ X, f X * j (c • X) ∂μ =
        ∫ Z, fourierLie 𝔤 b ψ f (c • Z) ∂(orbitMeasure G 𝔤 b ψ O) := by
      have h1 := integral_comp_smul_absF μ hc (fun W => f (c⁻¹ • W) * j W)
      simp only [inv_smul_smul₀ hc] at h1
      rw [h1, ← hid _ htest]
      simp only [fourierLie_comp_smul_inv ψ hc f]
      rw [integral_const_mul, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos,
        Complex.ofReal_one, one_mul]
    rw [orbitMeasure_smul ψ hc O hu k hk, hsd, integral_smul_nnreal_measure,
      integral_smul_nnreal_measure, NNReal.smul_def, NNReal.smul_def, Complex.real_smul,
      Complex.real_smul]
    simp only [fourierLie_smul ψ hc f]
    rw [integral_const_mul, ← key, ← integral_const_mul, ← integral_const_mul,
      ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    ring

/-- **BP (1.8.5): `ĵ(O, c X) = |c|_F^{-dim(O)/2} ĵ(c O, X)`** for `X ∈ 𝔤` regular semisimple and
`c ∈ F^×`, where `dim O = k` (`hk`: `dim 𝔤_Y + k = dim 𝔤` for `Y ∈ O`), under the hypotheses of
`jHat_scale`: `b` nondegenerate on `𝔤`, the regular semisimple set of `𝔤` open, orbit measures for
`b` unique. Beuzart-Plessis, Astérisque 418, (1.8.5), p. 34 (arXiv:1506.01452, p. 40). Proof:
`ĵ_b(c O, X) = ĵ_{c b}(O, X)` (`jHat_scale`) and `ĵ_{c b}(O, X) = |c|^{k/2} ĵ_b(O, c X)`
(`isJHat_smul`; both are `0` when no representative exists). -/
theorem jHat_smul (ψ : NontrivialAddChar F) {c : F} (hc : c ≠ 0)
    (hnd : (restrictForm 𝔤 b).Nondegenerate)
    (hopen : IsOpen {Z : ↥𝔤 | IsRegularSS 𝔤 (Z : A)})
    (hu : ∀ O' μ ν, IsOrbitMeasure G 𝔤 b ψ O' μ → IsOrbitMeasure G 𝔤 b ψ O' ν → μ = ν)
    (O : NilOrbit G 𝔤) (k : ℕ)
    (hk : ∀ X ∈ nilOrbitSet O,
      Module.finrank F ↥(lieCentralizer 𝔤 (X : A)) + k = Module.finrank F ↥𝔤)
    (X : A) (hX : X ∈ 𝔤) (hXr : IsRegularSS 𝔤 X) :
    jHat G 𝔤 b ψ O (c • X) =
      (((absFHalfPow c k : ℝ)⁻¹ : ℝ) : ℂ) *
        jHat G 𝔤 b ψ (nilScale (algebraMap F A c) (Algebra.commutes c)
          (fun Y hY => by rw [← Algebra.smul_def]; exact 𝔤.smul_mem c hY) O) X := by
  obtain ⟨_, _, _, _, _⟩ := lieSubalgebra_topology 𝔤
  haveI := t2Space_of_moduleTopology F A
  haveI := isTopologicalAddGroup_lieSubalgebra 𝔤
  set κ := absFHalfPow c k
  have hκ : ((κ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast absFHalfPow_ne_zero hc k
  -- `ĵ_b(c O, X) = ĵ_{c b}(O, X)`
  let u : Aˣ := Units.map (algebraMap F A).toMonoidHom (Units.mk0 c hc)
  have hu1 : (u : A) = algebraMap F A c := rfl
  have hu2 : ((u⁻¹ : Aˣ) : A) = algebraMap F A c⁻¹ := rfl
  have hscale := jHat_scale (G := G) ψ u (fun a => Algebra.commutes c a)
    (fun Y hY => by rw [hu1, ← Algebra.smul_def]; exact 𝔤.smul_mem c hY)
    (fun Y hY => by rw [hu2, ← Algebra.smul_def]; exact 𝔤.smul_mem c⁻¹ hY)
    (fun Y Z => by rw [hu1, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul,
      LinearMap.smul_apply])
    hnd hopen hu O X hX hXr
  have hform : scaleForm b (u : A) = c • b := LinearMap.ext₂ fun Y Z => by
    rw [scaleForm_apply, hu1, ← Algebra.smul_def, map_smul, LinearMap.smul_apply]
    rfl
  rw [hform] at hscale
  rw [show jHat G 𝔤 b ψ (nilScale (algebraMap F A c) (Algebra.commutes c)
      (fun Y hY => by rw [← Algebra.smul_def]; exact 𝔤.smul_mem c hY) O) X =
      jHat G 𝔤 (c • b) ψ O X from hscale.symm]
  -- `ĵ_{c b}(O, X) = |c|^{k/2} ĵ_b(O, c X)`
  have hnd' := restrictForm_smul_nondegenerate hc hnd
  have hmain : jHat G 𝔤 (c • b) ψ O X = ((κ : ℝ) : ℂ) * jHat G 𝔤 b ψ O (c • X) := by
    unfold jHat
    by_cases h : ∃ j, IsJHat G 𝔤 b ψ O j
    · have hj' := isJHat_smul ψ hc hnd O (hu O) k hk h.choose_spec
      have h' : ∃ j, IsJHat G 𝔤 (c • b) ψ O j := ⟨_, hj'⟩
      rw [dite_eq_left h', dite_eq_left h, dite_eq_left hX, dite_eq_left (𝔤.smul_mem c hX)]
      have hμ := isSelfDual_selfDualHaar_of_nondegenerate 𝔤 hnd' ψ
      haveI := hμ.1
      exact eqOn_of_isJHat hμ h'.choose_spec hj' hopen le_rfl
        (show (⟨X, hX⟩ : ↥𝔤) ∈ {Z : ↥𝔤 | IsRegularSS 𝔤 (Z : A)} from hXr)
    · have h' : ¬ ∃ j, IsJHat G 𝔤 (c • b) ψ O j := by
        rintro ⟨j, hj⟩
        have := isJHat_smul ψ (inv_ne_zero hc) hnd' O
          (isOrbitMeasure_unique_smul ψ hc O (hu O) k hk) k hk hj
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
        exact h ⟨_, this⟩
      rw [dite_eq_right h, dite_eq_right h', mul_zero]
  rw [hmain, ← mul_assoc, Complex.ofReal_inv, inv_mul_cancel₀ hκ, one_mul]


/-- `dim 𝔤_X` is constant on a nilpotent orbit, when `G` normalizes `𝔤`. -/
theorem finrank_lieCentralizer_eq_of_mem_nilOrbitSet
    (hG : ∀ g ∈ G, ∀ Y ∈ 𝔤, (g : A) * Y * (↑g⁻¹ : A) ∈ 𝔤) {O : NilOrbit G 𝔤} {X Y : ↥𝔤}
    (hX : X ∈ nilOrbitSet O) (hY : Y ∈ nilOrbitSet O) :
    Module.finrank F ↥(lieCentralizer 𝔤 (X : A)) =
      Module.finrank F ↥(lieCentralizer 𝔤 (Y : A)) := by
  obtain ⟨hXn, hXO⟩ := hX
  obtain ⟨hYn, hYO⟩ := hY
  obtain ⟨g, hg, h⟩ := Quotient.exact (hYO.trans hXO.symm)
  have h' : (Y : A) = (g⁻¹ : Aˣ) * X * ((g⁻¹)⁻¹ : Aˣ) := by
    rw [inv_inv, ← h]
    simp [mul_assoc]
  rw [h', finrank_lieCentralizer_conj 𝔤 g⁻¹ (hG _ (G.inv_mem hg))
    (fun Z hZ => by simpa using hG g hg Z hZ)]

/-- **BP (1.8.5) with `dim O = dim 𝔤 − dim 𝔤_{X₀}`** for any `X₀ ∈ O`, when `G` normalizes `𝔤`
(`jHat_smul`, the dimension being constant on `O` by
`finrank_lieCentralizer_eq_of_mem_nilOrbitSet`). -/
theorem jHat_smul_of_mem (ψ : NontrivialAddChar F) {c : F} (hc : c ≠ 0)
    (hG : ∀ g ∈ G, ∀ Y ∈ 𝔤, (g : A) * Y * (↑g⁻¹ : A) ∈ 𝔤)
    (hnd : (restrictForm 𝔤 b).Nondegenerate)
    (hopen : IsOpen {Z : ↥𝔤 | IsRegularSS 𝔤 (Z : A)})
    (hu : ∀ O' μ ν, IsOrbitMeasure G 𝔤 b ψ O' μ → IsOrbitMeasure G 𝔤 b ψ O' ν → μ = ν)
    (O : NilOrbit G 𝔤) {X₀ : ↥𝔤} (hX₀ : X₀ ∈ nilOrbitSet O)
    (X : A) (hX : X ∈ 𝔤) (hXr : IsRegularSS 𝔤 X) :
    jHat G 𝔤 b ψ O (c • X) =
      (((absFHalfPow c (Module.finrank F ↥𝔤 -
          Module.finrank F ↥(lieCentralizer 𝔤 (X₀ : A))) : ℝ)⁻¹ : ℝ) : ℂ) *
        jHat G 𝔤 b ψ (nilScale (algebraMap F A c) (Algebra.commutes c)
          (fun Y hY => by rw [← Algebra.smul_def]; exact 𝔤.smul_mem c hY) O) X := by
  refine jHat_smul ψ hc hnd hopen hu O _ (fun Y hY => ?_) X hX hXr
  rw [finrank_lieCentralizer_eq_of_mem_nilOrbitSet hG hY hX₀]
  have : Module.finrank F ↥(lieCentralizer 𝔤 (X₀ : A)) ≤ Module.finrank F ↥𝔤 :=
    Submodule.finrank_mono (show (lieCentralizer 𝔤 (X₀ : A)).toSubmodule ≤ 𝔤.toSubmodule from
      fun Z hZ => (mem_lieCentralizer.mp hZ).1)
  omega

end OrbitScale

end GSpinGGP
