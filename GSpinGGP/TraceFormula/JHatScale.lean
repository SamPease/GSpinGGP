/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.JHatTransport

/-!
# `ĵ(O, ·)` under rescaling of the form by a central unit, and under equal descent data

* `nilOrbitCongr`: for equal pairs `(G, 𝔤) = (G', 𝔤')`, the identification
  `Nil(𝔤) ≃ Nil(𝔤')`, compatible with `ĵ`, `Nil_reg` and the orbits as sets.
* `nilScale`: multiplication by a central unit `c` (preserving `𝔤`) permutes the nilpotent orbits;
  it preserves the regular ones (`nilScale_mem_nilReg_iff`).
* `isOrbitMeasure_scale_iff`: `μ` is the orbit measure of `O` for the form `b(c ·, ·)` iff
  `c_* μ` is the orbit measure of `c O` for `b`: the Kirillov form of `b(c ·, ·)` at `X` is that of
  `b` at `c X` (`c` is central and `b(c Y, Z) = b(Y, c Z)`), and the chart at `c X` is `c` times the
  chart at `X`.
* `jHat_scale`: **`ĵ_{b(c ·, ·)}(O, X) = ĵ_b(c O, X)`** for `X` regular semisimple, when `b` is
  nondegenerate on `𝔤`, the regular set of `𝔤` is open and orbit measures for `b` are unique.  The
  two self-dual measures differ by a constant `κ > 0` (uniqueness of Haar measure), and both sides of
  the identity defining `ĵ` acquire the factor `κ`, so `κ` need not be computed.
-/

noncomputable section

open MeasureTheory Filter Topology

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
  {A : Type*} [Ring A] [Algebra F A] [TopologicalSpace A] [Module.Finite F A] [IsModuleTopology F A]

/-! ## Equal descent data -/

section Congr

variable {G G' : Subgroup Aˣ} {𝔤 𝔤' : LieSubalgebra F A}

/-- For `G = G'` and `𝔤 = 𝔤'`, the identification `Nil(𝔤) ≃ Nil(𝔤')`. -/
def nilOrbitCongr (hG : G = G') (h𝔤 : 𝔤 = 𝔤') : NilOrbit G 𝔤 ≃ NilOrbit G' 𝔤' := by
  subst hG h𝔤
  exact Equiv.refl _

theorem jHat_nilOrbitCongr (hG : G = G') (h𝔤 : 𝔤 = 𝔤') (b : LinearMap.BilinForm F A)
    (ψ : NontrivialAddChar F) (O : NilOrbit G 𝔤) (X : A) :
    jHat G' 𝔤' b ψ (nilOrbitCongr hG h𝔤 O) X = jHat G 𝔤 b ψ O X := by
  subst hG h𝔤
  rfl

theorem nilOrbitCongr_mem_nilReg_iff (hG : G = G') (h𝔤 : 𝔤 = 𝔤') (O : NilOrbit G 𝔤) :
    nilOrbitCongr hG h𝔤 O ∈ NilReg G' 𝔤' ↔ O ∈ NilReg G 𝔤 := by
  subst hG h𝔤
  rfl

theorem exists_mem_nilOrbitSet_nilOrbitCongr_iff (hG : G = G') (h𝔤 : 𝔤 = 𝔤')
    (O : NilOrbit G 𝔤) (P : A → Prop) :
    (∃ Y ∈ nilOrbitSet (nilOrbitCongr hG h𝔤 O), P (Y : A)) ↔ ∃ Y ∈ nilOrbitSet O, P (Y : A) := by
  subst hG h𝔤
  rfl

theorem nilOrbitCongr_mk (hG : G = G') (h𝔤 : 𝔤 = 𝔤') (Y : {X : A // X ∈ 𝔤 ∧ IsNilpotent X}) :
    nilOrbitCongr hG h𝔤 (Quotient.mk _ Y) =
      Quotient.mk (nilSetoid G' 𝔤') ⟨Y.1, h𝔤 ▸ Y.2.1, Y.2.2⟩ := by
  subst hG h𝔤
  rfl

end Congr

/-! ## Rescaling by a central unit -/

section Scale

/-- The form `b(c ·, ·)`. -/
def scaleForm (b : LinearMap.BilinForm F A) (c : A) : LinearMap.BilinForm F A :=
  b.compl₁₂ (LinearMap.mulLeft F c) LinearMap.id

@[simp] theorem scaleForm_apply (b : LinearMap.BilinForm F A) (c X Y : A) :
    scaleForm b c X Y = b (c * X) Y := rfl

variable {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A}

/-- The inverse of a central unit is central. -/
theorem inv_mul_eq_mul_inv_of_central {c : Aˣ} (hc : ∀ a : A, (c : A) * a = a * c) (a : A) :
    ((c⁻¹ : Aˣ) : A) * a = a * ((c⁻¹ : Aˣ) : A) := by
  calc ((c⁻¹ : Aˣ) : A) * a = ((c⁻¹ : Aˣ) : A) * (a * c) * ((c⁻¹ : Aˣ) : A) := by
        rw [mul_assoc, mul_assoc a, Units.mul_inv, mul_one]
    _ = ((c⁻¹ : Aˣ) : A) * (c * a) * ((c⁻¹ : Aˣ) : A) := by rw [hc]
    _ = a * ((c⁻¹ : Aˣ) : A) := by rw [← mul_assoc, Units.inv_mul, one_mul]

theorem isNilpotent_mul_of_central {c : A} (hc : ∀ a : A, c * a = a * c) {Y : A}
    (hY : IsNilpotent Y) : IsNilpotent (c * Y) := by
  obtain ⟨n, hn⟩ := hY
  exact ⟨n, by rw [(show Commute c Y from hc Y).mul_pow, hn, mul_zero]⟩

/-- Multiplication by `c` on `𝔤`, for a unit `c` with `c 𝔤 = 𝔤`. -/
def scaleEquiv (c : Aˣ) (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤)
    (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤) : ↥𝔤 ≃ₗ[F] ↥𝔤 where
  toFun Y := ⟨c * Y, hc𝔤 _ Y.2⟩
  invFun Y := ⟨((c⁻¹ : Aˣ) : A) * Y, hc𝔤' _ Y.2⟩
  map_add' Y Z := Subtype.ext (mul_add _ _ _)
  map_smul' r Y := Subtype.ext (mul_smul_comm r _ _)
  left_inv Y := Subtype.ext (by simp [← mul_assoc])
  right_inv Y := Subtype.ext (by simp [← mul_assoc])

@[simp] theorem coe_scaleEquiv (c : Aˣ) (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤)
    (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤) (Y : ↥𝔤) :
    ((scaleEquiv c hc𝔤 hc𝔤' Y : ↥𝔤) : A) = c * Y := rfl

@[simp] theorem coe_scaleEquiv_symm (c : Aˣ) (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤)
    (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤) (Y : ↥𝔤) :
    (((scaleEquiv c hc𝔤 hc𝔤').symm Y : ↥𝔤) : A) = ((c⁻¹ : Aˣ) : A) * Y := rfl

/-- `G`-conjugation commutes with multiplication by a central `c`. -/
theorem conj_mul_of_central {c : A} (hc : ∀ a : A, c * a = a * c) (g : Aˣ) (X : A) :
    (g : A) * (c * X) * (↑g⁻¹ : A) = c * ((g : A) * X * (↑g⁻¹ : A)) := by
  rw [← mul_assoc (g : A), ← hc (g : A)]
  simp only [mul_assoc]

/-- **Multiplication by a central unit `c` on nilpotent orbits**, `O ↦ c O`. -/
def nilScale (c : A) (hc : ∀ a : A, c * a = a * c) (hc𝔤 : ∀ Y ∈ 𝔤, c * Y ∈ 𝔤) :
    NilOrbit G 𝔤 → NilOrbit G 𝔤 :=
  Quotient.map (fun Y => ⟨c * Y.1, hc𝔤 _ Y.2.1, isNilpotent_mul_of_central hc Y.2.2⟩)
    fun X Y ⟨g, hg, h⟩ => ⟨g, hg, by
      change (g : A) * (c * X.1) * (↑g⁻¹ : A) = c * Y.1
      rw [conj_mul_of_central hc, h]⟩

theorem nilScale_mk (c : A) (hc : ∀ a : A, c * a = a * c) (hc𝔤 : ∀ Y ∈ 𝔤, c * Y ∈ 𝔤)
    (Y : {X : A // X ∈ 𝔤 ∧ IsNilpotent X}) :
    nilScale (G := G) c hc hc𝔤 (Quotient.mk _ Y) =
      Quotient.mk _ ⟨c * Y.1, hc𝔤 _ Y.2.1, isNilpotent_mul_of_central hc Y.2.2⟩ := rfl

/-- `c⁻¹ (c O) = O`. -/
theorem nilScale_inv_nilScale (c : Aˣ) (hc : ∀ a : A, (c : A) * a = a * c)
    (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤) (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤)
    (O : NilOrbit G 𝔤) :
    nilScale ((c⁻¹ : Aˣ) : A) (inv_mul_eq_mul_inv_of_central hc) hc𝔤'
      (nilScale (c : A) hc hc𝔤 O) =
      O := by
  induction O using Quotient.inductionOn with | h Y => ?_
  rw [nilScale_mk, nilScale_mk]
  exact congrArg (Quotient.mk _) (Subtype.ext (by simp [← mul_assoc]))

/-- `c (c⁻¹ O) = O`. -/
theorem nilScale_nilScale_inv (c : Aˣ) (hc : ∀ a : A, (c : A) * a = a * c)
    (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤) (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤)
    (O : NilOrbit G 𝔤) :
    nilScale (c : A) hc hc𝔤
      (nilScale ((c⁻¹ : Aˣ) : A) (inv_mul_eq_mul_inv_of_central hc) hc𝔤' O) =
      O := by
  induction O using Quotient.inductionOn with | h Y => ?_
  rw [nilScale_mk, nilScale_mk]
  exact congrArg (Quotient.mk _) (Subtype.ext (by simp [← mul_assoc]))

/-- `O ↦ c O` as a bijection of `Nil(𝔤)`. -/
def nilScaleEquiv (c : Aˣ) (hc : ∀ a : A, (c : A) * a = a * c)
    (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤) (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤) :
    NilOrbit G 𝔤 ≃ NilOrbit G 𝔤 where
  toFun := nilScale (c : A) hc hc𝔤
  invFun := nilScale ((c⁻¹ : Aˣ) : A) (inv_mul_eq_mul_inv_of_central hc) hc𝔤'
  left_inv O := nilScale_inv_nilScale (G := G) c hc hc𝔤 hc𝔤' O
  right_inv O := nilScale_nilScale_inv (G := G) c hc hc𝔤 hc𝔤' O

theorem nilScaleEquiv_apply (c : Aˣ) (hc : ∀ a : A, (c : A) * a = a * c)
    (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤) (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤)
    (O : NilOrbit G 𝔤) : nilScaleEquiv c hc hc𝔤 hc𝔤' O = nilScale (c : A) hc hc𝔤 O := rfl

/-- `c Y ∈ c O` iff `Y ∈ O`. -/
theorem scaleEquiv_mem_nilOrbitSet_iff (c : Aˣ) (hc : ∀ a : A, (c : A) * a = a * c)
    (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤) (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤)
    (O : NilOrbit G 𝔤) (Y : ↥𝔤) :
    scaleEquiv c hc𝔤 hc𝔤' Y ∈ nilOrbitSet (nilScale (c : A) hc hc𝔤 O) ↔ Y ∈ nilOrbitSet O := by
  constructor
  · rintro ⟨hn, hq⟩
    have hn' : IsNilpotent (Y : A) := by
      have := isNilpotent_mul_of_central (inv_mul_eq_mul_inv_of_central hc) hn
      simpa [← mul_assoc] using this
    refine ⟨hn', ?_⟩
    have := congrArg (nilScale ((c⁻¹ : Aˣ) : A) (inv_mul_eq_mul_inv_of_central hc) hc𝔤') hq
    rw [nilScale_inv_nilScale, nilScale_mk] at this
    rw [← this]
    exact congrArg (Quotient.mk _) (Subtype.ext (by simp [← mul_assoc]))
  · rintro ⟨hn, rfl⟩
    exact ⟨isNilpotent_mul_of_central hc hn, rfl⟩

/-- The orbits of `c O` are `c` times those of `O`. -/
theorem exists_mem_nilOrbitSet_nilScale_iff (c : Aˣ) (hc : ∀ a : A, (c : A) * a = a * c)
    (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤) (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤)
    (O : NilOrbit G 𝔤) (P : A → Prop) :
    (∃ Y ∈ nilOrbitSet (nilScale (c : A) hc hc𝔤 O), P (Y : A)) ↔
      ∃ Y ∈ nilOrbitSet O, P ((c : A) * Y) := by
  constructor
  · rintro ⟨Y, hY, hP⟩
    refine ⟨(scaleEquiv c hc𝔤 hc𝔤').symm Y, ?_, ?_⟩
    · rw [← scaleEquiv_mem_nilOrbitSet_iff c hc hc𝔤 hc𝔤', LinearEquiv.apply_symm_apply]
      exact hY
    · simpa [← mul_assoc] using hP
  · rintro ⟨Y, hY, hP⟩
    exact ⟨scaleEquiv c hc𝔤 hc𝔤' Y, (scaleEquiv_mem_nilOrbitSet_iff c hc hc𝔤 hc𝔤' O Y).mpr hY,
      hP⟩

/-- `𝔤_{c Y} = 𝔤_Y` for a central unit `c`. -/
theorem lieCentralizer_mul_of_central (c : Aˣ) (hc : ∀ a : A, (c : A) * a = a * c) (Y : A) :
    lieCentralizer 𝔤 ((c : A) * Y) = lieCentralizer 𝔤 Y := by
  ext Z
  rw [mem_lieCentralizer, mem_lieCentralizer]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · have e1 : (c : A) * Y * Z = c * (Y * Z) := mul_assoc _ _ _
    have e2 : Z * ((c : A) * Y) = c * (Z * Y) := by rw [← mul_assoc, ← hc Z, mul_assoc]
    rw [e1, e2] at h
    exact (Units.mul_right_inj c).mp h
  · rw [mul_assoc, h, ← mul_assoc, hc Z, mul_assoc]

/-- Multiplication by a central unit preserves the regular nilpotent orbits. -/
theorem nilScale_mem_nilReg_iff (c : Aˣ) (hc : ∀ a : A, (c : A) * a = a * c)
    (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤) (hG : ∀ g ∈ G, ∀ Y ∈ 𝔤, (g : A) * Y * (↑g⁻¹ : A) ∈ 𝔤)
    (O : NilOrbit G 𝔤) : nilScale (c : A) hc hc𝔤 O ∈ NilReg G 𝔤 ↔ O ∈ NilReg G 𝔤 := by
  induction O using Quotient.inductionOn with | h Y => ?_
  rw [nilScale_mk]
  refine (mk_mem_nilReg_iff hG _).trans (Iff.trans ?_ (mk_mem_nilReg_iff hG Y).symm)
  unfold IsRegularNil
  rw [lieCentralizer_mul_of_central c hc]
  exact ⟨fun h => ⟨Y.2.1, Y.2.2, h.2.2⟩, fun h => ⟨hc𝔤 _ Y.2.1,
    isNilpotent_mul_of_central hc Y.2.2, h.2.2⟩⟩

end Scale

/-! ## `ĵ` under rescaling of the form -/

section ScaleMeasure

variable {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A} {b : LinearMap.BilinForm F A}

theorem locallyIntegrable_nnreal_smul_iff {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {f : X → ℂ} {μ : Measure X} {κ : NNReal} (hκ : κ ≠ 0) :
    LocallyIntegrable f (κ • μ) ↔ LocallyIntegrable f μ := by
  have e : κ • μ = (κ : ENNReal) • μ := by
    ext s _
    simp
  rw [e]
  have h1 : (κ : ENNReal) ≠ 0 := by exact_mod_cast hκ
  unfold LocallyIntegrable IntegrableAtFilter IntegrableOn
  simp only [Measure.restrict_smul, integrable_smul_measure h1 ENNReal.coe_ne_top]

theorem continuous_scaleEquiv (c : Aˣ) (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤)
    (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤) : Continuous (scaleEquiv c hc𝔤 hc𝔤') := by
  haveI := isModuleTopology_lieSubalgebra 𝔤
  haveI : ContinuousAdd ↥𝔤 := IsModuleTopology.toContinuousAdd F _
  exact IsModuleTopology.continuous_of_linearMap (scaleEquiv c hc𝔤 hc𝔤').toLinearMap

theorem continuous_scaleEquiv_symm (c : Aˣ) (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤)
    (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤) :
    Continuous (scaleEquiv c hc𝔤 hc𝔤').symm := by
  haveI := isModuleTopology_lieSubalgebra 𝔤
  haveI : ContinuousAdd ↥𝔤 := IsModuleTopology.toContinuousAdd F _
  exact IsModuleTopology.continuous_of_linearMap (scaleEquiv c hc𝔤 hc𝔤').symm.toLinearMap

/-- `e^Y (c X) e^{-Y} = c e^Y X e^{-Y}` for central `c`. -/
theorem orbitMap_mul_of_central {c : A} (hc : ∀ a : A, c * a = a * c) (X Y : A) :
    orbitMap F (c * X) Y = c * orbitMap F X Y := by
  unfold orbitMap
  rw [← mul_assoc (expA F Y), ← hc (expA F Y)]
  simp only [mul_assoc]

/-- `[c X, Z] = c [X, Z]` for central `c`. -/
theorem scaleEquiv_lie (c : Aˣ) (hc : ∀ a : A, (c : A) * a = a * c)
    (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤) (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤) (X Z : ↥𝔤) :
    (⁅scaleEquiv c hc𝔤 hc𝔤' X, Z⁆ : ↥𝔤) = scaleEquiv c hc𝔤 hc𝔤' ⁅X, Z⁆ := by
  apply Subtype.ext
  simp only [LieSubalgebra.coe_bracket, Ring.lie_def, coe_scaleEquiv]
  rw [mul_sub, mul_assoc, ← mul_assoc (Z : A), ← hc (Z : A), mul_assoc]

/-- `ad(c X) = c ad(X)` on `𝔤`, so the centralizers agree. -/
theorem ker_ad_scaleEquiv (c : Aˣ) (hc : ∀ a : A, (c : A) * a = a * c)
    (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤) (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤) (X : ↥𝔤) :
    LinearMap.ker (LieAlgebra.ad F ↥𝔤 (scaleEquiv c hc𝔤 hc𝔤' X)) =
      LinearMap.ker (LieAlgebra.ad F ↥𝔤 X) := by
  ext Z
  simp only [LinearMap.mem_ker, LieAlgebra.ad_apply]
  rw [scaleEquiv_lie c hc, LinearEquiv.map_eq_zero_iff]

/-- The Kirillov form of `b` at `c X` is that of `b(c ·, ·)` at `X`. -/
theorem kirillovForm_scaleEquiv (c : Aˣ) (hc : ∀ a : A, (c : A) * a = a * c)
    (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤) (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤)
    (hb : ∀ Y Z : A, b ((c : A) * Y) Z = b Y ((c : A) * Z)) (X : ↥𝔤) :
    kirillovForm 𝔤 b (scaleEquiv c hc𝔤 hc𝔤' X) = kirillovForm 𝔤 (scaleForm b c) X := by
  refine LinearMap.ext₂ fun Y Z => ?_
  simp only [kirillovForm, restrictForm, LinearMap.compl₂_apply, LinearMap.compl₁₂_apply,
    LieAlgebra.ad_apply, scaleForm_apply]
  rw [hb, scaleEquiv_lie c hc]
  rfl

/-- **Orbit measures under rescaling of the form**: `c_* μ` is an orbit measure of `c O` for `b`
iff `μ` is an orbit measure of `O` for `b(c ·, ·)` (`c` a central unit with `c 𝔤 = 𝔤` and
`b(c Y, Z) = b(Y, c Z)`). -/
theorem isOrbitMeasure_scale_iff (ψ : NontrivialAddChar F) (c : Aˣ)
    (hc : ∀ a : A, (c : A) * a = a * c)
    (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤) (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤)
    (hb : ∀ Y Z : A, b ((c : A) * Y) Z = b Y ((c : A) * Z)) (O : NilOrbit G 𝔤)
    (μ : Measure ↥𝔤) :
    IsOrbitMeasure G 𝔤 b ψ (nilScale (c : A) hc hc𝔤 O) (μ.map (scaleEquiv c hc𝔤 hc𝔤')) ↔
      IsOrbitMeasure G 𝔤 (scaleForm b c) ψ O μ := by
  haveI := t2Space_of_moduleTopology F A
  haveI := isModuleTopology_lieSubalgebra 𝔤
  haveI := isTopologicalAddGroup_lieSubalgebra 𝔤
  set e := scaleEquiv c hc𝔤 hc𝔤' with he_def
  let h : ↥𝔤 ≃ₜ ↥𝔤 :=
    ⟨e.toEquiv, continuous_scaleEquiv c hc𝔤 hc𝔤', continuous_scaleEquiv_symm c hc𝔤 hc𝔤'⟩
  let em := h.toMeasurableEquiv
  have hem : (em : ↥𝔤 → ↥𝔤) = e := rfl
  have hmap : ∀ T, (μ.map e) T = μ (e ⁻¹' T) := fun T => by
    rw [← hem]; exact em.map_apply T
  have hnil : e ⁻¹' nilOrbitSet (nilScale (c : A) hc hc𝔤 O) = nilOrbitSet O :=
    Set.ext fun X => scaleEquiv_mem_nilOrbitSet_iff c hc hc𝔤 hc𝔤' O X
  -- conjugation commutes with `e`
  have hconj : ∀ (g : Aˣ) (S : Set ↥𝔤), e ⁻¹' (Subtype.val ⁻¹' (conjAd F g ⁻¹' (Subtype.val '' S)))
      = Subtype.val ⁻¹' (conjAd F g ⁻¹' (Subtype.val '' (e ⁻¹' S))) := by
    intro g S
    ext Z
    simp only [Set.mem_preimage, Set.mem_image]
    have hcz : conjAd F g ((e Z : ↥𝔤) : A) = (c : A) * conjAd F g (Z : A) :=
      conj_mul_of_central hc g _
    rw [hcz]
    constructor
    · rintro ⟨s, hs, hse⟩
      refine ⟨e.symm s, by rwa [LinearEquiv.apply_symm_apply], ?_⟩
      rw [coe_scaleEquiv_symm, hse, ← mul_assoc, Units.inv_mul, one_mul]
    · rintro ⟨w, hw, hwe⟩
      exact ⟨e w, hw, by rw [coe_scaleEquiv, hwe]⟩
  -- charts: `e⁻¹` of the chart at `c X` is the chart at `X`
  have hchart : ∀ (X : ↥𝔤) (C : Submodule F ↥𝔤) (S : Set ↥C),
      e ⁻¹' (Subtype.val ⁻¹' ((fun Y : ↥C ↦ orbitMap F ((e X : ↥𝔤) : A) ((Y : ↥𝔤) : A)) '' S)) =
        Subtype.val ⁻¹' ((fun Y : ↥C ↦ orbitMap F (X : A) ((Y : ↥𝔤) : A)) '' S) := by
    intro X C S
    ext Z
    simp only [Set.mem_preimage, Set.mem_image, he_def, coe_scaleEquiv,
      orbitMap_mul_of_central hc]
    refine exists_congr fun Y => and_congr_right fun _ => ⟨fun h => ?_, fun h => by rw [h]⟩
    exact (Units.mul_right_inj c).mp h
  unfold IsOrbitMeasure
  rw [hmap, Set.preimage_compl, hnil]
  refine and_congr Iff.rfl (and_congr ⟨fun h2' => ?_, fun h2 => ?_⟩ ⟨fun h3' => ?_, fun h3 => ?_⟩)
  · intro g hg S hS
    have hS' : MeasurableSet (e.symm ⁻¹' S) := hS.preimage em.symm.measurable
    have hpre : e ⁻¹' (e.symm ⁻¹' S) = S := by ext; simp
    have := h2' g hg _ hS'
    rwa [hmap, hmap, hconj, hpre] at this
  · intro g hg S hS
    rw [hmap, hmap, hconj]
    exact h2 g hg _ (hS.preimage em.measurable)
  · intro X hX C hC
    obtain ⟨U, hU, hUS⟩ := h3' (e X) ((scaleEquiv_mem_nilOrbitSet_iff c hc hc𝔤 hc𝔤' O X).mpr hX)
      C (by rwa [ker_ad_scaleEquiv c hc hc𝔤 hc𝔤'])
    refine ⟨U, hU, fun S hS hSU => ?_⟩
    have := hUS S hS hSU
    rwa [hmap, hchart, kirillovForm_scaleEquiv c hc hc𝔤 hc𝔤' hb] at this
  · intro X' hX' C hC
    obtain ⟨X, rfl⟩ := e.surjective X'
    rw [ker_ad_scaleEquiv c hc hc𝔤 hc𝔤'] at hC
    obtain ⟨U, hU, hUS⟩ := h3 X ((scaleEquiv_mem_nilOrbitSet_iff c hc hc𝔤 hc𝔤' O X).mp hX') C hC
    refine ⟨U, hU, fun S hS hSU => ?_⟩
    rw [hmap, hchart, kirillovForm_scaleEquiv c hc hc𝔤 hc𝔤' hb]
    exact hUS S hS hSU

/-- **The orbit measures correspond under rescaling**, when orbit measures for `b` are unique. -/
theorem orbitMeasure_scale (ψ : NontrivialAddChar F) (c : Aˣ)
    (hc : ∀ a : A, (c : A) * a = a * c)
    (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤) (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤)
    (hb : ∀ Y Z : A, b ((c : A) * Y) Z = b Y ((c : A) * Z))
    (hu : ∀ O' μ ν, IsOrbitMeasure G 𝔤 b ψ O' μ → IsOrbitMeasure G 𝔤 b ψ O' ν → μ = ν)
    (O : NilOrbit G 𝔤) :
    orbitMeasure G 𝔤 b ψ (nilScale (c : A) hc hc𝔤 O) =
      (orbitMeasure G 𝔤 (scaleForm b c) ψ O).map (scaleEquiv c hc𝔤 hc𝔤') := by
  have key := isOrbitMeasure_scale_iff (G := G) ψ c hc hc𝔤 hc𝔤' hb O
  have hc1 := continuous_scaleEquiv c hc𝔤 hc𝔤'
  have hc2 := continuous_scaleEquiv_symm c hc𝔤 hc𝔤'
  unfold orbitMeasure
  by_cases h : ∃ μ, IsOrbitMeasure G 𝔤 (scaleForm b c) ψ O μ
  · have h' : ∃ μ, IsOrbitMeasure G 𝔤 b ψ (nilScale (c : A) hc hc𝔤 O) μ :=
      ⟨_, (key _).mpr h.choose_spec⟩
    simp only [h, h', ↓reduceDIte]
    exact hu _ _ _ h'.choose_spec ((key _).mpr h.choose_spec)
  · have h' : ¬ ∃ μ, IsOrbitMeasure G 𝔤 b ψ (nilScale (c : A) hc hc𝔤 O) μ := by
      rintro ⟨μ', hμ'⟩
      refine h ⟨μ'.map (scaleEquiv c hc𝔤 hc𝔤').symm, (key _).mp ?_⟩
      rw [Measure.map_map hc1.measurable hc2.measurable,
        show (⇑(scaleEquiv c hc𝔤 hc𝔤') ∘ ⇑(scaleEquiv c hc𝔤 hc𝔤').symm) = id from
          funext (scaleEquiv c hc𝔤 hc𝔤').apply_symm_apply, Measure.map_id]
      exact hμ'
    simp only [h, h', ↓reduceDIte, Measure.map_zero]

/-- `b(c ·, ·)` is nondegenerate on `𝔤` when `b` is. -/
theorem restrictForm_scaleForm_nondegenerate (c : Aˣ)
    (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤) (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤)
    (hnd : (restrictForm 𝔤 b).Nondegenerate) :
    (restrictForm 𝔤 (scaleForm b c)).Nondegenerate := by
  set e := scaleEquiv c hc𝔤 hc𝔤'
  have hr : ∀ Y Z : ↥𝔤, restrictForm 𝔤 (scaleForm b c) Y Z = restrictForm 𝔤 b (e Y) Z :=
    fun _ _ => rfl
  refine ⟨fun Y hY => ?_, fun Z hZ => ?_⟩
  · have : e Y = 0 := hnd.1 _ fun Z => by rw [← hr]; exact hY Z
    exact e.map_eq_zero_iff.mp this
  · exact hnd.2 Z fun Y => by
      have := hZ (e.symm Y)
      rwa [hr, LinearEquiv.apply_symm_apply] at this

/-- The self-dual measures for `b(c ·, ·)` and `b` differ by a constant `κ ≠ 0` (both are Haar
measures, `b` being nondegenerate). -/
theorem exists_selfDualHaar_scaleForm_eq (ψ : NontrivialAddChar F) (c : Aˣ)
    (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤) (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤)
    (hnd : (restrictForm 𝔤 b).Nondegenerate) :
    ∃ κ : NNReal, κ ≠ 0 ∧ selfDualHaar 𝔤 (scaleForm b c) ψ = κ • selfDualHaar 𝔤 b ψ := by
  obtain ⟨_, _, _, _, _⟩ := lieSubalgebra_topology 𝔤
  haveI := t2Space_of_moduleTopology F A
  haveI := isTopologicalAddGroup_lieSubalgebra 𝔤
  have hμ := isSelfDual_selfDualHaar_of_nondegenerate 𝔤 hnd ψ
  have hν := isSelfDual_selfDualHaar_of_nondegenerate 𝔤
    (restrictForm_scaleForm_nondegenerate c hc𝔤 hc𝔤' hnd) ψ
  haveI := hμ.1
  haveI := hν.1
  have hκ := Measure.isAddLeftInvariant_eq_smul (selfDualHaar 𝔤 (scaleForm b c) ψ)
    (selfDualHaar 𝔤 b ψ)
  refine ⟨_, fun h0 => ?_, hκ⟩
  rw [h0, zero_smul] at hκ
  exact NeZero.ne (selfDualHaar 𝔤 (scaleForm b c) ψ) hκ

/-- **Representatives of `f ↦ μ_O(f̂)` under rescaling**: `j` represents it for `O` and
`b(c ·, ·)` iff it does for `c O` and `b`.  The self-dual measure for `b(c ·, ·)` is `κ` times that
for `b` (`exists_selfDualHaar_scaleForm_eq`), so `f̂_{b(c·,·)}(Y) = κ f̂_b(c Y)`; with
`c_* μ_O = μ_{cO}` (`orbitMeasure_scale`) both sides of the identity defining `ĵ` acquire the
factor `κ`. -/
theorem isJHat_scale_iff (ψ : NontrivialAddChar F) (c : Aˣ)
    (hc : ∀ a : A, (c : A) * a = a * c)
    (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤) (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤)
    (hb : ∀ Y Z : A, b ((c : A) * Y) Z = b Y ((c : A) * Z))
    (hnd : (restrictForm 𝔤 b).Nondegenerate)
    (hu : ∀ O' μ ν, IsOrbitMeasure G 𝔤 b ψ O' μ → IsOrbitMeasure G 𝔤 b ψ O' ν → μ = ν)
    (O : NilOrbit G 𝔤) (j : ↥𝔤 → ℂ) :
    IsJHat G 𝔤 (scaleForm b c) ψ O j ↔ IsJHat G 𝔤 b ψ (nilScale (c : A) hc hc𝔤 O) j := by
  obtain ⟨κ, hκ0, hκ⟩ := exists_selfDualHaar_scaleForm_eq ψ c hc𝔤 hc𝔤' hnd
  have hμO := orbitMeasure_scale ψ c hc hc𝔤 hc𝔤' hb hu O
  set e := scaleEquiv c hc𝔤 hc𝔤' with he_def
  let h : ↥𝔤 ≃ₜ ↥𝔤 :=
    ⟨e.toEquiv, continuous_scaleEquiv c hc𝔤 hc𝔤', continuous_scaleEquiv_symm c hc𝔤 hc𝔤'⟩
  let em := h.toMeasurableEquiv
  have hem : (em : ↥𝔤 → ↥𝔤) = e := rfl
  have hfour : ∀ f Y, fourierLie 𝔤 (scaleForm b c) ψ f Y =
      ((κ : ℝ) : ℂ) * fourierLie 𝔤 b ψ f (e Y) := by
    intro f Y
    unfold fourierLie fourierWRT
    rw [hκ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [restrictForm, LinearMap.compl₁₂_apply, scaleForm_apply, hb]
    rfl
  have hint1 : ∀ f, ∫ X, fourierLie 𝔤 (scaleForm b c) ψ f X ∂(orbitMeasure G 𝔤 (scaleForm b c) ψ O)
      = ((κ : ℝ) : ℂ) * ∫ X, fourierLie 𝔤 b ψ f X ∂(orbitMeasure G 𝔤 b ψ
        (nilScale (c : A) hc hc𝔤 O)) := by
    intro f
    rw [hμO, ← hem, integral_map_equiv em, hem, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun X => hfour f X)
  have hint2 : ∀ f : ↥𝔤 → ℂ, ∫ X, f X * j X ∂(selfDualHaar 𝔤 (scaleForm b c) ψ) =
      ((κ : ℝ) : ℂ) * ∫ X, f X * j X ∂(selfDualHaar 𝔤 b ψ) := fun f => by
    rw [hκ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hκc : ((κ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hκ0
  unfold IsJHat
  refine and_congr Iff.rfl (and_congr ?_ (forall_congr' fun f => imp_congr_right fun _ => ?_))
  · rw [hκ]
    exact locallyIntegrable_nnreal_smul_iff hκ0
  · rw [hint1, hint2]
    exact mul_right_inj' hκc

/-- **`ĵ_{b(c ·, ·)}(O, X) = ĵ_b(c O, X)`** for `X ∈ 𝔤` regular semisimple, `c` a central unit
with `c 𝔤 = 𝔤` and `b(c Y, Z) = b(Y, c Z)`, when `b` is nondegenerate on `𝔤`, the regular
semisimple set of `𝔤` is open, and orbit measures for `b` are unique: both are representatives of
the same distribution (`isJHat_scale_iff`), which agree on the open regular set
(`eqOn_of_isJHat`). -/
theorem jHat_scale (ψ : NontrivialAddChar F) (c : Aˣ)
    (hc : ∀ a : A, (c : A) * a = a * c)
    (hc𝔤 : ∀ Y ∈ 𝔤, (c : A) * Y ∈ 𝔤) (hc𝔤' : ∀ Y ∈ 𝔤, ((c⁻¹ : Aˣ) : A) * Y ∈ 𝔤)
    (hb : ∀ Y Z : A, b ((c : A) * Y) Z = b Y ((c : A) * Z))
    (hnd : (restrictForm 𝔤 b).Nondegenerate)
    (hopen : IsOpen {Z : ↥𝔤 | IsRegularSS 𝔤 (Z : A)})
    (hu : ∀ O' μ ν, IsOrbitMeasure G 𝔤 b ψ O' μ → IsOrbitMeasure G 𝔤 b ψ O' ν → μ = ν)
    (O : NilOrbit G 𝔤) (X : A) (hX : X ∈ 𝔤) (hXr : IsRegularSS 𝔤 X) :
    jHat G 𝔤 (scaleForm b c) ψ O X = jHat G 𝔤 b ψ (nilScale (c : A) hc hc𝔤 O) X := by
  have key := isJHat_scale_iff ψ c hc hc𝔤 hc𝔤' hb hnd hu O
  unfold jHat
  by_cases h : ∃ j, IsJHat G 𝔤 (scaleForm b c) ψ O j
  · have h' : ∃ j, IsJHat G 𝔤 b ψ (nilScale (c : A) hc hc𝔤 O) j :=
      ⟨_, (key _).mp h.choose_spec⟩
    simp only [h, h', hX, ↓reduceDIte]
    obtain ⟨_, _, _, _, _⟩ := lieSubalgebra_topology 𝔤
    haveI := t2Space_of_moduleTopology F A
    haveI := isTopologicalAddGroup_lieSubalgebra 𝔤
    have hμ := isSelfDual_selfDualHaar_of_nondegenerate 𝔤 hnd ψ
    haveI := hμ.1
    exact eqOn_of_isJHat hμ ((key _).mp h.choose_spec) h'.choose_spec hopen le_rfl
      (show (⟨X, hX⟩ : ↥𝔤) ∈ {Z : ↥𝔤 | IsRegularSS 𝔤 (Z : A)} from hXr)
  · have h' : ¬ ∃ j, IsJHat G 𝔤 b ψ (nilScale (c : A) hc hc𝔤 O) j :=
      fun ⟨j, hj⟩ => h ⟨j, (key j).mpr hj⟩
    simp only [h, h', ↓reduceDIte]

end ScaleMeasure

end GSpinGGP
