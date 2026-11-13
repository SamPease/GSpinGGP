/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LuoTorusIntegral
import GSpinGGP.TraceFormula.CThetaTransport
import GSpinGGP.Foundations.CommutantSquarefree

/-!
# The torus integrals of `θ ∘ ad` and of `θ` agree (step (L8) of `LuoTransfer`)

`torusIntegralLie_toSO` (Thesis §12.1; Luo §7.1), from the reduction
`torusIntegralLie_toSO_of_germ_conj` and its two hypotheses:

* `unitConj`, `conjCentralizerIso`: conjugation by `u ∈ G(F)` is an isomorphism of descent data
  `(Z_G(X), 𝔤_X) ≃ (Z_G(uXu⁻¹), 𝔤_{uXu⁻¹})`;
* `germLie_conj`: germs of a Lie quasi-character are conjugation invariant (the orbits matched by
  `Ad u`);
* `LuoDatum.orbitSpec_unitConj_diagU`: Luo's recipe is `SO(W)`-invariant
  (`SingleBlock.isInOrbitNu_conj_iff`);
* `LuoDatum.cTheta_unitConj_diagU`, `cTheta_toSOLin_diagLie_conj`: Luo's `c_θ` is invariant under
  conjugation by `SO(W)`; `germLie0_diagLie_conj` (`hgerm`): the germs of `θ ∘ ad` at `X` and at
  `gXg⁻¹` agree (both are Luo's `c_θ`, `cTheta_toSO`);
* `commClause_iff_squarefree`, `isGammaEltLie_iff_isNat` (`hnat`): `ad` carries `𝔱⁰_♮` onto Luo's
  `𝔱_♮` (regularity in `𝔱⁰` is a squarefree characteristic polynomial on `W''`,
  `Foundations/CommutantSquarefree.lean`).
-/

noncomputable section

open MeasureTheory Topology Filter

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

section UnitConj

variable {F : Type*} [CommRing F] {A : Type*} [Ring A] [Algebra F A]

variable (F) in
/-- Conjugation `a ↦ u a u⁻¹` by a unit, as an algebra automorphism (`ConjAct`). -/
def unitConj (u : Aˣ) : A ≃ₐ[F] A := MulSemiringAction.toAlgEquiv F A (ConjAct.toConjAct u)

theorem unitConj_apply (u : Aˣ) (a : A) :
    unitConj F u a = (u : A) * a * ((u⁻¹ : Aˣ) : A) := rfl

end UnitConj

section GermConj

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
  {A : Type*} [Ring A] [Algebra F A] [TopologicalSpace A] [Module.Finite F A]
  [IsModuleTopology F A]

/-- **Conjugation by `u ∈ G(F)` is an isomorphism of descent data** `(Z_G(X), 𝔤_X, b) ≃
`(Z_G(uXu⁻¹), 𝔤_{uXu⁻¹}, b)` when `G(F)` normalizes `𝔤` and `b` is `Ad u`-invariant
(`CentralizerIso.ofSubalgebra` for the algebra automorphism `Ad u`). -/
def conjCentralizerIso {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A} {b : LinearMap.BilinForm F A}
    (hG : ∀ g ∈ G, ∀ Y ∈ 𝔤, (g : A) * Y * (↑g⁻¹ : A) ∈ 𝔤) {u : Aˣ} (hu : u ∈ G)
    (hb : ∀ Y Z : A, b (unitConj F u Y) (unitConj F u Z) = b Y Z) (X : A) :
    CentralizerIso (lieGrpCentralizer G X) (lieCentralizer 𝔤 X) b
      (lieGrpCentralizer G (unitConj F u X)) (lieCentralizer 𝔤 (unitConj F u X)) b 1 1 :=
  CentralizerIso.ofSubalgebra ⊤ ⊤ (unitConj F u).toLinearMap (unitConj F u⁻¹).toLinearMap
    (fun _ _ => trivial) (fun _ _ => trivial) (map_one (unitConj F u))
    (fun a _ c _ => map_mul (unitConj F u) a c)
    (fun a _ => by simp [unitConj_apply, mul_assoc]) (fun a _ => by simp [unitConj_apply, mul_assoc])
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun Y hY => by
      rw [mem_lieCentralizer_units_one] at hY ⊢
      obtain ⟨hY𝔤, hXY⟩ := mem_lieCentralizer.mp hY
      refine mem_lieCentralizer.mpr ⟨hG u hu Y hY𝔤, ?_⟩
      change unitConj F u X * unitConj F u Y = unitConj F u Y * unitConj F u X
      rw [← map_mul, ← map_mul, hXY])
    (fun Y hY => by
      rw [mem_lieCentralizer_units_one] at hY ⊢
      obtain ⟨hY𝔤, hXY⟩ := mem_lieCentralizer.mp hY
      refine mem_lieCentralizer.mpr ⟨?_, ?_⟩
      · have := hG u⁻¹ (inv_mem hu) Y hY𝔤
        rwa [inv_inv] at this
      · have h := congrArg (unitConj F u⁻¹) hXY
        simp only [map_mul] at h
        have e : unitConj F u⁻¹ (unitConj F u X) = X := by simp [unitConj_apply, mul_assoc]
        rw [e] at h
        exact h)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun v hv w hw => by
      rw [grpCentralizer_one] at hv ⊢
      have hw' : w = u * v * u⁻¹ := Units.ext (by rw [hw]; rfl)
      subst hw'
      refine ⟨G.mul_mem (G.mul_mem hu hv.1) (inv_mem hu), ?_⟩
      have h := congrArg (unitConj F u) hv.2
      simp only [map_mul, unitConj_apply] at h
      simpa [mul_assoc, unitConj_apply] using h)
    (fun v hv w hw => by
      rw [grpCentralizer_one] at hv ⊢
      have hw' : w = u⁻¹ * v * u⁻¹⁻¹ := Units.ext (by rw [hw]; rfl)
      subst hw'
      refine ⟨G.mul_mem (G.mul_mem (inv_mem hu) hv.1) (inv_mem (inv_mem hu)), ?_⟩
      have h := congrArg (unitConj F u⁻¹) hv.2
      simp only [map_mul, unitConj_apply] at h
      simpa [mul_assoc, unitConj_apply] using h)
    (fun Y _ Z _ => hb Y Z)

/-- **Germs of a Lie quasi-character are conjugation invariant**: for `u ∈ G(F)` and `X ∈ 𝔤`
semisimple, `Ad u` matches the nilpotent orbits of `𝔤_X` with those of `𝔤_{uXu⁻¹}`, regular ones
with regular ones, and `c_{θ, u O u⁻¹}(uXu⁻¹) = c_{θ,O}(X)`.  Hypotheses: `G(F)` normalizes `𝔤`,
`b` is `G(F)`-invariant, local expansions at `X` have unique regular coefficients (`huniq`), and at
`uXu⁻¹` the form is nondegenerate on the centralizer, the regular set is open and orbit measures
are unique (the hypotheses of `CentralizerIso.jHat_map`).  Proof: `θ(u Z u⁻¹) = θ(Z)` on the
regular set, so `Ad u` transports local expansions (`germLie_eq_of_transport`). -/
theorem germLie_conj [PerfectField F] {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A}
    {b : LinearMap.BilinForm F A} {ψ : NontrivialAddChar F} {θ : ↥𝔤 → ℂ}
    (hG : ∀ g ∈ G, ∀ Y ∈ 𝔤, (g : A) * Y * (↑g⁻¹ : A) ∈ 𝔤)
    (hθ : IsLieQuasiCharacter G 𝔤 b ψ θ) {u : Aˣ} (hu : u ∈ G)
    (hb : ∀ Y Z : A, b (unitConj F u Y) (unitConj F u Z) = b Y Z)
    {X : A} (hX : X ∈ 𝔤) (hss : IsSS F X)
    (hnd : (restrictForm (lieCentralizer 𝔤 (unitConj F u X)) b).Nondegenerate)
    (hopen : IsOpen {Z : ↥(lieCentralizer 𝔤 (unitConj F u X)) |
      IsRegularSS (lieCentralizer 𝔤 (unitConj F u X)) (Z : A)})
    (hum : ∀ O μ ν, IsOrbitMeasure (lieGrpCentralizer G (unitConj F u X))
        (lieCentralizer 𝔤 (unitConj F u X)) b ψ O μ →
      IsOrbitMeasure (lieGrpCentralizer G (unitConj F u X))
        (lieCentralizer 𝔤 (unitConj F u X)) b ψ O ν → μ = ν)
    (huniq : ∀ c c'', HasGermExpansionLie G 𝔤 b ψ θ X c → HasGermExpansionLie G 𝔤 b ψ θ X c'' →
      ∀ O ∈ NilReg _ _, c O = c'' O) :
    ∃ E : NilOrbit (lieGrpCentralizer G X) (lieCentralizer 𝔤 X) ≃
        NilOrbit (lieGrpCentralizer G (unitConj F u X)) (lieCentralizer 𝔤 (unitConj F u X)),
      (∀ O, E O ∈ NilReg _ _ ↔ O ∈ NilReg _ _) ∧
      (∀ O (P : A → Prop), (∃ Y ∈ nilOrbitSet (E O), P (Y : A)) ↔
        ∃ Y ∈ nilOrbitSet O, P (unitConj F u (Y : A))) ∧
      E (Quotient.mk (nilSetoid _ _) ⟨0, LieSubalgebra.zero_mem _, IsNilpotent.zero⟩) =
        Quotient.mk (nilSetoid _ _) ⟨0, LieSubalgebra.zero_mem _, IsNilpotent.zero⟩ ∧
      ∀ O, germLie G 𝔤 b ψ θ (unitConj F u X) (E O) = germLie G 𝔤 b ψ θ X O := by
  classical
  set X' := unitConj F u X with hX'
  have hX'm : X' ∈ 𝔤 := hG u hu X hX
  have hss' : IsSS F X' := (isSS_units_conj u X).mpr hss
  let ι := conjCentralizerIso hG hu hb X
  have hG₀ := conj_mem_lieCentralizer_of_mem_lieGrpCentralizer hG X
  have hG₁ := conj_mem_lieCentralizer_of_mem_lieGrpCentralizer hG X'
  have e𝔤₀ : lieCentralizer (lieCentralizer 𝔤 X) ((1 : Aˣ) : A) = lieCentralizer 𝔤 X := by
    rw [Units.val_one, lieCentralizer_one]
  have e𝔤₁ : lieCentralizer (lieCentralizer 𝔤 X') ((1 : Aˣ) : A) = lieCentralizer 𝔤 X' := by
    rw [Units.val_one, lieCentralizer_one]
  have eG₀ := grpCentralizer_one (lieGrpCentralizer G X)
  have eG₁ := grpCentralizer_one (lieGrpCentralizer G X')
  have hnd' : (restrictForm (lieCentralizer (lieCentralizer 𝔤 X') ((1 : Aˣ) : A)) b).Nondegenerate
      := by rw [e𝔤₁]; exact hnd
  have hopen' : IsOpen {Z : ↥(lieCentralizer (lieCentralizer 𝔤 X') ((1 : Aˣ) : A)) |
      IsRegularSS (lieCentralizer (lieCentralizer 𝔤 X') ((1 : Aˣ) : A)) (Z : A)} := by
    rw [e𝔤₁]; exact hopen
  have hu' : ∀ O' μ ν, IsOrbitMeasure (grpCentralizer (lieGrpCentralizer G X') 1)
      (lieCentralizer (lieCentralizer 𝔤 X') ((1 : Aˣ) : A)) b ψ O' μ →
      IsOrbitMeasure (grpCentralizer (lieGrpCentralizer G X') 1)
      (lieCentralizer (lieCentralizer 𝔤 X') ((1 : Aˣ) : A)) b ψ O' ν → μ = ν := by
    rw [eG₁, e𝔤₁]; exact hum
  let β₀ := nilOrbitCongr eG₀.symm e𝔤₀.symm
  let ν := ι.nilOrbitEquiv hG₀
  let β₁ := nilOrbitCongr eG₁ e𝔤₁
  let E := β₀.trans (ν.trans β₁)
  have hE : ∀ O, E O = β₁ (ν (β₀ O)) := fun _ => rfl
  have hreg : ∀ O, E O ∈ NilReg _ _ ↔ O ∈ NilReg _ _ := fun O => by
    rw [hE, nilOrbitCongr_mem_nilReg_iff, ι.nilOrbitEquiv_mem_nilReg_iff hG₀ hG₁,
      nilOrbitCongr_mem_nilReg_iff]
  have hspec : ∀ O (P : A → Prop), (∃ Y ∈ nilOrbitSet (E O), P (Y : A)) ↔
      ∃ Y ∈ nilOrbitSet O, P (unitConj F u (Y : A)) := fun O P => by
    rw [hE]
    refine (exists_mem_nilOrbitSet_nilOrbitCongr_iff eG₁ e𝔤₁ _ P).trans ?_
    refine (ι.exists_mem_nilOrbitSet_nilOrbitEquiv_iff hG₀ (β₀ O) P).trans ?_
    exact exists_mem_nilOrbitSet_nilOrbitCongr_iff eG₀.symm e𝔤₀.symm O
      (fun Y => P (unitConj F u Y))
  have hzero : E (Quotient.mk (nilSetoid _ _) ⟨0, LieSubalgebra.zero_mem _, IsNilpotent.zero⟩) =
      Quotient.mk (nilSetoid _ _) ⟨0, LieSubalgebra.zero_mem _, IsNilpotent.zero⟩ := by
    change β₁ (ι.nilOrbitMap (β₀ (Quotient.mk _ _))) = _
    rw [nilOrbitCongr_mk, ι.nilOrbitMap_mk, nilOrbitCongr_mk]
    exact congrArg (Quotient.mk _) (Subtype.ext (by
      change unitConj F u 0 = 0
      rw [map_zero]))
  refine ⟨E, hreg, hspec, hzero, fun O => ?_⟩
  have htr : ∀ c', HasGermExpansionLie G 𝔤 b ψ θ X' c' →
      HasGermExpansionLie G 𝔤 b ψ θ X (c' ∘ E) := by
    rintro c' ⟨hfin, ω', hω', hexp⟩
    obtain ⟨ωr, hωr, hregadd⟩ := exists_nhds_isRegularSS_add F 𝔤 hss
    haveI : ContinuousAdd A := IsModuleTopology.toContinuousAdd F A
    have hcont : Continuous (unitConj F u) :=
      IsModuleTopology.continuous_of_linearMap (unitConj F u).toLinearMap
    refine ⟨?_, unitConj F u ⁻¹' ω' ∩ ωr, inter_mem
      (hcont.continuousAt.preimage_mem_nhds (by simpa using hω')) hωr,
      fun Y hY hYc hYr Z hZ => ?_⟩
    · rw [Function.support_comp_eq_preimage]
      exact hfin.preimage E.injective.injOn
    have hYc1 : Y ∈ lieCentralizer (lieCentralizer 𝔤 X) ((1 : Aˣ) : A) :=
      mem_lieCentralizer_units_one.mpr hYc
    have hY' : unitConj F u Y ∈ lieCentralizer 𝔤 X' := by
      have := ι.bijOn.mapsTo hYc1
      rw [SetLike.mem_coe, mem_lieCentralizer_units_one] at this
      exact this
    have hYr1 : IsRegularSS (lieCentralizer (lieCentralizer 𝔤 X) ((1 : Aˣ) : A)) Y := by
      rw [e𝔤₀]; exact hYr
    have hYr' : IsRegularSS (lieCentralizer 𝔤 X') (unitConj F u Y) := by
      have := (ι.isRegularSS_iff Y hYc1).mpr hYr1
      rwa [e𝔤₁] at this
    let Z' : ↥𝔤 := ⟨unitConj F u Z, hG u hu Z Z.2⟩
    have hZ' : (Z' : A) = X' + unitConj F u Y := by
      change unitConj F u Z = _
      rw [hZ, map_add]
    have hθZ : θ Z' = θ Z :=
      hθ.1 u hu Z Z' ⟨Z.2, by rw [hZ]; exact hregadd Y hY.2 hYc hYr⟩ rfl
    rw [← hθZ, hexp _ hY.1 hY' hYr' Z' hZ', ← finsum_comp_equiv E]
    refine finsum_congr fun O => ?_
    simp only [Function.comp_apply]
    congr 1
    rw [hE, jHat_nilOrbitCongr eG₁ e𝔤₁, ← jHat_nilOrbitCongr eG₀.symm e𝔤₀.symm _ ψ O Y]
    exact ι.jHat_map hG₀ ψ hnd' hopen' hu' (β₀ O) Y hYc1 hYr1
  exact (germLie_eq_of_transport E hreg (hθ.2 ⟨X', hX'm⟩ hss') htr huniq O).symm

end GermConj


namespace LuoDatum

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (L : LuoDatum F)

/-- The trace form is invariant under conjugation by a unit of `End W × End V`. -/
theorem traceForm_unitConj (u : L.Ambˣ) (Y Z : L.Amb) :
    L.traceForm (unitConj F u Y) (unitConj F u Z) = L.traceForm Y Z := by
  have hW : L.fstA ((u⁻¹ : L.Ambˣ) : L.Amb) * L.fstA (u : L.Amb) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hV : L.sndA ((u⁻¹ : L.Ambˣ) : L.Amb) * L.sndA (u : L.Amb) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have keyW : ∀ P R : Module.End F L.W, LinearMap.trace F L.W
      (L.fstA (u : L.Amb) * P * L.fstA ((u⁻¹ : L.Ambˣ) : L.Amb) *
        (L.fstA (u : L.Amb) * R * L.fstA ((u⁻¹ : L.Ambˣ) : L.Amb))) =
      LinearMap.trace F L.W (P * R) := by
    intro P R
    have e : L.fstA (u : L.Amb) * P * L.fstA ((u⁻¹ : L.Ambˣ) : L.Amb) *
        (L.fstA (u : L.Amb) * R * L.fstA ((u⁻¹ : L.Ambˣ) : L.Amb)) =
        L.fstA (u : L.Amb) * (P * R) * L.fstA ((u⁻¹ : L.Ambˣ) : L.Amb) := by
      simp only [mul_assoc]
      rw [← mul_assoc _ (L.fstA (u : L.Amb)), hW, one_mul]
    rw [e, LinearMap.trace_mul_comm, ← mul_assoc, hW, one_mul]
  have keyV : ∀ P R : Module.End F L.V, LinearMap.trace F L.V
      (L.sndA (u : L.Amb) * P * L.sndA ((u⁻¹ : L.Ambˣ) : L.Amb) *
        (L.sndA (u : L.Amb) * R * L.sndA ((u⁻¹ : L.Ambˣ) : L.Amb))) =
      LinearMap.trace F L.V (P * R) := by
    intro P R
    have e : L.sndA (u : L.Amb) * P * L.sndA ((u⁻¹ : L.Ambˣ) : L.Amb) *
        (L.sndA (u : L.Amb) * R * L.sndA ((u⁻¹ : L.Ambˣ) : L.Amb)) =
        L.sndA (u : L.Amb) * (P * R) * L.sndA ((u⁻¹ : L.Ambˣ) : L.Amb) := by
      simp only [mul_assoc]
      rw [← mul_assoc _ (L.sndA (u : L.Amb)), hV, one_mul]
    rw [e, LinearMap.trace_mul_comm, ← mul_assoc, hV, one_mul]
  simp only [traceForm, LinearMap.mk₂_apply, unitConj_apply, map_mul]
  rw [keyW, keyV]

/-- `diagU p ∈ Ḡ` for `p ∈ SO(W)`. -/
theorem diagU_mem_Gbar {p : (Module.End F L.W)ˣ} (hp : p ∈ SOu L.QW) : L.diagU p ∈ L.Gbar :=
  Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr (by rw [unitFst_diagU]; exact hp),
    Subgroup.mem_comap.mpr (by rw [unitSnd_diagU]; exact L.extU_mem_SOu hp)⟩

/-- **Luo's recipe is invariant under `SO(W)`**: conjugating by `diagU p`, `p ∈ SO(W)`, and
moving `U` by `p` (`SingleBlock.isInOrbitNu_conj_iff` on `W` and on `V`, where `p` acts as
`p ⊕ 1`). -/
theorem orbitSpec_unitConj_diagU {p : (Module.End F L.W)ˣ} (hp : p ∈ SOu L.QW)
    (U : Submodule F L.W) (Y : L.Amb) :
    L.OrbitSpec (U.map (p : Module.End F L.W)) (unitConj F (L.diagU p) Y) ↔ L.OrbitSpec U Y := by
  have hpV := L.extU_mem_SOu hp
  set σW : L.QW.IsometryEquiv L.QW :=
    ⟨LinearMap.GeneralLinearGroup.generalLinearEquiv F _ p, fun v => hp.1 v⟩
  set σV : L.QV.IsometryEquiv L.QV :=
    ⟨LinearMap.GeneralLinearGroup.generalLinearEquiv F _ (Units.map L.extGrp p), fun v => hpV.1 v⟩
  have hf : L.fstA (unitConj F (L.diagU p) Y) = σW.toLinearEquiv.conj (L.fstA Y) :=
    LinearMap.ext fun _ => rfl
  have hs : L.sndA (unitConj F (L.diagU p) Y) = σV.toLinearEquiv.conj (L.sndA Y) :=
    LinearMap.ext fun _ => rfl
  have e1 : U.map (p : Module.End F L.W) = U.map (σW.toLinearEquiv : L.W →ₗ[F] L.W) := rfl
  have hprod : (U.map (σW.toLinearEquiv : L.W →ₗ[F] L.W)).prod (⊤ : Submodule F L.Zs) =
      (U.prod ⊤).map (σV.toLinearEquiv : L.V →ₗ[F] L.V) := by
    ext ⟨w, z⟩
    rw [Submodule.mem_map_equiv, Submodule.mem_prod, Submodule.mem_prod, Submodule.mem_map_equiv]
    simp only [Submodule.mem_top, and_true]
    rfl
  unfold OrbitSpec
  rw [e1, hprod, LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq, hf, hs,
    SingleBlock.isInOrbitNu_conj_iff σV, SingleBlock.isInOrbitNu_conj_iff σW]

/-- **Luo's `c_θ` is invariant under conjugation by `SO(W)`** (diagonally in `Ḡ`), given
uniqueness of the orbit selected by Luo's recipe at `M' = p M p⁻¹` (`huniq'`) and of orbit measures
at `M'` (`hum`), and openness of the regular set of `𝔤_{M'}` (`hopen`): `germLie_conj` for
`Ad(diagU p)`, using `germLie_unique_SO` at `M`; `Ad(diagU p)` carries the recipe at `M` to the
recipe at `M'` (`orbitSpec_unitConj_diagU`, `ker M' = p ker M`, `map_dite_choose_eq`). -/
theorem cTheta_unitConj_diagU (hQV : IsNondeg L.QV) (ψ : NontrivialAddChar F) {θ : ↥L.lie → ℂ}
    (hθ : IsLieQuasiCharacter L.Gbar L.lie L.traceForm ψ θ) {p : (Module.End F L.W)ˣ}
    (hp : p ∈ SOu L.QW) {M : L.Amb} (hM : M ∈ L.lie) (hss : IsSS F M)
    (hopen : IsOpen {Z : ↥(lieCentralizer L.lie (unitConj F (L.diagU p) M)) |
      IsRegularSS (lieCentralizer L.lie (unitConj F (L.diagU p) M)) (Z : L.Amb)})
    (hum : ∀ O μ ν, IsOrbitMeasure (lieGrpCentralizer L.Gbar (unitConj F (L.diagU p) M))
        (lieCentralizer L.lie (unitConj F (L.diagU p) M)) L.traceForm ψ O μ →
      IsOrbitMeasure (lieGrpCentralizer L.Gbar (unitConj F (L.diagU p) M))
        (lieCentralizer L.lie (unitConj F (L.diagU p) M)) L.traceForm ψ O ν → μ = ν)
    (huniq' : ∀ O O' : NilOrbit (lieGrpCentralizer L.Gbar (unitConj F (L.diagU p) M))
        (lieCentralizer L.lie (unitConj F (L.diagU p) M)), O ∈ NilReg _ _ → O' ∈ NilReg _ _ →
      (∃ Y ∈ nilOrbitSet O, L.OrbitSpec (LinearMap.ker (L.fstA (unitConj F (L.diagU p) M)))
        (Y : L.Amb)) →
      (∃ Y ∈ nilOrbitSet O', L.OrbitSpec (LinearMap.ker (L.fstA (unitConj F (L.diagU p) M)))
        (Y : L.Amb)) → O = O') :
    L.cTheta ψ θ (unitConj F (L.diagU p) M) = L.cTheta ψ θ M := by
  classical
  have hu := L.diagU_mem_Gbar hp
  have hM' : unitConj F (L.diagU p) M ∈ L.lie := L.conj_mem_lie_of_mem_Gbar _ hu M hM
  have hss' : IsSS F (unitConj F (L.diagU p) M) := (isSS_units_conj _ M).mpr hss
  have hnd := restrictForm_lieCentralizer_nondegenerate_of_isSS
    (L.restrictForm_lie_traceForm_nondegenerate hQV) L.traceForm_invariant hM'
    (LieAlgebra.ad_isSemisimple_of_isSemisimple_mulLeft hss')
  obtain ⟨E, hreg, hspec, hzero, hgerm⟩ := germLie_conj L.conj_mem_lie_of_mem_Gbar hθ hu
    (L.traceForm_unitConj _) hM hss hnd hopen hum
    (germLie_unique_SO L hQV ψ θ M hM hss)
  have hker : LinearMap.ker (L.fstA (unitConj F (L.diagU p) M)) =
      (LinearMap.ker (L.fstA M)).map (p : Module.End F L.W) := by
    ext v
    rw [LinearMap.mem_ker, Submodule.mem_map]
    have hpp : ∀ w, (p : Module.End F L.W) (((p⁻¹ : (Module.End F L.W)ˣ) : Module.End F L.W) w) = w :=
      fun w => by rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
    have hpp' : ∀ w, ((p⁻¹ : (Module.End F L.W)ˣ) : Module.End F L.W) ((p : Module.End F L.W) w) = w :=
      fun w => by rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
    change (p : Module.End F L.W) (L.fstA M (((p⁻¹ : (Module.End F L.W)ˣ) : Module.End F L.W) v)) = 0
      ↔ _
    constructor
    · intro h
      refine ⟨_, ?_, hpp v⟩
      rw [LinearMap.mem_ker]
      simpa [hpp'] using congrArg ((p⁻¹ : (Module.End F L.W)ˣ) : Module.End F L.W) h
    · rintro ⟨w, hw, rfl⟩
      rw [hpp', LinearMap.mem_ker.mp hw, map_zero]
  have hspecK : ∀ O, (∃ Y ∈ nilOrbitSet (E O),
      L.OrbitSpec (LinearMap.ker (L.fstA (unitConj F (L.diagU p) M))) (Y : L.Amb)) ↔
      ∃ Y ∈ nilOrbitSet O, L.OrbitSpec (LinearMap.ker (L.fstA M)) (Y : L.Amb) := fun O => by
    rw [hspec O, hker]
    exact exists_congr fun Y => and_congr_right fun _ => L.orbitSpec_unitConj_diagU hp _ _
  unfold cTheta
  rw [← hgerm (L.orbitChoice M)]
  congr 1
  unfold orbitChoice
  refine (map_dite_choose_eq (p := fun O => O ∈ NilReg _ _ ∧ ∃ Y ∈ nilOrbitSet O,
      L.OrbitSpec (LinearMap.ker (L.fstA M)) (Y : L.Amb))
    (q := fun O => O ∈ NilReg _ _ ∧ ∃ Y ∈ nilOrbitSet O,
      L.OrbitSpec (LinearMap.ker (L.fstA (unitConj F (L.diagU p) M))) (Y : L.Amb))
    E E.surjective (fun O => and_congr (hreg O) (hspecK O))
    (fun O O' h h' => E.injective (huniq' _ _ ((hreg O).mpr h.1) ((hreg O').mpr h'.1)
      ((hspecK O).mpr h.2) ((hspecK O').mpr h'.2))) hzero).symm

end LuoDatum

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)
  (ψ : NontrivialAddChar F)

/-- **At most one regular nilpotent orbit of `(so(W) ⊕ so(V))_{ad X}` meets Luo's recipe**, for
`X ∈ 𝔱⁰_♮` of a torus of `Γ(G,H)`: `orbitSpecAt_orbit_unique` transported along the orbit map of
`exists_nilOrbitEquiv_toSOLin` (for any `ψ`; the statement does not involve it). -/
theorem orbitSpec_orbit_unique_toSOLin (ψ : NontrivialAddChar F) (hW : ¬ IsHypPlane d.QW)
    (hV : ¬ IsHypPlane d.QV)
    (T : d.GammaTorus) {X : CliffordAlgebra d.QW} (hX : d.IsGammaEltLie T.1 X) :
    ∀ O O' : NilOrbit (lieGrpCentralizer d.luoOf.Gbar (d.toSOLin (d.diagLie X)))
        (lieCentralizer d.luoOf.lie (d.toSOLin (d.diagLie X))), O ∈ NilReg _ _ →
      O' ∈ NilReg _ _ →
      (∃ Y ∈ nilOrbitSet O, d.luoOf.OrbitSpec
        (LinearMap.ker (d.luoOf.fstA (d.toSOLin (d.diagLie X)))) (Y : d.luoOf.Amb)) →
      (∃ Y ∈ nilOrbitSet O', d.luoOf.OrbitSpec
        (LinearMap.ker (d.luoOf.fstA (d.toSOLin (d.diagLie X)))) (Y : d.luoOf.Amb)) →
      O = O' := by
  have hD : d.diagLie X ∈ d.lieZero := d.diagLie_mem_lieZero hX.1.1
  have hssD : IsSS F (d.diagLie X) := d.isSS_diagLie (d.isSS_of_isGammaEltLie T hX)
  obtain ⟨E, hreg, hspec, -, -, -⟩ := d.exists_nilOrbitEquiv_toSOLin ψ hW hV hD hssD
    (formConst_ne_zero (Module.finrank F (Fin d.m → F))) (formConst_ne_zero (Module.finrank F d.V))
    (fun _ hY _ hZ => d.scaleForm_traceForm_toSOLin hY hZ)
  intro O O' hO hO' hs hs'
  have h := d.orbitSpecAt_orbit_unique T hX (E.symm O) (E.symm O')
    ((hreg _).mp (by rwa [Equiv.apply_symm_apply])) ((hreg _).mp (by rwa [Equiv.apply_symm_apply]))
    ((hspec _ _).mp (by rwa [Equiv.apply_symm_apply]))
    ((hspec _ _).mp (by rwa [Equiv.apply_symm_apply]))
  simpa using congrArg E h

/-- `ad(g X g⁻¹, g X g⁻¹) = φ(g) ad(X, X) φ(g)⁻¹` with `φ(g) = diagU P(g)` (`diagLie_conj`,
`toSOLin_conj`, `toGbarU_comp_diag`). -/
theorem toSOLin_diagLie_conj (g : ↥(GSpin d.QW)) {X : CliffordAlgebra d.QW}
    (hX : X ∈ soSub d.QW) :
    d.toSOLin (d.diagLie (((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X *
        (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))) =
      unitConj F (d.luoOf.diagU (d.specPU g)) (d.toSOLin (d.diagLie X)) := by
  rw [d.diagLie_conj g X, d.toSOLin_conj (d.diag g) (d.lieZero_le_lie (d.diagLie_mem_lieZero hX))]
  have h : d.toGbarU (d.diag g) = d.luoOf.diagU (d.specPU g) := by
    have := DFunLike.congr_fun d.toGbarU_comp_diag g
    simpa only [MonoidHom.comp_apply] using this
  rw [h]
  rfl

/-- **Luo's `c_θ` at `ad(gXg⁻¹)` and at `ad X` agree**, for `X ∈ 𝔱⁰_♮(T)` and `gXg⁻¹ ∈ 𝔱⁰_♮(T')`
(`T, T'` tori of `Γ(G,H)`): `cTheta_unitConj_diagU` for `p = P(g)`, with the hypotheses at
`ad(gXg⁻¹)` from `isOpen_setOf_isRegularSS_lieCentralizer_toSOLin`, `isOrbitMeasure_unique_luo`
and `orbitSpec_orbit_unique_toSOLin`. -/
theorem cTheta_toSOLin_diagLie_conj (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    {θ : ↥d.luoOf.lie → ℂ}
    (hθ : IsLieQuasiCharacter d.luoOf.Gbar d.luoOf.lie d.luoOf.traceForm ψ θ)
    (T T' : d.GammaTorus) (g : ↥(GSpin d.QW)) {X : CliffordAlgebra d.QW}
    (hX : d.IsGammaEltLie T.1 X)
    (hX' : d.IsGammaEltLie T'.1 (((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X *
      (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))) :
    d.luoOf.cTheta ψ θ (d.toSOLin (d.diagLie (((g : (CliffordAlgebra d.QW)ˣ) :
        CliffordAlgebra d.QW) * X *
        (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)))) =
      d.luoOf.cTheta ψ θ (d.toSOLin (d.diagLie X)) := by
  have hD : d.diagLie X ∈ d.lieZero := d.diagLie_mem_lieZero hX.1.1
  have hssD : IsSS F (d.diagLie X) := d.isSS_diagLie (d.isSS_of_isGammaEltLie T hX)
  have hD' := d.diagLie_mem_lieZero hX'.1.1
  have hssD' := d.isSS_diagLie (d.isSS_of_isGammaEltLie T' hX')
  have hopen := d.isOpen_setOf_isRegularSS_lieCentralizer_toSOLin hW hV hD' hssD'
    (formConst_ne_zero (Module.finrank F (Fin d.m → F))) (formConst_ne_zero (Module.finrank F d.V))
    (fun _ hY _ hZ => d.scaleForm_traceForm_toSOLin hY hZ)
  have huniq := d.orbitSpec_orbit_unique_toSOLin ψ hW hV T' hX'
  have hM' := d.toSOLin_diagLie_conj g hX.1.1
  rw [hM'] at hopen huniq ⊢
  exact d.luoOf.cTheta_unitConj_diagU d.nondeg_QV ψ hθ (d.specPU_mem_SOu g) (d.toSO_mem ⟨_, hD⟩)
    (d.isSS_toSOLin hD hssD) hopen (fun _ _ _ h1 h2 => d.isOrbitMeasure_unique_luo _ h1 h2) huniq

/-- **The germs at `X` and at `g X g⁻¹` agree** (the hypothesis `hgerm` of
`torusIntegralLie_toSO_of_germ_conj`), for `x ∈ Γ(G,H)`, `g ∈ GSpin(W)(F)` and `X ∈ 𝔱⁰_♮(T_x)`
(then `gXg⁻¹ ∈ 𝔱⁰_♮(T_{gxg⁻¹})`): both germs are Luo's `c_θ` (`cTheta_toSO`), and
`c_θ(ad(gXg⁻¹)) = c_θ(ad X)`
(`cTheta_toSOLin_diagLie_conj`). -/
theorem germLie0_diagLie_conj (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    (θ : ↥d.luoOf.lie → ℂ)
    (hθ : IsLieQuasiCharacter d.luoOf.Gbar d.luoOf.lie d.luoOf.traceForm ψ θ)
    (x g : ↥(GSpin d.QW)) (hx : d.IsGammaElt x) (X : CliffordAlgebra d.QW) (hX : d.IsGammaEltLie (d.torusOf x) X) :
    d.germLie0 ψ (θ ∘ d.toSO)
        (d.diagLie (((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X *
          (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)))
        (d.orbitChoiceLie (((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X *
          (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))) =
      d.germLie0 ψ (θ ∘ d.toSO) (d.diagLie X) (d.orbitChoiceLie X) := by
  have hx' := d.isGammaElt_conj hx g
  have hX' : d.IsGammaEltLie (d.torusOf (g * x * g⁻¹)) (((g : (CliffordAlgebra d.QW)ˣ) :
      CliffordAlgebra d.QW) * X *
      (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) := by
    rw [d.torusOf_conj]
    exact d.isGammaEltLie_conj g hX
  rw [d.cTheta_toSO ψ hW hV hθ ⟨_, g * x * g⁻¹, hx', rfl⟩ _ hX',
    d.cTheta_toSO ψ hW hV hθ ⟨_, x, hx, rfl⟩ _ hX]
  exact d.cTheta_toSOLin_diagLie_conj ψ hW hV hθ ⟨_, x, hx, rfl⟩ ⟨_, g * x * g⁻¹, hx', rfl⟩ g hX hX'

end GGPData

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

/-- **Regularity in `𝔱⁰` is a squarefree characteristic polynomial** (the third clause of
`IsGammaEltLie` vs that of Luo's `IsNat`): for `x ∈ Γ(G,H)`, `X ∈ 𝔱⁰(T_x)` with `ker X = W'`,
every `Y ∈ so(W)` commuting with `X` and killing `W'` lies in `𝔱⁰` iff `X` has a squarefree
characteristic polynomial on `W'' = X(W)`.  `X` is semisimple, `W = W' ⊥ W''`.
`⇐`: `ad Y` and `P(t)`, `t ∈ T_x`, commute with `X`, so on `W''` they commute
(`commute_of_squarefree_charpoly`), and on `W'` `ad Y = 0`, `P(t) = 1`.
`⇒`: a skew map of `W''` commuting with `X|_{W''}`, extended by `0` on `W'`, is `ad Y` with `Y` as
in the clause, so it lies in `𝔱⁰`, which is abelian (`movedPartAbelian_of_isGammaElt`); hence all
endomorphisms of `W''` commuting with `X` commute (`commute_of_commute_of_isSkewAdjoint`) and the
characteristic polynomial is squarefree (`squarefree_charpoly_of_commute`). -/
theorem commClause_iff_squarefree {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    {X : CliffordAlgebra d.QW} (hX : X ∈ d.lieTorus (d.torusOf x))
    (hker : LinearMap.ker (adV d.QW X) = commonFixed (d.torusOf x)) :
    (∀ Y ∈ soSub d.QW, Y * X = X * Y → (∀ w ∈ commonFixed (d.torusOf x), adV d.QW Y w = 0) →
        Y ∈ d.lieTorus (d.torusOf x)) ↔
      Squarefree (LinearMap.charpoly ((adV d.QW X).restrict (p := LinearMap.range (adV d.QW X))
        (q := LinearMap.range (adV d.QW X)) (fun v _ => LinearMap.mem_range_self _ v))) := by
  classical
  set T := d.torusOf x with hT
  set A := adV d.QW X with hA
  set R := LinearMap.range A with hRdef
  have hXg : X ∈ gspin d.QW := hX.1.1
  have hfixx : commonFixed T = fixedSub x := d.commonFixed_torusOf x
  have hss : A.IsSemisimple := isSemisimple_adV hXg
    (d.isSS_of_commute_of_isGammaElt hx hXg (hX.2.1 x (d.self_mem_torusOf x))
      (fun v hv => hX.2.2 v (by rw [hfixx]; exact hv)))
  have hc : IsCompl (LinearMap.ker A) R := isCompl_ker_range_of_isSemisimple hss
  have hRA : ∀ v ∈ R, A v ∈ R := fun v _ => LinearMap.mem_range_self _ v
  set A₀ := A.restrict hRA with hA₀
  have hskA : ∀ u w, bform d.QW (A u) w = -bform d.QW u (A w) := bform_adV hXg
  have horth : ∀ r ∈ R, ∀ k ∈ LinearMap.ker A, bform d.QW r k = 0 := by
    rintro _ ⟨v, rfl⟩ k hk
    rw [hskA, LinearMap.mem_ker.mp hk, map_zero, neg_zero]
  have hdecomp : ∀ v, ∃ k ∈ LinearMap.ker A, ∃ r ∈ R, v = k + r := fun v => by
    obtain ⟨k, hk, r, hr, h⟩ := Submodule.mem_sup.mp (hc.codisjoint.eq_top ▸ Submodule.mem_top :
      v ∈ LinearMap.ker A ⊔ R)
    exact ⟨k, hk, r, hr, h.symm⟩
  -- commuting with `A` preserves `R`
  have hmapsR : ∀ {g : Module.End F (Fin d.m → F)}, g * A = A * g → ∀ v ∈ R, g v ∈ R := by
    rintro g hg _ ⟨v, rfl⟩
    exact ⟨g v, by rw [← Module.End.mul_apply, ← hg, Module.End.mul_apply]⟩
  have hcommR : ∀ {g : Module.End F (Fin d.m → F)} (hg : g * A = A * g),
      Commute A₀ (g.restrict (hmapsR hg)) := fun {g} hg =>
    LinearMap.ext fun v => Subtype.ext (by
      change A (g v) = g (A v)
      rw [← Module.End.mul_apply, ← hg, Module.End.mul_apply])
  constructor
  · -- `⇒`
    intro hcl
    have hss₀ : Module.End.IsSemisimple A₀ :=
      hss.restrict (p := R) ((Module.End.mem_invtSubmodule A).mpr hRA)
    have hA₀inj : Function.Injective A₀ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro r hr
      have h1 : (r : Fin d.m → F) ∈ LinearMap.ker A := by
        rw [LinearMap.mem_ker]
        exact congrArg Subtype.val hr
      have h2 := hc.disjoint.le_bot ⟨h1, r.2⟩
      exact Subtype.ext ((Submodule.mem_bot F).mp h2)
    let BR : LinearMap.BilinForm F R := (bform d.QW).restrict R
    have hBRsymm : BR.IsSymm := ⟨fun a b => bform_comm d.QW a b⟩
    have hsepR : ∀ r : R, (∀ r' : R, bform d.QW r r' = 0) → r = 0 := by
      intro r h
      refine Subtype.ext (d.nondeg.1 _ fun w => ?_)
      obtain ⟨k, hk, r', hr', rfl⟩ := hdecomp w
      rw [map_add, horth r r.2 k hk, zero_add]
      exact h ⟨r', hr'⟩
    have hBRnd : BR.Nondegenerate := ⟨fun r h => hsepR r h, fun r h => hsepR r fun r' => by
      rw [bform_comm]; exact h r'⟩
    have hA₀sk : BR.IsSkewAdjoint A₀ := fun u w => by
      change bform d.QW (A u) w = bform d.QW u (-(A w))
      rw [hskA, map_neg]
    let π := Submodule.projectionOnto R (LinearMap.ker A) hc.symm
    have hπr : ∀ r (hr : r ∈ R), π r = ⟨r, hr⟩ := fun r hr =>
      Submodule.projectionOnto_apply_left hc.symm ⟨r, hr⟩
    have hπk : ∀ k ∈ LinearMap.ker A, π k = 0 := fun k hk =>
      Submodule.projectionOnto_apply_right hc.symm ⟨k, hk⟩
    let ext : Module.End F R → Module.End F (Fin d.m → F) := fun S => R.subtype ∘ₗ S ∘ₗ π
    have hext : ∀ S k r (hk : k ∈ LinearMap.ker A) (hr : r ∈ R),
        ext S (k + r) = (S ⟨r, hr⟩ : Fin d.m → F) := fun S k r hk hr => by
      simp only [ext, LinearMap.comp_apply, map_add, hπk k hk, hπr r hr, zero_add, map_zero,
        Submodule.subtype_apply]
    have hext0 : ∀ S k, k ∈ LinearMap.ker A → ext S k = 0 := fun S k hk => by
      simp only [ext, LinearMap.comp_apply, hπk k hk, map_zero]
    have hextr : ∀ S r (hr : r ∈ R), ext S r = (S ⟨r, hr⟩ : Fin d.m → F) := fun S r hr => by
      simp only [ext, LinearMap.comp_apply, hπr r hr, Submodule.subtype_apply]
    have key : ∀ S : Module.End F R, BR.IsSkewAdjoint S → Commute A₀ S →
        ∃ Y ∈ soSub d.QW, adV d.QW Y = ext S ∧ Y ∈ d.lieTorus T := by
      intro S hS hSc
      have hsk : ∀ u w, bform d.QW (ext S u) w = -bform d.QW u (ext S w) := by
        intro u w
        obtain ⟨k, hk, r, hr, rfl⟩ := hdecomp u
        obtain ⟨k', hk', r', hr', rfl⟩ := hdecomp w
        rw [hext S k r hk hr, hext S k' r' hk' hr', map_add, map_add, LinearMap.add_apply,
          horth _ (S ⟨r, hr⟩).2 k' hk', bform_comm d.QW k, horth _ (S ⟨r', hr'⟩).2 k hk, zero_add,
          zero_add]
        have := hS ⟨r, hr⟩ ⟨r', hr'⟩
        change bform d.QW (S ⟨r, hr⟩ : Fin d.m → F) r' =
          bform d.QW r (-(S ⟨r', hr'⟩ : Fin d.m → F)) at this
        rw [this, map_neg]
      have hlie : d.luoOf.pair (ext S) 0 ∈ d.luoOf.lie :=
        ⟨(LinearMap.mem_skewAdjointSubmodule _).2 fun u w => by
            have := hsk u w
            rw [← map_neg] at this
            exact this,
          (skewAdjointLieSubalgebra (bform d.luoOf.QV)).zero_mem⟩
      obtain ⟨Z, hZ, hZM⟩ := d.exists_toSOLin_eq hlie
      have hadZ : adV d.QW Z.1 = ext S := congrArg Prod.fst hZM
      have hSA : ext S * A = A * ext S := LinearMap.ext fun v => by
        obtain ⟨k, hk, r, hr, rfl⟩ := hdecomp v
        rw [Module.End.mul_apply, Module.End.mul_apply, map_add, LinearMap.mem_ker.mp hk, zero_add,
          hextr S _ (hRA r hr), hext S k r hk hr]
        have := congrArg Subtype.val (LinearMap.congr_fun hSc.eq ⟨r, hr⟩)
        simp only [Module.End.mul_apply] at this
        exact this.symm
      refine ⟨Z.1, hZ.1, hadZ, hcl Z.1 hZ.1 ?_ fun w hw => ?_⟩
      · have hmem : Z.1 * X - X * Z.1 ∈ soSub d.QW := by
          have := (soSub d.QW).lie_mem hZ.1 hX.1
          rwa [Ring.lie_def] at this
        have h0 := eq_zero_of_mem_soSub_of_adV_eq_zero d.nondeg hmem (by
          rw [adV_commutator hZ.1.1 hXg, hadZ, hSA, sub_self])
        exact sub_eq_zero.mp h0
      · rw [hadZ]
        exact hext0 S w (hker ▸ hw)
    have hskewR : ∀ S₁ S₂ : Module.End F R, BR.IsSkewAdjoint S₁ → BR.IsSkewAdjoint S₂ →
        Commute A₀ S₁ → Commute A₀ S₂ → Commute S₁ S₂ := by
      intro S₁ S₂ h₁ h₂ hc₁ hc₂
      obtain ⟨Y₁, hY₁, hY₁a, hY₁T⟩ := key S₁ h₁ hc₁
      obtain ⟨Y₂, hY₂, hY₂a, hY₂T⟩ := key S₂ h₂ hc₂
      have hcent : ∀ {Y}, Y ∈ soSub d.QW → Y ∈ d.lieTorus T →
          Y ∈ lieCentralizer (gspin d.QW) ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) :=
        fun hY hYT => mem_lieCentralizer.2 ⟨hY.1, hYT.2.1 x (d.self_mem_torusOf x)⟩
      have hkill : ∀ {Y}, Y ∈ soSub d.QW → Y ∈ d.lieTorus T →
          ∀ v ∈ fixedSub x, ⁅Y, CliffordAlgebra.ι d.QW v⁆ = 0 := fun hY hYT v hv => by
        rw [Ring.lie_def, ← ι_adV hY.1, hYT.2.2 v (by rw [hfixx]; exact hv), map_zero]
      have h := movedPartAbelian_of_isGammaElt d x hx Y₁ (hcent hY₁ hY₁T) Y₂ (hcent hY₂ hY₂T)
        (hkill hY₁ hY₁T) (hkill hY₂ hY₂T)
      rw [Ring.lie_def] at h
      have h' := congrArg (adV d.QW) h
      rw [adV_commutator hY₁.1 hY₂.1, hY₁a, hY₂a] at h'
      have h0 : adV d.QW (0 : CliffordAlgebra d.QW) = 0 := by ext; simp
      rw [h0, sub_eq_zero] at h'
      refine LinearMap.ext fun r => Subtype.ext ?_
      have := LinearMap.congr_fun h' (r : Fin d.m → F)
      simp only [Module.End.mul_apply] at this
      rw [hextr S₂ r r.2, hextr S₁ r r.2, hextr S₁ _ (S₂ r).2, hextr S₂ _ (S₁ r).2] at this
      simpa only [Module.End.mul_apply] using this
    have hcommR := fun g g' (hg : Commute A₀ g) (hg' : Commute A₀ g') =>
      commute_of_commute_of_isSkewAdjoint two_ne_zero hBRsymm hBRnd hA₀sk hA₀inj hskewR hg hg'
    exact squarefree_charpoly_of_commute hss₀ hcommR
  · -- `⇐`
    intro hsq Y hY hYX hYf
    refine ⟨hY, fun t ht => ?_, hYf⟩
    set Bm := adV d.QW Y
    have hBA : Bm * A = A * Bm := by
      have h := adV_commutator hY.1 hXg
      rw [hYX, sub_self] at h
      have h0 : adV d.QW (0 : CliffordAlgebra d.QW) = 0 := by ext; simp
      rw [h0] at h
      exact sub_eq_zero.mp h.symm
    have hPA : (specP d.QW t : Module.End F (Fin d.m → F)) * A =
        A * (specP d.QW t : Module.End F (Fin d.m → F)) :=
      (commute_iff_adV d.nondeg t hXg).mp (hX.2.1 t ht)
    have hPB := commute_of_squarefree_charpoly hsq (hcommR hPA) (hcommR hBA)
    refine (commute_iff_adV d.nondeg t hY.1).mpr (LinearMap.ext fun v => ?_)
    obtain ⟨k, hk, r, hr, rfl⟩ := hdecomp v
    have hkT : k ∈ commonFixed T := hker ▸ hk
    have hPk : specP d.QW t k = k := by
      have : k ∈ fixedSub t := (Submodule.mem_iInf _).mp hkT ⟨t, ht⟩
      exact (d.mem_fixedSub_iff).mp this
    have hBk : adV d.QW Y k = 0 := hYf k hkT
    have hr' := congrArg Subtype.val (LinearMap.congr_fun hPB.eq ⟨r, hr⟩)
    simp only [Module.End.mul_apply, LinearMap.restrict_apply] at hr'
    simp only [Module.End.mul_apply, map_add]
    erw [hPk, hBk]
    simp only [map_zero, zero_add]
    exact hr'

/-- **`ad` carries `𝔱⁰_♮(T_x)` onto Luo's `𝔱_♮(φ(T_x))`** for `x ∈ Γ(G,H)` (the hypothesis `hnat` of
`torusIntegralLie_toSO_of_germ_conj`): the first two clauses correspond (`mem_lieTorus_map_iff`,
`commonFixed_eq_fixedOf_map`), the third by `commClause_iff_squarefree`. -/
theorem isGammaEltLie_iff_isNat {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    (X : ↥(d.lieTorus (d.torusOf x))) :
    d.IsGammaEltLie (d.torusOf x) X ↔
      d.luoOf.IsNat ((d.torusOf x).map (d.toGbarU.comp d.diag)) (d.toSOLin (d.diagLie X)) := by
  have hXs : (X : CliffordAlgebra d.QW) ∈ soSub d.QW := X.2.1
  have hfst : d.luoOf.fstA (d.toSOLin (d.diagLie X)) = adV d.QW X := by
    rw [d.toSOLin_diagLie hXs.1]
    rfl
  have hsq : ∀ {B : Module.End F (Fin d.m → F)}, B = adV d.QW X →
      (Squarefree (LinearMap.charpoly (B.restrict (p := LinearMap.range B)
        (q := LinearMap.range B) (fun v _ => LinearMap.mem_range_self _ v))) ↔
      Squarefree (LinearMap.charpoly ((adV d.QW X).restrict (p := LinearMap.range (adV d.QW X))
        (q := LinearMap.range (adV d.QW X)) (fun v _ => LinearMap.mem_range_self _ v)))) := by
    rintro _ rfl
    rfl
  have hfix := d.commonFixed_eq_fixedOf_map (d.torusOf x)
  have hmem := d.mem_lieTorus_map_iff (d.torusOf x) hXs
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨hmem.mp h1, by rw [hfst, ← hfix]; exact h2, (hsq hfst).mpr ?_⟩
    exact (d.commClause_iff_squarefree hx h1 h2).mp h3
  · rintro ⟨h1, h2, h3⟩
    have h1' := hmem.mpr h1
    have h2' : LinearMap.ker (adV d.QW X) = commonFixed (d.torusOf x) := by
      rw [← hfst, hfix]; exact h2
    exact ⟨h1', h2', (d.commClause_iff_squarefree hx h1' h2').mpr ((hsq hfst).mp h3)⟩

variable (ψ : NontrivialAddChar F)

/-- **(L8) The torus integrals agree**, for a bijection of classes matching each torus with its
image (`IsNaturalTorusCorr`, as given by `gammaClass_equiv`) and the measures
`ν(T) dX`: on each torus, `ad` maps `𝔱⁰ = lieTorus T` onto Luo's `𝔱` (embedded diagonally), carries
`measLieTorus` (`exp`-compatible with the probability measure on `T(F)/A_{G,H}(F)`) to the
`exp`-compatible measure for the probability measure on `H''(F)`, `𝔱⁰_♮` (`IsGammaEltLie`) to `𝔱_♮`
(`IsNat`), `D^G` (`weylDiscLie` on `𝔤⁰` vs on `so(W) ⊕ so(V)`) and `Δ` to the same values, and (by
the hypothesis `hc`, i.e. `cTheta_toSO`) `c_θ` to `c_θ`; the representatives of the classes differ
by conjugation, which preserves the integrands and measures.  Proof:
`torusIntegralLie_toSO_of_germ_conj` with `isGammaEltLie_iff_isNat` and `germLie0_diagLie_conj`. -/
theorem torusIntegralLie_toSO (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    (e : GammaClass d ≃ d.luoOf.GammaClass)
    (hen : ∀ c, d.IsNaturalTorusCorr (Quot.out c).1 (Quot.out (e c)).1) :
    ∃ μT : ∀ T : d.luoOf.GammaTorus, Measure ↥(d.luoOf.lieTorus T.1),
      (∀ T, d.luoOf.IsExpCompatT T.1 (μT T)) ∧
      ∀ θ : ↥d.luoOf.lie → ℂ,
        IsLieQuasiCharacter d.luoOf.Gbar d.luoOf.lie d.luoOf.traceForm ψ θ →
        (∀ (T : d.GammaTorus) (X : CliffordAlgebra d.QW), d.IsGammaEltLie T.1 X →
          d.germLie0 ψ (θ ∘ d.toSO) (d.diagLie X) (d.orbitChoiceLie X) =
            d.luoOf.cTheta ψ θ (d.toSOLin (d.diagLie X))) →
        ∀ (c : GammaClass d) (s : ℝ), 0 < s →
          d.torusIntegralLie ψ (θ ∘ d.toSO) (Quot.out c).1 s =
            ∫ X : ↥(d.luoOf.lieTorus (Quot.out (e c)).1),
              d.luoOf.gammaIntegrand ψ θ (Quot.out (e c)).1 s X ∂μT (Quot.out (e c)) := by
  exact d.torusIntegralLie_toSO_of_germ_conj ψ (fun _ hx X => d.isGammaEltLie_iff_isNat hx X)
    (fun θ hθ x g hx X hX => d.germLie0_diagLie_conj ψ hW hV θ hθ x g hx X hX) e hen

end GGPData

end GSpinGGP
