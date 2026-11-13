/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LuoTorusConj
import GSpinGGP.TraceFormula.CThetaTransport

/-!
# The torus integrals of `θ ∘ ad` and of `θ` agree (step (L8) of `LuoTransfer`)

* `unitConj`, `conjCentralizerIso`: conjugation by `u ∈ G(F)` is an isomorphism of descent data
  `(Z_G(X), 𝔤_X) ≃ (Z_G(uXu⁻¹), 𝔤_{uXu⁻¹})`;
* `germLie_conj`: germs of a Lie quasi-character are conjugation invariant (the orbits matched by
  `Ad u`).
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
/-- Conjugation `a ↦ u a u⁻¹` by a unit, as an `F`-linear map. -/
def unitConj (u : Aˣ) : A →ₗ[F] A where
  toFun a := (u : A) * a * ((u⁻¹ : Aˣ) : A)
  map_add' a c := by simp [mul_add, add_mul]
  map_smul' r a := by simp

@[simp] theorem unitConj_apply (u : Aˣ) (a : A) :
    unitConj F u a = (u : A) * a * ((u⁻¹ : Aˣ) : A) := rfl

theorem unitConj_mul (u : Aˣ) (a c : A) :
    unitConj F u (a * c) = unitConj F u a * unitConj F u c := by
  simp [mul_assoc]

theorem unitConj_inv_unitConj (u : Aˣ) (a : A) : unitConj F u⁻¹ (unitConj F u a) = a := by
  simp [mul_assoc]

theorem unitConj_unitConj_inv (u : Aˣ) (a : A) : unitConj F u (unitConj F u⁻¹ a) = a := by
  simp [mul_assoc]

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
  CentralizerIso.ofSubalgebra ⊤ ⊤ (unitConj F u) (unitConj F u⁻¹) (fun _ _ => trivial)
    (fun _ _ => trivial) (by simp) (fun a _ c _ => unitConj_mul u a c)
    (fun a _ => unitConj_inv_unitConj u a) (fun a _ => unitConj_unitConj_inv u a)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun Y hY => by
      rw [mem_lieCentralizer_units_one] at hY ⊢
      obtain ⟨hY𝔤, hXY⟩ := mem_lieCentralizer.mp hY
      refine mem_lieCentralizer.mpr ⟨hG u hu Y hY𝔤, ?_⟩
      rw [← unitConj_mul, ← unitConj_mul, hXY])
    (fun Y hY => by
      rw [mem_lieCentralizer_units_one] at hY ⊢
      obtain ⟨hY𝔤, hXY⟩ := mem_lieCentralizer.mp hY
      refine mem_lieCentralizer.mpr ⟨?_, ?_⟩
      · have := hG u⁻¹ (inv_mem hu) Y hY𝔤
        rwa [inv_inv] at this
      · have h := congrArg (unitConj F u⁻¹) hXY
        rwa [unitConj_mul, unitConj_mul, unitConj_inv_unitConj] at h)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun v hv w hw => by
      rw [grpCentralizer_one] at hv ⊢
      have hw' : w = u * v * u⁻¹ := Units.ext (by rw [hw]; rfl)
      subst hw'
      refine ⟨G.mul_mem (G.mul_mem hu hv.1) (inv_mem hu), ?_⟩
      have h := congrArg (unitConj F u) hv.2
      rw [unitConj_mul, unitConj_mul] at h
      simpa [mul_assoc] using h)
    (fun v hv w hw => by
      rw [grpCentralizer_one] at hv ⊢
      have hw' : w = u⁻¹ * v * u⁻¹⁻¹ := Units.ext (by rw [hw]; rfl)
      subst hw'
      refine ⟨G.mul_mem (G.mul_mem (inv_mem hu) hv.1) (inv_mem (inv_mem hu)), ?_⟩
      have h := congrArg (unitConj F u⁻¹) hv.2
      rw [unitConj_mul, unitConj_mul, unitConj_inv_unitConj] at h
      simpa [mul_assoc] using h)
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
    have hcont : Continuous (unitConj F u) := IsModuleTopology.continuous_of_linearMap _
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

section OrbitNuConj

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
  {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- `x ⊥ span{e}` iff `b(e, x) = 0`. -/
theorem mem_orthogonal_span_singleton_iff (B : LinearMap.BilinForm F V) {e x : V} :
    x ∈ B.orthogonal (Submodule.span F {e}) ↔ B e x = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    exact h e (Submodule.mem_span_singleton_self e)
  · intro h n hn
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hn
    change B (c • e) x = 0
    rw [map_smul, LinearMap.smul_apply, h, smul_zero]

/-- One direction of `isInOrbitNu_conj_iff`. -/
theorem isInOrbitNu_conj_of {Q : QuadraticForm F V} (σ : V ≃ₗ[F] V) (hσ : ∀ v, Q (σ v) = Q v)
    {U : Submodule F V} {ν : F} {N : V →ₗ[F] V} (h : IsInOrbitNu Q U ν N) :
    IsInOrbitNu Q (U.map (σ : V →ₗ[F] V)) ν (σ.conj N) := by
  obtain ⟨d₀, U₁, h1, h2, h3, h4, h5, h6, h7, ⟨u, hu, hu'⟩, e, he, hQe, hsplit⟩ := h
  have hb : ∀ a c, bform Q (σ a) (σ c) = bform Q a c := fun a c => by
    simp only [bform, QuadraticMap.associated_apply]
    rw [← map_add, hσ, hσ, hσ]
  have hconj : ∀ v, σ.conj N v = σ (N (σ.symm v)) := fun v => rfl
  have hpow : ∀ k : ℕ, ∀ v, (σ.conj N ^ k) v = σ ((N ^ k) (σ.symm v)) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih => intro v; rw [pow_succ, Module.End.mul_apply, ih, hconj, pow_succ,
        Module.End.mul_apply, LinearEquiv.symm_apply_apply]
  refine ⟨σ d₀, U₁.map (σ : V →ₗ[F] V), ⟨d₀, h1, rfl⟩, by rwa [hσ], Submodule.map_mono h3,
    ?_, ?_, ?_, ?_, ⟨σ u, ⟨u, hu, rfl⟩, ?_⟩, σ e, ⟨e, he, rfl⟩, by rw [hσ, hQe], ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    rw [LinearEquiv.coe_coe, hb]
    exact h4 w hw
  · rw [← h5, Submodule.map_sup, Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe]
  · rw [hconj, LinearEquiv.symm_apply_apply, h6, map_zero]
  · rintro _ ⟨w, hw, rfl⟩
    rw [LinearEquiv.coe_coe, hconj, LinearEquiv.symm_apply_apply]
    exact ⟨_, h7 w hw, rfl⟩
  · rw [LinearEquiv.finrank_map_eq, hpow, LinearEquiv.symm_apply_apply]
    exact fun h0 => hu' (σ.injective (by rw [h0, map_zero]))
  · set S := U₁ ⊓ (bform Q).orthogonal (Submodule.span F {e})
    have hS : U₁.map (σ : V →ₗ[F] V) ⊓ (bform Q).orthogonal (Submodule.span F {σ e}) =
        S.map (σ : V →ₗ[F] V) := by
      ext x
      simp only [Submodule.mem_inf, S, Submodule.mem_map_equiv, mem_orthogonal_span_singleton_iff]
      rw [← hb e (σ.symm x), LinearEquiv.apply_symm_apply]
    rw [hS]
    let iso : (Q.comp S.subtype).IsometryEquiv (Q.comp (S.map (σ : V →ₗ[F] V)).subtype) :=
      { toLinearEquiv := σ.submoduleMap S
        map_app' := fun v => hσ v }
    unfold IsSplitQF at hsplit ⊢
    rw [← LinearEquiv.finrank_eq iso.toLinearEquiv, ← QuadClassify.wittIndex_eq_of_isometryEquiv iso]
    exact hsplit

/-- **Luo's orbit `O_ν` is intrinsic**: an isometry `σ` of `Q` carries `N ∈ O_ν` on `U` to
`σ N σ⁻¹ ∈ O_ν` on `σ U`. -/
theorem isInOrbitNu_conj_iff {Q : QuadraticForm F V} (σ : V ≃ₗ[F] V) (hσ : ∀ v, Q (σ v) = Q v)
    {U : Submodule F V} {ν : F} {N : V →ₗ[F] V} :
    IsInOrbitNu Q (U.map (σ : V →ₗ[F] V)) ν (σ.conj N) ↔ IsInOrbitNu Q U ν N := by
  refine ⟨fun h => ?_, isInOrbitNu_conj_of σ hσ⟩
  have hσ' : ∀ v, Q (σ.symm v) = Q v := fun v => by
    rw [← hσ (σ.symm v), LinearEquiv.apply_symm_apply]
  have := isInOrbitNu_conj_of σ.symm hσ' h
  rwa [← Submodule.map_comp, show ((σ.symm : V →ₗ[F] V) ∘ₗ (σ : V →ₗ[F] V)) = LinearMap.id
    from by ext; simp, Submodule.map_id,
    show σ.symm.conj (σ.conj N) = N from by ext v; simp [LinearEquiv.conj_apply]] at this

end OrbitNuConj

namespace LuoDatum

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (L : LuoDatum F)

/-- The trace form is invariant under conjugation by a unit of `End W × End V`. -/
theorem traceForm_unitConj (u : L.Ambˣ) (Y Z : L.Amb) :
    L.traceForm (unitConj F u Y) (unitConj F u Z) = L.traceForm Y Z := by
  have hW : L.fstA ((u⁻¹ : L.Ambˣ) : L.Amb) * L.fstA (u : L.Amb) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hV : L.sndA ((u⁻¹ : L.Ambˣ) : L.Amb) * L.sndA (u : L.Amb) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  simp only [traceForm, LinearMap.mk₂_apply, ← map_mul, ← unitConj_mul]
  simp only [unitConj_apply, map_mul]
  have e1 : LinearMap.trace F L.W (L.fstA (u : L.Amb) * (L.fstA Y * L.fstA Z) *
      L.fstA ((u⁻¹ : L.Ambˣ) : L.Amb)) = LinearMap.trace F L.W (L.fstA Y * L.fstA Z) := by
    rw [LinearMap.trace_mul_comm, ← mul_assoc, hW, one_mul]
  have e2 : LinearMap.trace F L.V (L.sndA (u : L.Amb) * (L.sndA Y * L.sndA Z) *
      L.sndA ((u⁻¹ : L.Ambˣ) : L.Amb)) = LinearMap.trace F L.V (L.sndA Y * L.sndA Z) := by
    rw [LinearMap.trace_mul_comm, ← mul_assoc, hV, one_mul]
  rw [e1, e2]

/-- `diagU p ∈ Ḡ` for `p ∈ SO(W)`. -/
theorem diagU_mem_Gbar {p : (Module.End F L.W)ˣ} (hp : p ∈ SOu L.QW) : L.diagU p ∈ L.Gbar :=
  Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr (by rw [unitFst_diagU]; exact hp),
    Subgroup.mem_comap.mpr (by rw [unitSnd_diagU]; exact L.extU_mem_SOu hp)⟩

/-- `p ∈ SO(W)` as a linear isometry. -/
abbrev soEquiv {U : Type*} [AddCommGroup U] [Module F U] (p : (Module.End F U)ˣ) : U ≃ₗ[F] U :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv F U p

theorem fstA_unitConj_diagU (p : (Module.End F L.W)ˣ) (Y : L.Amb) :
    L.fstA (unitConj F (L.diagU p) Y) = (soEquiv p).conj (L.fstA Y) :=
  LinearMap.ext fun _ => rfl

theorem sndA_unitConj_diagU (p : (Module.End F L.W)ˣ) (Y : L.Amb) :
    L.sndA (unitConj F (L.diagU p) Y) = (soEquiv (Units.map L.extGrp p)).conj (L.sndA Y) :=
  LinearMap.ext fun _ => rfl

theorem ker_conj {U : Type*} [AddCommGroup U] [Module F U] (σ : U ≃ₗ[F] U) (N : Module.End F U) :
    LinearMap.ker (σ.conj N) = (LinearMap.ker N).map (σ : U →ₗ[F] U) := by
  ext x
  rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker, LinearEquiv.conj_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    LinearEquiv.map_eq_zero_iff]

/-- **Luo's recipe is invariant under `SO(W)`**: conjugating by `diagU p`, `p ∈ SO(W)`, and
moving `U` by `p` (`isInOrbitNu_conj_iff` on `W` and on `V`, where `p` acts as `p ⊕ 1`). -/
theorem orbitSpec_unitConj_diagU {p : (Module.End F L.W)ˣ} (hp : p ∈ SOu L.QW)
    (U : Submodule F L.W) (Y : L.Amb) :
    L.OrbitSpec (U.map (soEquiv p : L.W →ₗ[F] L.W)) (unitConj F (L.diagU p) Y) ↔
      L.OrbitSpec U Y := by
  have hpV := L.extU_mem_SOu hp
  have hprod : (U.map (soEquiv p : L.W →ₗ[F] L.W)).prod (⊤ : Submodule F L.Zs) =
      (U.prod ⊤).map (soEquiv (Units.map L.extGrp p) : L.V →ₗ[F] L.V) := by
    ext ⟨w, z⟩
    rw [Submodule.mem_map_equiv, Submodule.mem_prod, Submodule.mem_prod, Submodule.mem_map_equiv]
    simp only [Submodule.mem_top, and_true]
    rfl
  unfold OrbitSpec
  rw [hprod, LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq, fstA_unitConj_diagU,
    sndA_unitConj_diagU, isInOrbitNu_conj_iff (soEquiv p) (fun v => hp.1 v),
    isInOrbitNu_conj_iff (soEquiv (Units.map L.extGrp p)) (fun v => hpV.1 v)]

/-- **Luo's `c_θ` is invariant under conjugation by `SO(W)`** (diagonally in `Ḡ`), given
uniqueness of the regular germ coefficients at `M` (`germLie_unique_SO`), of the orbit selected by
Luo's recipe at `M' = p M p⁻¹` (`huniq'`), orbit measures at `M'` (`hum`) and openness of the
regular set of `𝔤_{M'}` (`hopen`): `germLie_conj` for `Ad(diagU p)`, which carries the recipe at
`M` to the recipe at `M'` (`orbitSpec_unitConj_diagU`, `ker M' = p ker M`). -/
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
      (LinearMap.ker (L.fstA M)).map (soEquiv p : L.W →ₗ[F] L.W) := by
    rw [fstA_unitConj_diagU, ker_conj]
  have hspecK : ∀ O, (∃ Y ∈ nilOrbitSet (E O),
      L.OrbitSpec (LinearMap.ker (L.fstA (unitConj F (L.diagU p) M))) (Y : L.Amb)) ↔
      ∃ Y ∈ nilOrbitSet O, L.OrbitSpec (LinearMap.ker (L.fstA M)) (Y : L.Amb) := fun O => by
    rw [hspec O, hker]
    exact exists_congr fun Y => and_congr_right fun _ => L.orbitSpec_unitConj_diagU hp _ _
  unfold cTheta
  rw [← hgerm (L.orbitChoice M)]
  congr 1
  unfold orbitChoice
  by_cases h : ∃ O ∈ NilReg (lieGrpCentralizer L.Gbar M) (lieCentralizer L.lie M),
      ∃ Y ∈ nilOrbitSet O, L.OrbitSpec (LinearMap.ker (L.fstA M)) (Y : L.Amb)
  · have h' : ∃ O ∈ NilReg (lieGrpCentralizer L.Gbar (unitConj F (L.diagU p) M))
        (lieCentralizer L.lie (unitConj F (L.diagU p) M)), ∃ Y ∈ nilOrbitSet O,
          L.OrbitSpec (LinearMap.ker (L.fstA (unitConj F (L.diagU p) M))) (Y : L.Amb) :=
      ⟨E h.choose, (hreg _).mpr h.choose_spec.1, (hspecK _).mpr h.choose_spec.2⟩
    simp only [h, h', ↓reduceDIte]
    exact huniq' _ _ h'.choose_spec.1 ((hreg _).mpr h.choose_spec.1) h'.choose_spec.2
      ((hspecK _).mpr h.choose_spec.2)
  · have h' : ¬ ∃ O ∈ NilReg (lieGrpCentralizer L.Gbar (unitConj F (L.diagU p) M))
        (lieCentralizer L.lie (unitConj F (L.diagU p) M)), ∃ Y ∈ nilOrbitSet O,
          L.OrbitSpec (LinearMap.ker (L.fstA (unitConj F (L.diagU p) M))) (Y : L.Amb) := by
      rintro ⟨O', hO', hs⟩
      refine h ⟨E.symm O', (hreg _).mp ?_, (hspecK _).mp ?_⟩
      · rwa [Equiv.apply_symm_apply]
      · rwa [Equiv.apply_symm_apply]
    simp only [h, h', ↓reduceDIte]
    exact hzero.symm

end LuoDatum

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)
  (ψ : NontrivialAddChar F)

/-- **The regular set of `(so(W) ⊕ so(V))_{ad D}` is open** for semisimple `D ∈ 𝔤⁰`: the image of
the open regular set of `𝔤⁰_D` (`isOpen_setOf_isRegularSS_lieCentralizer_lieZero`) under the
homeomorphism `ad` (`adCentralizerIso`). -/
theorem isOpen_setOf_isRegularSS_lieCentralizer_toSOLin (hW : ¬ IsHypPlane d.QW)
    (hV : ¬ IsHypPlane d.QV) {D : d.ambient} (hD : D ∈ d.lieZero) (hss : IsSS F D) :
    IsOpen {Z : ↥(lieCentralizer d.luoOf.lie (d.toSOLin D)) |
      IsRegularSS (lieCentralizer d.luoOf.lie (d.toSOLin D)) (Z : d.luoOf.Amb)} := by
  let ι := d.adCentralizerIso hW hV hD
    (d.luoOf.scalarUnit (formConst_ne_zero (Module.finrank F (Fin d.m → F)))
      (formConst_ne_zero (Module.finrank F d.V)))
    (fun _ hY _ hZ => d.scaleForm_traceForm_toSOLin hY hZ)
  have e𝔤₀ : lieCentralizer (lieCentralizer d.lieZero D) ((1 : d.ambientˣ) : d.ambient)
      = lieCentralizer d.lieZero D := by rw [Units.val_one, lieCentralizer_one]
  have e𝔤₁ : lieCentralizer (lieCentralizer d.luoOf.lie (d.toSOLin D))
      ((1 : d.luoOf.Ambˣ) : d.luoOf.Amb) = lieCentralizer d.luoOf.lie (d.toSOLin D) := by
    rw [Units.val_one, lieCentralizer_one]
  have hopen₀ : IsOpen {Z : ↥(lieCentralizer (lieCentralizer d.lieZero D)
      ((1 : d.ambientˣ) : d.ambient)) | IsRegularSS (lieCentralizer (lieCentralizer d.lieZero
        D) ((1 : d.ambientˣ) : d.ambient)) (Z : d.ambient)} := by
    rw [e𝔤₀]
    exact d.isOpen_setOf_isRegularSS_lieCentralizer_lieZero hD hss
  have hopen' : IsOpen {Z : ↥(lieCentralizer (lieCentralizer d.luoOf.lie
      (d.toSOLin D)) ((1 : d.luoOf.Ambˣ) : d.luoOf.Amb)) |
      IsRegularSS (lieCentralizer (lieCentralizer d.luoOf.lie (d.toSOLin D))
        ((1 : d.luoOf.Ambˣ) : d.luoOf.Amb)) (Z : d.luoOf.Amb)} := by
    convert hopen₀.preimage ι.continuous_linEquiv_symm using 1
    ext Z'
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [← ι.isRegularSS_iff _ (ι.linEquiv.symm Z').2, ← CentralizerIso.linEquiv_apply,
      LinearEquiv.apply_symm_apply]
  rw [← e𝔤₁]
  exact hopen'

/-- **At most one regular nilpotent orbit of `(so(W) ⊕ so(V))_{ad X}` meets Luo's recipe**, for
`X ∈ 𝔱⁰_♮` of a torus of `Γ(G,H)`: `orbitSpecAt_orbit_unique` transported along the orbit map of
`exists_nilOrbitEquiv_toSOLin` (for any `ψ`; the statement does not involve it). -/
theorem orbitSpec_orbit_unique_toSOLin (ψ : NontrivialAddChar F) (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
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
  have huniq := d.orbitSpec_orbit_unique_toSOLin ψ hW hV T' hX'
  have hM' := d.toSOLin_diagLie_conj g hX.1.1
  rw [hM'] at hopen huniq ⊢
  exact d.luoOf.cTheta_unitConj_diagU d.nondeg_QV ψ hθ (d.specPU_mem_SOu g) (d.toSO_mem ⟨_, hD⟩)
    (d.isSS_toSOLin hD hssD) hopen (fun _ _ _ h1 h2 => d.isOrbitMeasure_unique_luo _ h1 h2) huniq

/-- **The germs at `X` and at `g X g⁻¹` agree** (the hypothesis `hgerm` of
`torusIntegralLie_toSO_of_germ_conj`), for `x, x' ∈ Γ(G,H)` with `T_{x'} = g T_x g⁻¹` and
`X ∈ 𝔱⁰_♮(T_x)`: both germs are Luo's `c_θ` (`cTheta_toSO`), and `c_θ(ad(gXg⁻¹)) = c_θ(ad X)`
(`cTheta_toSOLin_diagLie_conj`). -/
theorem germLie0_diagLie_conj (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    (θ : ↥d.luoOf.lie → ℂ)
    (hθ : IsLieQuasiCharacter d.luoOf.Gbar d.luoOf.lie d.luoOf.traceForm ψ θ)
    (x x' g : ↥(GSpin d.QW)) (hx : d.IsGammaElt x) (hx' : d.IsGammaElt x')
    (hT : d.torusOf x' = (d.torusOf x).map (MulAut.conj g).toMonoidHom)
    (X : CliffordAlgebra d.QW) (hX : d.IsGammaEltLie (d.torusOf x) X) :
    d.germLie0 ψ (θ ∘ d.toSO)
        (d.diagLie (((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X *
          (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)))
        (d.orbitChoiceLie (((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X *
          (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))) =
      d.germLie0 ψ (θ ∘ d.toSO) (d.diagLie X) (d.orbitChoiceLie X) := by
  have hX' : d.IsGammaEltLie (d.torusOf x') (((g : (CliffordAlgebra d.QW)ˣ) :
      CliffordAlgebra d.QW) * X *
      (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) := by
    rw [hT]
    exact d.isGammaEltLie_conj g hX
  rw [d.cTheta_toSO ψ hW hV hθ ⟨_, x', hx', rfl⟩ _ hX', d.cTheta_toSO ψ hW hV hθ ⟨_, x, hx, rfl⟩ _ hX]
  exact d.cTheta_toSOLin_diagLie_conj ψ hW hV hθ ⟨_, x, hx, rfl⟩ ⟨_, x', hx', rfl⟩ g hX hX'

end GGPData

end GSpinGGP
