/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.OrbitSpecUnique
import GSpinGGP.TraceFormula.ExpIntertwine
import GSpinGGP.TraceFormula.LuoJLie
import GSpinGGP.TraceFormula.JHatScale
import GSpinGGP.Literature.HarishChandra
import TauCeti.LinearAlgebra.CliffordAlgebra.ScalarTrace.Basic

/-!
# Transport of local expansions from `so(W) ⊕ so(V)` to `𝔤⁰` (steps (L6), (L7) of `LuoTransfer`)

For `X ∈ 𝔱⁰_♮`, local expansions of a quasi-character `θ` on `so(W) ⊕ so(V)` at `ad X` (Luo's
normalization: the trace form `B = ½ (tr_W + tr_V)`) give local expansions of `θ ∘ ad` on
`𝔤⁰ = so_Cliff(W) ⊕ so_Cliff(V)` at `X` (the trace form `bilin` of `C(W) × C(V)`).  The map of
nilpotent orbits is `ad`, followed by multiplication by `c = (2^{dim W}/4 · 1, 2^{dim V}/4 · 1)`,
which turns `bilin` into `B` (`scaleForm_traceForm_toSOLin`).

* `LuoDatum.conj_mem_lie_of_mem_Gbar`, `eventually_expA_mem_Gbar`,
  `LuoDatum.eventually_mem_lie_of_expA_mem`: `Ḡ(F) = SO(W) × SO(V)` and `so(W) ⊕ so(V)` correspond
  under `exp` near `0`; hence orbit measures on centralizers are unique
  (`isOrbitMeasure_unique_luo`).
* `adCentralizerIso`: `ad : (Z_G(D), 𝔤⁰_D, bilin) ≃ (Ḡ_{ad D}, 𝔤_{ad D}, B(c ·, ·))` is an
  isomorphism of descent data (`CentralizerIso`).
* `isOpen_setOf_isRegularSS_lieCentralizer_lieZero`: the regular set of `𝔤⁰_D` is open (with
  `restrictForm_lieCentralizer_nondegenerate_of_isSS`, the remaining hypotheses of `jHat_map`).
* `eight_mul_scalarTrace_mul`: `8 τ(Y Z) = tr(ad Y ad Z)` on `so_Cliff(V)` (`τ` the scalar part).
* `cTheta_toSO_of_germUnique`: the conclusion of `cTheta_toSO` from uniqueness of the regular
  coefficients of Lie-algebra local expansions on `𝔤⁰` at `X` alone.
-/

noncomputable section

open MeasureTheory Filter Topology

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-! ## `exp` on `Ḡ = SO(W) × SO(V)` -/

namespace LuoDatum

variable (L : LuoDatum F)

/-- Conjugation by `Ḡ(F)` preserves `so(W) ⊕ so(V)`. -/
theorem conj_mem_lie_of_mem_Gbar :
    ∀ g ∈ L.Gbar, ∀ Y ∈ L.lie, ((g : L.Ambˣ) : L.Amb) * Y * ((g⁻¹ : L.Ambˣ) : L.Amb) ∈ L.lie := by
  intro g hg Y hY
  refine ⟨?_, ?_⟩
  · have h := conj_mem_skewAdjoint (u := (L.unitFst g)⁻¹) (inv_mem hg.1) hY.1
    rw [inv_inv] at h
    rw [map_mul, map_mul]
    exact h
  · have h := conj_mem_skewAdjoint (u := (L.unitSnd g)⁻¹) (inv_mem hg.2) hY.2
    rw [inv_inv] at h
    rw [map_mul, map_mul]
    exact h

/-- **The logarithm of `Ḡ(F)` near `1` lies in `so(W) ⊕ so(V)`**: for `Y` near `0`, `e^Y ∈ Ḡ(F)`
forces `Y` skew on each factor (`eventually_isAdjointPair_neg_of_isOrthogonal_expA`). -/
theorem eventually_mem_lie_of_expA_mem :
    ∀ᶠ Y in 𝓝 (0 : L.Amb), ∀ g ∈ L.Gbar, ((g : L.Ambˣ) : L.Amb) = expA F Y → Y ∈ L.lie := by
  haveI : IsModuleTopology F (Module.End F L.W) := ⟨rfl⟩
  haveI : IsModuleTopology F (Module.End F L.V) := ⟨rfl⟩
  have hf := eventually_map_expA (F := F) (A := L.Amb) L.fstA.toLinearMap
    (fun X n => map_pow L.fstA X n)
  have hs := eventually_map_expA (F := F) (A := L.Amb) L.sndA.toLinearMap
    (fun X n => map_pow L.sndA X n)
  have hcf : Continuous L.fstA := IsModuleTopology.continuous_of_linearMap L.fstA.toLinearMap
  have hcs : Continuous L.sndA := IsModuleTopology.continuous_of_linearMap L.sndA.toLinearMap
  have e1 := (hcf.tendsto' 0 0 (map_zero _)).eventually
    (eventually_isAdjointPair_neg_of_isOrthogonal_expA (F := F) (bform L.QW))
  have e2 := (hcs.tendsto' 0 0 (map_zero _)).eventually
    (eventually_isAdjointPair_neg_of_isOrthogonal_expA (F := F) (bform L.QV))
  filter_upwards [hf, hs, e1, e2] with Y h1 h2 k1 k2 g hg hgY
  refine ⟨?_, ?_⟩
  · change L.fstA Y ∈ (bform L.QW).skewAdjointSubmodule
    rw [LinearMap.mem_skewAdjointSubmodule]
    refine k1 ?_
    have e : expA F (L.fstA Y) = ((L.unitFst g : (Module.End F L.W)ˣ) : Module.End F L.W) := by
      have := h1
      simp only [AlgHom.toLinearMap_apply] at this
      rw [← this, ← hgY]
      rfl
    rw [e]
    exact isOrthogonal_of_mem_SOu hg.1
  · change L.sndA Y ∈ (bform L.QV).skewAdjointSubmodule
    rw [LinearMap.mem_skewAdjointSubmodule]
    refine k2 ?_
    have e : expA F (L.sndA Y) = ((L.unitSnd g : (Module.End F L.V)ˣ) : Module.End F L.V) := by
      have := h2
      simp only [AlgHom.toLinearMap_apply] at this
      rw [← this, ← hgY]
      rfl
    rw [e]
    exact isOrthogonal_of_mem_SOu hg.2

end LuoDatum

namespace GGPData

variable (d : GGPData F)

/-- **`e^Y ∈ Ḡ(F)` for `Y ∈ so(W) ⊕ so(V)` near `0`**: `Y = ad Z` with `Z ∈ 𝔤⁰` near `0`
(`toSOCLE`), `e^Z ∈ G(F)` (`eventually_expA_mem_G`) and its image in `Ḡ(F)` is
`e^{ad Z}` (`eventually_toGbarU_eq_expA_toSOLin`). -/
theorem eventually_expA_mem_Gbar :
    ∀ᶠ Y in 𝓝 (0 : d.luoOf.Amb), Y ∈ d.luoOf.lie →
      ∃ g ∈ d.luoOf.Gbar, ((g : d.luoOf.Ambˣ) : d.luoOf.Amb) = expA F Y := by
  have hP : ∀ᶠ Z in 𝓝 (0 : d.ambient), Z ∈ d.lie → ∃ g : ↥d.G,
      ((d.toGbarU g : d.luoOf.Ambˣ) : d.luoOf.Amb) = expA F (d.toSOLin Z) := by
    filter_upwards [eventually_expA_mem_G d, d.eventually_toGbarU_eq_expA_toSOLin] with Z h1 h2 hZ
    obtain ⟨g, hg⟩ := h1 hZ
    exact ⟨g, h2 hZ g hg⟩
  obtain ⟨U, hU, hUP⟩ := hP.exists_mem
  have hc : Continuous (fun Y : ↥d.luoOf.lie => ((d.toSOCLE.symm Y : ↥d.lieZero) : d.ambient)) :=
    continuous_subtype_val.comp d.toSOCLE.symm.continuous
  have hV : (fun Y : ↥d.luoOf.lie => ((d.toSOCLE.symm Y : ↥d.lieZero) : d.ambient)) ⁻¹' U ∈
      𝓝 (0 : ↥d.luoOf.lie) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU)
  rw [mem_nhds_subtype] at hV
  obtain ⟨V, hV0, hVs⟩ := hV
  have hV0' : V ∈ 𝓝 (0 : d.luoOf.Amb) := by simpa using hV0
  filter_upwards [hV0'] with Y hYV hY
  have hZ := hVs (show (⟨Y, hY⟩ : ↥d.luoOf.lie) ∈ Subtype.val ⁻¹' V from hYV)
  set Z := d.toSOCLE.symm ⟨Y, hY⟩
  obtain ⟨g, hg⟩ := hUP _ hZ (d.lieZero_le_lie Z.2)
  refine ⟨d.toGbarU g, d.toGbarU_mem g, ?_⟩
  rw [hg]
  congr 1
  exact d.toSOLin_toSO_symm ⟨Y, hY⟩

/-- **Orbit measures on centralizers in `so(W) ⊕ so(V)` are unique**, for any form `b`
(`isOrbitMeasure_unique_lieCentralizer` with `Ḡ(F) ↔ so(W) ⊕ so(V)` under `exp`). -/
theorem isOrbitMeasure_unique_luo (Y : d.luoOf.Amb) {b : LinearMap.BilinForm F d.luoOf.Amb}
    {ψ : NontrivialAddChar F}
    {O : NilOrbit (lieGrpCentralizer d.luoOf.Gbar Y) (lieCentralizer d.luoOf.lie Y)}
    {μ ν : Measure ↥(lieCentralizer d.luoOf.lie Y)}
    (hμ : IsOrbitMeasure (lieGrpCentralizer d.luoOf.Gbar Y) (lieCentralizer d.luoOf.lie Y) b ψ O μ)
    (hν : IsOrbitMeasure (lieGrpCentralizer d.luoOf.Gbar Y) (lieCentralizer d.luoOf.lie Y) b ψ O
      ν) :
    μ = ν :=
  isOrbitMeasure_unique_lieCentralizer d.luoOf.conj_mem_lie_of_mem_Gbar d.eventually_expA_mem_Gbar
    d.luoOf.eventually_mem_lie_of_expA_mem Y hμ hν

end GGPData

/-! ## `ad` as an isomorphism of descent data at a point of `𝔤⁰` -/

theorem mem_lieCentralizer_units_one {A : Type*} [Ring A] [Algebra F A] {𝔤 : LieSubalgebra F A}
    {Y : A} : Y ∈ lieCentralizer 𝔤 ((1 : Aˣ) : A) ↔ Y ∈ 𝔤 := by
  rw [Units.val_one, lieCentralizer_one]

namespace GGPData

variable (d : GGPData F)

/-- `D`, `Y ∈ 𝔤⁰` commute iff `ad D`, `ad Y` do. -/
theorem commute_iff_toSOLin {D Y : d.ambient} (hD : D ∈ d.lieZero) (hY : Y ∈ d.lieZero) :
    D * Y = Y * D ↔ d.toSOLin D * d.toSOLin Y = d.toSOLin Y * d.toSOLin D := by
  rw [← sub_eq_zero, ← sub_eq_zero (a := d.toSOLin D * _), ← d.toSOLin_commutator hD hY]
  have hc : D * Y - Y * D ∈ d.lieZero := by
    have := d.lieZero.lie_mem hD hY
    rwa [Ring.lie_def] at this
  exact ⟨fun h => by rw [h, map_zero],
    fun h => d.eq_of_toSOLin_eq hc (zero_mem _) (by rw [h, map_zero])⟩

/-- `ad Y ∈ (so(W) ⊕ so(V))_{ad D}` iff `Y ∈ 𝔤⁰_D`, for `Y ∈ 𝔤⁰`. -/
theorem toSOLin_mem_lieCentralizer_iff {D Y : d.ambient} (hD : D ∈ d.lieZero)
    (hY : Y ∈ d.lieZero) :
    d.toSOLin Y ∈ lieCentralizer d.luoOf.lie (d.toSOLin D) ↔ Y ∈ lieCentralizer d.lieZero D := by
  rw [mem_lieCentralizer, mem_lieCentralizer, ← d.commute_iff_toSOLin hD hY]
  exact and_congr_left' ⟨fun _ => hY, fun _ => d.toSO_mem ⟨Y, hY⟩⟩

/-- Every element of `so(W) ⊕ so(V)` is `ad Y` for some `Y ∈ 𝔤⁰`. -/
theorem exists_toSOLin_eq {M : d.luoOf.Amb} (hM : M ∈ d.luoOf.lie) :
    ∃ Y ∈ d.lieZero, d.toSOLin Y = M :=
  ⟨_, (d.toSO.symm ⟨M, hM⟩).2, d.toSOLin_toSO_symm ⟨M, hM⟩⟩

/-- Abelianness is transported by `ad` between Lie subalgebras of `𝔤⁰` and of `so(W) ⊕ so(V)`
that correspond. -/
theorem isLieAbelian_iff_of_toSOLin {L₀ : LieSubalgebra F d.ambient}
    {L₁ : LieSubalgebra F d.luoOf.Amb} (h₀ : ∀ Y ∈ L₀, Y ∈ d.lieZero)
    (h₁ : ∀ M ∈ L₁, M ∈ d.luoOf.lie) (h : ∀ Y ∈ d.lieZero, d.toSOLin Y ∈ L₁ ↔ Y ∈ L₀) :
    IsLieAbelian L₁ ↔ IsLieAbelian L₀ := by
  rw [isLieAbelian_iff_forall_commute, isLieAbelian_iff_forall_commute]
  constructor
  · intro hab Y₁ m₁ Y₂ m₂
    exact (d.commute_iff_toSOLin (h₀ _ m₁) (h₀ _ m₂)).mpr
      (hab _ ((h _ (h₀ _ m₁)).mpr m₁) _ ((h _ (h₀ _ m₂)).mpr m₂))
  · intro hab M₁ m₁ M₂ m₂
    obtain ⟨Y₁, hY₁, rfl⟩ := d.exists_toSOLin_eq (h₁ _ m₁)
    obtain ⟨Y₂, hY₂, rfl⟩ := d.exists_toSOLin_eq (h₁ _ m₂)
    exact (d.commute_iff_toSOLin hY₁ hY₂).mp (hab _ ((h _ hY₁).mp m₁) _ ((h _ hY₂).mp m₂))

open Classical in
/-- `u ↦ P(u)` on `G(F)`, extended by `1`. -/
def toGbarFun (u : d.ambientˣ) : d.luoOf.Ambˣ :=
  if h : u ∈ d.G then d.toGbarU ⟨u, h⟩ else 1

theorem toGbarFun_of_mem {u : d.ambientˣ} (h : u ∈ d.G) : d.toGbarFun u = d.toGbarU ⟨u, h⟩ := by
  simp [toGbarFun, h]

/-- `D ∈ 𝔤⁰` commutes with `g ∈ G(F)` iff `ad D` commutes with `P(g)`. -/
theorem toGbarU_mul_comm_iff (g : ↥d.G) {D : d.ambient} (hD : D ∈ d.lieZero) :
    ((d.toGbarU g : d.luoOf.Ambˣ) : d.luoOf.Amb) * d.toSOLin D =
        d.toSOLin D * ((d.toGbarU g : d.luoOf.Ambˣ) : d.luoOf.Amb) ↔
      ((g : d.ambientˣ) : d.ambient) * D = D * ((g : d.ambientˣ) : d.ambient) := by
  have hc := d.toSOLin_conj g (d.lieZero_le_lie hD)
  have hD' := d.conj_mem_lie0 g hD
  constructor
  · intro h
    have e : d.toSOLin (((g : d.ambientˣ) : d.ambient) * D *
        (((g : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient)) = d.toSOLin D := by
      rw [hc, h, mul_assoc, Units.mul_inv, mul_one]
    have := d.eq_of_toSOLin_eq hD' hD e
    conv_rhs => rw [← this]
    simp [mul_assoc]
  · intro h
    have e : ((g : d.ambientˣ) : d.ambient) * D *
        (((g : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) = D := by
      rw [h, mul_assoc, Units.mul_inv, mul_one]
    rw [e] at hc
    exact ((Units.eq_mul_inv_iff_mul_eq _).mp hc).symm

/-- **`ad : 𝔤⁰_D → (so(W) ⊕ so(V))_{ad D}` is an isomorphism of descent data** (at `x = y = 1`),
for `D ∈ 𝔤⁰` and a central unit `c` of `End W × End V` with
`B(c · ad Y, ad Z) = bilin(Y, Z)` on `𝔤⁰` (`hform`; `B` the trace form): `ad` is bijective,
preserves brackets (`toSOLin_commutator`), nilpotency and semisimplicity (`isNilpotent_toSOLin_iff`,
`isSS_toSOLin_iff`), and near `0` the charts (`P(e^Y) = e^{ad Y}`,
`eventually_toGbarU_eq_expA_toSOLin`); on groups `Z_G(D)(F) → Ḡ_{ad D}(F)` is onto because
`G(F) → Ḡ(F)` is (`toGbar_surjective`) and `ad` is injective on `𝔤⁰`. -/
def adCentralizerIso (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) {D : d.ambient}
    (hD : D ∈ d.lieZero) (c : d.luoOf.Ambˣ)
    (hform : ∀ Y ∈ d.lieZero, ∀ Z ∈ d.lieZero,
      scaleForm d.luoOf.traceForm (c : d.luoOf.Amb) (d.toSOLin Y) (d.toSOLin Z) = d.bilin Y Z) :
    CentralizerIso (lieGrpCentralizer d.G D) (lieCentralizer d.lieZero D) d.bilin
      (lieGrpCentralizer d.luoOf.Gbar (d.toSOLin D)) (lieCentralizer d.luoOf.lie (d.toSOLin D))
      (scaleForm d.luoOf.traceForm (c : d.luoOf.Amb)) 1 1 where
  lin := d.toSOLin
  bijOn := by
    refine ⟨fun Y hY => ?_, fun Y hY Z hZ h => ?_, fun M hM => ?_⟩
    · simp only [SetLike.mem_coe, mem_lieCentralizer_units_one] at hY ⊢
      exact (d.toSOLin_mem_lieCentralizer_iff hD (mem_lieCentralizer.mp hY).1).mpr hY
    · simp only [SetLike.mem_coe, mem_lieCentralizer_units_one] at hY hZ
      exact d.eq_of_toSOLin_eq (mem_lieCentralizer.mp hY).1 (mem_lieCentralizer.mp hZ).1 h
    · simp only [SetLike.mem_coe, mem_lieCentralizer_units_one] at hM
      obtain ⟨Y, hY0, hYM⟩ := d.exists_toSOLin_eq (mem_lieCentralizer.mp hM).1
      refine ⟨Y, ?_, hYM⟩
      simp only [SetLike.mem_coe, mem_lieCentralizer_units_one]
      rw [← d.toSOLin_mem_lieCentralizer_iff hD hY0, hYM]
      exact hM
  map_commutator := fun X hX Y hY => by
    rw [mem_lieCentralizer_units_one] at hX hY
    exact d.toSOLin_commutator (mem_lieCentralizer.mp hX).1 (mem_lieCentralizer.mp hY).1
  map_bilin := fun X hX Y hY => by
    rw [mem_lieCentralizer_units_one] at hX hY
    exact hform X (mem_lieCentralizer.mp hX).1 Y (mem_lieCentralizer.mp hY).1
  isNilpotent_iff := fun X hX => by
    rw [mem_lieCentralizer_units_one] at hX
    exact d.isNilpotent_toSOLin_iff (mem_lieCentralizer.mp hX).1
  isRegularSS_iff := fun X hX => by
    rw [mem_lieCentralizer_units_one] at hX
    have hX0 := (mem_lieCentralizer.mp hX).1
    rw [Units.val_one, Units.val_one, lieCentralizer_one, lieCentralizer_one]
    refine and_congr (d.isSS_toSOLin_iff hX0) (d.isLieAbelian_iff_of_toSOLin
      (fun Z hZ => (mem_lieCentralizer.mp (mem_lieCentralizer.mp hZ).1).1)
      (fun Z hZ => (mem_lieCentralizer.mp (mem_lieCentralizer.mp hZ).1).1) fun Z hZ => ?_)
    rw [mem_lieCentralizer (𝔤 := lieCentralizer d.luoOf.lie _),
      mem_lieCentralizer (𝔤 := lieCentralizer d.lieZero D), d.toSOLin_mem_lieCentralizer_iff hD hZ,
      ← d.commute_iff_toSOLin hX0 hZ]
  map_orbitMap := by
    have hP : ∀ᶠ Y in 𝓝 (0 : d.ambient), Y ∈ d.lie → ∃ g : ↥d.G,
        ((g : d.ambientˣ) : d.ambient) = expA F Y ∧
          ((d.toGbarU g : d.luoOf.Ambˣ) : d.luoOf.Amb) = expA F (d.toSOLin Y) := by
      filter_upwards [eventually_expA_mem_G d, d.eventually_toGbarU_eq_expA_toSOLin]
        with Y h1 h2 hY
      obtain ⟨g, hg⟩ := h1 hY
      exact ⟨g, hg, h2 hY g hg⟩
    have hQ : ∀ᶠ Y in 𝓝 (0 : d.ambient), ∀ g : ↥d.G,
        ((g : d.ambientˣ) : d.ambient) = expA F (-Y) → -Y ∈ d.lie →
          ((d.toGbarU g : d.luoOf.Ambˣ) : d.luoOf.Amb) = expA F (d.toSOLin (-Y)) :=
      (continuous_neg.tendsto' (0 : d.ambient) 0 neg_zero).eventually
        ((d.eventually_toGbarU_eq_expA_toSOLin).mono fun Y h g hg hY => h hY g hg)
    obtain ⟨Ui, hUi, hinv⟩ := expA_mul_expA_neg F (A := d.ambient)
    refine ⟨{Y | (Y ∈ d.lie → ∃ g : ↥d.G, ((g : d.ambientˣ) : d.ambient) = expA F Y ∧
        ((d.toGbarU g : d.luoOf.Ambˣ) : d.luoOf.Amb) = expA F (d.toSOLin Y)) ∧
        (∀ g : ↥d.G, ((g : d.ambientˣ) : d.ambient) = expA F (-Y) → -Y ∈ d.lie →
          ((d.toGbarU g : d.luoOf.Ambˣ) : d.luoOf.Amb) = expA F (d.toSOLin (-Y))) ∧ Y ∈ Ui},
      hP.and (hQ.and hUi), fun X hX Y hY hYU => ?_⟩
    rw [mem_lieCentralizer_units_one] at hX hY
    have hX0 := (mem_lieCentralizer.mp hX).1
    have hY0 := (mem_lieCentralizer.mp hY).1
    obtain ⟨hYP, hYQ, hYi⟩ := hYU
    obtain ⟨g, hg, hgP⟩ := hYP (d.lieZero_le_lie hY0)
    have hgi : (((g : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) = expA F (-Y) :=
      Units.inv_eq_of_mul_eq_one_right (by rw [hg]; exact hinv Y hYi)
    have hPi : (((d.toGbarU g)⁻¹ : d.luoOf.Ambˣ) : d.luoOf.Amb) = expA F (-d.toSOLin Y) := by
      rw [← map_inv, ← map_neg]
      exact hYQ g⁻¹ hgi (neg_mem (d.lieZero_le_lie hY0))
    unfold orbitMap
    rw [← hg, ← hgi, d.toSOLin_conj g (d.lieZero_le_lie hX0), hgP, hPi]
  grp := d.toGbarFun
  grp_mapsTo := fun u hu => by
    rw [SetLike.mem_coe, grpCentralizer_one] at hu ⊢
    obtain ⟨huG, huD⟩ := hu
    rw [d.toGbarFun_of_mem huG]
    exact ⟨d.toGbarU_mem _, (d.toGbarU_mul_comm_iff ⟨u, huG⟩ hD).mpr huD⟩
  grp_surjOn := fun v hv => by
    rw [SetLike.mem_coe, grpCentralizer_one] at hv
    obtain ⟨hvG, hvD⟩ := hv
    obtain ⟨g, hg⟩ := d.toGbar_surjective hW hV ⟨v, hvG⟩
    have hgv : d.toGbarU g = v := congrArg Subtype.val hg
    refine ⟨(g : d.ambientˣ), ?_, ?_⟩
    · rw [SetLike.mem_coe, grpCentralizer_one]
      refine ⟨g.2, (d.toGbarU_mul_comm_iff g hD).mp ?_⟩
      rw [hgv]
      exact hvD
    · rw [d.toGbarFun_of_mem g.2]
      exact hgv
  map_conj := fun g hg Y hY => by
    rw [grpCentralizer_one] at hg
    rw [mem_lieCentralizer_units_one] at hY
    rw [d.toGbarFun_of_mem hg.1]
    exact d.toSOLin_conj ⟨g, hg.1⟩ (d.lieZero_le_lie (mem_lieCentralizer.mp hY).1)

end GGPData

/-! ## The form on centralizers -/

namespace LuoDatum

variable (L : LuoDatum F)

/-- The trace form is invariant: `B([X, Y], Z) = B(X, [Y, Z])`. -/
theorem traceForm_invariant (X Y Z : L.Amb) :
    L.traceForm (X * Y - Y * X) Z = L.traceForm X (Y * Z - Z * Y) := by
  have e1 : LinearMap.trace F L.W (L.fstA Y * (L.fstA X * L.fstA Z)) =
      LinearMap.trace F L.W (L.fstA X * (L.fstA Z * L.fstA Y)) := by
    rw [LinearMap.trace_mul_comm, mul_assoc]
  have e2 : LinearMap.trace F L.V (L.sndA Y * (L.sndA X * L.sndA Z)) =
      LinearMap.trace F L.V (L.sndA X * (L.sndA Z * L.sndA Y)) := by
    rw [LinearMap.trace_mul_comm, mul_assoc]
  simp only [traceForm, LinearMap.mk₂_apply, LinearMap.sub_apply, map_sub, map_mul, mul_assoc,
    e1, e2]

/-- The unit `(a · 1_W, b · 1_V)` of `End W × End V` (`a, b ≠ 0`), central. -/
def scalarUnit {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : L.Ambˣ where
  val := L.pair (a • 1) (b • 1)
  inv := L.pair (a⁻¹ • 1) (b⁻¹ • 1)
  val_inv := Prod.ext (by
      change (a • (1 : Module.End F L.W)) * (a⁻¹ • 1) = 1
      rw [smul_mul_smul_comm, mul_inv_cancel₀ ha, one_smul, one_mul])
    (by
      change (b • (1 : Module.End F L.V)) * (b⁻¹ • 1) = 1
      rw [smul_mul_smul_comm, mul_inv_cancel₀ hb, one_smul, one_mul])
  inv_val := Prod.ext (by
      change (a⁻¹ • (1 : Module.End F L.W)) * (a • 1) = 1
      rw [smul_mul_smul_comm, inv_mul_cancel₀ ha, one_smul, one_mul])
    (by
      change (b⁻¹ • (1 : Module.End F L.V)) * (b • 1) = 1
      rw [smul_mul_smul_comm, inv_mul_cancel₀ hb, one_smul, one_mul])

variable {L}

theorem fstA_scalarUnit_mul {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (Y : L.Amb) :
    L.fstA ((L.scalarUnit ha hb : L.Amb) * Y) = a • L.fstA Y := by
  rw [map_mul]
  change (a • (1 : Module.End F L.W)) * L.fstA Y = _
  rw [smul_mul_assoc, one_mul]

theorem sndA_scalarUnit_mul {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (Y : L.Amb) :
    L.sndA ((L.scalarUnit ha hb : L.Amb) * Y) = b • L.sndA Y := by
  rw [map_mul]
  change (b • (1 : Module.End F L.V)) * L.sndA Y = _
  rw [smul_mul_assoc, one_mul]

theorem fstA_scalarUnit_inv_mul {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (Y : L.Amb) :
    L.fstA (((L.scalarUnit ha hb)⁻¹ : L.Ambˣ) * Y) = a⁻¹ • L.fstA Y := by
  rw [map_mul]
  change (a⁻¹ • (1 : Module.End F L.W)) * L.fstA Y = _
  rw [smul_mul_assoc, one_mul]

theorem sndA_scalarUnit_inv_mul {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (Y : L.Amb) :
    L.sndA (((L.scalarUnit ha hb)⁻¹ : L.Ambˣ) * Y) = b⁻¹ • L.sndA Y := by
  rw [map_mul]
  change (b⁻¹ • (1 : Module.End F L.V)) * L.sndA Y = _
  rw [smul_mul_assoc, one_mul]

theorem scalarUnit_central {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (Y : L.Amb) :
    (L.scalarUnit ha hb : L.Amb) * Y = Y * (L.scalarUnit ha hb : L.Amb) := by
  refine Prod.ext ?_ ?_
  · change (a • (1 : Module.End F L.W)) * L.fstA Y = L.fstA Y * (a • 1)
    rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  · change (b • (1 : Module.End F L.V)) * L.sndA Y = L.sndA Y * (b • 1)
    rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

/-- `B(c Y, Z) = B(Y, c Z)` for `c = (a · 1, b · 1)`. -/
theorem traceForm_scalarUnit {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (Y Z : L.Amb) :
    L.traceForm ((L.scalarUnit ha hb : L.Amb) * Y) Z =
      L.traceForm Y ((L.scalarUnit ha hb : L.Amb) * Z) := by
  simp only [traceForm, LinearMap.mk₂_apply, fstA_scalarUnit_mul, sndA_scalarUnit_mul,
    smul_mul_assoc, mul_smul_comm]

/-- `B((a · 1, b · 1) P, R) = ½ (a tr(P_W R_W) + b tr(P_V R_V))`. -/
theorem traceForm_scalarUnit_mul {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (P R : L.Amb) :
    L.traceForm ((L.scalarUnit ha hb : L.Amb) * P) R = ⅟(2 : F) *
      (a * LinearMap.trace F L.W (L.fstA P * L.fstA R) +
        b * LinearMap.trace F L.V (L.sndA P * L.sndA R)) := by
  simp only [traceForm, LinearMap.mk₂_apply, fstA_scalarUnit_mul, sndA_scalarUnit_mul,
    smul_mul_assoc, map_smul, smul_eq_mul]

/-- `(a · 1, b · 1)` and its inverse preserve `𝔤_Y`. -/
theorem scalarUnit_mul_mem_lieCentralizer {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) {Y M : L.Amb}
    (hM : M ∈ lieCentralizer L.lie Y) :
    (L.scalarUnit ha hb : L.Amb) * M ∈ lieCentralizer L.lie Y ∧
      (((L.scalarUnit ha hb)⁻¹ : L.Ambˣ) : L.Amb) * M ∈ lieCentralizer L.lie Y := by
  obtain ⟨hM𝔤, hMY⟩ := mem_lieCentralizer.mp hM
  have hc := scalarUnit_central (L := L) ha hb
  have hci := inv_mul_eq_mul_inv_of_central hc
  refine ⟨mem_lieCentralizer.mpr ⟨⟨?_, ?_⟩, ?_⟩, mem_lieCentralizer.mpr ⟨⟨?_, ?_⟩, ?_⟩⟩
  · rw [fstA_scalarUnit_mul]; exact Submodule.smul_mem _ a hM𝔤.1
  · rw [sndA_scalarUnit_mul]; exact Submodule.smul_mem _ b hM𝔤.2
  · rw [← mul_assoc, ← hc, mul_assoc, hMY, mul_assoc]
  · rw [fstA_scalarUnit_inv_mul]; exact Submodule.smul_mem _ a⁻¹ hM𝔤.1
  · rw [sndA_scalarUnit_inv_mul]; exact Submodule.smul_mem _ b⁻¹ hM𝔤.2
  · rw [← mul_assoc, ← hci, mul_assoc, hMY, mul_assoc]

end LuoDatum

namespace GGPData

variable (d : GGPData F)

/-! ## Semisimplicity of `X ∈ 𝔱⁰_♮` and openness of the regular set of `𝔤⁰_X` -/

/-- `X ∈ 𝔱⁰_♮` is semisimple (`isSS_of_commute_of_isGammaElt`: it commutes with the
`Γ`-element defining the torus and kills its fixed space). -/
theorem isSS_of_isGammaEltLie (T : d.GammaTorus) {X : CliffordAlgebra d.QW}
    (hX : d.IsGammaEltLie T.1 X) : IsSS F X := by
  obtain ⟨_, x, hx, rfl⟩ := T
  refine d.isSS_of_commute_of_isGammaElt hx hX.1.1.1 (hX.1.2.1 x (d.self_mem_torusOf x))
    fun v hv => hX.1.2.2 v ?_
  rw [d.commonFixed_torusOf]
  exact hv

/-- `(X, X)` is semisimple when `X` is. -/
theorem isSS_diagLie {X : CliffordAlgebra d.QW} (hX : IsSS F X) : IsSS F (d.diagLie X) :=
  isSS_prod (Y := d.diagLie X) hX
    (isSS_algHom (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)) hX)

/-- For semisimple `D ∈ 𝔤`, some semisimple `g ∈ G(F)` (`g = e^{tD}`, `t ≠ 0` small) has the same
centralizer in `𝔤` as `D` (`exists_nhds_commute_of_commute_expA`). -/
theorem exists_lieCentralizer_eq {D : d.ambient} (hD : D ∈ d.lie) (hss : IsSS F D) :
    ∃ g : ↥d.G, IsSS F ((g : d.ambientˣ) : d.ambient) ∧
      lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient) = lieCentralizer d.lie D := by
  haveI := IsModuleTopology.toContinuousSMul F d.ambient
  obtain ⟨U₁, hU₁, hcomm⟩ := exists_nhds_commute_of_commute_expA F (A := d.ambient)
  obtain ⟨U₂, hU₂, hssU⟩ := exists_nhds_isSS_expA F (A := d.ambient)
  obtain ⟨U₃, hU₃, hexp⟩ := (eventually_expA_mem_G d).exists_mem
  have ht : Tendsto (fun t : F => t • D) (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous (fun t : F => t • D) := continuous_id.smul continuous_const
    have h := hc.tendsto 0
    simp only [zero_smul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[≠] (0 : F), t • D ∈ U₁ ∩ U₂ ∩ U₃ :=
    ht (Filter.inter_mem (Filter.inter_mem hU₁ hU₂) hU₃)
  obtain ⟨t, htU, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
  have ht0' : t ≠ 0 := ht0
  obtain ⟨⟨htU₁, htU₂⟩, htU₃⟩ := htU
  have hsst : IsSS F (t • D) := isSS_smul t hss
  obtain ⟨g, hg⟩ := hexp _ htU₃ (d.lie.smul_mem t hD)
  refine ⟨g, by rw [hg]; exact hssU _ htU₂ hsst, ?_⟩
  ext Y
  rw [mem_lieCentralizer, mem_lieCentralizer]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : Commute Y (expA F (t • D)) := by rw [← hg]; exact h.symm
    have h2 : Y * (t • D) = (t • D) * Y := (hcomm _ htU₁ Y h1).eq
    rw [mul_smul_comm, smul_mul_assoc] at h2
    exact (smul_right_injective _ ht0' h2).symm
  · have h1 : Commute Y (t • D) := (show Commute Y D from h.symm).smul_right t
    have h2 := (commute_expA_of_commute (F := F) h1).eq
    rw [← hg] at h2
    exact h2.symm

/-- Regular semisimplicity in `𝔤⁰_D` and in `𝔤_D = 𝔷 ⊕ 𝔤⁰_D` agree (the centre `𝔷` is central). -/
theorem isRegularSS_lieCentralizer_lieZero_iff {D Z : d.ambient}
    (_hZ : Z ∈ lieCentralizer d.lieZero D) :
    IsRegularSS (lieCentralizer d.lieZero D) Z ↔ IsRegularSS (lieCentralizer d.lie D) Z := by
  unfold IsRegularSS
  refine and_congr_right fun _ => ?_
  rw [isLieAbelian_iff_forall_commute, isLieAbelian_iff_forall_commute]
  have dec : ∀ {Y}, Y ∈ lieCentralizer (lieCentralizer d.lie D) Z → ∃ z ∈ d.lieCenter,
      ∃ A ∈ lieCentralizer (lieCentralizer d.lieZero D) Z, Y = z + A := by
    intro Y hY
    obtain ⟨hY1, hYZ⟩ := mem_lieCentralizer.mp hY
    obtain ⟨hYl, hYD⟩ := mem_lieCentralizer.mp hY1
    have hs : Y ∈ d.lieCenter ⊔ d.lie0 := by rw [← lie_eq_center_sup_lie0]; exact hYl
    obtain ⟨z, hz, A, hA, rfl⟩ := Submodule.mem_sup.mp hs
    refine ⟨z, hz, A, mem_lieCentralizer.mpr ⟨mem_lieCentralizer.mpr ⟨hA, ?_⟩, ?_⟩, rfl⟩
    · rw [mul_add, add_mul, d.commute_of_mem_lieCenter hz D] at hYD
      exact add_left_cancel hYD
    · rw [mul_add, add_mul, d.commute_of_mem_lieCenter hz Z] at hYZ
      exact add_left_cancel hYZ
  constructor
  · intro h Y₁ h₁ Y₂ h₂
    obtain ⟨z₁, hz₁, A₁, hA₁, rfl⟩ := dec h₁
    obtain ⟨z₂, hz₂, A₂, hA₂, rfl⟩ := dec h₂
    have hAA := h A₁ hA₁ A₂ hA₂
    have c1 := d.commute_of_mem_lieCenter hz₁
    have c2 := d.commute_of_mem_lieCenter hz₂
    calc (z₁ + A₁) * (z₂ + A₂) = z₁ * z₂ + z₁ * A₂ + (A₁ * z₂ + A₁ * A₂) := by noncomm_ring
      _ = z₂ * z₁ + A₂ * z₁ + (z₂ * A₁ + A₂ * A₁) := by rw [c1 z₂, c1 A₂, ← c2 A₁, hAA]
      _ = (z₂ + A₂) * (z₁ + A₁) := by noncomm_ring
  · intro h Y₁ h₁ Y₂ h₂
    have sub : ∀ {Y}, Y ∈ lieCentralizer (lieCentralizer d.lieZero D) Z →
        Y ∈ lieCentralizer (lieCentralizer d.lie D) Z := fun {Y} hY => by
      obtain ⟨hY1, hYZ⟩ := mem_lieCentralizer.mp hY
      obtain ⟨hY0, hYD⟩ := mem_lieCentralizer.mp hY1
      exact mem_lieCentralizer.mpr ⟨mem_lieCentralizer.mpr ⟨d.lieZero_le_lie hY0, hYD⟩, hYZ⟩
    exact h Y₁ (sub h₁) Y₂ (sub h₂)

/-- **The regular semisimple set of `𝔤⁰_D` is open** for semisimple `D ∈ 𝔤⁰`: it is the preimage
of that of `𝔤_g` (`isOpen_setOf_isRegularSS_lieCentralizer`) for `g ∈ G(F)` semisimple with
`𝔤_g = 𝔤_D` (`exists_lieCentralizer_eq`). -/
theorem isOpen_setOf_isRegularSS_lieCentralizer_lieZero {D : d.ambient} (hD : D ∈ d.lieZero)
    (hss : IsSS F D) :
    IsOpen {Z : ↥(lieCentralizer d.lieZero D) |
      IsRegularSS (lieCentralizer d.lieZero D) (Z : d.ambient)} := by
  obtain ⟨g, hg, hcent⟩ := d.exists_lieCentralizer_eq (d.lieZero_le_lie hD) hss
  have hO := isOpen_setOf_isRegularSS_lieCentralizer d g hg
  rw [hcent] at hO
  have hmem : ∀ Z : ↥(lieCentralizer d.lieZero D), (Z : d.ambient) ∈ lieCentralizer d.lie D :=
    fun Z => mem_lieCentralizer.mpr ⟨d.lieZero_le_lie (mem_lieCentralizer.mp Z.2).1,
      (mem_lieCentralizer.mp Z.2).2⟩
  have hc : Continuous fun Z : ↥(lieCentralizer d.lieZero D) =>
      (⟨Z, hmem Z⟩ : ↥(lieCentralizer d.lie D)) :=
    Continuous.subtype_mk continuous_subtype_val _
  convert hO.preimage hc using 1
  ext Z
  exact d.isRegularSS_lieCentralizer_lieZero_iff Z.2

end GGPData

namespace GGPData

variable (d : GGPData F) (ψ : NontrivialAddChar F)

/-- **`cTheta_toSO`'s conclusion from Lie germ uniqueness on `𝔤⁰`**, given constants `a, b ≠ 0`
with `bilin(Y, Z) = B((a · 1, b · 1) ad Y, ad Z)` on `𝔤⁰` (`hform`; `B` the trace form).  The
orbit map is `E = c · (ad ∘ ·)`, `c = (a · 1, b · 1)`: `ad` is an isomorphism of descent data
`(Z_G(X), 𝔤⁰_X, bilin) ≃ (Ḡ_{ad X}, 𝔤_{ad X}, B(c ·, ·))` (`adCentralizerIso`), so it transports
`ĵ` (`CentralizerIso.jHat_map`), and `ĵ_{B(c ·, ·)}(O, ·) = ĵ_B(c O, ·)` (`jHat_scale`).  The
hypotheses of these on `𝔤_{ad X}`: `B` is nondegenerate there (`ad X` is semisimple), the regular
set is open (`isOpen_setOf_isRegularSS_lieCentralizer_lieZero`, transported by `ad`), orbit measures
are unique (`isOrbitMeasure_unique_luo`).  Luo's recipe is invariant under `c`
(`orbitSpec_iff_of_smul`) and is `OrbitSpecAt` under `ad`; `horb` is `orbitSpecAt_orbit_unique`. -/
theorem cTheta_toSO_of_germUnique_of_form (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    {θ : ↥d.luoOf.lie → ℂ}
    (hθ : IsLieQuasiCharacter d.luoOf.Gbar d.luoOf.lie d.luoOf.traceForm ψ θ)
    (T : d.GammaTorus) (X : CliffordAlgebra d.QW) (hX : d.IsGammaEltLie T.1 X)
    {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (hform : ∀ Y ∈ d.lieZero, ∀ Z ∈ d.lieZero,
      scaleForm d.luoOf.traceForm (d.luoOf.scalarUnit ha hb : d.luoOf.Amb) (d.toSOLin Y)
        (d.toSOLin Z) = d.bilin Y Z)
    (hgerm : ∀ c c'' : NilOrbit (lieGrpCentralizer d.G (d.diagLie X))
        (lieCentralizer d.lieZero (d.diagLie X)) → ℂ,
      HasGermExpansionLie d.G d.lieZero d.bilin ψ (θ ∘ d.toSO) (d.diagLie X) c →
      HasGermExpansionLie d.G d.lieZero d.bilin ψ (θ ∘ d.toSO) (d.diagLie X) c'' →
      ∀ O ∈ NilReg _ _, c O = c'' O) :
    d.germLie0 ψ (θ ∘ d.toSO) (d.diagLie X) (d.orbitChoiceLie X) =
      d.luoOf.cTheta ψ θ (d.toSOLin (d.diagLie X)) := by
  classical
  have hX0 : X ∈ soSub d.QW := hX.1.1
  have hD : d.diagLie X ∈ d.lieZero := d.diagLie_mem_lieZero hX0
  have hXm : d.toSOLin (d.diagLie X) ∈ d.luoOf.lie := d.toSO_mem ⟨_, hD⟩
  have hssD : IsSS F (d.diagLie X) := d.isSS_diagLie (d.isSS_of_isGammaEltLie T hX)
  have hss : IsSS F (d.toSOLin (d.diagLie X)) := d.isSS_toSOLin hD hssD
  -- the scaling unit
  set c := d.luoOf.scalarUnit ha hb with hc_def
  have hc : ∀ a' : d.luoOf.Amb, (c : d.luoOf.Amb) * a' = a' * c :=
    LuoDatum.scalarUnit_central ha hb
  have hc𝔤 : ∀ Y ∈ lieCentralizer d.luoOf.lie (d.toSOLin (d.diagLie X)),
      (c : d.luoOf.Amb) * Y ∈ lieCentralizer d.luoOf.lie (d.toSOLin (d.diagLie X)) :=
    fun _ hY => (LuoDatum.scalarUnit_mul_mem_lieCentralizer ha hb hY).1
  have hc𝔤' : ∀ Y ∈ lieCentralizer d.luoOf.lie (d.toSOLin (d.diagLie X)),
      ((c⁻¹ : d.luoOf.Ambˣ) : d.luoOf.Amb) * Y ∈
        lieCentralizer d.luoOf.lie (d.toSOLin (d.diagLie X)) :=
    fun _ hY => (LuoDatum.scalarUnit_mul_mem_lieCentralizer ha hb hY).2
  have hbc : ∀ Y Z : d.luoOf.Amb, d.luoOf.traceForm ((c : d.luoOf.Amb) * Y) Z =
      d.luoOf.traceForm Y ((c : d.luoOf.Amb) * Z) := LuoDatum.traceForm_scalarUnit ha hb
  -- descent data
  have hG₀ : ∀ g ∈ lieGrpCentralizer d.G (d.diagLie X), ∀ Y ∈ lieCentralizer d.lieZero
      (d.diagLie X), (g : d.ambient) * Y * (↑g⁻¹ : d.ambient) ∈
        lieCentralizer d.lieZero (d.diagLie X) :=
    fun _ hg _ hY => d.conj_mem_lieCentralizer_lieZero hg hY
  have hG₁ := conj_mem_lieCentralizer_of_mem_lieGrpCentralizer
    d.luoOf.conj_mem_lie_of_mem_Gbar (d.toSOLin (d.diagLie X))
  have e𝔤₀ : lieCentralizer (lieCentralizer d.lieZero (d.diagLie X)) ((1 : d.ambientˣ) : d.ambient)
      = lieCentralizer d.lieZero (d.diagLie X) := by rw [Units.val_one, lieCentralizer_one]
  have e𝔤₁ : lieCentralizer (lieCentralizer d.luoOf.lie (d.toSOLin (d.diagLie X)))
      ((1 : d.luoOf.Ambˣ) : d.luoOf.Amb) =
        lieCentralizer d.luoOf.lie (d.toSOLin (d.diagLie X)) := by
    rw [Units.val_one, lieCentralizer_one]
  have eG₀ := grpCentralizer_one (lieGrpCentralizer d.G (d.diagLie X))
  have eG₁ := grpCentralizer_one (lieGrpCentralizer d.luoOf.Gbar (d.toSOLin (d.diagLie X)))
  let ι := d.adCentralizerIso hW hV hD c hform
  -- hypotheses of `jHat_scale` and `jHat_map` on `𝔤_{ad X}`
  have hnd₁ : (restrictForm (lieCentralizer d.luoOf.lie (d.toSOLin (d.diagLie X)))
      d.luoOf.traceForm).Nondegenerate :=
    restrictForm_lieCentralizer_nondegenerate_of_isSS
      (d.luoOf.restrictForm_lie_traceForm_nondegenerate d.nondeg_QV)
      d.luoOf.traceForm_invariant hXm (LieAlgebra.ad_isSemisimple_of_isSemisimple_mulLeft hss)
  have hopen₀ : IsOpen {Z : ↥(lieCentralizer (lieCentralizer d.lieZero (d.diagLie X))
      ((1 : d.ambientˣ) : d.ambient)) | IsRegularSS (lieCentralizer (lieCentralizer d.lieZero
        (d.diagLie X)) ((1 : d.ambientˣ) : d.ambient)) (Z : d.ambient)} := by
    rw [e𝔤₀]
    exact d.isOpen_setOf_isRegularSS_lieCentralizer_lieZero hD hssD
  have hopen' : IsOpen {Z : ↥(lieCentralizer (lieCentralizer d.luoOf.lie
      (d.toSOLin (d.diagLie X))) ((1 : d.luoOf.Ambˣ) : d.luoOf.Amb)) |
      IsRegularSS (lieCentralizer (lieCentralizer d.luoOf.lie (d.toSOLin (d.diagLie X)))
        ((1 : d.luoOf.Ambˣ) : d.luoOf.Amb)) (Z : d.luoOf.Amb)} := by
    convert hopen₀.preimage ι.continuous_linEquiv_symm using 1
    ext Z'
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [← ι.isRegularSS_iff _ (ι.linEquiv.symm Z').2, ← CentralizerIso.linEquiv_apply,
      LinearEquiv.apply_symm_apply]
  have hopen₁ : IsOpen {Z : ↥(lieCentralizer d.luoOf.lie (d.toSOLin (d.diagLie X))) |
      IsRegularSS (lieCentralizer d.luoOf.lie (d.toSOLin (d.diagLie X))) (Z : d.luoOf.Amb)} := by
    rw [← e𝔤₁]
    exact hopen'
  have hnd' : (restrictForm (lieCentralizer (lieCentralizer d.luoOf.lie (d.toSOLin (d.diagLie X)))
      ((1 : d.luoOf.Ambˣ) : d.luoOf.Amb))
        (scaleForm d.luoOf.traceForm (c : d.luoOf.Amb))).Nondegenerate
      := by
    rw [e𝔤₁]
    exact restrictForm_scaleForm_nondegenerate c hc𝔤 hc𝔤' hnd₁
  have hu' : ∀ O' μ ν, IsOrbitMeasure (grpCentralizer (lieGrpCentralizer d.luoOf.Gbar
      (d.toSOLin (d.diagLie X))) 1) (lieCentralizer (lieCentralizer d.luoOf.lie
        (d.toSOLin (d.diagLie X))) ((1 : d.luoOf.Ambˣ) : d.luoOf.Amb))
        (scaleForm d.luoOf.traceForm (c : d.luoOf.Amb)) ψ O' μ →
      IsOrbitMeasure (grpCentralizer (lieGrpCentralizer d.luoOf.Gbar
      (d.toSOLin (d.diagLie X))) 1) (lieCentralizer (lieCentralizer d.luoOf.lie
        (d.toSOLin (d.diagLie X))) ((1 : d.luoOf.Ambˣ) : d.luoOf.Amb))
        (scaleForm d.luoOf.traceForm (c : d.luoOf.Amb)) ψ O' ν → μ = ν := by
    rw [eG₁, e𝔤₁]
    exact fun _ _ _ h1 h2 => d.isOrbitMeasure_unique_luo _ h1 h2
  have hu₁ : ∀ O' μ ν, IsOrbitMeasure (lieGrpCentralizer d.luoOf.Gbar (d.toSOLin (d.diagLie X)))
      (lieCentralizer d.luoOf.lie (d.toSOLin (d.diagLie X))) d.luoOf.traceForm ψ O' μ →
      IsOrbitMeasure (lieGrpCentralizer d.luoOf.Gbar (d.toSOLin (d.diagLie X)))
      (lieCentralizer d.luoOf.lie (d.toSOLin (d.diagLie X))) d.luoOf.traceForm ψ O' ν → μ = ν :=
    fun _ _ _ h1 h2 => d.isOrbitMeasure_unique_luo _ h1 h2
  -- the orbit map
  let β₀ := nilOrbitCongr eG₀.symm e𝔤₀.symm
  let ν := ι.nilOrbitEquiv hG₀
  let β₁ := nilOrbitCongr eG₁ e𝔤₁
  let σ := nilScaleEquiv (G := lieGrpCentralizer d.luoOf.Gbar (d.toSOLin (d.diagLie X))) c hc
    hc𝔤 hc𝔤'
  let E := β₀.trans (ν.trans (β₁.trans σ))
  have hE : ∀ O, E O = nilScale (c : d.luoOf.Amb) hc hc𝔤 (β₁ (ν (β₀ O))) := fun _ => rfl
  refine d.cTheta_toSO_of_transport ψ hθ X hXm hss hgerm (d.orbitSpecAt_orbit_unique T hX) E
    E.surjective (fun O => ?_) (fun O => ?_) ?_ (fun c' hc' => ?_)
  · -- regular orbits
    rw [hE, nilScale_mem_nilReg_iff c hc hc𝔤 hG₁, nilOrbitCongr_mem_nilReg_iff,
      ι.nilOrbitEquiv_mem_nilReg_iff hG₀ hG₁, nilOrbitCongr_mem_nilReg_iff]
  · -- Luo's recipe
    rw [hE]
    set K : Submodule F (Fin d.m → F) := LinearMap.ker (adV d.QW X)
    refine (exists_mem_nilOrbitSet_nilScale_iff c hc hc𝔤 hc𝔤' _
      (fun Y => d.luoOf.OrbitSpec K Y)).trans ?_
    refine (exists_mem_nilOrbitSet_nilOrbitCongr_iff eG₁ e𝔤₁ _
      (fun Y => d.luoOf.OrbitSpec K ((c : d.luoOf.Amb) * Y))).trans ?_
    refine (ι.exists_mem_nilOrbitSet_nilOrbitEquiv_iff hG₀ (β₀ O)
      (fun Y => d.luoOf.OrbitSpec K ((c : d.luoOf.Amb) * Y))).trans ?_
    refine (exists_mem_nilOrbitSet_nilOrbitCongr_iff eG₀.symm e𝔤₀.symm O
      (fun Y => d.luoOf.OrbitSpec K ((c : d.luoOf.Amb) * ι.lin Y))).trans ?_
    refine exists_congr fun Y => and_congr_right fun _ => ?_
    exact (d.luoOf.orbitSpec_iff_of_smul ha hb K (LuoDatum.fstA_scalarUnit_mul ha hb _)
      (LuoDatum.sndA_scalarUnit_mul ha hb _)).trans (d.orbitSpecAt_iff_orbitSpec_toSOLin K _).symm
  · -- the zero orbit
    change nilScale (c : d.luoOf.Amb) hc hc𝔤 (β₁ (ι.nilOrbitMap (β₀ (Quotient.mk _ _)))) = _
    rw [nilOrbitCongr_mk, ι.nilOrbitMap_mk, nilOrbitCongr_mk, nilScale_mk]
    exact congrArg (Quotient.mk _) (Subtype.ext (by
      change (c : d.luoOf.Amb) * d.toSOLin 0 = 0
      rw [map_zero, mul_zero]))
  · -- transport of the expansion
    obtain ⟨hfin, ω', hω', hexp⟩ := hc'
    have hcont : Continuous d.toSOLin := IsModuleTopology.continuous_of_linearMap d.toSOLin
    refine ⟨?_, d.toSOLin ⁻¹' ω', hcont.continuousAt.preimage_mem_nhds (by rwa [map_zero]),
      fun Y hYω hY hYr Z hZ => ?_⟩
    · rw [Function.support_comp_eq_preimage]
      exact hfin.preimage E.injective.injOn
    have hY1 : d.toSOLin Y ∈ lieCentralizer d.luoOf.lie (d.toSOLin (d.diagLie X)) :=
      (d.toSOLin_mem_lieCentralizer_iff hD (mem_lieCentralizer.mp hY).1).mpr hY
    have hY' : Y ∈ lieCentralizer (lieCentralizer d.lieZero (d.diagLie X))
        ((1 : d.ambientˣ) : d.ambient) := mem_lieCentralizer_units_one.mpr hY
    have hYr' : IsRegularSS (lieCentralizer (lieCentralizer d.lieZero (d.diagLie X))
        ((1 : d.ambientˣ) : d.ambient)) Y := by rw [e𝔤₀]; exact hYr
    have hYr1 : IsRegularSS (lieCentralizer d.luoOf.lie (d.toSOLin (d.diagLie X)))
        (d.toSOLin Y) := by
      have := (ι.isRegularSS_iff Y hY').mpr hYr'
      rwa [e𝔤₁] at this
    have hZ' : ((d.toSO Z : ↥d.luoOf.lie) : d.luoOf.Amb) =
        d.toSOLin (d.diagLie X) + d.toSOLin Y := by
      rw [coe_toSO, hZ, map_add]
    rw [Function.comp_apply, hexp _ hYω hY1 hYr1 _ hZ', ← finsum_comp_equiv E]
    refine finsum_congr fun O => ?_
    simp only [Function.comp_apply]
    congr 1
    rw [hE, ← jHat_scale ψ c hc hc𝔤 hc𝔤' hbc hnd₁ hopen₁ hu₁ _ _ hY1 hYr1,
      jHat_nilOrbitCongr eG₁ e𝔤₁, ← jHat_nilOrbitCongr eG₀.symm e𝔤₀.symm _ ψ O Y]
    exact ι.jHat_map hG₀ ψ hnd' hopen' hu' (β₀ O) Y hY' hYr'

end GGPData

/-! ## The trace form of `C(V)` on `so_Cliff(V)` -/

section CliffTraceForm

open CliffordAlgebra

variable {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]

/-- `tr(ad(ι x ι y) ∘ M) = polar(y, M x) − polar(x, M y)` (`ad(ι x ι y)` has rank `≤ 2`). -/
theorem trace_adV_ι_mul_ι_mul (Q : QuadraticForm F V) (x y : V) (M : Module.End F V) :
    LinearMap.trace F V (adV Q (ι Q x * ι Q y) * M) =
      QuadraticMap.polar Q y (M x) - QuadraticMap.polar Q x (M y) := by
  have e : adV Q (ι Q x * ι Q y) * M =
      (QuadraticMap.polarBilin Q y ∘ₗ M).smulRight x -
        (QuadraticMap.polarBilin Q x ∘ₗ M).smulRight y := by
    ext w
    simp [adV_ι_mul_ι]
  rw [e, map_sub, LinearMap.trace_smulRight, LinearMap.trace_smulRight]
  simp

/-- `τ(ι a ι b Z) − τ(ι b ι a Z) = −B(a, ad Z b)` for `Z ∈ gspin(V)` (`τ` the scalar part,
cyclic). -/
theorem scalarTrace_ι_mul_ι_mul_sub (Q : QuadraticForm F V) (a b : V) {Z : CliffordAlgebra Q}
    (hZ : Z ∈ gspin Q) :
    scalarTrace Q (ι Q a * ι Q b * Z) - scalarTrace Q (ι Q b * ι Q a * Z) =
      -QuadraticMap.associated Q a (adV Q Z b) := by
  have e1 : scalarTrace Q (ι Q b * ι Q a * Z) = scalarTrace Q (ι Q a * (Z * ι Q b)) := by
    rw [mul_assoc, scalarTrace_mul_comm, mul_assoc]
  rw [e1, ← map_sub, mul_assoc, ← mul_sub, show ι Q b * Z - Z * ι Q b = -ι Q (adV Q Z b) by
    rw [ι_adV hZ]; abel, mul_neg, map_neg, scalarTrace_ι_mul_ι]

/-- **`8 τ(Y Z) = tr(ad Y ∘ ad Z)` on `so_Cliff(V)`** (`τ` the scalar part of `C(V)`): by
bilinearity on bivectors `Y = ½(ι a ι b − ι b ι a)` (which span `so_Cliff(V)`), where both sides
are `−4 B(a, ad Z b)`. -/
theorem eight_mul_scalarTrace_mul {Q : QuadraticForm F V} (hQ : IsNondeg Q)
    {Y Z : CliffordAlgebra Q} (hY : Y ∈ soSub Q) (hZ : Z ∈ soSub Q) :
    8 * scalarTrace Q (Y * Z) = LinearMap.trace F V (adV Q Y * adV Q Z) := by
  rw [soSub_eq_quadraticLieSubalgebra hQ] at hY
  change Y ∈ (quadraticLieSubalgebra Q).toSubmodule at hY
  rw [quadraticLieSubalgebra_toSubmodule] at hY
  induction hY using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    simp only [bivector_def, smul_mul_assoc, map_smul, sub_mul, map_sub, smul_eq_mul]
    rw [scalarTrace_ι_mul_ι_mul_sub Q a b hZ.1, trace_adV_ι_mul_ι_mul,
      trace_adV_ι_mul_ι_mul, polar_eq_two_mul_bform, polar_eq_two_mul_bform]
    have hs : bform Q b (adV Q Z a) = -bform Q a (adV Q Z b) := by
      rw [bform_comm Q b]
      exact bform_adV hZ.1 a b
    rw [hs]
    simp only [invOf_eq_inv]
    ring
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul, map_add, mul_add, hx, hy, map_add, add_mul, map_add]
  | smul r x _ hx =>
    rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_left_comm, hx, map_smul, smul_mul_assoc,
      map_smul, smul_eq_mul]

end CliffTraceForm

namespace GGPData

variable (d : GGPData F) (ψ : NontrivialAddChar F)

/-- `bilin(Y, Z) = tr_{C(W)}(L_{Y_W Z_W}) + tr_{C(V)}(L_{Y_V Z_V})`. -/
theorem bilin_eq_cliffTrace_add (Y Z : d.ambient) :
    d.bilin Y Z = cliffTrace d.QW (Y.1 * Z.1) + cliffTrace d.QV (Y.2 * Z.2) := by
  rw [bilin_apply]
  have e : LinearMap.mulLeft F (Y * Z) =
      (LinearMap.mulLeft F (Y.1 * Z.1)).prodMap (LinearMap.mulLeft F (Y.2 * Z.2)) :=
    LinearMap.ext fun _ => rfl
  rw [e, LinearMap.trace_prodMap']

/-- The constant comparing `bilin` with the trace form on a factor of dimension `n`:
`2ⁿ / 4` (`tr_{C}(L_{YZ}) = 2ⁿ τ(YZ) = (2ⁿ/8) tr(ad Y ad Z)` and `B = ½ tr`). -/
def formConst (n : ℕ) : F := (2 : F) ^ n / 4

theorem formConst_ne_zero (n : ℕ) : (formConst n : F) ≠ 0 :=
  div_ne_zero (pow_ne_zero _ two_ne_zero) (by norm_num)

/-- **`bilin` is the rescaled trace form on `𝔤⁰`**: for `Y, Z ∈ 𝔤⁰`,
`bilin(Y, Z) = B((2^{dim W}/4 · 1_W, 2^{dim V}/4 · 1_V) ad Y, ad Z)`, `B` Luo's trace form
`½ (tr_W + tr_V)`: on each factor `tr_{C}(L_{YZ}) = 2ⁿ τ(YZ)` (Tau Ceti's
`trace_mulLeft_eq_two_pow_mul_scalarTrace`) and `8 τ(YZ) = tr(ad Y ad Z)`
(`eight_mul_scalarTrace_mul`). -/
theorem scaleForm_traceForm_toSOLin {Y Z : d.ambient} (hY : Y ∈ d.lieZero) (hZ : Z ∈ d.lieZero) :
    scaleForm d.luoOf.traceForm
        (d.luoOf.scalarUnit (formConst_ne_zero (Module.finrank F (Fin d.m → F)))
          (formConst_ne_zero (Module.finrank F d.V)) : d.luoOf.Amb) (d.toSOLin Y) (d.toSOLin Z) =
      d.bilin Y Z := by
  have h1 := eight_mul_scalarTrace_mul d.nondeg hY.1 hZ.1
  have h2 := eight_mul_scalarTrace_mul d.nondeg_QV hY.2 hZ.2
  rw [bilin_eq_cliffTrace_add, cliffTrace, cliffTrace,
    CliffordAlgebra.trace_mulLeft_eq_two_pow_mul_scalarTrace,
    CliffordAlgebra.trace_mulLeft_eq_two_pow_mul_scalarTrace]
  rw [scaleForm_apply, LuoDatum.traceForm_scalarUnit_mul]
  have e1 : LinearMap.trace F d.luoOf.W (d.luoOf.fstA (d.toSOLin Y) * d.luoOf.fstA (d.toSOLin Z)) =
      LinearMap.trace F (Fin d.m → F) (adV d.QW Y.1 * adV d.QW Z.1) := rfl
  have e2 : LinearMap.trace F d.luoOf.V (d.luoOf.sndA (d.toSOLin Y) * d.luoOf.sndA (d.toSOLin Z)) =
      LinearMap.trace F d.V (adV d.QV Y.2 * adV d.QV Z.2) := rfl
  rw [e1, e2, ← h1, ← h2]
  simp only [formConst, invOf_eq_inv]
  ring

/-- **`cTheta_toSO`'s conclusion from Lie germ uniqueness on `𝔤⁰` alone** (`hgerm`, the
Lie-algebra case of Harish-Chandra 1999 Cor 5.10 / BP §4.5 for `(G, 𝔤⁰, bilin)`): all other
hypotheses of `cTheta_toSO_of_transport` are proved — the uniqueness of the orbit picked by the
recipe (`orbitSpecAt_orbit_unique`) and the transport of local expansions along
`E = c · ad`, with `c = (2^{dim W}/4, 2^{dim V}/4)` (`cTheta_toSO_of_germUnique_of_form`,
`scaleForm_traceForm_toSOLin`). -/
theorem cTheta_toSO_of_germUnique (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    {θ : ↥d.luoOf.lie → ℂ}
    (hθ : IsLieQuasiCharacter d.luoOf.Gbar d.luoOf.lie d.luoOf.traceForm ψ θ)
    (T : d.GammaTorus) (X : CliffordAlgebra d.QW) (hX : d.IsGammaEltLie T.1 X)
    (hgerm : ∀ c c'' : NilOrbit (lieGrpCentralizer d.G (d.diagLie X))
        (lieCentralizer d.lieZero (d.diagLie X)) → ℂ,
      HasGermExpansionLie d.G d.lieZero d.bilin ψ (θ ∘ d.toSO) (d.diagLie X) c →
      HasGermExpansionLie d.G d.lieZero d.bilin ψ (θ ∘ d.toSO) (d.diagLie X) c'' →
      ∀ O ∈ NilReg _ _, c O = c'' O) :
    d.germLie0 ψ (θ ∘ d.toSO) (d.diagLie X) (d.orbitChoiceLie X) =
      d.luoOf.cTheta ψ θ (d.toSOLin (d.diagLie X)) :=
  d.cTheta_toSO_of_germUnique_of_form ψ hW hV hθ T X hX _ _
    (fun _ hY _ hZ => d.scaleForm_traceForm_toSOLin hY hZ) hgerm

end GGPData

end GSpinGGP
