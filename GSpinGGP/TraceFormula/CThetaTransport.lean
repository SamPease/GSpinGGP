/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.OrbitSpecUnique
import GSpinGGP.TraceFormula.ExpIntertwine
import GSpinGGP.TraceFormula.LuoJLie
import GSpinGGP.TraceFormula.JHatScale
import GSpinGGP.Literature.HarishChandra

/-!
# Transport of local expansions from `so(W) ⊕ so(V)` to `𝔤⁰` (Thesis §6.5, (L6))

For `X ∈ so(W)` with `ad X` semisimple, local expansions of a quasi-character `θ` on
`so(W) ⊕ so(V)` at `ad X` (Luo's normalization: the trace form) give local expansions of `θ ∘ ad`
on `𝔤⁰ = so(W) ⊕ so(V)` at `X` (the trace form `bilin` of `C(W) × C(V)`).  The map of nilpotent
orbits is `ad`, followed by the rescaling of each factor that turns `bilin` into the trace form.

* `LuoDatum.conj_mem_lie_of_mem_Gbar`, `eventually_expA_mem_Gbar`,
  `LuoDatum.eventually_mem_lie_of_expA_mem`: `Ḡ(F) = SO(W) × SO(V)` and `so(W) ⊕ so(V)` correspond
  under `exp` near `0`;
* `isOrbitMeasure_unique_luo`: hence orbit measures on centralizers `(Ḡ_Y, 𝔤_Y)` are unique.
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
  · show L.fstA Y ∈ (bform L.QW).skewAdjointSubmodule
    rw [LinearMap.mem_skewAdjointSubmodule]
    refine k1 ?_
    have e : expA F (L.fstA Y) = ((L.unitFst g : (Module.End F L.W)ˣ) : Module.End F L.W) := by
      have := h1
      simp only [AlgHom.toLinearMap_apply] at this
      rw [← this, ← hgY]
      rfl
    rw [e]
    exact isOrthogonal_of_mem_SOu hg.1
  · show L.sndA Y ∈ (bform L.QV).skewAdjointSubmodule
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

/-- `ad(g Y g⁻¹) = P(g) ad(Y) P(g)⁻¹` for `g ∈ G(F)` and `Y ∈ 𝔤` (`adV_conj` on each factor). -/
theorem toSOLin_conj (g : ↥d.G) {Y : d.ambient} (hY : Y ∈ d.lie) :
    d.toSOLin (((g : d.ambientˣ) : d.ambient) * Y * (((g : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient)) =
      ((d.toGbarU g : d.luoOf.Ambˣ) : d.luoOf.Amb) * d.toSOLin Y *
        (((d.toGbarU g)⁻¹ : d.luoOf.Ambˣ) : d.luoOf.Amb) := by
  have hinv : (d.toGbarU g)⁻¹ = d.toGbarU g⁻¹ := (map_inv d.toGbarU g).symm
  rw [hinv]
  refine Prod.ext (LinearMap.ext fun v => ?_) (LinearMap.ext fun v => ?_)
  · have h := adV_conj (d.fst g) hY.1 v
    rw [← map_inv] at h
    exact h
  · have h := adV_conj (d.snd g) hY.2 v
    rw [← map_inv] at h
    exact h

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
    (hν : IsOrbitMeasure (lieGrpCentralizer d.luoOf.Gbar Y) (lieCentralizer d.luoOf.lie Y) b ψ O ν) :
    μ = ν :=
  isOrbitMeasure_unique_lieCentralizer d.luoOf.conj_mem_lie_of_mem_Gbar d.eventually_expA_mem_Gbar
    d.luoOf.eventually_mem_lie_of_expA_mem Y hμ hν

end GGPData

/-! ## `ad` detects nilpotent and semisimple elements of `𝔤⁰` -/

section Converse

/-- In a product of algebras, nilpotency is componentwise. -/
theorem isNilpotent_prod_iff {A₁ A₂ : Type*} [Ring A₁] [Ring A₂] {Y : A₁ × A₂} :
    IsNilpotent Y ↔ IsNilpotent Y.1 ∧ IsNilpotent Y.2 := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨⟨n, by rw [← Prod.pow_fst, hn]; rfl⟩, ⟨n, by rw [← Prod.pow_snd, hn]; rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨a + b, Prod.ext ?_ ?_⟩
    · rw [Prod.pow_fst, pow_add, ha, zero_mul]; rfl
    · rw [Prod.pow_snd, pow_add, hb, mul_zero]; rfl

/-- A nilpotent difference `y − s` of commuting semisimple elements is `0`. -/
theorem eq_zero_of_isNilpotent_of_eq_sub {B : Type*} [Ring B] [Algebra F B] [FiniteDimensional F B]
    {y s n : B} (hy : IsSS F y) (hs : IsSS F s) (hc : Commute y s) (hn : IsNilpotent n)
    (h : n = y - s) : n = 0 := by
  have hcomm : Commute (Algebra.lmul F B y) (Algebra.lmul F B s) := hc.map (Algebra.lmul F B)
  have hsem : (Algebra.lmul F B n).IsSemisimple := by
    rw [h, map_sub]
    exact Module.End.IsSemisimple.sub_of_commute hcomm hy hs
  have hnl : IsNilpotent (Algebra.lmul F B n) := hn.map (Algebra.lmul F B)
  have h0 := Module.End.eq_zero_of_isNilpotent_isSemisimple hnl hsem
  exact Algebra.lmul_injective (R := F) (h0.trans (map_zero _).symm)

/-- In a product of finite-dimensional algebras, an element with semisimple components is
semisimple: in its Jordan decomposition `Y = s + n` (`exists_jordan_algebra`) each component of
`n` is the difference of two commuting semisimple elements, hence semisimple and nilpotent, hence
`0`. -/
theorem isSS_prod {A₁ A₂ : Type*} [Ring A₁] [Algebra F A₁] [FiniteDimensional F A₁] [Ring A₂]
    [Algebra F A₂] [FiniteDimensional F A₂] {Y : A₁ × A₂} (h1 : IsSS F Y.1) (h2 : IsSS F Y.2) :
    IsSS F Y := by
  obtain ⟨s, hs, n, -, hss, hnil, hY⟩ := exists_jordan_algebra (F := F) Y
  have hc : Commute Y s := Algebra.commute_of_mem_adjoin_self hs
  have e1 : n.1 = 0 := eq_zero_of_isNilpotent_of_eq_sub h1
    (isSS_algHom (AlgHom.fst F A₁ A₂) hss) (hc.map (AlgHom.fst F A₁ A₂))
    (hnil.map (AlgHom.fst F A₁ A₂)) (by rw [hY]; simp)
  have e2 : n.2 = 0 := eq_zero_of_isNilpotent_of_eq_sub h2
    (isSS_algHom (AlgHom.snd F A₁ A₂) hss) (hc.map (AlgHom.snd F A₁ A₂))
    (hnil.map (AlgHom.snd F A₁ A₂)) (by rw [hY]; simp)
  have hn0 : n = 0 := Prod.ext e1 e2
  rw [hY, hn0, add_zero]
  exact hss

/-- `IsSS F M` (left multiplication by `M` on `End U` semisimple) implies `M` semisimple on `U`. -/
theorem isSemisimple_of_isSS_end {U : Type*} [AddCommGroup U] [Module F U] [Module.Finite F U]
    {M : Module.End F U} (h : IsSS F M) : M.IsSemisimple := by
  set p := minpoly F (LinearMap.mulLeft F M)
  have hsq : Squarefree p := Module.End.IsSemisimple.minpoly_squarefree h
  have h0 : Polynomial.aeval (Algebra.lmul F (Module.End F U) M) p = 0 := minpoly.aeval F _
  rw [Polynomial.aeval_algHom_apply] at h0
  have h1 : Polynomial.aeval M p = 0 :=
    Algebra.lmul_injective (R := F) (h0.trans (map_zero _).symm)
  exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq h1

variable {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]

/-- **`X ∈ so_Cliff(V)` is nilpotent if `ad X` is** (converse of `isNilpotent_adV`): in the Jordan
decomposition `X = s + n` in `gspin(V)`, `ad s = ad X − ad n` is semisimple and nilpotent, so `s` is
a scalar (`eq_algebraMap_of_adV_eq_zero`), which vanishes since `X` and `n` are traceless. -/
theorem isNilpotent_of_isNilpotent_adV {Q : QuadraticForm F V} (hQ : IsNondeg Q)
    {X : CliffordAlgebra Q} (hX : X ∈ soSub Q) (h : IsNilpotent (adV Q X)) : IsNilpotent X := by
  obtain ⟨s, -, n, hn, hss, hnil, rfl, hsg, hng⟩ := exists_jordan_gspin hX.1
  have hc : (s + n) * n = n * (s + n) := (Algebra.commute_of_mem_adjoin_self hn).eq
  have hcV : Commute (adV Q (s + n)) (adV Q n) := by
    have h' := adV_commutator hX.1 hng
    rw [hc, sub_self, map_zero, eq_comm, sub_eq_zero] at h'
    exact h'
  have hsV : adV Q s = adV Q (s + n) - adV Q n := by rw [map_add, add_sub_cancel_right]
  have hnilV : IsNilpotent (adV Q s) := hsV ▸ hcV.isNilpotent_sub h (isNilpotent_adV hng hnil)
  have h0 : adV Q s = 0 :=
    Module.End.eq_zero_of_isNilpotent_isSemisimple hnilV (isSemisimple_adV hsg hss)
  obtain ⟨r, hr⟩ := eq_algebraMap_of_adV_eq_zero hQ hsg h0
  have htr := hX.2
  rw [cliffTrace_add, hr, cliffTrace_algebraMap, cliffTrace_eq_zero_of_isNilpotent Q hnil,
    add_zero] at htr
  have hr0 : r = 0 := (mul_eq_zero.mp htr).resolve_right (cast_finrank_cliffordAlgebra_ne_zero Q)
  rw [hr, hr0, map_zero, zero_add]
  exact hnil

/-- **`X ∈ gspin(V)` is semisimple if `ad X` is** (over `F`; the semisimplicity over `F̄` needed by
`isSemisimple_mulLeft_of_isSemisimple_adV_baseChange` follows, `F` being perfect). -/
theorem isSS_of_isSemisimple_adV {Q : QuadraticForm F V} (hQ : IsNondeg Q)
    {X : CliffordAlgebra Q} (hX : X ∈ gspin Q) (h : (adV Q X).IsSemisimple) : IsSS F X :=
  isSemisimple_mulLeft_of_isSemisimple_adV_baseChange hQ hX
    (IsomCent.isSemisimple_baseChange_algebraicClosure h)

end Converse

namespace GGPData

variable (d : GGPData F)

/-- `ad Y` is nilpotent iff `Y` is, for `Y ∈ 𝔤⁰`. -/
theorem isNilpotent_toSOLin_iff {Y : d.ambient} (hY : Y ∈ d.lieZero) :
    IsNilpotent (d.toSOLin Y) ↔ IsNilpotent Y := by
  constructor
  · intro h
    have h1 : IsNilpotent (adV d.QW Y.1) := h.map d.luoOf.fstA
    have h2 : IsNilpotent (adV d.QV Y.2) := h.map d.luoOf.sndA
    exact isNilpotent_prod_iff.mpr ⟨isNilpotent_of_isNilpotent_adV d.nondeg hY.1 h1,
      isNilpotent_of_isNilpotent_adV d.nondeg_QV hY.2 h2⟩
  · intro h
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := isNilpotent_prod_iff.mp h
    obtain ⟨a', ha'⟩ := isNilpotent_adV hY.1.1 ⟨a, ha⟩
    obtain ⟨b', hb'⟩ := isNilpotent_adV hY.2.1 ⟨b, hb⟩
    refine ⟨a' + b', Prod.ext ?_ ?_⟩
    · change d.luoOf.fstA (d.toSOLin Y ^ (a' + b')) = 0
      rw [map_pow, fstA_toSOLin]
      exact pow_eq_zero_of_le (Nat.le_add_right a' b') ha'
    · change d.luoOf.sndA (d.toSOLin Y ^ (a' + b')) = 0
      rw [map_pow, sndA_toSOLin]
      exact pow_eq_zero_of_le (Nat.le_add_left b' a') hb'

/-- `ad Y` is semisimple iff `Y` is, for `Y ∈ 𝔤⁰`. -/
theorem isSS_toSOLin_iff {Y : d.ambient} (hY : Y ∈ d.lieZero) :
    IsSS F (d.toSOLin Y) ↔ IsSS F Y := by
  refine ⟨fun h => ?_, d.isSS_toSOLin hY⟩
  have h1 : IsSS F (d.luoOf.fstA (d.toSOLin Y)) := isSS_algHom _ h
  have h2 : IsSS F (d.luoOf.sndA (d.toSOLin Y)) := isSS_algHom _ h
  rw [fstA_toSOLin] at h1
  rw [sndA_toSOLin] at h2
  exact isSS_prod (isSS_of_isSemisimple_adV d.nondeg hY.1.1 (isSemisimple_of_isSS_end h1))
    (isSS_of_isSemisimple_adV d.nondeg_QV hY.2.1 (isSemisimple_of_isSS_end h2))

end GGPData

/-! ## `ad` as an isomorphism of descent data at a point of `𝔤⁰` -/

theorem mem_lieCentralizer_units_one {A : Type*} [Ring A] [Algebra F A] {𝔤 : LieSubalgebra F A}
    {Y : A} : Y ∈ lieCentralizer 𝔤 ((1 : Aˣ) : A) ↔ Y ∈ 𝔤 := by
  rw [Units.val_one, lieCentralizer_one]

namespace GGPData

variable (d : GGPData F)

/-- `ad` is injective on `𝔤⁰` (`toSO_bijective`). -/
theorem eq_of_toSOLin_eq {Y Z : d.ambient} (hY : Y ∈ d.lieZero) (hZ : Z ∈ d.lieZero)
    (h : d.toSOLin Y = d.toSOLin Z) : Y = Z :=
  congrArg Subtype.val (d.toSO_bijective.1 (a₁ := ⟨Y, hY⟩) (a₂ := ⟨Z, hZ⟩) (Subtype.ext h))

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

/-- Conjugation by `G(F)` preserves `𝔤⁰`. -/
theorem conj_mem_lieZero_of_mem : ∀ g ∈ d.G, ∀ Y ∈ d.lieZero,
    (g : d.ambient) * Y * (↑g⁻¹ : d.ambient) ∈ d.lieZero :=
  fun g hg _ hY => d.conj_mem_lie0 ⟨g, hg⟩ hY

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

end GSpinGGP
