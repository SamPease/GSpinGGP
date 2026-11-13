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

end GSpinGGP
