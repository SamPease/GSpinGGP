/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LuoJLie
import GSpinGGP.TraceFormula.ExpCompatH

/-!
# `J^Lie` of the triple is Luo's `J^Lie`

* `isExpCompatH_map_toSOHCLE`: the push-forwards of `Measure.haar` on `H(F)/A_{G,H}(F)` and of
  `measH0` along `H(F)/A_{G,H}(F) ≃ H̄(F)` and `ad : 𝔥⁰ ≃ 𝔥` are `exp`-compatible on Luo's side.
* `exists_JLie_transfer` (L4): `J^Lie` of `d` is Luo's `J^Lie` for compatible measures.
-/

noncomputable section

open MeasureTheory Topology Filter

set_option linter.style.haveILetI false

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

/-- **`exp`-compatibility transfers to Luo's side** (Thesis §5.2, §12.4): for an isomorphism
`e_H : H(F)/A_{G,H}(F) ≃ H̄(F)` induced by `G → Ḡ`, the push-forwards `(e_H)_* dh` and
`ad_* measH0` are `exp`-compatible. Near `0`, `e_H` carries `{e^X A_{G,H}(F) : X ∈ S}` onto
`{e^{ad X} : X ∈ S}`: `e^{ad X}` is the image of `e^X` in `Ḡ(F)`
(`eventually_toGbarU_eq_expA_toSOLin`), and `e^X ∈ H(F)` for `X ∈ 𝔥⁰` small
(`eventually_exists_mem_H_eq_expA`). -/
theorem isExpCompatH_map_toSOHCLE (eH : d.HmodAGH ≃ₜ* ↥d.luoOf.Hbar)
    (heH : ∀ h : ↥d.H, ((eH (QuotientGroup.mk h) : ↥d.luoOf.Gbar)) = d.toGbar (h : ↥d.G)) :
    d.luoOf.IsExpCompatH ((Measure.haar : Measure d.HmodAGH).map eH)
      (d.measH0.map d.toSOHCLE) := by
  obtain ⟨hμ, U, hU, hUS⟩ := d.isExpCompatH_measH0
  let e := d.toSOHCLE
  have he : e = d.toSOHCLE := rfl
  refine ⟨e.toLinearEquiv.toAddEquiv.isAddHaarMeasure_map _ e.continuous e.symm.continuous, ?_⟩
  -- the neighbourhood of `0` in `𝔥⁰` where the exponential facts hold
  have hval : Tendsto (fun X : ↥d.lieH0 => (X : d.ambient)) (𝓝 0) (𝓝 0) :=
    continuous_subtype_val.tendsto' 0 0 rfl
  have hev := hval.eventually
    ((d.eventually_exists_mem_H_eq_expA).and d.eventually_toGbarU_eq_expA_toSOLin)
  let U₀ := U ∩ {X : ↥d.lieH0 | (X : d.ambient) ∈ d.lieH0 →
      ∃ h : ↥d.H, (((h : ↥d.G) : d.ambientˣ) : d.ambient) = expA F (X : d.ambient)} ∩
    {X : ↥d.lieH0 | (X : d.ambient) ∈ d.lie → ∀ g : ↥d.G,
      ((g : d.ambientˣ) : d.ambient) = expA F (X : d.ambient) →
        ((d.toGbarU g : d.luoOf.Ambˣ) : d.luoOf.Amb) = expA F (d.toSOLin X)}
  have hU₀n : U₀ ∈ 𝓝 (0 : ↥d.lieH0) :=
    inter_mem (inter_mem hU (hev.mono fun X hX => hX.1)) (hev.mono fun X hX => hX.2)
  refine ⟨e.symm ⁻¹' U₀, e.symm.continuous.continuousAt.preimage_mem_nhds
    (by rw [map_zero]; exact hU₀n), fun S' hS' hS'U => ?_⟩
  have hSm : MeasurableSet (e ⁻¹' S') := e.continuous.measurable hS'
  have hSU : e ⁻¹' S' ⊆ U₀ := fun X hX => by simpa using hS'U hX
  rw [Measure.map_apply e.continuous.measurable hS', hUS _ hSm (hSU.trans
    (Set.inter_subset_left.trans Set.inter_subset_left))]
  let eM : d.HmodAGH ≃ᵐ ↥d.luoOf.Hbar := eH.toHomeomorph.toMeasurableEquiv
  have hmap : (Measure.haar : Measure d.HmodAGH).map eH =
      (Measure.haar : Measure d.HmodAGH).map eM := rfl
  rw [hmap, MeasurableEquiv.map_apply]
  congr 1
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨X, hX, h, hh, rfl⟩
    refine ⟨e X, hX, ?_⟩
    have hX0 := hSU hX
    have hexp := hX0.2 (d.lie0_le_lie (d.lieH0_le_lie0 X.2)) (h : ↥d.G) hh
    change (((eH (QuotientGroup.mk h) : ↥d.luoOf.Gbar) : d.luoOf.Ambˣ) : d.luoOf.Amb) = _
    rw [heH, coe_toSOHCLE]
    exact hexp
  · rintro ⟨Y, hY, hq⟩
    set X := e.symm Y with hXdef
    have hXS : X ∈ e ⁻¹' S' := by simpa [hXdef] using hY
    have hX0 := hSU hXS
    obtain ⟨h, hh⟩ := hX0.1.2 X.2
    refine ⟨X, hXS, h, hh, ?_⟩
    apply eH.injective
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    have hexp := hX0.2 (d.lie0_le_lie (d.lieH0_le_lie0 X.2)) (h : ↥d.G) hh
    change _ = (((eH (QuotientGroup.mk h) : ↥d.luoOf.Gbar) : d.luoOf.Ambˣ) : d.luoOf.Amb)
    rw [heH]
    change _ = ((d.toGbarU (h : ↥d.G) : d.luoOf.Ambˣ) : d.luoOf.Amb)
    rw [hexp]
    change (((eM q : ↥d.luoOf.Gbar) : d.luoOf.Ambˣ) : d.luoOf.Amb) = _
    rw [hq, hXdef, ← coe_toSOHCLE, he, ContinuousLinearEquiv.apply_symm_apply]

variable (ψ : NontrivialAddChar F)

/-- **(L4) `J^Lie` of `d` is Luo's `J^Lie`** for `muG`, a Haar measure `μH` on `H̄(F)`, the
`exp`-compatible `μ_𝔥` and the quotient measure: `H(F)/A_{G,H}(F) ≃ H̄(F)` (Hilbert 90 and
`ker P ∩ H = A_{G,H}`, through `quotHG_equiv_SO`), `ad : 𝔥⁰ ≃ 𝔥 = so(W) ⊕ 𝔫`, `λ` (`lam_toSO`),
`measH0` and `weilMeasureHG` push forward to an `exp`-compatible pair and its Weil
measure (independence of the `exp`-compatible pair), and change of variables.
Proved by `exists_JLie_transfer_of` with `isExpCompatH_map_toSOHCLE`. -/
theorem exists_JLie_transfer (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) :
    ∃ (μH : Measure ↥d.luoOf.Hbar) (μ𝔥 : Measure ↥d.luoOf.lieH)
      (m : Measure (CosetSpace d.luoOf.Hbar.subtype)),
      μH.IsHaarMeasure ∧ d.luoOf.IsExpCompatH μH μ𝔥 ∧
      IsWeilMeasure d.luoOf.Hbar.subtype d.muG μH m ∧
      ∀ f : ↥d.lieZero → ℂ, d.IsLieScusp f →
        d.distribJLie ψ f = d.luoOf.distribJLie ψ μ𝔥 m (f ∘ d.toSO.symm) :=
  d.exists_JLie_transfer_of ψ hW hV d.isExpCompatH_map_toSOHCLE

end GGPData

end GSpinGGP

