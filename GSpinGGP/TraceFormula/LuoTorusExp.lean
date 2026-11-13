/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.ExpCompatT
import GSpinGGP.TraceFormula.ExpIntertwine
import GSpinGGP.GGP.TorusIntegral

/-!
# The measures `ν(T) dX` on the tori of `Γ(G,H)` and of Luo's `𝒯`

For `x ∈ Γ(G,H)`, `T = T_x` and `φ : t ↦ (P(t), P(t) ⊕ 1)`:

* `torusQuotHomeomorph`: `T(F)/A_{G,H}(F) ≃ φ(T)(F)` as topological groups (`torusQuotMap` is a
  continuous bijection from a compact group);
* `isExpCompatT_map_lieTorusCLE`: `ad : 𝔱⁰ ≃ 𝔱` carries the `exp`-compatible measure on `𝔱⁰(F)` to
  the `exp`-compatible measure on Luo's `𝔱(F)`, since `φ(e^X) = e^{ad X}` near `0`;
* `exists_luo_isExpCompatT`: every torus of Luo's `𝒯` carries an `exp`-compatible measure (every
  such torus is some `φ(T_x)`, `exists_isGammaElt_torusOf_eq_of_luo`).
-/

noncomputable section

open MeasureTheory Topology Filter

set_option linter.style.haveILetI false

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

/-- `T(F)/A_{G,H}(F) ≃* φ(T)(F)`, induced by `φ : t ↦ (P(t), P(t) ⊕ 1)`. -/
def torusQuotMulEquiv (T : Subgroup ↥(GSpin d.QW)) :
    d.TorusQuot T ≃* ↥(T.map (d.toGbarU.comp d.diag)) :=
  (MonoidHom.ofInjective (d.torusQuotMap_injective T)).trans
    (MulEquiv.subgroupCongr (d.range_torusQuotMap T))

@[simp] theorem coe_torusQuotMulEquiv (T : Subgroup ↥(GSpin d.QW)) (q : d.TorusQuot T) :
    ((d.torusQuotMulEquiv T q : ↥(T.map (d.toGbarU.comp d.diag))) : d.luoOf.Ambˣ) =
      d.torusQuotMap T q := rfl

/-- **`T(F)/A_{G,H}(F) ≃ φ(T)(F)` as topological groups** when `T(F)/A_{G,H}(F)` is compact:
`torusQuotMap` is a continuous bijection onto `φ(T)` from a compact space to a Hausdorff one. -/
def torusQuotHomeomorph (T : Subgroup ↥(GSpin d.QW)) [CompactSpace (d.TorusQuot T)] :
    d.TorusQuot T ≃ₜ* ↥(T.map (d.toGbarU.comp d.diag)) :=
  haveI : T2Space d.luoOf.Amb := t2Space_of_moduleTopology F d.luoOf.Amb
  let h : d.TorusQuot T ≃ₜ ↥(T.map (d.toGbarU.comp d.diag)) :=
    Continuous.homeoOfEquivCompactToT2 (f := (d.torusQuotMulEquiv T).toEquiv)
      ((d.continuous_torusQuotMap T).subtype_mk _)
  { d.torusQuotMulEquiv T with
    continuous_toFun := h.continuous
    continuous_invFun := h.symm.continuous }

@[simp] theorem coe_torusQuotHomeomorph (T : Subgroup ↥(GSpin d.QW))
    [CompactSpace (d.TorusQuot T)] (q : d.TorusQuot T) :
    ((d.torusQuotHomeomorph T q : ↥(T.map (d.toGbarU.comp d.diag))) : d.luoOf.Ambˣ) =
      d.torusQuotMap T q := rfl

/-- **`ad : 𝔱⁰ ≃ 𝔱` carries `ν(T) dX` to `ν(φ(T)) dX`** (Thesis §12.1; Luo §7.1) for
`x ∈ Γ(G,H)`, `T = T_x`: if `μ` on `𝔱⁰(F)` is compatible through `exp` with the probability Haar
measure on `T(F)/A_{G,H}(F)`, then `ad_* μ` on Luo's `𝔱(F)` is compatible through `exp` with the
probability Haar measure on `φ(T)(F)`. Near `0`, `T(F)/A_{G,H}(F) ≃ φ(T)(F)`
(`torusQuotHomeomorph`, which carries probability Haar measure to probability Haar measure,
`probHaar_preimage`) maps
`{e^X A_{G,H}(F) : X ∈ S}` onto `{e^{ad X} : X ∈ S}`: `φ(e^X) = e^{ad X}`
(`eventually_toGbarU_diag_eq_expA`) and `e^X ∈ T(F)` (`eventually_exists_mem_torusOf_eq_expA`). -/
theorem isExpCompatT_map_lieTorusCLE {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    {μ : Measure ↥(d.lieTorus (d.torusOf x))} (hμ : d.IsExpCompatT (d.torusOf x) μ) :
    d.luoOf.IsExpCompatT ((d.torusOf x).map (d.toGbarU.comp d.diag))
      (μ.map (d.lieTorusCLE (d.torusOf x))) := by
  haveI : CompactSpace (d.TorusQuot (d.torusOf x)) := hx.2.2
  set T := d.torusOf x with hT
  letI : MeasurableSpace (d.TorusQuot T) := borel _
  haveI : BorelSpace (d.TorusQuot T) := ⟨rfl⟩
  letI : MeasurableSpace ↥(T.map (d.toGbarU.comp d.diag)) := borel _
  haveI : BorelSpace ↥(T.map (d.toGbarU.comp d.diag)) := ⟨rfl⟩
  have := submodule_isTopologicalAddGroup (d.lieTorus T)
  have := submodule_isTopologicalAddGroup (d.luoOf.lieTorus (T.map (d.toGbarU.comp d.diag)))
  obtain ⟨hμH, U, hU, hUS⟩ := hμ
  let e := d.lieTorusCLE T
  have he : e = d.lieTorusCLE T := rfl
  refine ⟨e.toLinearEquiv.toAddEquiv.isAddHaarMeasure_map _ e.continuous e.symm.continuous, ?_⟩
  -- the neighbourhood of `0` in `𝔱⁰` where the exponential facts hold
  have hval : Tendsto (fun X : ↥(d.lieTorus T) => (X : CliffordAlgebra d.QW)) (𝓝 0) (𝓝 0) :=
    continuous_subtype_val.tendsto' 0 0 rfl
  have hev := hval.eventually
    ((d.eventually_exists_mem_torusOf_eq_expA x).and d.eventually_toGbarU_diag_eq_expA)
  let U₀ := U ∩ {X : ↥(d.lieTorus T) | (X : CliffordAlgebra d.QW) ∈ d.lieTorus T →
      ∃ t : ↥T, (((t : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) =
        expA F (X : CliffordAlgebra d.QW)} ∩
    {X : ↥(d.lieTorus T) | (X : CliffordAlgebra d.QW) ∈ soSub d.QW → ∀ y : ↥(GSpin d.QW),
      ((y : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) = expA F (X : CliffordAlgebra d.QW) →
        ((d.toGbarU (d.diag y) : d.luoOf.Ambˣ) : d.luoOf.Amb) =
          expA F (d.toSOLin (d.diagLie X))}
  have hU₀n : U₀ ∈ 𝓝 (0 : ↥(d.lieTorus T)) :=
    inter_mem (inter_mem hU (hev.mono fun X hX => hX.1)) (hev.mono fun X hX => hX.2)
  refine ⟨e.symm ⁻¹' U₀, e.symm.continuous.continuousAt.preimage_mem_nhds
    (by rw [map_zero]; exact hU₀n), fun S' hS' hS'U => ?_⟩
  have hSm : MeasurableSet (e ⁻¹' S') := e.continuous.measurable hS'
  have hSU : e ⁻¹' S' ⊆ U₀ := fun X hX => by simpa using hS'U hX
  refine (Measure.map_apply e.continuous.measurable hS').trans ((hUS _ hSm (hSU.trans
    (Set.inter_subset_left.trans Set.inter_subset_left))).trans ?_)
  let E := d.torusQuotHomeomorph T
  haveI : CompactSpace ↥(T.map (d.toGbarU.comp d.diag)) := E.toHomeomorph.compactSpace
  refine Eq.trans ?_ (probHaar_preimage E _)
  congr 1
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨X, hX, t, ht, rfl⟩
    refine ⟨e X, hX, ?_⟩
    have hX0 := hSU hX
    change ((d.torusQuotMap T (t : d.TorusQuot T) : d.luoOf.Ambˣ) : d.luoOf.Amb) = _
    exact hX0.2 X.2.1 (t : ↥(GSpin d.QW)) ht
  · rintro ⟨Y, hY, hq⟩
    obtain ⟨X, rfl⟩ := e.surjective Y
    have hX0 := hSU hY
    obtain ⟨t, ht⟩ := hX0.1.2 X.2
    refine ⟨X, hY, t, ht, E.injective (Subtype.ext (Units.ext ?_))⟩
    refine hq.trans ?_
    change _ = ((d.toGbarU (d.diag (t : ↥(GSpin d.QW))) : d.luoOf.Ambˣ) : d.luoOf.Amb)
    rw [hX0.2 X.2.1 (t : ↥(GSpin d.QW)) ht]
    rfl

/-- **Every torus of Luo's `𝒯` carries an `exp`-compatible measure** `ν(T) dX` (Luo §7.1): such a
torus is `φ(T_x)` for some `x ∈ Γ(G,H)` (`exists_isGammaElt_torusOf_eq_of_luo`), `𝔱⁰(F)` carries
one (`exists_isExpCompatT`), and `ad` transports it (`isExpCompatT_map_lieTorusCLE`). -/
theorem exists_luo_isExpCompatT (T : d.luoOf.GammaTorus) :
    ∃ μ, d.luoOf.IsExpCompatT T.1 μ := by
  obtain ⟨T, X, hX, rfl⟩ := T
  obtain ⟨x, hx, hxX⟩ := d.exists_isGammaElt_torusOf_eq_of_luo hX
  obtain ⟨μ, hμ⟩ := d.exists_isExpCompatT ⟨_, x, hx, rfl⟩
  change ∃ μ, d.luoOf.IsExpCompatT (d.luoOf.torusOf X) μ
  rw [hxX]
  exact ⟨_, d.isExpCompatT_map_lieTorusCLE hx hμ⟩

end GGPData

end GSpinGGP
