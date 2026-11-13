/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LieAlgebra
import GSpinGGP.Foundations.ExpHaar

/-!
# The `exp`-compatible measure on `𝔱⁰(F)`

`exists_isExpCompatT`: for the tori `T = T_x` of `Γ(G,H)`, an additive Haar measure on
`𝔱⁰(F)` compatible through `exp` with the probability Haar measure on `T(F)/A_{G,H}(F)`
(`IsExpCompatT`, defined in `TraceFormula/LieAlgebra.lean`). It is a leaf file so that
`LieAlgebra.lean` need not import the analysis of `Foundations/ExpHaar.lean`.
-/

noncomputable section

open MeasureTheory Topology Filter

set_option linter.style.haveILetI false

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

/-- **`e^X ∈ T_x` for `X ∈ 𝔱⁰` near `0`**: `e^X ∈ GSpin(W)(F)` for `X ∈ so_Cliff(W)` small
(`MovedPart.exists_nhds_expA_mem_GSpin`), and `e^X` commutes with `x` and fixes `W'_x`, as `X`
commutes with `x ∈ T_x` and kills `W'_x`. -/
theorem eventually_exists_mem_torusOf_eq_expA (x : ↥(GSpin d.QW)) :
    ∀ᶠ X in 𝓝 (0 : CliffordAlgebra d.QW), X ∈ d.lieTorus (d.torusOf x) →
      ∃ t : ↥(d.torusOf x),
        (((t : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) = expA F X := by
  letI := isTopologicalRing_of_moduleTopology F (CliffordAlgebra d.QW)
  set T := d.torusOf x with hT
  have hxT : x ∈ T := ⟨Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff] at hh; rw [hh], fun v hv => by
    simpa [sub_eq_zero] using LinearMap.mem_ker.mp hv⟩
  obtain ⟨U₁, hU₁, h₁⟩ := MovedPart.exists_nhds_expA_mem_GSpin (F := F) d.QW
  filter_upwards [hU₁] with X hX hXT
  obtain ⟨g, hg⟩ := h₁ X hX hXT.1.1
  have hcomm : ∀ y : CliffordAlgebra d.QW, Commute y X → Commute y (expA F X) :=
    fun y h => commute_expA_of_commute (F := F) h
  refine ⟨⟨g, ⟨Subgroup.mem_centralizer_iff.mpr fun h hh => ?_, fun w hw => ?_⟩⟩, hg⟩
  · rw [Set.mem_singleton_iff] at hh
    subst hh
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hg]
    exact (hcomm _ (hXT.2.1 h hxT)).eq
  · have hwc : w ∈ commonFixed T := by
      refine (Submodule.mem_iInf _).mpr fun t => ?_
      have := t.2.2 w hw
      exact LinearMap.mem_ker.mpr (by simp [this])
    have had := hXT.2.2 w hwc
    have hc : Commute (CliffordAlgebra.ι d.QW w) X := by
      have := ι_adV hXT.1.1 w
      rw [had, map_zero] at this
      exact (sub_eq_zero.mp this.symm).symm
    apply CliffordAlgebra.ι_injective d.QW
    have e : ((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * CliffordAlgebra.ι d.QW w =
        CliffordAlgebra.ι d.QW w * ((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) := by
      rw [hg]; exact (hcomm _ hc).eq.symm
    rw [ι_specP, e, mul_assoc, Units.mul_inv, mul_one]

/-- **An `exp`-compatible Haar measure on `𝔱⁰(F)` exists** for the tori `T = T_x` of
`Γ(G,H)` (BP §1.6, §11.1; Thesis §12.1): `T(F)` is commutative, so `exp` is a homomorphism on a
small lattice of `𝔱⁰(F)`, a homeomorphism onto an open compact subgroup of `T(F)/A_{G,H}(F)`
(`𝔱 = Lie(A_{G,H}) ⊕ 𝔱⁰`), and it carries an additive Haar measure to a multiple of the
probability Haar measure there. Proved via the isometry chart (`exists_isAddHaarMeasure_eq_expA_image`,
with `j : T(F) → C(W)ˣ`, the scalars `A_{G,H}(F) ⊆ T(F)`, and `𝔱⁰ ⊕ F = Lie(T)` near `0`). -/
theorem exists_isExpCompatT (T : d.GammaTorus) : ∃ μ, d.IsExpCompatT T.1 μ := by
  obtain ⟨T, x, hx, rfl⟩ := T
  letI := isTopologicalRing_of_moduleTopology F (CliffordAlgebra d.QW)
  haveI := t2Space_of_moduleTopology F (CliffordAlgebra d.QW)
  haveI := submodule_isTopologicalAddGroup (d.lieTorus (d.torusOf x))
  obtain ⟨_, _, _, _, _⟩ := submodule_topology (d.lieTorus (d.torusOf x))
  set T := d.torusOf x with hT
  have hxT : x ∈ T := ⟨Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff] at hh; rw [hh], fun v hv => by
    simpa [sub_eq_zero] using LinearMap.mem_ker.mp hv⟩
  let j : ↥T →* (CliffordAlgebra d.QW)ˣ := (GSpin d.QW).subtype.comp T.subtype
  have hj : Topology.IsEmbedding
      fun t : ↥T => ((j t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) :=
    (isEmbedding_units_val F).comp
      (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal)
  have hZ : ∀ t : ↥T, t ∈ d.scalarsIn T ↔
      ((j t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) ∈
        Set.range (algebraMap F (CliffordAlgebra d.QW)) := by
    intro t
    rw [scalarsIn, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨(c : F), by
        change _ = (((t : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)
        rw [← hc]; rfl⟩
    · rintro ⟨c, hc⟩
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [map_zero] at hc
        exact Units.ne_zero _ hc.symm
      exact ⟨Units.mk0 c hc0, Subtype.ext (Units.ext hc)⟩
  have hscal : ∀ c : F, c ≠ 0 → ∃ t : ↥T,
      ((j t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) =
        algebraMap F (CliffordAlgebra d.QW) c :=
    fun c hc => ⟨⟨scalarGSpin d.QW (Units.mk0 c hc), d.scalar_mem_torusOf x _⟩, rfl⟩
  have h𝔤 : ∀ t : F, algebraMap F (CliffordAlgebra d.QW) t ∈ d.lieTorus T → t = 0 :=
    fun t ht => eq_zero_of_algebraMap_mem_soSub ht.1
  have hexp : ∀ᶠ X in 𝓝 (0 : CliffordAlgebra d.QW), X ∈ d.lieTorus T →
      ∃ t : ↥T, ((j t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) = expA F X :=
    d.eventually_exists_mem_torusOf_eq_expA x
  have hlog : ∀ᶠ W in 𝓝 (0 : CliffordAlgebra d.QW), ∀ t : ↥T,
      ((j t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) = expA F W →
      ∃ c : F, W - algebraMap F (CliffordAlgebra d.QW) c ∈ d.lieTorus T := by
    obtain ⟨U₂, hU₂, h₂⟩ := exists_nhds_commute_of_commute_expA F (A := CliffordAlgebra d.QW)
    filter_upwards [eventually_mem_gspin_of_expA_mem (F := F) d.QW, hU₂] with W hW hWU t ht
    have hWg : W ∈ (gspin d.QW).toSubmodule := hW (t : GSpin d.QW) ht
    rw [gspin_eq_span_one_sup_soSub] at hWg
    obtain ⟨a, ha, S, hS, hWS⟩ := Submodule.mem_sup.mp hWg
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
    refine ⟨c, ?_⟩
    have hWS' : W - algebraMap F (CliffordAlgebra d.QW) c = S := by
      rw [← hWS, Algebra.algebraMap_eq_smul_one]; abel
    rw [hWS']
    have hcW : ∀ y : CliffordAlgebra d.QW, Commute y W → Commute y S := by
      intro y hy
      rw [← hWS']
      exact hy.sub_right (Algebra.commutes c y).symm
    refine ⟨hS, fun t' ht' => ?_, fun w hw => ?_⟩
    · have h1 : Commute ((((t' : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW)
          (expA F W) := by
        rw [← ht]
        have := hx.2.1 t' ht' (t : GSpin d.QW) t.2
        exact congrArg (fun g : GSpin d.QW => ((g : (CliffordAlgebra d.QW)ˣ) :
          CliffordAlgebra d.QW)) this.eq
      exact (hcW _ (h₂ W hWU _ h1)).eq
    · have hfix : specP d.QW (t : GSpin d.QW) w = w := by
        have h0 := LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hw t)
        simpa [sub_eq_zero] using h0
      have h1 : Commute (CliffordAlgebra.ι d.QW w) (expA F W) := by
        rw [← ht]
        have e := congrArg (CliffordAlgebra.ι d.QW) hfix
        rw [ι_specP] at e
        show CliffordAlgebra.ι d.QW w * (((t : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) =
          (((t : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * CliffordAlgebra.ι d.QW w
        conv_lhs => rw [← e]
        rw [mul_assoc, Units.inv_mul, mul_one]
      have hc := hcW _ (h₂ W hWU _ h1)
      have e2 := ι_adV hS.1 w
      rw [hc.eq, sub_self] at e2
      exact CliffordAlgebra.ι_injective d.QW (by rw [e2, map_zero])
  haveI : CompactSpace (d.TorusQuot T) := hx.2.2
  haveI : IsClosed (d.scalarsIn T : Set ↥T) := by
    have hcl : IsClosed (Set.range (algebraMap F (CliffordAlgebra d.QW))) := by
      have := Submodule.closed_of_finiteDimensional
        (Subalgebra.toSubmodule (⊥ : Subalgebra F (CliffordAlgebra d.QW)))
      simpa [Algebra.coe_bot] using this
    have e : (d.scalarsIn T : Set ↥T) = (fun t : ↥T =>
        ((j t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) ⁻¹'
          Set.range (algebraMap F (CliffordAlgebra d.QW)) := by
      ext t; exact hZ t
    rw [e]; exact hcl.preimage hj.continuous
  letI : MeasurableSpace (d.TorusQuot T) := borel _
  haveI : BorelSpace (d.TorusQuot T) := ⟨rfl⟩
  obtain ⟨μ, hμ, U, hU, hUS⟩ := exists_isAddHaarMeasure_eq_expA_image j hj (d.scalarsIn T) hZ
    hscal (d.lieTorus T) h𝔤 hexp hlog (probHaar (d.TorusQuot T))
  exact ⟨μ, hμ, U, hU, hUS⟩

end GGPData

end GSpinGGP
