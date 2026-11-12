/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.ExpLocal
import GSpinGGP.Foundations.GSpin

/-!
# The exponential on `GSpin` near the identity

The exponential and the group of points of `GSpin` correspond near the identity: small elements of
`gspin` exponentiate into `GSpin(F)`, and conversely. (The first lemma keeps its historical
namespace `MovedPart`.)

* `MovedPart.exists_nhds_expA_mem_GSpin`: `e^X ∈ GSpin(V)(F)` for small `X ∈ gspin(V)`, and
  conversely `eventually_mem_gspin_of_expA_mem`;
* `eventually_expA_mem_G`, `eventually_mem_lie_of_expA_mem`: the same for
  `G = GSpin(W) × GSpin(V)` and `𝔤 = gspin(W) × gspin(V)` (componentwise, `eventually_expA_ambient`).
-/

noncomputable section

open MeasureTheory Filter Topology Module
open scoped Classical

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]


/-! ### `GSpin(V)(F)` and `gspin(V)` near the identity

The exponential of a small element of `gspin(W)` lies in `GSpin(W)(F)`
(`MovedPart.exists_nhds_expA_mem_GSpin`): conjugation by `e^X` is `e^{ad X}` (`expA_ad_eq`), which
preserves the `ad X`-stable subspace `ι(W)`. -/

namespace MovedPart

variable {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A]
  [IsModuleTopology F A]

/-- **`e^X ∈ GSpin(V)` for `X ∈ gspin(V)` near `0`**: `e^X` is a unit (inverse `e^{-X}`), even
(`e^X ∈ F[X] ⊆ C⁺(V)`), and conjugation by `e^{±X}` preserves `ι(V)`, which is `ad X`-stable
(`exists_nhds_expA_conj_mem`). -/
lemma exists_nhds_expA_mem_GSpin {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (Q : QuadraticForm F V) :
    ∃ U ∈ 𝓝 (0 : CliffordAlgebra Q), ∀ X ∈ U, X ∈ gspin Q →
      ∃ g : GSpin Q, (((g : (CliffordAlgebra Q)ˣ)) : CliffordAlgebra Q) = expA F X := by
  obtain ⟨U₁, hU₁, hconj⟩ := exists_nhds_expA_conj_mem (F := F) (A := CliffordAlgebra Q)
  obtain ⟨U₂, hU₂, hinv⟩ := expA_mul_expA_neg F (A := CliffordAlgebra Q)
  obtain ⟨U₃, hU₃, hadj⟩ := exists_nhds_expA_mem_adjoin F (A := CliffordAlgebra Q)
  have hneg : (fun X : CliffordAlgebra Q => -X) ⁻¹' (U₁ ∩ U₂) ∈ 𝓝 (0 : CliffordAlgebra Q) := by
    have hc : ContinuousAt (fun X : CliffordAlgebra Q => -X) 0 := continuous_neg.continuousAt
    exact hc.preimage_mem_nhds (by rw [neg_zero]; exact inter_mem hU₁ hU₂)
  refine ⟨U₁ ∩ U₂ ∩ U₃ ∩ (fun X : CliffordAlgebra Q => -X) ⁻¹' (U₁ ∩ U₂),
    inter_mem (inter_mem (inter_mem hU₁ hU₂) hU₃) hneg, ?_⟩
  rintro X ⟨⟨⟨hX1, hX2⟩, hX3⟩, ⟨hXn1, hXn2⟩⟩ hX
  have hXn : -X ∈ gspin Q := neg_mem hX
  have hR : ∀ Z ∈ gspin Q, ∀ r ∈ LinearMap.range (CliffordAlgebra.ι Q), Z * r - r * Z ∈ LinearMap.range (CliffordAlgebra.ι Q) := by
    rintro Z hZ _ ⟨v, rfl⟩
    rw [← Ring.lie_def]
    exact hZ.2 v
  have h1 : expA F X * expA F (-X) = 1 := hinv X hX2
  have h2 : expA F (-X) * expA F X = 1 := by
    simpa using hinv (-X) hXn2
  let u : (CliffordAlgebra Q)ˣ := ⟨expA F X, expA F (-X), h1, h2⟩
  have heven : expA F X ∈ CliffordAlgebra.even Q :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hX.1) (hadj X hX3)
  refine ⟨⟨u, heven, fun v => ?_, fun v => ?_⟩, rfl⟩
  · exact hconj X hX1 _ (hR X hX) _ ⟨v, rfl⟩
  · have := hconj (-X) hXn1 _ (hR (-X) hXn) _ ⟨v, rfl⟩
    rw [neg_neg] at this
    exact this

end MovedPart

section Clifford

open CliffordAlgebra

variable {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] (Q : QuadraticForm F V)

/-- **The logarithm of `GSpin(Q)` near `1` lies in `gspin(Q)`** (converse of
`MovedPart.exists_nhds_expA_mem_GSpin`): for `Y` near `0` in `C(Q)`, if
`e^Y ∈ GSpin(Q)` then `Y` is even (`e^Y` is, and `exp` detects subalgebras near `0`) and
`[Y, ι(V)] ⊆ ι(V)` (`e^{ad Y} = Ad(e^Y)` preserves `ι(V)`, and `exp` detects the stabilizer of
`ι(V)` in `End(C(Q))`). -/
theorem eventually_mem_gspin_of_expA_mem :
    ∀ᶠ Y in 𝓝 (0 : CliffordAlgebra Q), ∀ g : ↥(GSpin Q),
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = expA F Y → Y ∈ gspin Q := by
  letI : TopologicalSpace (Module.End F (CliffordAlgebra Q)) :=
    moduleTopology F (Module.End F (CliffordAlgebra Q))
  haveI : IsModuleTopology F (Module.End F (CliffordAlgebra Q)) := ⟨rfl⟩
  letI := isTopologicalRing_of_moduleTopology F (Module.End F (CliffordAlgebra Q))
  obtain ⟨U₁, hU₁, hsub⟩ := exists_nhds_mem_of_expA_mem F (A := CliffordAlgebra Q)
  obtain ⟨U₂, hU₂, hneg⟩ := expA_mul_expA_neg F (A := CliffordAlgebra Q)
  obtain ⟨UB, hUB, hsubB⟩ := exists_nhds_mem_of_expA_mem F (A := Module.End F (CliffordAlgebra Q))
  set ad : CliffordAlgebra Q →ₗ[F] Module.End F (CliffordAlgebra Q) :=
    (Algebra.lmul F (CliffordAlgebra Q)).toLinearMap - mulRightₗ with had
  have hadc : Continuous ad := IsModuleTopology.continuous_of_linearMap ad
  have h3 : ad ⁻¹' UB ∈ 𝓝 (0 : CliffordAlgebra Q) :=
    hadc.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  filter_upwards [hU₁, hU₂, h3, expA_ad_eq F (B := CliffordAlgebra Q)] with Y hY₁ hY₂ hY₃ hY₄
  intro g hg
  obtain ⟨hg0, hg1, -⟩ := g.2
  have hginv : (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      expA F (-Y) := Units.inv_eq_of_mul_eq_one_right (by rw [hg]; exact hneg Y hY₂)
  refine ⟨hsub Y hY₁ (CliffordAlgebra.even Q) (hg ▸ hg0), fun v => ?_⟩
  -- `Ad(e^Y) = e^{ad Y}` preserves `ι(V)`
  have hAd : expA F (ad Y) ∈ stabSubalgebra (LinearMap.range (ι Q)) := by
    have : ad Y = LinearMap.mulLeft F Y - LinearMap.mulRight F Y := rfl
    rw [this, hY₄, mem_stabSubalgebra]
    rintro _ ⟨w, rfl⟩
    have := hg1 w
    rw [hg, hginv] at this
    simpa [mul_assoc] using this
  have hmem := hsubB _ hY₃ _ hAd (ι Q v) (LinearMap.mem_range_self _ v)
  have : ad Y (ι Q v) = ⁅Y, ι Q v⁆ := by
    simp [had, mulRightₗ_apply, Ring.lie_def]
  rwa [this] at hmem

end Clifford

/-! ### `G = GSpin(W) × GSpin(V)` -/

section GGP

variable (d : GGPData F)

/-- `expA` on `C(W) × C(V)` is computed componentwise near `0`. -/
theorem eventually_expA_ambient :
    ∀ᶠ X in 𝓝 (0 : d.ambient), (expA F X).1 = expA F X.1 ∧ (expA F X).2 = expA F X.2 := by
  have h1 := eventually_map_expA (F := F) (A := d.ambient)
    (LinearMap.fst F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) (fun X n => Prod.pow_fst X n)
  have h2 := eventually_map_expA (F := F) (A := d.ambient)
    (LinearMap.snd F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) (fun X n => Prod.pow_snd X n)
  filter_upwards [h1, h2] with X hX1 hX2
  exact ⟨hX1, hX2⟩

/-- **`e^X ∈ G(F)` for `X ∈ 𝔤` near `0`** (componentwise `MovedPart.exists_nhds_expA_mem_GSpin`). -/
theorem eventually_expA_mem_G :
    ∀ᶠ X in 𝓝 (0 : d.ambient), X ∈ d.lie → ∃ g : ↥d.G, ((g : d.ambientˣ) : d.ambient) = expA F X := by
  obtain ⟨U₁, hU₁, h₁⟩ := MovedPart.exists_nhds_expA_mem_GSpin (F := F) d.QW
  obtain ⟨U₂, hU₂, h₂⟩ := MovedPart.exists_nhds_expA_mem_GSpin (F := F) d.QV
  have hf : (fun X : d.ambient => X.1) ⁻¹' U₁ ∈ 𝓝 (0 : d.ambient) :=
    continuous_fst.continuousAt.preimage_mem_nhds hU₁
  have hs : (fun X : d.ambient => X.2) ⁻¹' U₂ ∈ 𝓝 (0 : d.ambient) :=
    continuous_snd.continuousAt.preimage_mem_nhds hU₂
  filter_upwards [hf, hs, eventually_expA_ambient d] with X hX1 hX2 hX hXl
  obtain ⟨g₁, hg₁⟩ := h₁ X.1 hX1 hXl.1
  obtain ⟨g₂, hg₂⟩ := h₂ X.2 hX2 hXl.2
  refine ⟨d.pair (g₁, g₂), Prod.ext ?_ ?_⟩
  · rw [hX.1]; exact hg₁
  · rw [hX.2]; exact hg₂

/-- **The logarithm of `G(F)` near `1` lies in `𝔤`**: for `Y` near `0`, `e^Y ∈ G(F)` implies
`Y ∈ 𝔤 = gspin(W) × gspin(V)` (componentwise `eventually_mem_gspin_of_expA_mem`). -/
theorem eventually_mem_lie_of_expA_mem :
    ∀ᶠ Y in 𝓝 (0 : d.ambient), ∀ g : ↥d.G, ((g : d.ambientˣ) : d.ambient) = expA F Y →
      Y ∈ d.lie := by
  have h₁ := (continuous_fst.tendsto (0 : d.ambient)).eventually
    (eventually_mem_gspin_of_expA_mem (F := F) d.QW)
  have h₂ := (continuous_snd.tendsto (0 : d.ambient)).eventually
    (eventually_mem_gspin_of_expA_mem (F := F) d.QV)
  filter_upwards [h₁, h₂, eventually_expA_ambient d] with Y hY1 hY2 hY g hg
  refine ⟨hY1 (d.fst g) ?_, hY2 (d.snd g) ?_⟩
  · rw [← hY.1, ← hg]; rfl
  · rw [← hY.2, ← hg]; rfl
end GGP

end GSpinGGP
