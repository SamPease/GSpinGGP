/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.ExpLocal

/-!
# Orbit charts and uniqueness of orbit measures

For a nilpotent `X ∈ 𝔤` and a complement `C` of `𝔤_X = ker(ad X)`, the chart
`Y ↦ e^Y X e^{-Y}` (`orbitMap`) on `C` near `0` is what the definition `IsOrbitMeasure` uses to
prescribe the orbit measure. This file shows that the prescription determines the measure.

* `exists_nhds_continuousOn_orbitMap`: the chart is continuous on a neighbourhood of `0`;
* `IsOrbitMeasure.eq_of_eventually_conj_eq_orbitMap`: if, near `1 ∈ G(F)`, conjugates `k X k⁻¹`
  lie in chart images of arbitrarily small parts of `C`, then two measures satisfying
  `IsOrbitMeasure` are equal. (The orbit is covered by the `G(F)`-translates, by a countable dense
  set of `G(F)`, of one compact chart image, on which the measure is prescribed.)
* `eventually_eq_expA_mul_expA`: **local factorization** (inverse function theorem): if `H ⊆ Aˣ`
  and `𝔥 ⊆ A` correspond under `exp` near `0`, and `𝔥 = C ⊕ K`, then every `k ∈ H` near `1` is
  `e^Y e^W` with `Y ∈ C`, `W ∈ K` small;
* `eventually_conj_eq_orbitMap`: hence, for `K = 𝔥_X`, `k X k⁻¹ = e^Y X e^{-Y}` with `Y ∈ C` small;
* `eventually_expA_mem_grpCentralizer`, `eventually_mem_lieCentralizer_of_expA_mem`: the
  correspondence between `H` and `𝔥` near `0` passes to centralizers `G_x`, `𝔤_x`.
-/

noncomputable section

open MeasureTheory Topology Filter
open scoped Classical

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
  {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A]
  [IsModuleTopology F A]

variable (F) in
/-- The chart `Y ↦ e^Y X e^{-Y}` is continuous on a neighbourhood of `0`. -/
lemma exists_nhds_continuousOn_orbitMap (X : A) :
    ∃ U ∈ 𝓝 (0 : A), ContinuousOn (orbitMap F X) U := by
  letI := isTopologicalRing_of_moduleTopology F A
  obtain ⟨U, hU, -, hc⟩ := exists_nhds_continuousOn_expA F (A := A)
  have hneg : (fun Y : A => -Y) ⁻¹' U ∈ 𝓝 (0 : A) :=
    continuous_neg.continuousAt.preimage_mem_nhds (by rwa [neg_zero])
  refine ⟨U ∩ (fun Y : A => -Y) ⁻¹' U, inter_mem hU hneg, ?_⟩
  have h1 : ContinuousOn (expA F : A → A) (U ∩ (fun Y : A => -Y) ⁻¹' U) :=
    hc.mono Set.inter_subset_left
  have h2 : ContinuousOn (fun Y : A => expA F (-Y)) (U ∩ (fun Y : A => -Y) ⁻¹' U) :=
    hc.comp continuous_neg.continuousOn fun Y hY => hY.2
  exact (h1.mul continuousOn_const).mul h2

/-- **Uniqueness of the orbit measure, given local surjectivity of the charts.** Let `G ⊆ Aˣ`
normalize `𝔤`, and suppose that for every `X` in the nilpotent orbit `O`, every complement `C` of
`𝔤_X` and every neighbourhood `U` of `0`, the conjugates `k X k⁻¹` for `k ∈ G` near `1` are of the
form `e^Y X e^{-Y}` with `Y ∈ C ∩ U`. Then at most one measure satisfies `IsOrbitMeasure`.

Proof: fix `X₀ ∈ O`, a complement `C`, and a compact neighbourhood `K` of `0` on which both
measures are prescribed in the chart. Both measures agree on measurable subsets of the compact
chart image `V = e^{C ∩ K} X₀ e^{-(C ∩ K)}`, hence (invariance) on measurable subsets of each
`g⁻¹ V g`. By the hypothesis and density of a countable `D ⊆ G` (`G` is second countable), the
`g⁻¹ V g`, `g ∈ D`, cover `O`; and both measures vanish off `O`. -/
theorem IsOrbitMeasure.eq_of_eventually_conj_eq_orbitMap {G : Subgroup Aˣ}
    {𝔤 : LieSubalgebra F A} (hG : ∀ g ∈ G, ∀ Y ∈ 𝔤, (g : A) * Y * (↑g⁻¹ : A) ∈ 𝔤)
    {b : LinearMap.BilinForm F A} {ψ : NontrivialAddChar F} {O : NilOrbit G 𝔤}
    (hsurj : ∀ X ∈ nilOrbitSet O, ∀ C : Submodule F ↥𝔤,
      IsCompl C (LinearMap.ker (LieAlgebra.ad F ↥𝔤 X)) → ∀ U ∈ 𝓝 (0 : A),
      ∀ᶠ k : ↥G in 𝓝 1, ∃ Y : ↥C, ((Y : ↥𝔤) : A) ∈ U ∧
        ((k : Aˣ) : A) * (X : A) * (((k : Aˣ)⁻¹ : Aˣ) : A) = orbitMap F (X : A) ((Y : ↥𝔤) : A))
    {μ ν : Measure ↥𝔤} (hμ : IsOrbitMeasure G 𝔤 b ψ O μ) (hν : IsOrbitMeasure G 𝔤 b ψ O ν) :
    μ = ν := by
  letI := isTopologicalRing_of_moduleTopology F A
  haveI := t2Space_of_moduleTopology F A
  haveI := locallyCompactSpace_of_moduleTopology F A
  haveI := subgroup_secondCountableTopology F A G
  haveI := subgroup_isTopologicalGroup F A G
  haveI : ContinuousSMul F A := IsModuleTopology.toContinuousSMul F A
  -- base point, complement, neighbourhoods
  set X₀ : ↥𝔤 := ⟨(Quotient.out O).1, (Quotient.out O).2.1⟩ with hX₀
  have hX₀O : X₀ ∈ nilOrbitSet O := ⟨(Quotient.out O).2.2, Quotient.out_eq O⟩
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker (LieAlgebra.ad F ↥𝔤 X₀))
  obtain ⟨Uμ, hUμ, hμC⟩ := hμ.2.2 X₀ hX₀O C hC.symm
  obtain ⟨Uν, hUν, hνC⟩ := hν.2.2 X₀ hX₀O C hC.symm
  obtain ⟨Uc, hUc, hcont⟩ := exists_nhds_continuousOn_orbitMap F (X₀ : A)
  obtain ⟨Um, hUm, hmem⟩ := exists_nhds_expA_conj_mem (F := F) (A := A)
  obtain ⟨K, hK, hKW, hKc⟩ := local_compact_nhds
    (inter_mem (inter_mem (inter_mem hUμ hUν) hUc) hUm)
  -- the chart is `𝔤`-valued on `𝔤 ∩ K`
  have hmemK : ∀ Y ∈ 𝔤, Y ∈ K → orbitMap F (X₀ : A) Y ∈ 𝔤 := by
    intro Y hY hYK
    refine hmem Y (hKW hYK).2 𝔤.toSubmodule (fun r hr => ?_) _ X₀.2
    have := 𝔤.lie_mem hY hr
    rwa [Ring.lie_def] at this
  -- the compact chart image `VA`
  set CA : Submodule F A := C.map 𝔤.incl.toLinearMap with hCA
  have hCAc : IsClosed (CA : Set A) := CA.closed_of_finiteDimensional
  set VA : Set A := orbitMap F (X₀ : A) '' ((CA : Set A) ∩ K) with hVA
  have hVAc : IsCompact VA :=
    (hKc.inter_left hCAc).image_of_continuousOn
      (hcont.mono fun Y hY => (hKW hY.2).1.2)
  set V : Set ↥𝔤 := Subtype.val ⁻¹' VA with hV
  have hVm : MeasurableSet V := (hVAc.isClosed.preimage continuous_subtype_val).measurableSet
  -- the chart with values in `𝔤`
  set φ : ↥C → ↥𝔤 := fun Y =>
    if h : orbitMap F (X₀ : A) ((Y : ↥𝔤) : A) ∈ 𝔤 then ⟨_, h⟩ else 0 with hφ
  set CK : Set ↥C := {Y | ((Y : ↥𝔤) : A) ∈ K} with hCK
  have hι : Continuous fun Y : ↥C => ((Y : ↥𝔤) : A) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hCKm : MeasurableSet CK := (hKc.isClosed.preimage hι).measurableSet
  have hφK : ∀ Y ∈ CK, ((φ Y : ↥𝔤) : A) = orbitMap F (X₀ : A) ((Y : ↥𝔤) : A) := by
    intro Y hY
    simp [hφ, hmemK _ (Y : ↥𝔤).2 hY]
  have hφc : ContinuousOn φ CK := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr ?_ fun Y hY => hφK Y hY
    exact (hcont.mono fun Y hY => (hKW hY).1.2).comp hι.continuousOn fun Y hY => hY
  -- both measures agree on measurable subsets of `V`
  have hkey : ∀ T : Set ↥𝔤, MeasurableSet T → T ⊆ V → μ T = ν T := by
    intro T hT hTV
    set S : Set ↥C := CK ∩ (CK.piecewise φ fun _ => 0) ⁻¹' T with hS
    have hSm : MeasurableSet S :=
      hCKm.inter ((hφc.measurable_piecewise continuousOn_const hCKm) hT)
    have hSU : ∀ Y ∈ S, ((Y : ↥𝔤) : A) ∈ K := fun Y hY => hY.1
    have himg : Subtype.val ⁻¹'
        ((fun Y : ↥C ↦ orbitMap F (X₀ : A) ((Y : ↥𝔤) : A)) '' S) = T := by
      ext Z
      constructor
      · rintro ⟨Y, ⟨hYK, hYT⟩, hYZ⟩
        have hpw : (CK.piecewise φ fun _ => 0) Y = φ Y := Set.piecewise_eq_of_mem _ _ _ hYK
        have : φ Y = Z := Subtype.ext ((hφK Y hYK).trans hYZ)
        rw [Set.mem_preimage, hpw, this] at hYT
        exact hYT
      · intro hZ
        obtain ⟨y, ⟨hyC, hyK⟩, hyZ⟩ := hTV hZ
        obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hyC
        refine ⟨⟨c, hc⟩, ⟨hyK, ?_⟩, hyZ⟩
        have hpw : (CK.piecewise φ fun _ => 0) ⟨c, hc⟩ = φ ⟨c, hc⟩ :=
          Set.piecewise_eq_of_mem _ _ _ hyK
        have : φ ⟨c, hc⟩ = Z := Subtype.ext ((hφK _ hyK).trans hyZ)
        rw [Set.mem_preimage, hpw, this]
        exact hZ
    rw [← himg, hμC S hSm fun Y hY => (hKW (hSU Y hY)).1.1.1,
      hνC S hSm fun Y hY => (hKW (hSU Y hY)).1.1.2]
  -- translates of `V`
  set P : ↥G → Set ↥𝔤 := fun g =>
    {Z | ((g : Aˣ) : A) * (Z : A) * (((g : Aˣ)⁻¹ : Aˣ) : A) ∈ VA} with hP
  have hPeq : ∀ g : ↥G, μ.restrict (P g) = ν.restrict (P g) := by
    intro g
    ext T hT
    rw [Measure.restrict_apply hT, Measure.restrict_apply hT]
    set ρ : ↥𝔤 → ↥𝔤 := fun W =>
      ⟨((((g : Aˣ)⁻¹ : Aˣ)) : A) * (W : A) * ((((g : Aˣ)⁻¹)⁻¹ : Aˣ) : A),
        hG _ (G.inv_mem g.2) _ W.2⟩ with hρ
    have hρc : Continuous ρ :=
      Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
    set S' : Set ↥𝔤 := V ∩ ρ ⁻¹' T with hS'
    have hS'm : MeasurableSet S' := hVm.inter (hρc.measurable hT)
    have hset : Subtype.val ⁻¹' (conjAd F (g : Aˣ) ⁻¹' (Subtype.val '' S')) = T ∩ P g := by
      ext Z
      simp only [Set.mem_preimage, conjAd_apply, Set.mem_image, Set.mem_inter_iff, hS', hV, hP,
        Set.mem_ofPred_eq]
      constructor
      · rintro ⟨W, ⟨hWV, hWT⟩, hWZ⟩
        have hρW : ρ W = Z := by
          apply Subtype.ext
          simp only [hρ, hWZ, inv_inv]
          simp [mul_assoc]
        rw [hρW] at hWT
        exact ⟨hWT, hWZ ▸ hWV⟩
      · rintro ⟨hZT, hZV⟩
        refine ⟨⟨_, hG _ g.2 _ Z.2⟩, ⟨hZV, ?_⟩, rfl⟩
        have hρW : ρ ⟨_, hG _ g.2 _ Z.2⟩ = Z := by
          apply Subtype.ext
          simp [hρ, mul_assoc]
        rw [hρW]
        exact hZT
    rw [← hset, hμ.2.1 _ g.2 S' hS'm, hν.2.1 _ g.2 S' hS'm]
    exact hkey S' hS'm Set.inter_subset_left
  -- a countable dense subset of `G`, and the covering
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense ↥G
  haveI : Countable ↥D := hDc.to_subtype
  have hN := hsurj X₀ hX₀O C hC.symm K hK
  have hcover : ∀ Z ∈ nilOrbitSet O, ∃ g ∈ D, Z ∈ P g := by
    rintro Z ⟨hn, hZ⟩
    obtain ⟨h, hh, hhZ⟩ := Quotient.exact (hZ.trans (Quotient.out_eq O).symm)
    set h' : ↥G := ⟨h, hh⟩
    have hnb : {g : ↥G | g * h'⁻¹ ∈ {k : ↥G | ∃ Y : ↥C, ((Y : ↥𝔤) : A) ∈ K ∧
        ((k : Aˣ) : A) * (X₀ : A) * (((k : Aˣ)⁻¹ : Aˣ) : A) =
          orbitMap F (X₀ : A) ((Y : ↥𝔤) : A)}} ∈ 𝓝 h' :=
      (continuous_mul_const h'⁻¹).continuousAt.preimage_mem_nhds (by rwa [mul_inv_cancel])
    obtain ⟨g, hgN, hgD⟩ := mem_closure_iff_nhds.mp (hD h') _ hnb
    obtain ⟨Y, hYK, hYeq⟩ := hgN
    refine ⟨g, hgD, ?_⟩
    show ((g : Aˣ) : A) * (Z : A) * (((g : Aˣ)⁻¹ : Aˣ) : A) ∈ VA
    have hZ' : (Z : A) = (((h : Aˣ)⁻¹ : Aˣ) : A) * (X₀ : A) * (h : A) := by
      rw [← show (h : A) * (Z : A) * (↑h⁻¹ : A) = (X₀ : A) from hhZ]
      simp [mul_assoc]
    refine ⟨((Y : ↥𝔤) : A), ⟨Submodule.mem_map.mpr ⟨Y, Y.2, rfl⟩, hYK⟩, ?_⟩
    rw [← hYeq, hZ']
    simp [h', mul_assoc]
  -- conclusion
  set s : Option ↥D → Set ↥𝔤 := fun i => i.elim (nilOrbitSet O)ᶜ fun g => P g with hs
  have hU : ⋃ i, s i = Set.univ := by
    refine Set.eq_univ_of_forall fun Z => ?_
    by_cases hZ : Z ∈ nilOrbitSet O
    · obtain ⟨g, hgD, hgZ⟩ := hcover Z hZ
      exact Set.mem_iUnion.mpr ⟨some ⟨g, hgD⟩, hgZ⟩
    · exact Set.mem_iUnion.mpr ⟨none, hZ⟩
  refine (Measure.ext_iff_of_iUnion_eq_univ hU).mpr fun i => ?_
  cases i with
  | none =>
    show μ.restrict (nilOrbitSet O)ᶜ = ν.restrict (nilOrbitSet O)ᶜ
    rw [Measure.restrict_eq_zero.mpr hμ.1, Measure.restrict_eq_zero.mpr hν.1]
  | some g => exact hPeq g

section Factorization

open NormedSpace

local notation "VA" => (Fin (Module.finrank F A) → F)

variable (F) in
/-- **Local factorization `H = e^C e^K` near `1`** (inverse function theorem). Let `H ⊆ Aˣ` and
`𝔥 ⊆ A` correspond under the exponential near `0` (`e^Y ∈ H` for small `Y ∈ 𝔥`, and conversely
`e^Y ∈ H` with `Y` small forces `Y ∈ 𝔥`), and let `𝔥 = C ⊕ K`. Then for every neighbourhood `U` of
`0`, every `k ∈ H` near `1` is `e^Y e^W` with `Y ∈ C ∩ U`, `W ∈ K`.

Proof: choose a complement `M` of `𝔥` in `A`, and work in the Banach algebra `End(F^d)` through
`lmulPi`. The map `z ↦ e^{a z} e^{b z} e^{c z} - 1 + d z`, with `a, b, c` the projections onto
`C, K, M` (transported) and `d = 1 - ℓ ℓ⁻¹`, has derivative `1` at `0`, so it maps neighbourhoods
of `0` onto neighbourhoods of `0` (Mathlib `HasStrictFDerivAt.map_nhds_eq_of_surj`). This writes
`k = e^Y e^W e^m` with `m ∈ M` small; then `e^m ∈ H`, so `m ∈ 𝔥 ∩ M = 0`. -/
theorem eventually_eq_expA_mul_expA {H : Subgroup Aˣ} {𝔥 : LieSubalgebra F A}
    (hexp : ∀ᶠ Y in 𝓝 (0 : A), Y ∈ 𝔥 → ∃ g ∈ H, (g : A) = expA F Y)
    (hlog : ∀ᶠ Y in 𝓝 (0 : A), ∀ g ∈ H, (g : A) = expA F Y → Y ∈ 𝔥)
    {C K : Submodule F ↥𝔥} (hCK : IsCompl C K) {U : Set A} (hU : U ∈ 𝓝 (0 : A)) :
    ∀ᶠ k in 𝓝 (1 : A), ∀ g ∈ H, (g : A) = k →
      ∃ Y ∈ C, ((Y : ↥𝔥) : A) ∈ U ∧ ∃ W ∈ K, k = expA F (Y : A) * expA F (W : A) := by
  letI := isTopologicalRing_of_moduleTopology F A
  haveI := t2Space_of_moduleTopology F A
  -- linear algebra: `A = C ⊕ K ⊕ M`
  obtain ⟨M, hM⟩ := Submodule.exists_isCompl 𝔥.toSubmodule
  let e : A →ₗ[F] ↥𝔥 := 𝔥.toSubmodule.projectionOnto M hM
  let πC : A →ₗ[F] A := 𝔥.incl.toLinearMap ∘ₗ C.projection K hCK ∘ₗ e
  let πK : A →ₗ[F] A := 𝔥.incl.toLinearMap ∘ₗ K.projection C hCK.symm ∘ₗ e
  let πM : A →ₗ[F] A := M.projection 𝔥.toSubmodule hM.symm
  have hsum : ∀ w : A, πC w + πK w + πM w = w := by
    intro w
    have h1 := Submodule.projection_add_projection_eq_self hCK (e w)
    have h1' : πC w + πK w = ((e w : ↥𝔥) : A) := by
      show ((C.projection K hCK (e w) : ↥𝔥) : A) +
        ((K.projection C hCK.symm (e w) : ↥𝔥) : A) = ((e w : ↥𝔥) : A)
      exact congrArg Subtype.val h1
    rw [h1']
    exact Submodule.projection_add_projection_eq_self hM w
  -- the map in `End(F^d)`
  let ℓL : A →L[F] (VA →L[F] VA) := ⟨lmulPiₗ F, continuous_lmulPi F⟩
  let cl : (A →ₗ[F] A) → (A →L[F] A) := fun f => ⟨f, IsModuleTopology.continuous_of_linearMap f⟩
  let a : (VA →L[F] VA) →L[F] (VA →L[F] VA) := ℓL ∘L cl πC ∘L lmulPiInv F
  let b : (VA →L[F] VA) →L[F] (VA →L[F] VA) := ℓL ∘L cl πK ∘L lmulPiInv F
  let c : (VA →L[F] VA) →L[F] (VA →L[F] VA) := ℓL ∘L cl πM ∘L lmulPiInv F
  let d : (VA →L[F] VA) →L[F] (VA →L[F] VA) := 1 - ℓL ∘L lmulPiInv F
  have habc : ∀ z, a z + b z + c z = ℓL (lmulPiInv F z) := by
    intro z
    show ℓL (πC _) + ℓL (πK _) + ℓL (πM _) = _
    rw [← map_add, ← map_add, hsum]
    rfl
  let Θ : (VA →L[F] VA) → (VA →L[F] VA) := fun z => exp (a z) * exp (b z) * exp (c z) - 1 + d z
  have hE : HasStrictFDerivAt (exp : (VA →L[F] VA) → (VA →L[F] VA)) (1 : _ →L[F] _) 0 :=
    hasStrictFDerivAt_exp_zero_of_radius_pos (expSeries_radius_pos_of_pAdic F _)
  have hcomp : ∀ f : (VA →L[F] VA) →L[F] (VA →L[F] VA),
      HasStrictFDerivAt (fun z => exp (f z)) f 0 := by
    intro f
    have h0 : HasStrictFDerivAt (exp : (VA →L[F] VA) → (VA →L[F] VA)) (1 : _ →L[F] _) (f 0) := by
      rw [map_zero]; exact hE
    convert h0.comp (0 : VA →L[F] VA) f.hasStrictFDerivAt using 1
    ext x; rfl
  have hΘ : HasStrictFDerivAt Θ (1 : (VA →L[F] VA) →L[F] (VA →L[F] VA)) 0 := by
    have h := ((((hcomp a).mul' (hcomp b)).mul' (hcomp c)).sub_const 1).add d.hasStrictFDerivAt
    refine h.congr_fderiv ?_
    ext1 z
    have := habc z
    have ha0 : exp (a 0) = 1 := by rw [map_zero, exp_zero]
    have hb0 : exp (b 0) = 1 := by rw [map_zero, exp_zero]
    have hc0 : exp (c 0) = 1 := by rw [map_zero, exp_zero]
    have hab : ((fun z => exp (a z)) * fun z => exp (b z)) 0 = 1 := by
      show exp (a 0) * exp (b 0) = 1
      rw [ha0, hb0, one_mul]
    rw [hab, ha0, hb0, hc0]
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_one, one_mul,
      one_apply_eq_self]
    rw [show d z = z - ℓL (lmulPiInv F z) from rfl, ← this]
    abel
  have hmap := hΘ.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr fun y => ⟨y, rfl⟩)
  have hΘ0 : Θ 0 = 0 := by simp [Θ]
  -- neighbourhoods
  obtain ⟨Ua, hUa, -, haux⟩ := expA_aux F (A := A)
  obtain ⟨Ue, hUe, hexp'⟩ := hexp.exists_mem
  obtain ⟨Ul, hUl, hlog'⟩ := hlog.exists_mem
  have hπ : ∀ (f : A →ₗ[F] A) (S : Set A), S ∈ 𝓝 (0 : A) → f ⁻¹' S ∈ 𝓝 (0 : A) :=
    fun f S hS => (IsModuleTopology.continuous_of_linearMap f).continuousAt.preimage_mem_nhds
      (by rwa [map_zero])
  set WA : Set A := πC ⁻¹' (U ∩ Ua ∩ Ue) ∩ πK ⁻¹' (Ua ∩ Ue) ∩ πM ⁻¹' (Ua ∩ Ul) with hWA
  have hWAn : WA ∈ 𝓝 (0 : A) :=
    inter_mem (inter_mem (hπ _ _ (inter_mem (inter_mem hU hUa) hUe))
      (hπ _ _ (inter_mem hUa hUe))) (hπ _ _ (inter_mem hUa hUl))
  set N : Set (VA →L[F] VA) := lmulPiInv F ⁻¹' WA with hN
  have hNn : N ∈ 𝓝 (0 : VA →L[F] VA) :=
    (lmulPiInv F).continuous.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  have himg : Θ '' N ∈ 𝓝 (0 : VA →L[F] VA) := by
    have := image_mem_map (m := Θ) hNn
    rwa [hmap, hΘ0] at this
  have hk : ∀ᶠ k in 𝓝 (1 : A), ℓL k - 1 ∈ Θ '' N := by
    have hc : ContinuousAt (fun k : A => ℓL k - 1) 1 :=
      (ℓL.continuous.sub continuous_const).continuousAt
    refine hc.preimage_mem_nhds ?_
    show Θ '' N ∈ 𝓝 (ℓL 1 - 1)
    rw [show ℓL 1 = 1 from lmulPi_one F, sub_self]
    exact himg
  filter_upwards [hk] with k hk g hg hgk
  obtain ⟨z, hzN, hz⟩ := hk
  obtain ⟨⟨⟨⟨hYU, hYa⟩, hYe⟩, ⟨hWa, hWe⟩⟩, ⟨hma, hml⟩⟩ := hzN
  set w := lmulPiInv F z with hw
  set Y : ↥𝔥 := C.projection K hCK (e w) with hY
  set W : ↥𝔥 := K.projection C hCK.symm (e w) with hW
  set m := πM w with hm
  have hYw : (Y : A) = πC w := rfl
  have hWw : (W : A) = πK w := rfl
  have heq : expA F (Y : A) * expA F (W : A) * expA F m = k := by
    have hd0 : lmulPiInv F (d z) = 0 := by
      simp [d, lmulPiInv_lmulPi, ℓL, lmulPiₗ]
    have h1 : lmulPi F (expA F (Y : A) * expA F (W : A) * expA F m) + d z = lmulPi F k := by
      rw [hYw, hWw, lmulPi_mul, lmulPi_mul, (haux _ hYa).2.2, (haux _ hWa).2.2, (haux _ hma).2.2]
      have h2 : Θ z = ℓL k - 1 := hz
      have h3 : exp (a z) * exp (b z) * exp (c z) + d z = ℓL k := by
        have := congrArg (· + 1) h2
        simp only [Θ, sub_add_cancel] at this
        rw [← this]; abel
      exact h3
    have h2 := congrArg (lmulPiInv F) h1
    rwa [map_add, lmulPiInv_lmulPi, lmulPiInv_lmulPi, hd0, add_zero] at h2
  obtain ⟨gY, hgY, hgYe⟩ := hexp' _ hYe Y.2
  obtain ⟨gW, hgW, hgWe⟩ := hexp' _ hWe W.2
  have hm𝔥 : m ∈ 𝔥 := by
    refine hlog' _ hml ((gY * gW)⁻¹ * g) (H.mul_mem (H.inv_mem (H.mul_mem hgY hgW)) hg) ?_
    have : ((gY * gW : Aˣ) : A) * expA F m = (g : A) := by
      rw [Units.val_mul, hgYe, hgWe, hgk, ← heq]
      rfl
    rw [Units.val_mul, Units.inv_mul_eq_iff_eq_mul]
    exact this.symm
  have hmM : m ∈ M := Submodule.projection_apply_mem _ _
  have hm0 : m = 0 := (Submodule.disjoint_def.mp hM.disjoint) m hm𝔥 hmM
  refine ⟨Y, Submodule.projection_apply_mem _ _, hYU, W, Submodule.projection_apply_mem _ _, ?_⟩
  rw [← heq, hm0, expA_zero_eq_one, mul_one]

variable (F) in
/-- **Conjugates near `1` are chart points**: under the hypotheses of `eventually_eq_expA_mul_expA`,
for `X ∈ 𝔥`, a complement `C` of `𝔥_X = ker(ad X)` and a neighbourhood `U` of `0`, every
`k ∈ H` near `1` satisfies `k X k⁻¹ = e^Y X e^{-Y}` for some `Y ∈ C ∩ U`: write `k = e^Y e^W` with
`W ∈ 𝔥_X`, and `e^W` commutes with `X`. -/
theorem eventually_conj_eq_orbitMap {H : Subgroup Aˣ} {𝔥 : LieSubalgebra F A}
    (hexp : ∀ᶠ Y in 𝓝 (0 : A), Y ∈ 𝔥 → ∃ g ∈ H, (g : A) = expA F Y)
    (hlog : ∀ᶠ Y in 𝓝 (0 : A), ∀ g ∈ H, (g : A) = expA F Y → Y ∈ 𝔥)
    (X : ↥𝔥) (C : Submodule F ↥𝔥) (hC : IsCompl C (LinearMap.ker (LieAlgebra.ad F ↥𝔥 X)))
    {U : Set A} (hU : U ∈ 𝓝 (0 : A)) :
    ∀ᶠ k : ↥H in 𝓝 1, ∃ Y : ↥C, ((Y : ↥𝔥) : A) ∈ U ∧
      ((k : Aˣ) : A) * (X : A) * (((k : Aˣ)⁻¹ : Aˣ) : A) = orbitMap F (X : A) ((Y : ↥𝔥) : A) := by
  letI := isTopologicalRing_of_moduleTopology F A
  obtain ⟨Ui, hUi, hinv⟩ := expA_mul_expA_neg F (A := A)
  have hneg : (fun Y : A => -Y) ⁻¹' Ui ∈ 𝓝 (0 : A) :=
    continuous_neg.continuousAt.preimage_mem_nhds (by rwa [neg_zero])
  have hfac := eventually_eq_expA_mul_expA F hexp hlog hC (inter_mem (inter_mem hU hUi) hneg)
  have hval : Tendsto (fun k : ↥H => ((k : Aˣ) : A)) (𝓝 1) (𝓝 1) :=
    (Units.continuous_val.comp continuous_subtype_val).tendsto' 1 1 rfl
  filter_upwards [hval.eventually hfac] with k hk
  obtain ⟨Y, hYC, ⟨⟨hYU, -⟩, hYn⟩, W, hWK, hkYW⟩ := hk (k : Aˣ) k.2 rfl
  refine ⟨⟨Y, hYC⟩, hYU, ?_⟩
  have hWX : Commute (X : A) (W : A) := by
    have h := congrArg Subtype.val (LinearMap.mem_ker.mp hWK)
    rw [LieAlgebra.ad_apply, LieSubalgebra.coe_bracket, Ring.lie_def, ZeroMemClass.coe_zero,
      sub_eq_zero] at h
    exact h
  have hcW : Commute (X : A) (expA F (W : A)) := commute_expA_of_commute hWX
  have hY1 : expA F (-(Y : A)) * expA F (Y : A) = 1 := by
    simpa using hinv _ hYn
  have h1 : expA F (-(Y : A)) * ((k : Aˣ) : A) = expA F (W : A) := by
    rw [hkYW, ← mul_assoc, hY1, one_mul]
  have hW' : expA F (W : A) * (((k : Aˣ)⁻¹ : Aˣ) : A) = expA F (-(Y : A)) := by
    rw [← h1, mul_assoc, Units.mul_inv, mul_one]
  calc ((k : Aˣ) : A) * (X : A) * (((k : Aˣ)⁻¹ : Aˣ) : A)
      = expA F (Y : A) * (expA F (W : A) * (X : A)) * (((k : Aˣ)⁻¹ : Aˣ) : A) := by
        rw [hkYW, mul_assoc (expA F _)]
    _ = expA F (Y : A) * (X : A) * (expA F (W : A) * (((k : Aˣ)⁻¹ : Aˣ) : A)) := by
        rw [← hcW.eq]; simp only [mul_assoc]
    _ = orbitMap F (X : A) ((Y : ↥𝔥) : A) := by rw [hW']; rfl

end Factorization

section Centralizer

/-- If `e^Y ∈ G` for small `Y ∈ 𝔤`, then `e^Y ∈ G_x` for small `Y ∈ 𝔤_x` (`e^Y` commutes with
what `Y` commutes with). -/
theorem eventually_expA_mem_grpCentralizer {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A}
    (hexp : ∀ᶠ Y in 𝓝 (0 : A), Y ∈ 𝔤 → ∃ g ∈ G, (g : A) = expA F Y) (x : Aˣ) :
    ∀ᶠ Y in 𝓝 (0 : A), Y ∈ lieCentralizer 𝔤 (x : A) →
      ∃ g ∈ grpCentralizer G x, (g : A) = expA F Y := by
  filter_upwards [hexp] with Y hY hYx
  obtain ⟨hY𝔤, hYc⟩ := mem_lieCentralizer.mp hYx
  obtain ⟨g, hg, hgY⟩ := hY hY𝔤
  refine ⟨g, ⟨hg, Subgroup.mem_centralizer_singleton_iff.mpr (Units.ext ?_)⟩, hgY⟩
  rw [Units.val_mul, Units.val_mul, hgY]
  exact (commute_expA_of_commute hYc).eq.symm

/-- If `e^Y ∈ G` with `Y` small forces `Y ∈ 𝔤`, then `e^Y ∈ G_x` with `Y` small forces
`Y ∈ 𝔤_x` (near `0`, `Y` commutes with what `e^Y` commutes with,
`exists_nhds_commute_of_commute_expA`). -/
theorem eventually_mem_lieCentralizer_of_expA_mem {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A}
    (hlog : ∀ᶠ Y in 𝓝 (0 : A), ∀ g ∈ G, (g : A) = expA F Y → Y ∈ 𝔤) (x : Aˣ) :
    ∀ᶠ Y in 𝓝 (0 : A), ∀ g ∈ grpCentralizer G x, (g : A) = expA F Y →
      Y ∈ lieCentralizer 𝔤 (x : A) := by
  obtain ⟨U, hU, hc⟩ := exists_nhds_commute_of_commute_expA F (A := A)
  filter_upwards [hlog, hU] with Y hY hYU g hgx hgY
  refine mem_lieCentralizer.mpr ⟨hY g hgx.1 hgY, hc Y hYU _ ?_⟩
  have h := congrArg Units.val (Subgroup.mem_centralizer_singleton_iff.mp hgx.2)
  rw [Units.val_mul, Units.val_mul, hgY] at h
  exact h.symm

end Centralizer

end GSpinGGP
