/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Interface
import GSpinGGP.Literature.Waldspurger
import GSpinGGP.Literature.KottwitzClay
import GSpinGGP.TraceFormula.TorusDescent

/-!
# Invariant open and closed subsets of `G(F)` (`p`-adic)

Two facts about conjugation-invariant subsets of `G(F)`, `G = GSpin(W) × GSpin(V)`, used by the
localization arguments of Thesis Ch. 12 (`TraceFormula/Scusp.lean`, `TraceFormula/Geometric.lean`).
Both concern `IsInvariantClopen` sets: open, closed, invariant and `A_G(F)`-stable.

* `hc_exists_invariantClopen_nearCentral` (**proved**): the near-central elements have arbitrarily small
  invariant clopen `A_G(F)`-stable neighbourhoods. From Waldspurger 2010 §3.1 at `x = 1`
  (`waldspurger_goodNbhd_one`, `Literature/Waldspurger.lean`): a good neighbourhood `ω` of `0` inside
  `ω₀^{G(F)}` gives the `G`-domain `Ω₀ = exp(ω)`, compact modulo conjugation
  (`exists_compact_conj_of_expHomeo`), and `Ω = A_G(F)·Ω₀` is closed because `H_G` confines the
  `A_G(F)`-factor near every point (`isClosed_AG_mul_of_subset_conj`, `isInvariantClopen_AG_mul`).
  This replaces the passage to `Ḡ = G/A_G`.
* `hc_exists_invariantClopen_superset` (**proved**, adapted): every compact subset lies in such a set
  that is compact modulo conjugation and `A_G(F)`. Each `c = s e^N` (Jordan decomposition, `N = log u`
  nilpotent in `𝔤_s`, `exists_eq_mul_expA_nilpotent`) lies in the `G`-domain `(s exp ω_s)^{G(F)}` of
  Waldspurger 2010 §3.1 at `s` (`waldspurger_goodNbhd`): `α²N ∈ ω_s` for small `α`, and `α²N` is
  conjugate to `N` under the centralizer of `s` (Kottwitz, Clay Proc. 4, §17.5, p. 461, applied to
  `Z_G(s)⁰`; `kottwitz_nilpotent_sq_smul`). Finitely many such domains cover the compact set, and the
  union is saturated by `A_G(F)`. (Beuzart-Plessis's characterization of compactness modulo
  conjugation, Astérisque 418 §1.7, is stated without proof for general connected groups and is not
  used.)

**Degenerate checks** (`Sanity/InvariantSetsAudit.lean`): at `toyD` (`A_G = G`) both conclusions hold
with `Ω = G(F)`.
-/

open Topology Filter
open scoped Pointwise

noncomputable section

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-! ## `A_G(F)`-saturation of `G`-domains -/

namespace GGPData

variable (d : GGPData F)

/-- The elements of `A_G(F)` with `H_G` in a finite set form a compact set (finitely many cosets of
the compact `A_G(F) ∩ ker H_G`; `isCompact_preimage_hcA`). -/
theorem isCompact_AG_inter_hcG_mem {R : Set HCVal} (hR : R.Finite) :
    IsCompact ((d.AG : Set ↥d.G) ∩ {g | d.hcG g ∈ R}) := by
  have e : (d.AG : Set ↥d.G) ∩ {g | d.hcG g ∈ R} = Subtype.val '' (d.hcA ⁻¹' R) := by
    ext g
    constructor
    · rintro ⟨hg, hgR⟩; exact ⟨⟨g, hg⟩, hgR, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨a.2, ha⟩
  rw [e]
  exact (d.isCompact_preimage_hcA hR).image continuous_subtype_val

/-- **`A_G(F)`-saturation preserves closedness** for a closed set `Ω₀` contained in the conjugates of
a compact `K`: near any point, `H_G` (locally constant, conjugation invariant) confines the
`A_G(F)`-factor to a compact set. -/
theorem isClosed_AG_mul_of_subset_conj {Ω₀ : Set ↥d.G} (hΩ : IsClosed Ω₀) {K : Set ↥d.G}
    (hK : IsCompact K) (hsub : ∀ g ∈ Ω₀, ∃ (x k : ↥d.G), k ∈ K ∧ g = x * k * x⁻¹) :
    IsClosed ((d.AG : Set ↥d.G) * Ω₀) := by
  classical
  rw [← closure_subset_iff_isClosed]
  intro g hg
  set U : Set ↥d.G := {g' | d.hcG g' = d.hcG g}
  have hU : IsOpen U := (d.isLocallyConstant_hcG.isClopen_fiber (d.hcG g)).isOpen
  set R : Set HCVal := (fun s => d.hcG g * s⁻¹) '' (d.hcG '' K)
  have hAR := d.isCompact_AG_inter_hcG_mem ((d.finite_image_hcG hK).image _ : R.Finite)
  have hsubR : U ∩ ((d.AG : Set ↥d.G) * Ω₀) ⊆ ((d.AG : Set ↥d.G) ∩ {a | d.hcG a ∈ R}) * Ω₀ := by
    rintro g' ⟨hg'U, a, ha, w, hw, rfl⟩
    obtain ⟨x, k, hk, rfl⟩ := hsub w hw
    refine ⟨a, ⟨ha, d.hcG k, ⟨k, hk, rfl⟩, ?_⟩, _, hw, rfl⟩
    have h1 : d.hcG (a * (x * k * x⁻¹)) = d.hcG g := hg'U
    rw [map_mul, d.hcG_conj] at h1
    rw [← h1]; group
  have hgc : g ∈ closure (U ∩ ((d.AG : Set ↥d.G) * Ω₀)) := by
    rw [mem_closure_iff_nhds] at hg ⊢
    intro t ht
    obtain ⟨z, ⟨hzt, hzU⟩, hz⟩ := hg (t ∩ U) (Filter.inter_mem ht (hU.mem_nhds rfl))
    exact ⟨z, hzt, hzU, hz⟩
  exact Set.mul_subset_mul_right Set.inter_subset_left
    (closure_minimal hsubR (hΩ.mul_left_of_isCompact hAR) hgc)

/-- **`A_G(F)`-saturation of a `G`-domain compact modulo conjugation** is open, closed, invariant and
`A_G(F)`-stable (`isClosed_AG_mul_of_subset_conj`; `A_G(F)` is central). -/
theorem isInvariantClopen_AG_mul {Ω₀ : Set ↥d.G} (hΩo : IsOpen Ω₀) (hΩc : IsClosed Ω₀)
    (hinv : ∀ x g : ↥d.G, g ∈ Ω₀ → x * g * x⁻¹ ∈ Ω₀) {K : Set ↥d.G} (hK : IsCompact K)
    (hsub : ∀ g ∈ Ω₀, ∃ (x k : ↥d.G), k ∈ K ∧ g = x * k * x⁻¹) :
    IsInvariantClopen d ((d.AG : Set ↥d.G) * Ω₀) := by
  refine ⟨hΩo.mul_left, d.isClosed_AG_mul_of_subset_conj hΩc hK hsub, ?_, ?_⟩
  · rintro x _ ⟨a, ha, w, hw, rfl⟩
    refine ⟨a, ha, x * w * x⁻¹, hinv x w hw, ?_⟩
    have hc := Subgroup.mem_center_iff.mp (d.AG_le_center ha) x
    calc a * (x * w * x⁻¹) = (a * x) * w * x⁻¹ := by group
      _ = (x * a) * w * x⁻¹ := by rw [hc]
      _ = x * (a * w) * x⁻¹ := by group
  · rintro a' _ ⟨a, ha, w, hw, rfl⟩
    exact ⟨a' * a, d.AG.mul_mem a'.2 ha, w, hw, by simp [mul_assoc]⟩

end GGPData

/-! ## Images of good neighbourhoods under `exp` -/

section ExpDomain

variable (d : GGPData F)

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra in
/-- A subset of `𝔤(F)` closed in `𝔤(F)` is closed in the ambient algebra (`𝔤(F)` is a
finite-dimensional, hence closed, subspace). -/
theorem isClosed_of_subset_lie {ω : Set d.ambient} (hωlie : ω ⊆ d.lie)
    (hωc : IsClosed (Subtype.val ⁻¹' ω : Set ↥d.lie)) : IsClosed ω := by
  haveI := t2Space_of_moduleTopology F d.ambient
  haveI := isTopologicalRing_of_moduleTopology F d.ambient
  haveI : ContinuousSMul F d.ambient := IsModuleTopology.toContinuousSMul F d.ambient
  have hlie : IsClosed (d.lie : Set d.ambient) :=
    Submodule.closed_of_finiteDimensional (LieSubalgebra.toSubmodule d.lie)
  have := hωc.trans hlie
  convert this using 1
  ext X
  constructor
  · intro hX; exact ⟨⟨X, hωlie hX⟩, hX, rfl⟩
  · rintro ⟨Y, hY, rfl⟩; exact hY

/-- `expA` intertwines conjugation by `G(F)`. -/
theorem expA_conj_G (h : ↥d.G) (X : d.ambient) :
    expA F (((h : d.ambientˣ) : d.ambient) * X * ((h⁻¹ : d.ambientˣ) : d.ambient)) =
      ((h : d.ambientˣ) : d.ambient) * expA F X * ((h⁻¹ : d.ambientˣ) : d.ambient) := by
  simpa using expA_units_conj F (h : d.ambientˣ) X

variable {d} {ω : Set d.ambient} {Ω : Set ↥d.G} (e : ↥ω ≃ₜ ↥Ω)
  (he : ∀ X : ↥ω, ((((e X : ↥Ω) : ↥d.G) : d.ambientˣ) : d.ambient) = expA F (X : d.ambient))
include he

/-- If `exp : ω ≃ Ω` and `ω ⊆ Γ^{G(F)}` with `Γ` compact (and `ω` closed and invariant), then
`Ω ⊆ K^{G(F)}` with `K = exp(Γ ∩ ω)` compact. -/
theorem exists_compact_conj_of_expHomeo (hωlie : ω ⊆ d.lie)
    (hωc : IsClosed (Subtype.val ⁻¹' ω : Set ↥d.lie))
    (hωinv : ∀ g : ↥d.G, ∀ X ∈ ω,
      ((g : d.ambientˣ) : d.ambient) * X * ((g⁻¹ : d.ambientˣ) : d.ambient) ∈ ω)
    {Γ : Set d.ambient} (hΓ : IsCompact Γ)
    (hωΓ : ∀ X ∈ ω, ∃ g : ↥d.G, ∃ Y ∈ Γ,
      X = ((g : d.ambientˣ) : d.ambient) * Y * ((g⁻¹ : d.ambientˣ) : d.ambient)) :
    ∃ K : Set ↥d.G, IsCompact K ∧ ∀ g ∈ Ω, ∃ (x k : ↥d.G), k ∈ K ∧ g = x * k * x⁻¹ := by
  have hωcl : IsClosed ω := isClosed_of_subset_lie d hωlie hωc
  refine ⟨Subtype.val '' (e '' {X : ↥ω | (X : d.ambient) ∈ Γ}),
    ((hωcl.isClosedEmbedding_subtypeVal.isCompact_preimage hΓ).image e.continuous).image
      continuous_subtype_val, fun g hg => ?_⟩
  set X := e.symm ⟨g, hg⟩
  obtain ⟨h, Y, hY, hXY⟩ := hωΓ X X.2
  have hYω : Y ∈ ω := by
    convert hωinv h⁻¹ X X.2 using 1
    rw [hXY]; simp [mul_assoc]
  refine ⟨h, e ⟨Y, hYω⟩, ⟨e ⟨Y, hYω⟩, ⟨⟨Y, hYω⟩, hY, rfl⟩, rfl⟩, ?_⟩
  apply Subtype.ext; apply Units.ext
  have h1 : (((g : ↥d.G) : d.ambientˣ) : d.ambient) = expA F (X : d.ambient) := by
    rw [← he X]; simp [X]
  rw [h1, hXY, expA_conj_G, ← he ⟨Y, hYω⟩]
  simp

/-- `exp(0) = 1` lies in `Ω`. -/
theorem one_mem_of_expHomeo (h0ω : (0 : d.ambient) ∈ ω) : (1 : ↥d.G) ∈ Ω := by
  have h := he ⟨0, h0ω⟩
  rw [show ((⟨0, h0ω⟩ : ↥ω) : d.ambient) = 0 from rfl, expA_zero_eq_one] at h
  have : ((e ⟨0, h0ω⟩ : ↥Ω) : ↥d.G) = 1 := Subtype.ext (Units.ext h)
  rw [← this]; exact (e ⟨0, h0ω⟩).2

/-- **Smallness**: if `ω ⊆ ω₀^{G(F)}`, every `w ∈ Ω` is conjugate to `exp(Y)` with `Y ∈ ω₀`. -/
theorem exists_conj_eq_expA_of_expHomeo {ω₀ : Set d.ambient}
    (hsmall : ∀ X ∈ ω, ∃ g : ↥d.G, ∃ Y ∈ ω₀,
      X = ((g : d.ambientˣ) : d.ambient) * Y * ((g⁻¹ : d.ambientˣ) : d.ambient))
    {w : ↥d.G} (hw : w ∈ Ω) :
    ∃ (h : ↥d.G), ∃ Y ∈ ω₀, (((h⁻¹ * w * h : ↥d.G) : d.ambientˣ) : d.ambient) = expA F Y := by
  set X := e.symm ⟨w, hw⟩
  obtain ⟨h, Y, hY, hXY⟩ := hsmall X X.2
  have hw' : (((w : ↥d.G) : d.ambientˣ) : d.ambient) = expA F (X : d.ambient) := by
    rw [← he X]; simp [X]
  refine ⟨h, Y, hY, ?_⟩
  have hYX : Y = (((h⁻¹ : ↥d.G) : d.ambientˣ) : d.ambient) * (X : d.ambient) *
      ((((h⁻¹ : ↥d.G) : d.ambientˣ))⁻¹ : d.ambientˣ) := by rw [hXY]; simp [mul_assoc]
  rw [hYX, expA_conj_G, ← hw']
  simp [mul_assoc]

end ExpDomain

/-- **Small invariant open-and-closed neighbourhoods of the near-central set** (Thesis §3.5.2;
BP Astérisque 418 §3.3 for the Lie-algebra analogue).
For every neighbourhood `U` of `1` in `G(F)` there is an open and closed, invariant,
`A_G(F)`-stable `Ω` that contains every near-central `c` (`1` lies in the closure of
`A_G(F) · c^{G(F)}`; Lean: `IsNearCentral`, `TraceFormula/Geometric.lean`, written out here), and
every element of which is conjugate into `U` modulo `A_G(F)`.

Proved from Waldspurger 2010 §3.1 at `x = 1` (`waldspurger_goodNbhd_one`) and `A_G(F)`-saturation
(`isInvariantClopen_AG_mul`): `Ω = A_G(F) · exp(ω)` for a good neighbourhood `ω ⊆ ω₀^{G(F)}`, with `ω₀`
so small that `exp(ω₀) ∩ G(F) ⊆ U` (`eventually_mem_of_eq_mul_expA`). -/
theorem hc_exists_invariantClopen_nearCentral (d : GGPData F) {U : Set ↥d.G}
    (hU : U ∈ 𝓝 (1 : ↥d.G)) :
    ∃ Ω : Set ↥d.G, IsInvariantClopen d Ω ∧
      (∀ c : ↥d.G, (∀ V ∈ 𝓝 (1 : ↥d.G), ∃ (a : ↥d.AG) (x : ↥d.G),
          ((a : ↥d.G))⁻¹ * (x * c * x⁻¹) ∈ V) → c ∈ Ω) ∧
      ∀ g ∈ Ω, ∃ (a : ↥d.AG) (x : ↥d.G), ((a : ↥d.G))⁻¹ * (x * g * x⁻¹) ∈ U := by
  obtain ⟨O, hOU, hOo, h1O⟩ := mem_nhds_iff.1 hU
  obtain ⟨ω, Ω, hωlie, h0ω, -, hωc, hωinv, ⟨Γ, -, hΓ, hωΓ⟩, hΩo, hΩc, hΩinv, ⟨e, he⟩, hsmall⟩ :=
    waldspurger_goodNbhd_one d (eventually_mem_of_eq_mul_expA d 1 hOo h1O)
  obtain ⟨K, hK, hsub⟩ := exists_compact_conj_of_expHomeo e he hωlie hωc hωinv hΓ hωΓ
  have hcl := d.isInvariantClopen_AG_mul hΩo hΩc hΩinv hK hsub
  refine ⟨(d.AG : Set ↥d.G) * Ω, hcl, fun c hc => ?_, ?_⟩
  · obtain ⟨a, x, hax⟩ := hc Ω (hΩo.mem_nhds (one_mem_of_expHomeo e he h0ω))
    have hxc : x * c * x⁻¹ ∈ (d.AG : Set ↥d.G) * Ω := ⟨a, a.2, _, hax, by group⟩
    have := hcl.2.2.1 x⁻¹ _ hxc
    rwa [show x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ = c by group] at this
  · rintro _ ⟨a, ha, w, hw, rfl⟩
    obtain ⟨h, Y, hY, hy⟩ := exists_conj_eq_expA_of_expHomeo e he hsmall hw
    have hyO := hY (h⁻¹ * w * h) (by rw [hy]; simp)
    have hc := Subgroup.mem_center_iff.mp (d.AG_le_center ha) h⁻¹
    have heq : (a : ↥d.G)⁻¹ * (h⁻¹ * (a * w) * h⁻¹⁻¹) = h⁻¹ * w * h := by
      calc (a : ↥d.G)⁻¹ * (h⁻¹ * (a * w) * h⁻¹⁻¹) = (a : ↥d.G)⁻¹ * ((h⁻¹ * a) * w * h) := by
            group
        _ = (a : ↥d.G)⁻¹ * ((a * h⁻¹) * w * h) := by rw [hc]
        _ = h⁻¹ * w * h := by group
    refine ⟨⟨a, ha⟩, h⁻¹, hOU ?_⟩
    change (a : ↥d.G)⁻¹ * (h⁻¹ * (a * w) * h⁻¹⁻¹) ∈ O
    rw [heq]; exact hyO

/-! ## Compact sets lie in `G`-domains compact modulo conjugation -/

section GoodDomain

variable (d : GGPData F)

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra in
/-- **Every element lies in a `G`-domain compact modulo conjugation.** For `c = s u` (Jordan
decomposition, `exists_jordan_G`), `u = e^N` with `N = log u` nilpotent in `𝔤_s`
(`exists_expA_nsmul_eq_one_add_pow`; `N ∈ 𝔤` because `e^{mᵏN} = u^{mᵏ} ∈ G(F)` with `mᵏN → 0`,
`eventually_mem_lie_of_expA_mem`). Waldspurger §3.1 at `s` (`waldspurger_goodNbhd`) gives a good
neighbourhood `ω_s` and the `G`-domain `Ω_s = (s exp ω_s)^{G(F)}`, compact modulo conjugation. For
small `α ≠ 0`, `α²N ∈ ω_s`, and `α²N = h N h⁻¹` with `h` commuting with `s`
(`kottwitz_nilpotent_sq_smul`), so `h c h⁻¹ = s e^{α²N} ∈ Ω_s` and `c ∈ Ω_s`. -/
theorem exists_goodDomain_mem (c : ↥d.G) :
    ∃ Ω : Set ↥d.G, IsOpen Ω ∧ IsClosed Ω ∧ (∀ x g : ↥d.G, g ∈ Ω → x * g * x⁻¹ ∈ Ω) ∧
      ∃ K : Set ↥d.G, IsCompact K ∧ (∀ g ∈ Ω, ∃ (x k : ↥d.G), k ∈ K ∧ g = x * k * x⁻¹) ∧
        c ∈ Ω := by
  have := isTopologicalRing_of_moduleTopology F d.ambient
  have : ContinuousSMul F d.ambient := IsModuleTopology.toContinuousSMul F d.ambient
  have hval : ∀ g h : ↥d.G, ((g : d.ambientˣ) : d.ambient) = ((h : d.ambientˣ) : d.ambient) →
      g = h := fun g h hgh => Subtype.ext (Units.ext hgh)
  obtain ⟨sG, hss, N, hNs, ⟨n, hNn⟩, hcN⟩ := exists_eq_mul_expA_nilpotent d c
  set s : d.ambient := ((sG : d.ambientˣ) : d.ambient) with hsd
  -- Waldspurger at `s`
  obtain ⟨ω, E, Ω, -, h0, hωo, -, -, -, -, ⟨e, he⟩, hΩo, hΩc, hΩinv, hΩeq, ⟨K, hK, hKsub⟩, -⟩ :=
    waldspurger_goodNbhd d sG hss Filter.univ_mem
  -- a small `α ≠ 0` with `α²N ∈ ω`
  obtain ⟨U, hUo, hUω⟩ := isOpen_induced_iff.1 hωo
  have hαN : ∀ α : F, α ^ 2 • N ∈ lieCentralizer d.lie s := fun α =>
    (lieCentralizer d.lie s).smul_mem _ hNs
  have h0U : (0 : d.ambient) ∈ U := by
    have : (⟨0, (lieCentralizer d.lie s).zero_mem⟩ : ↥(lieCentralizer d.lie s)) ∈
        Subtype.val ⁻¹' U := by rw [hUω]; exact h0
    exact this
  have hf : Continuous fun α : F => α ^ 2 • N := (continuous_pow 2).smul continuous_const
  have hpre : (fun α : F => α ^ 2 • N) ⁻¹' U ∈ 𝓝 (0 : F) :=
    hf.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by simpa using h0U))
  have := NormedField.nhdsNE_neBot (0 : F)
  obtain ⟨α, hαU, hα0⟩ : ∃ α : F, α ^ 2 • N ∈ U ∧ α ≠ 0 :=
    ((eventually_nhdsWithin_of_eventually_nhds (s := {0}ᶜ) hpre).and
      (self_mem_nhdsWithin (s := {0}ᶜ) (a := (0 : F)))).exists
  have hαω : α ^ 2 • N ∈ ω := by
    have : (⟨α ^ 2 • N, hαN α⟩ : ↥(lieCentralizer d.lie s)) ∈ Subtype.val ⁻¹' ω := by
      rw [← hUω]; exact hαU
    exact this
  obtain ⟨h, hhs, hhN⟩ := kottwitz_nilpotent_sq_smul d sG hss hNs ⟨n, hNn⟩ hα0
  set X : ↥ω := ⟨α ^ 2 • N, hαω⟩
  have hcomm : ((h : d.ambientˣ) : d.ambient) * s = s * ((h : d.ambientˣ) : d.ambient) := by
    simpa using congrArg (fun g : ↥d.G => ((g : d.ambientˣ) : d.ambient)) hhs
  have hc' : h * c * h⁻¹ ∈ Ω := by
    rw [hΩeq]
    refine ⟨1, (e X : ↥d.G), (e X).2, hval _ _ ?_⟩
    rw [show (1 : ↥d.G) * (sG * (e X : ↥d.G)) * 1⁻¹ = sG * (e X : ↥d.G) by group]
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [he X]
    change ((h : d.ambientˣ) : d.ambient) * ((c : d.ambientˣ) : d.ambient) *
      ((h⁻¹ : ↥d.G) : d.ambientˣ) = s * expA F (α ^ 2 • N)
    rw [← hhN, expA_conj_G, hcN, ← mul_assoc, hcomm, mul_assoc, mul_assoc, mul_assoc]
    simp
  refine ⟨Ω, hΩo, hΩc, hΩinv, K, hK, hKsub, ?_⟩
  have := hΩinv h⁻¹ _ hc'
  rwa [show h⁻¹ * (h * c * h⁻¹) * h⁻¹⁻¹ = c by group] at this

end GoodDomain

/-- **Compactness modulo conjugation, `p`-adic open-and-closed form** (BP Astérisque 418
Prop 3.1.1(i) = Thesis Prop 3.5.1(i), adapted). Every compact `C ⊆ G(F)` is contained in a subset `Ω`
that is open and closed, conjugation invariant and `A_G(F)`-stable (`IsInvariantClopen`), and compact
modulo conjugation and `A_G(F)`: `Ω ⊆ A_G(F) · C'^{G(F)}` for a compact `C'`. (In
`TraceFormula/Geometric.lean` terms: `C` lies in a set of the projective system `IsQCCutoff`.)

BP Prop 3.1.1(i) gives open invariant sets with closures compact modulo conjugation, not closed
`A_G(F)`-stable ones. Proof: every `c ∈ C` lies in a `G`-domain compact modulo conjugation
(`exists_goodDomain_mem`); finitely many cover `C`, and their union is saturated by `A_G(F)`
(`isInvariantClopen_AG_mul`). -/
theorem hc_exists_invariantClopen_superset (d : GGPData F) {C : Set ↥d.G} (hC : IsCompact C) :
    ∃ Ω : Set ↥d.G, IsInvariantClopen d Ω ∧ C ⊆ Ω ∧
      ∃ C' : Set ↥d.G, IsCompact C' ∧
        ∀ g ∈ Ω, ∃ (a : ↥d.AG) (x c : ↥d.G), c ∈ C' ∧ g = (a : ↥d.G) * (x * c * x⁻¹) := by
  choose Ωf hΩo hΩc hΩinv Kf hKf hKsub hmem using exists_goodDomain_mem d
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover Ωf hΩo fun c _ => Set.mem_iUnion.2 ⟨c, hmem c⟩
  set Ω₀ : Set ↥d.G := ⋃ i ∈ t, Ωf i
  set K : Set ↥d.G := ⋃ i ∈ t, Kf i
  have hΩ₀o : IsOpen Ω₀ := isOpen_biUnion fun i _ => hΩo i
  have hΩ₀c : IsClosed Ω₀ := t.finite_toSet.isClosed_biUnion fun i _ => hΩc i
  have hΩ₀inv : ∀ x g : ↥d.G, g ∈ Ω₀ → x * g * x⁻¹ ∈ Ω₀ := by
    intro x g hg
    obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion₂.1 hg
    exact Set.mem_iUnion₂.2 ⟨i, hi, hΩinv i x g hgi⟩
  have hK : IsCompact K := t.isCompact_biUnion fun i _ => hKf i
  have hsub : ∀ g ∈ Ω₀, ∃ (x k : ↥d.G), k ∈ K ∧ g = x * k * x⁻¹ := by
    intro g hg
    obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion₂.1 hg
    obtain ⟨x, k, hk, rfl⟩ := hKsub i g hgi
    exact ⟨x, k, Set.mem_iUnion₂.2 ⟨i, hi, hk⟩, rfl⟩
  refine ⟨(d.AG : Set ↥d.G) * Ω₀, d.isInvariantClopen_AG_mul hΩ₀o hΩ₀c hΩ₀inv hK hsub,
    fun c hc => ⟨1, d.AG.one_mem, c, ht hc, one_mul c⟩, K, hK, ?_⟩
  rintro _ ⟨a, ha, w, hw, rfl⟩
  obtain ⟨x, k, hk, rfl⟩ := hsub w hw
  exact ⟨⟨a, ha⟩, x, k, hk, rfl⟩

end GSpinGGP
