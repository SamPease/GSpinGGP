/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LieAlgebra
import GSpinGGP.TraceFormula.InvariantSets
import GSpinGGP.Foundations.GSpinExp
import GSpinGGP.Foundations.RatioNearOne

/-!
# Descent neighbourhoods of `0` in `𝔤⁰(F)`

Waldspurger's good neighbourhoods (2010, §3.1; `waldspurger_goodNbhd_one`) are neighbourhoods of `0`
in `𝔤(F) = 𝔷(F) ⊕ 𝔤⁰(F)`. This file passes from them to neighbourhoods in `𝔤⁰(F)`, for triples
without a hyperbolic-plane factor (then `A_G(F)` is the group of pairs of scalars and
`Lie(A_G) = 𝔷`).

* `cenAlg`, `cenCoord`: `𝔷 = F·(1,0) ⊕ F·(0,1) ≅ F × F`, and the central coordinate
  `Y ↦ (tr L_{Y₁} / dim C(W), tr L_{Y₂} / dim C(V))`, which vanishes on `𝔤⁰` (`so` is the traceless
  part of `gspin`), is invariant under conjugation, and splits `Y ∈ 𝔤` as
  `Y = cenAlg (cenCoord Y) + Y⁰` with `Y⁰ ∈ 𝔤⁰` (`sub_cenAlg_cenCoord_mem_lie0`).
* `eq_of_expA_eq_mul_AG`: if `X, X' ∈ 𝔤⁰` are conjugate to small elements, `X` lies in a good
  neighbourhood `ω₁` and `e^X = a e^{X'}` with `a ∈ A_G(F)`, then `X = X'`. The traces of left
  multiplication by `e^X` and `e^{X'}` on each factor are close to `dim C(W)`, `dim C(V)` (they are
  conjugation invariant), so the scalars `a = (c₁, c₂)` are close to `1` and `a = e^z` with `z ∈ 𝔷`
  small; then `e^X = e^{z + X'}` with `X, z + X' ∈ ω₁`, so `X = z + X'` and `z ∈ 𝔷 ∩ 𝔤⁰ = 0`.
* `exists_isLieDescentNbhd`: the construction. Take a good neighbourhood `ω₁` (for injectivity of
  `exp`), a smaller one `ω₂` inside `S^{G(F)}` for a set `S` chosen small with respect to `ω₁`, and
  `ω = {X ∈ 𝔤⁰ : z + X ∈ ω₂ for some z ∈ 𝔷}` (the projection of `ω₂` to `𝔤⁰`). Then `ω ⊆ ω₁`,
  `exp` is a homeomorphism of `ω` onto its image `Ω₀`, injective modulo `A_G(F)`, and
  `A_G(F)·Ω₀ = A_G(F)·exp(ω₂)` is open, closed and invariant (`isInvariantClopen_AG_mul`).
-/

noncomputable section

open Topology Filter Module
open scoped Pointwise

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

/-! ## Descent neighbourhoods -/

/-- **A descent neighbourhood of `0` in `𝔤⁰(F)`** (Thesis §12.4, BP §3.3, Waldspurger 2010 §3.1):
`ω ⊆ 𝔤⁰(F)` open and closed, containing `0`, invariant under `G(F)`, compact modulo conjugation;
`exp` is a homeomorphism of `ω` onto `Ω₀ ⊆ G(F)`; two elements of `Ω₀` that differ by an element of
`A_G(F)` are equal; and `Ω = A_G(F)·Ω₀` is open, closed, invariant and `A_G(F)`-stable.  This is a
weakening of the thesis's `G(F)`-excellent neighbourhood `ω` with `Ω = A_G(F)·exp(ω)`, written for
`𝔤⁰` (Thesis §12.4 uses `𝔤 = Lie(A_G) ⊕ 𝔤⁰`); the smallness conditions are imposed separately by
`IsConjSmall`. -/
structure IsLieDescentNbhd (ω : Set ↥d.lieZero) (Ω₀ : Set ↥d.G) : Prop where
  isOpen : IsOpen ω
  isClosed : IsClosed ω
  zero_mem : (0 : ↥d.lieZero) ∈ ω
  adLie0_mem : ∀ (g : ↥d.G) (X : ↥d.lieZero), X ∈ ω → d.adLie0 g X ∈ ω
  compact_mod_conj : ∃ Γ : Set ↥d.lieZero, IsCompact Γ ∧
    ∀ X ∈ ω, ∃ g : ↥d.G, ∃ Y ∈ Γ, X = d.adLie0 g Y
  exp_homeo : ∃ e : ↥ω ≃ₜ ↥Ω₀, ∀ X : ↥ω,
    ((((e X : ↥Ω₀) : ↥d.G) : d.ambientˣ) : d.ambient) = expA F ((X : ↥d.lieZero) : d.ambient)
  eq_of_mul_AG : ∀ g ∈ Ω₀, ∀ g' ∈ Ω₀, ∀ a ∈ d.AG, g = a * g' → g = g'
  isInvariantClopen : IsInvariantClopen d ((d.AG : Set ↥d.G) * Ω₀)

/-- Every element of `ω` is `G(F)`-conjugate into `ω₀` (`ω ⊆ ω₀^{G(F)}`, Waldspurger 2010 §3.1). -/
def IsConjSmall (ω₀ : Set d.ambient) (ω : Set ↥d.lieZero) : Prop :=
  ∀ X ∈ ω, ∃ g : ↥d.G, ∃ Y ∈ ω₀,
    ((X : ↥d.lieZero) : d.ambient) = ((g : d.ambientˣ) : d.ambient) * Y * ((g⁻¹ : d.ambientˣ) : d.ambient)

theorem IsConjSmall.mono {ω₀ ω₁ : Set d.ambient} {ω : Set ↥d.lieZero} (h : d.IsConjSmall ω₀ ω)
    (h01 : ω₀ ⊆ ω₁) : d.IsConjSmall ω₁ ω := fun X hX => by
  obtain ⟨g, Y, hY, e⟩ := h X hX
  exact ⟨g, Y, h01 hY, e⟩

theorem IsConjSmall.of_inter_left {ω₀ ω₁ : Set d.ambient} {ω : Set ↥d.lieZero}
    (h : d.IsConjSmall (ω₀ ∩ ω₁) ω) : d.IsConjSmall ω₀ ω := h.mono _ Set.inter_subset_left

theorem IsConjSmall.of_inter_right {ω₀ ω₁ : Set d.ambient} {ω : Set ↥d.lieZero}
    (h : d.IsConjSmall (ω₀ ∩ ω₁) ω) : d.IsConjSmall ω₁ ω := h.mono _ Set.inter_subset_right

/-- `1 = e^0 ∈ Ω = A_G(F)·Ω₀`. -/
theorem IsLieDescentNbhd.one_mem {ω : Set ↥d.lieZero} {Ω₀ : Set ↥d.G}
    (h : d.IsLieDescentNbhd ω Ω₀) : (1 : ↥d.G) ∈ (d.AG : Set ↥d.G) * Ω₀ := by
  obtain ⟨e, he⟩ := h.exp_homeo
  have h0 := he ⟨0, h.zero_mem⟩
  rw [show (((⟨0, h.zero_mem⟩ : ↥ω) : ↥d.lieZero) : d.ambient) = 0 from rfl,
    expA_zero_eq_one] at h0
  have h1 : ((e ⟨0, h.zero_mem⟩ : ↥Ω₀) : ↥d.G) = 1 := Subtype.ext (Units.ext h0)
  exact ⟨1, d.AG.one_mem, _, h1 ▸ (e ⟨0, h.zero_mem⟩).2, one_mul _⟩

/-! ## The centre `𝔷 ≅ F × F` and the central coordinate -/

section Central

/-- `𝔷 ≅ F × F`: `(w₁, w₂) ↦ (w₁·1, w₂·1)`, an algebra homomorphism `F × F → C(W) × C(V)`. -/
def cenAlg : F × F →ₐ[F] d.ambient := (Algebra.ofId F _).prodMap (Algebra.ofId F _)

@[simp] theorem cenAlg_apply (w : F × F) :
    d.cenAlg w =
      (algebraMap F (CliffordAlgebra d.QW) w.1, algebraMap F (CliffordAlgebra d.QV) w.2) :=
  rfl

theorem cenAlg_mem_lieCenter (w : F × F) : d.cenAlg w ∈ d.lieCenter := by
  have e : d.cenAlg w =
      w.1 • ((1 : CliffordAlgebra d.QW), (0 : CliffordAlgebra d.QV)) + w.2 • (0, 1) := by
    ext <;> simp [Algebra.algebraMap_eq_smul_one]
  rw [e]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem cenAlg_mem_lie (w : F × F) : d.cenAlg w ∈ d.lie :=
  d.lieCenter_le_lie (d.cenAlg_mem_lieCenter w)

theorem cenAlg_commute (w : F × F) (Y : d.ambient) : Commute (d.cenAlg w) Y :=
  Prod.ext (Algebra.commutes w.1 Y.1) (Algebra.commutes w.2 Y.2)

/-- Conjugation fixes `𝔷`. -/
theorem conj_add_cenAlg (g : ↥d.G) (w : F × F) (Y : d.ambient) :
    ((g : d.ambientˣ) : d.ambient) * (d.cenAlg w + Y) * ((g⁻¹ : d.ambientˣ) : d.ambient) =
      d.cenAlg w + ((g : d.ambientˣ) : d.ambient) * Y * ((g⁻¹ : d.ambientˣ) : d.ambient) := by
  have h1 : ((g : d.ambientˣ) : d.ambient) * d.cenAlg w * ((g⁻¹ : d.ambientˣ) : d.ambient) =
      d.cenAlg w := by
    rw [← (d.cenAlg_commute w _).eq, mul_assoc]
    simp
  rw [mul_add, add_mul, h1]

/-- The traces `(tr L_{Y₁}, tr L_{Y₂})` of left multiplication on the two factors, as a linear
map. -/
def trPairₗ : d.ambient →ₗ[F] F × F :=
  ((LinearMap.trace F _ ∘ₗ LinearMap.mul F _) ∘ₗ LinearMap.fst F _ _).prod
    ((LinearMap.trace F _ ∘ₗ LinearMap.mul F _) ∘ₗ LinearMap.snd F _ _)

/-- `trPair Y = (tr L_{Y₁}, tr L_{Y₂})`. -/
def trPair : d.ambient → F × F := ⇑d.trPairₗ

theorem trPairₗ_apply (Y : d.ambient) : d.trPairₗ Y = d.trPair Y := rfl

theorem continuous_trPair : Continuous d.trPair :=
  IsModuleTopology.continuous_of_linearMap d.trPairₗ

/-- `(dim C(W), dim C(V))`. -/
private def dimPair : F × F :=
  ((finrank F (CliffordAlgebra d.QW) : F), (finrank F (CliffordAlgebra d.QV) : F))

private theorem dimPair_fst_ne_zero : d.dimPair.1 ≠ 0 := cast_finrank_cliffordAlgebra_ne_zero d.QW

private theorem dimPair_snd_ne_zero : d.dimPair.2 ≠ 0 := cast_finrank_cliffordAlgebra_ne_zero d.QV

private theorem trPair_one : d.trPair 1 = d.dimPair :=
  Prod.ext (cliffTrace_one d.QW) (cliffTrace_one d.QV)

theorem trPair_cenAlg_mul (w : F × F) (Y : d.ambient) :
    d.trPair (d.cenAlg w * Y) = w * d.trPair Y := by
  refine Prod.ext ?_ ?_
  · show cliffTrace d.QW (algebraMap F _ w.1 * Y.1) = w.1 * cliffTrace d.QW Y.1
    rw [← Algebra.smul_def, cliffTrace_smul]
  · show cliffTrace d.QV (algebraMap F _ w.2 * Y.2) = w.2 * cliffTrace d.QV Y.2
    rw [← Algebra.smul_def, cliffTrace_smul]

theorem trPair_add (Y Y' : d.ambient) : d.trPair (Y + Y') = d.trPair Y + d.trPair Y' :=
  map_add d.trPairₗ Y Y'

/-- `trPair` is invariant under conjugation by `G(F)`. -/
theorem trPair_conj (g : ↥d.G) (Y : d.ambient) :
    d.trPair (((g : d.ambientˣ) : d.ambient) * Y * ((g⁻¹ : d.ambientˣ) : d.ambient)) =
      d.trPair Y := by
  have hinv : ((g⁻¹ : d.ambientˣ) : d.ambient) * ((g : d.ambientˣ) : d.ambient) = 1 := by simp
  refine Prod.ext ?_ ?_
  · exact cliffTrace_mul_mul_of_mul_eq_one d.QW Y.1 (congrArg Prod.fst hinv)
  · exact cliffTrace_mul_mul_of_mul_eq_one d.QV Y.2 (congrArg Prod.snd hinv)

/-- `trPair` vanishes on `𝔤⁰ = so(W) ⊕ so(V)`. -/
theorem trPair_eq_zero_of_mem_lie0 {Y : d.ambient} (hY : Y ∈ d.lie0) : d.trPair Y = 0 :=
  Prod.ext hY.1.2 hY.2.2

/-- **The central coordinate** `Y ↦ (tr L_{Y₁} / dim C(W), tr L_{Y₂} / dim C(V))`. -/
def cenCoord (Y : d.ambient) : F × F := (d.dimPair)⁻¹ * d.trPair Y

theorem continuous_cenCoord : Continuous d.cenCoord :=
  continuous_const.mul d.continuous_trPair

theorem cenCoord_zero : d.cenCoord 0 = 0 := by
  simp [cenCoord, ← d.trPairₗ_apply]

theorem cenCoord_conj (g : ↥d.G) (Y : d.ambient) :
    d.cenCoord (((g : d.ambientˣ) : d.ambient) * Y * ((g⁻¹ : d.ambientˣ) : d.ambient)) =
      d.cenCoord Y := by
  rw [cenCoord, cenCoord, trPair_conj]

theorem cenCoord_cenAlg_add {w : F × F} {Y : d.ambient} (hY : Y ∈ d.lie0) :
    d.cenCoord (d.cenAlg w + Y) = w := by
  rw [cenCoord, trPair_add, trPair_eq_zero_of_mem_lie0 d hY, add_zero,
    show d.cenAlg w = d.cenAlg w * 1 from (mul_one _).symm, trPair_cenAlg_mul, trPair_one]
  refine Prod.ext ?_ ?_
  · show (d.dimPair.1)⁻¹ * (w.1 * d.dimPair.1) = w.1
    field_simp [d.dimPair_fst_ne_zero]
  · show (d.dimPair.2)⁻¹ * (w.2 * d.dimPair.2) = w.2
    field_simp [d.dimPair_snd_ne_zero]

/-- **`𝔤 = 𝔷 ⊕ 𝔤⁰`, explicitly**: `Y − cenAlg (cenCoord Y) ∈ 𝔤⁰` for `Y ∈ 𝔤`. -/
theorem sub_cenAlg_cenCoord_mem_lie0 {Y : d.ambient} (hY : Y ∈ d.lie) :
    Y - d.cenAlg (d.cenCoord Y) ∈ d.lie0 := by
  have hY' : Y ∈ d.lie.toSubmodule := hY
  rw [d.lie_eq_center_sup_lie0, Submodule.mem_sup] at hY'
  obtain ⟨z, hz, Y₀, hY₀, rfl⟩ := hY'
  rw [lieCenter, Submodule.mem_span_pair] at hz
  obtain ⟨a, b, rfl⟩ := hz
  have hz : a • ((1 : CliffordAlgebra d.QW), (0 : CliffordAlgebra d.QV)) +
      b • ((0 : CliffordAlgebra d.QW), (1 : CliffordAlgebra d.QV)) = d.cenAlg (a, b) := by
    ext <;> simp [Algebra.algebraMap_eq_smul_one]
  rw [hz, cenCoord_cenAlg_add d hY₀, add_sub_cancel_left]
  exact hY₀

/-- `𝔷 ∩ 𝔤⁰ = 0`, for elements of the form `cenAlg w`. -/
theorem cenAlg_eq_zero_of_mem_lie0 {w : F × F} (hw : d.cenAlg w ∈ d.lie0) : d.cenAlg w = 0 :=
  (Submodule.disjoint_def.1 d.disjoint_lieCenter_lie0) _ (d.cenAlg_mem_lieCenter w) hw

end Central

/-! ## The exponential on `𝔷` and on `𝔷 + (conjugates of small elements)` -/

section Exp

theorem continuous_cenAlg : Continuous d.cenAlg :=
  IsModuleTopology.continuous_of_linearMap d.cenAlg.toLinearMap

/-- The value of `(c₁, c₂) ∈ G(F)` is `cenAlg (c₁, c₂)`. -/
private theorem val_scalarPair_eq_cenAlg (c₁ c₂ : Fˣ) :
    (((d.scalarPair c₁ c₂ : ↥d.G) : d.ambientˣ) : d.ambient) = d.cenAlg ((c₁ : F), (c₂ : F)) :=
  rfl

/-- For `w` near `0`: `e^{cenAlg w} = cenAlg (e^w)`, and it is a pair of scalars in `A_G(F)`. -/
theorem eventually_expA_cenAlg :
    ∀ᶠ w in 𝓝 (0 : F × F), d.cenAlg (expA F w) = expA F (d.cenAlg w) ∧
      ∃ a ∈ d.AG, ((a : d.ambientˣ) : d.ambient) = expA F (d.cenAlg w) := by
  obtain ⟨U, hU, hinv⟩ := expA_mul_expA_neg F (A := F × F)
  filter_upwards [eventually_map_expA (F := F) (A := F × F) (B := d.ambient) d.cenAlg.toLinearMap
    (fun X n => map_pow d.cenAlg X n), hU] with w hw hwU
  have h1 := hinv w hwU
  have hne1 : (expA F w).1 ≠ 0 := left_ne_zero_of_mul_eq_one (congrArg Prod.fst h1)
  have hne2 : (expA F w).2 ≠ 0 := left_ne_zero_of_mul_eq_one (congrArg Prod.snd h1)
  refine ⟨hw, d.scalarPair (Units.mk0 _ hne1) (Units.mk0 _ hne2), d.scalarPair_mem_AG _ _, ?_⟩
  rw [val_scalarPair_eq_cenAlg]
  exact hw

/-- Every `c ∈ F × F` near `1` is `e^w` with `w` in a given neighbourhood of `0`. -/
theorem eventually_exists_expA_eq {W : Set (F × F)} (hW : W ∈ 𝓝 (0 : F × F)) :
    ∀ᶠ c in 𝓝 (1 : F × F), ∃ w ∈ W, expA F w = c := by
  obtain ⟨log, hlc, hl1, hlog⟩ := exists_logA F (A := F × F)
  filter_upwards [hlog, hlc.preimage_mem_nhds (by rwa [hl1])] with c hc hcW
  exact ⟨log c, hcW, hc⟩

/-- **`e^{z + X} = e^z e^X`** for `z ∈ 𝔷` small and `X` conjugate to a small element (`z` is
central; transport `expA_add_of_commute` by conjugation). -/
theorem exists_nhds_expA_cenAlg_add_conj :
    ∃ U ∈ 𝓝 (0 : d.ambient), ∀ w : F × F, d.cenAlg w ∈ U → ∀ (h : ↥d.G), ∀ Y ∈ U,
      expA F (d.cenAlg w +
          ((h : d.ambientˣ) : d.ambient) * Y * ((h⁻¹ : d.ambientˣ) : d.ambient)) =
        expA F (d.cenAlg w) *
          expA F (((h : d.ambientˣ) : d.ambient) * Y * ((h⁻¹ : d.ambientˣ) : d.ambient)) := by
  obtain ⟨U, hU, hadd⟩ := expA_add_of_commute F (A := d.ambient)
  refine ⟨U, hU, fun w hw h Y hY => ?_⟩
  rw [← d.conj_add_cenAlg, expA_conj_G d h, hadd _ hw _ hY (d.cenAlg_commute w Y), expA_conj_G d h]
  have hc : Commute ((h : d.ambientˣ) : d.ambient) (expA F (d.cenAlg w)) :=
    commute_expA_of_commute (F := F) (d.cenAlg_commute w _).symm
  simp only [← mul_assoc, hc.eq]

/-- An open subset of `𝔤(F)` containing `0` contains `O ∩ 𝔤(F)` for a neighbourhood `O` of `0`. -/
theorem exists_nhds_of_isOpen_lie {ω : Set d.ambient}
    (hωo : IsOpen (Subtype.val ⁻¹' ω : Set ↥d.lie)) (h0 : (0 : d.ambient) ∈ ω) :
    ∃ O ∈ 𝓝 (0 : d.ambient), ∀ Y ∈ O, Y ∈ d.lie → Y ∈ ω := by
  obtain ⟨O, hO, hOω⟩ :=
    (mem_nhds_subtype _ ⟨0, d.lie.zero_mem⟩ _).1 (hωo.mem_nhds (x := ⟨0, d.lie.zero_mem⟩) h0)
  exact ⟨O, hO, fun Y hY hYl => hOω (a := ⟨Y, hYl⟩) hY⟩

end Exp

/-! ## Injectivity of `exp` modulo `A_G(F)` -/

section Core

variable {d} {ω₁ : Set d.ambient} {Ω₁ : Set ↥d.G} (e₁ : ↥ω₁ ≃ₜ ↥Ω₁)
  (he₁ : ∀ X : ↥ω₁, ((((e₁ X : ↥Ω₁) : ↥d.G) : d.ambientˣ) : d.ambient) = expA F (X : d.ambient))
include he₁

/-- **`exp` is injective modulo `A_G(F)` on small elements of `𝔤⁰`.** Let `ω₁` be invariant with
`exp : ω₁ ≃ Ω₁`, `O` a neighbourhood of `0` with `O ∩ 𝔤 ⊆ ω₁`, `V + V ⊆ O`, `U` as in
`exists_nhds_expA_cenAlg_add_conj`, and `WF`, `Uc`, `N` neighbourhoods of `0`, `1`,
`(dim C(W), dim C(V))` with: `cenAlg (WF) ⊆ V ∩ U` (and `exp` commutes with `cenAlg` there),
every `c ∈ Uc` is `e^w`
with `w ∈ WF`, and `p = cq` with `p, q ∈ N` forces `c ∈ Uc`. If `X, X' ∈ 𝔤⁰`, `X ∈ ω₁`, `X` is
conjugate to `Y` with `trPair (e^Y) ∈ N`, `X'` is conjugate to `Y' ∈ V ∩ U ∩ 𝔤` with
`trPair (e^{Y'}) ∈ N`, and `e^X = a e^{X'}` with `a ∈ A_G(F)`, then `X = X'`. -/
private theorem eq_of_expA_eq_mul_AG (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    (hω₁inv : ∀ g : ↥d.G, ∀ X ∈ ω₁,
      ((g : d.ambientˣ) : d.ambient) * X * ((g⁻¹ : d.ambientˣ) : d.ambient) ∈ ω₁)
    {O : Set d.ambient} (hO : ∀ Y ∈ O, Y ∈ d.lie → Y ∈ ω₁)
    {V : Set d.ambient} (hVO : ∀ v ∈ V, ∀ v' ∈ V, v + v' ∈ O)
    {U : Set d.ambient} (hU : ∀ w : F × F, d.cenAlg w ∈ U → ∀ (h : ↥d.G), ∀ Y ∈ U,
      expA F (d.cenAlg w +
          ((h : d.ambientˣ) : d.ambient) * Y * ((h⁻¹ : d.ambientˣ) : d.ambient)) =
        expA F (d.cenAlg w) *
          expA F (((h : d.ambientˣ) : d.ambient) * Y * ((h⁻¹ : d.ambientˣ) : d.ambient)))
    {WF : Set (F × F)} (hWF : ∀ w ∈ WF, d.cenAlg w ∈ V ∧ d.cenAlg w ∈ U ∧
      d.cenAlg (expA F w) = expA F (d.cenAlg w))
    {Uc : Set (F × F)} (hUc : ∀ c ∈ Uc, ∃ w ∈ WF, expA F w = c)
    {N : Set (F × F)} (hN : ∀ p ∈ N, ∀ q ∈ N, ∀ c : F × F, p = c * q → c ∈ Uc)
    {X X' : d.ambient} (hX0 : X ∈ d.lie0) (hX'0 : X' ∈ d.lie0) (hX1 : X ∈ ω₁)
    (hXT : ∃ (g : ↥d.G) (Y : d.ambient), d.trPair (expA F Y) ∈ N ∧
      X = ((g : d.ambientˣ) : d.ambient) * Y * ((g⁻¹ : d.ambientˣ) : d.ambient))
    (hX' : ∃ (h : ↥d.G) (Y : d.ambient), Y ∈ V ∧ Y ∈ U ∧ d.trPair (expA F Y) ∈ N ∧ Y ∈ d.lie ∧
      X' = ((h : d.ambientˣ) : d.ambient) * Y * ((h⁻¹ : d.ambientˣ) : d.ambient))
    {a : ↥d.G} (ha : a ∈ d.AG)
    (heq : expA F X = ((a : d.ambientˣ) : d.ambient) * expA F X') : X = X' := by
  obtain ⟨c₁, c₂, rfl⟩ := d.exists_eq_scalarPair_of_mem_AG hW hV ha
  obtain ⟨g, Y, hYN, hXY⟩ := hXT
  obtain ⟨h, Y', hY'V, hY'U, hY'N, hY'l, hXY'⟩ := hX'
  have hτX : d.trPair (expA F X) ∈ N := by rw [hXY, expA_conj_G d g, trPair_conj]; exact hYN
  have hτX' : d.trPair (expA F X') ∈ N := by rw [hXY', expA_conj_G d h, trPair_conj]; exact hY'N
  obtain ⟨w, hwWF, hew⟩ := hUc _ (hN _ hτX _ hτX' ((c₁ : F), (c₂ : F))
    (by rw [heq, val_scalarPair_eq_cenAlg, trPair_cenAlg_mul]))
  obtain ⟨hwV, hwU, hwexp⟩ := hWF w hwWF
  have hez : expA F (d.cenAlg w) =
      (((d.scalarPair c₁ c₂ : ↥d.G) : d.ambientˣ) : d.ambient) := by
    rw [← hwexp, hew, val_scalarPair_eq_cenAlg]
  have hsplit : expA F (d.cenAlg w + X') = expA F (d.cenAlg w) * expA F X' := by
    rw [hXY']; exact hU w hwU h Y' hY'U
  have hmem : d.cenAlg w + X' ∈ ω₁ := by
    rw [hXY', ← d.conj_add_cenAlg]
    exact hω₁inv h _ (hO _ (hVO _ hwV _ hY'V) (add_mem (d.cenAlg_mem_lie w) hY'l))
  have hinj : X = d.cenAlg w + X' := by
    have := e₁.injective (a₁ := ⟨X, hX1⟩) (a₂ := ⟨_, hmem⟩)
      (Subtype.ext (Subtype.ext (Units.ext (by rw [he₁, he₁, heq, hsplit, hez]))))
    exact congrArg Subtype.val this
  have hz0 : d.cenAlg w ∈ d.lie0 := by
    have e : d.cenAlg w = X - X' := by rw [hinj]; abel
    rw [e]; exact sub_mem hX0 hX'0
  rw [hinj, d.cenAlg_eq_zero_of_mem_lie0 hz0, zero_add]

end Core

/-! ## The construction -/

section Construction

/-- `𝔤⁰(F)` is closed in `C(W) × C(V)` (a finite-dimensional subspace). -/
theorem isClosed_lieZero : IsClosed (d.lieZero : Set d.ambient) := by
  have := t2Space_of_moduleTopology F d.ambient
  have := isTopologicalRing_of_moduleTopology F d.ambient
  have : ContinuousSMul F d.ambient := IsModuleTopology.toContinuousSMul F d.ambient
  exact Submodule.isClosed_of_finiteDimensional (LieSubalgebra.toSubmodule d.lieZero)

/-- The projection to `𝔤⁰` of the part of `ω₂` with central coordinate in `K`:
`{X ∈ 𝔤⁰ : cenAlg w + X ∈ ω₂ for some w ∈ K}`. -/
private def projLie0 (K : Set (F × F)) (ω₂ : Set d.ambient) : Set ↥d.lieZero :=
  {X | ∃ w ∈ K, d.cenAlg w + (X : d.ambient) ∈ ω₂}

private theorem isOpen_projLie0 (K : Set (F × F)) {ω₂ : Set d.ambient}
    (hω₂o : IsOpen (Subtype.val ⁻¹' ω₂ : Set ↥d.lie)) : IsOpen (d.projLie0 K ω₂) := by
  have e : d.projLie0 K ω₂ = ⋃ w ∈ K, (fun X : ↥d.lieZero => (⟨d.cenAlg w + X,
      add_mem (d.cenAlg_mem_lie w) (d.lieZero_le_lie X.2)⟩ : ↥d.lie)) ⁻¹'
        (Subtype.val ⁻¹' ω₂) := by
    ext X; simp [projLie0]
  rw [e]
  exact isOpen_biUnion fun w _ => hω₂o.preimage
    ((continuous_const.add continuous_subtypeVal).subtype_mk _)

/-- For compact `K` and closed `ω₂`, the projection is closed (projection along a compact
factor). -/
private theorem isClosed_projLie0 {K : Set (F × F)} (hK : IsCompact K) {ω₂ : Set d.ambient}
    (hω₂c : IsClosed ω₂) : IsClosed (d.projLie0 K ω₂) := by
  have : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  have := isTopologicalRing_of_moduleTopology F d.ambient
  have e : d.projLie0 K ω₂ =
      Prod.snd '' {p : ↥K × ↥d.lieZero | d.cenAlg p.1 + (p.2 : d.ambient) ∈ ω₂} := by
    ext X
    constructor
    · rintro ⟨w, hw, hX⟩; exact ⟨(⟨w, hw⟩, X), hX, rfl⟩
    · rintro ⟨⟨w, X'⟩, hX', rfl⟩; exact ⟨w, w.2, hX'⟩
  rw [e]
  exact isClosedMap_snd_of_compactSpace _ (hω₂c.preimage
    (((d.continuous_cenAlg.comp continuous_subtypeVal).comp _root_.continuous_fst).add
      (continuous_subtypeVal.comp _root_.continuous_snd)))

private theorem adLie0_mem_projLie0 {K : Set (F × F)} {ω₂ : Set d.ambient}
    (hω₂inv : ∀ g : ↥d.G, ∀ X ∈ ω₂,
      ((g : d.ambientˣ) : d.ambient) * X * ((g⁻¹ : d.ambientˣ) : d.ambient) ∈ ω₂)
    (g : ↥d.G) {X : ↥d.lieZero} (hX : X ∈ d.projLie0 K ω₂) : d.adLie0 g X ∈ d.projLie0 K ω₂ := by
  obtain ⟨w, hw, hX⟩ := hX
  refine ⟨w, hw, ?_⟩
  have := hω₂inv g _ hX
  rw [d.conj_add_cenAlg] at this
  rw [coe_adLie0]
  exact this

/-- If every element of `ω₂` is conjugate into `S`, and `Y − cenAlg (cenCoord Y) ∈ P` for `Y ∈ S`,
then every `X ∈ 𝔤⁰` with `cenAlg w + X ∈ ω₂` is conjugate to an element of `P ∩ 𝔤⁰`. -/
private theorem exists_conj_of_cenAlg_add_mem {ω₂ S P : Set d.ambient} (hω₂lie : ω₂ ⊆ d.lie)
    (hsmall : ∀ Y ∈ ω₂, ∃ g : ↥d.G, ∃ Y' ∈ S,
      Y = ((g : d.ambientˣ) : d.ambient) * Y' * ((g⁻¹ : d.ambientˣ) : d.ambient))
    (hS : ∀ Y ∈ S, Y - d.cenAlg (d.cenCoord Y) ∈ P)
    {w : F × F} {X : d.ambient} (hX : X ∈ d.lie0) (hwX : d.cenAlg w + X ∈ ω₂) :
    ∃ (h : ↥d.G) (Y : d.ambient), Y ∈ P ∧ Y ∈ d.lie0 ∧
      X = ((h : d.ambientˣ) : d.ambient) * Y * ((h⁻¹ : d.ambientˣ) : d.ambient) := by
  obtain ⟨h, Y', hY'S, hEq⟩ := hsmall _ hwX
  have hcc : d.cenCoord Y' = w := by
    rw [← d.cenCoord_conj h Y', ← hEq, d.cenCoord_cenAlg_add hX]
  have hY'l : Y' ∈ d.lie := by
    have := d.conj_mem_lie h⁻¹ (hω₂lie hwX)
    rw [hEq] at this
    simpa [mul_assoc] using this
  refine ⟨h, Y' - d.cenAlg w, by rw [← hcc]; exact hS Y' hY'S,
    by rw [← hcc]; exact d.sub_cenAlg_cenCoord_mem_lie0 hY'l, ?_⟩
  have h2 := d.conj_add_cenAlg h w (Y' - d.cenAlg w)
  rw [show d.cenAlg w + (Y' - d.cenAlg w) = Y' by abel, ← hEq] at h2
  exact add_left_cancel h2

/-- **Descent neighbourhoods exist inside every `ω₀^{G(F)}`** (Waldspurger 2010 §3.1 at `x = 1`,
applied to `𝔤 = 𝔷 ⊕ 𝔤⁰`; BP §3.3), when neither `W` nor `V` is a hyperbolic plane (so `A_G(F)` is
the group of pairs of scalars and `Lie(A_G) = 𝔷`).

Proof: take a good neighbourhood
`ω₁` of `0` in `𝔤(F)` (`waldspurger_goodNbhd_one`), a smaller one `ω₂ ⊆ S^{G(F)}` with `S` small
relative to `ω₁` and `ω₀`, and `ω = {X ∈ 𝔤⁰(F) : z + X ∈ ω₂ for some small z ∈ 𝔷}` (the projection
of `ω₂` along `𝔤 = 𝔷 ⊕ 𝔤⁰`), `Ω₀ = exp(ω)`.  Since `𝔷` is central, `e^{z + X} = e^z e^X` with
`e^z ∈ A_G(F)`, so `A_G(F)·Ω₀ = A_G(F)·exp(ω₂)`, which is open, closed, invariant and
`A_G(F)`-stable (`isInvariantClopen_AG_mul`); `ω ⊆ ω₁`, so `exp` is a homeomorphism of `ω` onto
`Ω₀`.  If `e^X = a e^{X'}` with `X, X' ∈ ω`, `a ∈ A_G(F)`, then `a` is close to `1` (the traces of
left multiplication by `e^X`, `e^{X'}` on `C(W)`, `C(V)` are conjugation invariant, hence close to
`dim C(W)`, `dim C(V)`), so `a = e^z` with `z ∈ 𝔷` small, `e^X = e^{z + X'}` with `X, z + X' ∈ ω₁`,
so `X = z + X'`, and `z ∈ 𝔷 ∩ 𝔤⁰ = 0`. -/
theorem exists_isLieDescentNbhd (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    {ω₀ : Set d.ambient} (hω₀ : ω₀ ∈ 𝓝 (0 : d.ambient)) :
    ∃ (ω : Set ↥d.lieZero) (Ω₀ : Set ↥d.G), d.IsLieDescentNbhd ω Ω₀ ∧ d.IsConjSmall ω₀ ω := by
  have := isTopologicalRing_of_moduleTopology F d.ambient
  -- the injectivity domain `ω₁` and the neighbourhoods chosen relative to it
  obtain ⟨ω₁, Ω₁, -, h0ω₁, hω₁o, -, hω₁inv, ⟨Γ₁, -, hΓ₁, hω₁Γ⟩, -, -, -, ⟨e₁, he₁⟩, -⟩ :=
    waldspurger_goodNbhd_one d Filter.univ_mem
  obtain ⟨O, hO, hOω₁⟩ := d.exists_nhds_of_isOpen_lie hω₁o h0ω₁
  obtain ⟨V, hV0, hVO⟩ := exists_nhds_zero_half hO
  obtain ⟨U, hU0, hU⟩ := d.exists_nhds_expA_cenAlg_add_conj
  set WF : Set (F × F) := {w | (d.cenAlg w ∈ V ∧ d.cenAlg w ∈ U ∧
    d.cenAlg (expA F w) = expA F (d.cenAlg w)) ∧
      ∃ a ∈ d.AG, ((a : d.ambientˣ) : d.ambient) = expA F (d.cenAlg w)}
  have hWF : WF ∈ 𝓝 (0 : F × F) := by
    have hc : Tendsto d.cenAlg (𝓝 0) (𝓝 0) := by
      have := d.continuous_cenAlg.tendsto (0 : F × F)
      rwa [map_zero] at this
    filter_upwards [hc (inter_mem hV0 hU0), d.eventually_expA_cenAlg] with w hw hw'
    exact ⟨⟨hw.1, hw.2, hw'.1⟩, hw'.2⟩
  obtain ⟨K, hK0, hKWF, hK⟩ := local_compact_nhds hWF
  set Uc : Set (F × F) := {c | ∃ w ∈ WF, expA F w = c}
  have hUc : Uc ∈ 𝓝 (1 : F × F) := eventually_exists_expA_eq hWF
  obtain ⟨N, hN0, hN⟩ :=
    exists_mem_nhds_eq_mul_imp_mem_prod d.dimPair_fst_ne_zero d.dimPair_snd_ne_zero hUc
  set T : Set d.ambient := {Y | d.trPair (expA F Y) ∈ N}
  have hT : T ∈ 𝓝 (0 : d.ambient) := by
    have hc : ContinuousAt (fun Y => d.trPair (expA F Y)) 0 :=
      d.continuous_trPair.continuousAt.comp (continuousAt_expA_at_zero F)
    exact hc.preimage_mem_nhds (by simpa [expA_zero_eq_one, trPair_one] using hN0)
  set P : Set d.ambient := V ∩ U ∩ T ∩ ω₀ ∩ O
  have hP : P ∈ 𝓝 (0 : d.ambient) :=
    inter_mem (inter_mem (inter_mem (inter_mem hV0 hU0) hT) hω₀) hO
  set S : Set d.ambient := {Y | d.cenCoord Y ∈ K ∧ Y - d.cenAlg (d.cenCoord Y) ∈ P}
  have hS : S ∈ 𝓝 (0 : d.ambient) := by
    refine (inter_mem ?_ ?_ : {Y : d.ambient | d.cenCoord Y ∈ K} ∩
      {Y | Y - d.cenAlg (d.cenCoord Y) ∈ P} ∈ 𝓝 (0 : d.ambient))
    · exact d.continuous_cenCoord.continuousAt.preimage_mem_nhds (by rwa [d.cenCoord_zero])
    · refine (continuous_id.sub
        (d.continuous_cenAlg.comp d.continuous_cenCoord)).continuousAt.preimage_mem_nhds ?_
      change _ ∈ 𝓝 ((0 : d.ambient) - d.cenAlg (d.cenCoord 0))
      rw [d.cenCoord_zero, map_zero, sub_zero]
      exact hP
  -- the small good neighbourhood `ω₂ ⊆ S^{G(F)}`
  obtain ⟨ω₂, Ω₂, hω₂lie, h0ω₂, hω₂o, hω₂c, hω₂inv, ⟨Γ₂, -, hΓ₂, hω₂Γ⟩, hΩ₂o, hΩ₂c, hΩ₂inv,
    ⟨e₂, he₂⟩, hsmall₂⟩ := waldspurger_goodNbhd_one d hS
  have hrep : ∀ {w : F × F} {X : d.ambient}, X ∈ d.lie0 → d.cenAlg w + X ∈ ω₂ →
      ∃ (h : ↥d.G) (Y : d.ambient), Y ∈ P ∧ Y ∈ d.lie0 ∧
        X = ((h : d.ambientˣ) : d.ambient) * Y * ((h⁻¹ : d.ambientˣ) : d.ambient) :=
    fun hX hwX => d.exists_conj_of_cenAlg_add_mem hω₂lie hsmall₂ (fun Y hY => hY.2) hX hwX
  set ω := d.projLie0 K ω₂ with hωdef
  have hsub : ∀ X ∈ ω, ((X : ↥d.lieZero) : d.ambient) ∈ ω₁ := by
    rintro X ⟨w, -, hwX⟩
    obtain ⟨h, Y, hYP, hY0, hXY⟩ := hrep X.2 hwX
    rw [hXY]
    exact hω₁inv h _ (hOω₁ _ hYP.2 (d.lie0_le_lie hY0))
  have hsplit : ∀ {w : F × F} {X : d.ambient}, X ∈ d.lie0 → w ∈ K → d.cenAlg w + X ∈ ω₂ →
      ∃ b ∈ d.AG, expA F (d.cenAlg w + X) = ((b : d.ambientˣ) : d.ambient) * expA F X := by
    intro w X hX hwK hwX
    obtain ⟨h, Y, hYP, -, rfl⟩ := hrep hX hwX
    obtain ⟨⟨-, hwU, -⟩, b, hb, hbv⟩ := hKWF hwK
    exact ⟨b, hb, by rw [hbv]; exact hU w hwU h Y hYP.1.1.1.2⟩
  -- `exp : ω → G(F)` is an embedding (the restriction of `e₁`)
  let ι : ↥ω → ↥ω₁ := fun X => ⟨((X : ↥d.lieZero) : d.ambient), hsub X X.2⟩
  let f : ↥ω → ↥d.G := fun X => (e₁ (ι X) : ↥d.G)
  have hfval : ∀ X : ↥ω, (((f X : ↥d.G) : d.ambientˣ) : d.ambient) =
      expA F ((X : ↥d.lieZero) : d.ambient) := fun X => he₁ (ι X)
  have hf : Topology.IsEmbedding f := by
    have h2 : Topology.IsEmbedding (fun X : ↥ω => ((X : ↥d.lieZero) : d.ambient)) :=
      Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    have hι : Topology.IsEmbedding ι := (Topology.IsEmbedding.subtypeVal.of_comp_iff).1 h2
    exact Topology.IsEmbedding.subtypeVal.comp (e₁.isEmbedding.comp hι)
  refine ⟨ω, Set.range f, ⟨d.isOpen_projLie0 K hω₂o,
    d.isClosed_projLie0 hK (isClosed_of_subset_lie d hω₂lie hω₂c),
    ⟨0, mem_of_mem_nhds hK0, by
      show d.cenAlg 0 + ((0 : ↥d.lieZero) : d.ambient) ∈ ω₂
      rw [map_zero, zero_add]; exact h0ω₂⟩,
    fun g X hX => d.adLie0_mem_projLie0 hω₂inv g hX, ?_, ⟨hf.toHomeomorph, hfval⟩, ?_, ?_⟩, ?_⟩
  · -- compact modulo conjugation
    refine ⟨Subtype.val ⁻¹' Γ₁,
      d.isClosed_lieZero.isClosedEmbedding_subtypeVal.isCompact_preimage hΓ₁,
      fun X hX => ?_⟩
    obtain ⟨g, Y, hYΓ, hXY⟩ := hω₁Γ _ (hsub X hX)
    have hY0 : Y ∈ d.lie0 := by
      have := d.conj_mem_lie0 g⁻¹ (d.mem_lieZero.1 X.2)
      rw [hXY] at this
      simpa [mul_assoc] using this
    exact ⟨g, ⟨Y, hY0⟩, hYΓ, Subtype.ext (by rw [coe_adLie0]; exact hXY)⟩
  · -- injectivity modulo `A_G(F)`
    rintro _ ⟨X, rfl⟩ _ ⟨X', rfl⟩ a ha hfa
    have hv : expA F ((X : ↥d.lieZero) : d.ambient) =
        ((a : d.ambientˣ) : d.ambient) * expA F ((X' : ↥d.lieZero) : d.ambient) := by
      rw [← hfval X, ← hfval X', hfa]; rfl
    obtain ⟨w, -, hwX⟩ := X.2
    obtain ⟨w', -, hwX'⟩ := X'.2
    obtain ⟨h, Y, hYP, -, hXY⟩ := hrep (X : ↥d.lieZero).2 hwX
    obtain ⟨h', Y', hY'P, hY'0, hXY'⟩ := hrep (X' : ↥d.lieZero).2 hwX'
    have hXX := eq_of_expA_eq_mul_AG e₁ he₁ hW hV hω₁inv hOω₁ hVO hU (WF := WF)
      (fun w hw => hw.1) (Uc := Uc) (fun c hc => hc) hN (X := ((X : ↥d.lieZero) : d.ambient))
      (X' := ((X' : ↥d.lieZero) : d.ambient)) (X : ↥d.lieZero).2 (X' : ↥d.lieZero).2
      (hsub X X.2) ⟨h, Y, hYP.1.1.2, hXY⟩
      ⟨h', Y', hY'P.1.1.1.1, hY'P.1.1.1.2, hY'P.1.1.2, d.lie0_le_lie hY'0, hXY'⟩ ha hv
    rw [Subtype.ext (Subtype.ext hXX)]
  · -- `A_G(F)·Ω₀ = A_G(F)·Ω₂`
    obtain ⟨K₂, hK₂, hK₂sub⟩ := exists_compact_conj_of_expHomeo e₂ he₂ hω₂lie hω₂c hω₂inv hΓ₂ hω₂Γ
    have hcl := d.isInvariantClopen_AG_mul hΩ₂o hΩ₂c hΩ₂inv hK₂ hK₂sub
    suffices e : (d.AG : Set ↥d.G) * Set.range f = (d.AG : Set ↥d.G) * Ω₂ by rw [e]; exact hcl
    apply Set.Subset.antisymm
    · rintro _ ⟨a, ha, _, ⟨X, rfl⟩, rfl⟩
      obtain ⟨w, hwK, hwX⟩ := X.2
      obtain ⟨b, hb, hbe⟩ := hsplit (X : ↥d.lieZero).2 hwK hwX
      have he : (e₂ ⟨_, hwX⟩ : ↥d.G) = b * f X := by
        apply Subtype.ext; apply Units.ext
        rw [he₂]
        change expA F (d.cenAlg w + _) =
          ((b : d.ambientˣ) : d.ambient) * (((f X : ↥d.G) : d.ambientˣ) : d.ambient)
        rw [hbe, hfval]
      refine ⟨a * b⁻¹, d.AG.mul_mem ha (d.AG.inv_mem hb), _, (e₂ ⟨_, hwX⟩).2, ?_⟩
      show a * b⁻¹ * (e₂ ⟨_, hwX⟩ : ↥d.G) = a * f X
      rw [he]; group
    · rintro _ ⟨a, ha, y, hy, rfl⟩
      set Y : d.ambient := ((e₂.symm ⟨y, hy⟩ : ↥ω₂) : d.ambient) with hYdef
      have hYω₂ : Y ∈ ω₂ := (e₂.symm ⟨y, hy⟩).2
      have hyY : ((y : d.ambientˣ) : d.ambient) = expA F Y := by
        rw [hYdef, ← he₂, e₂.apply_symm_apply]
      obtain ⟨h, Y', hY'S, hYY'⟩ := hsmall₂ Y hYω₂
      have hwY : d.cenCoord Y = d.cenCoord Y' := by rw [hYY', cenCoord_conj]
      have hX0 : Y - d.cenAlg (d.cenCoord Y') ∈ d.lie0 := by
        rw [← hwY]; exact d.sub_cenAlg_cenCoord_mem_lie0 (hω₂lie hYω₂)
      have hwX : d.cenAlg (d.cenCoord Y') + (Y - d.cenAlg (d.cenCoord Y')) ∈ ω₂ := by
        rw [show d.cenAlg (d.cenCoord Y') + (Y - d.cenAlg (d.cenCoord Y')) = Y by abel]
        exact hYω₂
      have hXω : (⟨_, hX0⟩ : ↥d.lieZero) ∈ ω := ⟨_, hY'S.1, hwX⟩
      obtain ⟨b, hb, hbe⟩ := hsplit hX0 hY'S.1 hwX
      have hyb : y = b * f ⟨_, hXω⟩ := by
        apply Subtype.ext; apply Units.ext
        show _ = ((b : d.ambientˣ) : d.ambient) * (((f _ : ↥d.G) : d.ambientˣ) : d.ambient)
        rw [hyY, hfval]
        rw [show d.cenAlg (d.cenCoord Y') + (Y - d.cenAlg (d.cenCoord Y')) = Y by abel] at hbe
        exact hbe
      refine ⟨a * b, d.AG.mul_mem ha hb, f ⟨_, hXω⟩, ⟨_, rfl⟩, ?_⟩
      show a * b * f ⟨_, hXω⟩ = a * y
      rw [hyb, mul_assoc]
  · -- smallness
    rintro X ⟨w, -, hwX⟩
    obtain ⟨h, Y, hYP, -, hXY⟩ := hrep X.2 hwX
    exact ⟨h, Y, hYP.1.2, hXY⟩

end Construction

end GGPData

end GSpinGGP
