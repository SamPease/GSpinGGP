/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.MGeom
import GSpinGGP.Literature.TraceFormula
import GSpinGGP.Literature.InvariantSets

/-!
# Elliptic isolation and cutting quasi-characters

The statements in §1 are the interface consumed by
`Spine.lean` (and available to `Lie.lean`).  §2 is proved
from §1.

The spine statement `exists_scusp_ell` (Thesis Cor 4.8.3(i) in `χ`-equivariant form) is
proved in `Spine.lean` as `exists_scusp_ell_bp` (§3 below), from BP Cor 5.7.2(i) and the
`χ`-transfer; `exists_qc_cutoff_ell` cuts `θ_P` off near the elliptic set (proved here from BP
Cor 5.7.2(i)).

**What is proved here, and what is not.**
* §0 helpers: multiplying a quasi-character by a locally constant invariant function
  (`isQuasiCharacter_mul_of_isLocallyConstant`); invariant clopen sets.
* `LitTF.bp_scusp_surj_ell` (BP Cor 5.7.2(i), untwisted on `G(F)`) gives *one* invariant clopen
  `Ω ⊇ G_ell,reg`, compact modulo conjugation and `A_G(F)`, on which `S_scusp(Ω) → QC_c(Ω)` is onto.
  The own **`χ`-transfer** (`exists_scusp_of_qc_bp`, §3): `θ₀ = κ θ` for the `A_G`-cutoff `κ`
  (`exists_isAGCutoff`), `f₀` from BP Cor 5.7.2(i), `f = P_χ f₀`, and `θ_f = ∫ χ(a) θ₀(a ·) da = θ`
  (`isThetaF_chiProj_avg`).  Consequence: `exists_scusp_ell_bp`, which has exactly the type of the
  spine statement `exists_scusp_ell` and depends only on BP Cor 5.7.2(i) and the
  `A_G`-cutoff of `SpinorNorm.lean`/`ThetaF.lean`.
* Surjectivity onto the compactly supported quasi-characters of an *arbitrary* invariant clopen `Ω`
  is not stated: it is **stronger than BP Cor 5.7.2(i)**, which is existential in `Ω` (one
  `Ω` containing the elliptic set) (see §1).
* `exists_scusp_cut` uses no surjectivity statement: `f₁ = 1_Ω f` works directly
  (`indicator_mem_scuspTestFn`, `isThetaF_indicator`), from the elementary fact that an invariant
  clopen set is saturated along unipotent radicals (`mem_mul_parabolicU_iff`, SORRY).
-/

noncomputable section

open MeasureTheory Topology Filter
open scoped Pointwise

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-! ## 0. Helpers -/

section ExpHelper

variable {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A]
  [IsModuleTopology F A]

/-- **Local constancy transported along `x e^X`** (copy of `Sanity/Witnesses.lean`
`exists_nhds_zero_mul_expA`, which cannot be imported here): if `θ` is constant near `x` in
`G(F)`, then `θ(y) = θ(x)` whenever `y = x e^X` with `X` in a neighbourhood of `0` (the topology of
`G(F) ⊆ Aˣ` is that of `A × Aᵐᵒᵖ` via `(y, y⁻¹)`; `e^{-X} x⁻¹` is the inverse of `x e^X`). -/
theorem exists_nhds_zero_mul_expA_of_eventually {G : Subgroup Aˣ} {θ : ↥G → ℂ} {x : ↥G}
    (hθ : ∀ᶠ y in 𝓝 x, θ y = θ x) :
    ∃ ω ∈ 𝓝 (0 : A), ∀ X ∈ ω, ∀ y : ↥G,
      ((y : Aˣ) : A) = ((x : Aˣ) : A) * expA F X → θ y = θ x := by
  let _ := isTopologicalRing_of_moduleTopology F A
  rw [nhds_subtype, Filter.eventually_comap] at hθ
  have hθ' : ∀ᶠ u in 𝓝 (x : Aˣ), ∀ y : ↥G, (y : Aˣ) = u → θ y = θ x := hθ
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.eventually_comap] at hθ'
  set f : A → A × Aᵐᵒᵖ := fun X => (((x : Aˣ) : A) * expA F X,
      MulOpposite.op (expA F (-X) * (((x : Aˣ)⁻¹ : Aˣ) : A))) with hf
  have hc : ContinuousAt f 0 := by
    have h1 : ContinuousAt (fun X : A => expA F X) 0 := continuousAt_expA_at_zero F
    have h2 : ContinuousAt (fun X : A => expA F (-X)) 0 := by
      have : ContinuousAt (fun X : A => -X) 0 := continuous_neg.continuousAt
      exact ContinuousAt.comp (g := expA F) (by simpa using continuousAt_expA_at_zero F) this
    refine ContinuousAt.prodMk (continuousAt_const.mul h1) ?_
    exact MulOpposite.continuous_op.continuousAt.comp (h2.mul continuousAt_const)
  have hval : f 0 = Units.embedProduct A (x : Aˣ) := by
    simp [hf, expA_zero_eq_one F, Units.embedProduct]
  have hc2 : Tendsto f (𝓝 0) (𝓝 (Units.embedProduct A (x : Aˣ))) := by
    rw [← hval]; exact hc
  obtain ⟨U, hU, hUinv⟩ := expA_mul_expA_neg F (A := A)
  refine ⟨_, Filter.inter_mem (hc2.eventually hθ') hU, fun X hX y hy => ?_⟩
  obtain ⟨hX1, hX2⟩ := hX
  refine hX1 (y : Aˣ) ?_ y rfl
  have hinv : (((y : Aˣ)⁻¹ : Aˣ) : A) = expA F (-X) * (((x : Aˣ)⁻¹ : Aˣ) : A) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hy, mul_assoc, ← mul_assoc (expA F X), hUinv X hX2, one_mul, Units.mul_inv]
  simp only [hf, Units.embedProduct_apply, hy, hinv]

end ExpHelper

/-- The indicator of an open and closed set times a locally constant function is locally
constant. -/
theorem isLocallyConstant_indicator_of_isClopen {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsClopen s) {f : X → ℂ} (hf : IsLocallyConstant f) : IsLocallyConstant (s.indicator f) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ s
  · filter_upwards [hs.isOpen.mem_nhds hx, hf.eventually_eq x] with y hy h
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, h]
  · filter_upwards [hs.isClosed.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

section Helpers

variable (d : GGPData F)

/-- **A quasi-character times a locally constant invariant function is a quasi-character** (Thesis
§4.1.1: "if `θ` is a quasi-character and `f ∈ C^∞(ω)^G` then `fθ` is a quasi-character"; BP §4.1).
At a semisimple `x`, `κ` is constant on `x e^ω` for `ω` small, so the germs are multiplied by
`κ(x)`. -/
theorem isQuasiCharacter_mul_of_isLocallyConstant (ψ : NontrivialAddChar F) {κ θ : ↥d.G → ℂ}
    (hκ : IsLocallyConstant κ) (hconj : ∀ x g : ↥d.G, κ (x * g * x⁻¹) = κ g)
    (hθ : IsQuasiCharacter d.G d.lie d.bilin ψ θ) :
    IsQuasiCharacter d.G d.lie d.bilin ψ (fun g => κ g * θ g) := by
  refine ⟨fun g y hy => ?_, fun x hx => ?_⟩
  · simp only [hconj g y, hθ.1 g y hy]
  · obtain ⟨c, hfin, ω, hω, hexp⟩ := hθ.2 x hx
    obtain ⟨ω', hω', hκω⟩ :=
      exists_nhds_zero_mul_expA_of_eventually (F := F) (hκ.eventually_eq x)
    refine ⟨fun O => κ x * c O, hfin.subset fun O hO => ?_, ω ∩ ω', inter_mem hω hω',
      fun X hX hXc hXr y hy => ?_⟩
    · exact fun h => hO (by simp [h])
    · dsimp only
      rw [hκω X hX.2 y hy, hexp X hX.1 hXc hXr y hy, mul_finsum]
      simp only [mul_assoc]

variable {d}

theorem IsInvariantClopen.isClopen {Ω : Set ↥d.G} (hΩ : IsInvariantClopen d Ω) : IsClopen Ω :=
  ⟨hΩ.2.1, hΩ.1⟩

theorem IsInvariantClopen.conj_mem_iff {Ω : Set ↥d.G} (hΩ : IsInvariantClopen d Ω) (x g : ↥d.G) :
    x * g * x⁻¹ ∈ Ω ↔ g ∈ Ω := by
  refine ⟨fun h => ?_, hΩ.2.2.1 x g⟩
  have := hΩ.2.2.1 x⁻¹ _ h
  rwa [show x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g by group] at this

theorem IsInvariantClopen.inv_conj_mem_iff {Ω : Set ↥d.G} (hΩ : IsInvariantClopen d Ω)
    (x g : ↥d.G) : x⁻¹ * g * x ∈ Ω ↔ g ∈ Ω := by
  simpa using hΩ.conj_mem_iff x⁻¹ g

theorem IsInvariantClopen.AG_mul_mem_iff {Ω : Set ↥d.G} (hΩ : IsInvariantClopen d Ω) (a : ↥d.AG)
    (g : ↥d.G) : (a : ↥d.G) * g ∈ Ω ↔ g ∈ Ω := by
  refine ⟨fun h => ?_, hΩ.2.2.2 a g⟩
  have := hΩ.2.2.2 a⁻¹ _ h
  simpa using this

variable (d)

/-- **Invariant clopen sets are saturated along unipotent radicals** (complete invariance, BP §3.1:
the semisimple part of `p u` is conjugate to that of `p`).  For `p = m u₀ ∈ P(F) = M(F) U(F)` and
`u ∈ U(F)`, conjugating `p u = m (u₀ u)` by `a ∈ A_M(F)` contracting `U` gives `m (a u₀ u a⁻¹) → m`,
so `m` lies in the closure of the class of `p u` and of `p`; `Ω` closed gives "⇒" (for `pu` and
for `p`), `Ω` open and invariant gives "⇐".  For a flag pair whose `U` is trivial there is nothing
to prove.  Status: SORRY (own work, PROVE: needs a Levi decomposition `P = M U` of the flag
stabilizers `GGPData.whittB` and a contracting cocharacter of `A_M`, lifted from `SO` to `GSpin`;
neither is formalized yet). -/
theorem mem_mul_parabolicU_iff {Ω : Set ↥d.G} (hΩ : IsInvariantClopen d Ω)
    (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) {p : ↥d.G}
    (hp : p ∈ d.parabolicP FW FV) {u : ↥d.G} (hu : u ∈ d.parabolicU FW FV) :
    p * u ∈ Ω ↔ p ∈ Ω := by
  sorry

/-- BP Cor 5.7.2(i) (`LitTF.bp_scusp_surj_ell`) in the vocabulary of `Basic.lean`/`ThetaF.lean`. -/
theorem exists_bpOmega : ∃ Ω : Set ↥d.G, IsInvariantClopen d Ω ∧ d.ellRegSet ⊆ Ω ∧
    (∃ C : Set ↥d.G, IsCompact C ∧
      ∀ g ∈ Ω, ∃ (a : ↥d.AG) (x c : ↥d.G), c ∈ C ∧ g = (a : ↥d.G) * (x * c * x⁻¹)) ∧
    ∀ θ₀ : ↥d.G → ℂ, (∀ ψ : NontrivialAddChar F, IsQuasiCharacter d.G d.lie d.bilin ψ θ₀) →
      (∃ C₀ : Set ↥d.G, IsCompact C₀ ∧ C₀ ⊆ Ω ∧
        ∀ g ∈ regularSet d.G d.lie, θ₀ g ≠ 0 → ∃ x c : ↥d.G, c ∈ C₀ ∧ g = x * c * x⁻¹) →
      ∃ f₀ ∈ testFunctions ↥d.G, IsStronglyCuspidalInline d f₀ ∧ Function.support f₀ ⊆ Ω ∧
        ∃ θ : ↥d.G → ℂ, IsThetaF d f₀ θ ∧ Set.EqOn θ θ₀ (regularSet d.G d.lie) := by
  obtain ⟨Ω, ho, hc, hconj, hAG, hell, hcpt, hsurj⟩ := LitTF.bp_scusp_surj_ell d
  refine ⟨Ω, ⟨ho, hc, hconj, hAG⟩, hell, hcpt, fun θ₀ hq hs => ?_⟩
  obtain ⟨f₀, hf₀, hcusp, hsupp, θ, hli, hco, heq, hpair⟩ := hsurj θ₀ hq hs
  exact ⟨f₀, hf₀, hcusp, hsupp, θ, ⟨hli, hco, hpair⟩, heq⟩

end Helpers

variable (d : GGPData F) (χ : CentralCharOn d)

/-! ## 1. Interface statements -/

/-- **Invariant clopen cutoffs preserve quasi-characters** (BP §4.1: the local expansion at a
semisimple `x` only involves a neighbourhood of `x`; `Ω` is open, its complement is open, and
`Ω` is invariant and `A_G(F)`-stable).  Status: PROVED (`1_Ω` is locally constant and invariant,
`isQuasiCharacter_mul_of_isLocallyConstant`). -/
theorem indicator_mem_QC {Ω : Set ↥d.G} (hΩ : IsInvariantClopen d Ω) {θ : ↥d.G → ℂ}
    (hθ : θ ∈ QC d χ) : Ω.indicator θ ∈ QC d χ := by
  have he : Ω.indicator θ = fun g => Ω.indicator (fun _ => (1 : ℂ)) g * θ g := by
    funext g
    by_cases hg : g ∈ Ω
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, one_mul]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]
  refine ⟨fun ψ => ?_, fun a g hg => ?_⟩
  · rw [he]
    refine isQuasiCharacter_mul_of_isLocallyConstant d ψ
      (isLocallyConstant_indicator_of_isClopen hΩ.isClopen (IsLocallyConstant.const 1))
      (fun x g => ?_) (hθ.1 ψ)
    by_cases hg : g ∈ Ω
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hΩ.conj_mem_iff x g).2 hg)]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt (hΩ.conj_mem_iff x g).1 hg)]
  · by_cases hga : g ∈ Ω
    · rw [Set.indicator_of_mem ((hΩ.AG_mul_mem_iff a g).2 hga), Set.indicator_of_mem hga,
        hθ.2 a g hg]
    · rw [Set.indicator_of_notMem (mt (hΩ.AG_mul_mem_iff a g).1 hga),
        Set.indicator_of_notMem hga, mul_zero]

/-- **Cutting a virtual character off near the elliptic set** (BP Lemma 4.2.3 and Prop 4.4.1 for
invariant cutoffs; Thesis §4.8): for a virtual tempered `P` with
central character `η`, there is `θ ∈ QC(G, η)` (Lean: `QC d η.inv`), compactly supported modulo
conjugation and `A_G(F)`, equal to `θ_P` on `G_ell,reg(F)`.  (Take `θ = κ θ_P` with `κ` the
indicator of an invariant, `A_G(F)`-stable open and closed neighbourhood of the elliptic set that is
compact modulo conjugation and `A_G(F)`; `θ_P ∈ QC d η.inv` is `vChar_mem_QC`.)
Status: PROVED from BP Cor 5.7.2(i) (`LitTF.bp_scusp_surj_ell`, whose `Ω` is such a neighbourhood),
`indicator_mem_QC` and `vChar_mem_QC`. -/
theorem exists_qc_cutoff_ell {η : CentralCharOn d} (P : VirtualTemp d η) :
    ∃ θ ∈ QC d η.inv, HasCompactSupportModConjAG d θ ∧ Set.EqOn θ (vChar d P) d.ellRegSet := by
  obtain ⟨Ω, hΩ, hell, ⟨C, hC, hCΩ⟩, -⟩ := exists_bpOmega d
  exact ⟨Ω.indicator (vChar d P), indicator_mem_QC d η.inv hΩ (vChar_mem_QC d P),
    ⟨C, hC, fun g _ hg => hCΩ g (Set.mem_of_indicator_ne_zero hg)⟩,
    fun x hx => Set.indicator_of_mem (hell hx) _⟩

/-! Surjectivity of `f ↦ θ_f` onto the compactly supported quasi-characters of an *arbitrary*
invariant clopen `Ω` (or of `Ω = G(F)`) is not stated: it is stronger than BP Cor 5.7.2(i), which
is existential in `Ω`.  The form used is `exists_scusp_of_qc_bp` (§3: one invariant clopen
`Ω ⊇ G_ell,reg`, from BP Cor 5.7.2(i) and the `χ`-transfer);
the cut `exists_scusp_cut` takes `f₁ = 1_Ω f` and needs no surjectivity.  A near-`1` use would cite
BP Prop 5.6.1(i) on `𝔤(F)` descended by `exp` (BP Prop 4.1.1). -/

/-! ## 2. Consequences (proved) -/

/-- **`1_Ω f` is again in `𝒞_scusp`** for an invariant clopen `Ω`: locally constant (`Ω` clopen),
`χ`-equivariant (`Ω` is `A_G(F)`-stable), supported in `supp f`, and strongly cuspidal because
`1_Ω(p u) = 1_Ω(p)` on `P(F)` (`mem_mul_parabolicU_iff`). -/
theorem indicator_mem_scuspTestFn {f : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d χ) {Ω : Set ↥d.G}
    (hΩ : IsInvariantClopen d Ω) : Ω.indicator f ∈ ScuspTestFn d χ := by
  classical
  obtain ⟨hf1, hf2, ⟨C, hC, hs⟩, hf4⟩ := hf
  refine ⟨isLocallyConstant_indicator_of_isClopen hΩ.isClopen hf1, fun a g => ?_,
    ⟨C, hC, fun x hx => hs ?_⟩, fun FW FV hP p hp => ?_⟩
  · by_cases hg : g ∈ Ω
    · rw [Set.indicator_of_mem ((hΩ.AG_mul_mem_iff a g).2 hg), Set.indicator_of_mem hg, hf2]
    · rw [Set.indicator_of_notMem (mt (hΩ.AG_mul_mem_iff a g).1 hg),
        Set.indicator_of_notMem hg, mul_zero]
  · rw [Function.mem_support] at hx ⊢
    exact fun h => hx (by simp [Set.indicator, h])
  · have hu : ∀ u : ↥(d.parabolicU FW FV),
        Ω.indicator f (p * u) = if p ∈ Ω then f (p * u) else 0 := fun u => by
      by_cases hpΩ : p ∈ Ω
      · simp only [hpΩ, ↓reduceIte]
        rw [Set.indicator_of_mem ((mem_mul_parabolicU_iff d hΩ FW FV hp u.2).2 hpΩ)]
      · simp only [hpΩ, ↓reduceIte]
        rw [Set.indicator_of_notMem (mt (mem_mul_parabolicU_iff d hΩ FW FV hp u.2).1 hpΩ)]
    simp_rw [hu]
    by_cases hpΩ : p ∈ Ω
    · simp only [hpΩ, ↓reduceIte]
      exact hf4 FW FV hP p hp
    · simp only [hpΩ, ↓reduceIte]
      exact ⟨integrable_zero _ _ _, integral_zero _ _⟩

/-- **`θ_{1_Ω f} = 1_Ω θ_f`** for an invariant clopen `Ω`: `⟨1_Ω f, f'⟩ = ⟨f, 1_Ω f'⟩` because
`x⁻¹ g x ∈ Ω ⟺ g ∈ Ω`, and `1_Ω f'` is again a test function. -/
theorem isThetaF_indicator {f θ : ↥d.G → ℂ} (h : IsThetaF d f θ) {Ω : Set ↥d.G}
    (hΩ : IsInvariantClopen d Ω) : IsThetaF d (Ω.indicator f) (Ω.indicator θ) := by
  obtain ⟨hli, hco, hpair⟩ := h
  refine ⟨hli.indicator hΩ.2.1.measurableSet, fun g hg => ?_, fun f' hf' => ?_⟩
  · by_cases hgΩ : g ∈ Ω
    · refine (hco g hg).congr_of_eventuallyEq ?_ (Set.indicator_of_mem hgΩ θ)
      exact nhdsWithin_le_nhds
        (Filter.mem_of_superset (hΩ.1.mem_nhds hgΩ) fun y hy => Set.indicator_of_mem hy θ)
    · refine (continuousWithinAt_const (b := (0 : ℂ))).congr_of_eventuallyEq ?_
        (Set.indicator_of_notMem hgΩ θ)
      exact nhdsWithin_le_nhds
        (Filter.mem_of_superset (hΩ.2.1.isOpen_compl.mem_nhds hgΩ)
          fun y hy => Set.indicator_of_notMem hy θ)
  · have hf'Ω : Ω.indicator f' ∈ testFunctions ↥d.G := by
      refine ⟨isLocallyConstant_indicator_of_isClopen hΩ.isClopen hf'.1, hf'.2.mono ?_⟩
      intro x hx
      rw [Function.mem_support] at hx ⊢
      exact fun h0 => hx (by simp [Set.indicator, h0])
    calc ∫ g, Ω.indicator θ g * f' g ∂Measure.haar
        = ∫ g, θ g * Ω.indicator f' g ∂Measure.haar := by
          refine integral_congr_ae (Eventually.of_forall fun g => ?_)
          by_cases hg : g ∈ Ω
          · simp only [Set.indicator_of_mem hg]
          · simp only [Set.indicator_of_notMem hg, zero_mul, mul_zero]
      _ = orbitalPairing d f (Ω.indicator f') := hpair _ hf'Ω
      _ = orbitalPairing d (Ω.indicator f) f' := by
          unfold orbitalPairing
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          refine integral_congr_ae (Eventually.of_forall fun g => ?_)
          by_cases hg : g ∈ Ω
          · simp only [Set.indicator_of_mem hg,
              Set.indicator_of_mem ((hΩ.inv_conj_mem_iff _ g).2 hg)]
          · simp only [Set.indicator_of_notMem hg,
              Set.indicator_of_notMem (mt (hΩ.inv_conj_mem_iff _ g).1 hg), mul_zero, zero_mul]

/-- **Cutting `θ_f` by an invariant clopen set** (BP §11.6, partition of unity): for
`f ∈ ScuspTestFn d χ` and invariant clopen `Ω`, some `f₁ ∈ ScuspTestFn d χ` supported in `Ω`
has `θ_{f₁} = 1_Ω θ_f` on `G_reg(F)`.  Proof: `f₁ = 1_Ω f` (`indicator_mem_scuspTestFn`,
`isThetaF_indicator`); no surjectivity statement (Cor 5.7.2) is needed. -/
theorem exists_scusp_cut {f : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d χ) {Ω : Set ↥d.G}
    (hΩ : IsInvariantClopen d Ω) :
    ∃ f₁ ∈ ScuspTestFn d χ, Function.support f₁ ⊆ Ω ∧
      Set.EqOn (thetaF d f₁) (Ω.indicator (thetaF d f)) (regularSet d.G d.lie) :=
  ⟨Ω.indicator f, indicator_mem_scuspTestFn d χ hf hΩ, Set.support_indicator_subset,
    eqOn_thetaF d (isThetaF_indicator d (thetaF_spec d χ hf).1 hΩ)⟩

/-- **`θ_f` is compactly supported modulo conjugation and `A_G(F)`** for
`f ∈ 𝒞_scusp(A_G(F)\G(F), χ⁻¹)` compactly supported modulo `A_G(F)` (BP §5.2, §5.5: `θ_f(x)` is a
weighted orbital integral of `f` at `x`, which vanishes unless the conjugacy class of `x` meets
`Supp f`).  (Frozen interface statement of §1, placed here because its proof uses
`isThetaF_indicator`.)
Proof: `supp f ⊆ A_G(F)·C` with `C` compact; Harish-Chandra's compactness lemma
(`hc_exists_invariantClopen_superset`) gives an invariant clopen `Ω ⊇ C`, `A_G(F)`-stable, hence
`⊇ supp f`, with `Ω ⊆ A_G(F)·C'^{G(F)}` for a compact `C'`.  Then `1_Ω f = f`, so
`θ_f = θ_{1_Ω f} = 1_Ω θ_f` on `G_reg(F)` (`isThetaF_indicator`, uniqueness `eqOn_thetaF`): `θ_f`
vanishes on `G_reg(F) ∖ Ω`.  Used by `geomAt_away` (`Geometric.lean`). -/
theorem thetaF_hasCompactSupportModConjAG {f : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d χ) :
    HasCompactSupportModConjAG d (thetaF d f) := by
  obtain ⟨C, hC, hs⟩ := hf.2.2.1
  obtain ⟨Ω, hΩ, hCΩ, C', hC', hΩC'⟩ := hc_exists_invariantClopen_superset d hC
  have hsΩ : Function.support f ⊆ Ω := fun g hg => by
    obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_mul.mp (hs hg)
    exact hΩ.2.2.2 ⟨a, ha⟩ c (hCΩ hc)
  have hθ : IsThetaF d f (Ω.indicator (thetaF d f)) := by
    have := isThetaF_indicator d (thetaF_spec d χ hf).1 hΩ
    rwa [Set.indicator_eq_self.2 hsΩ] at this
  refine ⟨C', hC', fun g hg hne => hΩC' g ?_⟩
  by_contra hgΩ
  exact hne ((eqOn_thetaF d hθ hg).trans (Set.indicator_of_notMem hgΩ _))

/-! ## 3. Elliptic isolation from BP Cor 5.7.2(i) and the own `χ`-transfer -/

/-- **`χ`-equivariant BP Cor 5.7.2(i)** (the density statement for Cor 5.7.2(i),
`p`-adic): for the invariant clopen `Ω ⊇ G_ell,reg` of BP Cor 5.7.2(i) (`LitTF.bp_scusp_surj_ell`),
compact modulo conjugation and `A_G(F)`, and every central character `χ`, every `θ ∈ QC(G, χ⁻¹)`
(Lean: `QC d χ`) compactly supported modulo conjugation and `A_G(F)` and vanishing on
`G_reg(F) ∖ Ω` is `θ_f` on `G_reg(F)` for some `f ∈ ScuspTestFn d χ` supported in `Ω`.

Own `χ`-transfer: `θ₀ = κ θ` with the `A_G`-cutoff `κ` (`exists_isAGCutoff`) is a
quasi-character supported in `Ad(G)(tsupport κ ∩ A_G·(C ∩ Ω))`, compact modulo conjugation inside
`Ω`; BP Cor 5.7.2(i) gives a strongly cuspidal `f₀ ∈ C_c^∞(Ω)` with `θ_{f₀} = θ₀`; then `f = P_χ f₀`
(`chiProj_mem_scusp`) and `θ_f(g) = ∫ χ(a) κ(a g) θ(a g) da = θ(g) ∫ κ(a g) da = θ(g)`
(`isThetaF_chiProj_avg`, `θ(ag) = χ(a)⁻¹ θ(g)`). -/
theorem exists_scusp_of_qc_bp : ∃ Ω : Set ↥d.G, IsInvariantClopen d Ω ∧ d.ellRegSet ⊆ Ω ∧
    (∃ C : Set ↥d.G, IsCompact C ∧
      ∀ g ∈ Ω, ∃ (a : ↥d.AG) (x c : ↥d.G), c ∈ C ∧ g = (a : ↥d.G) * (x * c * x⁻¹)) ∧
    ∀ (χ : CentralCharOn d) {θ : ↥d.G → ℂ}, θ ∈ QC d χ → HasCompactSupportModConjAG d θ →
      (∀ g ∈ regularSet d.G d.lie, g ∉ Ω → θ g = 0) →
      ∃ f ∈ ScuspTestFn d χ, Function.support f ⊆ Ω ∧
        Set.EqOn (thetaF d f) θ (regularSet d.G d.lie) := by
  obtain ⟨Ω, hΩ, hell, hcpt, hsurj⟩ := exists_bpOmega d
  refine ⟨Ω, hΩ, hell, hcpt, fun χ θ hθ hc hs => ?_⟩
  obtain ⟨κ, hκ⟩ := exists_isAGCutoff d
  have hq : ∀ ψ : NontrivialAddChar F,
      IsQuasiCharacter d.G d.lie d.bilin ψ (fun g => κ g * θ g) := fun ψ =>
    isQuasiCharacter_mul_of_isLocallyConstant d ψ hκ.isLocallyConstant hκ.conj (hθ.1 ψ)
  obtain ⟨C, hC, hsupp⟩ := hc
  have hsupp₀ : ∃ C₀ : Set ↥d.G, IsCompact C₀ ∧ C₀ ⊆ Ω ∧
      ∀ g ∈ regularSet d.G d.lie, (fun g => κ g * θ g) g ≠ 0 →
        ∃ x c : ↥d.G, c ∈ C₀ ∧ g = x * c * x⁻¹ := by
    refine ⟨tsupport κ ∩ ((d.AG : Set ↥d.G) * (C ∩ Ω)),
      hκ.isCompact_inter _ (hC.inter_right hΩ.2.1), ?_, fun g hg hne => ?_⟩
    · rintro _ ⟨-, a, ha, c, hc, rfl⟩
      exact hΩ.2.2.2 ⟨a, ha⟩ c hc.2
    · have hθg : θ g ≠ 0 := right_ne_zero_of_mul hne
      have hκg : κ g ≠ 0 := left_ne_zero_of_mul hne
      obtain ⟨a, x, c, hcC, rfl⟩ := hsupp g hg hθg
      have hgΩ : (a : ↥d.G) * (x * c * x⁻¹) ∈ Ω := by
        by_contra h
        exact hθg (hs _ hg h)
      have hcΩ : c ∈ Ω := (hΩ.conj_mem_iff x c).1 ((hΩ.AG_mul_mem_iff a _).1 hgΩ)
      have hxa : x * (a : ↥d.G) = (a : ↥d.G) * x :=
        Subgroup.mem_center_iff.mp (d.AG_le_center a.2) x
      have hcomm : (a : ↥d.G) * (x * c * x⁻¹) = x * ((a : ↥d.G) * c) * x⁻¹ := by
        rw [← mul_assoc x, hxa]
        simp only [mul_assoc]
      refine ⟨x, (a : ↥d.G) * c, ⟨subset_tsupport κ ?_, a, a.2, c, ⟨hcC, hcΩ⟩, rfl⟩, hcomm⟩
      rw [Function.mem_support, ← hκ.conj x, ← hcomm]
      exact hκg
  obtain ⟨f₀, hf₀, hcusp, hsuppf₀, θ', hθ', heq⟩ := hsurj _ hq hsupp₀
  have havg := isThetaF_chiProj_avg d χ hf₀ hcusp hθ'
  refine ⟨chiProj d χ f₀, chiProj_mem_scusp d χ hf₀ hcusp, fun g hg => ?_, fun g hg => ?_⟩
  · by_contra hgΩ
    apply hg
    unfold chiProj
    refine integral_eq_zero_of_ae (Eventually.of_forall fun a => ?_)
    have : f₀ ((a : ↥d.G) * g) = 0 := by
      by_contra hne
      exact hgΩ ((hΩ.AG_mul_mem_iff a g).1 (hsuppf₀ hne))
    simp [this]
  · rw [eqOn_thetaF d havg hg]
    have hpt : ∀ a : ↥d.AG, ((χ.toHom a : Circle) : ℂ) * θ' ((a : ↥d.G) * g) =
        κ ((a : ↥d.G) * g) * θ g := by
      intro a
      rw [heq (mul_mem_regularSet_of_mem_AG d a hg)]
      dsimp only
      rw [hθ.2 a g hg, Circle.coe_inv]
      have hu : ((χ.toHom a : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
      field_simp
    simp_rw [hpt]
    rw [integral_mul_const, hκ.integral_AG g, one_mul]

/-- **Elliptic isolation** (Thesis Cor 4.8.3(i) in `χ`-equivariant form): for a virtual tempered `P` with central character `η` there is
`f ∈ ScuspTestFn d η⁻¹` with `θ_f = θ_P` on `G_ell,reg(F)`.  This has exactly the type of the
spine statement `exists_scusp_ell` (`Spine.lean`) and is proved from BP Cor 5.7.2(i) and the `A_G`-cutoff only
(`exists_scusp_of_qc_bp` applied to `1_Ω θ_P`), without `exists_scusp_of_qc_on`. -/
theorem exists_scusp_ell_bp (η : CentralCharOn d) (P : VirtualTemp d η) :
    ∃ f ∈ ScuspTestFn d η.inv, ∀ x ∈ d.ellRegSet, thetaF d f x = vChar d P x := by
  obtain ⟨Ω, hΩ, hell, ⟨C, hC, hCΩ⟩, htr⟩ := exists_scusp_of_qc_bp d
  obtain ⟨f, hf, -, hfθ⟩ := htr η.inv (indicator_mem_QC d η.inv hΩ (vChar_mem_QC d P))
    ⟨C, hC, fun g _ hg => hCΩ g (Set.mem_of_indicator_ne_zero hg)⟩
    (fun g _ hg => Set.indicator_of_notMem hg _)
  exact ⟨f, hf, fun x hx =>
    (hfθ (d.ellRegSet_subset_regularSet hx)).trans (Set.indicator_of_mem (hell hx) _)⟩

end GSpinGGP
