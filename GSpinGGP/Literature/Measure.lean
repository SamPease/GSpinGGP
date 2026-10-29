/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Weil's quotient-measure formula (generic)

Layer-1 Literature file. It imports
Mathlib only and knows nothing about GSpin.

For a homomorphism `ι : S →* Γ` of groups, `CosetSpace ι` is the space `ι(S)\Γ` of *right*
cosets `ι(S)γ`, with the quotient topology and its Borel σ-algebra. A measure `m` on it is a
**Weil measure** for Haar measures `ν` on `Γ` and `μ` on `S` when

  `∫_Γ φ(γ) dν(γ) = ∫_{ι(S)\Γ} ∫_S φ(ι(s) γ) dμ(s) dm(γ)`  for all `φ ∈ C_c(Γ)`.

Consumer: the measure on `H(F)\G(F)/A_G(F)` in the distribution `J` (Thesis §7.1),
where `ι` is the closed embedding `H/A_{G,H} ↪ G/A_G`. The Haar measure on
`H/A_{G,H}` cancels between `dh` and `m`, so `J` depends on the Haar measure of `G/A_G` only.

## Contents
* `CosetSpace ι` (a `def`, see the note below), `CosetSpace.mk`, `CosetSpace.out`,
  `CosetSpace.ind`, its quotient topology and Borel σ-algebra;
* `IsWeilMeasure ι ν μ m`;
* `integral_fibre_eq_of_rel`, `integral_fibre_out_mk`: the fibre integral `∫_S φ(ι(s)γ) dμ(s)`
  does not depend on the representative `γ` of the coset (right invariance of `μ`);
* `IsWeilMeasure.smul_left`, `IsWeilMeasure.smul_right`: rescaling `ν` by `c` rescales `m` by
  `c`; rescaling `μ` by `c` rescales `m` by `c⁻¹`;
* `IsWeilMeasure.integral_complex`: the formula for `ℂ`-valued `φ ∈ C_c(Γ)`;
* `isWeilMeasure_of_subsingleton` (sanity): for trivial `S` the Weil measure is the pushforward
  of `ν`;
* **axiom** `weil_quotient` (existence and uniqueness; Bourbaki, Folland), and its corollary
  `IsWeilMeasure.unique`;
* `CosetSpace.exists_isCompact_image_superset` (compact sets lift) and
  `IsWeilMeasure.isFiniteMeasureOnCompacts` (a Weil measure is finite on compacts, proved from
  the defining formula).

## Why `CosetSpace` is a `def` and not an `abbrev`
Mathlib has a global instance `Quotient.instMeasurableSpace` giving `Quotient s` the pushforward
σ-algebra `{A | mk⁻¹ A measurable}`. Through an `abbrev`, instance search would pick that one,
not the Borel σ-algebra of the quotient topology; `BorelSpace` would then not be available. As a
`def`, `CosetSpace ι` carries the Borel σ-algebra by the instances below. Use `CosetSpace.mk`,
`CosetSpace.out` (= `Quotient.out`) and `CosetSpace.ind` rather than the raw `Quotient` API.

## Why only continuous compactly supported `φ`
For a general Borel `φ` the fibre function `q ↦ ∫_S φ(ι(s) q)` need not be Borel on the
quotient; in Lean a Bochner integral of a non-measurable function is `0`, so the
formula for all measurable `φ` can be false. `C_c` functions are what the sources prove the
formula for, and they separate Radon measures, so uniqueness is unaffected.
-/

open MeasureTheory Topology

open scoped ENNReal Pointwise

noncomputable section

namespace GSpinGGP

section CosetSpace

variable {S Γ : Type*} [Group S] [Group Γ]

/-- The space `ι(S)\Γ` of right cosets `ι(S)γ` of the image of `ι : S →* Γ` (for
`ι : H/A_{G,H} → G/A_G` it is `H(F)\G(F)/A_G(F)` of Thesis §7.1).
Two elements `x, y` are related iff `y x⁻¹ ∈ ι(S)` (`QuotientGroup.rightRel`).

A `def` rather than an `abbrev`: see the module docstring. -/
def CosetSpace (ι : S →* Γ) : Type _ := Quotient (QuotientGroup.rightRel ι.range)

namespace CosetSpace

variable (ι : S →* Γ)

/-- The projection `Γ → ι(S)\Γ`. -/
def mk : Γ → CosetSpace ι := Quotient.mk _

/-- The quotient topology. -/
instance instTopologicalSpace [TopologicalSpace Γ] : TopologicalSpace (CosetSpace ι) :=
  instTopologicalSpaceQuotient

/-- The Borel σ-algebra of the quotient topology (not Mathlib's pushforward σ-algebra on a
quotient; see the module docstring). -/
instance instMeasurableSpace [TopologicalSpace Γ] : MeasurableSpace (CosetSpace ι) := borel _

instance instBorelSpace [TopologicalSpace Γ] : BorelSpace (CosetSpace ι) := ⟨rfl⟩

theorem continuous_mk [TopologicalSpace Γ] : Continuous (mk ι) := continuous_quot_mk

theorem measurable_mk [TopologicalSpace Γ] [MeasurableSpace Γ] [OpensMeasurableSpace Γ] :
    Measurable (mk ι) := (continuous_mk ι).measurable

/-- A chosen representative of a coset (`Quotient.out`). Use this rather than `Quotient.out`
directly: since `CosetSpace` is a `def`, `CosetSpace.out ι q` for `q : CosetSpace ι` elaborates but is
not type-correct at reducible transparency, which can break `rw`/`simp`. -/
def out (q : CosetSpace ι) : Γ := Quotient.out (s := QuotientGroup.rightRel ι.range) q

@[simp] theorem mk_out (q : CosetSpace ι) : mk ι (out ι q) = q := Quotient.out_eq q

theorem out_eq_quotient_out (q : CosetSpace ι) :
    out ι q = Quotient.out (s := QuotientGroup.rightRel ι.range) q := rfl

/-- `out (mk γ)` is in the same coset as `γ`. -/
theorem rel_out_mk (γ : Γ) : QuotientGroup.rightRel ι.range (out ι (mk ι γ)) γ :=
  Quotient.mk_out (s := QuotientGroup.rightRel ι.range) γ

theorem mk_eq_mk_iff (x y : Γ) : mk ι x = mk ι y ↔ QuotientGroup.rightRel ι.range x y :=
  Quotient.eq (r := QuotientGroup.rightRel ι.range)

/-- Induction principle: a property of cosets holds if it holds on every `mk γ`. -/
@[elab_as_elim]
theorem ind {P : CosetSpace ι → Prop} (h : ∀ γ, P (mk ι γ)) (q : CosetSpace ι) : P q :=
  Quotient.ind h q

/-- Elements in the same coset differ by an element of `ι(S)` on the left. -/
theorem rel_iff (x y : Γ) :
    QuotientGroup.rightRel ι.range x y ↔ ∃ s : S, y = ι s * x := by
  rw [QuotientGroup.rightRel_apply]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, by rw [hs, inv_mul_cancel_right]⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, by rw [mul_inv_cancel_right]⟩

/-- The representative `out (mk γ)` lies in the coset `ι(S)γ`. -/
theorem exists_out_mk (γ : Γ) : ∃ s : S, γ = ι s * out ι (mk ι γ) :=
  (rel_iff ι _ _).1 (rel_out_mk ι γ)

/-- A function on `Γ` is continuous on the quotient (e.g. after composing with `out`) as soon
as its composite with `mk` is continuous (quotient topology). -/
theorem continuous_of_comp_mk [TopologicalSpace Γ] {X : Type*} [TopologicalSpace X]
    {g : CosetSpace ι → X} (hg : Continuous (g ∘ mk ι)) : Continuous g :=
  continuous_coinduced_dom.2 hg

end CosetSpace

end CosetSpace

section Weil

variable {S Γ : Type*} [Group S] [Group Γ]

/-- **Weil measure** on `ι(S)\Γ` for measures `ν` on `Γ` and `μ` on `S` (Bourbaki, *Intégration*
VII §2 no. 6): for every continuous compactly supported `φ : Γ → ℝ`,

  `∫_Γ φ dν = ∫_{ι(S)\Γ} ∫_S φ(ι(s) · out q) dμ(s) dm(q)`.

This is the measure `dγ` on `H(F)\G(F)` used in `J` (Thesis §7.1). Only `C_c`
functions are quantified over; see the module docstring. -/
def IsWeilMeasure [TopologicalSpace Γ] [MeasurableSpace Γ] [MeasurableSpace S]
    (ι : S →* Γ) (ν : Measure Γ) (μ : Measure S) (m : Measure (CosetSpace ι)) : Prop :=
  ∀ φ : Γ → ℝ, Continuous φ → HasCompactSupport φ →
    ∫ g, φ g ∂ν = ∫ q, ∫ s, φ (ι s * CosetSpace.out ι q) ∂μ ∂m

/-- **The fibre integral is independent of the representative**: if `γ' ∈ ι(S)γ` then
`∫_S φ(ι(s)γ') dμ(s) = ∫_S φ(ι(s)γ) dμ(s)`. Needs only right invariance of `μ` (no Haar,
no continuity of `φ`). This is what makes the inner integral of `IsWeilMeasure` (and the kernel
integral in `J`, Thesis §7.1) a function on the coset space. -/
theorem integral_fibre_eq_of_rel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace S] [MeasurableMul S] (ι : S →* Γ) (μ : Measure S) [μ.IsMulRightInvariant]
    (φ : Γ → E) {γ γ' : Γ} (h : QuotientGroup.rightRel ι.range γ γ') :
    ∫ s, φ (ι s * γ') ∂μ = ∫ s, φ (ι s * γ) ∂μ := by
  obtain ⟨s₀, rfl⟩ := (CosetSpace.rel_iff ι γ γ').1 h
  have : (fun s => φ (ι s * (ι s₀ * γ))) = fun s => (fun t => φ (ι t * γ)) (s * s₀) := by
    funext s; simp [mul_assoc]
  rw [this, integral_mul_right_eq_self (fun t => φ (ι t * γ)) s₀]

/-- The fibre integral at the chosen representative `out (mk γ)` equals the one at `γ`. -/
theorem integral_fibre_out_mk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace S] [MeasurableMul S] (ι : S →* Γ) (μ : Measure S) [μ.IsMulRightInvariant]
    (φ : Γ → E) (γ : Γ) :
    ∫ s, φ (ι s * CosetSpace.out ι (CosetSpace.mk ι γ)) ∂μ = ∫ s, φ (ι s * γ) ∂μ := by
  exact (integral_fibre_eq_of_rel ι μ φ (CosetSpace.rel_out_mk ι γ)).symm

variable [TopologicalSpace Γ] [MeasurableSpace Γ] [MeasurableSpace S]
  {ι : S →* Γ} {ν : Measure Γ} {μ : Measure S} {m : Measure (CosetSpace ι)}

/-- Rescaling the Haar measure `ν` on `Γ` by `c` rescales the Weil measure by `c`
(any `c : ℝ≥0∞`, including `0` and `∞`, by Lean's conventions). This
is how `J` scales with the Haar measure of `G/A_G`. -/
theorem IsWeilMeasure.smul_left (h : IsWeilMeasure ι ν μ m) (c : ℝ≥0∞) :
    IsWeilMeasure ι (c • ν) μ (c • m) := by
  intro φ hφ hφc
  rw [integral_smul_measure, integral_smul_measure, h φ hφ hφc]

/-- Rescaling the Haar measure `μ` on `S` by `c ∈ (0, ∞)` rescales the Weil measure by `c⁻¹`
(so the Haar measure of `H/A_{G,H}` cancels in `J`). The hypotheses `c ≠ 0`,
`c ≠ ∞` are necessary: for `c = 0` the right-hand side vanishes identically. -/
theorem IsWeilMeasure.smul_right (h : IsWeilMeasure ι ν μ m) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : c ≠ ∞) : IsWeilMeasure ι ν (c • μ) (c⁻¹ • m) := by
  intro φ hφ hφc
  have hc' : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hc0, hc⟩
  simp_rw [integral_smul_measure, smul_eq_mul, integral_const_mul, ENNReal.toReal_inv]
  rw [h φ hφ hφc, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]

/-- The Weil formula for complex-valued `φ ∈ C_c(Γ)` (real and imaginary parts). The kernels in
`J` and in the orbital pairing are complex-valued (Thesis §7.1). Needs `ν` finite on compacts and
integrability of the fibre integrals (true in the situation of `weil_quotient`, where the fibre
function is in `C_c(ι(S)\Γ)`, but not part of `IsWeilMeasure`). -/
theorem IsWeilMeasure.integral_complex [OpensMeasurableSpace Γ] [IsFiniteMeasureOnCompacts ν]
    (h : IsWeilMeasure ι ν μ m) (φ : Γ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hfib : ∀ q : CosetSpace ι, Integrable (fun s => φ (ι s * CosetSpace.out ι q)) μ)
    (hF : Integrable (fun q : CosetSpace ι => ∫ s, φ (ι s * CosetSpace.out ι q) ∂μ) m) :
    ∫ g, φ g ∂ν = ∫ q, ∫ s, φ (ι s * CosetSpace.out ι q) ∂μ ∂m := by
  have hint : Integrable φ ν := hφ.integrable_of_hasCompactSupport hφc
  have h1 := h (fun g => (φ g).re) (Complex.continuous_re.comp hφ) (hφc.comp_left Complex.zero_re)
  have h2 := h (fun g => (φ g).im) (Complex.continuous_im.comp hφ) (hφc.comp_left Complex.zero_im)
  apply Complex.ext
  · have a := integral_re hint
    have b := integral_re hF
    simp only [RCLike.re_to_complex] at a b
    rw [← a, h1, ← b]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    have c := integral_re (hfib q)
    simp only [RCLike.re_to_complex] at c
    exact c
  · have a := integral_im hint
    have b := integral_im hF
    simp only [RCLike.im_to_complex] at a b
    rw [← a, h2, ← b]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    have c := integral_im (hfib q)
    simp only [RCLike.im_to_complex] at c
    exact c

end Weil

section Sanity

variable {S Γ : Type*} [Group S] [Group Γ] [TopologicalSpace Γ] [MeasurableSpace Γ]
  [OpensMeasurableSpace Γ] [MeasurableSpace S]

/-- **Sanity check**: when `S` is trivial, the Weil measure for
`μ = δ_1` is the pushforward of `ν` to `ι(S)\Γ = Γ`. -/
theorem isWeilMeasure_of_subsingleton [Subsingleton S] (ι : S →* Γ) (ν : Measure Γ) :
    IsWeilMeasure ι ν (Measure.dirac 1) (ν.map (CosetSpace.mk ι)) := by
  intro φ hφ _
  -- the relation is equality, so `out ∘ mk = id`
  have hout : ∀ g : Γ, CosetSpace.out ι (CosetSpace.mk ι g) = g := by
    intro g
    obtain ⟨s, hs⟩ := CosetSpace.exists_out_mk ι g
    rw [Subsingleton.elim s 1, map_one, one_mul] at hs
    exact hs.symm
  have hinner : ∀ q : CosetSpace ι,
      ∫ s, φ (ι s * CosetSpace.out ι q) ∂(Measure.dirac (1 : S)) = φ (CosetSpace.out ι q) := by
    intro q
    rw [integral_dirac' _ _ (stronglyMeasurable_const' fun a b => by rw [Subsingleton.elim a b])]
    simp
  simp_rw [hinner]
  have hcont : Continuous (fun q : CosetSpace ι => φ (CosetSpace.out ι q)) := by
    refine CosetSpace.continuous_of_comp_mk ι ?_
    have : ((fun q : CosetSpace ι => φ (CosetSpace.out ι q)) ∘ CosetSpace.mk ι) = φ := by
      funext g; simp [hout]
    rw [this]; exact hφ
  rw [integral_map (CosetSpace.measurable_mk ι).aemeasurable hcont.aestronglyMeasurable]
  simp [hout]

end Sanity

/-- **Weil's quotient-measure formula** (Bourbaki, *Intégration* VII §2 no. 6,
Thm 3, number unverified; Folland, *A Course in Abstract Harmonic Analysis*, Thm 2.49, number
unverified — Folland states it for left cosets `Γ/S` and left Haar measures, the right-coset form
here is the same theorem applied to `γ ↦ γ⁻¹`).

Let `Γ` and `S` be locally compact, Hausdorff, second countable topological groups with their
Borel σ-algebras, `ι : S → Γ` a continuous homomorphism that is a closed embedding, and `ν`, `μ`
Haar measures on `Γ`, `S` that are also right invariant (`Γ` and `S` unimodular). Then there is
a unique measure `m` on `ι(S)\Γ` with
`∫_Γ φ dν = ∫_{ι(S)\Γ} ∫_S φ(ι(s) q) dμ(s) dm(q)` for all `φ ∈ C_c(Γ)`.

Unimodularity of both groups is stronger than the sources need (`Δ_Γ|_S = Δ_S`) but is what is
used: `Γ = G(F)/A_G(F)` and `S = H(F)/A_{G,H}(F)` (Thesis §7.1).

Uniqueness is over *all* measures on the Borel σ-algebra: any `m'` satisfying the formula
integrates every nonnegative `C_c` function on the quotient (each is a fibre integral, Bourbaki
loc. cit. no. 2, number unverified) to the same finite value as `m`, hence is finite on compacts, hence Radon
(second countability), hence equal to `m` by the Riesz uniqueness theorem. -/
axiom weil_quotient {S Γ : Type*}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ] [T2Space Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]
    [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S] [T2Space S]
    [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]
    (ι : S →* Γ) (hι : Continuous ι) (hemb : IsClosedEmbedding ι)
    (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (μ : Measure S) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    ∃! m : Measure (CosetSpace ι), IsWeilMeasure ι ν μ m


/-- Uniqueness of the Weil measure, in the form used to compare two candidates (from
`weil_quotient`). -/
theorem IsWeilMeasure.unique {S Γ : Type*}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ] [T2Space Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]
    [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S] [T2Space S]
    [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]
    {ι : S →* Γ} (hι : Continuous ι) (hemb : IsClosedEmbedding ι)
    {ν : Measure Γ} [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    {μ : Measure S} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    {m m' : Measure (CosetSpace ι)} (h : IsWeilMeasure ι ν μ m) (h' : IsWeilMeasure ι ν μ m') :
    m = m' :=
  (weil_quotient ι hι hemb ν μ).unique h h'

/-- Compact subsets of `ι(S)\Γ` lift to compact subsets of `Γ` (the projection is open and `Γ`
is locally compact). -/
theorem CosetSpace.exists_isCompact_image_superset {S Γ : Type*} [Group S] [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ] (ι : S →* Γ)
    {K : Set (CosetSpace ι)} (hK : IsCompact K) :
    ∃ K' : Set Γ, IsCompact K' ∧ K ⊆ CosetSpace.mk ι '' K' := by
  have hopen : IsOpenMap (CosetSpace.mk ι) := by
    have := isOpenMap_quotient_mk'_mul (Γ := ι.range) (T := Γ)
    exact this
  choose N hNc hN using fun q : CosetSpace ι => exists_compact_mem_nhds (CosetSpace.out ι q)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun q => CosetSpace.mk ι '' interior (N q))
    (fun q => hopen _ isOpen_interior) fun q _ => Set.mem_iUnion.2
      ⟨q, CosetSpace.out ι q, mem_interior_iff_mem_nhds.2 (hN q), CosetSpace.mk_out ι q⟩
  refine ⟨⋃ q ∈ t, N q, t.isCompact_biUnion fun q _ => hNc q, fun q hq => ?_⟩
  obtain ⟨q', hq', γ, hγ, rfl⟩ : ∃ q' ∈ t, q ∈ CosetSpace.mk ι '' interior (N q') := by
    simpa using ht hq
  exact ⟨γ, Set.mem_biUnion hq' (interior_subset hγ), rfl⟩

/-- **A Weil measure is finite on compact sets**.
Proved from the defining formula alone, so `weil_quotient` need not be strengthened.
For compact `K ⊆ ι(S)\Γ`, lift it to a compact `K' ⊆ Γ`, take `φ ∈ C_c(Γ)`, `0 ≤ φ ≤ 1`, with
`φ = 1` on `V K'` for a compact neighbourhood `V` of `1`.  Its fibre integral `F` is `≥ μ(ι⁻¹ V°) > 0`
on `K`, and `∫ F dm = ∫ φ dν > 0` forces `F` to be `m`-integrable (a non-integrable function has
Bochner integral `0`), so `m K ≤ m {F ≥ c} < ∞` (Markov).  Only the openness-positivity and
local finiteness of the Haar measures and the right invariance of `μ` are used. -/
theorem IsWeilMeasure.isFiniteMeasureOnCompacts {S Γ : Type*}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ] [T2Space Γ]
    [MeasurableSpace Γ] [BorelSpace Γ]
    [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [MeasurableSpace S] [BorelSpace S]
    {ι : S →* Γ} (hι : Continuous ι) (hemb : IsClosedEmbedding ι)
    {ν : Measure Γ} [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν]
    {μ : Measure S} [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant]
    {m : Measure (CosetSpace ι)} (h : IsWeilMeasure ι ν μ m) :
    IsFiniteMeasureOnCompacts m := by
  refine ⟨fun K hK => ?_⟩
  rcases K.eq_empty_or_nonempty with rfl | ⟨q₀, hq₀⟩
  · simp
  obtain ⟨K', hK'c, hKK'⟩ := CosetSpace.exists_isCompact_image_superset ι hK
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : Γ)
  have hL : IsCompact (V * K') := hVc.mul hK'c
  obtain ⟨φ, hφ1, -, hφc, hφ01⟩ :=
    exists_continuous_one_zero_of_isCompact hL isClosed_empty (Set.disjoint_empty _)
  -- the open set `U = ι⁻¹(int V)` of `S` has positive finite measure
  set U : Set S := ι ⁻¹' interior V
  have hUo : IsOpen U := isOpen_interior.preimage hι
  have hU1 : (1 : S) ∈ U := by
    show ι 1 ∈ interior V
    rw [map_one]; exact mem_interior_iff_mem_nhds.2 hV1
  have hUpos : 0 < μ U := hUo.measure_pos μ ⟨1, hU1⟩
  have hUfin : μ U < ∞ :=
    ((hemb.isCompact_preimage hVc).measure_lt_top).trans_le' (measure_mono
      (Set.preimage_mono interior_subset))
  set c : ℝ := (μ U).toReal
  have hc : 0 < c := ENNReal.toReal_pos hUpos.ne' hUfin.ne
  -- the fibre integral of `φ` is `≥ c` on `mk(K') ⊇ K`
  set Fq : CosetSpace ι → ℝ := fun q => ∫ s, φ (ι s * CosetSpace.out ι q) ∂μ
  have hfib : ∀ γ ∈ K', c ≤ Fq (CosetSpace.mk ι γ) := by
    intro γ hγ
    have hemb' : IsClosedEmbedding (fun s : S => ι s * γ) :=
      (Homeomorph.mulRight γ).isClosedEmbedding.comp hemb
    have hint : Integrable (fun s => φ (ι s * γ)) μ :=
      (φ.continuous.comp hemb'.continuous).integrable_of_hasCompactSupport
        (hφc.comp_isClosedEmbedding hemb')
    show c ≤ ∫ s, φ (ι s * CosetSpace.out ι (CosetSpace.mk ι γ)) ∂μ
    rw [integral_fibre_out_mk ι μ (fun x => φ x) γ]
    calc c = ∫ s in U, (1 : ℝ) ∂μ := by simp [c, Measure.real]
      _ = ∫ s in U, φ (ι s * γ) ∂μ := by
          refine setIntegral_congr_fun hUo.measurableSet fun s hs => ?_
          exact (hφ1 ⟨ι s, interior_subset hs, γ, hγ, rfl⟩).symm
      _ ≤ ∫ s, φ (ι s * γ) ∂μ :=
          setIntegral_le_integral hint (Filter.Eventually.of_forall fun s => (hφ01 _).1)
  -- the Weil formula forces the fibre integral to be `m`-integrable
  have hγ₀ : ∃ γ ∈ K', True := by
    obtain ⟨γ, hγ, -⟩ := hKK' hq₀; exact ⟨γ, hγ, trivial⟩
  obtain ⟨γ₀, hγ₀, -⟩ := hγ₀
  have hpos : 0 < ∫ x, φ x ∂ν := by
    refine φ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hφc
      (fun x => (hφ01 x).1) (x := γ₀) ?_
    rw [hφ1 ⟨1, mem_of_mem_nhds hV1, γ₀, hγ₀, one_mul γ₀⟩]; exact one_ne_zero
  have hF : Integrable Fq m := by
    refine Integrable.of_integral_ne_zero ?_
    rw [← h φ φ.continuous hφc]; exact hpos.ne'
  calc m K ≤ m {q | c ≤ Fq q} := measure_mono fun q hq => by
        obtain ⟨γ, hγ, rfl⟩ := hKK' hq
        exact hfib γ hγ
    _ < ∞ := hF.measure_ge_lt_top hc

end GSpinGGP
