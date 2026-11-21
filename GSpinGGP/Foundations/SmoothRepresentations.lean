/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.Representations
import TauCeti.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.Tensor.External

/-!
# Smooth admissible representations, and the smooth part of a unitary representation

The results of Harish-Chandra, Beuzart-Plessis and Emory–Takeda / Pan Yan that the proof cites
are stated in their sources for irreducible *admissible smooth* representations: linear
representations `ρ : Representation ℂ G V` on a vector space without topology. This file gives
the notions those statements need, for an arbitrary topological group `G`, and relates them to
a unitary representation `π` through its smooth part `π^∞` (Tau Ceti's
`Representation.smoothVectors` of `π.toRepresentation`).

## Main definitions

* `Representation.IsAdmissible`: smooth, with `V^K` finite-dimensional for every compact open
  subgroup `K`.
* `Representation.heckeOp ρ f K = μ(K) ∑_{gK ∈ G/K} f(g) ρ(g)`: the operator `ρ(f) = ∫ f(g) ρ(g) dg`
  on `V^K` when `f` is right `K`-invariant with compact support (a finite sum, since `ρ` has no
  topology).
* `Representation.traceOf`, `Representation.IsCharacterOf`, `Representation.characterOn`: the
  distribution character `f ↦ tr ρ(f)` and a function representing it, defined as for unitary
  representations (`GSpinGGP.traceOf` …).
* `Representation.equivariantForms`, `Representation.multiplicity`: `Hom_S(ρ, ξ)` and its
  dimension.
* `GSpinGGP.smoothRep π`: the smooth representation of `G` on `π^∞`.

## Main results

* `GSpinGGP.integral_eq_smul_finsum_quotient`: for `K` compact open and `F` right `K`-invariant with
  compact support, `∫_G F = μ(K) ∑_{gK} F(g)`.
* `GSpinGGP.traceOf_smoothRep`, `GSpinGGP.isCharacterOf_smoothRep`,
  `GSpinGGP.characterOn_smoothRep`: the trace and character of `π^∞` are those of `π`.
* `GSpinGGP.multiplicity_smoothRep`: `m(π)` is the multiplicity of `π^∞` (by definition).
* `GSpinGGP.isIrreducible_smoothRep`: if `π` is irreducible, `π^∞` is dense and the spaces `π^K`
  are finite-dimensional, then `π^∞` is an irreducible representation. Proof: a nonzero
  `G`-stable `W ⊆ π^∞` is dense; `e_K = π(1_K)` maps `W` into `W ∩ π^K`, which is
  finite-dimensional, hence closed, so `μ(K) π^K = e_K(π^K) ⊆ e_K(closure W) ⊆ W ∩ π^K`.
-/

open MeasureTheory Topology
open scoped Pointwise

noncomputable section

namespace Representation

section Admissible

variable {k G V : Type*} [Field k] [Group G] [TopologicalSpace G] [AddCommGroup V] [Module k V]

/-- A representation of a topological group is *admissible* if it is smooth and the invariants
`V^K` of every compact open subgroup `K` are finite-dimensional (Flath, *Decomposition of
representations into tensor products*, PSPUM 33 Part 1 (1979), §1; Cartier, *ibid.*, §2.5). -/
def IsAdmissible (ρ : Representation k G V) : Prop :=
  ρ.IsSmooth ∧ ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) →
    FiniteDimensional k ↥(invariants (ρ.comp K.subtype))

end Admissible

section Character

attribute [local instance] Classical.propDecidable

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup V] [Module ℂ V]

/-- The operator `ρ(f) = ∫_G f(g) ρ(g) dg` on `V^K`, for `f` right `K`-invariant with compact
support and `K` compact open: the integrand is constant on each coset `gK`, so the integral is the
finite sum `μ(K) ∑_{gK ∈ G/K} f(g) ρ(g)` (Haar measure `μ`). -/
def heckeOp (ρ : Representation ℂ G V) (f : G → ℂ) (K : Subgroup G) : V →ₗ[ℂ] V :=
  ((Measure.haar : Measure G) (K : Set G)).toReal • ∑ᶠ c : G ⧸ K, f c.out • ρ c.out

/-- The datum used to compute `tr ρ(f)`: a compact open subgroup `K` with `f` bi-`K`-invariant,
`V^K` finite-dimensional, and `ρ(f)` preserving `V^K` (as `GSpinGGP.TraceDatum`). -/
def TraceDatum (ρ : Representation ℂ G V) (f : G → ℂ) (K : Subgroup G) : Prop :=
  IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ GSpinGGP.IsBiInvariant K f ∧
    FiniteDimensional ℂ ↥(invariants (ρ.comp K.subtype)) ∧
    ∀ v ∈ invariants (ρ.comp K.subtype), heckeOp ρ f K v ∈ invariants (ρ.comp K.subtype)

/-- `tr ρ(f)` for an admissible `ρ` and a test function `f`: the trace of `ρ(f)` on `V^K`, for
`f` bi-`K`-invariant (`ρ(f)` has range in `V^K` and kills the other isotypic components of `K`).
Defined by the epsilon pattern (`0` if no such `K` exists), as `GSpinGGP.traceOf`. -/
def traceOf (ρ : Representation ℂ G V) (f : G → ℂ) : ℂ :=
  if h : ∃ K : Subgroup G, TraceDatum ρ f K then
    LinearMap.trace ℂ ↥(invariants (ρ.comp h.choose.subtype))
      ((heckeOp ρ f h.choose).restrict h.choose_spec.2.2.2.2)
  else 0

/-- `θ` is a character of `ρ`: `θ` is locally integrable and `∫_G θ(g) f(g) dg = tr ρ(f)` for every
test function `f` (Harish-Chandra's character `Θ_ρ`, represented by the function `θ`). -/
def IsCharacterOf (ρ : Representation ℂ G V) (θ : G → ℂ) : Prop :=
  LocallyIntegrable θ (Measure.haar : Measure G) ∧
    ∀ f ∈ GSpinGGP.testFunctions G, ∫ g, θ g * f g ∂(Measure.haar : Measure G) = traceOf ρ f

/-- The character `θ_ρ` as a function, normalised to be continuous on `S` (as
`GSpinGGP.characterOn`); `0` if there is no such representative. -/
def characterOn (ρ : Representation ℂ G V) (S : Set G) : G → ℂ :=
  if h : ∃ θ, IsCharacterOf ρ θ ∧ ContinuousOn θ S then h.choose else 0

end Character

section Multiplicity

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

/-- `Hom_S(ρ, ξ)`: linear forms `ℓ` on `V` with `ℓ(ρ(s) v) = ξ(s) ℓ(v)` for `s ∈ S`. -/
def equivariantForms (ρ : Representation ℂ G V) (S : Subgroup G) (ξ : ↥S → ℂ) :
    Submodule ℂ (Module.Dual ℂ V) where
  carrier := {ℓ | ∀ s : ↥S, ∀ v, ℓ (ρ s v) = ξ s * ℓ v}
  zero_mem' := by intro s v; simp
  add_mem' := by
    intro ℓ ℓ' hℓ hℓ' s v
    simp only [LinearMap.add_apply, hℓ s v, hℓ' s v, mul_add]
  smul_mem' := by
    intro c ℓ hℓ s v
    simp only [LinearMap.smul_apply, hℓ s v, smul_eq_mul]
    ring

/-- `dim Hom_S(ρ, ξ)`, valued in `ℕ∞` (`⊤` if infinite-dimensional). -/
def multiplicity (ρ : Representation ℂ G V) (S : Subgroup G) (ξ : ↥S → ℂ) : ℕ∞ :=
  Cardinal.toENat (Module.rank ℂ ↥(equivariantForms ρ S ξ))

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- Multiplicities are invariant under an equivariant linear isomorphism. -/
theorem multiplicity_eq_of_linearEquiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : V ≃ₗ[ℂ] W) (he : ∀ g v, e (ρ g v) = σ g (e v)) (S : Subgroup G) (ξ : ↥S → ℂ) :
    multiplicity ρ S ξ = multiplicity σ S ξ := by
  have hmem : ∀ ℓ, ℓ ∈ equivariantForms ρ S ξ ↔ e.symm.dualMap ℓ ∈ equivariantForms σ S ξ := by
    intro ℓ
    change (∀ s : ↥S, ∀ v, ℓ (ρ s v) = ξ s * ℓ v) ↔
      ∀ s : ↥S, ∀ w, ℓ (e.symm (σ s w)) = ξ s * ℓ (e.symm w)
    constructor
    · intro h s w
      have := h s (e.symm w)
      have hs : e.symm (σ s w) = ρ s (e.symm w) := by
        rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
      rwa [hs]
    · intro h s v
      have := h s (e v)
      rwa [← he, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at this
  have h := congrArg Cardinal.toENat (GSpinGGP.equivOfForallMemIff e.symm.dualMap hmem).lift_rank_eq
  rwa [Cardinal.toENat_lift, Cardinal.toENat_lift] at h

end Multiplicity

end Representation

namespace GSpinGGP

universe u

/-! ## Integrals of functions constant on the cosets of a compact open subgroup -/

section Cosets

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A function with compact support meets only finitely many cosets of an open subgroup. -/
theorem finite_setOf_out_ne_zero {M : Type*} [Zero M] {K : Subgroup G} (hK : IsOpen (K : Set G))
    {F : G → M} (hF : HasCompactSupport F) : {c : G ⧸ K | F c.out ≠ 0}.Finite := by
  have : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  refine (IsCompact.image (f := (QuotientGroup.mk : G → G ⧸ K)) hF
    QuotientGroup.continuous_mk).finite_of_discrete.subset ?_
  intro c hc
  exact ⟨c.out, subset_tsupport F hc, QuotientGroup.out_eq' c⟩

variable [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- **Integration over cosets.** For `K` a compact open subgroup and `F` right `K`-invariant with
compact support, `∫_G F = μ(K) ∑_{gK ∈ G/K} F(g)` (a finite sum). -/
theorem integral_eq_smul_finsum_quotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {K : Subgroup G} (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    {F : G → E} (hF : ∀ g, ∀ k ∈ K, F (g * k) = F g) (hFc : HasCompactSupport F) :
    ∫ g, F g ∂(Measure.haar : Measure G) =
      ((Measure.haar : Measure G) (K : Set G)).toReal • ∑ᶠ c : G ⧸ K, F c.out := by
  classical
  have : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have hs := finite_setOf_out_ne_zero hKo hFc
  set s := hs.toFinset with hs_def
  have hconst : ∀ g, F (QuotientGroup.mk g : G ⧸ K).out = F g := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hh, hF g h h.property]
  have hpre : ∀ c : G ⧸ K, (QuotientGroup.mk ⁻¹' {c} : Set G) = c.out • (K : Set G) := by
    intro c
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rw [eq_comm, QuotientGroup.eq, mem_leftCoset_iff]
    rfl
  have hmeas : ∀ c : G ⧸ K, MeasurableSet (QuotientGroup.mk ⁻¹' {c} : Set G) := fun c =>
    ((isOpen_discrete {c}).preimage QuotientGroup.continuous_mk).measurableSet
  have hμ : ∀ c : G ⧸ K, (Measure.haar : Measure G) (QuotientGroup.mk ⁻¹' {c}) =
      (Measure.haar : Measure G) (K : Set G) := fun c => by
    rw [hpre c, measure_smul]
  have hfin : (Measure.haar : Measure G) (K : Set G) ≠ ⊤ := hKc.measure_lt_top.ne
  have hsum : F = fun g => ∑ c ∈ s,
      (QuotientGroup.mk ⁻¹' {c} : Set G).indicator (fun _ => F c.out) g := by
    funext g
    by_cases hg : QuotientGroup.mk g ∈ s
    · rw [Finset.sum_eq_single (QuotientGroup.mk g)]
      · rw [Set.indicator_of_mem (by simp), hconst]
      · intro c _ hc
        rw [Set.indicator_of_notMem]
        simpa [eq_comm] using hc
      · intro h; exact absurd hg h
    · rw [Finset.sum_eq_zero]
      · have : F (QuotientGroup.mk g : G ⧸ K).out = 0 := by
          by_contra hne
          exact hg (by simpa [s] using hne)
        rw [← hconst g, this]
      · intro c hc
        rw [Set.indicator_of_notMem]
        intro hgc
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hgc
        exact hg (hgc ▸ hc)
  conv_lhs => rw [hsum]
  rw [integral_finsetSum]
  · simp_rw [integral_indicator_const _ (hmeas _), measureReal_def, hμ]
    rw [← Finset.smul_sum, finsum_eq_sum_of_support_subset _ (s := s) (by
      intro c hc; simpa [s] using hc)]
  · intro c _
    exact (integrable_indicator_iff (hmeas c)).2 (integrableOn_const (by rw [hμ]; exact hfin))

end Cosets

/-! ## The smooth part of a unitary representation -/

section SmoothPart

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The smooth representation of `G` on `π^∞` (Thesis Ch. 1): Tau Ceti's subrepresentation of
smooth vectors of `π.toRepresentation`. -/
abbrev smoothRep (π : UnitaryRep G) : Representation ℂ G ↥(smoothVectors π) :=
  π.toRepresentation.smoothVectors.toRepresentation

@[simp]
theorem smoothRep_apply (π : UnitaryRep G) (g : G) (v : ↥(smoothVectors π)) :
    ((smoothRep π g v : ↥(smoothVectors π)) : π.H) = π.ρ g v := rfl

/-- `Hom_S(π^∞, ξ)` is the space of equivariant forms of the smooth representation `π^∞`. -/
theorem equivariantForms_smoothRep (π : UnitaryRep G) (S : Subgroup G) (ξ : ↥S → ℂ) :
    Representation.equivariantForms (smoothRep π) S ξ = equivariantForms π S ξ := rfl

/-- `m(π)` is the multiplicity of the smooth representation `π^∞`. -/
theorem multiplicity_smoothRep (π : UnitaryRep G) (S : Subgroup G) (ξ : ↥S → ℂ) :
    Representation.multiplicity (smoothRep π) S ξ = multiplicity π S ξ := rfl

theorem mem_invariants_smoothRep_iff (π : UnitaryRep G) (K : Subgroup G)
    (v : ↥(smoothVectors π)) :
    v ∈ Representation.invariants ((smoothRep π).comp K.subtype) ↔
      (v : π.H) ∈ fixedSpace π K := by
  rw [Representation.mem_invariants]
  constructor
  · intro h k hk
    exact congrArg Subtype.val (h ⟨k, hk⟩)
  · intro h k
    exact Subtype.ext (h k k.property)

/-- `(π^∞)^K = π^K` for `K` open. -/
def invariantsSmoothEquiv (π : UnitaryRep G) {K : Subgroup G} (hK : IsOpen (K : Set G)) :
    ↥(Representation.invariants ((smoothRep π).comp K.subtype)) ≃ₗ[ℂ] ↥(fixedSpace π K) where
  toFun v := ⟨(v : ↥(smoothVectors π)), (mem_invariants_smoothRep_iff π K v).1 v.property⟩
  invFun u := ⟨⟨u, fixedSpace_le_smoothVectors π hK u.property⟩,
    (mem_invariants_smoothRep_iff π K _).2 u.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_invariantsSmoothEquiv (π : UnitaryRep G) {K : Subgroup G} (hK : IsOpen (K : Set G))
    (v : ↥(Representation.invariants ((smoothRep π).comp K.subtype))) :
    ((invariantsSmoothEquiv π hK v : ↥(fixedSpace π K)) : π.H) =
      ((v : ↥(smoothVectors π)) : π.H) := rfl

variable [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- `ρ(f) v = μ(K) ∑_{gK} f(g) ρ(g) v` when only finitely many cosets carry `f`. -/
theorem heckeOp_apply_of_finite {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (f : G → ℂ) (K : Subgroup G)
    (hs : {c : G ⧸ K | f c.out ≠ 0}.Finite) (v : V) :
    Representation.heckeOp ρ f K v =
      ((Measure.haar : Measure G) (K : Set G)).toReal • ∑ᶠ c : G ⧸ K, f c.out • ρ c.out v := by
  classical
  have h1 : (Function.support fun c : G ⧸ K => f c.out • ρ c.out) ⊆ hs.toFinset := by
    intro c hc
    simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    intro h0
    exact hc (by simp [h0])
  have h2 : (Function.support fun c : G ⧸ K => f c.out • ρ c.out v) ⊆ hs.toFinset := by
    intro c hc
    simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    intro h0
    exact hc (by simp [h0])
  rw [Representation.heckeOp, LinearMap.smul_apply, finsum_eq_sum_of_support_subset _ h1,
    finsum_eq_sum_of_support_subset _ h2, LinearMap.sum_apply]
  rfl

/-- On `π^K`, `π(f)` is the finite coset sum `μ(K) ∑_{gK} f(g) π(g)`, for `f` a test function,
right `K`-invariant, and `K` compact open. -/
theorem opOf_eq_smul_finsum (π : UnitaryRep G) {f : G → ℂ} (hf : f ∈ testFunctions G)
    {K : Subgroup G} (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hfK : ∀ g, ∀ k ∈ K, f (g * k) = f g) {v : π.H} (hv : v ∈ fixedSpace π K) :
    opOf π f v =
      ((Measure.haar : Measure G) (K : Set G)).toReal • ∑ᶠ c : G ⧸ K, f c.out • π.ρ c.out v := by
  rw [opOf_apply π (opIntegrable_of_mem_testFunctions π hf)]
  refine integral_eq_smul_finsum_quotient hKo hKc (fun g k hk => ?_) hf.2.smul_right
  rw [hfK g k hk, map_mul]
  change f g • π.ρ g (π.ρ k v) = _
  rw [hv k hk]

/-- On `(π^∞)^K = π^K`, the operator `ρ(f)` of the smooth representation `π^∞` is `π(f)`. -/
theorem coe_heckeOp_smoothRep (π : UnitaryRep G) {f : G → ℂ} (hf : f ∈ testFunctions G)
    {K : Subgroup G} (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hfK : IsBiInvariant K f) (v : ↥(smoothVectors π))
    (hv : (v : π.H) ∈ fixedSpace π K) :
    ((Representation.heckeOp (smoothRep π) f K v : ↥(smoothVectors π)) : π.H) =
      opOf π f v := by
  have hs := finite_setOf_out_ne_zero (K := K) hKo hf.2
  classical
  rw [heckeOp_apply_of_finite _ f K hs, opOf_eq_smul_finsum π hf hKo hKc
    (fun g k hk => (hfK k hk g).2) hv]
  have h2 : (Function.support fun c : G ⧸ K => f c.out • smoothRep π c.out v) ⊆ hs.toFinset := by
    intro c hc
    simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    intro h0
    exact hc (by simp [h0])
  have h3 : (Function.support fun c : G ⧸ K => f c.out • π.ρ c.out (v : π.H)) ⊆ hs.toFinset := by
    intro c hc
    simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    intro h0
    exact hc (by simp [h0])
  rw [finsum_eq_sum_of_support_subset _ h2, finsum_eq_sum_of_support_subset _ h3]
  simp only [Submodule.coe_smul_of_tower, Submodule.coe_sum]
  rfl

/-- **The trace of `π^∞` is the trace of `π`**: `tr π^∞(f) = tr π(f)` for every test function. -/
theorem traceOf_smoothRep (π : UnitaryRep G) {f : G → ℂ} (hf : f ∈ testFunctions G) :
    Representation.traceOf (smoothRep π) f = traceOf π f := by
  classical
  unfold Representation.traceOf
  split_ifs with h
  · set K := h.choose
    have hK : Representation.TraceDatum (smoothRep π) f K := h.choose_spec
    set e := invariantsSmoothEquiv π hK.1
    have hfd : FiniteDimensional ℂ ↥(fixedSpace π K) := by
      have := hK.2.2.2.1
      exact e.finiteDimensional
    have hK' : TraceDatum π f K :=
      ⟨hK.1, hK.2.1, hK.2.2.1, hfd, fun v hv => opOf_mem_fixedSpace π hf hK.2.2.1 hv⟩
    rw [traceOf_eq π f K hK', ← LinearMap.trace_conj' _ e]
    congr 1
    ext u
    simp only [LinearEquiv.conj_apply_apply, LinearMap.restrict_apply, ContinuousLinearMap.coe_coe]
    change ((Representation.heckeOp (smoothRep π) f K ((e.symm u : _) : ↥(smoothVectors π)) :
      ↥(smoothVectors π)) : π.H) = _
    rw [coe_heckeOp_smoothRep π hf hK.1 hK.2.1 hK.2.2.1 _ ((e.symm u).property |>
      (mem_invariants_smoothRep_iff π K _).1)]
    rfl
  · symm
    unfold traceOf
    split_ifs with h'
    swap
    · rfl
    exfalso
    obtain ⟨K, hK⟩ := h'
    apply h
    set e := invariantsSmoothEquiv π hK.1
    refine ⟨K, hK.1, hK.2.1, hK.2.2.1, ?_, fun v hv => ?_⟩
    · have := hK.2.2.2.1
      exact e.symm.finiteDimensional
    · rw [mem_invariants_smoothRep_iff] at hv ⊢
      rw [coe_heckeOp_smoothRep π hf hK.1 hK.2.1 hK.2.2.1 _ hv]
      exact hK.2.2.2.2 _ hv

/-- A function is a character of `π^∞` iff it is a character of `π`. -/
theorem isCharacterOf_smoothRep (π : UnitaryRep G) :
    Representation.IsCharacterOf (smoothRep π) = IsCharacterOf π := by
  funext θ
  apply propext
  unfold Representation.IsCharacterOf IsCharacterOf
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun f hf => (h2 f hf).trans (traceOf_smoothRep π hf)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun f hf => (h2 f hf).trans (traceOf_smoothRep π hf).symm⟩

/-- `θ_{π^∞} = θ_π` (same normalisation on `S`). -/
theorem characterOn_smoothRep (π : UnitaryRep G) (S : Set G) :
    Representation.characterOn (smoothRep π) S = characterOn π S := by
  unfold Representation.characterOn characterOn
  rw [isCharacterOf_smoothRep]

/-! ### Irreducibility of `π^∞` -/

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- A nonzero `G`-stable subspace of an irreducible unitary representation is dense. -/
theorem dense_of_invariant (π : UnitaryRep G) (hπ : π.IsIrreducible) {W : Submodule ℂ π.H}
    (hWg : ∀ g, ∀ w ∈ W, π.ρ g w ∈ W) (hW0 : W ≠ ⊥) : Dense (W : Set π.H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  refine (hπ.2 W.topologicalClosure W.isClosed_topologicalClosure (fun g w hw => ?_)).resolve_left
    fun h => hW0 (eq_bot_iff.2 (h ▸ W.le_topologicalClosure))
  have hle : W ≤ W.topologicalClosure.comap (π.ρ g).toLinearMap := fun x hx =>
    W.le_topologicalClosure (hWg g x hx)
  have hcl : IsClosed ((W.topologicalClosure.comap (π.ρ g).toLinearMap : Submodule ℂ π.H) :
      Set π.H) := W.isClosed_topologicalClosure.preimage (π.ρ g).continuous
  exact Submodule.topologicalClosure_minimal W hle hcl hw

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G]
  [BorelSpace G] in
theorem indicator_subgroup_mul_right {K : Subgroup G} {k : G} (hk : k ∈ K) (g : G) :
    (K : Set G).indicator (1 : G → ℂ) (g * k) = (K : Set G).indicator 1 g := by
  by_cases hg : g ∈ K
  · rw [Set.indicator_of_mem (show g * k ∈ (K : Set G) from K.mul_mem hg hk),
      Set.indicator_of_mem (show g ∈ (K : Set G) from hg)]
    rfl
  · rw [Set.indicator_of_notMem (show g * k ∉ (K : Set G) from
      fun h => hg ((K.mul_mem_cancel_right hk).1 h)),
      Set.indicator_of_notMem (show g ∉ (K : Set G) from hg)]

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G]
  [BorelSpace G] in
theorem indicator_subgroup_mul_left {K : Subgroup G} {k : G} (hk : k ∈ K) (g : G) :
    (K : Set G).indicator (1 : G → ℂ) (k * g) = (K : Set G).indicator 1 g := by
  by_cases hg : g ∈ K
  · rw [Set.indicator_of_mem (show k * g ∈ (K : Set G) from K.mul_mem hk hg),
      Set.indicator_of_mem (show g ∈ (K : Set G) from hg)]
    rfl
  · rw [Set.indicator_of_notMem (show k * g ∉ (K : Set G) from
      fun h => hg ((K.mul_mem_cancel_left hk).1 h)),
      Set.indicator_of_notMem (show g ∉ (K : Set G) from hg)]

variable [T2Space G]

/-- `e_K = π(1_K)` maps `π^∞ ∩ W` into `W`, for `W` a `G`-stable subspace: on a vector fixed by an
open `U`, the integral over `K` is a finite sum over `K/(K ∩ U)`. -/
theorem opOf_indicator_mem (π : UnitaryRep G) {K : Subgroup G} (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) {W : Submodule ℂ π.H} (hWg : ∀ g, ∀ w ∈ W, π.ρ g w ∈ W)
    {w : π.H} (hw : w ∈ W) (hws : w ∈ smoothVectors π) :
    opOf π ((K : Set G).indicator 1) w ∈ W := by
  obtain ⟨U, hUo, hU⟩ := (mem_smoothVectors_iff π).1 hws
  have hK0o : IsOpen ((K ⊓ U : Subgroup G) : Set G) := hKo.inter hUo
  have hK0c : IsCompact ((K ⊓ U : Subgroup G) : Set G) :=
    hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hK0o) inf_le_left
  have hfK : (K : Set G).indicator (1 : G → ℂ) ∈ testFunctions G :=
    indicator_mem_testFunctions hKc ⟨Subgroup.isClosed_of_isOpen _ hKo, hKo⟩
  rw [opOf_apply π (opIntegrable_of_mem_testFunctions π hfK),
    integral_eq_smul_finsum_quotient (F := fun g => (K : Set G).indicator (1 : G → ℂ) g • π.ρ g w)
      hK0o hK0c (fun g k hk => ?_) hfK.2.smul_right]
  · refine W.smul_mem _ (finsum_induction _ W.zero_mem (fun _ _ => W.add_mem) fun c => ?_)
    exact W.smul_mem _ (hWg _ _ hw)
  · have hkK : k ∈ K := hk.1
    have hkU : k ∈ U := hk.2
    change (K : Set G).indicator 1 (g * k) • π.ρ (g * k) w = _
    rw [indicator_subgroup_mul_right hkK, map_mul]
    change _ • π.ρ g (π.ρ k w) = _
    rw [hU k hkU]

/-- **`π^∞` is irreducible.** Let `π` be an irreducible unitary representation whose smooth
vectors are dense and whose spaces `π^K` (`K` compact open) are finite-dimensional, and suppose
compact open subgroups form a basis of neighbourhoods of `1`. Then the smooth representation `π^∞`
is (algebraically) irreducible. -/
theorem isIrreducible_smoothRep
    (hG : ∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G,
      IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {π : UnitaryRep G} (hπ : π.IsIrreducible) (hdense : Dense (smoothVectors π : Set π.H))
    (hadm : ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) →
      FiniteDimensional ℂ ↥(fixedSpace π K)) :
    (smoothRep π).IsIrreducible := by
  -- The key step: a nonzero `G`-stable `W ⊆ π^∞` contains `π^∞`.
  have key : ∀ W : Submodule ℂ π.H, W ≤ smoothVectors π → (∀ g, ∀ w ∈ W, π.ρ g w ∈ W) →
      W ≠ ⊥ → smoothVectors π ≤ W := by
    intro W hWs hWg hW0 v hv
    have hWd := dense_of_invariant π hπ hWg hW0
    obtain ⟨U, hUo, hU⟩ := (mem_smoothVectors_iff π).1 hv
    obtain ⟨K, hKo, hKc, hKU⟩ := hG U (hUo.mem_nhds U.one_mem)
    have := hadm K hKo hKc
    have hfK : (K : Set G).indicator (1 : G → ℂ) ∈ testFunctions G :=
      indicator_mem_testFunctions hKc ⟨Subgroup.isClosed_of_isOpen _ hKo, hKo⟩
    set e := opOf π ((K : Set G).indicator 1)
    have he_fix : ∀ x, e x ∈ fixedSpace π K := fun x k hk =>
      rho_opOf_of_leftInvariant π (fun k hk g => indicator_subgroup_mul_left hk g) hk x
    have he_id : ∀ u ∈ fixedSpace π K,
        e u = ((Measure.haar : Measure G) (K : Set G)).toReal • u := by
      intro u hu
      rw [opOf_apply π (opIntegrable_of_mem_testFunctions π hfK)]
      have : (fun g => (K : Set G).indicator (1 : G → ℂ) g • π.ρ g u) =
          (K : Set G).indicator (fun _ => u) := by
        funext g
        by_cases hg : g ∈ (K : Set G)
        · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, Pi.one_apply, one_smul,
            hu g hg]
        · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_smul]
      rw [this, integral_indicator_const _ hKo.measurableSet, measureReal_def]
    set S := W ⊓ fixedSpace π K
    have hS : IsClosed (S : Set π.H) := Submodule.isClosed_of_finiteDimensional S
    have hrange : ∀ x, e x ∈ S := by
      intro x
      have hx : x ∈ closure (W : Set π.H) := hWd x
      have := image_closure_subset_closure_image (f := e) e.continuous ⟨x, hx, rfl⟩
      refine (closure_minimal ?_ hS) this
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨opOf_indicator_mem π hKo hKc hWg hw (hWs hw), he_fix w⟩
    have hvK : v ∈ fixedSpace π K := fun k hk => hU k (hKU hk)
    have hpos : ((Measure.haar : Measure G) (K : Set G)).toReal ≠ 0 :=
      (ENNReal.toReal_pos (hKo.measure_pos _ ⟨1, K.one_mem⟩).ne' hKc.measure_lt_top.ne).ne'
    have : v = ((Measure.haar : Measure G) (K : Set G)).toReal⁻¹ • e v := by
      rw [he_id v hvK, smul_smul, inv_mul_cancel₀ hpos, one_smul]
    rw [this]
    exact W.smul_mem _ (hrange v).1
  apply Representation.isIrreducible_toRepresentation_of_isAtom
  refine ⟨fun h => ?_, fun τ hτ => ?_⟩
  · -- `π^∞ ≠ 0`: it is dense in `H ≠ 0`.
    have h0 : smoothVectors π = ⊥ := congrArg Subrepresentation.toSubmodule h
    have := hπ.1
    obtain ⟨x, hx⟩ := exists_ne (0 : π.H)
    have : x ∈ closure (smoothVectors π : Set π.H) := hdense x
    rw [h0, Submodule.bot_coe, closure_singleton] at this
    exact hx this
  · by_contra hne
    have hle : τ.toSubmodule ≤ smoothVectors π := hτ.le
    have h1 := key τ.toSubmodule hle (fun g w hw => τ.apply_mem_toSubmodule g hw)
      (fun h0 => hne (Subrepresentation.toSubmodule_injective (by rw [h0]; rfl)))
    exact hτ.not_ge h1

end SmoothPart

end GSpinGGP
