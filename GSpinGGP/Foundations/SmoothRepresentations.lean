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
* (`GSpinGGP.smoothRep π`, the smooth representation of `G` on `π^∞`, is in
  `Foundations/Representations`.)

## Main results

* `GSpinGGP.integral_eq_smul_finsum_quotient`: for `K` open with `μ(K) < ∞` (`μ` left invariant)
  and `F` right `K`-invariant with compact support, `∫_G F dμ = μ(K) ∑_{gK} F(g)`.
* `Representation.IsAdmissible.comp_continuousMulEquiv`: admissibility pulls back along an
  isomorphism of topological groups.
* `Representation.traceOf_eq`, `Representation.exists_traceDatum`: for admissible `ρ` a trace datum
  exists, and the trace does not depend on it.
* `GSpinGGP.traceOf_smoothRep`, `GSpinGGP.isCharacterOf_smoothRep`,
  `GSpinGGP.characterOn_smoothRep`: the trace and character of `π^∞` are those of `π`.
* `GSpinGGP.multiplicity_smoothRep`: `m(π)` is the multiplicity of `π^∞` (by definition).
* `GSpinGGP.isIrreducible_smoothRep`: if compact open subgroups form a basis of neighbourhoods of
  `1` (van Dantzig), `π` is irreducible, `π^∞ ≠ 0` and the spaces `π^K` are finite-dimensional,
  then `π^∞` is an irreducible representation. Proof: a nonzero
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
`V^K` of every compact open subgroup `K` are finite-dimensional (Harish-Chandra, *Admissible
invariant distributions on reductive p-adic groups*, AMS ULS 16 (1999), preface, p. ix; Flath,
*Decomposition of representations into tensor products*, PSPUM 33 Part 1 (1979), §1). -/
def IsAdmissible (ρ : Representation k G V) : Prop :=
  ρ.IsSmooth ∧ ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) →
    FiniteDimensional k ↥(invariants (ρ.comp K.subtype))

/-- Admissibility pulls back along an isomorphism of topological groups `e : H ≃ₜ* G`: compact
open subgroups of `H` and `G` correspond under `e`. -/
theorem IsAdmissible.comp_continuousMulEquiv {H : Type*} [Group H] [TopologicalSpace H]
    {ρ : Representation k G V} (h : ρ.IsAdmissible) (e : H ≃ₜ* G) :
    Representation.IsAdmissible (ρ.comp e.toMulEquiv.toMonoidHom) := by
  have := h.1
  refine ⟨IsSmooth.comp (ρ := ρ) e.toHomeomorph.continuous, fun K hKo hKc => ?_⟩
  have hco : IsOpen ((K.map e.toMulEquiv.toMonoidHom : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map]
    exact e.toHomeomorph.isOpenMap _ hKo
  have hcc : IsCompact ((K.map e.toMulEquiv.toMonoidHom : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map]
    exact hKc.image e.toHomeomorph.continuous
  have := h.2 _ hco hcc
  have heq : invariants ((ρ.comp e.toMulEquiv.toMonoidHom).comp K.subtype) =
      invariants (ρ.comp (K.map e.toMulEquiv.toMonoidHom).subtype) := by
    ext v
    rw [mem_invariants, mem_invariants]
    constructor
    · intro h' g
      obtain ⟨p, hp, hpg⟩ := Subgroup.mem_map.1 g.property
      change ρ (g : G) v = v
      rw [← hpg]
      exact h' ⟨p, hp⟩
    · intro h' p
      exact h' ⟨e p, Subgroup.mem_map_of_mem _ p.property⟩
  rw [heq]
  exact this

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

/-- `tr ρ(f)` for an admissible `ρ` and a test function `f`: the trace of `ρ(f)` restricted to
`V^K`, for `f` bi-`K`-invariant. (Only the restriction `heckeOp ρ f K` on `V^K` is meant; it is
the trace of `ρ(f)` on `V` because `ρ(f)` has range in `V^K` and kills the other isotypic
components of `K`.) Defined by the epsilon pattern (`0` if no such `K` exists), as
`GSpinGGP.traceOf`; it does not depend on the datum (`traceOf_eq`). -/
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

/-- Multiplicities are invariant under equivalence of representations. -/
theorem multiplicity_eq_of_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e' : Representation.Equiv ρ σ) (S : Subgroup G) (ξ : ↥S → ℂ) :
    multiplicity ρ S ξ = multiplicity σ S ξ := by
  let e : V ≃ₗ[ℂ] W := e'.toLinearEquiv
  have he : ∀ g v, e (ρ g v) = σ g (e v) := fun g v =>
    LinearMap.congr_fun (e'.toIntertwiningMap.isIntertwining' g) v
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

variable [MeasurableSpace G] [BorelSpace G]

/-- **Integration over cosets.** For `μ` a left-invariant measure, `K` an open subgroup with
`μ(K) < ∞` and `F` right `K`-invariant with compact support,
`∫_G F dμ = μ(K) ∑_{gK ∈ G/K} F(g)` (a finite sum). -/
theorem integral_eq_smul_finsum_quotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {K : Subgroup G} {μ : Measure G} [μ.IsMulLeftInvariant] (hKo : IsOpen (K : Set G))
    (hfin : μ (K : Set G) ≠ ⊤)
    {F : G → E} (hF : ∀ g, ∀ k ∈ K, F (g * k) = F g) (hFc : HasCompactSupport F) :
    ∫ g, F g ∂μ = (μ (K : Set G)).toReal • ∑ᶠ c : G ⧸ K, F c.out := by
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
  have hμ : ∀ c : G ⧸ K, μ (QuotientGroup.mk ⁻¹' {c}) = μ (K : Set G) := fun c => by
    rw [hpre c, measure_smul]
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

/-! ## The trace of an admissible representation -/

section Trace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] {V : Type*} [AddCommGroup V] [Module ℂ V]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- Linear algebra: if `T` maps `M` (finite-dimensional) into `W ≤ M`, the traces of `T` on `M`
and on `W` agree. -/
theorem trace_restrict_eq_of_mem_of_le {E : Type*} [AddCommGroup E] [Module ℂ E]
    (T : E →ₗ[ℂ] E) {M W : Submodule ℂ E} (hWM : W ≤ M) [FiniteDimensional ℂ ↥M]
    (hT : ∀ x ∈ M, T x ∈ W) :
    LinearMap.trace ℂ ↥M (T.restrict fun x hx => hWM (hT x hx)) =
      LinearMap.trace ℂ ↥W (T.restrict fun x hx => hT x (hWM hx)) := by
  have : FiniteDimensional ℂ ↥W :=
    Module.Finite.of_injective (Submodule.inclusion hWM) (Submodule.inclusion_injective hWM)
  let S : ↥M →ₗ[ℂ] ↥W := LinearMap.codRestrict W (T ∘ₗ M.subtype) fun x => hT x x.property
  have h1 : T.restrict (fun x hx => hWM (hT x hx)) = Submodule.inclusion hWM ∘ₗ S := by
    ext x; rfl
  have h2 : T.restrict (fun x hx => hT x (hWM hx)) = S ∘ₗ Submodule.inclusion hWM := by
    ext x; rfl
  rw [h1, h2, LinearMap.trace_comp_comm']

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

omit [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- If `f` is left `L`-invariant and right `K`-invariant, then `g ↦ f(g) ρ(g) v` (`v ∈ V^K`) sums
over `G/K` to an `L`-invariant vector. -/
theorem finsum_quotient_mem_invariants (ρ : Representation ℂ G V) {f : G → ℂ}
    {K L : Subgroup G} (hKo : IsOpen (K : Set G)) (hf : HasCompactSupport f)
    (hfK : ∀ g, ∀ k ∈ K, f (g * k) = f g) (hfL : ∀ l ∈ L, ∀ g, f (l * g) = f g) {v : V}
    (hv : v ∈ Representation.invariants (ρ.comp K.subtype)) :
    ∑ᶠ c : G ⧸ K, f c.out • ρ c.out v ∈ Representation.invariants (ρ.comp L.subtype) := by
  rw [Representation.mem_invariants]
  intro l
  have hs := finite_setOf_out_ne_zero (K := K) hKo hf
  have hfin : (Function.support fun c : G ⧸ K => f c.out • ρ c.out v).Finite :=
    hs.subset fun c hc h0 => hc (by simp [h0])
  change ρ (l : G) _ = _
  rw [map_finsum _ hfin]
  -- `φ(g) = f(g) ρ(g) v` is right `K`-invariant, and `f(c) ρ(l c) v = φ(l c)`.
  set φ : G → V := fun g => f g • ρ g v
  have hφ : ∀ g, ∀ k ∈ K, φ (g * k) = φ g := by
    intro g k hk
    simp only [φ, hfK g k hk, map_mul, mul_apply_eq_comp]
    have hk' : ρ k v = v := (Representation.mem_invariants _ _).1 hv ⟨k, hk⟩
    rw [hk']
  have hout : ∀ c : G ⧸ K, φ ((l : G) • c).out = φ ((l : G) * c.out) := by
    intro c
    have : ((l : G) • c : G ⧸ K) = QuotientGroup.mk ((l : G) * c.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' c]
      rfl
    rw [this]
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K ((l : G) * c.out)
    rw [hk, hφ _ k k.property]
  have : (fun c : G ⧸ K => ρ (l : G) (f c.out • ρ c.out v)) =
      fun c => φ (MulAction.toPerm (l : G) c).out := by
    funext c
    rw [MulAction.toPerm_apply, hout c]
    simp only [φ, map_smul, map_mul, mul_apply_eq_comp, hfL l l.property]
  rw [this, finsum_comp_equiv (MulAction.toPerm (l : G)) (f := fun c : G ⧸ K => φ c.out)]

/-- `ρ(f)` with `f` left `L`-invariant maps `V^K` into `V^L`. -/
theorem heckeOp_mem_invariants (ρ : Representation ℂ G V) {f : G → ℂ} {K L : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hf : HasCompactSupport f) (hfK : ∀ g, ∀ k ∈ K, f (g * k) = f g)
    (hfL : ∀ l ∈ L, ∀ g, f (l * g) = f g) {v : V}
    (hv : v ∈ Representation.invariants (ρ.comp K.subtype)) :
    Representation.heckeOp ρ f K v ∈ Representation.invariants (ρ.comp L.subtype) := by
  rw [heckeOp_apply_of_finite ρ f K (finite_setOf_out_ne_zero hKo hf)]
  exact Submodule.smul_of_tower_mem _ _ (finsum_quotient_mem_invariants ρ hKo hf hfK hfL hv)

/-- `ρ(f)` on `V^K` does not depend on `K`: for `K₀ ≤ K` open, `K` compact, `f` a test function
right `K`-invariant and `v ∈ V^K`, the coset sums over `G/K₀` and `G/K` agree (both compute
`ℓ(∫ f(g) ρ(g) v dg)` for every linear form `ℓ`, by `integral_eq_smul_finsum_quotient`). -/
theorem heckeOp_eq_of_le (ρ : Representation ℂ G V) {f : G → ℂ} (hf : f ∈ testFunctions G)
    {K₀ K : Subgroup G} (hle : K₀ ≤ K) (hK₀o : IsOpen (K₀ : Set G)) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (hfK : ∀ g, ∀ k ∈ K, f (g * k) = f g) {v : V}
    (hv : v ∈ Representation.invariants (ρ.comp K.subtype)) :
    Representation.heckeOp ρ f K₀ v = Representation.heckeOp ρ f K v := by
  have hK₀c : IsCompact (K₀ : Set G) :=
    hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hK₀o) hle
  have hs := finite_setOf_out_ne_zero (K := K) hKo hf.2
  have hs₀ := finite_setOf_out_ne_zero (K := K₀) hK₀o hf.2
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro ℓ
  rw [map_sub, sub_eq_zero, heckeOp_apply_of_finite ρ f K₀ hs₀, heckeOp_apply_of_finite ρ f K hs]
  set ψ : G → ℂ := fun g => ℓ (f g • ρ g v)
  have hψK : ∀ g, ∀ k ∈ K, ψ (g * k) = ψ g := by
    intro g k hk
    simp only [ψ, hfK g k hk, map_mul, mul_apply_eq_comp]
    have hk' : ρ k v = v := (Representation.mem_invariants _ _).1 hv ⟨k, hk⟩
    rw [hk']
  have hψc : HasCompactSupport ψ :=
    hf.2.mono fun g hg h0 => hg (by simp [ψ, h0])
  have h1 := integral_eq_smul_finsum_quotient (μ := (Measure.haar : Measure G)) hKo
    hKc.measure_lt_top.ne hψK hψc
  have h2 := integral_eq_smul_finsum_quotient (μ := (Measure.haar : Measure G)) hK₀o
    hK₀c.measure_lt_top.ne (fun g k hk => hψK g k (hle hk)) hψc
  have hfin : ∀ (H : Subgroup G), {c : G ⧸ H | f c.out ≠ 0}.Finite →
      (Function.support fun c : G ⧸ H => f c.out • ρ c.out v).Finite := fun H hH =>
    hH.subset fun c hc h0 => hc (by simp [h0])
  rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, map_finsum _ (hfin _ hs₀),
    map_finsum _ (hfin _ hs)]
  exact h2.symm.trans h1

/-- **Independence of the trace datum**: for a test function `f`, `tr ρ(f)` is the trace of `ρ(f)`
on `V^K` for any trace datum `K`. -/
theorem _root_.Representation.traceOf_eq (ρ : Representation ℂ G V) {f : G → ℂ}
    (hf : f ∈ testFunctions G) (K : Subgroup G) (hK : Representation.TraceDatum ρ f K) :
    Representation.traceOf ρ f = LinearMap.trace ℂ ↥(Representation.invariants (ρ.comp K.subtype))
      ((Representation.heckeOp ρ f K).restrict hK.2.2.2.2) := by
  classical
  have key : ∀ (K K' : Subgroup G) (hK : Representation.TraceDatum ρ f K)
      (hK' : Representation.TraceDatum ρ f K'),
      LinearMap.trace ℂ ↥(Representation.invariants (ρ.comp K.subtype))
          ((Representation.heckeOp ρ f K).restrict hK.2.2.2.2) =
        LinearMap.trace ℂ ↥(Representation.invariants (ρ.comp K'.subtype))
          ((Representation.heckeOp ρ f K').restrict hK'.2.2.2.2) := by
    intro K K' hK hK'
    have := hK.2.2.2.1
    have := hK'.2.2.2.1
    set W := Representation.invariants (ρ.comp K.subtype) ⊓
      Representation.invariants (ρ.comp K'.subtype)
    have hmapK : ∀ v ∈ Representation.invariants (ρ.comp K.subtype),
        Representation.heckeOp ρ f K v ∈ W := fun v hv =>
      ⟨hK.2.2.2.2 v hv, heckeOp_mem_invariants ρ hK.1 hf.2 (fun g k hk => (hK.2.2.1 k hk g).2)
        (fun l hl g => (hK'.2.2.1 l hl g).1) hv⟩
    have hmapK' : ∀ v ∈ Representation.invariants (ρ.comp K'.subtype),
        Representation.heckeOp ρ f K' v ∈ W := fun v hv =>
      ⟨heckeOp_mem_invariants ρ hK'.1 hf.2 (fun g k hk => (hK'.2.2.1 k hk g).2)
        (fun l hl g => (hK.2.2.1 l hl g).1) hv, hK'.2.2.2.2 v hv⟩
    have hW : ∀ v ∈ W, Representation.heckeOp ρ f K v = Representation.heckeOp ρ f K' v := by
      intro v hv
      rw [← heckeOp_eq_of_le ρ hf inf_le_left (hK.1.inter hK'.1) hK.1 hK.2.1
        (fun g k hk => (hK.2.2.1 k hk g).2) hv.1,
        ← heckeOp_eq_of_le ρ hf inf_le_right (hK.1.inter hK'.1) hK'.1 hK'.2.1
        (fun g k hk => (hK'.2.2.1 k hk g).2) hv.2]
    rw [trace_restrict_eq_of_mem_of_le _ inf_le_left hmapK,
      trace_restrict_eq_of_mem_of_le _ inf_le_right hmapK']
    congr 1
    ext v
    exact hW v v.property
  have h : ∃ K, Representation.TraceDatum ρ f K := ⟨K, hK⟩
  unfold Representation.traceOf
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact key _ _ h.choose_spec hK

/-- For an admissible `ρ`, a trace datum exists for every test function, provided compact open
subgroups form a basis of neighbourhoods of `1` (van Dantzig). -/
theorem _root_.Representation.exists_traceDatum
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G,
      IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {ρ : Representation ℂ G V} (hρ : ρ.IsAdmissible) {f : G → ℂ} (hf : f ∈ testFunctions G) :
    ∃ K, Representation.TraceDatum ρ f K := by
  obtain ⟨K, hKo, hKc, hKb⟩ := exists_biInvariant hG hf
  exact ⟨K, hKo, hKc, hKb, hρ.2 K hKo hKc, fun v hv =>
    heckeOp_mem_invariants ρ hKo hf.2 (fun g k hk => (hKb k hk g).2)
      (fun l hl g => (hKb l hl g).1) hv⟩

end Trace

/-! ## The smooth part of a unitary representation -/

section SmoothPart

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

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

/-- On `π^K`, `π(f)` is the finite coset sum `μ(K) ∑_{gK} f(g) π(g)`, for `f` a test function,
right `K`-invariant, and `K` compact open. -/
theorem opOf_eq_smul_finsum (π : UnitaryRep G) {f : G → ℂ} (hf : f ∈ testFunctions G)
    {K : Subgroup G} (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hfK : ∀ g, ∀ k ∈ K, f (g * k) = f g) {v : π.H} (hv : v ∈ fixedSpace π K) :
    opOf π f v =
      ((Measure.haar : Measure G) (K : Set G)).toReal • ∑ᶠ c : G ⧸ K, f c.out • π.ρ c.out v := by
  rw [opOf_apply π (opIntegrable_of_mem_testFunctions π hf)]
  refine integral_eq_smul_finsum_quotient hKo hKc.measure_lt_top.ne (fun g k hk => ?_)
    hf.2.smul_right
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
      hK0o hK0c.measure_lt_top.ne (fun g k hk => ?_) hfK.2.smul_right]
  · refine W.smul_mem _ (finsum_induction _ W.zero_mem (fun _ _ => W.add_mem) fun c => ?_)
    exact W.smul_mem _ (hWg _ _ hw)
  · have hkK : k ∈ K := hk.1
    have hkU : k ∈ U := hk.2
    change (K : Set G).indicator 1 (g * k) • π.ρ (g * k) w = _
    rw [indicator_subgroup_mul_right hkK, map_mul]
    change _ • π.ρ g (π.ρ k w) = _
    rw [hU k hkU]

end SmoothPart

section Irreducible

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **`π^∞` is irreducible.** Let `π` be an irreducible unitary representation with `π^∞ ≠ 0`
whose spaces `π^K` (`K` compact open) are finite-dimensional, and suppose compact open subgroups
form a basis of neighbourhoods of `1` (van Dantzig). Then the smooth representation `π^∞` is
(algebraically) irreducible. -/
theorem isIrreducible_smoothRep [LocallyCompactSpace G] [T2Space G]
    (hG : ∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G,
      IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {π : UnitaryRep G} (hπ : π.IsIrreducible) (hne : smoothVectors π ≠ ⊥)
    (hadm : IsAdmissible π) :
    (smoothRep π).IsIrreducible := by
  borelize G
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
  · exact hne (congrArg Subrepresentation.toSubmodule h)
  · by_contra hne
    have hle : τ.toSubmodule ≤ smoothVectors π := hτ.le
    have h1 := key τ.toSubmodule hle (fun g w hw => τ.apply_mem_toSubmodule g hw)
      (fun h0 => hne (Subrepresentation.toSubmodule_injective (by rw [h0]; rfl)))
    exact hτ.not_ge h1

end Irreducible

end GSpinGGP
