/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalGroups

/-!
# Self-dual Haar measures on a finite-dimensional `p`-adic vector space

Literature file. It imports only `Foundations/LocalGroups` (for `PAdicField`,
`NontrivialAddChar`, `IsSelfDual`).

Thesis §2.4 (and BP Astérisque 418 §1.6) equips `𝔤(F)`, and the tangent spaces `𝔤/𝔤_X` of
nilpotent orbits, with the Haar measure that is self-dual for `ψ ∘ B`. That such a measure exists
is standard and is used without comment. In this project `selfDualMeasure` is defined by
"if a self-dual measure exists then choose one, else `0`", so the existence has to be supplied:
it is the axiom below.

## Contents
* **axiom** `exists_isSelfDual`: for a finite-dimensional `F`-vector space `V` with its natural
  (module) topology and Borel σ-algebra, a nondegenerate bilinear form `B` and a nontrivial
  continuous character `ψ`, some Haar measure on `V` is self-dual for `ψ ∘ B`.
* `exists_isSelfDual_of_t2`: the same for any Hausdorff topological-vector-space topology on `V`
  (it is then the module topology, `F` being complete).
* `exists_isSelfDual_of_isInducing`: the same for the topology induced by an injective linear
  map into a Hausdorff topological vector space (e.g. a subspace of a Lie algebra with the
  subspace topology). This is the form used by `Sanity/Witnesses` and `Sanity/NilpotentOrbit`.
* `exists_isSelfDual_of_subsingleton` (sanity): on a zero space the axiom is consistent with
  the explicit witness `dirac 0`.
-/

noncomputable section

open MeasureTheory Topology

set_option linter.style.haveILetI false

namespace GSpinGGP

/-- **Existence of self-dual Haar measures** (Tate's thesis, 1950, printed in Cassels–Fröhlich,
*Algebraic Number Theory* (1967), Ch. XV, §2.2: the characters of `F` are the `x ↦ ψ(ax)`,
`F ≅ F^`, and for the Haar measure self-dual with respect to this identification the Fourier
inversion formula holds; Weil, *Basic Number Theory*, Ch. II §5 (for a finite-dimensional
`F`-vector space `V`, `Y ↦ ψ(⟨·, Y⟩)` identifies the algebraic dual `V'` with the Pontryagin
dual `V^`) and Ch. VII §2 (self-dual measures); theorem numbers not checked against the books.
Thesis §2.4; BP Astérisque 418 §1.6.)

Statement: let `F` be a `p`-adic field, `V` a finite-dimensional `F`-vector space with its
natural topology (`IsModuleTopology`) and the Borel σ-algebra, `B` a nondegenerate bilinear form
on `V` (left and right separating; it need not be symmetric — the Kirillov form is alternating)
and `ψ` a nontrivial continuous additive character. Then there is a Haar measure `μ` on `V` with
`f(Z) = ∫ f̂(Y) ψ(-B(Z,Y)) dμ(Y)`, `f̂(Y) = ∫ f(X) ψ(B(X,Y)) dμ(X)`, for every locally constant
compactly supported `f` (`IsSelfDual`).

Why this is the cited fact. `Y ↦ ψ(B(·, Y))` is a topological isomorphism `V ≅ V^` (Weil II §5,
using `F ≅ F^` and right separation of `B`); transporting the Pontryagin dual measure `μ^` of a
Haar measure `μ` along it gives `c·μ` for some `c > 0`, and `μ' = c^{-1/2} μ` is then equal to its
own dual. Fourier inversion for `μ'` and its dual (Pontryagin–Plancherel; Folland, *A Course in
Abstract Harmonic Analysis*, §4.3) is exactly the displayed formula, the character `ψ(B(·,Y))`
being conjugated to `ψ(-B(Z,Y))`. No symmetry of `B` is used.

Lean-specific points. All instance arguments are explicit binders of the axiom (no
section `variable` can be dropped). The integrands are continuous with compact support (`f̂` is
again locally constant and compactly supported), hence Bochner-integrable for a Haar measure, so
the Lean integrals are the true integrals and no "junk `0`" makes the statement easier or
harder than the mathematics. For `V = 0` the conclusion holds with `dirac 0`
(`exists_isSelfDual_of_subsingleton` below, proved without the axiom). -/
axiom exists_isSelfDual {F : Type*} [NontriviallyNormedField F] [PAdicField F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V]
    (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate) (ψ : NontrivialAddChar F) :
    ∃ μ : Measure V, IsSelfDual μ B ψ

section Corollaries

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]

/-- `exists_isSelfDual` for any Hausdorff topological-vector-space topology on `V`: over the
complete field `F` such a topology is the module topology (Mathlib
`isModuleTopologyOfFiniteDimensional`). -/
theorem exists_isSelfDual_of_t2 [T2Space V] [IsTopologicalAddGroup V] [ContinuousSMul F V]
    (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate) (ψ : NontrivialAddChar F) :
    ∃ μ : Measure V, IsSelfDual μ B ψ := by
  haveI : IsModuleTopology F V := isModuleTopologyOfFiniteDimensional (𝕜 := F) (E := V)
  exact exists_isSelfDual B hB ψ

/-- `exists_isSelfDual` for the topology on `V` induced by an injective linear map `j : V → W`
into a Hausdorff topological vector space `W`, e.g. a subspace (or a subspace of a subspace) of
a finite-dimensional algebra with the subspace topology. -/
theorem exists_isSelfDual_of_isInducing {W : Type*} [AddCommGroup W] [Module F W]
    [TopologicalSpace W] [T2Space W] [IsTopologicalAddGroup W] [ContinuousSMul F W]
    (j : V →ₗ[F] W) (hj : IsInducing j) (hinj : Function.Injective j)
    (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate) (ψ : NontrivialAddChar F) :
    ∃ μ : Measure V, IsSelfDual μ B ψ := by
  haveI : T2Space V := (IsEmbedding.mk hj hinj).t2Space
  haveI : IsTopologicalAddGroup V := hj.isTopologicalAddGroup j
  haveI : ContinuousSMul F V := hj.continuousSMul continuous_id (fun {c x} => j.map_smul c x)
  exact exists_isSelfDual_of_t2 B hB ψ

end Corollaries

/-! ## Sanity: the degenerate case `V = 0` -/

section Sanity

variable {F : Type*} [NontriviallyNormedField F]
variable {V : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V] [MeasurableSpace V]

/-- On a zero space `dirac 0` is self-dual for every `B` and `ψ` (no axiom; the same fact is
`Sanity.isSelfDual_dirac_zero`). So the axiom `exists_isSelfDual`, whose hypotheses hold there
for `B = 0`, asserts nothing false in dimension `0`. -/
theorem exists_isSelfDual_of_subsingleton [Subsingleton V] (B : LinearMap.BilinForm F V)
    (ψ : NontrivialAddChar F) : ∃ μ : Measure V, IsSelfDual μ B ψ := by
  have hms : ∀ s : Set V, MeasurableSet s := fun s => by
    rcases s.eq_empty_or_nonempty with h | ⟨x, hx⟩
    · rw [h]; exact MeasurableSet.empty
    · have : s = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
      rw [this]; exact MeasurableSet.univ
  haveI : MeasurableSingletonClass V := ⟨fun _ => hms _⟩
  have hψ0 : ψ 0 = 1 := by
    show ((ψ.toAddChar 0 : Circle) : ℂ) = 1
    simp
  refine ⟨Measure.dirac 0, ⟨?_, fun f _ Z => ?_⟩⟩
  · exact
      { lt_top_of_isCompact := fun _ _ => measure_lt_top _ _
        map_add_left_eq_self := fun a => by
          rw [Measure.map_dirac' (fun s _ => hms _), add_zero, Subsingleton.elim a 0]
        open_pos := fun U _ hU => by
          obtain ⟨x, hx⟩ := hU
          rw [Measure.dirac_apply' _ (hms U),
            Set.indicator_of_mem (Subsingleton.elim x (0 : V) ▸ hx)]
          simp }
  · simp only [fourierWRT, integral_dirac, map_zero, LinearMap.zero_apply, neg_zero, hψ0,
      mul_one]
    rw [Subsingleton.elim Z 0]

/-- The axiom at the zero space, for the zero form (nondegenerate there): consistent with the
explicit witness above (and, by `Sanity.eq_dirac_of_isSelfDual`, the witness is `dirac 0`). -/
example {F : Type} [NontriviallyNormedField F] [PAdicField F] [MeasurableSpace (Fin 0 → F)]
    [BorelSpace (Fin 0 → F)] (ψ : NontrivialAddChar F) :
    ∃ μ : Measure (Fin 0 → F), IsSelfDual μ 0 ψ :=
  exists_isSelfDual 0 ⟨fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩ ψ

end Sanity

end GSpinGGP
