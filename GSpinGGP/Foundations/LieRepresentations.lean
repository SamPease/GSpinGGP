/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
-/
import GSpinGGP.Foundations.Representations
import GSpinGGP.Foundations.HilbertTrace
import TauCeti.Geometry.Lie.TestFunction.Basic
import TauCeti.RepresentationTheory.Continuous.LieSmoothVector
import TauCeti.Analysis.LocallyConvex.WithSeminorms

/-!
# Unitary representations of real Lie groups

The archimedean counterparts of the notions of `GSpinGGP/Foundations/Representations.lean`
(which treats totally disconnected groups), for a unitary representation of a real Lie group,
in the setting of Harish-Chandra and Casselman–Wallach: test functions are smooth with compact
support, `π^∞` is the space of vectors with smooth orbit map, with its standard seminorms
`v ↦ ‖dπ(X₁) ⋯ dπ(Xₙ) v‖`, and the multiplicity counts *continuous* equivariant forms on `π^∞`.
Continuity of a linear form is expressed as boundedness by finitely many of these seminorms, which
is continuity for the locally convex (Fréchet) topology they generate; that topology itself is not
constructed here.

The real Lie group structure is data, `RealLieStructure G`, not an instance: a group such as
`G(F)` for a local field `F` gets it only in the archimedean case, and only after choices. The
fields of a `RealLieStructure` are made local instances inside this file only. Any two
`RealLieStructure`s on the same topological group give the same smooth structure (a continuous
homomorphism of Lie groups is smooth, by Cartan's theorem). That the identity is smooth between
two such structures, and that `testFunctions` and `smoothVectors` do not depend on `L`, is proved in
`GSpinGGP/Foundations/RealLieStructureOfClosed.lean` (`RealLieStructure.contMDiff_id`,
`RealLieStructure.testFunctions_eq`, `RealLieStructure.smoothVectors_eq`), and likewise for the
character (`RealLieStructure.isCharacterOf_iff`, `RealLieStructure.characterOn_eq`); `traceOf`
does not involve `L`. For the seminorms, forms, multiplicity and `HasModel` it is not yet proved.

Everything lives in the namespace `GSpinGGP.LieRep`, so the names (`smoothVectors`,
`multiplicity`, …) do not clash with the `p`-adic ones. Every notion takes the Lie structure `L`
as its first explicit argument and otherwise has the argument order and output type of its
`p`-adic namesake. `traceOf` does not depend on `L`.

## Main definitions

* `RealLieStructure G`: a finite-dimensional real normed space `E` with charts on `G` modelled on
  `E` for which `G` is a smooth Lie group (`𝓘(ℝ, E)`, so without boundary).
* `LieRep.testFunctions L`: `C_c^∞(G)`, the range of Tau Ceti's `LieTestFunction`.
* `LieRep.smoothVectors L π`: `π^∞`, Tau Ceti's `lieSmoothVectors` (smooth orbit maps).
* `LieRep.smoothAction L π g`: the action of `G` on `π^∞`.
* `LieRep.derivedAction L π Xs`: `dπ(X₁) ⋯ dπ(Xₙ)` on `π^∞` for a list of left-invariant
  derivations, from Tau Ceti's `lieSmoothVectorsDerivative`.
* `LieRep.smoothSeminorm L π Xs`: `v ↦ ‖dπ(X₁) ⋯ dπ(Xₙ) v‖`, the standard seminorms of `π^∞`.
* `LieRep.continuousForms L π`: the linear forms on `π^∞` bounded by finitely many of these
  seminorms (continuous for the topology these seminorms generate).
* `LieRep.equivariantForms L π S ξ`, `LieRep.multiplicity L π S ξ`, `LieRep.HasModel L π S ξ`.
* `LieRep.traceOf π f`: `hilbertTrace (opOf π f)`, the trace of the trace-class operator `π(f)`.
* `LieRep.IsCharacterOf L π θ`, `LieRep.characterOn L π S`.

## Main results

* `LieRep.rho_mem_smoothVectors`, `LieRep.smoothAction`: `π^∞` is stable under `G`.
* `LieRep.continuousForms`, `LieRep.equivariantForms` are submodules.
* `LieRep.hasModel_iff_multiplicity_ne_zero`.
* `LieRep.opIntegrable_of_mem_testFunctions`: `π(f)` is a Bochner integral for `f ∈ C_c^∞(G)`.
* Invariance under unitary equivalence: `smoothEquiv_derivative` (`U dπ(X) = dπ'(X) U`),
  `smoothSeminorm_smoothEquiv`, `isContinuousForm_iff_of_intertwines`, `multiplicity_congr`,
  `hasModel_congr`, `traceOf_congr`, `isCharacterOf_congr`, `characterOn_congr`.

Density of `π^∞` in `H` (Gårding) and the trace-class property of `π(f)` are not proved here;
`IsCharacterOf` carries the latter as a condition.

## References

* Harish-Chandra, *Representations of a semisimple Lie group on a Banach space. I*, Trans. AMS 75
  (1953): smooth vectors, `π(f)` for `f ∈ C_c^∞(G)`.
* N. Wallach, *Real Reductive Groups I*, Academic Press 1988, §1.6 (smooth vectors and their
  Fréchet topology) and Ch. 8 (the global character).
* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, Israel J. Math.
  199 (2014), §2.
-/

open MeasureTheory Manifold
open scoped ContDiff Manifold InnerProductSpace NNReal

namespace GSpinGGP

universe u

/-- A real Lie group structure on the topological group `G`, as data: a finite-dimensional real
normed space `E` and an atlas on `G` modelled on `E`, for which `G` is a smooth (`C^∞`) Lie group
with model `𝓘(ℝ, E)` (so without boundary). The topology of `G` is the given one. This is the
shape of Tau Ceti's `EmbeddedLieSubgroupData`. -/
structure RealLieStructure (G : Type u) [Group G] [TopologicalSpace G] where
  /-- The model space of the charts (a real normed space of dimension `dim G`). It lives in `Type`:
  a finite-dimensional real normed space is isomorphic to some `ℝⁿ : Type`, so this loses no
  generality and adds no universe parameter. -/
  E : Type
  [normedAddCommGroup : NormedAddCommGroup E]
  [normedSpace : NormedSpace ℝ E]
  [finiteDimensional : FiniteDimensional ℝ E]
  /-- The atlas of `G`, modelled on `E`. -/
  [chartedSpace : ChartedSpace E G]
  /-- The group operations are smooth. -/
  [lieGroup : LieGroup 𝓘(ℝ, E) ∞ G]

/-- A real Lie group is Hausdorff (Tau Ceti's `ModelWithCorners.t2Space_of_lieGroup`). -/
theorem RealLieStructure.t2Space {G : Type u} [Group G] [TopologicalSpace G]
    (L : RealLieStructure G) : T2Space G :=
  letI := L.normedAddCommGroup
  letI := L.normedSpace
  letI := L.chartedSpace
  haveI := L.lieGroup
  𝓘(ℝ, L.E).t2Space_of_lieGroup ∞

namespace LieRep

attribute [local instance] RealLieStructure.normedAddCommGroup RealLieStructure.normedSpace
  RealLieStructure.finiteDimensional RealLieStructure.chartedSpace RealLieStructure.lieGroup

variable {G : Type u} [Group G] [TopologicalSpace G] (L : RealLieStructure G)

/-! ### Test functions -/

/-- `C_c^∞(G)`: the smooth complex-valued functions on `G` with compact support (Harish-Chandra),
the range of Tau Ceti's `LieTestFunction` in the functions `G → ℂ`. -/
noncomputable def testFunctions : Submodule ℂ (G → ℂ) :=
  LinearMap.range (TauCeti.LieTestFunction.toFunction 𝓘(ℝ, L.E) G)

theorem mem_testFunctions {f : G → ℂ} :
    f ∈ testFunctions L ↔ ContMDiff 𝓘(ℝ, L.E) 𝓘(ℝ, ℂ) ∞ f ∧ HasCompactSupport f := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.contMDiff, a.hasCompactSupport⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨f, h₁, h₂⟩, rfl⟩

theorem continuous_of_mem_testFunctions {f : G → ℂ} (hf : f ∈ testFunctions L) : Continuous f :=
  ((mem_testFunctions L).1 hf).1.continuous

/-! ### Smooth vectors -/

/-- The smooth vectors `π^∞` of `π`: the vectors `v` whose orbit map `g ↦ π(g) v` is a smooth
map `G → H` (Harish-Chandra 1953; Wallach §1.6). This is Tau Ceti's `lieSmoothVectors`. -/
noncomputable def smoothVectors (π : UnitaryRep G) : Submodule ℂ π.H :=
  ContRepresentation.lieSmoothVectors 𝓘(ℝ, L.E) π.toContRepresentation

theorem mem_smoothVectors_iff (π : UnitaryRep G) {v : π.H} :
    v ∈ smoothVectors L π ↔ ContMDiff 𝓘(ℝ, L.E) 𝓘(ℝ, π.H) ∞ fun g => π.ρ g v :=
  Iff.rfl

/-- `π^∞` is stable under `π(g)`. -/
theorem rho_mem_smoothVectors (π : UnitaryRep G) {v : π.H} (hv : v ∈ smoothVectors L π) (g : G) :
    π.ρ g v ∈ smoothVectors L π :=
  ContRepresentation.IsLieSmoothVector.apply hv g

/-- The action of `G` on `π^∞`. -/
noncomputable def smoothAction (π : UnitaryRep G) (g : G) :
    ↥(smoothVectors L π) →ₗ[ℂ] ↥(smoothVectors L π) where
  toFun v := ⟨π.ρ g v, rho_mem_smoothVectors L π v.property g⟩
  map_add' v w := Subtype.ext (map_add (π.ρ g) (v : π.H) w)
  map_smul' c v := Subtype.ext (map_smul (π.ρ g) c (v : π.H))

@[simp]
theorem smoothAction_apply (π : UnitaryRep G) (g : G) (v : ↥(smoothVectors L π)) :
    (smoothAction L π g v : π.H) = π.ρ g v := rfl

/-! ### The seminorms of `π^∞` -/

section Seminorms

/-- The derived action `dπ(X) v = d/dt|₀ π(exp tX) v` of a left-invariant derivation `X` (an
element of the Lie algebra) on `π^∞`: Tau Ceti's `lieSmoothVectorsDerivative`. -/
noncomputable def derivative (π : UnitaryRep G) (X : LeftInvariantDerivation 𝓘(ℝ, L.E) G) :
    Module.End ℂ ↥(smoothVectors L π) :=
  haveI := L.t2Space
  ContRepresentation.lieSmoothVectorsDerivative 𝓘(ℝ, L.E) π.toContRepresentation X

theorem derivative_apply (π : UnitaryRep G) (X : LeftInvariantDerivation 𝓘(ℝ, L.E) G)
    (v : ↥(smoothVectors L π)) :
    haveI := L.t2Space
    (derivative L π X v : π.H) =
      deriv (fun t : ℝ => π.ρ (lieExp (t • X)) (v : π.H)) 0 :=
  rfl

/-- `dπ(X₁) ∘ ⋯ ∘ dπ(Xₙ)` on `π^∞`, for a list `[X₁, …, Xₙ]` of left-invariant derivations. -/
noncomputable def derivedAction (π : UnitaryRep G)
    (Xs : List (LeftInvariantDerivation 𝓘(ℝ, L.E) G)) : Module.End ℂ ↥(smoothVectors L π) :=
  (Xs.map (derivative L π)).prod

@[simp]
theorem derivedAction_nil (π : UnitaryRep G) : derivedAction L π [] = 1 := rfl

theorem derivedAction_cons (π : UnitaryRep G) (X : LeftInvariantDerivation 𝓘(ℝ, L.E) G)
    (Xs : List (LeftInvariantDerivation 𝓘(ℝ, L.E) G)) :
    derivedAction L π (X :: Xs) = derivative L π X * derivedAction L π Xs :=
  List.prod_cons

/-- The seminorm `v ↦ ‖dπ(X₁) ⋯ dπ(Xₙ) v‖` on `π^∞`. The family over all finite lists of
left-invariant derivations is the standard family of seminorms of `π^∞` (Wallach §1.6; it
generates the same topology as the monomials in a basis of the Lie algebra, as `dπ` is linear);
that topology is not constructed here. The empty list gives the norm of `H`. -/
noncomputable def smoothSeminorm (π : UnitaryRep G)
    (Xs : List (LeftInvariantDerivation 𝓘(ℝ, L.E) G)) : Seminorm ℂ ↥(smoothVectors L π) :=
  (normSeminorm ℂ π.H).comp ((smoothVectors L π).subtype ∘ₗ derivedAction L π Xs)

theorem smoothSeminorm_apply (π : UnitaryRep G)
    (Xs : List (LeftInvariantDerivation 𝓘(ℝ, L.E) G)) (v : ↥(smoothVectors L π)) :
    smoothSeminorm L π Xs v = ‖(derivedAction L π Xs v : π.H)‖ := rfl

@[simp]
theorem smoothSeminorm_nil (π : UnitaryRep G) (v : ↥(smoothVectors L π)) :
    smoothSeminorm L π [] v = ‖(v : π.H)‖ := rfl

/-- A linear form on `π^∞` is bounded by a constant times the maximum of finitely many of the
seminorms `smoothSeminorm` (Mathlib's `Seminorm.IsBounded`, against the absolute value on `ℂ`).
This is continuity for the locally convex topology the seminorms generate (that topology is not
constructed here). -/
def IsContinuousForm (π : UnitaryRep G) (ℓ : Module.Dual ℂ ↥(smoothVectors L π)) : Prop :=
  Seminorm.IsBounded (smoothSeminorm L π) (fun _ : Unit => normSeminorm ℂ ℂ) ℓ

theorem isContinuousForm_iff (π : UnitaryRep G) (ℓ : Module.Dual ℂ ↥(smoothVectors L π)) :
    IsContinuousForm L π ℓ ↔ ∃ (s : Finset (List (LeftInvariantDerivation 𝓘(ℝ, L.E) G)))
      (C : ℝ≥0), ∀ v, ‖ℓ v‖ ≤ C * (s.sup (smoothSeminorm L π)) v := by
  rw [IsContinuousForm, Seminorm.isBounded_const]
  rfl

open Classical in
/-- The linear forms on `π^∞` bounded by finitely many of the seminorms `smoothSeminorm`
(`IsContinuousForm`): the continuous dual for the topology these seminorms generate. -/
noncomputable def continuousForms (π : UnitaryRep G) :
    Submodule ℂ (Module.Dual ℂ ↥(smoothVectors L π)) where
  carrier := {ℓ | IsContinuousForm L π ℓ}
  zero_mem' := (isContinuousForm_iff L π 0).2 ⟨∅, 0, fun v => by simp⟩
  add_mem' := by
    intro ℓ ℓ' hℓ hℓ'
    obtain ⟨s, C, h⟩ := (isContinuousForm_iff L π ℓ).1 hℓ
    obtain ⟨s', C', h'⟩ := (isContinuousForm_iff L π ℓ').1 hℓ'
    refine (isContinuousForm_iff L π _).2 ⟨s ∪ s', C + C', fun v => ?_⟩
    have hs : s.sup (smoothSeminorm L π) v ≤ (s ∪ s').sup (smoothSeminorm L π) v :=
      Seminorm.le_def.1 (Finset.sup_mono Finset.subset_union_left) v
    have hs' : s'.sup (smoothSeminorm L π) v ≤ (s ∪ s').sup (smoothSeminorm L π) v :=
      Seminorm.le_def.1 (Finset.sup_mono Finset.subset_union_right) v
    calc ‖(ℓ + ℓ') v‖ ≤ ‖ℓ v‖ + ‖ℓ' v‖ := norm_add_le _ _
      _ ≤ C * s.sup (smoothSeminorm L π) v + C' * s'.sup (smoothSeminorm L π) v :=
          add_le_add (h v) (h' v)
      _ ≤ C * (s ∪ s').sup (smoothSeminorm L π) v + C' * (s ∪ s').sup (smoothSeminorm L π) v :=
          add_le_add (mul_le_mul_of_nonneg_left hs C.coe_nonneg)
            (mul_le_mul_of_nonneg_left hs' C'.coe_nonneg)
      _ = ((C + C' : ℝ≥0) : ℝ) * (s ∪ s').sup (smoothSeminorm L π) v := by push_cast; ring
  smul_mem' := by
    intro c ℓ hℓ
    obtain ⟨s, C, h⟩ := (isContinuousForm_iff L π ℓ).1 hℓ
    refine (isContinuousForm_iff L π _).2 ⟨s, ‖c‖₊ * C, fun v => ?_⟩
    rw [LinearMap.smul_apply, norm_smul, NNReal.coe_mul, coe_nnNorm, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h v) (norm_nonneg c)

theorem mem_continuousForms (π : UnitaryRep G) {ℓ : Module.Dual ℂ ↥(smoothVectors L π)} :
    ℓ ∈ continuousForms L π ↔ IsContinuousForm L π ℓ := Iff.rfl

end Seminorms

/-! ### Equivariant forms and multiplicities -/

section Multiplicity

/-- The space `Hom_S(π^∞, ξ)` of continuous `(S, ξ)`-equivariant linear forms on `π^∞`:
`ℓ(π(s) v) = ξ(s) ℓ(v)`, `ℓ` continuous (the archimedean multiplicity space of the
Gan–Gross–Prasad conjecture). -/
noncomputable def equivariantForms (π : UnitaryRep G) (S : Subgroup G) (ξ : ↥S → ℂ) :
    Submodule ℂ (Module.Dual ℂ ↥(smoothVectors L π)) where
  carrier := {ℓ | (∀ s : ↥S, ∀ v, ℓ (smoothAction L π s v) = ξ s * ℓ v) ∧ ℓ ∈ continuousForms L π}
  zero_mem' := ⟨fun s v => by simp, Submodule.zero_mem _⟩
  add_mem' := by
    rintro ℓ ℓ' ⟨hℓ, cℓ⟩ ⟨hℓ', cℓ'⟩
    refine ⟨fun s v => ?_, Submodule.add_mem _ cℓ cℓ'⟩
    simp only [LinearMap.add_apply, hℓ s v, hℓ' s v, mul_add]
  smul_mem' := by
    rintro c ℓ ⟨hℓ, cℓ⟩
    refine ⟨fun s v => ?_, Submodule.smul_mem _ c cℓ⟩
    simp only [LinearMap.smul_apply, hℓ s v, smul_eq_mul]
    ring

theorem mem_equivariantForms (π : UnitaryRep G) (S : Subgroup G) (ξ : ↥S → ℂ)
    {ℓ : Module.Dual ℂ ↥(smoothVectors L π)} :
    ℓ ∈ equivariantForms L π S ξ ↔
      (∀ s : ↥S, ∀ v, ℓ (smoothAction L π s v) = ξ s * ℓ v) ∧ IsContinuousForm L π ℓ :=
  Iff.rfl

/-- The multiplicity `m(π) = dim Hom_S(π^∞, ξ)` (continuous forms), valued in `ℕ∞`
(`⊤` if infinite-dimensional). -/
noncomputable def multiplicity (π : UnitaryRep G) (S : Subgroup G) (ξ : ↥S → ℂ) : ℕ∞ :=
  Cardinal.toENat (Module.rank ℂ ↥(equivariantForms L π S ξ))

/-- `π` has an `(S, ξ)`-model: there is a nonzero continuous `(S, ξ)`-equivariant form on
`π^∞`. -/
def HasModel (π : UnitaryRep G) (S : Subgroup G) (ξ : ↥S → ℂ) : Prop :=
  equivariantForms L π S ξ ≠ ⊥

theorem hasModel_iff_multiplicity_ne_zero (π : UnitaryRep G) (S : Subgroup G) (ξ : ↥S → ℂ) :
    HasModel L π S ξ ↔ multiplicity L π S ξ ≠ 0 := by
  rw [HasModel, multiplicity, Ne, Ne, Cardinal.toENat_eq_zero, Submodule.rank_eq_zero]

end Multiplicity

/-! ### Traces and characters -/

section Characters

attribute [local instance] Classical.propDecidable

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Test functions are `OpIntegrable`: `g ↦ f(g) π(g) v` is continuous with compact support. -/
theorem opIntegrable_of_mem_testFunctions (π : UnitaryRep G) {f : G → ℂ}
    (hf : f ∈ testFunctions L) : OpIntegrable π f := fun v =>
  ((continuous_of_mem_testFunctions L hf).smul (π.strongCont v)).integrable_of_hasCompactSupport
    ((mem_testFunctions L).1 hf).2.smul_right

/-- `tr π(f)`: the trace of `π(f) = ∫_G f(g) π(g) dg` (`opOf`) as an operator on the Hilbert
space (`hilbertTrace`). It is the trace of `π(f)` when `π(f)` is nuclear (trace class), as it is
for `f ∈ C_c^∞(G)` and `π` irreducible unitary of a real reductive group (Harish-Chandra), and
the junk value `0` otherwise. -/
noncomputable def traceOf (π : UnitaryRep G) (f : G → ℂ) : ℂ :=
  hilbertTrace (opOf π f)

/-- `θ` is the (Harish-Chandra) character of `π`: `π(f)` is trace class for every
`f ∈ C_c^∞(G)`, `θ` is locally integrable and `∫_G θ(g) f(g) dg = tr π(f)` for every
`f ∈ C_c^∞(G)` (Wallach Ch. 8). The trace-class condition is part of the definition because
`traceOf` is `0` off the nuclear operators. -/
def IsCharacterOf (π : UnitaryRep G) (θ : G → ℂ) : Prop :=
  LocallyIntegrable θ (Measure.haar : Measure G) ∧
    ∀ f ∈ testFunctions L, opOf π f ∈ TauCeti.nuclearOperators ℂ π.H π.H ∧
      ∫ g, θ g * f g ∂(Measure.haar : Measure G) = traceOf π f

/-- The character `θ_π` as a function, normalised to be continuous on `S` (`S` is intended to be
the regular semisimple set, where Harish-Chandra's regularity theorem gives an analytic
representative). Defined by the epsilon pattern; `0` if no such representative exists. -/
noncomputable def characterOn (π : UnitaryRep G) (S : Set G) : G → ℂ :=
  if h : ∃ θ, IsCharacterOf L π θ ∧ ContinuousOn θ S then h.choose else 0

/-- The character is unique as a function a.e.: two functions satisfying `IsCharacterOf L π`
agree almost everywhere for Haar measure (smooth compactly supported functions separate locally
integrable functions on a manifold, Mathlib's `ae_eq_of_integral_contMDiff_smul_eq`). -/
theorem IsCharacterOf.ae_eq [SigmaCompactSpace G] {π : UnitaryRep G} {θ θ' : G → ℂ}
    (hθ : IsCharacterOf L π θ) (hθ' : IsCharacterOf L π θ') :
    θ =ᵐ[(Measure.haar : Measure G)] θ' := by
  have := L.t2Space
  refine ae_eq_of_integral_contMDiff_smul_eq 𝓘(ℝ, L.E) hθ.1 hθ'.1 fun g hg hgc => ?_
  have hf : (fun x => (g x : ℂ)) ∈ testFunctions L :=
    (mem_testFunctions L).2 ⟨Complex.ofRealCLM.contMDiff.comp hg, hgc.comp_left Complex.ofReal_zero⟩
  have h := (hθ.2 _ hf).2.trans (hθ'.2 _ hf).2.symm
  simp only [Complex.real_smul]
  simpa only [mul_comm] using h

theorem characterOn_spec (π : UnitaryRep G) (S : Set G)
    (h : ∃ θ, IsCharacterOf L π θ ∧ ContinuousOn θ S) :
    IsCharacterOf L π (characterOn L π S) ∧ ContinuousOn (characterOn L π S) S := by
  unfold characterOn
  split_ifs
  exact h.choose_spec

end Characters

/-! ### Unitary equivalence

Smooth vectors, the seminorms, continuous equivariant forms, multiplicities, traces and
characters depend only on the unitary equivalence class of `π`. -/

section MultCongr

variable {π π' : UnitaryRep G}

/-- A unitary intertwiner maps smooth vectors to smooth vectors. -/
theorem mem_smoothVectors_of_intertwines (U : π.H ≃ₗᵢ[ℂ] π'.H)
    (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v)) {v : π.H} (hv : v ∈ smoothVectors L π) :
    U v ∈ smoothVectors L π' := by
  rw [mem_smoothVectors_iff] at hv ⊢
  have hfun : (fun g => π'.ρ g (U v)) =
      (U.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) ∘ fun g => π.ρ g v := by
    funext g
    simp [hU]
  rw [hfun]
  exact (ContinuousLinearMap.contMDiff _).comp hv

theorem mem_smoothVectors_iff_of_intertwines (U : π.H ≃ₗᵢ[ℂ] π'.H)
    (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v)) (v : π.H) :
    v ∈ smoothVectors L π ↔ U v ∈ smoothVectors L π' := by
  refine ⟨mem_smoothVectors_of_intertwines L U hU, fun hv => ?_⟩
  have := mem_smoothVectors_of_intertwines L U.symm (UnitaryRep.symm_intertwines U hU) hv
  simpa using this

/-- The isomorphism `π^∞ ≃ π'^∞` induced by a unitary intertwiner. -/
noncomputable def smoothEquiv (U : π.H ≃ₗᵢ[ℂ] π'.H) (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v)) :
    ↥(smoothVectors L π) ≃ₗ[ℂ] ↥(smoothVectors L π') :=
  equivOfForallMemIff U.toLinearEquiv (mem_smoothVectors_iff_of_intertwines L U hU)

@[simp]
theorem coe_smoothEquiv (U : π.H ≃ₗᵢ[ℂ] π'.H) (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v))
    (v : ↥(smoothVectors L π)) : (smoothEquiv L U hU v : π'.H) = U v := rfl

theorem smoothEquiv_smoothAction (U : π.H ≃ₗᵢ[ℂ] π'.H)
    (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v)) (g : G) (v : ↥(smoothVectors L π)) :
    smoothEquiv L U hU (smoothAction L π g v) = smoothAction L π' g (smoothEquiv L U hU v) :=
  Subtype.ext (hU g v)

/-- A unitary intertwiner intertwines the derived actions: `U dπ(X) = dπ'(X) U`. -/
theorem smoothEquiv_derivative (U : π.H ≃ₗᵢ[ℂ] π'.H) (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v))
    (X : LeftInvariantDerivation 𝓘(ℝ, L.E) G) (v : ↥(smoothVectors L π)) :
    smoothEquiv L U hU (derivative L π X v) = derivative L π' X (smoothEquiv L U hU v) := by
  have := L.t2Space
  apply Subtype.ext
  rw [coe_smoothEquiv, derivative_apply, derivative_apply, coe_smoothEquiv]
  set U' : π.H →L[ℝ] π'.H := U.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have hv : ContRepresentation.IsLieSmoothVector 𝓘(ℝ, L.E) π.toContRepresentation (v : π.H) :=
    v.property
  have h := U'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hv.hasDerivAt_lieDerivative X)
  have hfun : (U' ∘ fun t : ℝ => π.toContRepresentation (lieExp (t • X)) (v : π.H)) =
      fun t => π'.ρ (lieExp (t • X)) (U v) := by
    funext t
    simp only [Function.comp_apply, U']
    exact hU _ _
  rw [hfun] at h
  rw [h.deriv]
  rfl

theorem smoothEquiv_derivedAction (U : π.H ≃ₗᵢ[ℂ] π'.H)
    (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v)) (Xs : List (LeftInvariantDerivation 𝓘(ℝ, L.E) G))
    (v : ↥(smoothVectors L π)) :
    smoothEquiv L U hU (derivedAction L π Xs v) =
      derivedAction L π' Xs (smoothEquiv L U hU v) := by
  induction Xs generalizing v with
  | nil => rfl
  | cons X Xs ih =>
    rw [derivedAction_cons, derivedAction_cons, mul_apply_eq_comp, mul_apply_eq_comp,
      smoothEquiv_derivative, ih]

/-- A unitary intertwiner preserves the seminorms of `π^∞`. -/
theorem smoothSeminorm_smoothEquiv (U : π.H ≃ₗᵢ[ℂ] π'.H)
    (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v)) (Xs : List (LeftInvariantDerivation 𝓘(ℝ, L.E) G))
    (v : ↥(smoothVectors L π)) :
    smoothSeminorm L π' Xs (smoothEquiv L U hU v) = smoothSeminorm L π Xs v := by
  rw [smoothSeminorm_apply, smoothSeminorm_apply, ← smoothEquiv_derivedAction, coe_smoothEquiv,
    LinearIsometryEquiv.norm_map]

/-- A unitary intertwiner is bounded for the seminorms of `π^∞` and `π'^∞`. -/
theorem isBounded_smoothEquiv (U : π.H ≃ₗᵢ[ℂ] π'.H) (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v)) :
    Seminorm.IsBounded (smoothSeminorm L π) (smoothSeminorm L π')
      (smoothEquiv L U hU : ↥(smoothVectors L π) →ₗ[ℂ] ↥(smoothVectors L π')) := fun i =>
  ⟨{i}, 1, fun v => by simp [smoothSeminorm_smoothEquiv]⟩

theorem isContinuousForm_iff_of_intertwines (U : π.H ≃ₗᵢ[ℂ] π'.H)
    (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v)) (ℓ : Module.Dual ℂ ↥(smoothVectors L π')) :
    IsContinuousForm L π' ℓ ↔ IsContinuousForm L π ((smoothEquiv L U hU).dualMap ℓ) := by
  refine ⟨fun h => h.comp (isBounded_smoothEquiv L U hU), fun h => ?_⟩
  have hb : Seminorm.IsBounded (smoothSeminorm L π') (smoothSeminorm L π)
      ((smoothEquiv L U hU).symm : ↥(smoothVectors L π') →ₗ[ℂ] ↥(smoothVectors L π)) :=
    fun i => ⟨{i}, 1, fun w => by
      simpa [smoothSeminorm_smoothEquiv] using
        (smoothSeminorm_smoothEquiv L U hU i ((smoothEquiv L U hU).symm w)).ge⟩
  have he : (smoothEquiv L U hU).dualMap ℓ ∘ₗ
      ((smoothEquiv L U hU).symm : ↥(smoothVectors L π') →ₗ[ℂ] ↥(smoothVectors L π)) = ℓ := by
    ext w
    simp
  simpa [IsContinuousForm, he] using h.comp hb

theorem mem_equivariantForms_iff_of_intertwines (U : π.H ≃ₗᵢ[ℂ] π'.H)
    (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v)) (S : Subgroup G) (ξ : ↥S → ℂ)
    (ℓ : Module.Dual ℂ ↥(smoothVectors L π')) :
    ℓ ∈ equivariantForms L π' S ξ ↔
      (smoothEquiv L U hU).dualMap ℓ ∈ equivariantForms L π S ξ := by
  set e := smoothEquiv L U hU
  rw [mem_equivariantForms, mem_equivariantForms, isContinuousForm_iff_of_intertwines L U hU]
  refine and_congr_left fun _ => ⟨fun hℓ s v => ?_, fun hℓ s w => ?_⟩
  · simp only [LinearEquiv.dualMap_apply]
    rw [smoothEquiv_smoothAction, hℓ s]
  · have := hℓ s (e.symm w)
    simp only [LinearEquiv.dualMap_apply] at this
    rwa [smoothEquiv_smoothAction, LinearEquiv.apply_symm_apply] at this

/-- `Hom_S(π^∞, ξ) ≅ Hom_S(π'^∞, ξ)` for unitarily equivalent `π, π'`. -/
noncomputable def equivariantFormsEquiv (U : π.H ≃ₗᵢ[ℂ] π'.H)
    (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v)) (S : Subgroup G) (ξ : ↥S → ℂ) :
    ↥(equivariantForms L π' S ξ) ≃ₗ[ℂ] ↥(equivariantForms L π S ξ) :=
  equivOfForallMemIff (smoothEquiv L U hU).dualMap
    (mem_equivariantForms_iff_of_intertwines L U hU S ξ)

/-- The multiplicity is an invariant of the unitary equivalence class. -/
theorem multiplicity_congr (h : UnitaryRep.IsEquivalent π π') (S : Subgroup G) (ξ : ↥S → ℂ) :
    multiplicity L π S ξ = multiplicity L π' S ξ := by
  obtain ⟨U, hU⟩ := h
  unfold multiplicity
  rw [(equivariantFormsEquiv L U hU S ξ).rank_eq]

theorem hasModel_congr (h : UnitaryRep.IsEquivalent π π') (S : Subgroup G) (ξ : ↥S → ℂ) :
    HasModel L π S ξ ↔ HasModel L π' S ξ := by
  rw [hasModel_iff_multiplicity_ne_zero, hasModel_iff_multiplicity_ne_zero,
    multiplicity_congr L h]

end MultCongr

section TraceCongr

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {π π' : UnitaryRep G}

/-- A unitary intertwiner conjugates `π(f)` into `π'(f)`: `π'(f) = U π(f) U⁻¹`. -/
theorem opOf_eq_conj (U : π.H ≃ₗᵢ[ℂ] π'.H) (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v))
    (f : G → ℂ) :
    opOf π' f = (U : π.H →L[ℂ] π'.H) ∘L opOf π f ∘L (U.symm : π'.H →L[ℂ] π.H) :=
  ContinuousLinearMap.ext fun w => by
    simpa using opOf_intertwines U hU f (U.symm w)

theorem opOf_mem_nuclearOperators_congr (h : UnitaryRep.IsEquivalent π π') (f : G → ℂ) :
    opOf π f ∈ TauCeti.nuclearOperators ℂ π.H π.H ↔
      opOf π' f ∈ TauCeti.nuclearOperators ℂ π'.H π'.H := by
  suffices key : ∀ {σ σ' : UnitaryRep G}, UnitaryRep.IsEquivalent σ σ' →
      opOf σ f ∈ TauCeti.nuclearOperators ℂ σ.H σ.H →
        opOf σ' f ∈ TauCeti.nuclearOperators ℂ σ'.H σ'.H from ⟨key h, key h.symm⟩
  rintro σ σ' ⟨U, hU⟩ hT
  rw [opOf_eq_conj U hU]
  exact TauCeti.comp_left_mem_nuclearOperators _ (TauCeti.comp_right_mem_nuclearOperators hT _)

/-- The trace `tr π(f)` is an invariant of the unitary equivalence class. -/
theorem traceOf_congr (h : UnitaryRep.IsEquivalent π π') (f : G → ℂ) :
    traceOf π f = traceOf π' f := by
  by_cases hT : opOf π f ∈ TauCeti.nuclearOperators ℂ π.H π.H
  · obtain ⟨U, hU⟩ := h
    rw [traceOf, traceOf, opOf_eq_conj U hU,
      hilbertTrace_comp_comm _ (TauCeti.comp_right_mem_nuclearOperators hT _),
      ContinuousLinearMap.comp_assoc]
    congr 1
    refine ContinuousLinearMap.ext fun v => ?_
    simp
  · rw [traceOf, traceOf, hilbertTrace_of_notMem hT,
      hilbertTrace_of_notMem fun h' => hT ((opOf_mem_nuclearOperators_congr h f).2 h')]

theorem isCharacterOf_congr (h : UnitaryRep.IsEquivalent π π') :
    IsCharacterOf L π = IsCharacterOf L π' := by
  funext θ
  simp only [IsCharacterOf, opOf_mem_nuclearOperators_congr h, traceOf_congr h]

theorem characterOn_congr (h : UnitaryRep.IsEquivalent π π') (S : Set G) :
    characterOn L π S = characterOn L π' S := by
  unfold characterOn
  rw [isCharacterOf_congr L h]

end TraceCongr

end LieRep

end GSpinGGP
