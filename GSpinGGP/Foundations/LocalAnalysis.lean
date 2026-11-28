/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.RealLieStructureOfClosed
import GSpinGGP.Foundations.RealEmbeddingClassification

/-!
# Analytic notions over a local field, by case on the field

For a local field `F`, a finite-dimensional `F`-algebra `A` with its module topology and a
subgroup `G ≤ Aˣ`, the representation-theoretic notions attached to `G(F) = G` are those of
`GSpinGGP/Foundations/Representations.lean` when `F` is non-archimedean (`G` is totally
disconnected) and those of `GSpinGGP/Foundations/LieRepresentations.lean` when `F` is archimedean
(`G` is a real Lie group). This file defines each notion once over `F`, by case on whether the
norm of `F` is ultrametric:

* `localTestFunctions F G`: `C_c^∞(G)` (locally constant, resp. smooth, with compact support);
* `localMultiplicity F π S ξ`: `dim Hom_S(π^∞, ξ)` (all forms, resp. continuous forms);
* `LocalHasModel F π S ξ`: a nonzero `(S, ξ)`-equivariant form exists;
* `localTraceOf F π f`: `tr π(f)`;
* `LocalIsCharacterOf F π θ`, `localCharacterOn F π S`: the Harish-Chandra character.

Only notions whose type does not depend on the case are split (not `π^∞` or the space of forms).
The field `F` is an explicit argument, since it cannot be read off `G` or `π`; otherwise each
notion has the argument order and the instance arguments of its `p`-adic namesake, except
`localTraceOf`, which takes neither `[LocalField F]` nor the algebra instances on `A` (neither of
its branches needs a Lie structure).

In the archimedean case the Lie structure on `G` is `archLieStructure? F G`: the structure
`φ.realLieStructure G hG` of `GSpinGGP/Foundations/RealLieStructureOfClosed.lean`, for the real
embedding `φ : ℝ →+* F` (there is at most one, `RealEmbedding.instSubsingleton`, so this is no
choice) when it exists and `G` is closed, and `none` otherwise. For a local field a real embedding
exists exactly when `F` is not ultrametric (`not_isUltrametricDist_iff_nonempty_realEmbedding`),
so for closed `G` the value `none`, and with it the junk values of the selectors, is never reached
(`isSome_archLieStructure?_iff`). The other choices inside `realLieStructure` (a basis of `A`, the
slice charts) do not affect `C_c^∞(G)`, `π^∞` and the character
(`RealLieStructure.testFunctions_eq`, `RealLieStructure.smoothVectors_eq`,
`RealLieStructure.isCharacterOf_iff`, `RealLieStructure.characterOn_eq`); for the seminorms, the
continuous and equivariant forms, the multiplicity and `HasModel` this is not yet proved.

The definitions are reduced only through the lemmas `…_of_isUltrametricDist` (the `p`-adic notion)
and `…_of_not_isUltrametricDist` (the notion of `LieRep` at `φ.realLieStructure G hG`, for closed
`G` and any real embedding `φ`, by default the one given by the classification).

## Main definitions

* `archLieStructure? F G : Option (RealLieStructure G)`.
* `localTestFunctions`, `localMultiplicity`, `LocalHasModel`, `localTraceOf`,
  `LocalIsCharacterOf`, `localCharacterOn`.

## Main results

* `archLieStructure?_eq_some`, `isSome_archLieStructure?_iff`.
* `…_of_isUltrametricDist` and `…_of_not_isUltrametricDist` for each notion.
* `localHasModel_iff_localMultiplicity_ne_zero`, and invariance under unitary equivalence:
  `localMultiplicity_congr`, `localHasModel_congr`, `localTraceOf_congr`,
  `localIsCharacterOf_congr`, `localCharacterOn_congr`; `localCharacterOn_spec`.
-/

namespace GSpinGGP

attribute [local instance] Classical.propDecidable

variable (F : Type*) [NontriviallyNormedField F] [LocalField F]
  {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A] [IsModuleTopology F A]

/-! ### The real Lie structure in the archimedean case -/

/-- The real Lie structure of a subgroup `G ≤ Aˣ`: `φ.realLieStructure G hG` when `F` has a real
embedding `φ` (unique, `RealEmbedding.instSubsingleton`) and `G` is closed; `none` otherwise.
For a local field a real embedding exists if and only if `F` is not ultrametric. -/
noncomputable def archLieStructure? (G : Subgroup Aˣ) : Option (RealLieStructure ↥G) :=
  if h : Nonempty (RealEmbedding F) ∧ IsClosed (G : Set Aˣ) then
    some (h.1.some.realLieStructure G h.2)
  else none

/-- For a real embedding `φ` and closed `G`, the Lie structure is the one built from `φ`. -/
theorem archLieStructure?_eq_some (φ : RealEmbedding F) (G : Subgroup Aˣ)
    (hG : IsClosed (G : Set Aˣ)) :
    archLieStructure? F G = some (φ.realLieStructure G hG) := by
  rw [archLieStructure?, dite_eq_left ⟨⟨φ⟩, hG⟩, Subsingleton.elim (Nonempty.some _) φ]

theorem archLieStructure?_eq_none_of_not_isClosed {G : Subgroup Aˣ}
    (hG : ¬ IsClosed (G : Set Aˣ)) : archLieStructure? F G = none :=
  dite_eq_right fun h => hG h.2

theorem archLieStructure?_eq_none [IsUltrametricDist F] (G : Subgroup Aˣ) :
    archLieStructure? F G = none :=
  dite_eq_right fun h => IsEmpty.false h.1.some

/-- For closed `G`, the archimedean Lie structure exists exactly when `F` is not ultrametric
(the classification of local fields with a real embedding,
`not_isUltrametricDist_iff_nonempty_realEmbedding`). So the junk branches of the selectors below
are not reached for closed `G`. -/
theorem isSome_archLieStructure?_iff {G : Subgroup Aˣ} (hG : IsClosed (G : Set Aˣ)) :
    (archLieStructure? F G).isSome ↔ ¬ IsUltrametricDist F := by
  rw [archLieStructure?, Option.isSome_dite, not_isUltrametricDist_iff_nonempty_realEmbedding,
    and_iff_left hG]

variable {F}

/-! ### The selectors -/

section Selectors

variable {G : Subgroup Aˣ}

variable (F) in
/-- `C_c^∞(G)`: locally constant compactly supported functions if `F` is non-archimedean
(`testFunctions`), smooth compactly supported functions if `F` is archimedean
(`LieRep.testFunctions`; `⊥` in the unreachable case without a Lie structure). -/
noncomputable def localTestFunctions (G : Subgroup Aˣ) : Submodule ℂ (↥G → ℂ) :=
  if IsUltrametricDist F then testFunctions ↥G
  else (archLieStructure? F G).elim ⊥ LieRep.testFunctions

section Multiplicity

variable [IsTopologicalGroup ↥G]

variable (F) in
/-- The multiplicity `m(π) = dim Hom_S(π^∞, ξ)`: `multiplicity` (all linear forms on `π^∞`) if
`F` is non-archimedean, `LieRep.multiplicity` (continuous forms) if `F` is archimedean (`0` in the
unreachable case without a Lie structure). -/
noncomputable def localMultiplicity (π : UnitaryRep ↥G) (S : Subgroup ↥G) (ξ : ↥S → ℂ) : ℕ∞ :=
  if IsUltrametricDist F then multiplicity π S ξ
  else (archLieStructure? F G).elim 0 fun L => LieRep.multiplicity L π S ξ

variable (F) in
/-- `π` has an `(S, ξ)`-model: `HasModel` if `F` is non-archimedean, `LieRep.HasModel` (a nonzero
continuous form) if `F` is archimedean (`False` in the unreachable case without a Lie
structure). -/
def LocalHasModel (π : UnitaryRep ↥G) (S : Subgroup ↥G) (ξ : ↥S → ℂ) : Prop :=
  if IsUltrametricDist F then HasModel π S ξ
  else (archLieStructure? F G).elim False fun L => LieRep.HasModel L π S ξ

end Multiplicity

section Characters

variable [IsTopologicalGroup ↥G] [LocallyCompactSpace ↥G]
  [MeasurableSpace ↥G] [BorelSpace ↥G]

variable (F) in
/-- `tr π(f)`: the trace on the `K`-fixed vectors (`traceOf`) if `F` is non-archimedean, the
trace of the nuclear operator `π(f)` (`LieRep.traceOf`) if `F` is archimedean. Neither depends on
a Lie structure. -/
noncomputable def localTraceOf (π : UnitaryRep ↥G) (f : ↥G → ℂ) : ℂ :=
  if IsUltrametricDist F then traceOf π f else LieRep.traceOf π f

variable (F) in
/-- `θ` is the Harish-Chandra character of `π`: `IsCharacterOf` if `F` is non-archimedean,
`LieRep.IsCharacterOf` if `F` is archimedean (`False` in the unreachable case without a Lie
structure). -/
def LocalIsCharacterOf (π : UnitaryRep ↥G) (θ : ↥G → ℂ) : Prop :=
  if IsUltrametricDist F then IsCharacterOf π θ
  else (archLieStructure? F G).elim False fun L => LieRep.IsCharacterOf L π θ

variable (F) in
/-- The character `θ_π`, normalised to be continuous on `S`: `characterOn` if `F` is
non-archimedean, `LieRep.characterOn` if `F` is archimedean (`0` in the unreachable case without
a Lie structure). In either branch the value is `0` when `π` has no character function continuous
on `S`; over `ℝ` and `ℂ` its existence (on the regular set) is Harish-Chandra's regularity theorem,
which is not assumed in this file. -/
noncomputable def localCharacterOn (π : UnitaryRep ↥G) (S : Set ↥G) : ↥G → ℂ :=
  if IsUltrametricDist F then characterOn π S
  else (archLieStructure? F G).elim 0 fun L => LieRep.characterOn L π S

end Characters

end Selectors

/-! ### Reduction in the non-archimedean case -/

section Ultrametric

variable [IsUltrametricDist F] {G : Subgroup Aˣ}

@[simp]
theorem localTestFunctions_of_isUltrametricDist :
    localTestFunctions F G = testFunctions ↥G :=
  ite_eq_left ‹_›

variable [IsTopologicalGroup ↥G]

@[simp]
theorem localMultiplicity_of_isUltrametricDist (π : UnitaryRep ↥G) (S : Subgroup ↥G)
    (ξ : ↥S → ℂ) : localMultiplicity F π S ξ = multiplicity π S ξ :=
  ite_eq_left ‹_›

@[simp]
theorem localHasModel_of_isUltrametricDist (π : UnitaryRep ↥G) (S : Subgroup ↥G) (ξ : ↥S → ℂ) :
    LocalHasModel F π S ξ = HasModel π S ξ :=
  ite_eq_left ‹_›

variable [LocallyCompactSpace ↥G] [MeasurableSpace ↥G] [BorelSpace ↥G]

omit [LocalField F] [Algebra F A] [Module.Finite F A] [IsModuleTopology F A] in
@[simp]
theorem localTraceOf_of_isUltrametricDist (π : UnitaryRep ↥G) (f : ↥G → ℂ) :
    localTraceOf F π f = traceOf π f :=
  ite_eq_left ‹_›

@[simp]
theorem localIsCharacterOf_of_isUltrametricDist (π : UnitaryRep ↥G) (θ : ↥G → ℂ) :
    LocalIsCharacterOf F π θ = IsCharacterOf π θ :=
  ite_eq_left ‹_›

@[simp]
theorem localCharacterOn_of_isUltrametricDist (π : UnitaryRep ↥G) (S : Set ↥G) :
    localCharacterOn F π S = characterOn π S :=
  ite_eq_left ‹_›

end Ultrametric

/-! ### Reduction in the archimedean case

For `F` not ultrametric and `G` closed, each selector is the `LieRep` notion at
`φ.realLieStructure G hG`. The real embedding `φ` is an optional argument; its default is the one
given by the classification (`nonempty_realEmbedding_of_not_isUltrametricDist`), and any other
choice gives the same value, `RealEmbedding` being a subsingleton. -/

section Archimedean

variable {G : Subgroup Aˣ} (h : ¬ IsUltrametricDist F) (hG : IsClosed (G : Set Aˣ))

include h hG

theorem localTestFunctions_of_not_isUltrametricDist
    (φ : RealEmbedding F := (nonempty_realEmbedding_of_not_isUltrametricDist h).some) :
    localTestFunctions F G = LieRep.testFunctions (φ.realLieStructure G hG) := by
  rw [localTestFunctions, ite_eq_right h, archLieStructure?_eq_some F φ G hG]
  rfl

variable [IsTopologicalGroup ↥G]

theorem localMultiplicity_of_not_isUltrametricDist (π : UnitaryRep ↥G) (S : Subgroup ↥G)
    (ξ : ↥S → ℂ)
    (φ : RealEmbedding F := (nonempty_realEmbedding_of_not_isUltrametricDist h).some) :
    localMultiplicity F π S ξ = LieRep.multiplicity (φ.realLieStructure G hG) π S ξ := by
  rw [localMultiplicity, ite_eq_right h, archLieStructure?_eq_some F φ G hG]
  rfl

theorem localHasModel_of_not_isUltrametricDist (π : UnitaryRep ↥G) (S : Subgroup ↥G)
    (ξ : ↥S → ℂ)
    (φ : RealEmbedding F := (nonempty_realEmbedding_of_not_isUltrametricDist h).some) :
    LocalHasModel F π S ξ = LieRep.HasModel (φ.realLieStructure G hG) π S ξ := by
  rw [LocalHasModel, ite_eq_right h, archLieStructure?_eq_some F φ G hG]
  rfl

variable [LocallyCompactSpace ↥G] [MeasurableSpace ↥G] [BorelSpace ↥G]

omit hG [LocalField F] [Algebra F A] [Module.Finite F A] [IsModuleTopology F A] in
/-- `localTraceOf` needs neither a Lie structure nor closedness of `G`. -/
theorem localTraceOf_of_not_isUltrametricDist (π : UnitaryRep ↥G) (f : ↥G → ℂ) :
    localTraceOf F π f = LieRep.traceOf π f :=
  ite_eq_right h

theorem localIsCharacterOf_of_not_isUltrametricDist (π : UnitaryRep ↥G) (θ : ↥G → ℂ)
    (φ : RealEmbedding F := (nonempty_realEmbedding_of_not_isUltrametricDist h).some) :
    LocalIsCharacterOf F π θ = LieRep.IsCharacterOf (φ.realLieStructure G hG) π θ := by
  rw [LocalIsCharacterOf, ite_eq_right h, archLieStructure?_eq_some F φ G hG]
  rfl

theorem localCharacterOn_of_not_isUltrametricDist (π : UnitaryRep ↥G) (S : Set ↥G)
    (φ : RealEmbedding F := (nonempty_realEmbedding_of_not_isUltrametricDist h).some) :
    localCharacterOn F π S = LieRep.characterOn (φ.realLieStructure G hG) π S := by
  rw [localCharacterOn, ite_eq_right h, archLieStructure?_eq_some F φ G hG]
  rfl

end Archimedean

/-! ### Relations valid in both cases -/

section Relations

variable {G : Subgroup Aˣ} [IsTopologicalGroup ↥G] {π π' : UnitaryRep ↥G}

theorem localHasModel_iff_localMultiplicity_ne_zero (π : UnitaryRep ↥G) (S : Subgroup ↥G)
    (ξ : ↥S → ℂ) : LocalHasModel F π S ξ ↔ localMultiplicity F π S ξ ≠ 0 := by
  unfold LocalHasModel localMultiplicity
  split_ifs
  · exact hasModel_iff_multiplicity_ne_zero π S ξ
  · cases archLieStructure? F G with
    | none => simp
    | some L => exact LieRep.hasModel_iff_multiplicity_ne_zero L π S ξ

/-- The multiplicity is an invariant of the unitary equivalence class. -/
theorem localMultiplicity_congr (he : UnitaryRep.IsEquivalent π π') (S : Subgroup ↥G)
    (ξ : ↥S → ℂ) : localMultiplicity F π S ξ = localMultiplicity F π' S ξ := by
  unfold localMultiplicity
  split_ifs
  · exact multiplicity_congr he S ξ
  · cases archLieStructure? F G with
    | none => rfl
    | some L => exact LieRep.multiplicity_congr L he S ξ

theorem localHasModel_congr (he : UnitaryRep.IsEquivalent π π') (S : Subgroup ↥G)
    (ξ : ↥S → ℂ) : LocalHasModel F π S ξ ↔ LocalHasModel F π' S ξ := by
  rw [localHasModel_iff_localMultiplicity_ne_zero, localHasModel_iff_localMultiplicity_ne_zero,
    localMultiplicity_congr he]

variable [LocallyCompactSpace ↥G] [MeasurableSpace ↥G] [BorelSpace ↥G]

omit [LocalField F] [Algebra F A] [Module.Finite F A] [IsModuleTopology F A] in
/-- The trace `tr π(f)` is an invariant of the unitary equivalence class. -/
theorem localTraceOf_congr (he : UnitaryRep.IsEquivalent π π') (f : ↥G → ℂ) :
    localTraceOf F π f = localTraceOf F π' f := by
  unfold localTraceOf
  split_ifs
  · exact traceOf_congr he f
  · exact LieRep.traceOf_congr he f

theorem localIsCharacterOf_congr (he : UnitaryRep.IsEquivalent π π') :
    LocalIsCharacterOf F π = LocalIsCharacterOf F π' := by
  funext θ
  unfold LocalIsCharacterOf
  split_ifs
  · rw [isCharacterOf_congr he]
  · cases archLieStructure? F G with
    | none => rfl
    | some L => exact congrFun (LieRep.isCharacterOf_congr L he) θ

theorem localCharacterOn_congr (he : UnitaryRep.IsEquivalent π π') (S : Set ↥G) :
    localCharacterOn F π S = localCharacterOn F π' S := by
  unfold localCharacterOn
  split_ifs
  · exact characterOn_congr he S
  · cases archLieStructure? F G with
    | none => rfl
    | some L => exact LieRep.characterOn_congr L he S

/-- If `π` has a character continuous on `S`, then `localCharacterOn F π S` is one. -/
theorem localCharacterOn_spec (π : UnitaryRep ↥G) (S : Set ↥G)
    (h : ∃ θ, LocalIsCharacterOf F π θ ∧ ContinuousOn θ S) :
    LocalIsCharacterOf F π (localCharacterOn F π S) ∧ ContinuousOn (localCharacterOn F π S) S := by
  unfold LocalIsCharacterOf localCharacterOn at *
  split_ifs at * with hF
  · exact characterOn_spec π S h
  · revert h
    cases archLieStructure? F G with
    | none => simp
    | some L => exact LieRep.characterOn_spec L π S

end Relations

end GSpinGGP
