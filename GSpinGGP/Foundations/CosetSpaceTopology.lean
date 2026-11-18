/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.Measure
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Topology of a coset space

For a topological group `Γ` and `ι : S →* Γ`, the coset space `ι(S)\Γ` (`CosetSpace ι`, right
cosets `ι(S)γ`) is the orbit space of the left action of `ι(S)` on `Γ`. From Mathlib's results on
orbit spaces:

* it is locally compact if `Γ` is (`CosetSpace.instLocallyCompactSpace`), and second countable if
  `Γ` is (`CosetSpace.instSecondCountableTopology`), since the projection is an open quotient map;
* it is Hausdorff if `ι(S)` is closed (`CosetSpace.instT2Space`), since a closed subgroup acts
  properly by left translation.

Consequently, when `Γ` is locally compact and second countable and `ι(S)` is closed, every
Borel measure on `ι(S)\Γ` that is finite on compact sets is regular (in particular outer
regular), by Mathlib's `Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure` (the space is
metrizable by Urysohn's theorem and σ-compact); `CosetSpace.regular_of_isFiniteMeasureOnCompacts`.
-/

open MeasureTheory Topology

namespace GSpinGGP

namespace CosetSpace

variable {S Γ : Type*} [Group S] [Group Γ] [TopologicalSpace Γ] (ι : S →* Γ)

/-- The projection `Γ → ι(S)\Γ` is an open quotient map. -/
theorem isOpenQuotientMap_mk [ContinuousMul Γ] : IsOpenQuotientMap (mk ι) :=
  MulAction.isOpenQuotientMap_quotientMk (Γ := ι.range) (T := Γ)

/-- `ι(S)\Γ` is locally compact if `Γ` is. -/
instance instLocallyCompactSpace [ContinuousMul Γ] [LocallyCompactSpace Γ] :
    LocallyCompactSpace (CosetSpace ι) :=
  (isOpenQuotientMap_mk ι).locallyCompactSpace

/-- `ι(S)\Γ` is second countable if `Γ` is. -/
instance instSecondCountableTopology [ContinuousMul Γ] [SecondCountableTopology Γ] :
    SecondCountableTopology (CosetSpace ι) :=
  ContinuousConstSMul.secondCountableTopology (Γ := ι.range) (T := Γ)

/-- `ι(S)\Γ` is Hausdorff if `ι(S)` is closed: a closed subgroup acts properly on `Γ` by left
translation (`t2Space_quotient_mulAction_of_properSMul`). -/
instance instT2Space [IsTopologicalGroup Γ] [IsClosed (ι.range : Set Γ)] :
    T2Space (CosetSpace ι) :=
  t2Space_quotient_mulAction_of_properSMul (G := ι.range) (X := Γ)

/-- On `ι(S)\Γ`, for `Γ` locally compact and second countable and `ι(S)` closed, a Borel
measure that is finite on compact sets is regular (found by instance search). -/
theorem regular_of_isFiniteMeasureOnCompacts [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [IsClosed (ι.range : Set Γ)] (μ : Measure (CosetSpace ι))
    [IsFiniteMeasureOnCompacts μ] : μ.Regular :=
  inferInstance

end CosetSpace

end GSpinGGP
