/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.Measure

/-!
# Topology of a coset space

For a topological group `Γ` and `ι : S →* Γ`, the coset space `ι(S)\Γ` (`CosetSpace ι`, right
cosets `ι(S)γ`) is the orbit space of the left action of `ι(S)` on `Γ`. From Mathlib's results on
orbit spaces:

* it is locally compact if `Γ` is (`CosetSpace.instLocallyCompactSpace`), and second countable if
  `Γ` is (`CosetSpace.instSecondCountableTopology`), since the projection is an open quotient map;
* it is Hausdorff if `ι(S)` is closed (`CosetSpace.instT2Space`), since a closed subgroup acts
  properly by left translation.

Consequently, when `Γ` is locally compact and second countable and `ι(S)` is closed, instance
search shows every Borel measure on `ι(S)\Γ` that is finite on compact sets to be outer regular
(the space is metrizable by Urysohn's theorem; Mathlib's
`WeaklyRegular.of_pseudoMetrizableSpace_secondCountable_of_locallyFinite`).
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

end CosetSpace

end GSpinGGP
