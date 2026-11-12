/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.JHatTranslate
import GSpinGGP.Literature.Fourier

/-!
# `ĵ(O, ·)` under central translation, for a nondegenerate form

`jHat_add_eq_of_nondegenerate`: `jHat_add_eq` with its topological and measure-theoretic
hypotheses discharged when `b` is nondegenerate on `𝔤`, using the existence of the self-dual
measure (`exists_isSelfDual`).
-/

noncomputable section

open MeasureTheory Filter Topology

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.style.haveILetI false

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
  {A : Type*} [Ring A] [Algebra F A] [TopologicalSpace A] [Module.Finite F A] [IsModuleTopology F A]

/-- A Lie subalgebra of the ambient algebra is a topological additive group. -/
theorem isTopologicalAddGroup_lieSubalgebra (𝔤 : LieSubalgebra F A) : IsTopologicalAddGroup ↥𝔤 :=
  submodule_isTopologicalAddGroup 𝔤.toSubmodule

/-- `𝔤 ≅ F^n` gives `𝔤` the instances needed for self-dual measures and for
`eqOn_of_isJHat` (`submodule_isModuleTopology`). -/
theorem isModuleTopology_lieSubalgebra (𝔤 : LieSubalgebra F A) : IsModuleTopology F ↥𝔤 :=
  submodule_isModuleTopology 𝔤.toSubmodule

/-- The topological properties of a Lie subalgebra `𝔤 ≅ F^n` used for Haar measures and
`eqOn_of_isJHat` (`submodule_topology`). -/
theorem lieSubalgebra_topology (𝔤 : LieSubalgebra F A) :
    LocallyCompactSpace ↥𝔤 ∧ TotallyDisconnectedSpace ↥𝔤 ∧ SigmaCompactSpace ↥𝔤 ∧
      SecondCountableTopology ↥𝔤 ∧ TopologicalSpace.PseudoMetrizableSpace ↥𝔤 :=
  submodule_topology 𝔤.toSubmodule

/-- The self-dual measure on a Lie subalgebra on which `b` is nondegenerate is self-dual
(it exists, `exists_isSelfDual`). -/
theorem isSelfDual_selfDualHaar_of_nondegenerate (𝔤 : LieSubalgebra F A)
    {b : LinearMap.BilinForm F A} (hnd : (restrictForm 𝔤 b).Nondegenerate) (ψ : NontrivialAddChar F) :
    IsSelfDual (selfDualHaar 𝔤 b ψ) (restrictForm 𝔤 b) ψ := by
  haveI := t2Space_of_moduleTopology F A
  haveI := isTopologicalRing_of_moduleTopology F A
  have hind : IsInducing (𝔤.incl.toLinearMap : ↥𝔤 → A) := IsInducing.subtypeVal
  have hex : ∃ μ, IsSelfDual μ (restrictForm 𝔤 b) ψ :=
    exists_isSelfDual_of_isInducing 𝔤.incl.toLinearMap hind Subtype.val_injective _ hnd ψ
  unfold selfDualHaar selfDualMeasure
  rw [dif_pos hex]
  exact hex.choose_spec

/-- **`ĵ(O, ·)` is invariant under translation by `Y`**, for a Lie subalgebra `𝔤` on which `b` is
nondegenerate: `jHat_add_eq` with its topological and measure-theoretic hypotheses discharged
(`𝔤` is linearly homeomorphic to `F^n`; the self-dual measure exists, `exists_isSelfDual`, and is
regular, being a Haar measure on a second-countable locally compact group). -/
theorem jHat_add_eq_of_nondegenerate {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A}
    {b : LinearMap.BilinForm F A} {ψ : NontrivialAddChar F} (O : NilOrbit G 𝔤)
    (hnd : (restrictForm 𝔤 b).Nondegenerate) (Y : ↥𝔤)
    (hbY : ∀ N : ↥𝔤, IsNilpotent (N : A) → b (Y : A) (N : A) = 0)
    (hreg : ∀ Z : ↥𝔤, IsRegularSS 𝔤 ((Z + Y : ↥𝔤) : A) ↔ IsRegularSS 𝔤 (Z : A))
    {U : Set ↥𝔤} (hU : IsOpen U) (hUreg : U ⊆ {X | IsRegularSS 𝔤 (X : A)}) {X : ↥𝔤} (hX : X ∈ U) :
    jHat G 𝔤 b ψ O ((X : A) + (Y : A)) = jHat G 𝔤 b ψ O (X : A) := by
  obtain ⟨_, _, _, _, _⟩ := lieSubalgebra_topology 𝔤
  haveI := isTopologicalAddGroup_lieSubalgebra 𝔤
  haveI := isModuleTopology_lieSubalgebra 𝔤
  haveI := t2Space_of_moduleTopology F A
  have hμ := isSelfDual_selfDualHaar_of_nondegenerate 𝔤 hnd ψ
  haveI := hμ.1
  exact jHat_add_eq O hμ Y hbY hreg hU hUreg hX

end GSpinGGP
