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

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
  {A : Type*} [Ring A] [Algebra F A] [TopologicalSpace A] [Module.Finite F A] [IsModuleTopology F A]

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
  haveI := t2Space_of_moduleTopology F A
  haveI := isTopologicalRing_of_moduleTopology F A
  have hind : IsInducing (𝔤.incl.toLinearMap : ↥𝔤 → A) := IsInducing.subtypeVal
  haveI : IsTopologicalAddGroup ↥𝔤 := hind.isTopologicalAddGroup 𝔤.incl.toLinearMap
  haveI : ContinuousSMul F ↥𝔤 :=
    hind.continuousSMul continuous_id (fun {c x} => 𝔤.incl.toLinearMap.map_smul c x)
  -- `𝔤 ≅ F^n` as topological vector spaces
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let e : ↥𝔤 ≃L[F] (Fin (Module.finrank F ↥𝔤) → F) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  haveI : LocallyCompactSpace ↥𝔤 := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : TotallyDisconnectedSpace ↥𝔤 := e.toHomeomorph.symm.totallyDisconnectedSpace
  haveI : SigmaCompactSpace ↥𝔤 := e.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  haveI : SecondCountableTopology ↥𝔤 := e.toHomeomorph.isEmbedding.secondCountableTopology
  -- the self-dual measure
  have hex : ∃ μ, IsSelfDual μ (restrictForm 𝔤 b) ψ :=
    exists_isSelfDual_of_isInducing 𝔤.incl.toLinearMap hind Subtype.val_injective _ hnd ψ
  have hμ : IsSelfDual (selfDualHaar 𝔤 b ψ) (restrictForm 𝔤 b) ψ := by
    unfold selfDualHaar selfDualMeasure
    rw [dif_pos hex]
    exact hex.choose_spec
  haveI := hμ.1
  haveI : TopologicalSpace.PseudoMetrizableSpace ↥𝔤 :=
    e.toHomeomorph.isEmbedding.pseudoMetrizableSpace
  exact jHat_add_eq O hμ Y hbY hreg hU hUreg hX

end GSpinGGP
