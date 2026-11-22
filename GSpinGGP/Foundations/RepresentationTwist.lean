/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.Representations
import TauCeti.RepresentationTheory.Character.Twist

/-!
# Twisting a continuous representation by a character

For a continuous representation `π` of `G` on a topological module `V` and a character
`χ : G →* kˣ`, the twist `π ⊗ χ` acts on the same space by `g ↦ χ(g) • π(g)`
(`ContRepresentation.charTwist`).  Its underlying linear representation is Tau Ceti's
`Representation.charTwist` (`toRepresentation_charTwist`), which identifies it with the tensor
product with the line of `χ`.  The twist by a character of absolute value `1` of a unitary
representation is unitary (`ContRepresentation.IsUnitary.charTwist`).

For unitary representations on Hilbert spaces (`UnitaryRep`) and continuous unitary characters
`χ : G →ₜ* Circle` this gives `UnitaryRep.twist π χ` (Beuzart-Plessis, Astérisque 418, §2.2:
"`π_λ` acts on the same space as `π` and `π_λ(g) = e^{λ(H_G(g))} π(g)`"; Thesis §3.1.2).

## Main definitions

* `ContRepresentation.charTwist χ π`: `g ↦ χ(g) • π(g)`.
* `UnitaryRep.twist π χ`: the twist of a unitary representation by a continuous unitary character.

## Main results

* `ContRepresentation.toRepresentation_charTwist`, `charTwist_one`, `charTwist_charTwist`.
* `ContRepresentation.IsUnitary.charTwist`: twisting by a character with `‖χ g‖ = 1` preserves
  unitarity.
* `UnitaryRep.isEquivalent_twist_one`, `UnitaryRep.isEquivalent_twist_twist`,
  `UnitaryRep.IsEquivalent.twist`: the twists are an action of the character group on unitary
  equivalence classes.
* `UnitaryRep.isIrreducible_twist_iff`: the twist is irreducible iff `π` is (same closed invariant
  subspaces).
-/

open scoped InnerProductSpace

namespace ContRepresentation

section CommRing

variable {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module k V] [ContinuousConstSMul k V]

/-- **The twist of a continuous representation by a character** `χ : G →* kˣ`: the same space,
with `π(g)` rescaled by `χ(g)`.  Its linear representation is Tau Ceti's
`Representation.charTwist` (`toRepresentation_charTwist`). -/
def charTwist (χ : G →* kˣ) (π : ContRepresentation k G V) : ContRepresentation k G V :=
  .ofMonoidHom
    { toFun := fun g => (χ g : k) • π g
      map_one' := by ext v; simp
      map_mul' := fun g h => by
        ext v
        change ((χ (g * h) : kˣ) : k) • π (g * h) v = (χ g : k) • π g ((χ h : k) • π h v)
        rw [map_mul, map_mul, map_smul, smul_smul, Units.val_mul]
        rfl }

@[simp]
theorem charTwist_apply (χ : G →* kˣ) (π : ContRepresentation k G V) (g : G) :
    charTwist χ π g = (χ g : k) • π g :=
  rfl

theorem charTwist_apply_apply (χ : G →* kˣ) (π : ContRepresentation k G V) (g : G) (v : V) :
    charTwist χ π g v = (χ g : k) • π g v :=
  rfl

/-- The linear representation underlying the twist is Tau Ceti's `Representation.charTwist`. -/
theorem toRepresentation_charTwist (χ : G →* kˣ) (π : ContRepresentation k G V) :
    (charTwist χ π).toRepresentation = Representation.charTwist χ π.toRepresentation :=
  MonoidHom.ext fun _ => LinearMap.ext fun _ => rfl

/-- Twisting by the trivial character changes nothing. -/
@[simp]
theorem charTwist_one (π : ContRepresentation k G V) : charTwist (1 : G →* kˣ) π = π := by
  apply DFunLike.coe_injective
  funext g
  simp

/-- Twisting twice multiplies the characters. -/
theorem charTwist_charTwist (χ ψ : G →* kˣ) (π : ContRepresentation k G V) :
    charTwist χ (charTwist ψ π) = charTwist (χ * ψ) π := by
  apply DFunLike.coe_injective
  funext g
  simp [smul_smul]

/-- The orbit maps of the twist are continuous when those of `π` and the character are. -/
theorem continuous_charTwist_apply [TopologicalSpace G] [TopologicalSpace k]
    [ContinuousSMul k V] {χ : G →* kˣ} (hχ : Continuous fun g => (χ g : k))
    {π : ContRepresentation k G V} {v : V} (hv : Continuous fun g => π g v) :
    Continuous fun g => charTwist χ π g v :=
  hχ.smul hv

end CommRing

section Unitary

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- **The twist of a unitary representation by a character of absolute value `1` is unitary.** -/
theorem IsUnitary.charTwist {π : ContRepresentation 𝕜 G V} (hπ : IsUnitary π) {χ : G →* 𝕜ˣ}
    (hχ : ∀ g, ‖(χ g : 𝕜)‖ = 1) : IsUnitary (charTwist χ π) := by
  rw [isUnitary_iff_norm_map] at hπ ⊢
  intro g v
  rw [charTwist_apply_apply, norm_smul, hχ, one_mul, hπ]

end Unitary

end ContRepresentation

namespace GSpinGGP

universe u

namespace UnitaryRep

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **The twist `π ⊗ χ` of a unitary representation by a continuous unitary character**
(Beuzart-Plessis, Astérisque 418, §2.2, p. 40; Thesis §3.1.2): the same Hilbert space, with
`(π ⊗ χ)(g) = χ(g) π(g)`. -/
noncomputable def twist (π : UnitaryRep G) (χ : G →ₜ* Circle) : UnitaryRep G where
  H := π.H
  toContRepresentation :=
    π.toContRepresentation.charTwist (Circle.toUnits.comp (χ : G →* Circle))
  isUnitary := π.isUnitary.charTwist fun g => Circle.norm_coe (χ g)
  strongCont v :=
    ContRepresentation.continuous_charTwist_apply
      (continuous_subtypeVal.comp χ.continuous) (π.strongCont v)

theorem twist_ρ_apply (π : UnitaryRep G) (χ : G →ₜ* Circle) (g : G) (v : π.H) :
    (π.twist χ).ρ g v = ((χ g : Circle) : ℂ) • π.ρ g v :=
  rfl

/-- **Twisting by the trivial character changes nothing** (up to the identity equivalence). -/
theorem isEquivalent_twist_one (π : UnitaryRep G) : (π.twist 1).IsEquivalent π :=
  ⟨LinearIsometryEquiv.refl ℂ π.H, fun g v => by
    change (((1 : Circle) : ℂ) • π.ρ g v) = π.ρ g v
    rw [Circle.coe_one, one_smul]⟩

/-- **Twisting twice multiplies the characters.** -/
theorem isEquivalent_twist_twist (π : UnitaryRep G) (χ ψ : G →ₜ* Circle) :
    ((π.twist χ).twist ψ).IsEquivalent (π.twist (χ * ψ)) :=
  ⟨LinearIsometryEquiv.refl ℂ π.H, fun g v => by
    change ((ψ g : Circle) : ℂ) • ((χ g : Circle) : ℂ) • π.ρ g v =
      (((χ * ψ) g : Circle) : ℂ) • π.ρ g v
    rw [smul_smul, ContinuousMonoidHom.mul_apply, Circle.coe_mul, mul_comm]⟩

/-- **Twisting respects unitary equivalence.** -/
theorem IsEquivalent.twist {π π' : UnitaryRep G} (h : π.IsEquivalent π') (χ : G →ₜ* Circle) :
    (π.twist χ).IsEquivalent (π'.twist χ) := by
  obtain ⟨U, hU⟩ := h
  exact ⟨U, fun g v => by
    change U (((χ g : Circle) : ℂ) • π.ρ g v) = ((χ g : Circle) : ℂ) • π'.ρ g (U v)
    rw [map_smul]
    exact congrArg (((χ g : Circle) : ℂ) • ·) (hU g v)⟩

/-- **The twist of `π` is irreducible iff `π` is**: a subspace is stable under `χ(g) π(g)` iff it
is stable under `π(g)`, since `χ(g) ≠ 0`. -/
theorem isIrreducible_twist_iff (π : UnitaryRep G) (χ : G →ₜ* Circle) :
    (π.twist χ).IsIrreducible ↔ π.IsIrreducible := by
  have key : ∀ W : Submodule ℂ π.H,
      (∀ g, ∀ v ∈ W, (π.twist χ).ρ g v ∈ W) ↔ (∀ g, ∀ v ∈ W, π.ρ g v ∈ W) := by
    intro W
    refine ⟨fun h g v hv => ?_, fun h g v hv => ?_⟩
    · exact Representation.apply_mem_of_charTwist_apply_mem
        (χ := Circle.toUnits.comp (χ : G →* Circle))
        (ρ := π.toContRepresentation.toRepresentation) (fun g _ hv => h g _ hv) g hv
    · exact Representation.charTwist_apply_mem_of_apply_mem
        (χ := Circle.toUnits.comp (χ : G →* Circle))
        (ρ := π.toContRepresentation.toRepresentation) (fun g _ hv => h g _ hv) g hv
  unfold IsIrreducible
  exact and_congr Iff.rfl (forall_congr' fun W => forall_congr' fun _ => imp_congr_left (key W))

end UnitaryRep

end GSpinGGP
