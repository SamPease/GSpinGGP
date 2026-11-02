/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.GSpin
import GSpinGGP.GGP.Steinberg

/-!
# Centralizers in `GSpin`

Centralizers of semisimple elements of `GSpin` (Steinberg 1968): `steinberg_centralizer_connected`
is proved directly (`GGP/Steinberg.lean`). The regular nilpotent orbits of `GSpin` and of the GGP
centralizers `G_x` are in `GGP/RegularNilpotent.lean`.
-/

noncomputable section

open CliffordAlgebra Module
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

/-! ## Connectedness of centralizers (Steinberg) -/

section Steinberg

/-- **Centralizers of semisimple elements of `GSpin`** (Steinberg,
*Endomorphisms of linear algebraic groups* (1968), Thm. 8.1, since the derived group `Spin(V)` is
simply connected): for semisimple `x`, `Z_{GSpin(V)}(x) = P⁻¹(Z_{SO(V)}(P x)⁰)`.

The identity component is not a layer-1 notion, so we use its classical description for a
semisimple `x̄ = P(x)`: `Z_{O(V)}(x̄) = O(W₊₁) × O(W₋₁) × ∏ GL/unitary factors` (the latter
connected, with determinant one), so
`Z_{SO(V)}(x̄)⁰ = {h ∈ Z_{SO(V)}(x̄) | det h|_{W₊₁} = 1 ∧ det h|_{W₋₁} = 1}`, with
`W_{±1} = ker(x̄ ∓ 1)`.  Hence for `g ∈ GSpin(V)(K)`:
`g x = x g ↔ P(g) commutes with P(x) ∧ det P(g)|_{W'_x} = 1 ∧ det P(g)|_{W_{-1}} = 1`.
(The determinant conditions are stated as `∃` over the — unique — invariance proofs; see
`mapsTo_fixedSub_of_commute`.)  Valid over any field of characteristic `0` (in particular `F̄`,
via `Q.baseChange`); semisimplicity is that of left multiplication on `C(V)` (definitionally
`IsSS`, which needs a normed field — see `steinberg_centralizer_connected'`).

**Status: proved, with no literature input** and no `sorry` (`Steinberg.commute_iff`,
`GGP/Steinberg.lean`; the pair-block step is `PairBlock.commute_of_fix`). The
proof computes the sign `c` in `g x g⁻¹ = c x` as `det P(g)|_{W₋₁}`, instead of going through
Steinberg's connectedness theorem. -/
theorem steinberg_centralizer_connected {K : Type*} [Field K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : IsNondeg Q) (x : GSpin Q)
    (hx : Module.End.IsSemisimple
      (LinearMap.mulLeft K ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))
    (g : GSpin Q) :
    Commute (g : (CliffordAlgebra Q)ˣ) (x : (CliffordAlgebra Q)ˣ) ↔
      Commute (specP Q g) (specP Q x) ∧
      (∃ h : ∀ v ∈ fixedSub x, (specP Q g : V →ₗ[K] V) v ∈ fixedSub x,
        LinearMap.det ((specP Q g : V →ₗ[K] V).restrict h) = 1) ∧
      (∃ h : ∀ v ∈ negFixedSub x, (specP Q g : V →ₗ[K] V) v ∈ negFixedSub x,
        LinearMap.det ((specP Q g : V →ₗ[K] V).restrict h) = 1) :=
  Steinberg.commute_iff hQ x hx g

/-- `steinberg_centralizer_connected` for a normed field (e.g. `p`-adic `F`), with the hypothesis
phrased by `IsSS` (Foundations/LocalGroups), and the conclusion in terms of `grpCentralizer`. -/
theorem steinberg_centralizer_connected' {F : Type*} [NontriviallyNormedField F] [CharZero F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V) (hQ : IsNondeg Q) (x : GSpin Q)
    (hx : IsSS F ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) (g : GSpin Q) :
    (g : (CliffordAlgebra Q)ˣ) ∈ grpCentralizer (GSpin Q) (x : (CliffordAlgebra Q)ˣ) ↔
      Commute (specP Q g) (specP Q x) ∧
      (∃ h : ∀ v ∈ fixedSub x, (specP Q g : V →ₗ[F] V) v ∈ fixedSub x,
        LinearMap.det ((specP Q g : V →ₗ[F] V).restrict h) = 1) ∧
      (∃ h : ∀ v ∈ negFixedSub x, (specP Q g : V →ₗ[F] V) v ∈ negFixedSub x,
        LinearMap.det ((specP Q g : V →ₗ[F] V).restrict h) = 1) := by
  rw [← steinberg_centralizer_connected Q hQ x hx g]
  simp only [grpCentralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩

end Steinberg


end GSpinGGP
