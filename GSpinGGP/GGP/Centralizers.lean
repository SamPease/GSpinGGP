/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.GSpin
import GSpinGGP.GGP.Steinberg

/-!
# Centralizers and regular nilpotent orbits in `GSpin`

Statements about centralizers of semisimple elements and regular nilpotent orbits of `GSpin` and of
the GGP centralizers `G_x`. The literature states their ingredients for orthogonal groups or for
general reductive groups (Steinberg 1968; Waldspurger, *Astérisque* 269 (2001), Ch. I;
Luo, arXiv:2009.13947, §2.1). The forms here are derived from those, so they are `sorry`
theorems, and each docstring names its exact ingredients; `steinberg_centralizer_connected` is
proved directly (`GGP/Steinberg.lean`).
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

**Status: proved, with no literature input** (`Steinberg.commute_iff`, `GGP/Steinberg.lean`), from
the one remaining `sorry` `Steinberg.commute_of_fix` (elements acting trivially on `W₊₁ ⊕ W₋₁`). The
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

/-! ## Regular nilpotent orbits and quasi-splitness -/

section NilReg

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- **Regular nilpotent orbits exist iff `GSpin(V)` is quasi-split** (Thesis §5.1.4
"Regular Nilpotent Orbits"; Waldspurger, *Astérisque* 269 (2001), Ch. I; Waldspurger, *Compositio* 146
(2010), §7.1; Luo §2.1).  Since `P` is onto `SO(V)` with central kernel, the `GSpin(V)(F)`-orbits of nilpotents
in `gspin(V)` are the `SO(V)(F)`-orbits of nilpotents in `so(V)`; `Nil_reg(so(V))` is nonempty
iff the anisotropic kernel of `V` has dimension `≤ 2` (`IsQuasiSplitQF`).

**Status: `sorry`, not a literature axiom** (the statement is not verbatim in a source). Exact
ingredients: for a connected reductive group, regular nilpotent elements exist iff the group is
quasi-split (Kostant; used in BP Astérisque 418, proof of Prop 4.5.1); and `SO(V)` is quasi-split
iff the anisotropic kernel of `V` has dimension `≤ 2` (Witt). The transfer to `gspin(V) = so(V) ⊕ F`
goes through `specP`. -/
theorem nilReg_nonempty_iff_quasiSplit {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (hQ : IsNondeg Q) :
    (NilReg (GSpin Q) (gspin Q)).Nonempty ↔ IsQuasiSplitQF Q := by
  sorry

/-- **Germs vanish off quasi-split centralizers, GGP form; necessary condition**
(Waldspurger 2001 Ch. I applied to the factors of `G_x`; BP Prop. 4.5.1(i)).  For semisimple
`x ∈ GSpin(W)(F)` embedded diagonally, `G_x` is covered by `G'_x × G''_x` with central split
kernel, `G'_x = GSpin(W'_x) × GSpin(V'_x)`.  If `𝔤_x` has a regular nilpotent
orbit then `G_x`, hence `G'_x`, is quasi-split, i.e. `W'_x` and `V'_x = W'_x ⊕ Z` are (this
direction holds for every semisimple `x`; the converse needs `MovedPartAbelian`).
Combined with `germ = 0` off `NilReg`, this gives BP Prop. 4.5.1(i) for the germs `c_{θ,O}(x)`.

**Status: `sorry`, not a literature axiom** (the statement is not verbatim in a source). Derived
from `nilReg_nonempty_iff_quasiSplit` applied to the factors of the centralizer `G_x`. The
literature (Waldspurger 2001, Ch. I) treats the orthogonal factors one at a time; this GGP form is
not stated there. -/
theorem nilReg_centralizer_nonempty_imp (d : GGPData F) (x : GSpin d.QW)
    (hx : IsSS F ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) :
    (NilReg (grpCentralizer d.G ((d.diag x : d.G) : d.ambientˣ))
      (lieCentralizer d.lie (((d.diag x : d.G) : d.ambientˣ) : d.ambient))).Nonempty →
    IsQuasiSplitQF (d.QWfix x) ∧ IsQuasiSplitQF (d.QVfix x) := by
  sorry

/-- **Regular nilpotent orbits of GGP centralizers** (Waldspurger 2001
Ch. I, 2010 §7.1).  For semisimple `x ∈ GSpin(W)(F)` whose moved part `G''_x` is a torus
(`MovedPartAbelian`, true for all `x` contributing to `Γ(G,H)`), `Nil_reg(𝔤_x) ≠ ∅` iff `W'_x`
and `V'_x = W'_x ⊕ Z` are quasi-split.

NB: without the torus hypothesis the "if" direction is **false**, because
`G_x` is quasi-split iff both `G'_x` and `G''_x` are, and `G''_x` need not be.  For non-quasi-split
`G`: `P(x) = -1` on an anisotropic `W''_x` of dimension 4.  Even for quasi-split `G` (where that
example cannot occur, by a Witt-group computation): `F = Q_3`, `W = N_D ⊥ ⟨1,-2⟩`, `Z = ⟨-3⟩`,
`P(x) = -1` on the quaternion norm form `N_D` and `-(3+2√2) ∈ E¹` on `⟨1,-2⟩`; then
`G'_x = G_m × G_m` but `G''_x ⊇ SL₁(D)⁴`.  So "`G_x` quasi-split iff `G'_x` quasi-split" holds
only for `x` with `Z_{SO(W''_x)}(x̄)⁰` a torus, which is this hypothesis.  It holds on `Γ(G,H)` (`movedPartAbelian_of_isGammaElt` in `Main`).  See
`nilReg_centralizer_nonempty_imp` for the unconditional direction.

**Status: `sorry`, not a literature axiom** (the statement is not verbatim in a source). Derived as
`nilReg_centralizer_nonempty_imp`, using `MovedPartAbelian` for the converse. Not stated in this
form in the literature. -/
theorem nilReg_centralizer_nonempty_iff (d : GGPData F) (x : GSpin d.QW)
    (hx : IsSS F ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
    (hmoved : MovedPartAbelian d.QW x) :
    (NilReg (grpCentralizer d.G ((d.diag x : d.G) : d.ambientˣ))
      (lieCentralizer d.lie (((d.diag x : d.G) : d.ambientˣ) : d.ambient))).Nonempty ↔
    IsQuasiSplitQF (d.QWfix x) ∧ IsQuasiSplitQF (d.QVfix x) := by
  sorry

/-- **Luo's orbit `O_ν` exists in the GGP situation** (Waldspurger, *Compositio* 146 (2010),
§7.1; Luo, *A local trace formula for the local Gan–Gross–Prasad conjecture for special
orthogonal groups*, §2.1 and §7.1; classification of regular nilpotent orbits: Waldspurger,
*Astérisque* 269 (2001), Ch. I; Thesis §5.1.4 "Regular Nilpotent Orbits").

For a quasi-split GGP datum (`V = W ⊕^⊥ Z`, `Z = ⟨ν⟩ ⊕ H^r` with `q(z₀) = ν`):
* if `dim V` is even and `≥ 4`, some regular nilpotent `X ∈ gspin(V)` has image `ad X ∈ so(V)` in
  `O_ν` (`IsInOrbitNu`: `V = F d₀ ⊕^⊥ U₁`, `d₀` anisotropic, `U₁ ≅ ⟨ν⟩ ⊕ H^k`, `ad X` kills `d₀`
  and is one Jordan block on `U₁`);
* if `dim W` is even and `≥ 4`, some regular nilpotent `X ∈ gspin(W)` has `ad X ∈ O_{−ν}`.

What the sources give, and what is packaged here. The sources classify `Nil_reg(so(U))` for a
quasi-split even-dimensional `U` by the classes `ν' ∈ 𝒩^U` such that `U ≅ ⟨a⟩ ⊕ ⟨ν'⟩ ⊕ H^{k}`,
the orbit `O_{ν'}` being the orbit of a regular nilpotent of `so(U₁)`, `U₁ = ⟨ν'⟩ ⊕ H^k`, extended
by `0` on `⟨a⟩`; it is a regular orbit of `so(U)` (Jordan type `(dim U − 1, 1)`), and lifts to
`gspin(U) = so(U) ⊕ F` with centralizer of dimension `rank so(U) + 1 = rank gspin(U)`. The axiom
also contains the elementary (Witt-theory) fact that the relevant class is in `𝒩`:
`dim V` even ⇒ `W` odd and quasi-split, hence split, `W = ⟨a⟩ ⊕ W₁` with `W₁` hyperbolic, so
`V = ⟨a⟩ ⊕ (W₁ ⊕ Z)` and `W₁ ⊕ Z ≅ ⟨ν⟩ ⊕ H^{k+r}`; `dim W = 2m' ≥ 4` ⇒ `V` odd quasi-split,
hence `V ≅ ⟨b⟩ ⊕ H^{m'+r}`, and Witt cancellation of `H^r ⊕ ⟨ν⟩` against `⟨ν⟩ ⊕ ⟨−ν⟩ ≅ H` gives
`W ≅ ⟨b⟩ ⊕ ⟨−ν⟩ ⊕ H^{m'−1}`. These are the classes `ν₀ = q(z₀)` (for `V`) and `−ν₀` (for `W`)
used by Luo §7.1.

All hypotheses are explicit binders; for `toyData`
(`dim W = 0`, `dim V = 1`) both conjuncts are vacuous; the smallest non-vacuous cases
(`dim W = 1`, `r = 1`, `dim V = 4`; `dim W = 4`, `r = 0`, `dim V = 5`) agree with the
classification. `ν ≠ 0` (it is a unit) is what makes `U₁ ≠ 0`, so the clause
`(ad X)^{dim U₁ − 1} ≠ 0` on `U₁` is satisfiable.

**Status: `sorry`, not a literature axiom** (the statement is not verbatim in a source). The source
classification (Luo §2.1; Waldspurger 2001, Ch. I) is for `so(U)`. The lift to `gspin(U) = so(U) ⊕
F` and the two Witt-theory steps in the docstring are the remaining argument. -/
theorem exists_regularNil_inOrbitNu {F : Type*} [NontriviallyNormedField F] [PAdicField F]
    (d : GGPData F) (hqs : d.IsQuasiSplit) :
    (Even (finrank F d.V) → 4 ≤ finrank F d.V →
      ∃ X : CliffordAlgebra d.QV, IsRegularNil (gspin d.QV) X ∧
        IsInOrbitNu d.QV ⊤ (d.ν : F) (adV d.QV X)) ∧
    (Even d.m → 4 ≤ d.m →
      ∃ X : CliffordAlgebra d.QW, IsRegularNil (gspin d.QW) X ∧
        IsInOrbitNu d.QW ⊤ (-(d.ν : F)) (adV d.QW X)) := by
  sorry

end NilReg

end GSpinGGP
