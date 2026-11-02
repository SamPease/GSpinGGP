/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.HarishChandra

/-!
# The regular set and the transfer of germs

The regular set of `G = GSpin(W) × GSpin(V)` is open and conull (from Harish-Chandra's theorem
`hc_regular_open_dense_conull` and the identification of his regular set with `regularSet`, a
`sorry` theorem), and germs are preserved under transfer to inner forms (BP Astérisque 418,
(12.1.2), which is stated for pure inner forms; a `sorry` theorem with a proof sketch).
-/

open MeasureTheory Topology Filter

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

open HarishChandra

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **Harish-Chandra's regular set is the regular semisimple set** (characteristic `0`):
`D(x) ≠ 0` (`hcDisc`) iff `x` is semisimple with abelian centralizer in `𝔤` (`regularSet`).
Proof sketch. (⇐) For `x` regular semisimple, `1 − Ad x` is semisimple with kernel `𝔤_x`. The algebra
`𝔤_x` is reductive (centralizer of a semisimple element) and abelian, so it is a Cartan subalgebra of
dimension `ℓ = rank G`. Hence `0` is a root of multiplicity exactly `ℓ` of `det(t − (1 − Ad x))`, and
the coefficient of `t^ℓ` is `±det(1 − Ad x)|_{𝔤/𝔤_x} ≠ 0`. (⇒) `D(x) ≠ 0` says the generalized
`1`-eigenspace of `Ad x` has dimension `≤ ℓ`. For `x = su` (Jordan decomposition) that eigenspace is
`𝔤_s`, which contains a Cartan subalgebra, so `𝔤_s` is one and `s` is regular. Then `Z_G(s)⁰` is a
maximal torus, so the unipotent `u ∈ Z_G(s)⁰` is `1`: `x = s` is semisimple and `𝔤_x = 𝔤_s` is
abelian. Missing in the project: `lieRank 𝔤` is the dimension of a Cartan subalgebra, and the
Cartan-subalgebra facts above.
Status: SORRY (structure theory of `GSpin`). -/
theorem hcDisc_ne_zero_iff_mem_regularSet (d : GGPData F) (x : ↥d.G) :
    hcDisc d x ≠ 0 ↔ x ∈ regularSet d.G d.lie := by
  sorry

/-- `θ_π = characterOn π (regularSet d.G d.lie)` (Triple's `charG d π`) represents the character
of `π` and is continuous on `G_reg(F)`: Harish-Chandra's theorem (`hc_character_exists`) gives
continuity on `G' = {D ≠ 0}`, which contains `regularSet` (`hcDisc_ne_zero_iff_mem_regularSet`). -/
theorem hc_character (d : GGPData F) (π : UnitaryRep ↥d.G) (hπ : IsTempered π) :
    IsCharacterOf π (characterOn π (regularSet d.G d.lie)) ∧
      ContinuousOn (characterOn π (regularSet d.G d.lie)) (regularSet d.G d.lie) := by
  obtain ⟨θ, hθ, hcont⟩ := hc_character_exists d π hπ
  exact characterOn_spec π _ ⟨θ, hθ,
    hcont.mono fun x hx => (hcDisc_ne_zero_iff_mem_regularSet d x).2 hx⟩

/-- **The regular semisimple set `G_reg(F)` of `G = GSpin(W) × GSpin(V)` is open in `G(F)` and its
complement has Haar measure zero** (Thesis §2.1; BP Astérisque 418, §1). From Harish-Chandra's
theorem `hc_regular_open_dense_conull` (LNM 162, Part V §3, p. 54) and the identification of his
`G' = {D ≠ 0}` with `regularSet` (`hcDisc_ne_zero_iff_mem_regularSet`).

Its role in this project: two representatives of the character distribution that are continuous on
`G_reg(F)` agree on `G_reg(F)` (open, conull), so `characterOn π (regularSet …)` is canonical there.
Stated for the Haar measure `Measure.haar` used in `IsCharacterOf`. -/
theorem hc_regularSet_open_conull (d : GGPData F) :
    IsOpen (regularSet d.G d.lie) ∧
      (Measure.haar : Measure ↥d.G) (regularSet d.G d.lie)ᶜ = 0 := by
  have h := hc_regular_open_dense_conull d
  have hset : {x : ↥d.G | hcDisc d x ≠ 0} = regularSet d.G d.lie :=
    Set.ext (hcDisc_ne_zero_iff_mem_regularSet d)
  rw [hset] at h
  exact ⟨h.1, h.2.2⟩

/-- **(e) Beuzart-Plessis (12.1.2)** (Thesis (6.1.2)), for the inner twists of `GSpin`.
Let `G` be quasi-split, `τ` an inner twist (`G_α = (d.twist τ).G`), `θ` a *stable*
quasi-character on `G(F)` and `θ'` a stable quasi-character on `G_α(F)` which is a *transfer* of
`θ`: `θ'(y) = θ(x)` whenever `x ∈ G_reg(F)`, `y ∈ G_{α,reg}(F)` are stably conjugate through
`ψ_α = C(φ) × C(φ ⊕ id_Z)`. Then for `x ∈ GSpin(W)(F)`, `y ∈ GSpin(W_α)(F)` semisimple and strongly
stably conjugate (embedded diagonally), `c_{θ',O'}(y) = c_{θ,O}(x)` for all `O ∈ Nil_reg(𝔤_x)`,
`O' ∈ Nil_reg(𝔤_{α,y})`. (For stable `θ` the regular germs do not depend on the orbit; the
equality then follows from the limit formula BP Prop 4.5.1(ii) along a maximal torus of `G_x`
transported to `G_{α,y}`.)

Sources: Beuzart-Plessis, *A local trace formula for the Gan–Gross–Prasad conjecture for unitary
groups: the archimedean case* (Astérisque 418, 2020), (12.1.2) (as cited in Thesis §6.1) — stated there for pure inner
forms; here it is used for the inner twists of `GSpin` with cocycle in `SO(W) × SO(V)`, for
which the proof is unchanged. Stability and transfer are written out inline (Triple's
`IsStableFn` is not visible here). Only diagonal elements are needed (Thesis §6.7).

**Status: `sorry`, not a literature axiom** (the statement is not verbatim in a source). BP (12.1.2)
is stated for any connected reductive group, but for *pure* inner forms. The inner forms here have
cocycles valued in `SO(W) × SO(V)`, and those with the other Hasse invariant are not pure inner
forms of `GSpin(W) × GSpin(V)`. BP's proof uses only BP Prop 4.5.1 1.(i),(ii) for `G` and `G_α`
separately, `D^G(x) = D^{G_α}(y)`, and the transport of a Borel pair of `G_x` by the `F`-isomorphism
`G_x ≅ G_{α,y}`. All of these hold here. -/
theorem bp_germ_transfer (d : GGPData F) (hqs : d.IsQuasiSplit) (ψ : NontrivialAddChar F)
    (τ : InnerTwist d.QW) (θ : ↥d.G → ℂ) (θ' : ↥(d.twist τ).G → ℂ)
    (hθ : IsQuasiCharacter d.G d.lie d.bilin ψ θ)
    (hθ' : IsQuasiCharacter (d.twist τ).G (d.twist τ).lie (d.twist τ).bilin ψ θ')
    (hstab : ∀ x ∈ regularSet d.G d.lie, ∀ x' ∈ regularSet d.G d.lie,
      d.StablyConj x x' → θ x = θ x')
    (hstab' : ∀ y ∈ regularSet (d.twist τ).G (d.twist τ).lie,
      ∀ y' ∈ regularSet (d.twist τ).G (d.twist τ).lie,
      (d.twist τ).StablyConj y y' → θ' y = θ' y')
    (htrans : ∀ x ∈ regularSet d.G d.lie, ∀ y ∈ regularSet (d.twist τ).G (d.twist τ).lie,
      d.StablyConjG τ x y → θ' y = θ x)
    (x : GSpin d.QW) (y : GSpin (d.twist τ).QW)
    (hx : IsSS F (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient))
    (hy : IsSS F ((((d.twist τ).diag y : ↥(d.twist τ).G) : (d.twist τ).ambientˣ) :
      (d.twist τ).ambient))
    (hxy : d.StronglyStablyConjW τ x y) :
    ∀ O ∈ NilReg (grpCentralizer d.G (d.diag x))
        (lieCentralizer d.lie (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient)),
    ∀ O' ∈ NilReg (grpCentralizer (d.twist τ).G ((d.twist τ).diag y))
        (lieCentralizer (d.twist τ).lie
          ((((d.twist τ).diag y : ↥(d.twist τ).G) : (d.twist τ).ambientˣ) : (d.twist τ).ambient)),
      germ (d.twist τ).G (d.twist τ).lie (d.twist τ).bilin ψ θ' ((d.twist τ).diag y) O' =
        germ d.G d.lie d.bilin ψ θ (d.diag x) O := by
  sorry

end GSpinGGP
