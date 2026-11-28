/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Main

/-!
# The main theorem with the non-archimedean notions

Over a non-archimedean field the statement of `local_ggp` is equivalent to its formulation with
the non-archimedean notions: the multiplicity `multiplicity π d.H (d.xi ψ.toAddChar)` (all
equivariant linear forms on `π^∞`), the character `characterOn π (regularSet d.G d.lie)` and the
Whittaker condition `HasModel`.

* `PAdicTemperedPacketFamily`: the hypotheses (STAB), (TRANS), (WHITT) of Thesis §6.3 written
  with these notions;
* `PAdicTemperedPacketFamily.toTemperedPacketFamily`, `TemperedPacketFamily.toPAdic`: the two
  conversions;
* `local_ggp_pAdic`: Thesis Thm. 6.4.1 with these notions, deduced from `local_ggp`.

Over `ℝ`, `mult_of_not_isUltrametricDist` evaluates `mult` through the real Lie structure of
`G(F)` (`mult_real`).
-/

namespace GSpinGGP.Sanity.StatementInvariance

open GSpinGGP

section PAdic

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (ψ : NontrivialAddChar F)

/-- The hypotheses of Thesis §6.3 on a family of tempered packets `Π_α`, with the character
`characterOn π (regularSet G G.lie)` and Whittaker models `HasModel`. -/
structure PAdicTemperedPacketFamily (d : GGPData F) (IF : InnerFormSystem d) where
  /-- the index set of the packet `Π_α` -/
  ι : IF.Idx → Type
  [fintype : ∀ α, Fintype (ι α)]
  /-- the members of `Π_α` -/
  rep : ∀ α, ι α → UnitaryRep ↥(IF.data α).G
  tempered : ∀ α i, IsTempered (rep α i)
  inequiv : ∀ α (i j : ι α), i ≠ j → ¬ (rep α i).IsEquivalent (rep α j)
  central_trivial : ∀ α i, IsTrivialOn (rep α i) ((IF.data α).AGH : Set ↥(IF.data α).G)
  /-- **(STAB)** -/
  stab : ∀ α, IsStableFn (IF.data α)
    (fun y => ∑ i, characterOn (rep α i) (regularSet (IF.data α).G (IF.data α).lie) y)
  /-- **(TRANS)** -/
  trans : ∀ α (x : ↥d.G) (y : ↥(IF.data α).G), x ∈ regularSet d.G d.lie →
    y ∈ regularSet (IF.data α).G (IF.data α).lie → d.StablyConjG (IF.twist α) x y →
    ∑ i, characterOn (rep α i) (regularSet (IF.data α).G (IF.data α).lie) y =
      (kottwitzSign d (IF.twist α) : ℂ) *
        ∑ i, characterOn (rep IF.base i)
          (regularSet (IF.data IF.base).G (IF.data IF.base).lie) (IF.toBase x)
  /-- **(WHITT)** -/
  whitt : ∀ w : WhittakerDatum (IF.data IF.base),
    ∃! i : ι IF.base, HasModel (rep IF.base i) w.U w.χ

attribute [instance] PAdicTemperedPacketFamily.fintype

variable {d : GGPData F} {IF : InnerFormSystem d}

/-- A family satisfying the non-archimedean hypotheses is a `TemperedPacketFamily`. -/
def PAdicTemperedPacketFamily.toTemperedPacketFamily (Q : PAdicTemperedPacketFamily d IF) :
    TemperedPacketFamily d IF where
  ι := Q.ι
  rep := Q.rep
  tempered := Q.tempered
  inequiv := Q.inequiv
  central_trivial := Q.central_trivial
  stab α := by simpa only [charG_eq_characterOn] using Q.stab α
  trans α x y hx hy h := by simpa only [charG_eq_characterOn] using Q.trans α x y hx hy h
  whitt w := by simpa only [localHasModel_of_isUltrametricDist] using Q.whitt w

/-- A `TemperedPacketFamily` satisfies the non-archimedean hypotheses. -/
def _root_.GSpinGGP.TemperedPacketFamily.toPAdic (P : TemperedPacketFamily d IF) :
    PAdicTemperedPacketFamily d IF where
  ι := P.ι
  rep := P.rep
  tempered := P.tempered
  inequiv := P.inequiv
  central_trivial := P.central_trivial
  stab α := by simpa only [← charG_eq_characterOn] using P.stab α
  trans α x y hx hy h := by simpa only [← charG_eq_characterOn] using P.trans α x y hx hy h
  whitt w := P.whitt_hasModel w

/-- **Thesis Thm. 6.4.1 with the non-archimedean notions**: for `Π_α` satisfying (STAB), (TRANS),
(WHITT) with `characterOn` and `HasModel`, exactly one `π ∈ ⊔_α Π_α` has
`dim Hom_{H(F)}(π^∞, ξ) = 1` (all linear forms), and all others have `0`. -/
theorem local_ggp_pAdic (d : GGPData F) (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (Q : PAdicTemperedPacketFamily d IF) :
    (∃! p : Σ α : IF.Idx, Q.ι α,
      multiplicity (Q.rep p.1 p.2) (IF.data p.1).H ((IF.data p.1).xi ψ.toAddChar) = 1) ∧
    ∀ p : Σ α, Q.ι α,
      multiplicity (Q.rep p.1 p.2) (IF.data p.1).H ((IF.data p.1).xi ψ.toAddChar) = 1 ∨
        multiplicity (Q.rep p.1 p.2) (IF.data p.1).H ((IF.data p.1).xi ψ.toAddChar) = 0 := by
  simp only [← mult_eq_multiplicity]
  exact local_ggp ψ d hqs IF Q.toTemperedPacketFamily

end PAdic

/-! ### `F = ℝ` -/

/-- Over `ℝ`, `m(π)` is the dimension of the continuous `H(ℝ)`-equivariant forms on the smooth
vectors for the real Lie structure of `G(ℝ)`. -/
theorem mult_real (ψ : NontrivialAddChar ℝ) (d : GGPData ℝ) (π : UnitaryRep ↥d.G) :
    mult ψ d π = LieRep.multiplicity
      ((nonempty_realEmbedding_of_not_isUltrametricDist not_isUltrametricDist_real).some
        |>.realLieStructure d.G d.isClosed_G) π d.H (d.xi ψ.toAddChar) :=
  mult_of_not_isUltrametricDist not_isUltrametricDist_real ψ d π

end GSpinGGP.Sanity.StatementInvariance
