/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.RegularNilpotent
import GSpinGGP.Literature.NilpotentOrbits
import GSpinGGP.GGP.QuadClassify
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The rank of `gspin(V)` and regular nilpotent elements

* `le_finrank_soCent`: `dim so(V)_N ≥ ⌊dim V/2⌋` for every `N ∈ so(V)`, over any field of
  characteristic `0`: Jantzen's bound over `F̄` (`jantzen_finrank_soCentMat_ge`) and the invariance
  of `dim so(V)_N` under extension of scalars (`finrank_soCentMat_map`).
* `le_lieRank_gspin`: hence `lieRank gspin(V) ≥ ⌊dim V/2⌋ + 1` (`finrank_lieCentralizer_gspin`).
* `isRegularNil_regNil`: the explicit element `regNil` is regular nilpotent.
-/

noncomputable section

open CliffordAlgebra Module

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

section LowerBound

variable {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **`dim so(V)_N ≥ ⌊dim V/2⌋`** for every skew `N` (Thesis §5.1.4; the rank of `SO(V)`). For
`dim V ≥ 3` this is Jantzen's bound over the algebraic closure, transported by
`finrank_soCentMat_map`; for `dim V ≤ 2` it is checked directly. -/
theorem le_finrank_soCent {Q : QuadraticForm K V} (hQ : IsNondeg Q) {N : Module.End K V}
    (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w)) :
    finrank K V / 2 ≤ finrank K (soCent Q N) := by
  have hNmem : N ∈ soCent Q N := mem_soCent.2 ⟨hN, rfl⟩
  have hsymm : ∀ x y, bform Q x y = bform Q y x := fun x y => QuadraticMap.associated_isSymm K Q x y
  by_cases hn : 3 ≤ finrank K V
  · set n := finrank K V
    let b := Module.finBasis K V
    set J := LinearMap.toMatrix₂ b b (bform Q)
    set A := LinearMap.toMatrix b b N
    have e : finrank K (soCent Q N) = finrank K (soCentMat J A) := by
      rw [soCentMat_toMatrix, LinearEquiv.finrank_map_eq]
    have hA : A ∈ soCentMat J A := by
      rw [soCentMat_toMatrix]; exact Submodule.mem_map_of_mem hNmem
    have hJ : J.transpose = J := by
      ext i j; simp [J, LinearMap.toMatrix₂_apply, hsymm]
    have hdet : J.det ≠ 0 := (LinearMap.nondegenerate_iff_det_ne_zero b).1 hQ
    let φ := algebraMap K (AlgebraicClosure K)
    rw [e, ← finrank_soCentMat_map (K := AlgebraicClosure K)]
    refine jantzen_finrank_soCentMat_ge hn (J.map φ) ?_ ?_ (A.map φ) ?_
    · rw [← Matrix.transpose_map, hJ]
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero φ).2 hdet
    · have hsk := (Submodule.mem_inf.mp hA).1
      rw [mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] at hsk ⊢
      rw [← Matrix.transpose_map]
      simp only [← RingHom.mapMatrix_apply, ← map_mul, ← map_neg, hsk]
  · interval_cases h : finrank K V
    · simp
    · simp
    · -- `dim V = 2`
      show 1 ≤ finrank K (soCent Q N)
      rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
      intro hbot
      by_cases hN0 : N = 0
      · let b := Module.finBasis K V
        rw [h] at b
        set a := b ⟨0, by omega⟩
        set c := b ⟨1, by omega⟩
        have hc : c ≠ 0 := b.ne_zero _
        obtain ⟨v, hv⟩ : ∃ v, bform Q c v ≠ 0 := by
          by_contra hne
          push Not at hne
          exact hc ((isNondeg_iff Q).mp hQ c hne)
        have hmem : adV Q (ι Q a * ι Q c) ∈ soCent Q N :=
          mem_soCent.2 ⟨bform_adV (ι_mul_ι_mem_gspin Q a c), by rw [hN0, mul_zero, zero_mul]⟩
        rw [hbot, Submodule.mem_bot] at hmem
        have h0 := congrArg (fun M : Module.End K V => M v) hmem
        simp only [adV_ι_mul_ι, LinearMap.zero_apply] at h0
        have hli : LinearIndependent K ![a, c] := by
          have := b.linearIndependent
          convert this using 1
          ext i; fin_cases i <;> rfl
        have := (LinearIndependent.pair_iff.mp hli) _ _ (by rw [sub_eq_add_neg, ← neg_smul] at h0; exact h0)
        rw [polar_eq_two_mul_bform] at this
        exact hv ((mul_eq_zero.mp this.1).resolve_left (Invertible.ne_zero 2))
      · rw [hbot, Submodule.mem_bot] at hNmem
        exact hN0 hNmem

end LowerBound

section Rank

variable {K : Type*} [NontriviallyNormedField K] [CharZero K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **`rank gspin(V) ≥ ⌊dim V/2⌋ + 1`**: every centralizer `gspin(V)_X` has dimension
`1 + dim so(V)_{adV X} ≥ 1 + ⌊dim V/2⌋`. -/
theorem le_lieRank_gspin {Q : QuadraticForm K V} (hQ : IsNondeg Q) :
    finrank K V / 2 + 1 ≤ lieRank (gspin Q) := by
  have : Nonempty ↥(gspin Q) := ⟨0⟩
  refine le_ciInf fun X => ?_
  rw [finrank_lieCentralizer_gspin hQ X.2]
  exact Nat.add_le_add_right (le_finrank_soCent hQ (bform_adV X.2)) 1

/-- **The explicit element `regNil` is regular nilpotent** in `gspin(V)` when
`dim V ≤ 2k + 2`: its centralizer has dimension `≤ dim V − k`
(`finrank_lieCentralizer_regNil_le`), which is `⌊dim V/2⌋ + 1 ≤ lieRank` as `dim V ∈ {2k+1, 2k+2}`. -/
theorem isRegularNil_regNil {Q : QuadraticForm K V} (hQ : IsNondeg Q) {w : ℤ → V} {ν : K} {k : ℕ}
    (hw : IsSplitFamily Q w ν k) (hν : ν ≠ 0) (hdim : finrank K V ≤ 2 * k + 2) :
    IsRegularNil (gspin Q) (regNil Q w ν k) := by
  have hr : lieRank (gspin Q) ≤ finrank K (lieCentralizer (gspin Q) (regNil Q w ν k)) := by
    unfold lieRank
    exact ciInf_le (OrderBot.bddBelow _) (⟨regNil Q w ν k, regNil_mem_gspin⟩ : gspin Q)
  refine ⟨regNil_mem_gspin, isNilpotent_regNil hw hν, le_antisymm ?_ hr⟩
  have h1 := finrank_lieCentralizer_regNil_le hQ hw hν hdim
  have hge : 2 * k + 1 ≤ finrank K V := by
    have := (linearIndependent_isSplitFamily hw hν).fintype_card_le_finrank
    rwa [Fintype.card_fin] at this
  have h2 := le_lieRank_gspin (K := K) hQ
  omega

end Rank

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
