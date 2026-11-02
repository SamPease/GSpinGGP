/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.LieRank

/-!
# Regular nilpotent orbits force quasi-splitness

* `le_wittIndex_of_pow_ne_zero`: a skew nilpotent `N` with `N^m ≠ 0` has a totally isotropic
  subspace of dimension `⌈m/2⌉` (the upper half of a Jordan chain).
* `quasiSplit_of_nilReg_nonempty`: if `gspin(V)` has a regular nilpotent element, `V` is
  quasi-split (Thesis §5.1.4), from `lieRank_gspin` and Jantzen's description of regular nilpotent
  elements of `so(V)` over `F̄` (`jantzen_regularNil_partition`).
* `nilReg_nonempty_iff_quasiSplit`, and the GGP-centralizer versions
  `nilReg_centralizer_nonempty_imp` (`sorry`) and `nilReg_centralizer_nonempty_iff`.
-/

noncomputable section

open CliffordAlgebra Module

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

section WittIndex

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **A nilpotent skew `N` with `N^m ≠ 0` gives Witt index `≥ ⌈m/2⌉`**: take `v` with `N^m v ≠ 0`
and a Jordan chain `v, …, N^k v` (`k ≥ m`, `N^(k+1) v = 0`); its upper half
`N^a v, …, N^k v` (`a = ⌈(k+1)/2⌉`) is linearly independent and totally isotropic. -/
theorem le_wittIndex_of_pow_ne_zero {Q : QuadraticForm K V} {N : Module.End K V}
    (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w)) (hnil : IsNilpotent N) {m : ℕ}
    (hm : N ^ m ≠ 0) : (m + 1) / 2 ≤ wittIndex Q := by
  obtain ⟨v, hv⟩ : ∃ v, (N ^ m) v ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (LinearMap.ext h)
  obtain ⟨k, hmk, hk, hk'⟩ := exists_pow_apply_ne_zero_of_isNilpotent hnil hv
  set a := (k + 2) / 2
  have hli' := (linearIndependent_pow_apply hk hk').comp
    (fun i : Fin (k + 1 - a) => (⟨a + i, by have := i.2; omega⟩ : Fin (k + 1)))
    fun i j hij => Fin.ext (by have := congrArg Fin.val hij; simp only at this; omega)
  have hli : LinearIndependent K fun i : Fin (k + 1 - a) => (N ^ (a + (i : ℕ))) v := hli'
  have hU := QuadClassify.le_wittIndex (isTotallyIsotropic_span_pow hN hk' (a := a) (by omega) (k + 1 - a))
  rw [finrank_span_eq_card hli, Fintype.card_fin] at hU
  omega

end WittIndex

/-! ## Regular nilpotent orbits and quasi-splitness -/

section NilReg

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- **Regular nilpotent orbits exist only if `GSpin(V)` is quasi-split** (Thesis §5.1.4).
Proof (`n = dim V ≥ 3`; for `n ≤ 2`, `V` is always quasi-split): `lieRank gspin(V) = ⌊n/2⌋ + 1`
(`lieRank_gspin`), so a regular nilpotent `X` has `dim so(V)_N = ⌊n/2⌋` for `N = adV X`
(`finrank_lieCentralizer_gspin`), which is nilpotent (`isNilpotent_adV`). Over `F̄` the matrix of
`N` has the least centralizer dimension among nilpotents (`jantzen_finrank_soCentMat_ge`), so it is
regular nilpotent of partition `[n]` or `[n − 1, 1]` (`jantzen_regularNil_partition`, Jantzen 2004
§6.3); hence `N^m ≠ 0` with `m = n − 1` (`n` odd) or `n − 2` (`n` even), and
`le_wittIndex_of_pow_ne_zero` gives `w(V) ≥ ⌈m/2⌉ = ⌊(n − 1)/2⌋`, i.e. `n ≤ 2 w(V) + 2`. -/
theorem quasiSplit_of_nilReg_nonempty {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (hQ : IsNondeg Q)
    (h : (NilReg (GSpin Q) (gspin Q)).Nonempty) : IsQuasiSplitQF Q := by
  unfold IsQuasiSplitQF
  set n := finrank F V with hn_def
  by_cases hn : n ≤ 2
  · omega
  push Not at hn
  obtain ⟨O, hXg, hXn, hXr⟩ := h
  set X : CliffordAlgebra Q := (Quotient.out O).1
  have hdim : finrank F (soCent Q (adV Q X)) = n / 2 := by
    have := finrank_lieCentralizer_gspin hQ hXg
    rw [hXr, lieRank_gspin hQ] at this
    omega
  obtain ⟨Φ, A, hΦ, hdet, hA, hfin, hpow⟩ := exists_algebraicClosure_soCentMat hQ (bform_adV hXg)
  have hNn := isNilpotent_adV hXg hXn
  have hAn : IsNilpotent A := by
    obtain ⟨k, hk⟩ := hNn
    exact ⟨k, (hpow k).2 hk⟩
  have hreg : ∀ Y ∈ skewAdjointMatricesSubmodule Φ, IsNilpotent Y →
      finrank (AlgebraicClosure F) (soCentMat Φ A) ≤
        finrank (AlgebraicClosure F) (soCentMat Φ Y) := fun Y hY _ => by
    rw [hfin, hdim]
    exact jantzen_finrank_soCentMat_ge (by omega) Φ hΦ hdet Y hY
  have hp := jantzen_regularNil_partition (by omega) Φ hΦ hdet A hA hAn hreg
  have hN : ∀ m, A ^ m ≠ 0 → (m + 1) / 2 ≤ wittIndex Q := fun m hm =>
    le_wittIndex_of_pow_ne_zero (bform_adV hXg) hNn fun h0 => hm ((hpow m).2 h0)
  rcases Nat.even_or_odd n with he | ho
  · have := hN _ (hp.2 he).1
    obtain ⟨r, hr⟩ := he
    omega
  · have := hN _ (hp.1 ho)
    obtain ⟨r, hr⟩ := ho
    omega

/-- **Regular nilpotent orbits exist iff `GSpin(V)` is quasi-split** (Thesis §5.1.4
"Regular Nilpotent Orbits"; Waldspurger, *Astérisque* 269 (2001), Ch. I; Luo §2.1): `Nil_reg(so(V))` is
nonempty iff the anisotropic kernel of `V` has dimension `≤ 2` (`IsQuasiSplitQF`). The direction `⇐` is
proved (`nilReg_nonempty_of_quasiSplit`); `⇒` is `quasiSplit_of_nilReg_nonempty`. -/
theorem nilReg_nonempty_iff_quasiSplit {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (hQ : IsNondeg Q) :
    (NilReg (GSpin Q) (gspin Q)).Nonempty ↔ IsQuasiSplitQF Q :=
  ⟨quasiSplit_of_nilReg_nonempty Q hQ, nilReg_nonempty_of_quasiSplit Q hQ⟩

/-- **Germs vanish off quasi-split centralizers, GGP form; necessary condition**
(Waldspurger 2001 Ch. I applied to the factors of `G_x`; BP Prop. 4.5.1(i)).  For semisimple
`x ∈ GSpin(W)(F)` embedded diagonally, `G_x` is covered by `G'_x × G''_x` with central split
kernel, `G'_x = GSpin(W'_x) × GSpin(V'_x)`.  If `𝔤_x` has a regular nilpotent
orbit then `G_x`, hence `G'_x`, is quasi-split, i.e. `W'_x` and `V'_x = W'_x ⊕ Z` are (this
direction holds for every semisimple `x`; the converse needs `MovedPartAbelian`).
Combined with `germ = 0` off `NilReg`, this gives BP Prop. 4.5.1(i) for the germs `c_{θ,O}(x)`.

**Status: `sorry`, not a literature axiom** (the statement is not verbatim in a source). Sketch:
for `Y ∈ 𝔤_x`, `dim 𝔤_{x,Y} = a_W(Y) + b_W(Y) + a_V(Y) + b_V(Y) + 2` with
`a_W(Y) = dim so(W'_x)_{adV Y₁|W'_x}` and `b_W(Y)` the dimension of the part of `so(W)_{P x, adV Y₁}`
killing `W'_x`, likewise for `V` with `V'_x ≅ W'_x ⊕ Z` (`QVfixIso`)
(`finrank_lieCentralizer_lieCentralizer_lie`, `finrank_lieCentralizer_fixed`). Missing lemma:
restriction to `(W'_x)^⊥` identifies that part with `so(W''_x)_{x̄, adV Y₁|W''_x}`, so `b_W` depends
only on the moved component of `Y`. The four summands then depend on independent components of `Y`
(each extends by `0` and lifts, `exists_mem_gspin_adV_eq`), so `lieRank 𝔤_x` is the sum of their
minima and a regular nilpotent `X` minimizes `a_W` and `a_V`. A lift `Z'` of `adV X₁|_{W'_x}` to
`gspin(W'_x)` is nilpotent (nilpotent elements of `so` act nilpotently on the spin module) and regular
nilpotent there, so `W'_x` is quasi-split by `quasiSplit_of_nilReg_nonempty`; likewise `V'_x`. The
literature (Waldspurger 2001, Ch. I) treats the orthogonal factors one at a time; this GGP form is not
stated there. -/
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

**Status:** `⇐` is proved (`nilReg_centralizer_nonempty_of_quasiSplit`); `⇒` is
`nilReg_centralizer_nonempty_imp` (`sorry`). Not stated in this form in the literature. -/
theorem nilReg_centralizer_nonempty_iff (d : GGPData F) (x : GSpin d.QW)
    (hx : IsSS F ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
    (hmoved : MovedPartAbelian d.QW x) :
    (NilReg (grpCentralizer d.G ((d.diag x : d.G) : d.ambientˣ))
      (lieCentralizer d.lie (((d.diag x : d.G) : d.ambientˣ) : d.ambient))).Nonempty ↔
    IsQuasiSplitQF (d.QWfix x) ∧ IsQuasiSplitQF (d.QVfix x) :=
  ⟨nilReg_centralizer_nonempty_imp d x hx,
    fun h => nilReg_centralizer_nonempty_of_quasiSplit d x hx hmoved h.1 h.2⟩

end NilReg

end GSpinGGP
