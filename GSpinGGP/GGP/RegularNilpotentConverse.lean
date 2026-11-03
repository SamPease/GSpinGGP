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
* `isQuasiSplitQF_of_finrank_soCent_eq`: the core: a nilpotent skew `N` with
  `dim so(V)_N = ⌊dim V/2⌋` forces `V` quasi-split; `isQuasiSplitQF_fixedSub_of_forall_finrank_le`: the same for
  the fixed space `W'_y` when `X ∈ gspin(V)_y` minimizes `dim gspin(V)_{y,·}`.
* `nilReg_nonempty_iff_quasiSplit`, and the GGP-centralizer versions
  `nilReg_centralizer_nonempty_imp` and `nilReg_centralizer_nonempty_iff`.
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

section Core

variable {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **A nilpotent skew `N` with `dim so(V)_N = ⌊dim V/2⌋` forces `V` quasi-split**: over `K̄`, `N` has
the least centralizer dimension (`jantzen_finrank_soCentMat_ge`), so it is regular nilpotent of
partition `[n]` or `[n − 1, 1]` (`jantzen_regularNil_partition`); then
`le_wittIndex_of_pow_ne_zero` with `m = n − 1` or `n − 2` gives `n ≤ 2 w(V) + 2`. -/
theorem isQuasiSplitQF_of_finrank_soCent_eq {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    {N : Module.End K V} (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w)) (hNn : IsNilpotent N)
    (hdim : finrank K (soCent Q N) = finrank K V / 2) : IsQuasiSplitQF Q := by
  unfold IsQuasiSplitQF
  set n := finrank K V with hn_def
  by_cases hn : n ≤ 2
  · omega
  push Not at hn
  obtain ⟨Φ, A, hΦ, hdet, hA, hfin, hpow⟩ := exists_algebraicClosure_soCentMat hQ hN
  have hAn : IsNilpotent A := by
    obtain ⟨k, hk⟩ := hNn
    exact ⟨k, (hpow k).2 hk⟩
  have hreg : ∀ Y ∈ skewAdjointMatricesSubmodule Φ, IsNilpotent Y →
      finrank (AlgebraicClosure K) (soCentMat Φ A) ≤
        finrank (AlgebraicClosure K) (soCentMat Φ Y) := fun Y hY _ => by
    rw [hfin, hdim]
    exact jantzen_finrank_soCentMat_ge (by omega) Φ hΦ hdet Y hY
  have hp := jantzen_regularNil_partition (by omega) Φ hΦ hdet A hA hAn hreg
  have hW : ∀ m, A ^ m ≠ 0 → (m + 1) / 2 ≤ wittIndex Q := fun m hm =>
    le_wittIndex_of_pow_ne_zero hN hNn fun h0 => hm ((hpow m).2 h0)
  rcases Nat.even_or_odd n with he | ho
  · have := hW _ (hp.2 he).1
    obtain ⟨r, hr⟩ := he
    omega
  · have := hW _ (hp.1 ho)
    obtain ⟨r, hr⟩ := ho
    omega

/-- **The fixed-space factor**: if a nilpotent `X ∈ gspin(V)_y` minimizes `dim gspin(V)_{y,·}`, then the
fixed space `A = W'_y` is quasi-split. Changing the `A`-component of `X` to any skew `M`
(`exists_lieCentralizer_fixed_swap`) shows `dim so(A)_{adV X|_A} ≤ dim so(A)_M`, so it equals
`⌊dim A/2⌋` (`exists_skew_finrank_soCent_le`, `le_finrank_soCent`), and
`isQuasiSplitQF_of_finrank_soCent_eq` applies. -/
theorem isQuasiSplitQF_fixedSub_of_forall_finrank_le {Q : QuadraticForm K V} (hQ : IsNondeg Q) (y : GSpin Q)
    (hc : IsCompl (fixedSub y) ((bform Q).orthogonal (fixedSub y))) {X : CliffordAlgebra Q}
    (hXm : X ∈ lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
    (hXn : IsNilpotent X)
    (hmin : ∀ Y ∈ lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q),
      finrank K (lieCentralizer (lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q)) X) ≤
      finrank K (lieCentralizer (lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q)) Y)) :
    IsQuasiSplitQF (Q.comp (fixedSub y).subtype) := by
  obtain ⟨h, -⟩ := finrank_lieCentralizer_fixed hQ y hc hXm
  have hXg := (mem_lieCentralizer.mp hXm).1
  have hQA := isNondeg_comp_subtype_of_isCompl hc
  have hskew : ∀ u w, bform (Q.comp (fixedSub y).subtype) ((adV Q X).restrict h u) w =
      -bform (Q.comp (fixedSub y).subtype) u ((adV Q X).restrict h w) := fun u w => by
    simp only [bform_comp_subtype, LinearMap.restrict_coe_apply]
    exact bform_adV hXg _ _
  have hle : ∀ M : Module.End K (fixedSub y), (∀ u w, bform (Q.comp (fixedSub y).subtype) (M u) w =
      -bform (Q.comp (fixedSub y).subtype) u (M w)) →
      finrank K (soCent (Q.comp (fixedSub y).subtype) ((adV Q X).restrict h)) ≤
        finrank K (soCent (Q.comp (fixedSub y).subtype) M) := fun M hM => by
    obtain ⟨Y, hYm, e⟩ := exists_lieCentralizer_fixed_swap hQ y hc hXm h hM
    have := hmin Y hYm
    omega
  obtain ⟨M, hM, hMle⟩ := exists_skew_finrank_soCent_le _ (Q.comp (fixedSub y).subtype) rfl hQA
  have h1 := hle M (mem_soCent.1 hM).1
  have h2 := le_finrank_soCent hQA hskew
  exact isQuasiSplitQF_of_finrank_soCent_eq hQA hskew
    (Module.End.isNilpotent.restrict h (isNilpotent_adV hXg hXn)) (by omega)

end Core

/-! ## Regular nilpotent orbits and quasi-splitness -/

section NilReg

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- **Regular nilpotent orbits exist only if `GSpin(V)` is quasi-split** (Thesis §5.1.4).
Proof: `lieRank gspin(V) = ⌊n/2⌋ + 1` (`lieRank_gspin`), so a regular nilpotent `X` has
`dim so(V)_N = ⌊n/2⌋` for `N = adV X` (`finrank_lieCentralizer_gspin`), which is nilpotent
(`isNilpotent_adV`); conclude by `isQuasiSplitQF_of_finrank_soCent_eq` (Jantzen 2004 §6.3). -/
theorem quasiSplit_of_nilReg_nonempty {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (hQ : IsNondeg Q)
    (h : (NilReg (GSpin Q) (gspin Q)).Nonempty) : IsQuasiSplitQF Q := by
  obtain ⟨O, hXg, hXn, hXr⟩ := h
  refine isQuasiSplitQF_of_finrank_soCent_eq hQ (bform_adV hXg) (isNilpotent_adV hXg hXn) ?_
  have := finrank_lieCentralizer_gspin hQ hXg
  rw [hXr, lieRank_gspin hQ] at this
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

Proof: `𝔤_x = gspin(W)_x × gspin(V)_{incl x}` (`finrank_lieCentralizer_lieCentralizer_lie`), and a
regular nilpotent `X` minimizes `dim 𝔤_{x,·}`, so each component `X_i` minimizes its own factor
(change one component at a time). In each factor, `dim gspin_{y,Y} = dim so(A)_{adV Y|_A} +` (a term
depending only on `adV Y` on `A^⊥`) `+ 1` with `A` the fixed space (`finrank_lieCentralizer_fixed`,
`soCent_inf_killSub_congr`), and the `A`-component can be changed to any skew `M`
(`exists_lieCentralizer_fixed_swap`); so `adV X_i|_A` is a nilpotent of minimal centralizer
dimension in `so(A)`, and `A` is quasi-split (`isQuasiSplitQF_fixedSub_of_forall_finrank_le`, which rests on Jantzen
2004 §6.3). For `V`, `A = W'_x ⊕ Z` (`QVfixIso`). The literature (Waldspurger 2001, Ch. I) treats the
orthogonal factors one at a time; this GGP form is not stated there. -/
theorem nilReg_centralizer_nonempty_imp (d : GGPData F) (x : GSpin d.QW)
    (hx : IsSS F ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) :
    (NilReg (grpCentralizer d.G ((d.diag x : d.G) : d.ambientˣ))
      (lieCentralizer d.lie (((d.diag x : d.G) : d.ambientˣ) : d.ambient))).Nonempty →
    IsQuasiSplitQF (d.QWfix x) ∧ IsQuasiSplitQF (d.QVfix x) := by
  set dx : d.ambient := (((d.diag x : d.G) : d.ambientˣ) : d.ambient)
  rintro ⟨O, hXm, hXn, hXr⟩
  set X : d.ambient := (Quotient.out O).1
  have hdx : dx = (((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW),
      ((d.incl x : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) := rfl
  have hdisj := fixedSub_inf_movedSub_of_isSS x hx
  have hcW := isCompl_fixedSub_orthogonal d.nondeg x hdisj
  have hcV := isCompl_fixedSub_orthogonal d.nondeg_QV (d.incl x)
    (fixedSub_inf_movedSub_incl d x hdisj)
  have hmin : ∀ Y ∈ lieCentralizer d.lie dx, finrank F (lieCentralizer (lieCentralizer d.lie dx) X) ≤
      finrank F (lieCentralizer (lieCentralizer d.lie dx) Y) := fun Y hY => by
    rw [hXr]
    exact ciInf_le (OrderBot.bddBelow _) (⟨Y, hY⟩ : lieCentralizer d.lie dx)
  have hmem : ∀ Y : d.ambient, Y ∈ lieCentralizer d.lie dx ↔
      Y.1 ∈ lieCentralizer (gspin d.QW) ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) ∧
      Y.2 ∈ lieCentralizer (gspin d.QV)
        ((d.incl x : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) := by
    intro Y
    simp only [mem_lieCentralizer, hdx]
    constructor
    · rintro ⟨⟨h1, h2⟩, hc⟩
      exact ⟨⟨h1, congrArg Prod.fst hc⟩, ⟨h2, congrArg Prod.snd hc⟩⟩
    · rintro ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
      exact ⟨⟨h1, h2⟩, Prod.ext h3 h4⟩
  obtain ⟨hX1, hX2⟩ := (hmem X).1 hXm
  have hX1n : IsNilpotent X.1 := hXn.map (RingHom.fst _ _)
  have hX2n : IsNilpotent X.2 := hXn.map (RingHom.snd _ _)
  have hW : IsQuasiSplitQF (d.QW.comp (fixedSub x).subtype) := by
    refine isQuasiSplitQF_fixedSub_of_forall_finrank_le d.nondeg x hcW hX1 hX1n fun Y hY => ?_
    have := hmin (Y, X.2) ((hmem _).2 ⟨hY, hX2⟩)
    rw [finrank_lieCentralizer_lieCentralizer_lie, finrank_lieCentralizer_lieCentralizer_lie] at this
    exact Nat.le_of_add_le_add_right this
  have hV : IsQuasiSplitQF (d.QV.comp (fixedSub (d.incl x)).subtype) := by
    refine isQuasiSplitQF_fixedSub_of_forall_finrank_le d.nondeg_QV (d.incl x) hcV hX2 hX2n fun Y hY => ?_
    have := hmin (X.1, Y) ((hmem _).2 ⟨hX1, hY⟩)
    rw [finrank_lieCentralizer_lieCentralizer_lie, finrank_lieCentralizer_lieCentralizer_lie] at this
    exact Nat.le_of_add_le_add_left this
  exact ⟨hW, QuadClassify.isQuasiSplitQF_of_isometryEquiv (QVfixIso d x).symm hV⟩

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

Proved: `⇐` is `nilReg_centralizer_nonempty_of_quasiSplit`, `⇒` is
`nilReg_centralizer_nonempty_imp`. Not stated in this form in the literature. -/
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
