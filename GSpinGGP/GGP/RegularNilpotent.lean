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

section Witt

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **A quasi-split space contains a split family of maximal size** (Witt decomposition): if
`dim V > 0` and the anisotropic kernel has dimension `≤ 2`, there are `w_{-k..k}` with
`b(w_i, w_j) = ν δ_{i+j,0}`, `ν ≠ 0`, and `dim V ≤ 2k + 2`. From `V ≅ H^s ⊥ V_an`: the hyperbolic
pairs of `H^s` around an anisotropic vector of `V_an`, or (for `V_an = 0`) around `h₀ + h_{2s-1}`
with the remaining `s − 1` pairs. -/
theorem exists_isSplitFamily_of_quasiSplit {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    (hqs : IsQuasiSplitQF Q) (hpos : 0 < finrank K V) :
    ∃ (w : ℤ → V) (ν : K) (k : ℕ), ν ≠ 0 ∧ IsSplitFamily Q w ν k ∧ finrank K V ≤ 2 * k + 2 := by
  obtain ⟨ka, Qa, hani, ⟨I⟩, hdim⟩ := witt_decomposition Q hQ
  set s := wittIndex Q
  unfold IsQuasiSplitQF at hqs
  let J := I.symm
  have hJ : ∀ x y, bform Q (J x) (J y) = bform (hypForm K s) x.1 y.1 + bform Qa x.2 y.2 :=
    fun x y => (bform_isometry J.toIsometry x y).trans (bform_prod _ _ x y)
  let h : ℕ → V := fun a => if ha : a < 2 * s then J (Pi.single ⟨a, ha⟩ 1, 0) else 0
  have hh : ∀ a b : ℕ, a < 2 * s → b < 2 * s →
      bform Q (h a) (h b) = if a + b + 1 = 2 * s then 1 else 0 := by
    intro a b ha hb
    simp only [h, dite_eq_left ha, dite_eq_left hb]
    rw [hJ, bform_hypForm_single]
    simp
  have hsymm : ∀ x y, bform Q x y = bform Q y x := fun x y => QuadraticMap.associated_isSymm K Q x y
  have hQb : ∀ x, bform Q x x = Q x := fun x => QuadraticMap.associated_eq_self_apply K Q x
  by_cases hka : 1 ≤ ka
  · let g : Fin ka → K := Pi.single ⟨0, hka⟩ 1
    let u : V := J (0, g)
    have hQu : Q u = Qa g := by
      simp only [u, QuadraticMap.IsometryEquiv.map_app, QuadraticMap.prod_apply, map_zero,
        zero_add]
    have hν : Q u ≠ 0 := by
      rw [hQu]; intro h0
      have := hani g h0
      simpa [g] using congrFun this ⟨0, hka⟩
    refine ⟨extFamily (fun _ => u) h (Q u) 0 s, Q u, 0 + s, hν, ?_, by omega⟩
    refine isSplitFamily_extFamily (fun i j hi hj => ?_) hh (fun j _ a ha => ?_)
    · have hi0 : i = 0 := by rw [abs_le] at hi; omega
      have hj0 : j = 0 := by rw [abs_le] at hj; omega
      subst hi0 hj0
      simp [hQb]
    · simp only [u, h, dite_eq_left ha]
      rw [hJ]
      simp
  · have hka0 : ka = 0 := by omega
    have hs : 1 ≤ s := by omega
    let u : V := h 0 + h (2 * s - 1)
    have hbu : bform Q u u = 2 := by
      simp only [u, map_add, LinearMap.add_apply]
      rw [hh _ _ (by omega) (by omega), hh _ _ (by omega) (by omega), hh _ _ (by omega) (by omega),
        hh _ _ (by omega) (by omega), ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
        ite_eq_right (by omega)]
      norm_num
    refine ⟨extFamily (fun _ => u) (fun a => h (a + 1)) (2 : K) 0 (s - 1), (2 : K), 0 + (s - 1),
      Invertible.ne_zero 2, ?_, by omega⟩
    refine isSplitFamily_extFamily (fun i j hi hj => ?_) (fun a b ha hb => ?_) (fun j _ a ha => ?_)
    · have hi0 : i = 0 := by rw [abs_le] at hi; omega
      have hj0 : j = 0 := by rw [abs_le] at hj; omega
      subst hi0 hj0
      simp [hbu]
    · rw [hh _ _ (by omega) (by omega)]
      congr 1; apply propext; omega
    · simp only [u, map_add, LinearMap.add_apply]
      rw [hh _ _ (by omega) (by omega), hh _ _ (by omega) (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), add_zero]

/-- **An odd-dimensional quasi-split space is `H^s ⊥ ⟨a⟩`** (Witt decomposition): hyperbolic
pairs `h_0, …, h_{2s-1}` (`b(h_i, h_j) = δ_{i+j+1, 2s}`) and an anisotropic `a ⊥ h`, with
`dim V = 2s + 1`. -/
theorem exists_hyp_of_quasiSplit_odd {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    (hqs : IsQuasiSplitQF Q) (hodd : Odd (finrank K V)) :
    ∃ (s : ℕ) (h : ℕ → V) (a : V), (∀ i j : ℕ, i < 2 * s → j < 2 * s →
      bform Q (h i) (h j) = if i + j + 1 = 2 * s then 1 else 0) ∧ Q a ≠ 0 ∧
      (∀ j : ℕ, j < 2 * s → bform Q a (h j) = 0) ∧ finrank K V = 2 * s + 1 := by
  obtain ⟨ka, Qa, hani, ⟨I⟩, hdim⟩ := witt_decomposition Q hQ
  set s := wittIndex Q
  unfold IsQuasiSplitQF at hqs
  obtain ⟨t, ht⟩ := hodd
  have hka : ka = 1 := by omega
  let J := I.symm
  have hJ : ∀ x y, bform Q (J x) (J y) = bform (hypForm K s) x.1 y.1 + bform Qa x.2 y.2 :=
    fun x y => (bform_isometry J.toIsometry x y).trans (bform_prod _ _ x y)
  let h : ℕ → V := fun a => if ha : a < 2 * s then J (Pi.single ⟨a, ha⟩ 1, 0) else 0
  let g : Fin ka → K := Pi.single ⟨0, by omega⟩ 1
  refine ⟨s, h, J (0, g), fun i j hi hj => ?_, ?_, fun j hj => ?_, by omega⟩
  · simp only [h, dite_eq_left hi, dite_eq_left hj]
    rw [hJ, bform_hypForm_single]
    simp
  · simp only [QuadraticMap.IsometryEquiv.map_app, QuadraticMap.prod_apply, map_zero, zero_add]
    intro h0
    have := hani g h0
    simpa [g] using congrFun this ⟨0, by omega⟩
  · simp only [h, dite_eq_left hj]
    rw [hJ]
    simp

end Witt

/-! ## Regular nilpotent orbits and quasi-splitness -/

section NilReg

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- **A quasi-split `GSpin(V)` has a regular nilpotent orbit** (Thesis §5.1.4 "Regular Nilpotent
Orbits"). Proved: a split family `w_{-k..k}` with `dim V ≤ 2k + 2`
(`exists_isSplitFamily_of_quasiSplit`) gives the regular nilpotent element `regNil`
(`isRegularNil_regNil`, which rests on Jantzen's bound `jantzen_finrank_soCentMat_ge`); for
`V = 0`, `X = 0`. -/
theorem nilReg_nonempty_of_quasiSplit {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (hQ : IsNondeg Q) (hqs : IsQuasiSplitQF Q) :
    (NilReg (GSpin Q) (gspin Q)).Nonempty := by
  have hconj : ∀ g ∈ GSpin Q, ∀ Y ∈ gspin Q,
      (g : CliffordAlgebra Q) * Y * (↑g⁻¹ : CliffordAlgebra Q) ∈ gspin Q :=
    fun g hg Y hY => conj_mem_gspin Q ⟨g, hg⟩ hY
  obtain ⟨X, hX⟩ : ∃ X, IsRegularNil (gspin Q) X := by
    by_cases hpos : 0 < finrank F V
    · obtain ⟨w, ν, k, hν, hw, hdim⟩ := exists_isSplitFamily_of_quasiSplit hQ hqs hpos
      exact ⟨_, isRegularNil_regNil hQ hw hν hdim⟩
    · -- `V = 0`: every centralizer is `gspin(V) = F`
      have h0 : finrank F V = 0 := by omega
      refine ⟨0, (gspin Q).zero_mem, IsNilpotent.zero, le_antisymm ?_ ?_⟩
      · rw [finrank_lieCentralizer_gspin hQ (gspin Q).zero_mem]
        have : finrank F (soCent Q (adV Q 0)) = 0 := by
          have h1 := Submodule.finrank_le (soCent Q (adV Q 0))
          rw [Module.finrank_linearMap, h0, mul_zero] at h1
          omega
        have h2 := le_lieRank_gspin hQ
        rw [h0] at h2
        omega
      · unfold lieRank
        exact ciInf_le (OrderBot.bddBelow _) (⟨0, (gspin Q).zero_mem⟩ : gspin Q)
  exact ⟨_, mk_mem_nilReg_of_isRegularNil _ _ hconj ⟨X, hX.1, hX.2.1⟩ hX⟩

/-- **Regular nilpotent orbits exist only if `GSpin(V)` is quasi-split** (Thesis §5.1.4).

**Status: `sorry`, not a literature axiom.** Sketch: a regular nilpotent `X` of `gspin(V)` has
`dim so(V)_{adV X} = ⌊dim V/2⌋` (`finrank_lieCentralizer_gspin`, `le_lieRank_gspin`); over `F̄` it is
regular nilpotent in `so(V)`, so it has Jordan type `[n]` or `[n−1, 1]` (Jantzen 2004 §6.3 for
`SO(V, φ)`, `n = dim V ≥ 3`; `n ≤ 2` is always quasi-split); the rank of `(adV X)^{n-2}` does not change
under `F ⊂ F̄`, so `N = adV X` has a vector `v` with `N^{n-2} v ≠ 0`; then
`span(N^j v : j > (n − 2)/2)` is totally isotropic of dimension `⌊(n−1)/2⌋`
(`b(N^i v, N^j v) = ± b(v, N^{i+j} v) = 0` for `i + j ≥ n − 1`), so `n ≤ 2 w(V) + 2`. -/
theorem quasiSplit_of_nilReg_nonempty {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (hQ : IsNondeg Q)
    (h : (NilReg (GSpin Q) (gspin Q)).Nonempty) : IsQuasiSplitQF Q := by
  sorry

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

/-- **`regNil` lies in Luo's orbit `O_ν`** when `V = ⟨d₀⟩ ⊥ ⟨w_{-k..k}⟩` with `d₀` anisotropic
(`IsInOrbitNu`): `adV X` kills `d₀`, is one Jordan block on `U₁ = ⟨w⟩`, and `U₁ = ⟨w_0⟩ ⊥ ⟨w_j : j ≠ 0⟩`
with `q(w_0) = ν` and `⟨w_j : j ≠ 0⟩` hyperbolic (`⟨w_1, …, w_k⟩` totally isotropic). -/
theorem isInOrbitNu_regNil {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {Q : QuadraticForm F V} {w : ℤ → V} {ν : F} {k : ℕ} (hw : IsSplitFamily Q w ν k) (hν : ν ≠ 0)
    {d₀ : V} (hd₀ : Q d₀ ≠ 0) (hd₀w : ∀ j : ℤ, |j| ≤ k → bform Q (w j) d₀ = 0)
    (hdim : finrank F V = 2 * k + 2) :
    IsInOrbitNu Q ⊤ ν (adV Q (regNil Q w ν k)) := by
  have hsymm : ∀ x y, bform Q x y = bform Q y x := fun x y => QuadraticMap.associated_isSymm F Q x y
  have hQb : ∀ x, bform Q x x = Q x := fun x => QuadraticMap.associated_eq_self_apply F Q x
  set U₁ := Submodule.span F (Set.range fun i : Fin (2 * k + 1) => w ((i : ℤ) - k))
  have hwU : ∀ j : ℤ, |j| ≤ k → w j ∈ U₁ := fun j hj => Submodule.subset_span
    ⟨⟨(j + k).toNat, by rw [abs_le] at hj; omega⟩, by
      simp only; congr 1; rw [abs_le] at hj; omega⟩
  have hU : finrank F U₁ = 2 * k + 1 := by
    rw [finrank_span_eq_card (linearIndependent_isSplitFamily hw hν), Fintype.card_fin]
  have hd₀U : ∀ u ∈ U₁, bform Q d₀ u = 0 := by
    have hle : U₁ ≤ LinearMap.ker (bform Q d₀) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have hi := i.2
      simp only [SetLike.mem_coe, LinearMap.mem_ker]
      rw [hsymm]; exact hd₀w _ (abs_le.2 ⟨by omega, by omega⟩)
    exact fun u hu => hle hu
  have hd₀0 : d₀ ≠ 0 := fun h => hd₀ (by rw [h, map_zero])
  refine ⟨d₀, U₁, Submodule.mem_top, hd₀, le_top, hd₀U, ?_, adV_regNil_of_orthogonal hd₀w,
    fun u hu => adV_regNil_mem_span hw hν hu, ?_, w 0, hwU 0 (by simp), ?_, ?_⟩
  · -- `⟨d₀⟩ ⊔ U₁ = V`
    have hinf : Submodule.span F {d₀} ⊓ U₁ = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx1
      have := hd₀U _ hx2
      rw [map_smul, smul_eq_mul, hQb] at this
      rw [(mul_eq_zero.mp this).resolve_right hd₀, zero_smul]
      exact Submodule.zero_mem _
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F {d₀}) U₁
    rw [hinf, finrank_bot, add_zero, finrank_span_singleton hd₀0, hU] at this
    omega
  · -- one Jordan block
    obtain ⟨ε, hε, he⟩ := adV_regNil_pow_w hw hν (j := 2 * k) le_rfl
    refine ⟨w (-k), hwU _ (by simp), ?_⟩
    rw [hU, show 2 * k + 1 - 1 = 2 * k by omega, he]
    refine smul_ne_zero hε fun h0 => hν ?_
    have := hw ((2 * k : ℕ) - k) (-k) (by rw [abs_le]; push_cast; omega) (by simp)
    rw [h0, map_zero, LinearMap.zero_apply, ite_eq_left (by push_cast; ring)] at this
    exact this.symm
  · rw [← hQb, hw 0 0 (by simp) (by simp), ite_eq_left (by ring)]
  · -- `U₁ ∩ w_0^⊥` is split
    set S := U₁ ⊓ (bform Q).orthogonal (Submodule.span F {w 0})
    have hSlt : S < U₁ := by
      refine lt_of_le_of_ne inf_le_left fun hSU => ?_
      have h0 : w 0 ∈ S := hSU ▸ hwU 0 (by simp)
      have := (Submodule.mem_inf.mp h0).2 (w 0) (Submodule.mem_span_singleton_self _)
      change bform Q (w 0) (w 0) = 0 at this
      rw [hw 0 0 (by simp) (by simp), ite_eq_left (by ring)] at this
      exact hν this
    have hS : finrank F S ≤ 2 * k := by
      have := Submodule.finrank_lt_finrank_of_lt hSlt; omega
    set T := Submodule.span F (Set.range fun i : Fin k => w ((i : ℤ) + 1))
    have hTS : T ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have hi := i.2
      refine ⟨hwU _ (abs_le.2 ⟨by omega, by omega⟩), fun x hx => ?_⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      change bform Q (c • w 0) (w ((i : ℤ) + 1)) = 0
      rw [map_smul, LinearMap.smul_apply, hw 0 _ (by simp) (abs_le.2 ⟨by omega, by omega⟩),
        ite_eq_right (by omega), smul_zero]
    have hTiso : ∀ y ∈ T, ∀ z ∈ T, bform Q y z = 0 := by
      have hgen : ∀ i j : Fin k, bform Q (w ((i : ℤ) + 1)) (w ((j : ℤ) + 1)) = 0 := by
        intro i j
        have := i.2; have := j.2
        rw [hw _ _ (abs_le.2 ⟨by omega, by omega⟩) (abs_le.2 ⟨by omega, by omega⟩),
          ite_eq_right (by omega)]
      have h1 : ∀ i : Fin k, T ≤ LinearMap.ker (bform Q (w ((i : ℤ) + 1))) := fun i => by
        rw [Submodule.span_le]; rintro _ ⟨j, rfl⟩; exact hgen i j
      intro y hy z hz
      induction hy using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h1 i hz
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
      | smul c a _ ha => rw [map_smul, LinearMap.smul_apply, ha, smul_zero]
    have hTk : finrank F T = k := by
      let f : Fin k → Fin (2 * k + 1) := fun i => ⟨i + 1 + k, by omega⟩
      have hf : Function.Injective f := fun a b h => Fin.ext (by
        have := congrArg Fin.val h; simp only [f] at this; omega)
      have hli := (linearIndependent_isSplitFamily hw hν).comp f hf
      have e : ((fun i : Fin (2 * k + 1) => w ((i : ℤ) - k)) ∘ f) =
          fun i : Fin k => w ((i : ℤ) + 1) := by
        funext i; simp only [Function.comp, f]; congr 1; push_cast; ring
      rw [e] at hli
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    set T' := T.comap S.subtype
    have hT' : finrank F T' = k := by
      rw [(Submodule.comapSubtypeEquivOfLe hTS).finrank_eq, hTk]
    have hiso : IsTotallyIsotropic (Q.comp S.subtype) T' := by
      intro u hu
      have huT : (u : V) ∈ T := hu
      change Q (u : V) = 0
      rw [← hQb]; exact hTiso _ huT _ huT
    have := QuadClassify.le_wittIndex hiso
    unfold IsSplitQF
    omega

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

/-- **Witt data for `O_{−ν}` in `W`** (the second Witt-theory step in the docstring of
`exists_regularNil_inOrbitNu`): for a quasi-split GGP datum with `dim W = 2s + 2` even, `W` contains
hyperbolic pairs `h_0, …, h_{2s-1}`, a vector `u` with `q(u) = −ν` and an anisotropic `d₀`, all
mutually orthogonal (`W ≅ ⟨b⟩ ⊥ ⟨−ν⟩ ⊥ H^s`).

**Status: `sorry`** (quadratic forms only). Sketch: `V = W ⊥ Z` is odd and quasi-split, hence split,
`V ≅ ⟨b⟩ ⊥ H^{s+1+r}`; also `V ≅ W ⊥ ⟨ν⟩ ⊥ H^r`. Witt cancellation of `H^r` and adding `⟨−ν⟩`
(`⟨ν⟩ ⊥ ⟨−ν⟩ ≅ H`) give `W ⊥ H ≅ ⟨b⟩ ⊥ ⟨−ν⟩ ⊥ H^{s+1}`, and cancelling `H` gives the claim. -/
theorem exists_wittData_W (d : GGPData F) (hqs : d.IsQuasiSplit) (s : ℕ) (hm : d.m = 2 * s + 2) :
    ∃ (h : ℕ → Fin d.m → F) (u d₀ : Fin d.m → F), (∀ i j : ℕ, i < 2 * s → j < 2 * s →
      bform d.QW (h i) (h j) = if i + j + 1 = 2 * s then 1 else 0) ∧
      d.QW u = -(d.ν : F) ∧ d.QW d₀ ≠ 0 ∧ bform d.QW u d₀ = 0 ∧
      (∀ j : ℕ, j < 2 * s → bform d.QW u (h j) = 0) ∧
      (∀ j : ℕ, j < 2 * s → bform d.QW d₀ (h j) = 0) := by
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

**Status: proved**, except the second Witt-theory step (`exists_wittData_W`). The element is
`regNil` on a split family built from `Z` and the hyperbolic part of `W` (first case) or from
`exists_wittData_W` (second case); it is regular nilpotent (`isRegularNil_regNil`) and lies in `O_ν`
(`isInOrbitNu_regNil`). -/
theorem exists_regularNil_inOrbitNu {F : Type*} [NontriviallyNormedField F] [PAdicField F]
    (d : GGPData F) (hqs : d.IsQuasiSplit) :
    (Even (finrank F d.V) → 4 ≤ finrank F d.V →
      ∃ X : CliffordAlgebra d.QV, IsRegularNil (gspin d.QV) X ∧
        IsInOrbitNu d.QV ⊤ (d.ν : F) (adV d.QV X)) ∧
    (Even d.m → 4 ≤ d.m →
      ∃ X : CliffordAlgebra d.QW, IsRegularNil (gspin d.QW) X ∧
        IsInOrbitNu d.QW ⊤ (-(d.ν : F)) (adV d.QW X)) := by
  have hν : (d.ν : F) ≠ 0 := d.ν.ne_zero
  have hsymmW : ∀ x y, bform d.QW x y = bform d.QW y x :=
    fun x y => QuadraticMap.associated_isSymm F d.QW x y
  have hQbW : ∀ x, bform d.QW x x = d.QW x := fun x => QuadraticMap.associated_eq_self_apply F d.QW x
  constructor
  · intro hev h4
    have hdimV : finrank F d.V = d.m + (2 * d.r + 1) := by
      rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]
    have hodd : Odd (finrank F (Fin d.m → F)) := by
      rw [Module.finrank_fin_fun]; rw [hdimV] at hev
      obtain ⟨t, ht⟩ := hev; exact ⟨t - d.r - 1, by omega⟩
    obtain ⟨s, h, a, hh, ha, hah, hm⟩ := exists_hyp_of_quasiSplit_odd d.nondeg hqs.1 hodd
    rw [Module.finrank_fin_fun] at hm
    let wZ : ℤ → d.V := fun j => (0, zvec d.r j)
    have hwZ : IsSplitFamily d.QV wZ (d.ν : F) d.r := by
      intro i j hi hj
      rw [bform_prod]
      simp only [wZ, map_zero, zero_add]
      exact bform_splitOddForm_zvec d.r _ hi hj
    let hV : ℕ → d.V := fun b => (h b, 0)
    have hw : IsSplitFamily d.QV (extFamily wZ hV (d.ν : F) d.r s) (d.ν : F) (d.r + s) :=
      isSplitFamily_extFamily hwZ (fun i j hi hj => by
        rw [bform_prod]; simp only [hV, map_zero, add_zero]; exact hh i j hi hj)
        (fun j _ b _ => by rw [bform_prod]; simp [wZ, hV])
    have hdim : finrank F d.V = 2 * (d.r + s) + 2 := by omega
    refine ⟨_, isRegularNil_regNil d.nondeg_QV hw hν hdim.le, isInOrbitNu_regNil hw hν
      (d₀ := (a, 0)) ?_ (fun j hj => ?_) hdim⟩
    · simpa using ha
    · have hj' := abs_le.mp hj
      push_cast at hj'
      simp only [extFamily]
      split_ifs with h1 h2
      · rw [bform_prod]; simp [wZ]
      · rw [bform_prod]
        simp only [hV, Prod.smul_fst, Prod.smul_snd, smul_zero, map_smul, LinearMap.smul_apply,
          map_zero, add_zero]
        rw [hsymmW, hah _ (by rw [abs_le] at h1; omega), smul_zero]
      · rw [bform_prod]; simp only [hV, map_zero, add_zero]
        rw [hsymmW, hah _ (by rw [abs_le] at h1; omega)]
  · intro hev h4
    obtain ⟨s, hs⟩ : ∃ s, d.m = 2 * s + 2 := by
      obtain ⟨t, ht⟩ := hev; exact ⟨t - 1, by omega⟩
    obtain ⟨h, u, d₀, hh, hu, hd₀, hud, huh, hdh⟩ := exists_wittData_W d hqs s hs
    have hw : IsSplitFamily d.QW (extFamily (fun _ => u) h (-(d.ν : F)) 0 s) (-(d.ν : F)) (0 + s) :=
      isSplitFamily_extFamily (fun i j hi hj => by
        have hi0 : i = 0 := by rw [abs_le] at hi; omega
        have hj0 : j = 0 := by rw [abs_le] at hj; omega
        subst hi0 hj0; simp [hQbW, hu]) hh (fun j _ b hb => huh b hb)
    have hdim : finrank F (Fin d.m → F) = 2 * (0 + s) + 2 := by rw [Module.finrank_fin_fun]; omega
    refine ⟨_, isRegularNil_regNil d.nondeg hw (neg_ne_zero.2 hν) hdim.le,
      isInOrbitNu_regNil hw (neg_ne_zero.2 hν) hd₀ (fun j hj => ?_) hdim⟩
    have hj' := abs_le.mp hj
    push_cast at hj'
    simp only [extFamily]
    split_ifs with h1 h2
    · exact hud
    · rw [map_smul, LinearMap.smul_apply, hsymmW, hdh _ (by rw [abs_le] at h1; omega), smul_zero]
    · rw [hsymmW, hdh _ (by rw [abs_le] at h1; omega)]

end NilReg

end GSpinGGP
