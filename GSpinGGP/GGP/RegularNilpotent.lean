/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.RegularNilpotent
import GSpinGGP.Literature.NilpotentOrbits
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

end GSpinGGP
