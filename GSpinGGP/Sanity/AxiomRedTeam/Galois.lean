/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Main
import GSpinGGP.Literature.NilpotentOrbits
import GSpinGGP.Literature.Kottwitz1986
import GSpinGGP.Literature.KottwitzClay
import GSpinGGP.GGP.GammaClassFinite
import GSpinGGP.Sanity.Witnesses

/-!
# Checks of the Jantzen, Borel–Serre and Kottwitz axioms

* `jantzen_finrank_soCentMat_ge`: proved for `n = 3` (and `n = 2`, outside the axiom's range) over
  any field (`jantzen_ge_three`, `jantzen_ge_two`), from `so(Φ)_X ≠ 0` (`soCentMat_ne_bot`).
* `jantzen_regularNil_partition`: proved for `n = 3`, `Φ` antidiagonal, over any field of
  characteristic `0` (`jantzen_partition_three`; `so(3)` has no nilpotent of partition `[2,1]`).
  At `n = 4` both Jantzen axioms together return the partition `[3,1]` of an explicit regular
  nilpotent `X₄`, which is also computed directly (`partition_four_via_axioms`, `X₄_pow`).
* `finite_H1_torusBar`, `finite_H1_normalizerBar`: `H¹` of the trivial group is a point; this
  covers central `x` (`finite_H1_torusBar_central`) and `dim W = 0`, e.g. `toyData`
  (`finite_H1_dim_zero`, `finite_H1_toyData`).  The Galois stability of the groups of
  `F̄`-points involved is proved in the library (`galGL_mem_torusBarFbar`, `galGL_mem_fixerBar`,
  `GGPData.isGalStable_normalizerBar`).
* `exists_rel_torusBar_of_fixerBar`: for central `x`, `(SO(W)_{W'_x})(F̄) = 1` and the conclusion
  holds with the trivial cocycle (`exists_rel_central`).
* `kottwitz_nilpotent_sq_smul`: holds for `N = 0` (`kottwitz_sq_smul_zero`) and on `toyData`,
  where every nilpotent of `𝔤_s` is `0` (`kottwitz_sq_smul_toy`).

Not covered: `H¹` of a nontrivial torus, nonzero nilpotents in `kottwitz_nilpotent_sq_smul`,
the Jantzen axioms for `n ≥ 5`.
-/

noncomputable section

open Module

namespace GSpinGGP.AxiomRedTeam

/-- Independent of the axioms: for `n ≥ 2` and any field, `so(Φ)_X ≠ 0`. -/
theorem soCentMat_ne_bot {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n)
    (Φ : Matrix (Fin n) (Fin n) K) (hΦ : Φ.transpose = Φ) (hdet : Φ.det ≠ 0)
    (X : Matrix (Fin n) (Fin n) K) (hX : X ∈ skewAdjointMatricesSubmodule Φ) :
    soCentMat Φ X ≠ ⊥ := by
  classical
  by_cases hX0 : X = 0
  · subst hX0
    let a : Fin n := ⟨0, by omega⟩
    let b : Fin n := ⟨1, by omega⟩
    have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
    let S : Matrix (Fin n) (Fin n) K := Matrix.single a b 1 - Matrix.single b a 1
    have hS : S.transpose = -S := by
      simp [S, Matrix.transpose_sub, Matrix.transpose_single]
    have hu : IsUnit Φ.det := isUnit_iff_ne_zero.2 hdet
    have hΦi : Φ⁻¹.transpose = Φ⁻¹ := by rw [Matrix.transpose_nonsing_inv, hΦ]
    have hmem : Φ⁻¹ * S ∈ soCentMat Φ 0 := by
      refine ⟨?_, ?_⟩
      · change Φ⁻¹ * S ∈ skewAdjointMatricesSubmodule Φ
        rw [mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
        rw [Matrix.transpose_mul, hS, hΦi, Matrix.mul_neg, ← Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_assoc,
          Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
      · change Φ⁻¹ * S ∈ Set.centralizer {0}
        simp [Set.mem_centralizer_iff]
    intro hbot
    rw [hbot, Submodule.mem_bot] at hmem
    have : S = 0 := by
      have := congrArg (Φ * ·) hmem
      simpa [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu] using this
    have h2 := congrFun (congrFun this a) b
    simp [S, hab, hab.symm] at h2
  · intro hbot
    have hmem : X ∈ soCentMat Φ X :=
      ⟨hX, by change X ∈ Set.centralizer {X}; simp [Set.mem_centralizer_iff]⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hX0 hmem

/-- `jantzen_finrank_soCentMat_ge` for `n = 3`, any field, proved without axioms. -/
theorem jantzen_ge_three {K : Type*} [Field K]
    (Φ : Matrix (Fin 3) (Fin 3) K) (hΦ : Φ.transpose = Φ) (hdet : Φ.det ≠ 0)
    (X : Matrix (Fin 3) (Fin 3) K) (hX : X ∈ skewAdjointMatricesSubmodule Φ) :
    3 / 2 ≤ finrank K (soCentMat Φ X) := by
  have h := soCentMat_ne_bot (by norm_num) Φ hΦ hdet X hX
  have : 0 < finrank K (soCentMat Φ X) := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact h (Submodule.finrank_eq_zero.1 h0)
  omega

/-- `n = 2` (outside the axiom's range `3 ≤ n`, but the bound `⌊n/2⌋` still holds). -/
theorem jantzen_ge_two {K : Type*} [Field K]
    (Φ : Matrix (Fin 2) (Fin 2) K) (hΦ : Φ.transpose = Φ) (hdet : Φ.det ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) K) (hX : X ∈ skewAdjointMatricesSubmodule Φ) :
    2 / 2 ≤ finrank K (soCentMat Φ X) := by
  have h := soCentMat_ne_bot le_rfl Φ hΦ hdet X hX
  have : 0 < finrank K (soCentMat Φ X) := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact h (Submodule.finrank_eq_zero.1 h0)
  omega

/-- The antidiagonal form on `K³`. -/
def Φ₀ (K : Type*) [Field K] : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem Φ₀_symm (K : Type*) [Field K] : (Φ₀ K).transpose = Φ₀ K := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem Φ₀_det (K : Type*) [Field K] : (Φ₀ K).det ≠ 0 := by
  simp [Φ₀, Matrix.det_fin_three]

/-- The matrix `!![a, b, 0; c, 0, -b; 0, -c, -a]`. -/
def soMk {K : Type*} [Field K] (a b c : K) : Matrix (Fin 3) (Fin 3) K :=
  !![a, b, 0; c, 0, -b; 0, -c, -a]

theorem soMk_mem {K : Type*} [Field K] (a b c : K) :
    soMk a b c ∈ skewAdjointMatricesSubmodule (Φ₀ K) := by
  rw [mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  ext i j; fin_cases i <;> fin_cases j <;> simp [soMk, Φ₀, Matrix.mul_apply, Fin.sum_univ_three]

/-- Normal form of `so(Φ₀)`. -/
theorem so3_form {K : Type*} [Field K] [CharZero K] {X : Matrix (Fin 3) (Fin 3) K}
    (hX : X ∈ skewAdjointMatricesSubmodule (Φ₀ K)) : X = soMk (X 0 0) (X 0 1) (X 1 0) := by
  rw [mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] at hX
  have e : ∀ i j, (X.transpose * Φ₀ K) i j = ((Φ₀ K) * -X) i j := fun i j => by rw [hX]
  have e00 := e 0 0; have e01 := e 0 1; have e02 := e 0 2
  have e11 := e 1 1; have e12 := e 1 2; have e22 := e 2 2
  simp [Φ₀, Matrix.mul_apply, Fin.sum_univ_three] at e00 e01 e02 e11 e12 e22
  have h20 : X 2 0 = 0 := by linear_combination (e00) / 2
  have h11 : X 1 1 = 0 := by linear_combination (e11) / 2
  have h02 : X 0 2 = 0 := by linear_combination (e22) / 2
  have h12 : X 1 2 = -X 0 1 := by linear_combination e12
  have h21 : X 2 1 = -X 1 0 := by linear_combination e01
  have h22 : X 2 2 = -X 0 0 := by linear_combination e02
  ext i j; fin_cases i <;> fin_cases j <;> simp [soMk, h20, h11, h02, h12, h21, h22]

/-- In `so(Φ₀)`, `X² = 0` forces `X = 0` (no nilpotent of partition `[2,1]`). -/
theorem eq_zero_of_sq {K : Type*} [Field K] [CharZero K] {X : Matrix (Fin 3) (Fin 3) K}
    (hX : X ∈ skewAdjointMatricesSubmodule (Φ₀ K)) (h2 : X ^ 2 = 0) : X = 0 := by
  rw [so3_form hX] at h2 ⊢
  generalize X 0 0 = a, X 0 1 = b, X 1 0 = c at h2 ⊢
  have e := fun i j => congrFun (congrFun h2 i) j
  have e02 := e 0 2; have e20 := e 2 0; have e00 := e 0 0
  simp [soMk, sq] at e02 e20 e00
  have hb : b = 0 := by simpa using e02
  have hc : c = 0 := by simpa using e20
  have ha : a = 0 := mul_self_eq_zero.1 (by simpa [hc] using e00)
  rw [ha, hb, hc]; ext i j; fin_cases i <;> fin_cases j <;> simp [soMk]

/-- The regular nilpotent `Y₀ = soMk 0 1 0`. -/
theorem cent_Y₀_le {K : Type*} [Field K] [CharZero K] :
    soCentMat (Φ₀ K) (soMk 0 1 0) ≤ K ∙ soMk (0 : K) 1 0 := by
  intro B hB
  obtain ⟨hBs, hBc⟩ := hB
  have hc : B * soMk 0 1 0 = soMk 0 1 0 * B := by
    have : B ∈ Set.centralizer {soMk (0 : K) 1 0} := hBc
    rw [Set.mem_centralizer_iff] at this
    exact (this _ rfl).symm
  rw [so3_form hBs] at hc ⊢
  generalize B 0 0 = a, B 0 1 = b, B 1 0 = c at hc ⊢
  have e := fun i j => congrFun (congrFun hc i) j
  have e00 := e 0 0; have e01 := e 0 1
  simp [soMk] at e00 e01
  subst e01; rw [← e00]
  rw [Submodule.mem_span_singleton]
  exact ⟨b, by ext i j; fin_cases i <;> fin_cases j <;> simp [soMk]⟩

theorem finrank_cent_Y₀ {K : Type*} [Field K] [CharZero K] :
    finrank K (soCentMat (Φ₀ K) (soMk 0 1 0)) ≤ 1 := by
  refine (Submodule.finrank_mono cent_Y₀_le).trans ?_
  have := finrank_span_le_card (R := K) ({soMk (0 : K) 1 0} : Set _)
  simpa using this

theorem two_le_finrank_so {K : Type*} [Field K] [CharZero K] :
    2 ≤ finrank K (soCentMat (Φ₀ K) 0) := by
  have hli : LinearIndependent K ![soMk (1 : K) 0 0, soMk 0 1 0] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    simp [soMk] at h00 h01
    exact ⟨h00, h01⟩
  have hle : Submodule.span K (Set.range ![soMk (1 : K) 0 0, soMk 0 1 0]) ≤
      soCentMat (Φ₀ K) 0 := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨?_, ?_⟩
    · fin_cases i <;> exact soMk_mem _ _ _
    · change _ ∈ Set.centralizer {0}; simp [Set.mem_centralizer_iff]
  have := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hli] at this
  simpa using this

/-- `jantzen_regularNil_partition` for `n = 3`, `Φ = Φ₀`, proved without axioms (any field of
characteristic `0`; `IsAlgClosed` not needed). -/
theorem jantzen_partition_three {K : Type*} [Field K] [CharZero K]
    (X : Matrix (Fin 3) (Fin 3) K) (hX : X ∈ skewAdjointMatricesSubmodule (Φ₀ K))
    (hreg : ∀ Y ∈ skewAdjointMatricesSubmodule (Φ₀ K), IsNilpotent Y →
      finrank K (soCentMat (Φ₀ K) X) ≤ finrank K (soCentMat (Φ₀ K) Y)) :
    (Odd 3 → X ^ (3 - 1) ≠ 0) ∧ (Even 3 → X ^ (3 - 2) ≠ 0 ∧ X ^ (3 - 1) = 0) := by
  refine ⟨fun _ h2 => ?_, fun h => absurd h (by decide)⟩
  have hY : IsNilpotent (soMk (0 : K) 1 0) :=
    ⟨3, by ext i j; fin_cases i <;> fin_cases j <;> simp [soMk, pow_succ]⟩
  have h1 := (hreg _ (soMk_mem 0 1 0) hY).trans finrank_cent_Y₀
  have hX0 := eq_zero_of_sq hX h2
  subst hX0
  have := two_le_finrank_so (K := K)
  omega

/-- The regular nilpotent `Y₀` of `so(Φ₀)` satisfies the conclusion of
`jantzen_regularNil_partition` for `n = 3`: `Y₀² ≠ 0`. -/
theorem Y₀_sq_ne_zero {K : Type*} [Field K] : (soMk (0 : K) 1 0) ^ 2 ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 2
  simp [soMk, sq] at this

def Φ₄ (K : Type*) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
def N₁ (K : Type*) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, -1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0]
def N₂ (K : Type*) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, -1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0]
/-- A regular nilpotent of `so(Φ₄)` (partition `[3, 1]`). -/
def X₄ (K : Type*) [Field K] : Matrix (Fin 4) (Fin 4) K := N₁ K + N₂ K

theorem Φ₄_symm (K : Type*) [Field K] : (Φ₄ K).transpose = Φ₄ K := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem Φ₄_det (K : Type*) [Field K] : (Φ₄ K).det ≠ 0 := by
  simp [Φ₄, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem X₄_mem (K : Type*) [Field K] : X₄ K ∈ skewAdjointMatricesSubmodule (Φ₄ K) := by
  rw [mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [X₄, N₁, N₂, Φ₄, Matrix.mul_apply, Fin.sum_univ_four]

set_option linter.style.longLine false in
theorem cent_X₄_le (K : Type*) [Field K] [CharZero K] :
    soCentMat (Φ₄ K) (X₄ K) ≤ Submodule.span K {N₁ K, N₂ K} := by
  rintro B ⟨hBs, hBc⟩
  have hc : B * X₄ K = X₄ K * B := by
    have : B ∈ Set.centralizer {X₄ K} := hBc
    rw [Set.mem_centralizer_iff] at this
    exact (this _ rfl).symm
  have hBs' : B ∈ skewAdjointMatricesSubmodule (Φ₄ K) := hBs
  rw [mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] at hBs'
  have s := fun i j => congrFun (congrFun hBs' i) j
  have c := fun i j => congrFun (congrFun hc i) j
  have s00 := s 0 0
  have s01 := s 0 1
  have s02 := s 0 2
  have s03 := s 0 3
  have s10 := s 1 0
  have s11 := s 1 1
  have s12 := s 1 2
  have s13 := s 1 3
  have s20 := s 2 0
  have s21 := s 2 1
  have s22 := s 2 2
  have s23 := s 2 3
  have s30 := s 3 0
  have s31 := s 3 1
  have s32 := s 3 2
  have s33 := s 3 3
  have c00 := c 0 0
  have c01 := c 0 1
  have c02 := c 0 2
  have c03 := c 0 3
  have c10 := c 1 0
  have c11 := c 1 1
  have c12 := c 1 2
  have c13 := c 1 3
  have c20 := c 2 0
  have c21 := c 2 1
  have c22 := c 2 2
  have c23 := c 2 3
  have c30 := c 3 0
  have c31 := c 3 1
  have c32 := c 3 2
  have c33 := c 3 3
  simp [X₄, N₁, N₂, Φ₄, Matrix.mul_apply, Fin.sum_univ_four] at s00 s01 s02 s03 s10 s11 s12 s13 s20 s21 s22 s23 s30 s31 s32 s33 c00 c01 c02 c03 c10 c11 c12 c13 c20 c21 c22 c23 c30 c31 c32 c33
  clear s c hBs hBs' hBc hc
  rw [Submodule.mem_span_pair]
  refine ⟨-B 0 1, -B 0 2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [N₁, N₂] <;> grind

theorem finrank_cent_X₄ (K : Type*) [Field K] [CharZero K] :
    finrank K (soCentMat (Φ₄ K) (X₄ K)) ≤ 2 := by
  classical
  refine (Submodule.finrank_mono (cent_X₄_le K)).trans ?_
  have := finrank_span_le_card (R := K) ({N₁ K, N₂ K} : Set _)
  exact this.trans (by simpa using Finset.card_insert_le (N₁ K) {N₂ K})

/-- Axiom-free: `X₄` has partition `[3, 1]`, i.e. `X₄² ≠ 0`, `X₄³ = 0`. -/
theorem X₄_pow (K : Type*) [Field K] [CharZero K] : X₄ K ^ 2 ≠ 0 ∧ X₄ K ^ 3 = 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · have := congrFun (congrFun h 0) 3
    norm_num [X₄, N₁, N₂, sq, Matrix.mul_apply, Fin.sum_univ_four] at this
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [X₄, N₁, N₂, pow_succ, Matrix.mul_apply, Fin.sum_univ_four]

theorem X₄_nil (K : Type*) [Field K] [CharZero K] : IsNilpotent (X₄ K) :=
  ⟨3, (X₄_pow K).2⟩

/-- Uses BOTH Jantzen axioms (the `≥` axiom discharges `hreg`): the partition axiom at `n = 4`
applied to `X₄` returns exactly the axiom-free `X₄_pow` (even branch, exponents `n-2`,
`n-1`). -/
theorem partition_four_via_axioms (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    X₄ K ^ (4 - 2) ≠ 0 ∧ X₄ K ^ (4 - 1) = 0 := by
  refine (jantzen_regularNil_partition (by norm_num) (Φ₄ K) (Φ₄_symm K) (Φ₄_det K) (X₄ K)
    (X₄_mem K) (X₄_nil K) fun Y hY _ => ?_).2 ⟨2, rfl⟩
  exact (finrank_cent_X₄ K).trans
    (jantzen_finrank_soCentMat_ge (by norm_num) (Φ₄ K) (Φ₄_symm K) (Φ₄_det K) Y hY)

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

/-- `H¹(F, 1)` is a point. -/
theorem subsingleton_H1_of_eq_bot {m : ℕ} {S : Subgroup (GL (Fin m) Kb)} (hS : S = ⊥) :
    Subsingleton (H1 S) := by
  refine ⟨fun β β' => ?_⟩
  induction β using H1.ind with | h a => ?_
  induction β' using H1.ind with | h b => ?_
  exact H1.mk_eq_mk.2 (GalCocycle.rel_trans (GalCocycle.rel_symm
    (GalCocycle.rel_one_of_eq_bot hS a)) (GalCocycle.rel_one_of_eq_bot hS b))

omit [PAdicField F] in
/-- Every subgroup of `GL_0` is trivial. -/
theorem eq_bot_of_dim_zero (S : Subgroup (GL (Fin 0) Kb)) : S = ⊥ :=
  Subgroup.eq_bot_of_subsingleton S

/-! ### `finite_H1_torusBar`: instances proved without the axiom -/

/-- Central `x` (the atom `1` of `Γ(G,H)`, `isGammaElt_of_central`): `H¹(F, S_x)` is a point. -/
theorem finite_H1_torusBar_central (d : GGPData F) (x : ↥(GSpin d.QW)) (hx : IsCentralW d x) :
    d.IsGammaElt x ∧ Finite (H1 (d.torusBarFbar x)) := by
  refine ⟨isGammaElt_of_central x hx, ?_⟩
  have := subsingleton_H1_of_eq_bot (torusBarFbar_eq_bot_of_central x hx)
  exact Finite.of_subsingleton

/-- `dim W = 0` (e.g. `toyData`): both `H¹` sets are points. -/
theorem finite_H1_dim_zero (d : GGPData F) (hm : d.m = 0) (x : ↥(GSpin d.QW)) :
    Finite (H1 (d.torusBarFbar x)) ∧ Finite (H1 (d.normalizerBar x)) := by
  obtain ⟨m, QW, nd, r, ν⟩ := d
  subst hm
  exact ⟨@Finite.of_subsingleton _ (subsingleton_H1_of_eq_bot (eq_bot_of_dim_zero _)),
    @Finite.of_subsingleton _ (subsingleton_H1_of_eq_bot (eq_bot_of_dim_zero _))⟩

theorem finite_H1_toyData (x : ↥(GSpin (Sanity.toyData (K := F)).QW)) :
    Finite (H1 ((Sanity.toyData (K := F)).torusBarFbar x)) ∧
      Finite (H1 ((Sanity.toyData (K := F)).normalizerBar x)) :=
  finite_H1_dim_zero _ rfl x

/-! ### `exists_rel_torusBar_of_fixerBar`: central `x` and `dim W = 0`, without the axiom -/

theorem fixerBar_eq_bot_of_central (d : GGPData F) (x : ↥(GSpin d.QW)) (hx : IsCentralW d x) :
    d.fixerBar x = ⊥ := by
  obtain ⟨c, rfl⟩ := hx
  rw [eq_bot_iff]
  rintro s ⟨g, hg, rfl⟩
  rw [Subgroup.mem_bot]
  have hP : specP (d.QW.baseChange (AlgebraicClosure F)) g = 1 := by
    refine LinearEquiv.ext fun w => hg w ?_
    rw [fixedSub_scalar, Submodule.baseChange_top]
    trivial
  apply Units.ext
  rw [coe_specMatFbar, hP]
  simp

theorem exists_rel_of_fixerBar_eq_bot (d : GGPData F) (x : ↥(GSpin d.QW))
    (hF : d.fixerBar x = ⊥) (c : GalCocycle (d.fixerBar x)) :
    ∃ a : GalCocycle (d.torusBarFbar x), ∃ h ∈ d.fixerBar x,
      ∀ σ : GalF F, a.toFun σ = h⁻¹ * c.toFun σ * galGL d.m σ h := by
  refine ⟨GalCocycle.one _, 1, Subgroup.one_mem _, fun σ => ?_⟩
  have : c.toFun σ = 1 := by
    have h := c.mem' σ
    rw [Subgroup.mem_carrier.symm] at h
    simpa [hF] using h
  simp [GalCocycle.one, this]

theorem exists_rel_central (d : GGPData F) (x : ↥(GSpin d.QW)) (hx : IsCentralW d x)
    (c : GalCocycle (d.fixerBar x)) :
    ∃ a : GalCocycle (d.torusBarFbar x), ∃ h ∈ d.fixerBar x,
      ∀ σ : GalF F, a.toFun σ = h⁻¹ * c.toFun σ * galGL d.m σ h :=
  exists_rel_of_fixerBar_eq_bot d x (fixerBar_eq_bot_of_central d x hx) c

/-! ### `kottwitz_nilpotent_sq_smul`: `N = 0` and `toyData`, without the axiom -/

theorem kottwitz_sq_smul_zero (d : GGPData F) (s : ↥d.G) (α : F) :
    ∃ h : ↥d.G, h * s = s * h ∧
      ((h : d.ambientˣ) : d.ambient) * 0 * ((h⁻¹ : d.ambientˣ) : d.ambient) =
        (α ^ 2) • (0 : d.ambient) :=
  ⟨1, by simp, by simp⟩

omit [PAdicField F] in
theorem scalar_nil_eq_zero {A : Type*} [Ring A] [Algebra F A] {a : F}
    (h : IsNilpotent (algebraMap F A a)) : algebraMap F A a = 0 := by
  by_cases ha : a = 0
  · simp [ha]
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  · exact absurd h ((IsUnit.mk0 a ha).map (algebraMap F A)).not_isNilpotent

/-- In `toyData` every nilpotent `N ∈ 𝔤` is `0`, so the conclusion holds with `h = 1`. -/
theorem kottwitz_sq_smul_toy (s : ↥(Sanity.toyData (K := F)).G)
    {N : (Sanity.toyData (K := F)).ambient}
    (hN : N ∈ lieCentralizer (Sanity.toyData (K := F)).lie
      ((s : (Sanity.toyData (K := F)).ambientˣ) : _))
    (hNnil : IsNilpotent N) {α : F} :
    ∃ h : ↥(Sanity.toyData (K := F)).G, h * s = s * h ∧
      ((h : (Sanity.toyData (K := F)).ambientˣ) : (Sanity.toyData (K := F)).ambient) * N *
        ((h⁻¹ : (Sanity.toyData (K := F)).ambientˣ) : _) = (α ^ 2) • N := by
  obtain ⟨a, b, rfl⟩ := Sanity.toy_lie_scalar (mem_lieCentralizer.1 hN).1
  have h1 := hNnil.map (RingHom.fst _ _)
  have h2 := hNnil.map (RingHom.snd _ _)
  simp only [RingHom.coe_fst, RingHom.coe_snd] at h1 h2
  rw [scalar_nil_eq_zero h1, scalar_nil_eq_zero h2]
  exact ⟨1, by simp, by simp⟩

end GSpinGGP.AxiomRedTeam
