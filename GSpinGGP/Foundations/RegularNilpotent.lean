/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.SoCentralizer

/-!
# An explicit regular nilpotent element of `gspin(V)`

Let `w_{-k}, …, w_k ∈ V` satisfy `b(w_i, w_j) = ν δ_{i+j,0}` with `ν ≠ 0` (a copy of the split
space `Z_k(ν) = ⟨ν⟩ ⊕ H^k` of Thesis (5.2.1)). The element
`X = (2ν)⁻¹ Σ_{0 ≤ i < k} ι(w_{i+1}) ι(w_{-i})` of `gspin(V)` acts on `V` by
`w_l ↦ ± w_{l+1}` (`w_k ↦ 0`), killing `⟨w⟩^⊥`: one Jordan block on `⟨w⟩`. It is nilpotent in
`C(V)`, since `[h, X] = X` for `h = (2ν)⁻¹ Σ_j j ι(w_j) ι(w_{-j})`, which acts on `w_l` by `l`.
When `V = ⟨w⟩ ⊕ ⟨w⟩^⊥` with `dim ⟨w⟩^⊥ ≤ 1`, its centralizer in `gspin(V)` has dimension at most
`dim V − k` (`finrank_lieCentralizer_regNil_le`), which is the rank of `gspin(V)`.
-/

noncomputable section

open CliffordAlgebra Module

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

section Commutator

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]

omit [Invertible (2 : K)] in
/-- `[Σ cᵢ ι(aᵢ) ι(bᵢ), ι v] = ι(Σ cᵢ (polar(bᵢ, v) aᵢ − polar(aᵢ, v) bᵢ))`. -/
theorem sum_ι_mul_ι_commutator (Q : QuadraticForm K V) {ι' : Type*} (s : Finset ι') (c : ι' → K)
    (a b : ι' → V) (v : V) :
    (∑ i ∈ s, c i • (ι Q (a i) * ι Q (b i))) * ι Q v - ι Q v * ∑ i ∈ s, c i • (ι Q (a i) * ι Q (b i)) =
      ι Q (∑ i ∈ s, c i • (QuadraticMap.polar Q (b i) v • a i - QuadraticMap.polar Q (a i) v • b i)) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, map_smul, ← ι_mul_ι_commutator]

end Commutator

section Model

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The regular nilpotent element `X = (2ν)⁻¹ Σ_{0 ≤ i < k} ι(w_{i+1}) ι(w_{-i})`. -/
def regNil (Q : QuadraticForm K V) (w : ℤ → V) (ν : K) (k : ℕ) : CliffordAlgebra Q :=
  ∑ i ∈ Finset.range k, (2 * ν)⁻¹ • (ι Q (w (i + 1)) * ι Q (w (-i)))

/-- The grading element `h = (2ν)⁻¹ Σ_{1 ≤ j ≤ k} j ι(w_j) ι(w_{-j})`. -/
def regNilH (Q : QuadraticForm K V) (w : ℤ → V) (ν : K) (k : ℕ) : CliffordAlgebra Q :=
  ∑ j ∈ Finset.range k, ((2 * ν)⁻¹ * ((j : K) + 1)) • (ι Q (w (j + 1)) * ι Q (w (-(j + 1))))

variable {Q : QuadraticForm K V} {w : ℤ → V} {ν : K} {k : ℕ}

omit [Invertible (2 : K)] in
theorem regNil_mem_gspin : regNil Q w ν k ∈ gspin Q :=
  Submodule.sum_mem (gspin Q).toSubmodule fun _ _ =>
    (gspin Q).smul_mem _ (ι_mul_ι_mem_gspin Q _ _)

/-- The hypothesis on `w`: `b(w_i, w_j) = ν δ_{i+j,0}` for `|i|, |j| ≤ k`. -/
def IsSplitFamily (Q : QuadraticForm K V) (w : ℤ → V) (ν : K) (k : ℕ) : Prop :=
  ∀ i j : ℤ, |i| ≤ k → |j| ≤ k → bform Q (w i) (w j) = if i + j = 0 then ν else 0

theorem polar_of_isSplitFamily (hw : IsSplitFamily Q w ν k) {i j : ℤ} (hi : |i| ≤ k)
    (hj : |j| ≤ k) : QuadraticMap.polar Q (w i) (w j) = if i + j = 0 then 2 * ν else 0 := by
  rw [polar_eq_two_mul_bform, hw i j hi hj]; split_ifs <;> simp

/-- `adV X` as an explicit sum. -/
theorem adV_regNil (v : V) :
    adV Q (regNil Q w ν k) v = ∑ i ∈ Finset.range k, (2 * ν)⁻¹ •
      (QuadraticMap.polar Q (w (-i)) v • w (i + 1) - QuadraticMap.polar Q (w (i + 1)) v • w (-i)) := by
  apply ι_injective Q
  rw [ι_adV regNil_mem_gspin, regNil, sum_ι_mul_ι_commutator]

omit [Invertible (2 : K)] in
/-- `[h, ι v]` as an explicit sum. -/
theorem regNilH_commutator (v : V) :
    regNilH Q w ν k * ι Q v - ι Q v * regNilH Q w ν k = ι Q (∑ j ∈ Finset.range k,
      ((2 * ν)⁻¹ * ((j : K) + 1)) • (QuadraticMap.polar Q (w (-(j + 1))) v • w (j + 1) -
        QuadraticMap.polar Q (w (j + 1)) v • w (-(j + 1)))) := by
  rw [regNilH, sum_ι_mul_ι_commutator]

/-- `adV X` kills `⟨w⟩^⊥`. -/
theorem adV_regNil_of_orthogonal {v : V} (hv : ∀ j : ℤ, |j| ≤ k → bform Q (w j) v = 0) :
    adV Q (regNil Q w ν k) v = 0 := by
  rw [adV_regNil]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [polar_eq_two_mul_bform, polar_eq_two_mul_bform, hv (-i) (by rw [abs_neg]; simp; omega),
    hv (i + 1) (by rw [abs_le]; constructor <;> omega)]
  simp

omit [Invertible (2 : K)] in
theorem sum_range_ite_intCast_eq {M : Type*} [AddCommMonoid M] (x : M) (k : ℕ) (a : ℤ) :
    ∑ i ∈ Finset.range k, (if (i : ℤ) = a then x else 0) = if 0 ≤ a ∧ a < k then x else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single a.toNat (fun i _ hi => ite_eq_right (by omega))
      (fun h' => absurd (Finset.mem_range.mpr (by omega)) h'), ite_eq_left (by omega)]
  · exact Finset.sum_eq_zero fun i hi => ite_eq_right (by have := Finset.mem_range.mp hi; omega)

variable (hw : IsSplitFamily Q w ν k) (hν : ν ≠ 0)
include hw hν

/-- `adV X : w_l ↦ s_l w_{l+1}` with `s_l = -1` for `l < 0`, `1` for `0 ≤ l < k`, `0` for `l = k`. -/
theorem adV_regNil_w {l : ℤ} (hl : |l| ≤ k) :
    adV Q (regNil Q w ν k) (w l) =
      (if l < 0 then (-1 : K) else if l < k then 1 else 0) • w (l + 1) := by
  rw [abs_le] at hl
  rw [adV_regNil]
  have hterm : ∀ i ∈ Finset.range k, (2 * ν)⁻¹ • (QuadraticMap.polar Q (w (-i)) (w l) • w (i + 1) -
      QuadraticMap.polar Q (w (i + 1)) (w l) • w (-i)) =
      (if (i : ℤ) = l then w (l + 1) else 0) - (if (i : ℤ) = -l - 1 then w (l + 1) else 0) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [polar_of_isSplitFamily hw (abs_le.2 ⟨by omega, by omega⟩) (abs_le.2 hl),
      polar_of_isSplitFamily hw (abs_le.2 ⟨by omega, by omega⟩) (abs_le.2 hl)]
    rcases (by omega : l = i ∨ l = -i - 1 ∨ (l ≠ i ∧ l ≠ -i - 1)) with rfl | rfl | ⟨h1, h2⟩
    · simp only [show -(i : ℤ) + i = 0 by ring, show ¬ ((i : ℤ) + 1 + i = 0) by omega,
        show ¬ ((i : ℤ) = -i - 1) by omega, ↓reduceIte]
      match_scalars <;> field_simp
      simp
    · simp only [show ¬ (-(i : ℤ) + (-i - 1) = 0) by omega, show (i : ℤ) + 1 + (-i - 1) = 0 by ring,
        show ¬ ((i : ℤ) = -i - 1) by omega, show -(-(i : ℤ) - 1) - 1 = i by ring, ↓reduceIte,
        show -(i : ℤ) - 1 + 1 = -i by ring]
      match_scalars <;> field_simp
      simp
    · simp only [show ¬ (-(i : ℤ) + l = 0) by omega, show ¬ ((i : ℤ) + 1 + l = 0) by omega,
        show ¬ ((i : ℤ) = l) by omega, show ¬ ((i : ℤ) = -l - 1) by omega, ↓reduceIte]
      simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, sum_range_ite_intCast_eq,
    sum_range_ite_intCast_eq]
  split_ifs <;> first | (exfalso; omega) | simp

/-- `[h, ι(w_l)] = l ι(w_l)`. -/
theorem regNilH_commutator_w {l : ℤ} (hl : |l| ≤ k) :
    regNilH Q w ν k * ι Q (w l) - ι Q (w l) * regNilH Q w ν k = (l : K) • ι Q (w l) := by
  rw [regNilH_commutator, ← map_smul]
  congr 1
  rw [abs_le] at hl
  have hterm : ∀ j ∈ Finset.range k, ((2 * ν)⁻¹ * ((j : K) + 1)) •
      (QuadraticMap.polar Q (w (-(j + 1))) (w l) • w (j + 1) -
        QuadraticMap.polar Q (w (j + 1)) (w l) • w (-(j + 1))) =
      (if (j : ℤ) = l - 1 then (l : K) • w l else 0) +
        (if (j : ℤ) = -l - 1 then (l : K) • w l else 0) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [polar_of_isSplitFamily hw (abs_le.2 ⟨by omega, by omega⟩) (abs_le.2 hl),
      polar_of_isSplitFamily hw (abs_le.2 ⟨by omega, by omega⟩) (abs_le.2 hl)]
    rcases (by omega : l = j + 1 ∨ l = -j - 1 ∨ (l ≠ j + 1 ∧ l ≠ -j - 1)) with rfl | rfl | ⟨h1, h2⟩
    · simp only [show -((j : ℤ) + 1) + (j + 1) = 0 by ring, show ¬ ((j : ℤ) + 1 + (j + 1) = 0) by omega,
        show (j : ℤ) + 1 - 1 = j by ring, show ¬ ((j : ℤ) = -(j + 1) - 1) by omega, ↓reduceIte]
      match_scalars <;> field_simp
      simp
    · simp only [show (j : ℤ) + 1 + (-j - 1) = 0 by ring, show ¬ ((j : ℤ) = -j - 1 - 1) by omega,
        show ¬ (-(j : ℤ) - 1 + (-j - 1) = 0) by omega,
        show -(-(j : ℤ) - 1) - 1 = j by ring, show -((j : ℤ) + 1) = -j - 1 by ring, ↓reduceIte]
      match_scalars <;> field_simp
      all_goals ring
    · simp only [show ¬ (-((j : ℤ) + 1) + l = 0) by omega, show ¬ ((j : ℤ) + 1 + l = 0) by omega,
        show ¬ ((j : ℤ) = l - 1) by omega, show ¬ ((j : ℤ) = -l - 1) by omega, ↓reduceIte]
      simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, sum_range_ite_intCast_eq,
    sum_range_ite_intCast_eq]
  split_ifs <;> first | (exfalso; omega) | simp
  all_goals (obtain rfl : l = 0 := by omega); simp

/-- `[h, X] = X`. -/
theorem regNilH_commutator_regNil :
    regNilH Q w ν k * regNil Q w ν k - regNil Q w ν k * regNilH Q w ν k = regNil Q w ν k := by
  set h := regNilH Q w ν k
  rw [regNil, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have ha := regNilH_commutator_w hw hν (l := (i : ℤ) + 1) (by rw [abs_le]; constructor <;> omega)
  have hb := regNilH_commutator_w hw hν (l := -(i : ℤ)) (by rw [abs_neg]; simp; omega)
  have e : h * (ι Q (w (i + 1)) * ι Q (w (-i))) - ι Q (w (i + 1)) * ι Q (w (-i)) * h =
      (h * ι Q (w (i + 1)) - ι Q (w (i + 1)) * h) * ι Q (w (-i)) +
        ι Q (w (i + 1)) * (h * ι Q (w (-i)) - ι Q (w (-i)) * h) := by noncomm_ring
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, e, ha, hb, smul_mul_assoc, mul_smul_comm,
    ← add_smul]
  push_cast
  rw [show ((i : K) + 1 + -(i : K)) = 1 by ring, one_smul]

/-- `X` is nilpotent in `C(V)` (`[h, X] = X`). -/
theorem isNilpotent_regNil [CharZero K] [Module.Finite K V] : IsNilpotent (regNil Q w ν k) :=
  isNilpotent_of_mul_sub_mul_eq_self K (regNilH_commutator_regNil hw hν)

/-- The vectors `w_{-k}, …, w_k` are linearly independent. -/
theorem linearIndependent_isSplitFamily :
    LinearIndependent K fun i : Fin (2 * k + 1) => w ((i : ℤ) - k) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h : bform Q (∑ j, g j • w ((j : ℤ) - k)) (w (k - i)) = 0 := by rw [hg]; simp
  rw [map_sum, LinearMap.sum_apply] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  have hi := i.2
  rw [Finset.sum_eq_single i] at h
  · rw [hw ((i : ℤ) - k) (k - i) (abs_le.2 ⟨by omega, by omega⟩) (abs_le.2 ⟨by omega, by omega⟩),
      ite_eq_left (by ring)] at h
    exact (mul_eq_zero.mp h).resolve_right hν
  · intro j _ hji
    have hj := j.2
    rw [hw ((j : ℤ) - k) (k - i) (abs_le.2 ⟨by omega, by omega⟩) (abs_le.2 ⟨by omega, by omega⟩),
      ite_eq_right (fun h' => hji (Fin.ext (by omega))), mul_zero]
  · simp

/-- The Jordan chain: `(adV X)^j w_{-k} = ε_j w_{j-k}` with `ε_j ≠ 0`, for `j ≤ 2k`. -/
theorem adV_regNil_pow_w {j : ℕ} (hj : j ≤ 2 * k) :
    ∃ ε : K, ε ≠ 0 ∧ (adV Q (regNil Q w ν k) ^ j) (w (-k)) = ε • w ((j : ℤ) - k) := by
  induction j with
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | succ j ih =>
    obtain ⟨ε, hε, he⟩ := ih (by omega)
    refine ⟨ε * (if (j : ℤ) - k < 0 then (-1 : K) else if (j : ℤ) - k < k then 1 else 0), ?_, ?_⟩
    · refine mul_ne_zero hε ?_
      split_ifs <;> first | (exfalso; omega) | simp
    · rw [pow_succ', Module.End.mul_apply, he, map_smul,
        adV_regNil_w hw hν (abs_le.2 ⟨by omega, by omega⟩), smul_smul]
      congr 2
      push_cast; ring

/-- `adV X` maps `⟨w⟩` into itself. -/
theorem adV_regNil_mem_span {u : V}
    (hu : u ∈ Submodule.span K (Set.range fun i : Fin (2 * k + 1) => w ((i : ℤ) - k))) :
    adV Q (regNil Q w ν k) u ∈
      Submodule.span K (Set.range fun i : Fin (2 * k + 1) => w ((i : ℤ) - k)) := by
  have hle : Submodule.span K (Set.range fun i : Fin (2 * k + 1) => w ((i : ℤ) - k)) ≤
      (Submodule.span K (Set.range fun i : Fin (2 * k + 1) => w ((i : ℤ) - k))).comap
        (adV Q (regNil Q w ν k)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    rw [adV_regNil_w hw hν (abs_le.2 ⟨by omega, by omega⟩)]
    by_cases hik : (i : ℕ) < 2 * k
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i + 1, by omega⟩, ?_⟩)
      simp only; congr 1; push_cast; ring
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), zero_smul]
      exact Submodule.zero_mem _
  exact hle hu

end Model

section Centralizer

variable {K : Type*} [NontriviallyNormedField K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {Q : QuadraticForm K V} {w : ℤ → V} {ν : K} {k : ℕ}

/-- **The centralizer of `X` in `gspin(V)` has dimension `≤ dim V − k`** when
`V = ⟨w⟩ ⊕ ⟨w⟩^⊥` with `dim ⟨w⟩^⊥ ≤ 1` (`finrank_lieCentralizer_gspin` and the Jordan chain
`w_{-k} ↦ … ↦ w_k` of length `2k + 1`, `finrank_soCent_le_of_chain`). -/
theorem finrank_lieCentralizer_regNil_le (hQ : IsNondeg Q) (hw : IsSplitFamily Q w ν k)
    (hν : ν ≠ 0)
    (hsup : Submodule.span K (Set.range fun i : Fin (2 * k + 1) => w ((i : ℤ) - k)) ⊔
      (bform Q).orthogonal (Submodule.span K (Set.range fun i : Fin (2 * k + 1) => w ((i : ℤ) - k)))
        = ⊤)
    (hperp : finrank K ((bform Q).orthogonal
      (Submodule.span K (Set.range fun i : Fin (2 * k + 1) => w ((i : ℤ) - k)))) ≤ 1) :
    finrank K (lieCentralizer (gspin Q) (regNil Q w ν k)) ≤ finrank K V - (k + 1) + 1 := by
  set N := adV Q (regNil Q w ν k)
  have hε : ∀ i : Fin (2 * k + 1), ∃ ε : K, ε ≠ 0 ∧ (N ^ (i : ℕ)) (w (-k)) = ε • w ((i : ℤ) - k) :=
    fun i => adV_regNil_pow_w hw hν (by omega)
  choose ε hε0 hεe using hε
  have hchain : (fun i : Fin (2 * k + 1) => (N ^ (i : ℕ)) (w (-k))) =
      fun i => (Units.mk0 (ε i) (hε0 i)) • w ((i : ℤ) - k) := by
    funext i; rw [hεe, Units.smul_mk0]
  have hspan : Submodule.span K (Set.range fun i : Fin (2 * k + 1) => (N ^ (i : ℕ)) (w (-k))) =
      Submodule.span K (Set.range fun i : Fin (2 * k + 1) => w ((i : ℤ) - k)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show (N ^ (i : ℕ)) (w (-k)) ∈ _
      rw [hεe]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have : w ((i : ℤ) - k) = (ε i)⁻¹ • (N ^ (i : ℕ)) (w (-k)) := by
        rw [hεe, smul_smul, inv_mul_cancel₀ (hε0 i), one_smul]
      show w ((i : ℤ) - k) ∈ _
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent K fun i : Fin (2 * k + 1) => (N ^ (i : ℕ)) (w (-k)) := by
    rw [hchain]
    exact (linearIndependent_isSplitFamily hw hν).units_smul fun i => Units.mk0 (ε i) (hε0 i)
  have h := finrank_soCent_le_of_chain hQ (bform_adV regNil_mem_gspin) (w (-k)) (2 * k + 1) hli
    (by rw [hspan]; exact hsup) (by rw [hspan]; exact hperp)
  rw [finrank_lieCentralizer_gspin hQ regNil_mem_gspin]
  have h2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  rw [h2] at h
  omega

end Centralizer

end GSpinGGP
