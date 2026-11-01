/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.Cocharacter

/-!
# Contraction of a flag stabilizer by a cocharacter

Let `F` be an isotropic flag of a nondegenerate quadratic space `V` over a nontrivially normed
field `K`, with parabolic subgroup `P_F` and unipotent radical `N_F` in `GSpin(V)`
(Thesis §5.1.2, §5.2).  Using a splitting `bᵢ`, `wtᵢ` of the weight filtration of the flag
(`exists_flagSplitting`), this file builds:

1. the cocharacter `λ(t) : bᵢ ↦ t^{wtᵢ} bᵢ` of `SO(V)`, and a lift `T ∈ GSpin(V)` of `λ(t)` for
   `0 < |t| < 1` (surjectivity of `GSpin → SO`);
2. conjugation by `T^k` multiplies a monomial `ι(b_{i₁})⋯ι(b_{iₘ})` by `t^{k(wt_{i₁}+⋯+wt_{iₘ})}`,
   so it contracts every element of positive weight to `0` (`tendsto_gConj_pow_of_mem_wtFil_one`);
3. a Levi decomposition: every `p ∈ P_F` is `m y` where `P(m)` is the graded part of `P(p)`
   (it commutes with `λ`, so `T m T⁻¹ = c m` for a scalar `c`) and `y = c₀ + (positive weight)`;
4. consequently (`exists_tendsto_conj_flagStab`): up to central scalars, `T^k p T^{-k}` converges
   in `GSpin(V)` for every `p ∈ P_F`, and `T^k u T^{-k} → 1` for every `u ∈ N_F`
   (Borel–Tits: `P = M N` and `A_M` contracts `N`).
-/

noncomputable section

open CliffordAlgebra Module Filter Topology

namespace GSpinGGP

/-! ## 1. Conjugation and monomials -/

section Conj

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- Conjugation `x ↦ g x g⁻¹` by `g ∈ GSpin(V)` on `C(V)`. -/
def gConj (g : GSpin Q) (x : CliffordAlgebra Q) : CliffordAlgebra Q :=
  ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * x *
    (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)

theorem gConj_mul (g : GSpin Q) (x y : CliffordAlgebra Q) :
    gConj g (x * y) = gConj g x * gConj g y := by
  simp only [gConj, mul_assoc, Units.inv_mul_cancel_left]

theorem gConj_one (g : GSpin Q) : gConj g 1 = 1 := by
  simp [gConj]

theorem gConj_add (g : GSpin Q) (x y : CliffordAlgebra Q) :
    gConj g (x + y) = gConj g x + gConj g y := by
  simp only [gConj, mul_add, add_mul]

theorem gConj_sub (g : GSpin Q) (x y : CliffordAlgebra Q) :
    gConj g (x - y) = gConj g x - gConj g y := by
  simp only [gConj, mul_sub, sub_mul]

theorem gConj_zero (g : GSpin Q) : gConj g 0 = 0 := by
  simp [gConj]

theorem gConj_smul (g : GSpin Q) (r : K) (x : CliffordAlgebra Q) :
    gConj g (r • x) = r • gConj g x := by
  simp only [gConj, mul_smul_comm, smul_mul_assoc]

theorem gConj_algebraMap (g : GSpin Q) (r : K) :
    gConj g (algebraMap K _ r) = algebraMap K _ r := by
  rw [Algebra.algebraMap_eq_smul_one, gConj_smul, gConj_one]

theorem gConj_gmul (g h : GSpin Q) (x : CliffordAlgebra Q) :
    gConj (g * h) x = gConj g (gConj h x) := by
  simp only [gConj, Subgroup.coe_mul, mul_inv_rev, Units.val_mul, mul_assoc]

theorem gConj_ι (g : GSpin Q) (v : V) : gConj g (ι Q v) = ι Q (specP Q g v) :=
  (ι_specP g v).symm

variable {n : Type*} (b : Basis n K V)

/-- The monomial `ι(b_{i₁}) ⋯ ι(b_{iₘ})`. -/
def bMon (l : List n) : CliffordAlgebra Q := (l.map fun i => ι Q (b i)).prod

theorem gConj_bMon {g : GSpin Q} {c : n → K} (hg : ∀ i, specP Q g (b i) = c i • b i)
    (l : List n) : gConj g (bMon (Q := Q) b l) = (l.map c).prod • bMon b l := by
  induction l with
  | nil => simp [bMon, gConj_one]
  | cons i l ih =>
    simp only [bMon, List.map_cons, List.prod_cons] at ih ⊢
    rw [gConj_mul, gConj_ι, hg, map_smul, ih, smul_mul_smul_comm]

theorem specP_pow_basis {g : GSpin Q} {c : n → K} (hg : ∀ i, specP Q g (b i) = c i • b i)
    (k : ℕ) (i : n) : specP Q (g ^ k) (b i) = c i ^ k • b i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, specP_mul_apply, hg, map_smul, ih, smul_smul, pow_succ, mul_comm (c i)]

theorem list_prod_map_pow {M : Type*} [CommMonoid M] (c : n → M) (k : ℕ) (l : List n) :
    (l.map fun i => c i ^ k).prod = (l.map c).prod ^ k := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons, List.prod_cons, ih, mul_pow]

theorem list_prod_zpow {τ : K} (hτ : τ ≠ 0) (wt : n → ℤ) (l : List n) :
    (l.map fun i => τ ^ wt i).prod = τ ^ (l.map wt).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons, List.prod_cons, List.sum_cons, ih, zpow_add₀ hτ]

/-- The span of the monomials `ι(b_{i₁}) ⋯ ι(b_{iₘ})` of total weight `≥ j`. -/
def bMonSpan (wt : n → ℤ) (j : ℤ) : Submodule K (CliffordAlgebra Q) :=
  Submodule.span K {y | ∃ l : List n, j ≤ (l.map wt).sum ∧ y = bMon (Q := Q) b l}

variable {b}

theorem bMonSpan_anti {wt : n → ℤ} {j j' : ℤ} (h : j ≤ j') :
    bMonSpan (Q := Q) b wt j' ≤ bMonSpan b wt j :=
  Submodule.span_mono fun _ ⟨l, hl, hy⟩ => ⟨l, h.trans hl, hy⟩

theorem ι_b_mul_mem_bMonSpan {wt : n → ℤ} (i : n) {j : ℤ} {y : CliffordAlgebra Q}
    (hy : y ∈ bMonSpan b wt j) : ι Q (b i) * y ∈ bMonSpan b wt (wt i + j) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    refine Submodule.subset_span ⟨i :: l, by simp; omega, ?_⟩
    simp [bMon]
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

theorem gConj_mem_bMonSpan {wt : n → ℤ} {g : GSpin Q} {c : n → K}
    (hg : ∀ i, specP Q g (b i) = c i • b i) {j : ℤ} {x : CliffordAlgebra Q}
    (hx : x ∈ bMonSpan b wt j) : gConj g x ∈ bMonSpan b wt j := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    rw [gConj_bMon b hg]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, hl, rfl⟩)
  | zero => rw [gConj_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [gConj_add]; exact add_mem hx hy
  | smul r x _ hx => rw [gConj_smul]; exact Submodule.smul_mem _ r hx

variable [Fintype n]

/-- The weight filtration of `C(V)` is spanned by the monomials in a splitting basis. -/
theorem wtFil_le_bMonSpan {F : IsotropicFlag Q} {wt : n → ℤ} (hs : IsFlagSplitting F b wt)
    (j : ℤ) : wtFil Q (flagWt F) j ≤ bMonSpan b wt j := by
  rw [wtFil, Submodule.span_le]
  rintro _ ⟨l, hl, hj, rfl⟩
  induction l generalizing j with
  | nil =>
    refine Submodule.subset_span ⟨[], by simpa using hj, by simp [bMon]⟩
  | cons p l ih =>
    obtain ⟨w, v⟩ := p
    have hv : v ∈ flagWt F w := hl _ List.mem_cons_self
    have hrest := ih (j - w) (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      (by simp only [List.map_cons, List.sum_cons] at hj; omega)
    simp only [List.map_cons, List.prod_cons]
    rw [← b.sum_repr v, map_sum, Finset.sum_mul]
    refine sum_mem fun i _ => ?_
    rw [map_smul, smul_mul_assoc]
    by_cases hi : wt i < w
    · rw [hs.repr_eq_zero w v hv i hi, zero_smul]; exact zero_mem _
    · refine Submodule.smul_mem _ _ (bMonSpan_anti ?_ (ι_b_mul_mem_bMonSpan i hrest))
      omega

end Conj

section Normed

variable {K : Type*} [NontriviallyNormedField K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
variable {n : Type*} {b : Basis n K V} {wt : n → ℤ}

/-- **Contraction of positive weights**: if `T` acts on `bᵢ` by `τ^{wtᵢ}` with `|τ| < 1`, then
`T^k x T^{-k} → 0` for every `x` in the span of the monomials of weight `≥ 1`. -/
theorem tendsto_gConj_pow_bMonSpan {τ : K} (hτ0 : τ ≠ 0) (hτ : ‖τ‖ < 1) {T : GSpin Q}
    (hT : ∀ i, specP Q T (b i) = τ ^ wt i • b i) {x : CliffordAlgebra Q}
    (hx : x ∈ bMonSpan b wt 1) : Tendsto (fun k : ℕ => gConj (T ^ k) x) atTop (𝓝 0) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have hk : ∀ k : ℕ, gConj (T ^ k) (bMon (Q := Q) b l) =
        (τ ^ (l.map wt).sum) ^ k • bMon b l := by
      intro k
      rw [gConj_bMon b (specP_pow_basis b hT k)]
      congr 1
      rw [← list_prod_zpow hτ0 wt l, list_prod_map_pow]
    simp only [hk]
    have hs : (l.map wt).sum = (((l.map wt).sum).toNat : ℤ) := by omega
    have hlt : ‖τ ^ (l.map wt).sum‖ < 1 := by
      rw [hs, zpow_natCast, norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hτ (by omega)
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt).smul_const (bMon (Q := Q) b l)
  | zero => simpa [gConj_zero] using tendsto_const_nhds
  | add x y _ _ hx hy =>
    haveI := IsModuleTopology.toContinuousAdd K (CliffordAlgebra Q)
    simpa [gConj_add] using hx.add hy
  | smul r x _ hx => simpa [gConj_smul] using hx.const_smul r

end Normed

end GSpinGGP
