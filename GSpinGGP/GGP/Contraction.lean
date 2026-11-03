/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.Cocharacter

/-!
# Contraction of a flag stabilizer by a cocharacter

Let `F` be an isotropic flag of a nondegenerate quadratic space `V` over a nontrivially normed
field `K`, with parabolic subgroup `P_F` and unipotent radical `N_F` in `GSpin(V)`
(Thesis §5.1.2, §5.2).  With a splitting `bᵢ`, `wtᵢ` of the weight filtration of the flag, the
lift `T` of the cocharacter `λ(τ) : bᵢ ↦ τ^{wtᵢ} bᵢ` (`0 < |τ| < 1`) and the Levi decomposition
`p = m y` of `GGP/Cocharacter.lean`:

1. conjugation by `T^k` multiplies a monomial `ι(b_{i₁})⋯ι(b_{iₘ})` by `τ^{k(wt_{i₁}+⋯+wt_{iₘ})}`,
   so it contracts every element of positive weight to `0` (`tendsto_gConj_pow_bMonSpan`);
2. an element `y ∈ K^× · N_F` is a scalar `c` plus positive weight
   (`exists_sub_algebraMap_mem_wtFil_of_raisesFil`), with `c = 1` on `N_F`
   (`sub_one_mem_wtFil_of_mem_flagUnip`: this uses that `u − 1` is nilpotent, a condition in
   the definition of `N_F` in `GSpin(V)`), so `T^k y T^{-k} → c`
   (`tendsto_gConj_pow_of_sub_mem_wtFil`);
3. consequently (`exists_tendsto_conj_flagStab`): up to central scalars, `T^k (p u) T^{-k}` converges
   in `GSpin(V)` for every `p ∈ P_F`, to a limit independent of `u ∈ N_F`
   (Borel–Tits: `P = M N`, and the split centre of `M` contracts `N`).
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

section ScalarPart

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V] {Q : QuadraticForm K V}

omit [Invertible (2 : K)] [Module.Finite K V] in
theorem mem_evenOdd_zero_of_mem_GSpin (g : GSpin Q) :
    ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
  have := g.2.1
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at this
  exact this

omit [Module.Finite K V] in
theorem mul_ι_eq_ι_specP_mul (g : GSpin Q) (v : V) :
    ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q v =
      ι Q ((specP Q g : V →ₗ[K] V) v) * ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  rw [LinearEquiv.coe_coe, ι_specP, mul_assoc, Units.inv_mul, mul_one]

/-- An element of `K^× · N_F` (`P(g)` trivial on the graded pieces) is a scalar plus positive
weight. -/
theorem exists_sub_algebraMap_mem_wtFil_of_raisesFil (hQ : IsNondeg Q) {F : IsotropicFlag Q}
    {g : GSpin Q} (hg : RaisesFil (flagWt F) ((specP Q g : V →ₗ[K] V) - LinearMap.id)) :
    ∃ c : K, ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - algebraMap K _ c ∈
      wtFil Q (flagWt F) 1 :=
  exists_sub_algebraMap_mem_wtFil_one hQ F.isWtFil (F.orthogonal_flagWt_le hQ)
    (mem_evenOdd_zero_of_mem_GSpin g) (P := (specP Q g : V →ₗ[K] V)) (mul_ι_eq_ι_specP_mul g)
    (fun w v hv => by simpa using hg w v hv)

/-- An element of `N_F` is `1` plus positive weight. -/
theorem sub_one_mem_wtFil_of_mem_flagUnip (hQ : IsNondeg Q) {F : IsotropicFlag Q}
    {u : GSpin Q} (hu : u ∈ flagUnip F) :
    ((u : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1 ∈ wtFil Q (flagWt F) 1 :=
  sub_one_mem_wtFil_one hQ F.isWtFil (F.orthogonal_flagWt_le hQ) (mem_evenOdd_zero_of_mem_GSpin u)
    (P := (specP Q u : V →ₗ[K] V)) (mul_ι_eq_ι_specP_mul u)
    (F.specP_sub_mem_flagWt ⟨hu.1, hu.2.1, hu.2.2.1⟩) hu.2.2.2

end ScalarPart

/-- A sequence of units whose values and inverses converge converges in `Mˣ`. -/
theorem _root_.Units.exists_tendsto_of_tendsto_val {M : Type*} [Monoid M] [TopologicalSpace M]
    [ContinuousMul M] [T2Space M] {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → Mˣ} {a b : M}
    (ha : Tendsto (fun k => (f k : M)) l (𝓝 a))
    (hb : Tendsto (fun k => (((f k)⁻¹ : Mˣ) : M)) l (𝓝 b)) :
    ∃ L : Mˣ, (L : M) = a ∧ Tendsto f l (𝓝 L) := by
  have h1 : a * b = 1 := tendsto_nhds_unique (ha.mul hb) (by simp)
  have h2 : b * a = 1 := tendsto_nhds_unique (hb.mul ha) (by simp)
  refine ⟨⟨a, b, h1, h2⟩, rfl, ?_⟩
  rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
  exact ha.prodMk_nhds (MulOpposite.continuous_op.continuousAt.tendsto.comp hb)

section Limit

variable {K : Type*} [NontriviallyNormedField K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
theorem tendsto_gConj_pow_of_sub_mem_wtFil {F : IsotropicFlag Q} {n : Type*} [Fintype n]
    {b : Basis n K V} {wt : n → ℤ} (hs : IsFlagSplitting F b wt) {τ : K} (hτ0 : τ ≠ 0)
    (hτ : ‖τ‖ < 1) {T : GSpin Q} (hT : ∀ i, specP Q T (b i) = τ ^ wt i • b i)
    {x : CliffordAlgebra Q} {c : K} (hx : x - algebraMap K _ c ∈ wtFil Q (flagWt F) 1) :
    Tendsto (fun k : ℕ => gConj (T ^ k) x) atTop (𝓝 (algebraMap K _ c)) := by
  have := IsModuleTopology.toContinuousAdd K (CliffordAlgebra Q)
  have h := (tendsto_gConj_pow_bMonSpan hτ0 hτ hT (wtFil_le_bMonSpan hs 1 hx)).add_const
    (algebraMap K (CliffordAlgebra Q) c)
  simpa [gConj_sub, gConj_algebraMap] using h


/-- **Contraction of `P_F` by a cocharacter** (Thesis §5.1.2: `P = M N`, and the split centre of `M`
contracts `N`).  There is `T ∈ GSpin(V)` such that for every `p ∈ P_F`, after correction by central
scalars, `T^k (p u) T^{-k}` converges in `GSpin(V)` to a limit independent of `u ∈ N_F`. -/
theorem exists_tendsto_conj_flagStab (hQ : IsNondeg Q) (F : IsotropicFlag Q) :
    ∃ T : GSpin Q, ∀ p ∈ flagStab F, ∃ (s : Kˣ) (L : GSpin Q), ∀ u ∈ flagUnip F,
      Tendsto (fun k : ℕ => scalarGSpin Q (s ^ k)⁻¹ * (T ^ k * (p * u) * (T ^ k)⁻¹)) atTop
        (𝓝 L) := by
  classical
  obtain ⟨n, _, _, b, wt, hs⟩ := exists_flagSplitting hQ F
  obtain ⟨τ, hτ0, hτ1⟩ := NormedField.exists_norm_lt_one K
  have hτ : τ ≠ 0 := norm_pos_iff.1 hτ0
  obtain ⟨T, hT⟩ := hs.exists_cochar_lift hQ hτ
  refine ⟨T, fun p hp => ?_⟩
  obtain ⟨m, y, rfl, hm, hy, hy'⟩ := hs.exists_levi_decomp hQ hp
  obtain ⟨s, hsm⟩ := exists_mul_eq_scalarGSpin_mul_of_isHomog hQ hT hm
  have hcen : ∀ (c : Kˣ) (g : GSpin Q), scalarGSpin Q c * g = g * scalarGSpin Q c :=
    fun c g => (Subgroup.mem_center_iff.1 (scalarGSpin_mem_center Q c) g).symm
  have hTk : ∀ k : ℕ, T ^ k * m = scalarGSpin Q (s ^ k) * (m * T ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc T ^ (k + 1) * m = T * (T ^ k * m) := by rw [pow_succ', mul_assoc]
        _ = scalarGSpin Q (s ^ k) * ((T * m) * T ^ k) := by
          rw [ih, ← mul_assoc, ← hcen, mul_assoc, mul_assoc]
        _ = scalarGSpin Q (s ^ (k + 1)) * (m * T ^ (k + 1)) := by
          rw [hsm, pow_succ s k, map_mul, pow_succ' T k]
          simp only [mul_assoc]
  -- the conjugates, rewritten through the Levi decomposition
  have hq : ∀ (u : GSpin Q) (k : ℕ),
      scalarGSpin Q (s ^ k)⁻¹ * (T ^ k * (m * y * u) * (T ^ k)⁻¹) =
        m * (T ^ k * (y * u) * (T ^ k)⁻¹) := by
    intro u k
    rw [show T ^ k * (m * y * u) = T ^ k * m * (y * u) by group, hTk, map_inv]
    group
  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_wtFil_of_raisesFil hQ hy
  obtain ⟨c', hc'⟩ := exists_sub_algebraMap_mem_wtFil_of_raisesFil hQ hy'
  set C := CliffordAlgebra Q
  have : T2Space C := T2Space.of_injective_continuous (Module.finBasis K C).equivFun.injective
    (IsModuleTopology.continuous_of_linearMap (R := K) (Module.finBasis K C).equivFun.toLinearMap)
  -- weight `≥ 0` membership of the factors
  have h0 : ∀ {x : C} {a : K}, x - algebraMap K C a ∈ wtFil Q (flagWt F) 1 →
      x ∈ wtFil Q (flagWt F) 0 := fun {x a} h => by
    rw [← sub_add_cancel x (algebraMap K C a)]
    exact add_mem (wtFil_anti (by norm_num) h) (algebraMap_mem_wtFil a le_rfl)
  have hlim : ∀ u ∈ flagUnip F, ∃ L : Cˣ, (L : C) = (m : Cˣ) * algebraMap K C c ∧
      Tendsto (fun k : ℕ => ((scalarGSpin Q (s ^ k)⁻¹ * (T ^ k * (m * y * u) * (T ^ k)⁻¹) :
        GSpin Q) : Cˣ)) atTop (𝓝 L) := by
    intro u hu
    have hu1 := sub_one_mem_wtFil_of_mem_flagUnip hQ hu
    have hu1' := sub_one_mem_wtFil_of_mem_flagUnip hQ ((flagUnip F).inv_mem hu)
    -- `y u = c + (positive weight)`, `u⁻¹ y⁻¹ = c' + (positive weight)`
    have hyu : ((y : Cˣ) : C) * ((u : Cˣ) : C) - algebraMap K C c ∈ wtFil Q (flagWt F) 1 := by
      have : ((y : Cˣ) : C) * ((u : Cˣ) : C) - algebraMap K C c =
          (((y : Cˣ) : C) - algebraMap K C c) * ((u : Cˣ) : C) +
            algebraMap K C c * (((u : Cˣ) : C) - 1) := by noncomm_ring
      rw [this]
      exact add_mem (wtFil_anti (by norm_num) (mul_mem_wtFil hc (h0 (a := 1) (by simpa using hu1))))
        (wtFil_anti (by norm_num) (mul_mem_wtFil (algebraMap_mem_wtFil c le_rfl) hu1))
    have huy : (((u⁻¹ : GSpin Q) : Cˣ) : C) * (((y⁻¹ : GSpin Q) : Cˣ) : C) - algebraMap K C c' ∈
        wtFil Q (flagWt F) 1 := by
      have : (((u⁻¹ : GSpin Q) : Cˣ) : C) * (((y⁻¹ : GSpin Q) : Cˣ) : C) - algebraMap K C c' =
          ((((u⁻¹ : GSpin Q) : Cˣ) : C) - 1) * (((y⁻¹ : GSpin Q) : Cˣ) : C) +
            ((((y⁻¹ : GSpin Q) : Cˣ) : C) - algebraMap K C c') := by noncomm_ring
      rw [this]
      exact add_mem (wtFil_anti (by norm_num) (mul_mem_wtFil hu1' (h0 hc'))) hc'
    have hA := tendsto_gConj_pow_of_sub_mem_wtFil hs hτ hτ1 hT hyu
    have hB := tendsto_gConj_pow_of_sub_mem_wtFil hs hτ hτ1 hT huy
    refine Units.exists_tendsto_of_tendsto_val
      (b := algebraMap K C c' * (((m⁻¹ : GSpin Q) : Cˣ) : C)) ?_ ?_
    · simp_rw [hq]
      exact (hA.const_mul _).congr fun k => by
        simp [gConj, mul_assoc]
    · simp_rw [hq]
      exact (hB.mul_const _).congr fun k => by
        simp [gConj, mul_assoc]
  obtain ⟨L₁, hL₁, hT₁⟩ := hlim 1 (flagUnip F).one_mem
  have hL₁mem : L₁ ∈ GSpin Q :=
    (isClosed_GSpin Q).mem_of_tendsto hT₁ (Eventually.of_forall fun k => SetLike.coe_mem _)
  refine ⟨s, ⟨L₁, hL₁mem⟩, fun u hu => ?_⟩
  obtain ⟨L, hL, hTL⟩ := hlim u hu
  have : L = L₁ := Units.ext (hL.trans hL₁.symm)
  subst this
  exact tendsto_subtype_rng.2 hTL

end Limit

end GSpinGGP
