/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.GSpin
import GSpinGGP.Literature.GSpin

/-!
# Contracting cocharacters of flag stabilizers

For an isotropic flag `Z₁ ⊂ ⋯ ⊂ Z_k` of a nondegenerate quadratic space `V`, with weight filtration
`V_{≥w}` (`flagWt`, Thesis §5.2), this file constructs:

1. **A splitting** of the filtration (`exists_flagSplitting`): a basis `bᵢ` of `V` with weights
   `wtᵢ` such that `V_{≥w}` is spanned by the `bᵢ` with `wtᵢ ≥ w`, and `b(bᵢ, bⱼ) = 0` unless
   `wtᵢ + wtⱼ = 0` (a hyperbolic basis `e, f` dual on `Z_k`, plus a basis of `(Z_k ⊕ Z_k')ᗮ`).
2. **The cocharacter** `λ(t) : bᵢ ↦ t^{wtᵢ} bᵢ` of `SO(V)` and a lift `T ∈ GSpin(V)` of `λ(t)`
   (surjectivity of `GSpin → SO`), whose conjugation action on `C(V)` has the weight
   filtration `wtFil` in its non-negative weights.
3. **A Levi decomposition** (`exists_levi_decomp`): every `p ∈ P_F` is `m̃ y` with `P(m̃)` commuting
   with `λ` and `y` acting trivially on the graded pieces; `y ∈ c + (positive weight)`.
   Here `P(m̃)` is the limit of `λ(t)^k P(p) λ(t)^{-k}`, so is again an isometry of determinant `1`.
4. **Contraction** (`exists_contracting_seq`): over a nontrivially normed field, there is
   `T ∈ GSpin(V)` such that for every `p ∈ P_F` the sequence `T^k (p u) T^{-k}` converges, to a
   limit independent of `u ∈ N_F` (Borel–Tits; Thesis §5.1.2: `P = M ⋉ N`, and `A_M` contracts `N`).
-/

noncomputable section

open CliffordAlgebra Module Filter Topology

namespace GSpinGGP

/-! ## 1. A splitting of the weight filtration of a flag -/

section Splitting

universe u

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type u} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V}

/-- A basis `b` of `V` with weights `wt` splitting the weight filtration of the flag `F`, with
`b(bᵢ, bⱼ) = 0` unless `wtᵢ + wtⱼ = 0`, and total weight `0`. -/
structure IsFlagSplitting (F : IsotropicFlag Q) {ι : Type*} [Fintype ι] (b : Basis ι K V)
    (wt : ι → ℤ) : Prop where
  mem : ∀ i, b i ∈ flagWt F (wt i)
  repr_eq_zero : ∀ w, ∀ v ∈ flagWt F w, ∀ i, wt i < w → b.repr v i = 0
  orth : ∀ i j, wt i + wt j ≠ 0 → bform Q (b i) (b j) = 0
  sum_wt : ∑ i, wt i = 0

theorem IsotropicFlag.flagWt_one (F : IsotropicFlag Q) : flagWt F 1 = F.top := by
  rw [F.flagWt_of_pos le_rfl, IsotropicFlag.top]
  congr 1
  ext
  simp [IsotropicFlag.idx]

theorem IsotropicFlag.flagWt_zero (F : IsotropicFlag Q) :
    flagWt F 0 = (bform Q).orthogonal F.top := by
  rw [F.flagWt_of_nonpos le_rfl, IsotropicFlag.top]
  congr 2
  ext
  simp [IsotropicFlag.idx]

/-- Elements of `P_F` preserve every step `V_{≥w}` of the weight filtration. -/
theorem flagStab_mapsTo_flagWt {F : IsotropicFlag Q} {g : GSpin Q} (hg : g ∈ flagStab F) (w : ℤ)
    {v : V} (hv : v ∈ flagWt F w) : specP Q g v ∈ flagWt F w := by
  by_cases hw : 1 ≤ w
  · rw [F.flagWt_of_pos hw] at hv ⊢
    exact flagStab_mapsTo hg _ hv
  · rw [F.flagWt_of_nonpos (by omega)] at hv ⊢
    intro t ht
    have ht' : specP Q g⁻¹ t ∈ F.sub (F.idx (F.len + w)) :=
      flagStab_mapsTo ((flagStab F).inv_mem hg) _ ht
    rw [← specP_inv_apply_apply g t, bform_specP]
    exact hv _ ht'

variable [FiniteDimensional K V]

theorem exists_flagSplitting (hQ : IsNondeg Q) (F : IsotropicFlag Q) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (b : Basis ι K V) (wt : ι → ℤ),
      IsFlagSplitting F b wt := by
  classical
  set Z := F.top with hZdef
  have hZiso : IsTotallyIsotropic Q Z := F.isotropic _
  have hBZ : ∀ {x y : V}, x ∈ Z → y ∈ Z → bform Q x y = 0 := fun hx hy =>
    bform_eq_zero_of_isTotallyIsotropic hZiso hx hy
  have hsymm : ∀ x y : V, bform Q x y = bform Q y x := bform_comm Q
  -- an adapted basis of `Z`
  let Vf : ℤ → Submodule K Z := fun w => (flagWt F w).comap Z.subtype
  obtain ⟨s, e, wtE, he, hcoordE⟩ := exists_adapted_basis (Vf := Vf)
    (fun a b' h => Submodule.comap_mono (F.flagWt_anti h)) (F.len + 1)
    (by
      simp only [Vf]
      rw [F.flagWt_eq_top (by push_cast; omega), Submodule.comap_top])
    (by
      simp only [Vf]
      rw [F.flagWt_eq_bot (by push_cast; omega), Submodule.comap_bot, Submodule.ker_subtype])
  have : Fintype s := FiniteDimensional.fintypeBasisIndex e
  have he' : ∀ i, ((e i : Z) : V) ∈ flagWt F (wtE i) := he
  have hcoordV : ∀ i a, wtE i < a → ∀ z : Z, (z : V) ∈ flagWt F a → e.coord i z = 0 :=
    fun i a ha z hz => hcoordE i a ha z hz
  have hwt1 : ∀ i, 1 ≤ wtE i := by
    intro i
    by_contra h
    have h0 := hcoordV i 1 (by omega) (e i) (by rw [F.flagWt_one]; exact (e i).2)
    rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same] at h0
    exact one_ne_zero h0
  -- `z = ∑ coord_l(z) e_l` in `V`
  have hZsum : ∀ z : Z, (z : V) = ∑ l, e.coord l z • ((e l : Z) : V) := by
    intro z
    have h := congrArg Subtype.val (e.sum_repr z)
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul] at h
    simp only [Basis.coord_apply]
    exact h.symm
  -- dual vectors
  have hext : ∀ i, ∃ φ : V →ₗ[K] K, φ ∘ₗ Z.subtype = e.coord i := fun i =>
    LinearMap.exists_extend (e.coord i)
  choose φ hφ using hext
  let f' : s → V := fun i => ((bform Q).toDual hQ).symm (φ i)
  have hf'z : ∀ i (z : Z), bform Q (f' i) z = e.coord i z := by
    intro i z
    exact (LinearMap.BilinForm.apply_toDual_symm_apply (hB := hQ) _ _).trans congr($(hφ i) z)
  let f : s → V := fun i => f' i - (⅟2 : K) • ∑ l, bform Q (f' l) (f' i) • ((e l : Z) : V)
  have hfz : ∀ i (z : Z), bform Q (f i) z = e.coord i z := by
    intro i z
    simp only [f, map_sub, map_smul, map_sum, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, hBZ (e _).2 z.2, smul_zero, Finset.sum_const_zero,
      sub_zero, hf'z]
  have hcoord_e : ∀ i l, e.coord i (e l) = if l = i then 1 else 0 := by
    intro i l
    rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  have hfe : ∀ i l, bform Q (f i) (e l) = if l = i then 1 else 0 := fun i l => by
    rw [hfz, hcoord_e]
  have hff : ∀ i j, bform Q (f i) (f j) = 0 := by
    intro i j
    have h1 : ∀ x : V, bform Q (f i) x = bform Q (f' i) x -
        (⅟2 : K) * ∑ l, bform Q (f' l) (f' i) * bform Q (e l) x := by
      intro x
      simp only [f, map_sub, map_smul, map_sum, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.sum_apply, smul_eq_mul]
    have h2 : ∀ l, bform Q (e l) (f j) = if l = j then 1 else 0 := fun l => by
      rw [hsymm, hfe]
    have h3 : bform Q (f' i) (f j) = bform Q (f' i) (f' j) -
        (⅟2 : K) * bform Q (f' j) (f' i) := by
      have : bform Q (f' i) (f j) = bform Q (f' i) (f' j) -
          (⅟2 : K) * ∑ l, bform Q (f' l) (f' j) * bform Q (f' i) (e l) := by
        simp only [f, map_sub, map_smul, map_sum, smul_eq_mul]
      rw [this]
      simp only [hf'z, hcoord_e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
      rw [hsymm (f' i) (f' j)]
    rw [h1, h3]
    simp only [h2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hsymm (f' j) (f' i)]
    have : (⅟2 : K) + ⅟2 = 1 := by rw [← two_mul, mul_invOf_self]
    linear_combination (-(bform Q (f' i) (f' j))) * this
  -- the complement `X`
  let πX : V →ₗ[K] (s → K) × (s → K) :=
    LinearMap.prod (LinearMap.pi fun i => bform Q (e i)) (LinearMap.pi fun i => bform Q (f i))
  let X := LinearMap.ker πX
  have hX : ∀ {x : V}, x ∈ X ↔ (∀ i, bform Q (e i) x = 0) ∧ ∀ i, bform Q (f i) x = 0 := by
    intro x
    simp [X, πX, Prod.ext_iff, funext_iff]
  have hXZ : ∀ {x : V}, x ∈ X → ∀ z : Z, bform Q z x = 0 := by
    intro x hx z
    rw [hZsum z]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      (hX.1 hx).1, smul_zero, Finset.sum_const_zero]
  let bX := Module.finBasis K X
  -- the family
  let c : s ⊕ s ⊕ Fin (finrank K X) → V := fun x => match x with
    | Sum.inl i => e i
    | Sum.inr (Sum.inl i) => f i
    | Sum.inr (Sum.inr k) => bX k
  have hef : ∀ i j, bform Q (e i) (f j) = if i = j then 1 else 0 := fun i j => by
    rw [hsymm, hfe]
  have hli : LinearIndependent K c := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hpair : ∀ y : V, ∑ x, g x * bform Q y (c x) = 0 := by
      intro y
      have := congrArg (bform Q y) hg
      simpa [map_sum, map_smul] using this
    have hA : ∀ j, g (Sum.inr (Sum.inl j)) = 0 := by
      intro j
      have h := hpair (e j)
      simp only [Fintype.sum_sum_type, c, hBZ (e j).2 (e _).2, hef, (hX.1 (bX _).2).1, mul_zero,
        Finset.sum_const_zero, zero_add, add_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at h
      exact h
    have hB : ∀ j, g (Sum.inl j) = 0 := by
      intro j
      have h := hpair (f j)
      simp only [Fintype.sum_sum_type, c, hfe, hff, (hX.1 (bX _).2).2, mul_zero,
        Finset.sum_const_zero, zero_add, add_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at h
      exact h
    have hC : ∀ k, g (Sum.inr (Sum.inr k)) = 0 := by
      have h0 : ∑ k, g (Sum.inr (Sum.inr k)) • ((bX k : X) : V) = 0 := by
        simpa [Fintype.sum_sum_type, c, hA, hB] using hg
      have h1 : ∑ k, g (Sum.inr (Sum.inr k)) • bX k = 0 := by
        apply Subtype.ext
        simpa [Submodule.coe_sum] using h0
      exact (Fintype.linearIndependent_iff.1 bX.linearIndependent) _ h1
    rintro (j | j | k)
    exacts [hB j, hA j, hC k]
  -- decomposition
  have hproj : ∀ v : V, v - ∑ i, bform Q (f i) v • ((e i : Z) : V) -
      ∑ i, bform Q (e i) v • f i ∈ X := by
    intro v
    rw [hX]
    constructor
    · intro j
      simp only [map_sub, map_sum, map_smul, smul_eq_mul, hBZ (e j).2 (e _).2, mul_zero,
        Finset.sum_const_zero, sub_zero, hef, mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, sub_self]
    · intro j
      simp only [map_sub, map_sum, map_smul, smul_eq_mul, hfe, hff, mul_zero,
        Finset.sum_const_zero, sub_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, sub_self]
  have hsp : ⊤ ≤ Submodule.span K (Set.range c) := by
    intro v _
    have hx := hproj v
    have hv : v = ∑ i, bform Q (f i) v • c (Sum.inl i) + ∑ i, bform Q (e i) v • c (Sum.inr
        (Sum.inl i)) + ((⟨_, hx⟩ : X) : V) := by
      simp only [c]; abel
    rw [hv]
    refine add_mem (add_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨Sum.inl i, rfl⟩)) (sum_mem fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨Sum.inr (Sum.inl i), rfl⟩))) ?_
    have : ((⟨_, hx⟩ : X) : V) = ∑ k, bX.repr ⟨_, hx⟩ k • c (Sum.inr (Sum.inr k)) := by
      have h := congrArg Subtype.val (bX.sum_repr ⟨_, hx⟩)
      rw [Submodule.coe_sum] at h
      simp only [Submodule.coe_smul] at h
      exact h.symm
    rw [this]
    exact sum_mem fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr (Sum.inr k), rfl⟩)
  let b := Basis.mk hli hsp
  have hb : ∀ x, b x = c x := fun x => Basis.mk_apply hli hsp x
  let wt : s ⊕ s ⊕ Fin (finrank K X) → ℤ := fun x => match x with
    | Sum.inl i => wtE i
    | Sum.inr (Sum.inl i) => -wtE i
    | Sum.inr (Sum.inr _) => 0
  -- coefficients
  have hpairb : ∀ (y v : V), bform Q y v = ∑ x, b.repr v x * bform Q y (c x) := by
    intro y v
    conv_lhs => rw [← b.sum_repr v]
    simp [map_sum, map_smul, hb]
  have hrepr_f : ∀ v i, b.repr v (Sum.inr (Sum.inl i)) = bform Q (e i) v := by
    intro v i
    rw [hpairb]
    simp only [Fintype.sum_sum_type, c, hBZ (e i).2 (e _).2, hef, (hX.1 (bX _).2).1, mul_zero,
      Finset.sum_const_zero, zero_add, add_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hrepr_e : ∀ v i, b.repr v (Sum.inl i) = bform Q (f i) v := by
    intro v i
    rw [hpairb]
    simp only [Fintype.sum_sum_type, c, hfe, hff, (hX.1 (bX _).2).2, mul_zero,
      Finset.sum_const_zero, zero_add, add_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hrepr_Z : ∀ (z : Z) k, b.repr z (Sum.inr (Sum.inr k)) = 0 := by
    intro z k
    rw [hZsum z]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : ((e l : Z) : V) = b (Sum.inl l) := (hb (Sum.inl l)).symm
    rw [this, b.repr_self, Finsupp.single_apply, if_neg (by simp), smul_zero]
  have hle_Z : ∀ {w : ℤ}, 1 ≤ w → ∀ {v : V}, v ∈ flagWt F w → v ∈ Z := by
    intro w hw v hv
    show v ∈ F.top
    rw [← F.flagWt_one]; exact F.flagWt_anti hw hv
  refine ⟨_, inferInstance, inferInstance, b, wt, ⟨?_, ?_, ?_, ?_⟩⟩
  · rintro (i | i | k) <;> rw [hb]
    · exact he' i
    · show f i ∈ flagWt F (-wtE i)
      rw [F.flagWt_neg_eq_orthogonal (by have := hwt1 i; omega)]
      intro y hy
      rw [hsymm, hfz i ⟨y, hle_Z (by have := hwt1 i; omega) hy⟩]
      exact hcoordV i _ (by omega) _ hy
    · show (bX k : V) ∈ flagWt F 0
      rw [F.flagWt_zero]
      intro y hy
      exact hXZ (bX k).2 ⟨y, hy⟩
  · intro w v hv
    rintro (i | i | k) hi
    · have hi : wtE i < w := hi
      rw [hrepr_e, hfz i ⟨v, hle_Z (by have := hwt1 i; omega) hv⟩]
      exact hcoordV i w hi _ hv
    · have hi : -wtE i < w := hi
      rw [hrepr_f]
      exact F.bform_flagWt (by omega) (he' i) hv
    · have hi : (0 : ℤ) < w := hi
      exact hrepr_Z ⟨v, hle_Z (by omega) hv⟩ k
  · rintro (i | i | k) (j | j | l) hij <;> rw [hb, hb]
    · exact hBZ (e i).2 (e j).2
    · show bform Q (e i) (f j) = 0
      rw [hef, if_neg]
      rintro rfl; exact hij (by simp [wt])
    · exact (hX.1 (bX l).2).1 i
    · show bform Q (f i) (e j) = 0
      rw [hfe, if_neg]
      rintro rfl; exact hij (by simp [wt])
    · exact hff i j
    · exact (hX.1 (bX l).2).2 i
    · show bform Q (bX k) (e j) = 0
      rw [hsymm]; exact (hX.1 (bX k).2).1 j
    · show bform Q (bX k) (f j) = 0
      rw [hsymm]; exact (hX.1 (bX k).2).2 j
    · exact absurd (by simp [wt]) hij
  · simp [wt, Fintype.sum_sum_type]

end Splitting

end GSpinGGP
