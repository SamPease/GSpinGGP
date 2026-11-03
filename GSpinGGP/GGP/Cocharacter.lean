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
2. **The cocharacter** `λ(τ) : bᵢ ↦ τ^{wtᵢ} bᵢ` of `SO(V)` (`cochar`) and a lift `T ∈ GSpin(V)`
   (`exists_cochar_lift`, from the surjectivity of `GSpin → SO`).
3. **A Levi decomposition** (`exists_levi_decomp`; Thesis §5.1.2: `P = M ⋉ N`): every `p ∈ P_F` is
   `m y`, where `P(m)` is the graded part `gr P(p)` of `P(p)` (`grEnd`: the block-diagonal part in
   the basis `bᵢ`; an isometry of determinant `1`, as `gr P(p)⁻¹ P(p)` is unipotent) and `P(y)` is
   trivial on the graded pieces.  Then `m` commutes with `T` up to a central scalar
   (`exists_mul_eq_scalar_mul`).

The contraction of `P_F` by `T` is in `GGP/Contraction.lean`.
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

/-! ## 2. The cocharacter and the Levi decomposition -/

section Levi

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} {F : IsotropicFlag Q}
variable {ι : Type*} [Fintype ι] {b : Basis ι K V} {wt : ι → ℤ}

/-- In a splitting basis, `V_{≥w}` consists of the vectors with no coordinates of weight `< w`. -/
theorem IsFlagSplitting.mem_flagWt_iff (hs : IsFlagSplitting F b wt) {w : ℤ} {v : V} :
    v ∈ flagWt F w ↔ ∀ i, wt i < w → b.repr v i = 0 := by
  refine ⟨fun hv i hi => hs.repr_eq_zero w v hv i hi, fun h => ?_⟩
  rw [← b.sum_repr v]
  refine sum_mem fun i _ => ?_
  by_cases hi : wt i < w
  · rw [h i hi, zero_smul]; exact zero_mem _
  · exact Submodule.smul_mem _ _ (F.flagWt_anti (by omega) (hs.mem i))

variable (b wt) in
/-- `x` is homogeneous of weight `w`: its coordinates of weight `≠ w` vanish. -/
def IsHomog (x : V) (w : ℤ) : Prop := ∀ i, wt i ≠ w → b.repr x i = 0

theorem IsFlagSplitting.mem_flagWt_of_isHomog (hs : IsFlagSplitting F b wt) {x : V} {w : ℤ}
    (hx : IsHomog b wt x w) : x ∈ flagWt F w :=
  hs.mem_flagWt_iff.2 fun i hi => hx i (by omega)

theorem IsFlagSplitting.bform_eq_zero_of_isHomog (hs : IsFlagSplitting F b wt) {x y : V}
    {a c : ℤ} (hx : IsHomog b wt x a) (hy : IsHomog b wt y c) (hac : a + c ≠ 0) :
    bform Q x y = 0 := by
  rw [← b.sum_repr x, ← b.sum_repr y, LinearMap.BilinForm.sum_left]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.BilinForm.sum_right]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  by_cases hi : wt i = a
  · by_cases hj : wt j = c
    · rw [hs.orth i j (by omega), mul_zero, mul_zero]
    · rw [hy j hj, zero_mul, mul_zero]
  · rw [hx i hi, zero_mul]

variable (b wt) in
/-- The graded part of an endomorphism: `bⱼ ↦` the weight-`wtⱼ` part of `A bⱼ`. -/
def grEnd (A : V →ₗ[K] V) : V →ₗ[K] V :=
  b.constr K fun j => ∑ i with wt i = wt j, b.repr (A (b j)) i • b i

omit [Invertible (2 : K)] in
theorem repr_grEnd (A : V →ₗ[K] V) (j i : ι) :
    b.repr (grEnd b wt A (b j)) i = if wt i = wt j then b.repr (A (b j)) i else 0 := by
  classical
  rw [grEnd, Basis.constr_basis, map_sum, Finsupp.finsetSum_apply]
  simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_filter]

omit [Invertible (2 : K)] in
theorem isHomog_grEnd (A : V →ₗ[K] V) (j : ι) : IsHomog b wt (grEnd b wt A (b j)) (wt j) :=
  fun i hi => by simp [repr_grEnd, hi]

/-- `A` maps every `V_{≥w}` into itself. -/
def PresFil (F : IsotropicFlag Q) (A : V →ₗ[K] V) : Prop := ∀ w, ∀ v ∈ flagWt F w, A v ∈ flagWt F w

/-- `A` raises weights: `A V_{≥w} ⊆ V_{≥w+1}`. -/
def RaisesFil (F : IsotropicFlag Q) (A : V →ₗ[K] V) : Prop :=
  ∀ w, ∀ v ∈ flagWt F w, A v ∈ flagWt F (w + 1)

theorem IsFlagSplitting.raisesFil_of_basis (hs : IsFlagSplitting F b wt) {A : V →ₗ[K] V}
    (hA : ∀ j, A (b j) ∈ flagWt F (wt j + 1)) : RaisesFil F A := by
  intro w v hv
  rw [← b.sum_repr v, map_sum]
  refine sum_mem fun j _ => ?_
  by_cases hj : wt j < w
  · rw [hs.repr_eq_zero w v hv j hj, zero_smul, map_zero]; exact zero_mem _
  · rw [map_smul]; exact Submodule.smul_mem _ _ (F.flagWt_anti (by omega) (hA j))

theorem IsFlagSplitting.presFil_of_basis (hs : IsFlagSplitting F b wt) {A : V →ₗ[K] V}
    (hA : ∀ j, A (b j) ∈ flagWt F (wt j)) : PresFil F A := by
  intro w v hv
  rw [← b.sum_repr v, map_sum]
  refine sum_mem fun j _ => ?_
  by_cases hj : wt j < w
  · rw [hs.repr_eq_zero w v hv j hj, zero_smul, map_zero]; exact zero_mem _
  · rw [map_smul]; exact Submodule.smul_mem _ _ (F.flagWt_anti (by omega) (hA j))

theorem IsFlagSplitting.presFil_grEnd (hs : IsFlagSplitting F b wt) (A : V →ₗ[K] V) :
    PresFil F (grEnd b wt A) :=
  hs.presFil_of_basis fun j => hs.mem_flagWt_of_isHomog (isHomog_grEnd A j)

theorem IsFlagSplitting.raisesFil_sub_grEnd (hs : IsFlagSplitting F b wt) {A : V →ₗ[K] V}
    (hA : PresFil F A) : RaisesFil F (A - grEnd b wt A) := by
  refine hs.raisesFil_of_basis fun j => hs.mem_flagWt_iff.2 fun i hi => ?_
  rw [LinearMap.sub_apply, map_sub, Finsupp.sub_apply, repr_grEnd]
  rcases lt_or_eq_of_le (Int.lt_add_one_iff.mp hi) with hi | hi
  · simp [hi.ne, hs.repr_eq_zero _ _ (hA _ _ (hs.mem j)) i hi]
  · simp [hi]

/-- Uniqueness of the graded part: a degree-preserving `M` with `A − M` raising weights is
`gr A`. -/
theorem IsFlagSplitting.grEnd_eq (hs : IsFlagSplitting F b wt) {A M : V →ₗ[K] V}
    (hM : ∀ j, IsHomog b wt (M (b j)) (wt j)) (hAM : RaisesFil F (A - M)) : grEnd b wt A = M := by
  refine b.ext fun j => b.repr.injective (Finsupp.ext fun i => ?_)
  rw [repr_grEnd]
  split_ifs with hi
  · have h := hs.mem_flagWt_iff.1 (hAM _ _ (hs.mem j)) i (by omega)
    rwa [LinearMap.sub_apply, map_sub, Finsupp.sub_apply, sub_eq_zero] at h
  · exact (hM j i hi).symm

theorem PresFil.comp {A B : V →ₗ[K] V} (hA : PresFil F A) (hB : PresFil F B) : PresFil F (A ∘ₗ B) :=
  fun w v hv => hA w _ (hB w v hv)

theorem RaisesFil.comp_presFil {A B : V →ₗ[K] V} (hA : RaisesFil F A) (hB : PresFil F B) :
    RaisesFil F (A ∘ₗ B) := fun w v hv => hA w _ (hB w v hv)

theorem PresFil.comp_raisesFil {A B : V →ₗ[K] V} (hA : PresFil F A) (hB : RaisesFil F B) :
    RaisesFil F (A ∘ₗ B) := fun w v hv => hA (w + 1) _ (hB w v hv)

theorem RaisesFil.add {A B : V →ₗ[K] V} (hA : RaisesFil F A) (hB : RaisesFil F B) :
    RaisesFil F (A + B) := fun w v hv => add_mem (hA w v hv) (hB w v hv)

theorem IsFlagSplitting.grEnd_comp (hs : IsFlagSplitting F b wt) {A B : V →ₗ[K] V}
    (hA : PresFil F A) (hB : PresFil F B) :
    grEnd b wt (A ∘ₗ B) = grEnd b wt A ∘ₗ grEnd b wt B := by
  refine hs.grEnd_eq (fun j i hi => ?_) ?_
  · have hBj := isHomog_grEnd (b := b) (wt := wt) B j
    rw [LinearMap.comp_apply, ← b.sum_repr (grEnd b wt B (b j)), map_sum, map_sum,
      Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : wt k = wt j
    · rw [map_smul, map_smul, Finsupp.smul_apply, isHomog_grEnd A k i (hk ▸ hi), smul_zero]
    · rw [hBj k hk, zero_smul, map_zero, map_zero, Finsupp.zero_apply]
  · have : A ∘ₗ B - grEnd b wt A ∘ₗ grEnd b wt B =
        (A - grEnd b wt A) ∘ₗ B + grEnd b wt A ∘ₗ (B - grEnd b wt B) := by
      simp only [LinearMap.sub_comp, LinearMap.comp_sub]; abel
    rw [this]
    exact ((hs.raisesFil_sub_grEnd hA).comp_presFil hB).add
      ((hs.presFil_grEnd A).comp_raisesFil (hs.raisesFil_sub_grEnd hB))

theorem IsFlagSplitting.grEnd_id (hs : IsFlagSplitting F b wt) :
    grEnd b wt (LinearMap.id : V →ₗ[K] V) = LinearMap.id :=
  hs.grEnd_eq (fun j i hi => by
    classical
    simp [show j ≠ i from fun h => hi (h ▸ rfl)]) (fun w v _ => by simp)

/-- A weight-raising endomorphism is nilpotent. -/
theorem RaisesFil.isNilpotent {A : V →ₗ[K] V} (hA : RaisesFil F A) : IsNilpotent A := by
  refine ⟨2 * F.len + 1, LinearMap.ext fun v => ?_⟩
  have key : ∀ k : ℕ, ∀ v, (A ^ k) v ∈ flagWt F (-(F.len : ℤ) + k) := by
    intro k
    induction k with
    | zero => intro v; rw [F.flagWt_eq_top (by simp)]; trivial
    | succ k ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply]
      have := hA _ _ (ih v)
      rwa [show -(F.len : ℤ) + k + 1 = -(F.len : ℤ) + ↑(k + 1) by push_cast; ring] at this
  have := key (2 * F.len + 1) v
  rw [F.flagWt_eq_bot (by push_cast; omega)] at this
  simpa using this

/-- `det (1 + N) = 1` for a weight-raising `N`. -/
theorem RaisesFil.det_id_add [FiniteDimensional K V] {N : V →ₗ[K] V} (hN : RaisesFil F N) :
    LinearMap.det (LinearMap.id + N) = 1 := by
  have hn : IsNilpotent (-N) := hN.isNilpotent.neg
  have h := LinearMap.eval_charpoly (-N) (1 : K)
  rw [hn.charpoly_eq_X_pow_finrank, Polynomial.eval_pow, Polynomial.eval_X, one_pow] at h
  rw [h, map_one, sub_neg_eq_add]
  rfl


/-- The graded part of an isometry preserving the filtration is an isometry. -/
theorem IsFlagSplitting.bform_grEnd (hs : IsFlagSplitting F b wt) {A : V →ₗ[K] V}
    (hA : PresFil F A) (hiso : ∀ x y, bform Q (A x) (A y) = bform Q x y) (x y : V) :
    bform Q (grEnd b wt A x) (grEnd b wt A y) = bform Q x y := by
  have key : ∀ i j, bform Q (grEnd b wt A (b i)) (grEnd b wt A (b j)) = bform Q (b i) (b j) := by
    intro i j
    by_cases hij : wt i + wt j = 0
    · have hr := hs.raisesFil_sub_grEnd hA
      have hri := hr _ _ (hs.mem i)
      have hrj := hr _ _ (hs.mem j)
      have hgi := hs.mem_flagWt_of_isHomog (isHomog_grEnd (b := b) (wt := wt) A i)
      rw [LinearMap.sub_apply] at hri hrj
      have hgj := hs.mem_flagWt_of_isHomog (isHomog_grEnd (b := b) (wt := wt) A j)
      have h := hiso (b i) (b j)
      rw [← sub_add_cancel (A (b i)) (grEnd b wt A (b i)),
        ← sub_add_cancel (A (b j)) (grEnd b wt A (b j))] at h
      simp only [map_add, LinearMap.add_apply] at h
      rw [F.bform_flagWt (by omega) hri hrj, F.bform_flagWt (by omega) hri hgj,
        F.bform_flagWt (by omega) hgi hrj] at h
      simpa using h
    · rw [hs.bform_eq_zero_of_isHomog (isHomog_grEnd A i) (isHomog_grEnd A j) hij,
        hs.orth i j hij]
  have := LinearMap.BilinForm.ext_basis (B := (bform Q).compl₁₂ (grEnd b wt A) (grEnd b wt A))
    (F₂ := bform Q) b key
  exact congr($this x y)

/-- `T` acts diagonally on the splitting basis by weights: `λ(τ) bᵢ = τ^{wtᵢ} bᵢ`. -/
def cochar (b : Basis ι K V) (wt : ι → ℤ) (τ : K) : V →ₗ[K] V :=
  b.constr K fun i => τ ^ wt i • b i

omit [Invertible (2 : K)] [Fintype ι] in
theorem cochar_basis (τ : K) (i : ι) : cochar b wt τ (b i) = τ ^ wt i • b i := by
  rw [cochar, Basis.constr_basis]

omit [Invertible (2 : K)] [Fintype ι] in
theorem cochar_mul (τ σ : K) :
    cochar b wt τ ∘ₗ cochar b wt σ = cochar b wt (τ * σ) :=
  b.ext fun i => by
    rw [LinearMap.comp_apply, cochar_basis, map_smul, cochar_basis, cochar_basis, smul_smul,
      mul_zpow, mul_comm]

omit [Invertible (2 : K)] [Fintype ι] in
theorem cochar_one : cochar b wt (1 : K) = LinearMap.id :=
  b.ext fun i => by rw [cochar_basis, one_zpow, one_smul, LinearMap.id_apply]


theorem IsFlagSplitting.bform_cochar (hs : IsFlagSplitting F b wt) {τ : K} (hτ : τ ≠ 0)
    (x y : V) : bform Q (cochar b wt τ x) (cochar b wt τ y) = bform Q x y := by
  have key : ∀ i j, bform Q (cochar b wt τ (b i)) (cochar b wt τ (b j)) = bform Q (b i) (b j) := by
    intro i j
    rw [cochar_basis, cochar_basis, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
    by_cases hij : wt i + wt j = 0
    · rw [← mul_assoc, ← zpow_add₀ hτ, hij, zpow_zero, one_mul]
    · rw [hs.orth i j hij, mul_zero, mul_zero]
  have := LinearMap.BilinForm.ext_basis (B := (bform Q).compl₁₂ (cochar b wt τ) (cochar b wt τ))
    (F₂ := bform Q) b key
  exact congr($this x y)

theorem IsFlagSplitting.det_cochar [FiniteDimensional K V] (hs : IsFlagSplitting F b wt)
    {τ : K} (hτ : τ ≠ 0) : LinearMap.det (cochar b wt τ) = 1 := by
  classical
  rw [← LinearMap.det_toMatrix b]
  have : LinearMap.toMatrix b b (cochar b wt τ) = Matrix.diagonal fun i => τ ^ wt i := by
    ext i j
    rw [LinearMap.toMatrix_apply, cochar_basis, map_smul, b.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, Matrix.diagonal_apply]
    split_ifs with h1 h2 h2 <;> simp_all [eq_comm]
  have hprod : ∀ s : Finset ι, ∏ i ∈ s, τ ^ wt i = τ ^ ∑ i ∈ s, wt i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hτ]
  rw [this, Matrix.det_diagonal, hprod, hs.sum_wt, zpow_zero]


/-- An invertible endomorphism preserving `b` with determinant `1` is `P(g)` for some `g ∈ GSpin(V)`
(`gspin_specP_surjective_SO`). -/
theorem exists_specP_eq [FiniteDimensional K V] (hQ : IsNondeg Q) {A B : V →ₗ[K] V}
    (hAB : A ∘ₗ B = LinearMap.id) (hBA : B ∘ₗ A = LinearMap.id)
    (hiso : ∀ x y, bform Q (A x) (A y) = bform Q x y) (hdet : LinearMap.det A = 1) :
    ∃ g : GSpin Q, (specP Q g : V →ₗ[K] V) = A := by
  obtain ⟨g, hg⟩ := gspin_specP_surjective_SO Q hQ (LinearEquiv.ofLinearMap A B hAB hBA)
    (fun v => by
      rw [← QuadraticMap.associated_eq_self_apply K Q, ← QuadraticMap.associated_eq_self_apply K Q]
      exact hiso v v) hdet
  exact ⟨g, by rw [hg]; rfl⟩

/-- **The cocharacter** `λ(τ) : bᵢ ↦ τ^{wtᵢ} bᵢ` of `SO(V)` lifts to `GSpin(V)`. -/
theorem IsFlagSplitting.exists_cochar_lift [FiniteDimensional K V] (hQ : IsNondeg Q)
    (hs : IsFlagSplitting F b wt) {τ : K} (hτ : τ ≠ 0) :
    ∃ T : GSpin Q, ∀ i, specP Q T (b i) = τ ^ wt i • b i := by
  obtain ⟨T, hT⟩ := exists_specP_eq hQ
    (by rw [cochar_mul τ τ⁻¹, mul_inv_cancel₀ hτ, cochar_one])
    (by rw [cochar_mul τ⁻¹ τ, inv_mul_cancel₀ hτ, cochar_one])
    (hs.bform_cochar hτ) (hs.det_cochar hτ)
  exact ⟨T, fun i => by rw [← cochar_basis, ← hT]; rfl⟩

/-- **Levi decomposition of `P_F`** (Thesis §5.1.2: `P = M ⋉ N`): every `p ∈ P_F` is `m y`, where
`P(m)` preserves the weight of each `bⱼ` (`P(m)` is the graded part of `P(p)`, so `m` lies in the
Levi subgroup, which centralizes the cocharacter `λ` modulo scalars) and `P(y)` is trivial on the
graded pieces of the weight filtration. -/
theorem IsFlagSplitting.exists_levi_decomp [FiniteDimensional K V] (hQ : IsNondeg Q)
    (hs : IsFlagSplitting F b wt) {p : GSpin Q} (hp : p ∈ flagStab F) :
    ∃ m y : GSpin Q, p = m * y ∧ (∀ j, IsHomog b wt (specP Q m (b j)) (wt j)) ∧
      RaisesFil F ((specP Q y : V →ₗ[K] V) - LinearMap.id) := by
  set A : V →ₗ[K] V := (specP Q p : V →ₗ[K] V)
  set B : V →ₗ[K] V := (specP Q p⁻¹ : V →ₗ[K] V)
  have hA : PresFil F A := fun w v hv => flagStab_mapsTo_flagWt hp w hv
  have hB : PresFil F B := fun w v hv => flagStab_mapsTo_flagWt ((flagStab F).inv_mem hp) w hv
  have hAB : A ∘ₗ B = LinearMap.id := by
    ext v; exact specP_inv_apply_apply p v
  have hBA : B ∘ₗ A = LinearMap.id := by
    ext v
    have := specP_inv_apply_apply p⁻¹ v
    rwa [inv_inv] at this
  have hgAB : grEnd b wt A ∘ₗ grEnd b wt B = LinearMap.id := by
    rw [← hs.grEnd_comp hA hB, hAB, hs.grEnd_id]
  have hgBA : grEnd b wt B ∘ₗ grEnd b wt A = LinearMap.id := by
    rw [← hs.grEnd_comp hB hA, hBA, hs.grEnd_id]
  -- `gr(B) ∘ A = 1 + N` with `N` raising weights
  set N := grEnd b wt B ∘ₗ (A - grEnd b wt A)
  have hN : RaisesFil F N := (hs.presFil_grEnd B).comp_raisesFil (hs.raisesFil_sub_grEnd hA)
  have hBA' : grEnd b wt B ∘ₗ A = LinearMap.id + N := by
    change _ = _ + grEnd b wt B ∘ₗ (A - grEnd b wt A)
    rw [LinearMap.comp_sub, hgBA]; abel
  have hdetB : LinearMap.det (grEnd b wt B) = 1 := by
    have := congr_arg LinearMap.det hBA'
    rwa [LinearMap.det_comp, det_specP, mul_one, hN.det_id_add] at this
  have hdetA : LinearMap.det (grEnd b wt A) = 1 := by
    have := congr_arg LinearMap.det hgAB
    rwa [LinearMap.det_comp, hdetB, mul_one, LinearMap.det_id] at this
  obtain ⟨m, hm⟩ := exists_specP_eq hQ hgAB hgBA (hs.bform_grEnd hA (bform_specP p)) hdetA
  have hmB : (specP Q m⁻¹ : V →ₗ[K] V) = grEnd b wt B := by
    have h1 : (specP Q m : V →ₗ[K] V) ∘ₗ (specP Q m⁻¹ : V →ₗ[K] V) = LinearMap.id := by
      ext v; exact specP_inv_apply_apply m v
    calc (specP Q m⁻¹ : V →ₗ[K] V)
        = (grEnd b wt B ∘ₗ grEnd b wt A) ∘ₗ (specP Q m⁻¹ : V →ₗ[K] V) := by rw [hgBA]; rfl
      _ = grEnd b wt B ∘ₗ ((specP Q m : V →ₗ[K] V) ∘ₗ (specP Q m⁻¹ : V →ₗ[K] V)) := by
          rw [hm]; rfl
      _ = grEnd b wt B := by rw [h1]; rfl
  refine ⟨m, m⁻¹ * p, by group, fun j => by rw [← LinearEquiv.coe_coe, hm]; exact isHomog_grEnd A j,
    ?_⟩
  have : (specP Q (m⁻¹ * p) : V →ₗ[K] V) = grEnd b wt B ∘ₗ A := by
    rw [← hmB, map_mul]; rfl
  rw [this, hBA', add_sub_cancel_left]
  exact hN


omit [Invertible (2 : K)] [Fintype ι] in
theorem repr_cochar (τ : K) (x : V) (i : ι) :
    b.repr (cochar b wt τ x) i = τ ^ wt i * b.repr x i := by
  have : (b.coord i) ∘ₗ cochar b wt τ = τ ^ wt i • b.coord i := by
    classical
    refine b.ext fun j => ?_
    rw [LinearMap.comp_apply, cochar_basis, map_smul, LinearMap.smul_apply, Basis.coord_apply,
      b.repr_self, Finsupp.single_apply]
    split_ifs with h <;> simp [h]
  exact congr($this x)

omit [Invertible (2 : K)] [Fintype ι] in
/-- A weight-preserving endomorphism commutes with the cocharacter. -/
theorem cochar_comp_of_isHomog {M : V →ₗ[K] V} (hM : ∀ j, IsHomog b wt (M (b j)) (wt j)) (τ : K) :
    cochar b wt τ ∘ₗ M = M ∘ₗ cochar b wt τ := by
  refine b.ext fun j => b.repr.injective (Finsupp.ext fun i => ?_)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, repr_cochar, cochar_basis, map_smul, map_smul,
    Finsupp.smul_apply, smul_eq_mul]
  by_cases h : wt i = wt j
  · rw [h]
  · rw [hM j i h, mul_zero, mul_zero]

omit [Fintype ι] in
/-- A lift `m ∈ GSpin(V)` of a weight-preserving isometry commutes with a lift `T` of the
cocharacter up to a central scalar (`ker P = G_m`). -/
theorem exists_mul_eq_scalar_mul [FiniteDimensional K V] (hQ : IsNondeg Q) {τ : K} {T m : GSpin Q}
    (hT : ∀ i, specP Q T (b i) = τ ^ wt i • b i) (hm : ∀ j, IsHomog b wt (specP Q m (b j)) (wt j)) :
    ∃ s : Kˣ, T * m = scalarGSpin Q s * (m * T) := by
  have hTc : (specP Q T : V →ₗ[K] V) = cochar b wt τ :=
    b.ext fun i => by rw [cochar_basis]; exact hT i
  have hcomm : specP Q (T * m) = specP Q (m * T) := by
    refine LinearEquiv.toLinearMap_injective ?_
    rw [map_mul, map_mul]
    change (specP Q T : V →ₗ[K] V) ∘ₗ (specP Q m : V →ₗ[K] V) =
      (specP Q m : V →ₗ[K] V) ∘ₗ (specP Q T : V →ₗ[K] V)
    rw [hTc]
    exact cochar_comp_of_isHomog hm τ
  have hk : T * m * (m * T)⁻¹ ∈ (specP Q).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcomm, mul_inv_cancel]
  rw [ker_specP hQ] at hk
  obtain ⟨s, hs⟩ := hk
  exact ⟨s, by rw [hs, inv_mul_cancel_right]⟩

end Levi

end GSpinGGP
