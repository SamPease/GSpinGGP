/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.LeviLattice

/-!
# Weight spaces of a splitting

For a basis `b` with weights `wt` (a splitting of the weight filtration of an isotropic flag), the
weight spaces `wtSpan b wt w`, the projections `wtProj`, the Levi subgroup `flagLevi`, its split
centre `wtScalar` and the blocks `wtBlock` depend on `(b, wt)` only through the family of weight
spaces, up to relabelling the weights:

* `wtProj_eq_of_wtSpan_eq`, `wtBlock_eq_of_wtSpan_eq`, `flagLevi_eq_of_wtSpan_eq`,
  `wtScalar_le_of_wtSpan_eq`: if every weight space of one splitting is a weight space of the
  other (and conversely), the projections, blocks, Levi subgroups and split centres agree;
* `wtSpan_zero_eq_of_wtSpan_eq`: the weight-`0` spaces then agree (the other weight spaces are
  totally isotropic, a nonzero weight-`0` space is not);
* `wtSpan_reindexUnits`: reindexing and rescaling the basis does not change the weight spaces
  (`IsFlagSplitting.reindexUnits`, `GGP/Cocharacter.lean`).

**Determinant duality** (`det_wtBlock_neg_mul`): `det(P(g)|_{V_{−w}}) · det(P(g)|_{V_w}) = 1` for
`g` in the Levi subgroup: `b` pairs `V_w` with `V_{−w}` perfectly and `P(g)` preserves `b`, so
`aᵀ B c = B` for the blocks `a`, `c` of `P(g)` and the Gram matrix `B` (`transpose_mul_gram_mul`).
Hence `log ‖det(m|_{V_w})‖` is `0` or `± log ‖det(m|_{V_{i+1}})‖` (`log_det_wtBlock_cases`).
-/

noncomputable section

open Module Matrix

namespace GSpinGGP

section WtSpan

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {ι ι' : Type*} {b : Basis ι K V} {wt : ι → ℤ} {b' : Basis ι' K V} {wt' : ι' → ℤ}

theorem basis_mem_wtSpan (j : ι) : b j ∈ wtSpan b wt (wt j) :=
  Submodule.subset_span ⟨j, rfl, rfl⟩

/-- The weight projections on a vector of the weight-`u` space. -/
theorem wtProj_apply_of_mem_wtSpan {u : ℤ} {x : V} (hx : x ∈ wtSpan b wt u) (w : ℤ) :
    wtProj b wt w x = if u = w then x else 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    simp only [Set.mem_ofPred_eq] at hj
    rw [wtProj_basis, hj]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]; split_ifs <;> simp
  | smul a x _ hx => rw [map_smul, hx]; split_ifs <;> simp

theorem isHomog_of_mem_wtSpan {u : ℤ} {x : V} (hx : x ∈ wtSpan b wt u) : IsHomog b wt x u :=
  (isHomog_iff_wtProj x u).2 (by rw [wtProj_apply_of_mem_wtSpan hx, ite_eq_left rfl])

/-- Weight spaces of different weights meet in `0`. -/
theorem disjoint_wtSpan {u v : ℤ} (h : u ≠ v) : Disjoint (wtSpan b wt u) (wtSpan b wt v) :=
  b.linearIndependent.disjoint_span_image (Set.disjoint_left.2 fun _ hu hv => h (hu.symm.trans hv))

theorem wtProj_eq_zero_of_forall_ne {w : ℤ} (h : ∀ j, wt j ≠ w) : wtProj b wt w = 0 :=
  b.ext fun j => by rw [wtProj_basis, ite_eq_right (h j), LinearMap.zero_apply]

theorem exists_wt_eq_of_wtSpan_ne_bot {w : ℤ} (h : wtSpan b wt w ≠ ⊥) : ∃ j, wt j = w := by
  by_contra hne
  push Not at hne
  refine h ?_
  rw [wtSpan, Submodule.span_eq_bot]
  rintro _ ⟨j, hj, rfl⟩
  exact absurd hj (hne j)

/-- **The weight projections depend only on the weight spaces**: if every weight space of
`(b, wt)` is a weight space of `(b', wt')` and `V'_{w'} = V_w`, the projections onto them agree
(both are the projection onto `V_w` along the sum of the other weight spaces). -/
theorem wtProj_eq_of_wtSpan_eq (h : ∀ u, ∃ u', wtSpan b wt u = wtSpan b' wt' u') {w w' : ℤ}
    (hw : wtSpan b' wt' w' = wtSpan b wt w) : wtProj b' wt' w' = wtProj b wt w := by
  refine b.ext fun j => ?_
  obtain ⟨u', hu'⟩ := h (wt j)
  have hj' : b j ∈ wtSpan b' wt' u' := hu' ▸ basis_mem_wtSpan j
  rw [wtProj_apply_of_mem_wtSpan hj', wtProj_basis]
  by_cases hj : wt j = w
  · have hmem : b j ∈ wtSpan b' wt' w' := by rw [hw, ← hj]; exact basis_mem_wtSpan j
    have : u' = w' := by
      by_contra hne
      exact b.ne_zero j (Submodule.disjoint_def.1 (disjoint_wtSpan hne) _ hj' hmem)
    rw [ite_eq_left this, ite_eq_left hj]
  · have : u' ≠ w' := by
      rintro rfl
      have hmem : b j ∈ wtSpan b wt w := hw ▸ hj'
      exact b.ne_zero j (Submodule.disjoint_def.1 (disjoint_wtSpan hj) _
        (basis_mem_wtSpan j) hmem)
    rw [ite_eq_right this, ite_eq_right hj]

theorem wtBlock_eq_of_wtSpan_eq (h : ∀ u, ∃ u', wtSpan b wt u = wtSpan b' wt' u') {w w' : ℤ}
    (hw : wtSpan b' wt' w' = wtSpan b wt w) (A : V →ₗ[K] V) :
    wtBlock b' wt' w' A = wtBlock b wt w A := by
  simp only [wtBlock, wtProj_eq_of_wtSpan_eq h hw]

/-- `wtBlock` on a weight that does not occur is the identity. -/
theorem wtBlock_eq_id_of_forall_ne {w : ℤ} (h : ∀ j, wt j ≠ w) (A : V →ₗ[K] V) :
    wtBlock b wt w A = LinearMap.id := by
  simp [wtBlock, wtProj_eq_zero_of_forall_ne h]

end WtSpan

section WtSpanQ

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
variable {ι ι' : Type*} {b : Basis ι K V} {wt : ι → ℤ} {b' : Basis ι' K V} {wt' : ι' → ℤ}

/-- **The Levi subgroup depends only on the weight spaces** (up to relabelling). -/
theorem flagLevi_eq_of_wtSpan_eq (h : ∀ u, ∃ u', wtSpan b wt u = wtSpan b' wt' u')
    (h' : ∀ u', ∃ u, wtSpan b' wt' u' = wtSpan b wt u) :
    flagLevi (Q := Q) b' wt' = flagLevi (Q := Q) b wt := by
  ext g
  constructor
  · intro hg w
    obtain ⟨w', hw'⟩ := h w
    rw [← wtProj_eq_of_wtSpan_eq h hw'.symm]
    exact hg w'
  · intro hg w'
    obtain ⟨w, hw⟩ := h' w'
    rw [wtProj_eq_of_wtSpan_eq h hw]
    exact hg w

theorem mem_wtScalar_iff_wtSpan {g : GSpin Q} :
    g ∈ wtScalar Q b wt ↔
      ∃ t : ℤ → K, t 0 = 1 ∧ ∀ w, ∀ x ∈ wtSpan b wt w, specP Q g x = t w • x := by
  constructor
  · rintro ⟨t, ht0, ht⟩
    refine ⟨t, ht0, fun w x hx => ?_⟩
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      simp only [Set.mem_ofPred_eq] at hj
      rw [ht j, hj]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
    | smul a x _ hx => rw [map_smul, hx, smul_comm]
  · rintro ⟨t, ht0, ht⟩
    exact ⟨t, ht0, fun j => ht _ _ (basis_mem_wtSpan j)⟩

/-- **The split centre depends only on the weight spaces** (up to relabelling the nonzero
weights). -/
theorem wtScalar_le_of_wtSpan_eq (h' : ∀ u', ∃ u, wtSpan b' wt' u' = wtSpan b wt u)
    (h0 : wtSpan b' wt' 0 = wtSpan b wt 0) : wtScalar Q b wt ≤ wtScalar Q b' wt' := by
  classical
  intro g hg
  obtain ⟨t, ht0, ht⟩ := mem_wtScalar_iff_wtSpan.1 hg
  refine mem_wtScalar_iff_wtSpan.2 ⟨fun u' => if u' = 0 then 1 else t (h' u').choose,
    by simp, fun u' x hx => ?_⟩
  by_cases hu : u' = 0
  · subst hu
    simp only [↓reduceIte, one_smul]
    rw [ht 0 x (h0 ▸ hx), ht0, one_smul]
  · simp only [hu, ↓reduceIte]
    exact ht _ x ((h' u').choose_spec ▸ hx)

variable [Finite ι] [Finite ι']

theorem bform_eq_zero_of_mem_wtSpan (horth : ∀ i j, wt i + wt j ≠ 0 → bform Q (b i) (b j) = 0)
    {x y : V} {u v : ℤ} (hx : x ∈ wtSpan b wt u) (hy : y ∈ wtSpan b wt v) (h : u + v ≠ 0) :
    bform Q x y = 0 :=
  have := Fintype.ofFinite ι
  bform_eq_zero_of_isHomog_of_orth horth (isHomog_of_mem_wtSpan hx) (isHomog_of_mem_wtSpan hy) h

/-- A nonzero weight-`0` space is not a weight space of nonzero weight of another splitting: those
are totally isotropic, and `b` is nondegenerate on the weight-`0` space. -/
theorem eq_zero_of_wtSpan_zero_eq (hQ : IsNondeg Q)
    (horth : ∀ i j, wt i + wt j ≠ 0 → bform Q (b i) (b j) = 0)
    (horth' : ∀ i j, wt' i + wt' j ≠ 0 → bform Q (b' i) (b' j) = 0) {u' : ℤ}
    (hu : wtSpan b wt 0 = wtSpan b' wt' u') (hne : wtSpan b wt 0 ≠ ⊥) : u' = 0 := by
  have := Fintype.ofFinite ι
  obtain ⟨j, hj⟩ := exists_wt_eq_of_wtSpan_ne_bot hne
  obtain ⟨k, hk, hjk⟩ := exists_bform_ne_of_orth hQ horth j
  by_contra hu0
  refine hjk (bform_eq_zero_of_mem_wtSpan horth' (u := u') (v := u') ?_ ?_ (by omega))
  · rw [← hu, ← hj]; exact basis_mem_wtSpan j
  · rw [← hu, show (0 : ℤ) = wt k by omega]; exact basis_mem_wtSpan k

/-- **The weight-`0` spaces agree** when the families of weight spaces have the same members. -/
theorem wtSpan_zero_eq_of_wtSpan_eq (hQ : IsNondeg Q)
    (horth : ∀ i j, wt i + wt j ≠ 0 → bform Q (b i) (b j) = 0)
    (horth' : ∀ i j, wt' i + wt' j ≠ 0 → bform Q (b' i) (b' j) = 0)
    (h : ∀ u, ∃ u', wtSpan b wt u = wtSpan b' wt' u')
    (h' : ∀ u', ∃ u, wtSpan b' wt' u' = wtSpan b wt u) :
    wtSpan b' wt' 0 = wtSpan b wt 0 := by
  obtain ⟨u', hu'⟩ := h 0
  by_cases hne : wtSpan b wt 0 = ⊥
  · obtain ⟨u, hu⟩ := h' 0
    by_cases hne' : wtSpan b' wt' 0 = ⊥
    · rw [hne, hne']
    · have := eq_zero_of_wtSpan_zero_eq hQ horth' horth hu hne'
      rw [hu, this]
  · have := eq_zero_of_wtSpan_zero_eq hQ horth horth' hu' hne
    rw [hu', this]

end WtSpanQ

/-! ### Reindexing and rescaling a basis -/

section Rebase

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
variable {ι : Type*} {b : Basis ι K V} {wt : ι → ℤ}
variable [Fintype ι] {κ : Type*} [Fintype κ]

omit [Invertible (2 : K)] [Fintype ι] [Fintype κ] in
/-- Reindexing and rescaling the basis does not change the weight spaces. -/
theorem wtSpan_reindexUnits (e : ι ≃ κ) (u : κ → Kˣ) (w : ℤ) :
    wtSpan ((b.reindex e).unitsSMul u) (wt ∘ e.symm) w = wtSpan b wt w := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, hi, rfl⟩
    rw [Basis.unitsSMul_apply, Basis.reindex_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e.symm i, hi, rfl⟩)
  · rintro _ ⟨j, hj, rfl⟩
    have : b j = (u (e j))⁻¹ • (b.reindex e).unitsSMul u (e j) := by
      rw [Basis.unitsSMul_apply, Basis.reindex_apply, Equiv.symm_apply_apply, smul_smul,
        inv_mul_cancel, one_smul]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨e j, ?_, rfl⟩)
    simpa using hj

end Rebase

/-! ## 2. Determinant duality -/

section DetDuality

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} {F : IsotropicFlag Q}
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {b : Basis ι K V} {wt : ι → ℤ}

theorem toMatrix_specP_eq_zero_of_wt_ne {g : GSpin Q} (hg : g ∈ flagLevi (Q := Q) b wt) {i j : ι}
    (h : wt i ≠ wt j) : LinearMap.toMatrix b b (specP Q g : V →ₗ[K] V) i j = 0 := by
  rw [LinearMap.toMatrix_apply]
  exact mem_flagLevi_iff.1 hg j i h

theorem det_wtBlock_eq_det_toSquareBlockProp {g : GSpin Q} (hg : g ∈ flagLevi (Q := Q) b wt)
    (w : ℤ) : LinearMap.det (wtBlock b wt w (specP Q g : V →ₗ[K] V)) =
      ((LinearMap.toMatrix b b (specP Q g : V →ₗ[K] V)).toSquareBlockProp
        (fun i => wt i = w)).det := by
  set A := LinearMap.toMatrix b b (specP Q g : V →ₗ[K] V) with hAdef
  set N := LinearMap.toMatrix b b (wtBlock b wt w (specP Q g : V →ₗ[K] V))
  have hN : ∀ i j, N i j = if wt j = w then A i j else if i = j then 1 else 0 := by
    intro i j
    simp only [N, hAdef]
    rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
    simp only [wtBlock, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_add, map_sub,
      Finsupp.add_apply, Finsupp.sub_apply, repr_wtProj, b.repr_self, Finsupp.single_apply,
      LinearEquiv.coe_coe]
    have h0 := fun (h : wt i ≠ wt j) => mem_flagLevi_iff.1 hg j i h
    by_cases hij : j = i
    · subst hij; by_cases hj : wt j = w <;> simp [hj]
    · have hij' : ¬ i = j := Ne.symm hij
      by_cases hj : wt j = w <;> by_cases hi : wt i = w
      · simp [hj, hi, hij]
      · simp [hj, hi, hij, h0 (by rw [hj]; exact hi)]
      · simp [hj, hi, hij, hij', h0 (by rw [hi]; exact Ne.symm hj)]
      · simp [hj, hi, hij, hij']
  rw [← LinearMap.det_toMatrix b, twoBlockTriangular_det N (fun i => wt i = w) ?_]
  · have h1 : N.toSquareBlockProp (fun i => ¬ wt i = w) = 1 := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      rw [toSquareBlockProp_def, of_apply, hN]
      simp only [hj, ite_false]
      by_cases h : i = j
      · subst h; simp
      · rw [ite_eq_right h, one_apply_ne (by simpa [Subtype.ext_iff] using h)]
    have h2 : N.toSquareBlockProp (fun i => wt i = w) =
        A.toSquareBlockProp (fun i => wt i = w) := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      rw [toSquareBlockProp_def, toSquareBlockProp_def, of_apply, of_apply, hN]
      simp [hj]
    rw [h1, h2, det_one, mul_one]
  · intro i hi j hj
    rw [hN, ite_eq_left hj]
    exact toMatrix_specP_eq_zero_of_wt_ne hg (by rwa [hj])

omit [DecidableEq ι] in
/-- A sum over `ι` of a function vanishing off `{wt = w}` is a sum over `{wt = w}`. -/
theorem sum_eq_sum_subtype_of_wt {M : Type*} [AddCommMonoid M] (wt : ι → ℤ) (w : ℤ) (f : ι → M)
    (hf : ∀ i, wt i ≠ w → f i = 0) :
    ∑ i, f i = ∑ i : {i // wt i = w}, f i := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun i => wt i = w) f
  rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun i : {i // ¬ wt i = w} => f i)
    (fun i _ => hf i.1 i.2), add_zero] at h
  exact h.symm

/-- **The pairing of `V_w` with `V_{−w}`**: for `g` in the Levi subgroup, with `a`, `c` the blocks
of `P(g)` on `V_w`, `V_{−w}` and `B` the Gram matrix `b(b_s, b_t)` (`wt s = w`, `wt t = −w`),
`aᵀ B c = B` (`P(g)` preserves `b`). -/
theorem transpose_mul_gram_mul {g : GSpin Q} (hg : g ∈ flagLevi (Q := Q) b wt) (w : ℤ) :
    ((LinearMap.toMatrix b b (specP Q g : V →ₗ[K] V)).toSquareBlockProp (fun i => wt i = w))ᵀ *
        (of fun (s : {i // wt i = w}) (t : {i // wt i = -w}) => bform Q (b s) (b t)) *
        (LinearMap.toMatrix b b (specP Q g : V →ₗ[K] V)).toSquareBlockProp
          (fun i => wt i = -w) =
      of fun (s : {i // wt i = w}) (t : {i // wt i = -w}) => bform Q (b s) (b t) := by
  set A := LinearMap.toMatrix b b (specP Q g : V →ₗ[K] V) with hAdef
  have hA : ∀ j, specP Q g (b j) = ∑ i, A i j • b i := fun j => by
    rw [hAdef]; simp only [LinearMap.toMatrix_apply, LinearEquiv.coe_coe]; exact (b.sum_repr _).symm
  have h0 : ∀ i j, wt i ≠ wt j → A i j = 0 := fun i j h => toMatrix_specP_eq_zero_of_wt_ne hg h
  ext s t
  have e := bform_specP g (b s) (b t)
  rw [hA, hA] at e
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at e
  rw [of_apply, ← e, sum_eq_sum_subtype_of_wt wt (-w)
    (fun x => A x t * ∑ x1, A x1 s * bform Q (b x1) (b x))
    (fun x hx => by rw [h0 x t (by rw [t.2]; exact hx), zero_mul])]
  simp only [Matrix.mul_apply, transpose_apply, toSquareBlockProp_def, of_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_eq_sum_subtype_of_wt wt w (fun x1 => A x1 s * bform Q (b x1) (b j))
    (fun x1 hx => by rw [h0 x1 s (by rw [s.2]; exact hx), zero_mul]), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Determinant duality on the Levi subgroup**: `det(P(g)|_{V_{−w}}) · det(P(g)|_{V_w}) = 1` for
`g ∈ M_F` (`V_w`, `V_{−w}` are paired perfectly by `b`, and `P(g)` preserves `b`:
`transpose_mul_gram_mul`). -/
theorem det_toSquareBlockProp_neg_mul (hQ : IsNondeg Q) (hs : IsFlagSplitting F b wt)
    {g : GSpin Q} (hg : g ∈ flagLevi (Q := Q) b wt) (w : ℤ) :
    ((LinearMap.toMatrix b b (specP Q g : V →ₗ[K] V)).toSquareBlockProp
        (fun i => wt i = -w)).det *
      ((LinearMap.toMatrix b b (specP Q g : V →ₗ[K] V)).toSquareBlockProp
        (fun i => wt i = w)).det = 1 := by
  set A := LinearMap.toMatrix b b (specP Q g : V →ₗ[K] V)
  set a := A.toSquareBlockProp (fun i => wt i = w)
  set c := A.toSquareBlockProp (fun i => wt i = -w)
  set B : Matrix {i // wt i = w} {i // wt i = -w} K := of fun s t => bform Q (b s) (b t)
  have key : aᵀ * B * c = B := transpose_mul_gram_mul hg w
  let e : {i // wt i = -w} ≃ {i // wt i = w} := Fintype.equivOfCardEq (hs.card_wt_neg hQ w)
  set B' := B.submatrix id e.symm
  set c' := c.submatrix e.symm e.symm
  have h1 : B' * c' = (B * c).submatrix id e.symm := submatrix_mul_equiv B c id e.symm e.symm
  have h2 : aᵀ * (B * c).submatrix id e.symm = (aᵀ * (B * c)).submatrix id e.symm := rfl
  have key' : aᵀ * B' * c' = B' := by
    rw [Matrix.mul_assoc, h1, h2, ← Matrix.mul_assoc, key]
  have hB' : B'.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.2 h0
    set y : V := ∑ s, v s • b (e.symm s)
    have hy : ∀ k, wt k = -(-w) → bform Q (b k) y = 0 := by
      intro k hk
      rw [neg_neg] at hk
      have := congrFun hv ⟨k, hk⟩
      simp only [mulVec, dotProduct, B', B, submatrix_apply, of_apply, id, Pi.zero_apply] at this
      simp only [y, map_sum, map_smul, smul_eq_mul]
      rw [← this]
      exact Finset.sum_congr rfl fun s _ => mul_comm _ _
    apply hv0
    funext s
    have h := hs.repr_eq_zero_of_bform hQ hy (e.symm s).2
    have hinj : ∀ s', (e.symm s' : ι) = e.symm s → s' = s :=
      fun s' h => e.symm.injective (Subtype.ext h)
    simp only [y, map_sum, map_smul, b.repr_self, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul] at h
    rw [Finset.sum_eq_single s (fun s' _ hs' => by rw [if_neg (fun h => hs' (hinj s' h)), mul_zero])
      (by simp), if_pos rfl, mul_one] at h
    exact h
  have hdet := congrArg det key'
  rw [det_mul, det_mul, det_transpose] at hdet
  have hc : c'.det = c.det := det_submatrix_equiv_self e.symm c
  rw [hc] at hdet
  have h3 : a.det * c.det * B'.det = 1 * B'.det :=
    calc a.det * c.det * B'.det = a.det * B'.det * c.det := by ring
      _ = 1 * B'.det := by rw [hdet, one_mul]
  rw [mul_comm]; exact mul_right_cancel₀ hB' h3

/-- **Determinant duality**: `det(P(g)|_{V_{−w}}) · det(P(g)|_{V_w}) = 1` for `g ∈ M_F`, written
with the weights `−wt` of the opposite datum.  On the split centre `wtScalar` this is the scalar
statement `t(w) t(−w) = 1` of `mul_neg_eq_one_of_orth` raised to `dim V_w = dim V_{−w}`. -/
theorem det_wtBlock_neg_mul (hQ : IsNondeg Q) (hs : IsFlagSplitting F b wt) {g : GSpin Q}
    (hg : g ∈ flagLevi (Q := Q) b wt) (w : ℤ) :
    LinearMap.det (wtBlock b (-wt) w (specP Q g : V →ₗ[K] V)) *
      LinearMap.det (wtBlock b wt w (specP Q g : V →ₗ[K] V)) = 1 := by
  rw [wtBlock_neg_wt, det_wtBlock_eq_det_toSquareBlockProp hg,
    det_wtBlock_eq_det_toSquareBlockProp hg, det_toSquareBlockProp_neg_mul hQ hs hg w]

end DetDuality

/-! ## 3. Weights of a splitting -/

section Weights

/-- A weight `w` of a flag splitting either does not occur, or is `±(i + 1)` for some
`i < len`, or is `0`. -/
theorem IsFlagSplitting.wt_trichotomy {K V : Type*} [Field K]
    [Invertible (2 : K)] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    {Fl : IsotropicFlag Q} {ι : Type*} [Fintype ι] {b : Basis ι K V} {wt : ι → ℤ}
    (hs : IsFlagSplitting Fl b wt) (w : ℤ) :
    (∀ j, wt j ≠ w) ∨ w = 0 ∨ ∃ i : Fin Fl.len, ((i : ℤ) + 1 = w ∨ (i : ℤ) + 1 = -w) := by
  by_cases h : ∃ j, wt j = w
  · obtain ⟨j, rfl⟩ := h
    right
    have h1 := hs.wt_le j
    have h2 := hs.neg_len_le j
    rcases lt_trichotomy (wt j) 0 with hlt | heq | hgt
    · exact Or.inr ⟨⟨(-wt j - 1).toNat, by omega⟩, Or.inr (by simp; omega)⟩
    · exact Or.inl heq
    · exact Or.inr ⟨⟨(wt j - 1).toNat, by omega⟩, Or.inl (by simp; omega)⟩
  · push Not at h
    exact Or.inl h

/-- **`log ‖det(m|_{V_w})‖` on the Levi subgroup** is `0` when `w` does not occur, and
`± log ‖det(m|_{V_{i+1}})‖` for some `i < len` otherwise, provided `w ≠ 0` or the weight `0` does
not occur (determinant duality `det_wtBlock_neg_mul` for `w < 0`). -/
theorem IsFlagSplitting.log_det_wtBlock_cases {K V : Type*}
    [NontriviallyNormedField K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {Fl : IsotropicFlag Q} {ι : Type*} [Fintype ι] {b : Basis ι K V}
    {wt : ι → ℤ} (hQ : IsNondeg Q) (hs : IsFlagSplitting Fl b wt) (w : ℤ)
    (hw : w = 0 → ∀ j, wt j ≠ 0) :
    (∀ g ∈ flagLevi (Q := Q) b wt,
      Real.log ‖LinearMap.det (wtBlock b wt w (specP Q g : V →ₗ[K] V))‖ = 0) ∨
    ∃ (s : ℝ) (i : Fin Fl.len), ∀ g ∈ flagLevi (Q := Q) b wt,
      Real.log ‖LinearMap.det (wtBlock b wt w (specP Q g : V →ₗ[K] V))‖ =
        s * Real.log ‖LinearMap.det (wtBlock b wt ((i : ℤ) + 1) (specP Q g : V →ₗ[K] V))‖ := by
  classical
  rcases hs.wt_trichotomy w with h | h | ⟨i, hi | hi⟩
  · exact Or.inl fun g _ => by
      rw [wtBlock_eq_id_of_forall_ne h, LinearMap.det_id, norm_one, Real.log_one]
  · exact Or.inl fun g _ => by
      rw [wtBlock_eq_id_of_forall_ne (by subst h; exact hw rfl), LinearMap.det_id, norm_one,
        Real.log_one]
  · exact Or.inr ⟨1, i, fun g _ => by rw [one_mul, hi]⟩
  · refine Or.inr ⟨-1, i, fun g hg => ?_⟩
    have h := det_wtBlock_neg_mul hQ hs hg ((i : ℤ) + 1)
    rw [wtBlock_neg_wt, hi, neg_neg] at h
    rw [eq_inv_of_mul_eq_one_left h, norm_inv, Real.log_inv, neg_one_mul, hi]

end Weights

end GSpinGGP
