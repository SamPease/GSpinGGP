/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.LeviOpp

/-!
# Arthur's weight `v_M` depends on the presentation only through the weight spaces

A reduced Levi datum `L` presents its Levi subgroup `M` by bases with weights `(b_W, wt_W)`,
`(b_V, wt_V)`; `a_M` is written in the coordinates of the characters `char L c` (determinants on
the weight spaces of weights `1, …, len`, and the `GSpin`-norms).  This file shows that `v_M`
does not see the presentation beyond the family of weight spaces, up to relabelling the weights.

**Transport along a linear isomorphism of `a_M`.**  If `L.M = L'.M`, `A_M(F)` is the same and a
linear isomorphism `ψ : a_M^L ≃ a_M^{L'}` carries `H_M^L` to `H_M^{L'}` (exactly, not modulo
`a_G`), then `ψ` carries `a_G` (`aG_eq_map`), the lattice `proj_M^G(H_M(A_M(F)))`
(`latticeMG_eq_map`) and the points `H_P(g)` (`mkQ_hPar_eq`) of `L` to those of `L'`, so
`v_M` is the same for any two good subgroups with the same underlying `K` (`vM_eq_of_equiv`).
The inverse of `ψ` need not be given: linear maps both ways compatible with `H_M` are inverse to
each other because `H_M(A_M(F))` spans `a_M` (`aMEquivOfHM`).

**Same weight spaces up to relabelling** (`SameWtSpacesW`, `SameWtSpacesV`).  If the families
`w ↦ wtSpan b wt w` of `L` and `L'` have the same members (`Set.range`), for `W` and for `V` (this
covers reindexing and rescaling the bases, `L ↦ L.opp`, and permuting the weight spaces with
independent signs), then:
* the weight projections agree up to relabelling (`wtProj_eq_of_wtSpan_eq`), so `L.M = L'.M`
  (`M_eq_of_sameWtSpaces`);
* the weight-`0` spaces agree (`wtSpan_zero_eq_of_wtSpan_eq`: the other weight spaces are totally
  isotropic, a nonzero weight-`0` space is not), so `A_M(F)` agrees (`AMF_eq_of_sameWtSpaces`);
* every coordinate of `H_M^{L'}` is `0`, or `±` a coordinate of `H_M^{L}`
  (`exists_HM_coord_eq`; the sign `−` by determinant duality `det_wtBlock_neg_mul`), which gives
  the isomorphism `ψ` (`exists_aMEquiv_of_sameWtSpaces`);
* hence `v_M^{L'} = v_M^{L}` (`vM_eq_of_sameWtSpaces`).

A good `K` for `L` is good for `L'` (`goodKOfSameWtSpaces`).  Examples: `rebase` (reindexed and
rescaled bases, `sameWtSpaces_rebase`) and `L.opp` (`sameWtSpaces_opp`).

**Not proved here** (`sameWtSpaces_of_M_eq`, a `sorry` with a proof sketch, off the path of the
main theorem): two reduced data with the same Levi subgroup have the same weight spaces up to
relabelling.
-/

noncomputable section

open Module MeasureTheory

namespace GSpinGGP

/-! ## 1. Weight spaces and weight projections -/

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
theorem disjoint_wtSpan {u v : ℤ} (h : u ≠ v) : Disjoint (wtSpan b wt u) (wtSpan b wt v) := by
  rw [Submodule.disjoint_def]
  intro x hu hv
  have h1 := wtProj_apply_of_mem_wtSpan hu u
  have h2 := wtProj_apply_of_mem_wtSpan hv u
  rw [ite_eq_left rfl] at h1
  rw [ite_eq_right (Ne.symm h)] at h2
  rw [← h1, h2]

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

variable [Fintype ι] [Fintype ι']

theorem bform_eq_zero_of_mem_wtSpan (horth : ∀ i j, wt i + wt j ≠ 0 → bform Q (b i) (b j) = 0)
    {x y : V} {u v : ℤ} (hx : x ∈ wtSpan b wt u) (hy : y ∈ wtSpan b wt v) (h : u + v ≠ 0) :
    bform Q x y = 0 :=
  bform_eq_zero_of_isHomog_of_orth horth (isHomog_of_mem_wtSpan hx) (isHomog_of_mem_wtSpan hy) h

/-- A nonzero weight-`0` space is not a weight space of nonzero weight of another splitting: those
are totally isotropic, and `b` is nondegenerate on the weight-`0` space. -/
theorem eq_zero_of_wtSpan_zero_eq (hQ : IsNondeg Q)
    (horth : ∀ i j, wt i + wt j ≠ 0 → bform Q (b i) (b j) = 0)
    (horth' : ∀ i j, wt' i + wt' j ≠ 0 → bform Q (b' i) (b' j) = 0) {u' : ℤ}
    (hu : wtSpan b wt 0 = wtSpan b' wt' u') (hne : wtSpan b wt 0 ≠ ⊥) : u' = 0 := by
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

/-! ### Reindexing and rescaling a splitting -/

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

/-- **A reindexed and rescaled splitting is a splitting** of the same flag. -/
theorem IsFlagSplitting.reindexUnits {Fl : IsotropicFlag Q} (hs : IsFlagSplitting Fl b wt)
    (e : ι ≃ κ) (u : κ → Kˣ) : IsFlagSplitting Fl ((b.reindex e).unitsSMul u) (wt ∘ e.symm) where
  mem i := by
    rw [Basis.unitsSMul_apply, Basis.reindex_apply]
    exact Submodule.smul_mem _ _ (hs.mem _)
  repr_eq_zero w v hv i hi := by
    rw [Basis.repr_unitsSMul, Basis.repr_reindex_apply, hs.repr_eq_zero w v hv _ hi, smul_zero]
  orth i j h := by
    rw [Basis.unitsSMul_apply, Basis.unitsSMul_apply, Basis.reindex_apply, Basis.reindex_apply,
      Units.smul_def, Units.smul_def, LinearMap.map_smul₂, LinearMap.map_smul,
      hs.orth _ _ h, smul_zero, smul_zero]
  sum_wt := by
    rw [show (∑ i, (wt ∘ e.symm) i) = ∑ j, wt j from Equiv.sum_comp e.symm wt, hs.sum_wt]

end Rebase


/-! ## 2. Transport of `v_M` along an isomorphism of `a_M` -/

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] {d : GGPData F}

namespace ReducedLeviDatum

variable {L L' : d.ReducedLeviDatum}

/-- **Linear maps both ways compatible with `H_M` are inverse isomorphisms**: `H_M(A_M(F))` spans
`a_M` (`span_HMAMF_eq_top`). -/
def aMEquivOfHM (hM : L'.M = L.M) (Φ : L.aM →ₗ[ℝ] L'.aM)
    (Ψ : L'.aM →ₗ[ℝ] L.aM)
    (hΦ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = Φ (L.HM m))
    (hΨ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L.HM m = Ψ (L'.HM m')) :
    L.aM ≃ₗ[ℝ] L'.aM :=
  LinearEquiv.ofLinearMap Φ Ψ
    (LinearMap.ext_on L'.span_HMAMF_eq_top (by
      rintro _ ⟨⟨m', hm'⟩, rfl⟩
      let m : ↥L.M := ⟨m', hM.le m'.2⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [← hΨ m m' rfl, ← hΦ m m' rfl]))
    (LinearMap.ext_on L.span_HMAMF_eq_top (by
      rintro _ ⟨⟨m, hm⟩, rfl⟩
      let m' : ↥L'.M := ⟨m, hM.ge m.2⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [← hΦ m m' rfl, ← hΨ m m' rfl]))

@[simp] theorem aMEquivOfHM_apply (hM : L'.M = L.M)
    (Φ : L.aM →ₗ[ℝ] L'.aM) (Ψ : L'.aM →ₗ[ℝ] L.aM) (hΦ hΨ) (H : L.aM) :
    aMEquivOfHM hM Φ Ψ hΦ hΨ H = Φ H := rfl

variable (ψ : L.aM ≃ₗ[ℝ] L'.aM)

/-- **`a_G` is carried by `ψ`** (it is spanned by `H_M(A_G(F))`). -/
theorem aG_eq_map (hM : L'.M = L.M)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m)) :
    L'.aG = L.aG.map (ψ : L.aM →ₗ[ℝ] L'.aM) := by
  rw [ReducedLeviDatum.aG, ReducedLeviDatum.aG, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨⟨m', hm'⟩, rfl⟩
    exact ⟨_, ⟨⟨⟨m', hM.le m'.2⟩, hm'⟩, rfl⟩, (hψ _ m' rfl).symm⟩
  · rintro ⟨_, ⟨⟨m, hm⟩, rfl⟩, rfl⟩
    exact ⟨⟨⟨m, hM.ge m.2⟩, hm⟩, hψ m _ rfl⟩

/-- `ψ` on `a_M^G = a_M / a_G`. -/
def aMGEquiv (hM : L'.M = L.M)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m)) :
    L.aMG ≃L[ℝ] L'.aMG :=
  (Submodule.Quotient.equiv L.aG L'.aG ψ (aG_eq_map ψ hM hψ).symm).toContinuousLinearEquiv

theorem aMGEquiv_mkQ (hM : L'.M = L.M)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m)) (H : L.aM) :
    aMGEquiv ψ hM hψ (L.aG.mkQ H) = L'.aG.mkQ (ψ H) := rfl

theorem finrank_aMG_eq (hM : L'.M = L.M)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m)) :
    finrank ℝ L'.aMG = finrank ℝ L.aMG :=
  (aMGEquiv ψ hM hψ).toLinearEquiv.finrank_eq.symm

theorem mkQ_HM_eq (hM : L'.M = L.M)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m))
    (m : ↥L.M) (m' : ↥L'.M) (hmm : (m' : ↥d.G) = m) :
    L'.aG.mkQ (L'.HM m') = aMGEquiv ψ hM hψ (L.aG.mkQ (L.HM m)) := by
  rw [aMGEquiv_mkQ, hψ m m' hmm]

/-- **The lattice `proj_M^G(H_M(A_M(F)))` is carried by `ψ`.** -/
theorem latticeMG_eq_map (hM : L'.M = L.M) (hA : L'.AMF = L.AMF)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m)) :
    L'.latticeMG = L.latticeMG.map (aMGEquiv ψ hM hψ : L.aMG →+ L'.aMG) := by
  rw [ReducedLeviDatum.latticeMG, ReducedLeviDatum.latticeMG, AddMonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨⟨m', hm'⟩, rfl⟩
    exact ⟨_, ⟨⟨⟨m', hM.le m'.2⟩, hA ▸ hm'⟩, rfl⟩,
      (mkQ_HM_eq ψ hM hψ ⟨m', hM.le m'.2⟩ m' rfl).symm⟩
  · rintro ⟨_, ⟨⟨m, hm⟩, rfl⟩, rfl⟩
    exact ⟨⟨⟨m, hM.ge m.2⟩, hA.symm ▸ hm⟩, mkQ_HM_eq ψ hM hψ m ⟨m, hM.ge m.2⟩ rfl⟩

/-- **The points `H_P(g)` are carried by `ψ`**, for good subgroups `K`, `K'` of `L`, `L'` with the
same underlying subgroup and the same parabolic `P ∈ 𝒫(M)`. -/
theorem mkQ_hPar_eq (hM : L'.M = L.M)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m))
    (K : d.GoodK L.toFlagLeviDatum) (K' : d.GoodK L'.toFlagLeviDatum) (hK : K'.K = K.K)
    {P : Subgroup ↥d.G} (hP' : P ∈ d.parabolics L'.M) (hP : P ∈ d.parabolics L.M) (g : ↥d.G) :
    L'.aG.mkQ (L'.hPar K' ⟨P, hP'⟩ g) = aMGEquiv ψ hM hψ (L.aG.mkQ (L.hPar K ⟨P, hP⟩ g)) := by
  obtain ⟨FW, FV, hPeq, hL'⟩ := id hP'
  have hL : d.IsLevi FW FV L.M := hM ▸ hL'
  obtain ⟨p, hp, k, hk, rfl⟩ := K.mul_eq P hP g
  have hp' : p ∈ d.whittB FW FV := hPeq ▸ hp
  have hk' : k ∈ K'.K := hK ▸ hk
  rw [L'.hPar_eq K' ⟨P, hP'⟩ hPeq hL', L.hPar_eq K ⟨P, hP⟩ hPeq hL]
  have e3 := L'.hP_eq hL' K'.isOpen K'.isCompact (hPeq ▸ K'.mul_eq P hP') ⟨p, hp'⟩ hk'
  have e4 := L.hP_eq hL K.isOpen K.isCompact (hPeq ▸ K.mul_eq P hP) ⟨p, hp'⟩ hk
  rw [e3, e4]
  exact mkQ_HM_eq ψ hM hψ _ _ (IsLevi.coe_proj_congr hM hL' hL _)

/-- **`v_M` is carried by `ψ`**: `v_M^{L'}(g) = v_M^{L}(g)` for good subgroups with the same
underlying `K` (the hull and the lattice are carried by the linear isomorphism `aMGEquiv ψ`,
`Measure.hullVolume_map`). -/
theorem vM_eq_of_equiv (hM : L'.M = L.M) (hA : L'.AMF = L.AMF)
    (hψ : ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m → L'.HM m' = ψ (L.HM m))
    (K : d.GoodK L.toFlagLeviDatum) (K' : d.GoodK L'.toFlagLeviDatum) (hK : K'.K = K.K)
    (g : ↥d.G) : L'.vM K' g = L.vM K g := by
  have hS :
      (Set.range fun P : ↥(d.parabolics L'.M) => L'.aG.mkQ (L'.hPar K' P g)) =
      aMGEquiv ψ hM hψ '' Set.range fun P : ↥(d.parabolics L.M) => L.aG.mkQ (L.hPar K P g) := by
    ext v
    constructor
    · rintro ⟨⟨P, hP'⟩, rfl⟩
      have hP : P ∈ d.parabolics L.M := hM ▸ hP'
      exact ⟨_, ⟨⟨P, hP⟩, rfl⟩, (mkQ_hPar_eq ψ hM hψ K K' hK hP' hP g).symm⟩
    · rintro ⟨_, ⟨⟨P, hP⟩, rfl⟩, rfl⟩
      have hP' : P ∈ d.parabolics L'.M := hM.symm ▸ hP
      exact ⟨⟨P, hP'⟩, mkQ_hPar_eq ψ hM hψ K K' hK hP' hP g⟩
  obtain ⟨D, hD, -⟩ := L'.exists_isAddFundamentalDomain_latticeHaar_eq_one
  have hcount : Countable ↥(L'.latticeMG.toIntSubmodule) := by
    obtain ⟨h1, h2⟩ := L'.latticeMG_isLattice
    have : IsZLattice ℝ L'.latticeMG.toIntSubmodule := ⟨h2⟩
    infer_instance
  simp only [ReducedLeviDatum.vM]
  rw [hS]
  have : Countable ↥(L.latticeMG.map (aMGEquiv ψ hM hψ : L.aMG →+ L'.aMG)) := by
    rw [← latticeMG_eq_map ψ hM hA hψ]; exact hcount
  rw [latticeMG_eq_map ψ hM hA hψ] at hD
  rw [latticeMG_eq_map ψ hM hA hψ]
  exact Measure.hullVolume_map (aMGEquiv ψ hM hψ) hD _

/-! ## 3. Same weight spaces up to relabelling -/

variable (L L')

/-- The family of weight spaces of `W` of `L'` has the same members as that of `L`. -/
def SameWtSpacesW : Prop :=
  Set.range (wtSpan L'.bW L'.wtW) = Set.range (wtSpan L.bW L.wtW)

/-- The family of weight spaces of `V` of `L'` has the same members as that of `L`. -/
def SameWtSpacesV : Prop :=
  Set.range (wtSpan L'.bV L'.wtV) = Set.range (wtSpan L.bV L.wtV)

variable {L L'}

theorem SameWtSpacesW.exists (h : SameWtSpacesW L L') (u' : ℤ) :
    ∃ u, wtSpan L'.bW L'.wtW u' = wtSpan L.bW L.wtW u := by
  obtain ⟨u, hu⟩ : wtSpan L'.bW L'.wtW u' ∈ Set.range (wtSpan L.bW L.wtW) := h ▸ ⟨u', rfl⟩
  exact ⟨u, hu.symm⟩

theorem SameWtSpacesW.exists' (h : SameWtSpacesW L L') (u : ℤ) :
    ∃ u', wtSpan L.bW L.wtW u = wtSpan L'.bW L'.wtW u' := by
  obtain ⟨u', hu'⟩ : wtSpan L.bW L.wtW u ∈ Set.range (wtSpan L'.bW L'.wtW) := h.symm ▸ ⟨u, rfl⟩
  exact ⟨u', hu'.symm⟩

theorem SameWtSpacesV.exists (h : SameWtSpacesV L L') (u' : ℤ) :
    ∃ u, wtSpan L'.bV L'.wtV u' = wtSpan L.bV L.wtV u := by
  obtain ⟨u, hu⟩ : wtSpan L'.bV L'.wtV u' ∈ Set.range (wtSpan L.bV L.wtV) := h ▸ ⟨u', rfl⟩
  exact ⟨u, hu.symm⟩

theorem SameWtSpacesV.exists' (h : SameWtSpacesV L L') (u : ℤ) :
    ∃ u', wtSpan L.bV L.wtV u = wtSpan L'.bV L'.wtV u' := by
  obtain ⟨u', hu'⟩ : wtSpan L.bV L.wtV u ∈ Set.range (wtSpan L'.bV L'.wtV) := h.symm ▸ ⟨u, rfl⟩
  exact ⟨u', hu'.symm⟩

theorem SameWtSpacesW.symm (h : SameWtSpacesW L L') : SameWtSpacesW L' L := Eq.symm h

theorem SameWtSpacesV.symm (h : SameWtSpacesV L L') : SameWtSpacesV L' L := Eq.symm h

/-- **The Levi subgroup is the same.** -/
theorem M_eq_of_sameWtSpaces (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L') :
    L'.M = L.M := by
  change d.flagLeviG L'.bW L'.wtW L'.bV L'.wtV = d.flagLeviG L.bW L.wtW L.bV L.wtV
  unfold GGPData.flagLeviG
  rw [flagLevi_eq_of_wtSpan_eq hW.exists' hW.exists, flagLevi_eq_of_wtSpan_eq hV.exists' hV.exists]

theorem wtSpanW_zero_eq (hW : SameWtSpacesW L L') :
    wtSpan L'.bW L'.wtW 0 = wtSpan L.bW L.wtW 0 :=
  wtSpan_zero_eq_of_wtSpan_eq d.nondeg L.hsW.orth L'.hsW.orth hW.exists' hW.exists

theorem wtSpanV_zero_eq (hV : SameWtSpacesV L L') :
    wtSpan L'.bV L'.wtV 0 = wtSpan L.bV L.wtV 0 :=
  wtSpan_zero_eq_of_wtSpan_eq d.nondeg_QV L.hsV.orth L'.hsV.orth hV.exists' hV.exists

/-- **`A_M(F)` is the same.** -/
theorem AMF_eq_of_sameWtSpaces (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L') :
    L'.AMF = L.AMF := by
  have eW : wtScalar d.QW L'.bW L'.wtW = wtScalar d.QW L.bW L.wtW :=
    le_antisymm (wtScalar_le_of_wtSpan_eq hW.exists' (wtSpanW_zero_eq hW).symm)
      (wtScalar_le_of_wtSpan_eq hW.exists (wtSpanW_zero_eq hW))
  have eV : wtScalar d.QV L'.bV L'.wtV = wtScalar d.QV L.bV L.wtV :=
    le_antisymm (wtScalar_le_of_wtSpan_eq hV.exists' (wtSpanV_zero_eq hV).symm)
      (wtScalar_le_of_wtSpan_eq hV.exists (wtSpanV_zero_eq hV))
  ext g
  rw [L'.mem_AMF_iff, L.mem_AMF_iff, eW, eV]

/-- A weight `w` of a flag splitting either does not occur, or is `±(i + 1)` for some
`i < len`, or is `0`. -/
theorem _root_.GSpinGGP.IsFlagSplitting.wt_trichotomy {K V : Type*} [Field K]
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
theorem _root_.GSpinGGP.IsFlagSplitting.log_det_wtBlock_cases {K V : Type*}
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
      rw [wtBlock_eq_id_of_forall_ne (by subst h; exact hw rfl), LinearMap.det_id, norm_one, Real.log_one]
  · exact Or.inr ⟨1, i, fun g _ => by rw [one_mul, hi]⟩
  · refine Or.inr ⟨-1, i, fun g hg => ?_⟩
    have h := det_wtBlock_neg_mul hQ hs hg ((i : ℤ) + 1)
    rw [wtBlock_neg_wt, hi, neg_neg] at h
    rw [eq_inv_of_mul_eq_one_left h, norm_inv, Real.log_inv, neg_one_mul, hi]

/-- **Each coordinate of `H_M^{L'}` is `s` times a coordinate of `H_M^{L}`** (`s ∈ {0, ±1}`), when
the weight spaces are the same up to relabelling. -/
theorem exists_HM_coord_eq (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L') (c' : L'.Coord) :
    ∃ (s : ℝ) (c : L.Coord), ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m →
      L'.HM m' c' = s * L.HM m c := by
  rcases c' with (i' | _) | (i' | _)
  · obtain ⟨w, hw⟩ := hW.exists ((i' : ℤ) + 1)
    have hw0 : w = 0 → ∀ j, L.wtW j ≠ 0 := by
      rintro rfl j hj
      have h1 : L.bW j ∈ wtSpan L'.bW L'.wtW ((i' : ℤ) + 1) := by
        rw [hw, ← hj]; exact basis_mem_wtSpan j
      have h2 : L.bW j ∈ wtSpan L'.bW L'.wtW 0 := by
        rw [wtSpanW_zero_eq hW, ← hj]; exact basis_mem_wtSpan j
      exact L.bW.ne_zero j (Submodule.disjoint_def.1 (disjoint_wtSpan (by omega)) _ h1 h2)
    rcases L.hsW.log_det_wtBlock_cases d.nondeg w hw0 with h0 | ⟨s, i, h⟩
    · refine ⟨0, Sum.inl (Sum.inr ()), fun m m' hmm => ?_⟩
      change Real.log ‖LinearMap.det (wtBlock L'.bW L'.wtW ((i' : ℤ) + 1)
        (specP d.QW (d.fst (m' : ↥d.G)) : _ →ₗ[F] _))‖ = _
      rw [wtBlock_eq_of_wtSpan_eq hW.exists' hw, hmm, h0 _ m.2.1, zero_mul]
    · refine ⟨s, Sum.inl (Sum.inl i), fun m m' hmm => ?_⟩
      change Real.log ‖LinearMap.det (wtBlock L'.bW L'.wtW ((i' : ℤ) + 1)
        (specP d.QW (d.fst (m' : ↥d.G)) : _ →ₗ[F] _))‖ = s * Real.log ‖LinearMap.det
          (wtBlock L.bW L.wtW ((i : ℤ) + 1) (specP d.QW (d.fst (m : ↥d.G)) : _ →ₗ[F] _))‖
      rw [wtBlock_eq_of_wtSpan_eq hW.exists' hw, hmm, h _ m.2.1]
  · refine ⟨1, Sum.inl (Sum.inr ()), fun m m' hmm => ?_⟩
    change Real.log ‖((detChar d.QW (d.fst (m' : ↥d.G)) : Fˣ) : F)‖ =
      1 * Real.log ‖((detChar d.QW (d.fst (m : ↥d.G)) : Fˣ) : F)‖
    rw [hmm, one_mul]
  · obtain ⟨w, hw⟩ := hV.exists ((i' : ℤ) + 1)
    have hw0 : w = 0 → ∀ j, L.wtV j ≠ 0 := by
      rintro rfl j hj
      have h1 : L.bV j ∈ wtSpan L'.bV L'.wtV ((i' : ℤ) + 1) := by
        rw [hw, ← hj]; exact basis_mem_wtSpan j
      have h2 : L.bV j ∈ wtSpan L'.bV L'.wtV 0 := by
        rw [wtSpanV_zero_eq hV, ← hj]; exact basis_mem_wtSpan j
      exact L.bV.ne_zero j (Submodule.disjoint_def.1 (disjoint_wtSpan (by omega)) _ h1 h2)
    rcases L.hsV.log_det_wtBlock_cases d.nondeg_QV w hw0 with h0 | ⟨s, i, h⟩
    · refine ⟨0, Sum.inl (Sum.inr ()), fun m m' hmm => ?_⟩
      change Real.log ‖LinearMap.det (wtBlock L'.bV L'.wtV ((i' : ℤ) + 1)
        (specP d.QV (d.snd (m' : ↥d.G)) : _ →ₗ[F] _))‖ = _
      rw [wtBlock_eq_of_wtSpan_eq hV.exists' hw, hmm, h0 _ m.2.2, zero_mul]
    · refine ⟨s, Sum.inr (Sum.inl i), fun m m' hmm => ?_⟩
      change Real.log ‖LinearMap.det (wtBlock L'.bV L'.wtV ((i' : ℤ) + 1)
        (specP d.QV (d.snd (m' : ↥d.G)) : _ →ₗ[F] _))‖ = s * Real.log ‖LinearMap.det
          (wtBlock L.bV L.wtV ((i : ℤ) + 1) (specP d.QV (d.snd (m : ↥d.G)) : _ →ₗ[F] _))‖
      rw [wtBlock_eq_of_wtSpan_eq hV.exists' hw, hmm, h _ m.2.2]
  · refine ⟨1, Sum.inr (Sum.inr ()), fun m m' hmm => ?_⟩
    change Real.log ‖((detChar d.QV (d.snd (m' : ↥d.G)) : Fˣ) : F)‖ =
      1 * Real.log ‖((detChar d.QV (d.snd (m : ↥d.G)) : Fˣ) : F)‖
    rw [hmm, one_mul]

/-- A linear map `a_M^L → a_M^{L'}` carrying `H_M^L` to `H_M^{L'}`, for the same weight spaces up to
relabelling (`exists_HM_coord_eq`). -/
theorem exists_linearMap_HM (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L') :
    ∃ Φ : L.aM →ₗ[ℝ] L'.aM, ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m →
      L'.HM m' = Φ (L.HM m) := by
  choose s c hsc using exists_HM_coord_eq hW hV
  refine ⟨LinearMap.pi fun c' => s c' • LinearMap.proj (c c'), fun m m' hmm => ?_⟩
  funext c'
  rw [hsc c' m m' hmm]
  simp [smul_eq_mul]

/-- **The isomorphism `a_M^L ≃ a_M^{L'}` carrying `H_M`**, for the same weight spaces up to
relabelling. -/
theorem exists_aMEquiv_of_sameWtSpaces (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L') :
    ∃ ψ : L.aM ≃ₗ[ℝ] L'.aM, ∀ (m : ↥L.M) (m' : ↥L'.M), (m' : ↥d.G) = m →
      L'.HM m' = ψ (L.HM m) := by
  have hM := M_eq_of_sameWtSpaces hW hV
  obtain ⟨Φ, hΦ⟩ := exists_linearMap_HM hW hV
  obtain ⟨Ψ, hΨ⟩ := exists_linearMap_HM hW.symm hV.symm
  exact ⟨aMEquivOfHM hM Φ Ψ hΦ (fun m m' hmm => hΨ m' m hmm.symm), fun m m' hmm => hΦ m m' hmm⟩

/-- **`v_M` depends on the presentation only through the weight spaces**: for reduced data `L`,
`L'` whose families of weight spaces have the same members (for `W` and for `V`), and good
subgroups `K`, `K'` with the same underlying subgroup, `v_M^{L'}(g) = v_M^{L}(g)`. -/
theorem vM_eq_of_sameWtSpaces (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L')
    (K : d.GoodK L.toFlagLeviDatum) (K' : d.GoodK L'.toFlagLeviDatum) (hK : K'.K = K.K)
    (g : ↥d.G) : L'.vM K' g = L.vM K g := by
  obtain ⟨ψ, hψ⟩ := exists_aMEquiv_of_sameWtSpaces hW hV
  exact vM_eq_of_equiv ψ (M_eq_of_sameWtSpaces hW hV) (AMF_eq_of_sameWtSpaces hW hV) hψ K K' hK g

/-! ## 4. Good subgroups, rebased data, the opposite datum -/

/-- Good position only sees the weight spaces. -/
theorem _root_.GSpinGGP.GGPData.StabilizesSplitLattice.of_wtSpan_eq {V ι ι' : Type*}
    [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {b : Basis ι F V} {wt : ι → ℤ}
    {b' : Basis ι' F V} {wt' : ι' → ℤ} {S : Set (GSpin Q)}
    (h : ∀ w, ∃ w', wtSpan b wt w = wtSpan b' wt' w') (hS : StabilizesSplitLattice Q b wt S) :
    StabilizesSplitLattice Q b' wt' S := by
  obtain ⟨κ, hκ, e, he, hm⟩ := hS
  refine ⟨κ, hκ, e, fun i => ?_, hm⟩
  obtain ⟨w, hw⟩ := he i
  obtain ⟨w', hw'⟩ := h w
  exact ⟨w', hw' ▸ hw⟩

/-- **A good `K` for `L` is good for `L'`** with the same weight spaces up to relabelling (same
subgroup `K`). -/
def goodKOfSameWtSpaces (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L')
    (K : d.GoodK L.toFlagLeviDatum) : d.GoodK L'.toFlagLeviDatum where
  K := K.K
  isOpen := K.isOpen
  isCompact := K.isCompact
  mul_eq P hP := K.mul_eq P (M_eq_of_sameWtSpaces hW hV ▸ hP)
  goodPositionW := K.goodPositionW.of_wtSpan_eq hW.exists'
  goodPositionV := K.goodPositionV.of_wtSpan_eq hV.exists'

@[simp] theorem goodKOfSameWtSpaces_K (hW : SameWtSpacesW L L') (hV : SameWtSpacesV L L')
    (K : d.GoodK L.toFlagLeviDatum) : (goodKOfSameWtSpaces hW hV K).K = K.K := rfl

variable (L) in
/-- **The rebased datum**: the same flags, with the splitting bases reindexed by `eW`, `eV` and
rescaled by the units `uW`, `uV` (`IsFlagSplitting.reindexUnits`); the weights are carried along. -/
def rebase {κW κV : Type} [Fintype κW] [Fintype κV] (eW : L.ιW ≃ κW) (uW : κW → Fˣ)
    (eV : L.ιV ≃ κV) (uV : κV → Fˣ) : d.ReducedLeviDatum where
  FW := L.FW
  FV := L.FV
  ιW := κW
  ιV := κV
  bW := (L.bW.reindex eW).unitsSMul uW
  wtW := L.wtW ∘ eW.symm
  bV := (L.bV.reindex eV).unitsSMul uV
  wtV := L.wtV ∘ eV.symm
  hsW := L.hsW.reindexUnits eW uW
  hsV := L.hsV.reindexUnits eV uV
  reducedW := by rw [wtSpan_reindexUnits]; exact L.reducedW
  reducedV := by rw [wtSpan_reindexUnits]; exact L.reducedV

variable (L) in
theorem sameWtSpaces_rebase {κW κV : Type} [Fintype κW] [Fintype κV] (eW : L.ιW ≃ κW)
    (uW : κW → Fˣ) (eV : L.ιV ≃ κV) (uV : κV → Fˣ) :
    SameWtSpacesW L (L.rebase eW uW eV uV) ∧ SameWtSpacesV L (L.rebase eW uW eV uV) :=
  ⟨congrArg Set.range (funext fun w => wtSpan_reindexUnits (b := L.bW) eW uW w),
    congrArg Set.range (funext fun w => wtSpan_reindexUnits (b := L.bV) eV uV w)⟩

variable (L) in
/-- `L.opp` has the same weight spaces as `L`, relabelled by `w ↦ −w` (`wtSpan_neg_wt`). -/
theorem sameWtSpaces_opp : SameWtSpacesW L L.opp ∧ SameWtSpacesV L L.opp := by
  refine ⟨?_, ?_⟩
  · change Set.range (wtSpan L.bW (-L.wtW)) = Set.range (wtSpan L.bW L.wtW)
    rw [show wtSpan L.bW (-L.wtW) = wtSpan L.bW L.wtW ∘ Neg.neg from
      funext fun w => wtSpan_neg_wt w]
    exact neg_surjective.range_comp _
  · change Set.range (wtSpan L.bV (-L.wtV)) = Set.range (wtSpan L.bV L.wtV)
    rw [show wtSpan L.bV (-L.wtV) = wtSpan L.bV L.wtV ∘ Neg.neg from
      funext fun w => wtSpan_neg_wt w]
    exact neg_surjective.range_comp _

/-- **The weight spaces are intrinsic to `M`** (`sorry`): two reduced data with the same Levi
subgroup have the same weight spaces up to relabelling.  Not on the path of the main theorem.
Sketch (`G = GSpin(W) × GSpin(V)`, so `M` determines `flagLevi` of each factor; argue for `V`):
1. *Compatibility.*  For `w ≥ 1` the lift `T` of the one-weight cocharacter
   (`IsFlagSplitting.exists_oneWt_lift`, `‖τ‖ < 1`) lies in `M = M'`, so `P(T)` commutes with every
   `wtProj` of `L'`; `P(T)` is diagonal in `b` with eigenvalues `τ` on `V_w`, `τ⁻¹` on `V_{−w}`, `1`
   elsewhere, and `τ ≠ τ⁻¹`, `τ ≠ 1`.  So each `wtProj' u'` preserves the `τ^{±1}`-eigenspaces
   `V_{±w}` and the common `1`-eigenspace `V_0`: every `V_u = ⊕_{u'} (V_u ∩ V'_{u'})`, and
   symmetrically.
2. *`u ≠ 0`: one piece.*  If `x ∈ V_u ∩ V'_{u'}`, `x' ∈ V_u ∩ V'_{v'}` are nonzero with
   `u' ≠ v'`, choose `e ∈ V_{−u}` with `b(x, e) = 0`, `b(x', e) = 1` (`V_u × V_{−u}` is a perfect
   pairing).  The Eichler transformation `v ↦ v + b(v, e) x − b(v, x) e` preserves every `V_w`,
   lies in `SO(V)` with determinant `1` and lifts to `GSpin` (`exists_specP_eq_of_det_eq_one`),
   so it lies in `M = M'`; it sends `x'` to `x' + x ∉ V'_{v'}`, a contradiction.
3. *`u = 0`: reducedness.*  If `0 ≠ x ∈ V_0 ∩ V'_{u'}` with `u' ≠ 0`, `x` is isotropic, so
   `V_0` (nondegenerate, not a hyperbolic plane) has dimension `≥ 3`; take `e ∈ V_0` with
   `b(x, e) = 1`, `Q(e) = 0`, and `f ∈ V_0` anisotropic orthogonal to `x`, `e`.  The Eichler
   transformation `v ↦ v + b(v, e) f − b(v, f) e − Q(f) b(v, e) e` acts on `V_0` only, so lies in
   `M = M'`, and sends `x` to `x' = x + f − Q(f) e` with `b(x, x') = −Q(f) ≠ 0`; but `V'_{u'}` is
   totally isotropic and contains `x'`, a contradiction.
From 1–3 each nonzero `V_u` lies in one `V'_{u'}` and each nonzero `V'_{u'}` in one `V_v`, hence
`V_u = V'_{u'}` (`disjoint_wtSpan`). -/
theorem sameWtSpaces_of_M_eq (hM : L'.M = L.M) : SameWtSpacesW L L' ∧ SameWtSpacesV L L' := by
  sorry

end ReducedLeviDatum

end GGPData

end GSpinGGP
