/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.LeviSubgroup
import GSpinGGP.Foundations.ValueGroup

/-!
# `𝒜_{M,F} = H_M(M(F))` is a lattice of full rank in `a_M`

For a reduced flag Levi datum `L` with Levi subgroup `M = L.M` of `G = GSpin(W) × GSpin(V)`:

* **discreteness**: every coordinate `log ‖χ_c(m)‖` of `H_M(m)` lies in `ℤ ℓ` for one `ℓ > 0`
  (`exists_HM_mem_zmultiples`; the value group of `F` is cyclic, `exists_log_norm_mem_zmultiples`);
* **full rank**: the `H_M` of the split centre `A_M(F)` of `M` (`AMF`) already span `a_M`
  (`span_HMAMF_eq_top`).  For the `GL`-coordinate of weight `w = 1, …, len` of a flag, the lift
  to `GSpin` of the element of `SO` acting by `τ` on the weight-`w` space, by `τ⁻¹` on the
  weight-`(−w)` space and trivially elsewhere (`IsFlagSplitting.exists_oneWt_lift`; its
  determinant is `1` because the two spaces have the same dimension, `card_wt_neg`) has
  `H_M = n_w log ‖τ‖ e_w + x e_{GSpin}` (`exists_HM_torusW`, `exists_HM_torusV`); the central
  scalars give the `GSpin`-coordinates (`HM_scalarW`, `HM_scalarV`).

These are the facts behind Beuzart-Plessis, Astérisque 418, §1.1 (p. 12): `𝒜_{M,F}` is a lattice
in `a_M` and `i a*_{M,F} = i a*_M / i 𝒜^∨_{M,F}` a compact torus; and behind Waldspurger,
Compos. Math. 146 (2010), §1.2 (the projection of `H_M(A_M(F))` to `a_M^G` is a lattice).

Also: `wtScalar` is closed and normalized by the flag Levi subgroup (`isClosed_wtScalar`,
`mul_mul_inv_mem_wtScalar`), so `A_M(F)` is a closed subgroup of `M(F)` normalized by `M(F)`
(`AMF_le_M`, `isClosed_AMF`, `conj_mem_AMF`), and `H_M` is invariant under `M(F)`-conjugation
(`HM_conj`).
-/

noncomputable section

open Module

namespace GSpinGGP

/-! ## 1. One-weight cocharacters -/

section OneWeight

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} {F : IsotropicFlag Q}
variable {ι : Type*} [Fintype ι] {b : Basis ι K V} {wt : ι → ℤ}

/-- **Opposite weight spaces have the same dimension** (one inequality): a vector in the span of
the weight-`c` basis vectors that is orthogonal to all weight-`(−c)` basis vectors is `0`
(`IsFlagSplitting.repr_eq_zero_of_bform`). -/
theorem IsFlagSplitting.card_wt_le_card_wt_neg (hQ : IsNondeg Q) (hs : IsFlagSplitting F b wt)
    (c : ℤ) : Fintype.card {i // wt i = c} ≤ Fintype.card {i // wt i = -c} := by
  classical
  let φ : ({i // wt i = c} → K) →ₗ[K] ({j // wt j = -c} → K) :=
    { toFun := fun x j => bform Q (b j) (∑ i, x i • b i)
      map_add' := fun x y => by
        funext j; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a x => by
        funext j; simp [Finset.mul_sum, mul_assoc] }
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    funext i
    have h := hs.repr_eq_zero_of_bform hQ (v := ∑ i, x i • b i) (c := c)
      (fun k hk => congrFun hx ⟨k, hk⟩) i.2
    simpa [map_sum, Finsupp.single_apply, Subtype.val_inj] using h
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fintype_fun_eq_card] using this

/-- **Opposite weight spaces have the same dimension.** -/
theorem IsFlagSplitting.card_wt_neg (hQ : IsNondeg Q) (hs : IsFlagSplitting F b wt) (c : ℤ) :
    Fintype.card {i // wt i = -c} = Fintype.card {i // wt i = c} := by
  refine le_antisymm ?_ (hs.card_wt_le_card_wt_neg hQ c)
  simpa using hs.card_wt_le_card_wt_neg hQ (-c)

/-- **Every basis vector pairs with one of opposite weight**: `b(bⱼ, bₖ) ≠ 0` for some `k` with
`wtₖ = −wtⱼ` (`b` is nondegenerate and `b(bⱼ, bₖ) = 0` unless `wtⱼ + wtₖ = 0`). -/
theorem IsFlagSplitting.exists_bform_ne (hQ : IsNondeg Q) (hs : IsFlagSplitting F b wt) (j : ι) :
    ∃ k, wt k = -wt j ∧ bform Q (b j) (b k) ≠ 0 := by
  by_contra hne
  push Not at hne
  refine b.ne_zero j (hQ.1 (b j) fun y => ?_)
  rw [← b.sum_repr y, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_smul, smul_eq_mul]
  by_cases hk : wt k = -wt j
  · rw [hne k hk, mul_zero]
  · rw [hs.orth j k (fun h => hk (by omega)), mul_zero]

/-- **Opposite weights have inverse scalars**: if `P(g) bⱼ = t(wtⱼ) bⱼ` for all `j`, then
`t(w) t(−w) = 1` for every weight `w` of the splitting (`P(g)` preserves `b`). -/
theorem IsFlagSplitting.mul_neg_eq_one (hQ : IsNondeg Q) (hs : IsFlagSplitting F b wt)
    {g : GSpin Q} {t : ℤ → K} (ht : ∀ j, specP Q g (b j) = t (wt j) • b j) (j : ι) :
    t (wt j) * t (-wt j) = 1 := by
  obtain ⟨k, hk, hne⟩ := hs.exists_bform_ne hQ j
  have h := bform_specP g (b j) (b k)
  simp only [ht, hk, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  exact mul_right_cancel₀ hne (by linear_combination h)

/-- The weights `1` on `w`, `−1` on `−w`, `0` elsewhere. -/
def oneWt (w v : ℤ) : ℤ := (if v = w then 1 else 0) - (if v = -w then 1 else 0)

theorem oneWt_neg {w : ℤ} (v : ℤ) : oneWt w (-v) = -oneWt w v := by
  unfold oneWt
  split_ifs <;> omega

theorem oneWt_zero {w : ℤ} (hw : w ≠ 0) : oneWt w 0 = 0 := by
  simp [oneWt, eq_comm, hw]

theorem oneWt_of_pos {w v : ℤ} (hw : 0 < w) (hv : 0 < v) : oneWt w v = if v = w then 1 else 0 := by
  simp [oneWt, show v ≠ -w by omega]

/-- **The one-weight cocharacter lifts to `GSpin(V)`**: for `τ ≠ 0` there is
`T ∈ GSpin(V)` with `P(T) bᵢ = τ^{oneWt w wtᵢ} bᵢ` (`τ` on the weight-`w` space, `τ⁻¹` on the
weight-`(−w)` space, `1` elsewhere). -/
theorem IsFlagSplitting.exists_oneWt_lift [FiniteDimensional K V] (hQ : IsNondeg Q)
    (hs : IsFlagSplitting F b wt) (w : ℤ) {τ : K} (hτ : τ ≠ 0) :
    ∃ T : GSpin Q, ∀ i, specP Q T (b i) = τ ^ oneWt w (wt i) • b i := by
  classical
  set wt' : ι → ℤ := fun i => oneWt w (wt i)
  have horth : ∀ i j, wt' i + wt' j ≠ 0 → bform Q (b i) (b j) = 0 := fun i j h =>
    hs.orth i j fun h' => h (by
      simp only [wt', show wt j = -wt i by omega, oneWt_neg, add_neg_cancel])
  have hsum : ∑ i, wt' i = 0 := by
    have hc := hs.card_wt_neg hQ w
    rw [Fintype.card_subtype, Fintype.card_subtype] at hc
    simp only [wt', oneWt, Finset.sum_sub_distrib, Finset.sum_boole, hc, sub_self]
  exact exists_cochar_lift_of_orth (wt := wt') hQ horth hsum hτ

omit [Invertible (2 : K)] in
/-- **The determinant on a weight space of a diagonal map**: if `A bⱼ = sⱼ bⱼ`, then
`det(A|_{V_w}) = ∏_{wtⱼ = w} sⱼ`. -/
theorem det_wtBlock_of_diag {A : V →ₗ[K] V} {s : ι → K} (hA : ∀ j, A (b j) = s j • b j)
    (w : ℤ) : LinearMap.det (wtBlock b wt w A) = ∏ j, if wt j = w then s j else 1 := by
  classical
  have hdiag : LinearMap.toMatrix b b (wtBlock b wt w A) =
      Matrix.diagonal fun j => if wt j = w then s j else 1 := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
    simp only [wtBlock, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, hA, map_smul, wtProj_basis]
    rcases eq_or_ne i j with rfl | hij
    · by_cases hj : wt i = w <;> simp [hj, b.repr_self]
    · by_cases hj : wt j = w <;> simp [hj, hij, b.repr_self]
  rw [← LinearMap.det_toMatrix b, hdiag, Matrix.det_diagonal]

end OneWeight

/-! ## 1a. The split centre `wtScalar` of a flag Levi subgroup -/

section WtScalar

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V}
variable {ι : Type*} [Fintype ι] {b : Basis ι K V} {wt : ι → ℤ}

/-- An element of `wtScalar` acts on every homogeneous vector of weight `w` by `t w`. -/
theorem specP_apply_of_isHomog {a : GSpin Q} {t : ℤ → K}
    (ht : ∀ j, specP Q a (b j) = t (wt j) • b j) {v : V} {w : ℤ} (hv : IsHomog b wt v w) :
    specP Q a v = t w • v := by
  conv_lhs => rw [← b.sum_repr v]
  conv_rhs => rw [← b.sum_repr v]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ht]
  by_cases h : wt i = w
  · rw [h, smul_comm]
  · rw [hv i h, zero_smul, zero_smul, smul_zero]

/-- **`wtScalar` is normalized by the Levi subgroup** (with the same scalars): `M` preserves the
weight spaces, on which `a` acts by scalars. -/
theorem mul_mul_inv_mem_wtScalar {g a : GSpin Q} (hg : g ∈ flagLevi (Q := Q) b wt)
    (ha : a ∈ wtScalar Q b wt) : g * a * g⁻¹ ∈ wtScalar Q b wt := by
  obtain ⟨t, ht0, ht⟩ := ha
  refine ⟨t, ht0, fun j => ?_⟩
  have hh : IsHomog b wt (specP Q g⁻¹ (b j)) (wt j) :=
    mem_flagLevi_iff.1 ((flagLevi (Q := Q) b wt).inv_mem hg) j
  rw [specP_mul_apply, specP_mul_apply, specP_apply_of_isHomog ht hh, map_smul,
    specP_inv_apply_apply]

/-- `wtScalar` by closed conditions: `P(g)` fixes the weight-`0` basis vectors, preserves each line
`K bⱼ`, and each line `K (bᵢ + bⱼ)` with `bᵢ`, `bⱼ` of the same weight. -/
theorem wtScalar_eq_iInter :
    (wtScalar Q b wt : Set (GSpin Q)) =
      (⋂ j, {g | wt j = 0 → specP Q g (b j) - b j ∈ (⊥ : Submodule K V)}) ∩
      (⋂ j, {g | specP Q g (b j) - 0 ∈ K ∙ b j}) ∩
      ⋂ i, ⋂ j, {g | wt i = wt j → specP Q g (b i + b j) - 0 ∈ K ∙ (b i + b j)} := by
  classical
  ext g
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe,
    Submodule.mem_bot, sub_eq_zero, sub_zero, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, ht0, ht⟩
    refine ⟨⟨fun j hj => by rw [ht, hj, ht0, one_smul], fun j => ⟨t (wt j), (ht j).symm⟩⟩,
      fun i j hij => ⟨t (wt j), ?_⟩⟩
    rw [map_add, ht, ht, hij, smul_add]
  · rintro ⟨⟨h0, h1⟩, h2⟩
    -- the coefficient `s j` of `P(g) bⱼ` on `bⱼ`
    set s : ι → K := fun j => (h1 j).choose
    have hs : ∀ j, specP Q g (b j) = s j • b j := fun j => (h1 j).choose_spec.symm
    have hsame : ∀ i j, wt i = wt j → s i = s j := by
      intro i j hij
      by_cases hne : i = j
      · rw [hne]
      obtain ⟨c, hc⟩ := h2 i j hij
      rw [map_add, hs, hs, smul_add] at hc
      have hi := congrArg (fun v => b.repr v i) hc
      have hj := congrArg (fun v => b.repr v j) hc
      simp [b.repr_self, hne, Ne.symm hne] at hi hj
      rw [← hi, ← hj]
    refine ⟨fun w => if w = 0 then 1 else if h : ∃ j, wt j = w then s h.choose else 1,
      by simp, fun j => ?_⟩
    by_cases hw : wt j = 0
    · simp only [hw, ite_true, one_smul]; exact h0 j hw
    · have hex : ∃ i, wt i = wt j := ⟨j, rfl⟩
      simp only [hw, ite_false, dite_eq_left_of_eq_true (eq_true hex)]
      rw [hs, hsame _ _ hex.choose_spec]

/-- **`wtScalar` is closed.** -/
theorem isClosed_wtScalar [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    [Module.Finite K V] : IsClosed (wtScalar Q b wt : Set (GSpin Q)) := by
  rw [wtScalar_eq_iInter]
  refine ((isClosed_iInter fun j => ?_).inter (isClosed_iInter fun j =>
    isClosed_setOf_specP_sub_mem _ _ _)).inter
    (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
  · by_cases hj : wt j = 0
    · simpa only [hj, true_implies] using isClosed_setOf_specP_sub_mem (Q := Q) (b j) (b j) ⊥
    · simp only [hj, false_implies, Set.ofPred_true, isClosed_univ]
  · by_cases hij : wt i = wt j
    · simpa only [hij, true_implies] using
        isClosed_setOf_specP_sub_mem (Q := Q) (b i + b j) 0 (K ∙ (b i + b j))
    · simp only [hij, false_implies, Set.ofPred_true, isClosed_univ]

end WtScalar

/-! ## 2. `A_M(F)` and its `H_M` -/

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] {d : GGPData F}

namespace ReducedLeviDatum

variable (L : d.ReducedLeviDatum)

/-- **`A_M(F)`, the split component of the centre of `M`** (Thesis §2.1; Beuzart-Plessis §1.1:
`ã_{M,F} = H_M(A_M(F))`): the pairs in the split centres `wtScalar` of the two flag Levi
subgroups.  That this is the split centre uses that the datum is reduced (the weight-`0` spaces
are not hyperbolic planes). -/
def AMF : Subgroup ↥d.G :=
  ((wtScalar d.QW L.bW L.wtW).prod (wtScalar d.QV L.bV L.wtV)).map d.pair

/-- **Discreteness of `H_M`**: there is `ℓ > 0` such that every coordinate of every `H_M(m)` lies
in `ℤ ℓ` (the value group of `F` is cyclic, `exists_log_norm_mem_zmultiples`). -/
theorem exists_HM_mem_zmultiples :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ (m : ↥L.M) (c : L.Coord), L.HM m c ∈ AddSubgroup.zmultiples ℓ := by
  obtain ⟨ℓ, hℓ, h⟩ := exists_log_norm_mem_zmultiples (F := F)
  exact ⟨ℓ, hℓ, fun m c => h _ (L.char c m).ne_zero⟩

/-- The central scalar `(c, 1)` of `G`, as an element of `M`. -/
def scalarW (c : Fˣ) : ↥L.M :=
  ⟨d.pair (scalarGSpin d.QW c, 1), scalarGSpin_mem_flagLevi (Q := d.QW) L.bW L.wtW c,
    (flagLevi (Q := d.QV) L.bV L.wtV).one_mem⟩

/-- The central scalar `(1, c)` of `G`, as an element of `M`. -/
def scalarV (c : Fˣ) : ↥L.M :=
  ⟨d.pair (1, scalarGSpin d.QV c), (flagLevi (Q := d.QW) L.bW L.wtW).one_mem,
    scalarGSpin_mem_flagLevi (Q := d.QV) L.bV L.wtV c⟩

/-- The `GL`-coordinates of `H_M(m)` vanish when the components of `m` are scalars (scalars act
trivially on `W` and `V`). -/
theorem HM_inl_inl_eq_zero (m : ↥L.M) {c : Fˣ} (h : d.fst m = scalarGSpin d.QW c)
    (i : Fin L.FW.len) : L.HM m (Sum.inl (Sum.inl i)) = 0 := by
  have e : L.char (Sum.inl (Sum.inl i)) m =
      wtDet (Q := d.QW) L.bW L.wtW ((i : ℤ) + 1) ⟨d.fst m, m.2.1⟩ := rfl
  have : ((L.char (Sum.inl (Sum.inl i)) m : Fˣ) : F) = 1 := by
    rw [e, wtDet_apply]
    simp only [h, specP_scalarGSpin_eq_one]
    exact (congrArg LinearMap.det (wtBlock_id _)).trans LinearMap.det_id
  simp [HM, this]

theorem HM_inr_inl_eq_zero (m : ↥L.M) {c : Fˣ} (h : d.snd m = scalarGSpin d.QV c)
    (i : Fin L.FV.len) : L.HM m (Sum.inr (Sum.inl i)) = 0 := by
  have e : L.char (Sum.inr (Sum.inl i)) m =
      wtDet (Q := d.QV) L.bV L.wtV ((i : ℤ) + 1) ⟨d.snd m, m.2.2⟩ := rfl
  have : ((L.char (Sum.inr (Sum.inl i)) m : Fˣ) : F) = 1 := by
    rw [e, wtDet_apply]
    simp only [h, specP_scalarGSpin_eq_one]
    exact (congrArg LinearMap.det (wtBlock_id _)).trans LinearMap.det_id
  simp [HM, this]

/-- `H_M(c, 1) = 2^{dim W} log ‖c‖ e_{GSpin(W)}` (`detChar` is `c ↦ c^{2^{dim W}}` on scalars, and
scalars act trivially on `W`). -/
theorem HM_scalarW (c : Fˣ) : L.HM (L.scalarW c) =
    ((finrank F (CliffordAlgebra d.QW) : ℝ) * Real.log ‖(c : F)‖) •
      Pi.single (Sum.inl (Sum.inr ())) 1 := by
  classical
  funext x
  rcases x with (i | _) | (i | _)
  · simpa using L.HM_inl_inl_eq_zero (L.scalarW c) (c := c) rfl i
  · simp [scalarW, HM, char, fst_pair, detChar_scalarGSpin, norm_pow, Real.log_pow]
  · simpa using L.HM_inr_inl_eq_zero (L.scalarW c) (c := 1) (by simp [scalarW, snd_pair]) i
  · simp [scalarW, HM, char, snd_pair]

/-- `H_M(1, c) = 2^{dim V} log ‖c‖ e_{GSpin(V)}`. -/
theorem HM_scalarV (c : Fˣ) : L.HM (L.scalarV c) =
    ((finrank F (CliffordAlgebra d.QV) : ℝ) * Real.log ‖(c : F)‖) •
      Pi.single (Sum.inr (Sum.inr ())) 1 := by
  classical
  funext x
  rcases x with (i | _) | (i | _)
  · simpa using L.HM_inl_inl_eq_zero (L.scalarV c) (c := 1) (by simp [scalarV, fst_pair]) i
  · simp [scalarV, HM, char, fst_pair]
  · simpa using L.HM_inr_inl_eq_zero (L.scalarV c) (c := c) rfl i
  · simp [scalarV, HM, char, snd_pair, detChar_scalarGSpin, norm_pow, Real.log_pow]

theorem scalarW_mem_AMF (c : Fˣ) : ((L.scalarW c : ↥L.M) : ↥d.G) ∈ L.AMF :=
  ⟨(scalarGSpin d.QW c, 1), ⟨⟨fun _ => 1, rfl, fun j => by simp [specP_scalarGSpin_eq_one]⟩,
    Subgroup.one_mem _⟩, rfl⟩

theorem scalarV_mem_AMF (c : Fˣ) : ((L.scalarV c : ↥L.M) : ↥d.G) ∈ L.AMF :=
  ⟨(1, scalarGSpin d.QV c), ⟨Subgroup.one_mem _,
    ⟨fun _ => 1, rfl, fun j => by simp [specP_scalarGSpin_eq_one]⟩⟩, rfl⟩

/-- The `GL`-coordinates of `H_M(m)` for `m` acting diagonally on the splitting basis of `W`. -/
theorem HM_inl_inl_of_diag (m : ↥L.M) {s : L.ιW → F}
    (hs : ∀ j, specP d.QW (d.fst m) (L.bW j) = s j • L.bW j) (i : Fin L.FW.len) :
    L.HM m (Sum.inl (Sum.inl i)) =
      Real.log ‖∏ j, if L.wtW j = (i : ℤ) + 1 then s j else 1‖ := by
  have e : L.char (Sum.inl (Sum.inl i)) m =
      wtDet (Q := d.QW) L.bW L.wtW ((i : ℤ) + 1) ⟨d.fst m, m.2.1⟩ := rfl
  simp only [HM, e, wtDet_apply]
  rw [det_wtBlock_of_diag hs]

theorem HM_inr_inl_of_diag (m : ↥L.M) {s : L.ιV → F}
    (hs : ∀ j, specP d.QV (d.snd m) (L.bV j) = s j • L.bV j) (i : Fin L.FV.len) :
    L.HM m (Sum.inr (Sum.inl i)) =
      Real.log ‖∏ j, if L.wtV j = (i : ℤ) + 1 then s j else 1‖ := by
  have e : L.char (Sum.inr (Sum.inl i)) m =
      wtDet (Q := d.QV) L.bV L.wtV ((i : ℤ) + 1) ⟨d.snd m, m.2.2⟩ := rfl
  simp only [HM, e, wtDet_apply]
  rw [det_wtBlock_of_diag hs]

omit [PAdicField F] in
/-- `log ‖∏_{wtⱼ = u} τ^{oneWt w u}‖ = [u = w] · n_u log ‖τ‖` for `u, w > 0`. -/
theorem log_norm_prod_oneWt {ι : Type*} [Fintype ι] (wt : ι → ℤ) {τ : F} {u w : ℤ} (hu : 0 < u)
    (hw : 0 < w) :
    Real.log ‖∏ j, if wt j = u then τ ^ oneWt w (wt j) else 1‖ =
      if u = w then (Fintype.card {j // wt j = u} : ℝ) * Real.log ‖τ‖ else 0 := by
  classical
  have : (∏ j, if wt j = u then τ ^ oneWt w (wt j) else 1) =
      (τ ^ oneWt w u) ^ Fintype.card {j // wt j = u} := by
    rw [Fintype.card_subtype, ← Finset.prod_const, Finset.prod_filter]
    exact Finset.prod_congr rfl fun j _ => by split_ifs with h <;> simp [h]
  rw [this, oneWt_of_pos hw hu]
  split_ifs with h
  · rw [zpow_one, norm_pow, Real.log_pow]
  · simp

/-- **A `GL`-direction of `A_M(F)` on the `W` side**: for the weight `w = i + 1`, the lift `T` of
the one-weight cocharacter (`τ` on weight `w`, `τ⁻¹` on `−w`), `0 < ‖τ‖ < 1`, gives
`m = (T, 1) ∈ A_M(F)` with `H_M(m) = n_w log ‖τ‖ e_i + x e_{GSpin(W)}`, `n_w ≥ 1`. -/
theorem exists_HM_torusW (i : Fin L.FW.len) :
    ∃ (T : GSpin d.QW) (m : ↥L.M), (m : ↥d.G) = d.pair (T, 1) ∧ (m : ↥d.G) ∈ L.AMF ∧
      ∃ a : ℝ, a ≠ 0 ∧ L.HM m = a • Pi.single (Sum.inl (Sum.inl i)) 1 +
        L.HM m (Sum.inl (Sum.inr ())) • Pi.single (Sum.inl (Sum.inr ())) 1 := by
  classical
  obtain ⟨τ, hτ0, hτ1⟩ := NormedField.exists_norm_lt_one F
  have hτ : τ ≠ 0 := norm_pos_iff.1 hτ0
  obtain ⟨T, hT⟩ := L.hsW.exists_oneWt_lift d.nondeg ((i : ℤ) + 1) hτ
  have hTs : T ∈ wtScalar d.QW L.bW L.wtW :=
    ⟨fun v => τ ^ oneWt ((i : ℤ) + 1) v, by simp [oneWt_zero (show (i : ℤ) + 1 ≠ 0 by omega)],
      hT⟩
  let m : ↥L.M := ⟨d.pair (T, 1), wtScalar_le_flagLevi hTs,
    (flagLevi (Q := d.QV) L.bV L.wtV).one_mem⟩
  have hm1 : d.fst m = T := by simp [m, fst_pair]
  have hm2 : d.snd m = 1 := by simp [m, snd_pair]
  obtain ⟨j₀, hj₀⟩ := L.hsW.exists_wt_eq (w := (i : ℤ) + 1) (by omega) (by have := i.isLt; omega)
  have hn : 0 < Fintype.card {j // L.wtW j = (i : ℤ) + 1} := Fintype.card_pos_iff.2 ⟨⟨j₀, hj₀⟩⟩
  refine ⟨T, m, rfl, ⟨(T, 1), ⟨hTs, Subgroup.one_mem _⟩, rfl⟩,
    (Fintype.card {j // L.wtW j = (i : ℤ) + 1} : ℝ) * Real.log ‖τ‖,
    mul_ne_zero (by exact_mod_cast hn.ne') (Real.log_neg hτ0 hτ1).ne, ?_⟩
  funext x
  rcases x with (i' | _) | (i' | _)
  · rw [L.HM_inl_inl_of_diag m (s := fun j => τ ^ oneWt ((i : ℤ) + 1) (L.wtW j))
      (fun j => by rw [hm1]; exact hT j) i']
    rw [log_norm_prod_oneWt L.wtW (by omega) (by omega)]
    by_cases h : i' = i
    · subst h; simp
    · have h' : (i' : ℤ) + 1 ≠ (i : ℤ) + 1 := fun e => h (Fin.ext (by omega))
      simp [h, h']
  · simp
  · simpa using L.HM_inr_inl_eq_zero m (c := 1) (by rw [hm2, map_one]) i'
  · simp [m, HM, char, snd_pair]

/-- **A `GL`-direction of `A_M(F)` on the `V` side** (as `exists_HM_torusW`). -/
theorem exists_HM_torusV (i : Fin L.FV.len) :
    ∃ (T : GSpin d.QV) (m : ↥L.M), (m : ↥d.G) = d.pair (1, T) ∧ (m : ↥d.G) ∈ L.AMF ∧
      ∃ a : ℝ, a ≠ 0 ∧ L.HM m = a • Pi.single (Sum.inr (Sum.inl i)) 1 +
        L.HM m (Sum.inr (Sum.inr ())) • Pi.single (Sum.inr (Sum.inr ())) 1 := by
  classical
  obtain ⟨τ, hτ0, hτ1⟩ := NormedField.exists_norm_lt_one F
  have hτ : τ ≠ 0 := norm_pos_iff.1 hτ0
  obtain ⟨T, hT⟩ := L.hsV.exists_oneWt_lift d.nondeg_QV ((i : ℤ) + 1) hτ
  have hTs : T ∈ wtScalar d.QV L.bV L.wtV :=
    ⟨fun v => τ ^ oneWt ((i : ℤ) + 1) v, by simp [oneWt_zero (show (i : ℤ) + 1 ≠ 0 by omega)],
      hT⟩
  let m : ↥L.M := ⟨d.pair (1, T), (flagLevi (Q := d.QW) L.bW L.wtW).one_mem,
    wtScalar_le_flagLevi hTs⟩
  have hm1 : d.fst m = 1 := by simp [m, fst_pair]
  have hm2 : d.snd m = T := by simp [m, snd_pair]
  obtain ⟨j₀, hj₀⟩ := L.hsV.exists_wt_eq (w := (i : ℤ) + 1) (by omega) (by have := i.isLt; omega)
  have hn : 0 < Fintype.card {j // L.wtV j = (i : ℤ) + 1} := Fintype.card_pos_iff.2 ⟨⟨j₀, hj₀⟩⟩
  refine ⟨T, m, rfl, ⟨(1, T), ⟨Subgroup.one_mem _, hTs⟩, rfl⟩,
    (Fintype.card {j // L.wtV j = (i : ℤ) + 1} : ℝ) * Real.log ‖τ‖,
    mul_ne_zero (by exact_mod_cast hn.ne') (Real.log_neg hτ0 hτ1).ne, ?_⟩
  funext x
  rcases x with (i' | _) | (i' | _)
  · simpa using L.HM_inl_inl_eq_zero m (c := 1) (by rw [hm1, map_one]) i'
  · simp [m, HM, char, fst_pair]
  · rw [L.HM_inr_inl_of_diag m (s := fun j => τ ^ oneWt ((i : ℤ) + 1) (L.wtV j))
      (fun j => by rw [hm2]; exact hT j) i']
    rw [log_norm_prod_oneWt L.wtV (by omega) (by omega)]
    by_cases h : i' = i
    · subst h; simp
    · have h' : (i' : ℤ) + 1 ≠ (i : ℤ) + 1 := fun e => h (Fin.ext (by omega))
      simp [h, h']
  · simp

/-- The `H_M` of `A_M(F)`, as a set. -/
def HMAMF : Set L.aM :=
  Set.range fun m : {m : ↥L.M // (m : ↥d.G) ∈ L.AMF} => L.HM m

/-- `x e_c ∈ span` with `x ≠ 0` gives `e_c ∈ span`. -/
theorem single_mem_of_smul_mem {S : Submodule ℝ L.aM} {c : L.Coord} {a : ℝ} (ha : a ≠ 0)
    (h : a • Pi.single c (1 : ℝ) ∈ S) : Pi.single c (1 : ℝ) ∈ S := by
  have := S.smul_mem a⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this

/-- `e_{GSpin(W)}`, `e_{GSpin(V)}` lie in every subspace containing `H_M` of the central scalars. -/
theorem single_gspin_mem {S : Submodule ℝ L.aM} (hW : ∀ c, L.HM (L.scalarW c) ∈ S)
    (hV : ∀ c, L.HM (L.scalarV c) ∈ S) :
    Pi.single (Sum.inl (Sum.inr ())) (1 : ℝ) ∈ S ∧ Pi.single (Sum.inr (Sum.inr ())) (1 : ℝ) ∈ S := by
  obtain ⟨τ, hτ0, hτ1⟩ := NormedField.exists_norm_lt_one F
  have hτ : τ ≠ 0 := norm_pos_iff.1 hτ0
  have hlog : Real.log ‖τ‖ ≠ 0 := (Real.log_neg hτ0 hτ1).ne
  have hNW : (finrank F (CliffordAlgebra d.QW) : ℝ) ≠ 0 := by
    rw [finrank_cliffordAlgebra]; positivity
  have hNV : (finrank F (CliffordAlgebra d.QV) : ℝ) ≠ 0 := by
    rw [finrank_cliffordAlgebra]; positivity
  have h1 := hW (Units.mk0 τ hτ)
  have h2 := hV (Units.mk0 τ hτ)
  rw [HM_scalarW] at h1
  rw [HM_scalarV] at h2
  exact ⟨L.single_mem_of_smul_mem (mul_ne_zero hNW hlog) h1,
    L.single_mem_of_smul_mem (mul_ne_zero hNV hlog) h2⟩

/-- **`H_M(A_M(F))` spans `a_M`.** -/
theorem span_HMAMF_eq_top : Submodule.span ℝ L.HMAMF = ⊤ := by
  classical
  set S := Submodule.span ℝ L.HMAMF
  have hmem : ∀ m : ↥L.M, (m : ↥d.G) ∈ L.AMF → L.HM m ∈ S := fun m hm =>
    Submodule.subset_span ⟨⟨m, hm⟩, rfl⟩
  obtain ⟨hgW, hgV⟩ := L.single_gspin_mem (S := S) (fun c => hmem _ (L.scalarW_mem_AMF c))
    (fun c => hmem _ (L.scalarV_mem_AMF c))
  rw [eq_top_iff, ← (Pi.basisFun ℝ L.Coord).span_eq, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  simp only [Pi.basisFun_apply, SetLike.mem_coe]
  rcases x with (i | _) | (i | _)
  · obtain ⟨-, m, -, hm, a, ha, he⟩ := L.exists_HM_torusW i
    generalize L.HM m (Sum.inl (Sum.inr ())) = x at he
    have h := S.sub_mem (he ▸ hmem m hm) (S.smul_mem x hgW)
    rw [add_sub_cancel_right] at h
    exact L.single_mem_of_smul_mem ha h
  · exact hgW
  · obtain ⟨-, m, -, hm, a, ha, he⟩ := L.exists_HM_torusV i
    generalize L.HM m (Sum.inr (Sum.inr ())) = x at he
    have h := S.sub_mem (he ▸ hmem m hm) (S.smul_mem x hgV)
    rw [add_sub_cancel_right] at h
    exact L.single_mem_of_smul_mem ha h
  · exact hgV

/-- **`H_M(M(F))` spans `a_M`.** -/
theorem span_range_HM_eq_top : Submodule.span ℝ (Set.range L.HM) = ⊤ :=
  eq_top_iff.2 <| L.span_HMAMF_eq_top.symm.le.trans <| Submodule.span_mono <| by
    rintro _ ⟨m, rfl⟩; exact ⟨m.1, rfl⟩

/-! ## 3. `A_M(F)` inside `M(F)` -/

theorem mem_AMF_iff {g : ↥d.G} :
    g ∈ L.AMF ↔ d.fst g ∈ wtScalar d.QW L.bW L.wtW ∧ d.snd g ∈ wtScalar d.QV L.bV L.wtV := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro h
    exact ⟨(d.fst g, d.snd g), h, d.pair_fst_snd g⟩

/-- `A_M(F) ⊆ M(F)`. -/
theorem AMF_le_M : L.AMF ≤ L.M := fun _ hg =>
  ⟨wtScalar_le_flagLevi ((L.mem_AMF_iff).1 hg).1, wtScalar_le_flagLevi ((L.mem_AMF_iff).1 hg).2⟩

/-- `A_M(F)` is closed in `G(F)`. -/
theorem isClosed_AMF : IsClosed (L.AMF : Set ↥d.G) := by
  have : (L.AMF : Set ↥d.G) = d.fst ⁻¹' (wtScalar d.QW L.bW L.wtW : Set _) ∩
      d.snd ⁻¹' (wtScalar d.QV L.bV L.wtV : Set _) := by
    ext g; exact L.mem_AMF_iff
  rw [this]
  exact (isClosed_wtScalar.preimage d.continuous_fst).inter
    (isClosed_wtScalar.preimage d.continuous_snd)

/-- `A_M(F)` is normalized by `M(F)`. -/
theorem conj_mem_AMF {m a : ↥d.G} (hm : m ∈ L.M) (ha : a ∈ L.AMF) : m * a * m⁻¹ ∈ L.AMF := by
  rw [mem_AMF_iff] at ha ⊢
  simp only [map_mul, map_inv]
  exact ⟨mul_mul_inv_mem_wtScalar hm.1 ha.1, mul_mul_inv_mem_wtScalar hm.2 ha.2⟩

/-- `H_M` is invariant under conjugation in `M(F)` (its target is abelian). -/
theorem HM_conj (m a : ↥L.M) : L.HM (m * a * m⁻¹) = L.HM a := by
  rw [HM_mul, HM_mul, HM_inv]; abel

/-- `H_M : M(F) → a_M` as a homomorphism to `Multiplicative a_M`. -/
def HMHom : ↥L.M →* Multiplicative L.aM where
  toFun m := Multiplicative.ofAdd (L.HM m)
  map_one' := by rw [HM_one]; rfl
  map_mul' m m' := by rw [HM_mul]; rfl


end ReducedLeviDatum

end GGPData

end GSpinGGP
