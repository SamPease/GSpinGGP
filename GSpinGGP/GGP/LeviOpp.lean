/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.SpecialK

/-!
# The opposite presentation `L ↦ L.opp` of a Levi subgroup

`L.opp` (`ReducedLeviDatum.opp`) has the opposite flags, the same bases and the negated weights;
its Levi subgroup is the same (`FlagLeviDatum.opp_M`).  This file shows that everything entering
Arthur's weight `v_M` is the same for the two presentations.

* `det_wtBlock_neg_mul`: **determinant duality** `det(P(g)|_{V_{−w}}) · det(P(g)|_{V_w}) = 1` for
  `g` in the Levi subgroup: `b` pairs `V_w` with `V_{−w}` perfectly and `P(g)` preserves `b`, so
  `aᵀ B c = B` for the blocks `a`, `c` of `P(g)` and the Gram matrix `B`
  (`transpose_mul_gram_mul`).
* `GoodK.opp`, `GoodK.IsSpecial.opp`: the same subgroup `K` is good (special) for `L.opp`.
* `ReducedLeviDatum.opp_AMF`, `opp_aG`, `opp_finrank_aMG`: same `A_M(F)`, `a_G`, `dim a_M^G`.
* `ReducedLeviDatum.opp_HM_add_mem_aG`: `H_M` of `L.opp` is `−H_M` of `L` modulo `a_G` (the
  `GL`-coordinates change sign by determinant duality; the `GSpin`-coordinates lie in `a_G`).
* `ReducedLeviDatum.opp_latticeMG`, `opp_hPar`: the lattice `proj_M^G(H_M(A_M(F)))` and the points
  `H_P(g)` of `L.opp` are the images of those of `L` under `oppNegEquiv` (`−1` on `a_M^G`).
* `ReducedLeviDatum.opp_vM`: **`v_M` is the same for `L` and `L.opp`** (`Measure.hullVolume_map`).
-/

noncomputable section

open Module Matrix MeasureTheory

namespace GSpinGGP

section Opp

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
      · simp [hj, hi, hij, hij']
      · simp [hj, hi, hij, hij', h0 (by rw [hj]; exact hi)]
      · simp [hj, hi, hij, hij', h0 (by rw [hi]; exact Ne.symm hj)]
      · simp [hj, hi, hij, hij']
  rw [← LinearMap.det_toMatrix b, twoBlockTriangular_det N (fun i => wt i = w) ?_]
  · have h1 : N.toSquareBlockProp (fun i => ¬ wt i = w) = 1 := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      rw [toSquareBlockProp_def, of_apply, hN]
      simp only [hj, if_false]
      by_cases h : i = j
      · subst h; simp
      · rw [if_neg h, one_apply_ne (by simpa [Subtype.ext_iff] using h)]
    have h2 : N.toSquareBlockProp (fun i => wt i = w) =
        A.toSquareBlockProp (fun i => wt i = w) := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      rw [toSquareBlockProp_def, toSquareBlockProp_def, of_apply, of_apply, hN]
      simp [hj]
    rw [h1, h2, det_one, mul_one]
  · intro i hi j hj
    rw [hN, if_pos hj]
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

omit [Fintype ι] [DecidableEq ι] in
/-- The scalars on the weight spaces do not see the sign of the weights. -/
theorem wtScalar_neg (b : Basis ι K V) (wt : ι → ℤ) :
    wtScalar Q b (-wt) = wtScalar Q b wt := by
  ext g
  constructor
  · rintro ⟨t, ht0, ht⟩
    exact ⟨fun w => t (-w), by simpa using ht0, fun j => by simpa using ht j⟩
  · rintro ⟨t, ht0, ht⟩
    exact ⟨fun w => t (-w), by simpa using ht0, fun j => by simpa using ht j⟩

end Opp

section SpecialOpp

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
  {V : Type*} [AddCommGroup V] [Module F V] {ι : Type*}

omit [PAdicField F] in
/-- Adaptedness of a special lattice does not see the sign of the weights. -/
theorem SpecialLattice.IsAdapted.neg [FiniteDimensional F V] {Q : QuadraticForm F V}
    {S : SpecialLattice Q} {b : Basis ι F V} {wt : ι → ℤ} (h : S.IsAdapted b wt) :
    S.IsAdapted b (-wt) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i => exists_mem_wtSpan_neg (h1 i), fun i => exists_mem_wtSpan_neg (h2 i), ?_⟩
  rwa [wtSpan_neg]

end SpecialOpp

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] {d : GGPData F}

/-- Good position does not see the sign of the weights. -/
theorem StabilizesSplitLattice.neg {V ι : Type*} [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {b : Basis ι F V} {wt : ι → ℤ} {S : Set (GSpin Q)}
    (h : StabilizesSplitLattice Q b wt S) : StabilizesSplitLattice Q b (-wt) S := by
  obtain ⟨κ, hκ, e, he, hS⟩ := h
  exact ⟨κ, hκ, e, fun i => exists_mem_wtSpan_neg (he i), hS⟩

/-- **A good `K` for `L` is good for `L.opp`**: the same subgroup (`𝒫(M)` is the same, and the
weight spaces are the same up to sign). -/
def GoodK.opp {L : d.FlagLeviDatum} (K : d.GoodK L) : d.GoodK L.opp where
  K := K.K
  isOpen := K.isOpen
  isCompact := K.isCompact
  mul_eq P hP := K.mul_eq P (L.opp_M ▸ hP)
  goodPositionW := K.goodPositionW.neg
  goodPositionV := K.goodPositionV.neg

@[simp] theorem GoodK.opp_K {L : d.FlagLeviDatum} (K : d.GoodK L) : K.opp.K = K.K := rfl

/-- **`K` special for `L` is special for `L.opp`.** -/
theorem GoodK.IsSpecial.opp {L : d.FlagLeviDatum} {K : d.GoodK L} (h : K.IsSpecial) :
    K.opp.IsSpecial := by
  obtain ⟨SW, SV, hW, hV, hK⟩ := h
  exact ⟨SW, SV, hW.neg, hV.neg, hK⟩

/-- The projection `P → M` does not depend on how `M` is written. -/
theorem IsLevi.coe_proj_congr {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV}
    {M M' : Subgroup ↥d.G} (h : M = M') (hL : d.IsLevi FW FV M) (hL' : d.IsLevi FW FV M')
    (p : ↥(d.whittB FW FV)) : ((hL.proj p : ↥M) : ↥d.G) = ((hL'.proj p : ↥M') : ↥d.G) := by
  subst h; rfl

namespace ReducedLeviDatum

variable (L : d.ReducedLeviDatum)

/-- `GoodK.opp`, typed for the reduced datum `L.opp`. -/
def oppK (K : d.GoodK L.toFlagLeviDatum) : d.GoodK L.opp.toFlagLeviDatum := K.opp

@[simp] theorem oppK_K (K : d.GoodK L.toFlagLeviDatum) : (L.oppK K).K = K.K := rfl

theorem oppK_isSpecial {K : d.GoodK L.toFlagLeviDatum} (h : K.IsSpecial) : (L.oppK K).IsSpecial :=
  h.opp

/-- **`A_M(F)` is the same for `L` and `L.opp`.** -/
theorem opp_AMF : L.opp.AMF = L.AMF := by
  ext g
  rw [ReducedLeviDatum.mem_AMF_iff, ReducedLeviDatum.mem_AMF_iff]
  change d.fst g ∈ wtScalar d.QW L.bW (-L.wtW) ∧ d.snd g ∈ wtScalar d.QV L.bV (-L.wtV) ↔ _
  rw [wtScalar_neg, wtScalar_neg]

/-- **`a_G` is the same for `L` and `L.opp`** (same `a_M`; `a_G` is spanned by the central
coordinates, `mem_aG_iff`). -/
theorem opp_aG : L.opp.aG = L.aG := by
  ext H
  refine (L.opp.mem_aG_iff).trans (Iff.trans ?_ (L.mem_aG_iff (H := H)).symm)
  constructor <;> intro h c hc <;> rcases c with (i | u) | (i | u) <;> exact h _ hc

/-- `a_M^G` for `L` and `L.opp` (same `a_M`, same `a_G`). -/
def oppAMGEquiv : L.aMG ≃ₗ[ℝ] L.opp.aMG :=
  Submodule.quotEquivOfEq L.aG L.opp.aG L.opp_aG.symm

@[simp] theorem oppAMGEquiv_mkQ (H : L.aM) :
    L.oppAMGEquiv (L.aG.mkQ H) = L.opp.aG.mkQ H := rfl

/-- **`dim a_M^G` is the same for `L` and `L.opp`.** -/
theorem opp_finrank_aMG : finrank ℝ L.opp.aMG = finrank ℝ L.aMG :=
  L.oppAMGEquiv.finrank_eq.symm

/-- **`H_M` of `L.opp` is `−H_M` of `L` modulo `a_G`**: on the `GL`-coordinates by determinant
duality (`det_wtBlock_neg_mul`); the `GSpin`-coordinates are central. -/
theorem opp_HM_add_mem_aG (m : ↥L.M) (m' : ↥L.opp.M) (hmm : (m' : ↥d.G) = m) :
    (show L.aM from L.opp.HM m') + L.HM m ∈ L.aG := by
  classical
  have key : ∀ x y : F, x * y = 1 → Real.log ‖x‖ + Real.log ‖y‖ = 0 := fun x y h => by
    have hx : x ≠ 0 := left_ne_zero_of_mul_eq_one h
    have hy : y ≠ 0 := right_ne_zero_of_mul_eq_one h
    rw [← Real.log_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy), ← norm_mul, h, norm_one,
      Real.log_one]
  rw [L.mem_aG_iff]
  rintro ((i | u) | (i | u)) hc
  · change Real.log ‖LinearMap.det (wtBlock L.bW (-L.wtW) ((i : ℤ) + 1)
        (specP d.QW (d.fst m') : _ →ₗ[F] _))‖ + Real.log ‖LinearMap.det (wtBlock L.bW L.wtW
        ((i : ℤ) + 1) (specP d.QW (d.fst m) : _ →ₗ[F] _))‖ = 0
    rw [hmm]
    exact key _ _ (det_wtBlock_neg_mul d.nondeg L.hsW m.2.1 _)
  · exact absurd trivial hc
  · change Real.log ‖LinearMap.det (wtBlock L.bV (-L.wtV) ((i : ℤ) + 1)
        (specP d.QV (d.snd m') : _ →ₗ[F] _))‖ + Real.log ‖LinearMap.det (wtBlock L.bV L.wtV
        ((i : ℤ) + 1) (specP d.QV (d.snd m) : _ →ₗ[F] _))‖ = 0
    rw [hmm]
    exact key _ _ (det_wtBlock_neg_mul d.nondeg_QV L.hsV m.2.2 _)
  · exact absurd trivial hc

/-- **`−1` on `a_M^G`, from `L` to `L.opp`**: the map carrying the data of `L` to those of `L.opp`
(`opp_mkQ_HM`, `opp_latticeMG`, `opp_hPar`). -/
def oppNegEquiv : L.aMG ≃L[ℝ] L.opp.aMG :=
  ((LinearEquiv.neg ℝ).trans L.oppAMGEquiv).toContinuousLinearEquiv

theorem oppNegEquiv_mkQ (H : L.aM) : L.oppNegEquiv (L.aG.mkQ H) = -L.opp.aG.mkQ H := by
  change L.oppAMGEquiv (-(L.aG.mkQ H)) = _
  rw [map_neg]
  rfl

/-- `H_M` of `L.opp` is the image of `H_M` of `L` under `oppNegEquiv`, in `a_M^G`. -/
theorem opp_mkQ_HM (m : ↥L.M) (m' : ↥L.opp.M) (hmm : (m' : ↥d.G) = m) :
    L.opp.aG.mkQ (L.opp.HM m') = L.oppNegEquiv (L.aG.mkQ (L.HM m)) := by
  rw [oppNegEquiv_mkQ, eq_neg_iff_add_eq_zero]
  have h := L.opp_HM_add_mem_aG m m' hmm
  rw [← L.opp_aG] at h
  exact (Submodule.Quotient.mk_eq_zero L.opp.aG).2 h

/-- **`latticeMG` under `L ↦ L.opp`**: the lattice `proj_M^G(H_M(A_M(F)))` of `L.opp` is the
image of that of `L` under `oppNegEquiv`. -/
theorem opp_latticeMG :
    L.opp.latticeMG = L.latticeMG.map (L.oppNegEquiv : L.aMG →+ L.opp.aMG) := by
  rw [ReducedLeviDatum.latticeMG, ReducedLeviDatum.latticeMG, AddMonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨⟨m', hm'⟩, rfl⟩
    have hmM : (m' : ↥d.G) ∈ L.M := L.toFlagLeviDatum.opp_M ▸ m'.2
    have hA : (m' : ↥d.G) ∈ L.AMF := L.opp_AMF ▸ hm'
    exact ⟨_, ⟨⟨⟨m', hmM⟩, hA⟩, rfl⟩, (L.opp_mkQ_HM ⟨m', hmM⟩ m' rfl).symm⟩
  · rintro ⟨_, ⟨⟨m, hm⟩, rfl⟩, rfl⟩
    have hmM : (m : ↥d.G) ∈ L.opp.M := L.toFlagLeviDatum.opp_M.symm ▸ m.2
    have hA : (m : ↥d.G) ∈ L.opp.AMF := L.opp_AMF.symm ▸ hm
    exact ⟨⟨⟨m, hmM⟩, hA⟩, L.opp_mkQ_HM m ⟨m, hmM⟩ rfl⟩

/-- **`H_P` under `L ↦ L.opp`**: `H_P^{L.opp}(g) = −H_P^{L}(g)` in `a_M^G`, for the same `K` and the
same parabolic `P ∈ 𝒫(M)`. -/
theorem opp_hPar (K : d.GoodK L.toFlagLeviDatum) {P : Subgroup ↥d.G}
    (hP' : P ∈ d.parabolics L.opp.M) (hP : P ∈ d.parabolics L.M) (g : ↥d.G) :
    L.opp.aG.mkQ (L.opp.hPar (L.oppK K) ⟨P, hP'⟩ g) =
      L.oppNegEquiv (L.aG.mkQ (L.hPar K ⟨P, hP⟩ g)) := by
  obtain ⟨FW, FV, hPeq, hL'⟩ := id hP'
  have hL : d.IsLevi FW FV L.M := L.toFlagLeviDatum.opp_M ▸ hL'
  obtain ⟨p, hp, k, hk, rfl⟩ := K.mul_eq P hP g
  have hp' : p ∈ d.whittB FW FV := hPeq ▸ hp
  rw [L.opp.hPar_eq (L.oppK K) ⟨P, hP'⟩ hPeq hL', L.hPar_eq K ⟨P, hP⟩ hPeq hL]
  have e3 := L.opp.hP_eq hL' (L.oppK K).isOpen (L.oppK K).isCompact
    (hPeq ▸ (L.oppK K).mul_eq P hP') ⟨p, hp'⟩ hk
  have e4 := L.hP_eq hL K.isOpen K.isCompact (hPeq ▸ K.mul_eq P hP) ⟨p, hp'⟩ hk
  rw [e3, e4]
  exact L.opp_mkQ_HM _ _ (IsLevi.coe_proj_congr L.toFlagLeviDatum.opp_M hL' hL _)

/-- **`v_M` is the same for `L` and `L.opp`** (with the same `K`): the points `H_P(g)` and the
lattice are carried by the linear isomorphism `oppNegEquiv` (`opp_hPar`, `opp_latticeMG`), and the
lattice-normalized volume of a hull is invariant under it (`Measure.hullVolume_map`). -/
theorem opp_vM (K : d.GoodK L.toFlagLeviDatum) (g : ↥d.G) : L.opp.vM (L.oppK K) g = L.vM K g := by
  have hS :
      (Set.range fun P : ↥(d.parabolics L.opp.M) => L.opp.aG.mkQ (L.opp.hPar (L.oppK K) P g)) =
      L.oppNegEquiv '' Set.range fun P : ↥(d.parabolics L.M) => L.aG.mkQ (L.hPar K P g) := by
    ext v
    constructor
    · rintro ⟨⟨P, hP'⟩, rfl⟩
      have hP : P ∈ d.parabolics L.M := L.toFlagLeviDatum.opp_M ▸ hP'
      exact ⟨_, ⟨⟨P, hP⟩, rfl⟩, (L.opp_hPar K hP' hP g).symm⟩
    · rintro ⟨_, ⟨⟨P, hP⟩, rfl⟩, rfl⟩
      have hP' : P ∈ d.parabolics L.opp.M := L.toFlagLeviDatum.opp_M.symm ▸ hP
      exact ⟨⟨P, hP'⟩, L.opp_hPar K hP' hP g⟩
  obtain ⟨D, hD, -⟩ := L.opp.exists_isAddFundamentalDomain_latticeHaar_eq_one
  have hcount : Countable ↥(L.opp.latticeMG.toIntSubmodule) := by
    obtain ⟨h1, h2⟩ := L.opp.latticeMG_isLattice
    have : IsZLattice ℝ L.opp.latticeMG.toIntSubmodule := ⟨h2⟩
    infer_instance
  simp only [ReducedLeviDatum.vM]
  rw [hS]
  have : Countable ↥(L.latticeMG.map (L.oppNegEquiv : L.aMG →+ L.opp.aMG)) := by
    rw [← L.opp_latticeMG]; exact hcount
  rw [L.opp_latticeMG] at hD
  rw [L.opp_latticeMG]
  exact Measure.hullVolume_map L.oppNegEquiv hD _

end ReducedLeviDatum

end GGPData

end GSpinGGP
