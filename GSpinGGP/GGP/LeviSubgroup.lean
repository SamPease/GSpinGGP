/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.Levi
import GSpinGGP.TraceFormula.FlagLevi
import GSpinGGP.HarmonicAnalysis.LeviComplement
import GSpinGGP.TraceFormula.SpinorNorm

/-!
# Levi subgroups of `G` as subgroups, the set `𝒫(M)`, `a_M` and `H_P`

`parInd` (`GGP/Levi.lean`) induces from the quotient `P/U` (`LeviQuot`).  The weighted orbital
integrals and the spectral side need the Levi `M` as a *subgroup* of `G`, the finite set `𝒫(M)`
of parabolic subgroups with Levi component `M`, the real vector space `a_M` and the map `H_P`
(Thesis §2.1, §2.6, §5.1.2; Waldspurger 2003 §I.1; Beuzart-Plessis, Astérisque 418, §1.1, §1.10).
This file builds these objects for `G = GSpin(W) × GSpin(V)` and the Levi subgroups of its flag
stabilizers (M. Asgari, *Local L-functions for split spinor groups*, Canad. J. Math. 54 (2002),
§2: `M ≅ ∏ GL × GSpin`).

## Main definitions

* `GGPData.IsLevi FW FV M`: `M` is a closed subgroup of `P = P_{F_W} × P_{F_V}` complementary to
  the unipotent radical `U = N_{F_W} × N_{F_V}` (`P = M U`, `M ∩ U = 1`).  `P` and `U` are the
  genuine flag stabilizer and its unipotent radical, only `M` is free: so `U` cannot be replaced
  by a larger or smaller normal subgroup (a structure with `P`, `M`, `U` all free admits junk such
  as `M = 1`, `U = P`).
* `GGPData.parabolics M`: `𝒫(M)`, the parabolic subgroups `P_{F_W} × P_{F_V}` having `M` as a
  Levi component.
* `GGPData.FlagLeviDatum`: flags with splittings of their weight filtrations; its Levi
  `M = flagLeviG`, its opposite datum (`FlagLeviDatum.opp`, the opposite parabolic `P̄ = M Ū`),
  the space `a_M = Coord → ℝ` and `H_M : M → a_M`.
* `GGPData.hP`: `H_P(g) = H_M(m)` for `g = m u k`, any `P ∈ 𝒫(M)` and any compact open `K`
  with `G = P K`.

## Main results

* `IsFlagSplitting.flagLevi_inf_flagUnip`: `M_F ∩ N_F = 1`.
* `GGPData.FlagLeviDatum.isLevi`: `M = M_{F_W} × M_{F_V}` is a Levi of `P`;
  `IsLevi.leviQuotEquiv : M ≃* P/U` connects it with `LeviQuot`.
* `GGPData.FlagLeviDatum.mem_parabolics`, `opp_mem_parabolics`: `P, P̄ ∈ 𝒫(M)`.
* `GGPData.hP_mul`: `H_P(m u k) = H_M(m)` (well defined for any `K` with `G = P K`).
-/

noncomputable section

open Topology Filter Module

namespace GSpinGGP

/-! ## 1. `M_F ∩ N_F = 1`, closedness, and `M` of the opposite weights -/

section FlagLevi

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} {F : IsotropicFlag Q}
variable {ι : Type*} [Fintype ι] {b : Basis ι K V} {wt : ι → ℤ}

omit [Invertible (2 : K)] [Fintype ι] in
theorem wtProj_basis (w : ℤ) (j : ι) :
    wtProj b wt w (b j) = if wt j = w then b j else 0 := by
  simp [wtProj]

omit [Invertible (2 : K)] [Fintype ι] in
/-- `x` is homogeneous of weight `w` iff it is fixed by the weight projection `wtProj w`. -/
theorem isHomog_iff_wtProj (x : V) (w : ℤ) : IsHomog b wt x w ↔ wtProj b wt w x = x := by
  constructor
  · intro hx
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [repr_wtProj]
    split_ifs with h
    · rfl
    · exact (hx i h).symm
  · intro hx i hi
    rw [← hx, repr_wtProj]; simp [hi]

omit [Fintype ι] in
/-- `g ∈ M_F` iff `P(g)` maps each `bⱼ` to a vector of the same weight. -/
theorem mem_flagLevi_iff {g : GSpin Q} :
    g ∈ flagLevi (Q := Q) b wt ↔ ∀ j, IsHomog b wt (specP Q g (b j)) (wt j) := by
  refine ⟨fun hg j => ?_, fun h => wtProj_comp_of_isHomog h⟩
  rw [isHomog_iff_wtProj]
  have := congr($(hg (wt j)) (b j))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, wtProj_basis] at this
  exact this.symm

omit [Fintype ι] in
/-- The Levi subgroup depends only on the weight spaces: `M(b, −wt) = M(b, wt)`. -/
theorem flagLevi_neg : flagLevi (Q := Q) b (-wt) = flagLevi (Q := Q) b wt := by
  ext g
  simp only [mem_flagLevi_iff, IsHomog, Pi.neg_apply, ne_eq, neg_inj]

/-- **`M_F ∩ N_F = 1`**: an element of the Levi subgroup preserves every weight space, and an
element of `N_F` acts trivially on the graded pieces of the weight filtration, so `P(g) = 1`;
then `g` is a scalar `c` (`ker_specP`) with `c − 1` nilpotent, so `c = 1`. -/
theorem IsFlagSplitting.flagLevi_inf_flagUnip [FiniteDimensional K V] (hQ : IsNondeg Q)
    (hs : IsFlagSplitting F b wt) : flagLevi (Q := Q) b wt ⊓ flagUnip F = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hm, hu⟩
  have hA : ∀ j, specP Q g (b j) = b j := by
    intro j
    have hh := (isHomog_iff_wtProj _ _).1 (mem_flagLevi_iff.1 hm j)
    have hr := F.specP_sub_mem_flagWt (flagUnip_le_flagUnipSO F hu) (wt j) (b j) (hs.mem j)
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    by_cases hij : wt i = wt j
    · have := hs.repr_eq_zero _ _ hr i (by omega)
      rwa [map_sub, Finsupp.sub_apply, sub_eq_zero] at this
    · have hji : j ≠ i := fun h => hij (h ▸ rfl)
      rw [← hh, repr_wtProj]
      simp [hij, b.repr_self, hji]
  have hker : g ∈ (specP Q).ker := by
    rw [MonoidHom.mem_ker]
    refine LinearEquiv.toLinearMap_injective (b.ext fun j => ?_)
    simpa using hA j
  rw [ker_specP hQ] at hker
  obtain ⟨c, rfl⟩ := hker
  have hn := hu.2.2.2
  have hc : ((scalarGSpin Q c : GSpin Q) : (CliffordAlgebra Q)ˣ) =
      Units.map (algebraMap K (CliffordAlgebra Q)).toMonoidHom c := rfl
  rw [hc, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    ← map_one (algebraMap K (CliffordAlgebra Q)), ← map_sub] at hn
  have hc1 : (c : K) - 1 = 0 :=
    ((IsNilpotent.map_iff (algebraMap K (CliffordAlgebra Q)).injective).1 hn).eq_zero
  rw [Subgroup.mem_bot, show c = 1 from Units.ext (sub_eq_zero.1 hc1), map_one]

omit [Fintype ι] in
/-- `M_F` is closed in `GSpin(V)`. -/
theorem isClosed_flagLevi [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    [Module.Finite K V] : IsClosed (flagLevi (Q := Q) b wt : Set (GSpin Q)) := by
  have h : (flagLevi (Q := Q) b wt : Set (GSpin Q)) = ⋂ j, {g : GSpin Q |
      specP Q g (b j) - 0 ∈ LinearMap.ker (wtProj b wt (wt j) - LinearMap.id)} := by
    ext g
    simp only [SetLike.mem_coe, mem_flagLevi_iff, isHomog_iff_wtProj, Set.mem_iInter,
      Set.mem_ofPred_eq, sub_zero, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
  rw [h]
  exact isClosed_iInter fun j => isClosed_setOf_specP_sub_mem _ _ _

end FlagLevi


/-! ## 1a. The opposite flag -/

section Opposite

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} {F : IsotropicFlag Q}
variable {ι : Type*} [Fintype ι] {b : Basis ι K V} {wt : ι → ℤ}

/-- The weights of a splitting lie in `[−len, len]`. -/
theorem IsFlagSplitting.wt_le (hs : IsFlagSplitting F b wt) (j : ι) : wt j ≤ F.len := by
  by_contra h
  have := hs.mem j
  rw [F.flagWt_eq_bot (by omega), Submodule.mem_bot] at this
  exact b.ne_zero j this

theorem IsFlagSplitting.neg_len_le (hs : IsFlagSplitting F b wt) (j : ι) : -(F.len : ℤ) ≤ wt j := by
  by_contra h
  have := hs.repr_eq_zero (-(F.len : ℤ)) (b j)
    (by rw [F.flagWt_eq_top le_rfl]; trivial) j (by omega)
  simp at this

/-- A vector paired to `0` with all basis vectors of weight `−c` has no weight-`c` coordinates
(`b` nondegenerate, and `b(bᵢ, bₖ) = 0` unless `wtᵢ + wtₖ = 0`). -/
theorem IsFlagSplitting.repr_eq_zero_of_bform (hQ : IsNondeg Q) (hs : IsFlagSplitting F b wt)
    {v : V} {c : ℤ} (hv : ∀ k, wt k = -c → bform Q (b k) v = 0) {i : ι} (hi : wt i = c) :
    b.repr v i = 0 := by
  set x := wtProj b wt c v
  have hx : IsHomog b wt x c := (isHomog_iff_wtProj _ _).2 (by
    refine b.repr.injective (Finsupp.ext fun l => ?_)
    simp only [x, repr_wtProj]; split_ifs <;> rfl)
  -- `b(bₖ, y) = 0` when `y` has no coordinates of weight `−wtₖ`
  have hsum : ∀ k (y : V), (∀ l, wt l = -wt k → b.repr y l = 0) → bform Q (b k) y = 0 := by
    intro k y hy
    rw [← b.sum_repr y, map_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [map_smul, smul_eq_mul]
    by_cases hl : wt l = -wt k
    · rw [hy l hl, zero_mul]
    · rw [hs.orth k l (by omega), mul_zero]
  have hx0 : x = 0 := by
    refine hQ.1 x fun y => ?_
    rw [bform_comm, ← b.sum_repr y, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    by_cases hk : wt k = -c
    · have h1 : bform Q (b k) (v - x) = 0 := hsum k _ fun l hl => by
        simp only [x, map_sub, Finsupp.sub_apply, repr_wtProj]
        simp only [show wt l = c by omega, ite_true, sub_self]
      rw [map_sub, hv k hk, zero_sub, neg_eq_zero] at h1
      rw [h1, mul_zero]
    · rw [hs.bform_eq_zero_of_isHomog (x := b k) (a := wt k)
        (fun l hl => by
          have hkl : k ≠ l := fun h => hl (h ▸ rfl)
          simp [b.repr_self, hkl])
        hx (by omega), mul_zero]
  have := congr(b.repr $hx0 i)
  simpa [x, repr_wtProj, hi] using this

/-- Every weight `1, …, len` occurs in a splitting (the flag is strictly increasing). -/
theorem IsFlagSplitting.exists_wt_eq (hs : IsFlagSplitting F b wt) {w : ℤ} (h1 : 1 ≤ w)
    (h2 : w ≤ F.len) : ∃ i, wt i = w := by
  by_contra hne
  push Not at hne
  have hlt : F.sub (F.idx (F.len + 1 - (w + 1))) < F.sub (F.idx (F.len + 1 - w)) :=
    F.strictMono (by simp only [IsotropicFlag.idx, Fin.mk_lt_mk]; omega)
  rw [← F.flagWt_of_pos h1, ← F.flagWt_of_pos (by omega)] at hlt
  refine hlt.ne (le_antisymm (F.flagWt_anti (by omega)) fun v hv => ?_)
  rw [hs.mem_flagWt_iff] at hv ⊢
  intro i hi
  exact hv i (lt_of_le_of_ne (by omega) (hne i))

/-- Every weight `−1, …, −len` occurs in a splitting (pairing with the weight `w`). -/
theorem IsFlagSplitting.exists_wt_eq_neg (hQ : IsNondeg Q) (hs : IsFlagSplitting F b wt) {w : ℤ}
    (h1 : 1 ≤ w) (h2 : w ≤ F.len) : ∃ j, wt j = -w := by
  obtain ⟨i, hi⟩ := hs.exists_wt_eq h1 h2
  by_contra hne
  push Not at hne
  refine b.ne_zero i (hQ.1 (b i) fun y => ?_)
  rw [← b.sum_repr y, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, smul_eq_mul, hs.orth i j (fun h => hne j (by omega)), mul_zero]

/-- The span of basis vectors of negative weight is totally isotropic. -/
theorem IsFlagSplitting.isTotallyIsotropic_span (hs : IsFlagSplitting F b wt) {s : Set ι}
    (hneg : ∀ j ∈ s, wt j < 0) : IsTotallyIsotropic Q (Submodule.span K (b '' s)) := by
  have horth : ∀ x ∈ Submodule.span K (b '' s), ∀ y ∈ Submodule.span K (b '' s),
      bform Q x y = 0 := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, hj, rfl⟩ := hy
        exact hs.orth i j (by have := hneg i hi; have := hneg j hj; omega)
      | zero => simp
      | add y z _ _ h1 h2 => rw [map_add, h1, h2, add_zero]
      | smul c y _ h => rw [map_smul, h, smul_zero]
    | zero => simp
    | add x z _ _ h1 h2 => rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
    | smul c x _ h => rw [map_smul, LinearMap.smul_apply, h, smul_zero]
  intro u hu
  rw [← QuadraticMap.associated_eq_self_apply K Q]
  exact horth u hu u hu

/-- The opposite flag: `Z̄ᵢ` is spanned by the `bⱼ` with `−wtⱼ ≥ len + 1 − i`. -/
def IsFlagSplitting.oppFlag (hQ : IsNondeg Q) (hs : IsFlagSplitting F b wt) : IsotropicFlag Q where
  len := F.len
  sub i := Submodule.span K (b '' {j | (F.len : ℤ) + 1 - i ≤ -wt j})
  sub_zero := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨j, hj, rfl⟩
    have := hs.neg_len_le j
    simp only [Set.mem_ofPred_eq, Fin.val_zero, Nat.cast_zero, sub_zero] at hj
    omega
  strictMono := by
    intro i i' hii'
    refine lt_of_le_of_ne (Submodule.span_mono (Set.image_mono fun j hj => ?_)) fun he => ?_
    · simp only [Set.mem_ofPred_eq] at hj ⊢
      have : (i : ℤ) < i' := by exact_mod_cast hii'
      omega
    · have hi' := i'.isLt
      have hi : (i : ℕ) < i' := hii'
      obtain ⟨j, hj⟩ := hs.exists_wt_eq_neg hQ (w := (F.len : ℤ) + 1 - i') (by omega) (by omega)
      have hmem : b j ∈ Submodule.span K (b '' {j | (F.len : ℤ) + 1 - i' ≤ -wt j}) :=
        Submodule.subset_span ⟨j, by simp [hj], rfl⟩
      have he' : Submodule.span K (b '' {j | (F.len : ℤ) + 1 - i ≤ -wt j}) =
          Submodule.span K (b '' {j | (F.len : ℤ) + 1 - i' ≤ -wt j}) := he
      rw [← he', b.self_mem_span_image] at hmem
      simp only [Set.mem_ofPred_eq] at hmem
      omega
  isotropic i := hs.isTotallyIsotropic_span fun j hj => by
    have := (i : Fin (F.len + 1)).isLt
    simp only [Set.mem_ofPred_eq] at hj
    omega

theorem IsFlagSplitting.oppFlag_sub (hQ : IsNondeg Q) (hs : IsFlagSplitting F b wt)
    (i : Fin ((hs.oppFlag hQ).len + 1)) :
    (hs.oppFlag hQ).sub i = Submodule.span K (b '' {j | (F.len : ℤ) + 1 - i ≤ -wt j}) := rfl

/-- **The opposite flag** (`P̄ = M Ū`): `(b, −wt)` splits the flag `oppFlag`. -/
theorem IsFlagSplitting.isFlagSplitting_oppFlag (hQ : IsNondeg Q) (hs : IsFlagSplitting F b wt) :
    IsFlagSplitting (hs.oppFlag hQ) b (-wt) := by
  set F' := hs.oppFlag hQ
  have hlen : F'.len = F.len := rfl
  have hidx : ∀ t : ℤ, ((F'.idx t : Fin (F'.len + 1)) : ℕ) = min t.toNat F.len := fun _ => rfl
  refine ⟨fun j => ?_, fun w v hv i hi => ?_, fun i j hij => hs.orth i j (by
    simp only [Pi.neg_apply] at hij; omega), by simp [Finset.sum_neg_distrib, hs.sum_wt]⟩
  · have hb1 := hs.wt_le j
    have hb2 := hs.neg_len_le j
    simp only [Pi.neg_apply]
    by_cases hw : 1 ≤ -wt j
    · rw [F'.flagWt_of_pos hw, hs.oppFlag_sub]
      refine Submodule.subset_span ⟨j, ?_, rfl⟩
      simp only [Set.mem_ofPred_eq]
      have := hidx (F'.len + 1 - -wt j)
      omega
    · rw [F'.flagWt_of_nonpos (by omega), LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      rw [hs.oppFlag_sub] at hy
      have := hidx (F'.len + -wt j)
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨k, hk, rfl⟩ := hy
        simp only [Set.mem_ofPred_eq] at hk
        exact hs.orth k j (by omega)
      | zero => simp
      | add y z _ _ h1 h2 => rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
      | smul c y _ h => rw [map_smul, LinearMap.smul_apply, h, smul_zero]
  · simp only [Pi.neg_apply] at hi
    have hb1 := hs.wt_le i
    have hb2 := hs.neg_len_le i
    by_cases hw : 1 ≤ w
    · rw [F'.flagWt_of_pos hw, hs.oppFlag_sub] at hv
      have hsupp := b.repr_support_subset_of_mem_span _ hv
      by_contra hne
      have := hsupp (Finsupp.mem_support_iff.2 hne)
      simp only [Set.mem_ofPred_eq] at this
      have := hidx (F'.len + 1 - w)
      omega
    · rw [F'.flagWt_of_nonpos (by omega), LinearMap.BilinForm.mem_orthogonal_iff] at hv
      refine hs.repr_eq_zero_of_bform hQ (c := wt i) (fun k hk => hv _ ?_) rfl
      rw [hs.oppFlag_sub]
      refine Submodule.subset_span ⟨k, ?_, rfl⟩
      simp only [Set.mem_ofPred_eq]
      have := hidx (F'.len + w)
      omega

end Opposite

/-! ## 1b. The determinant characters of `M_F` -/

section WtDet

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {ι : Type*} {b : Basis ι K V} {wt : ι → ℤ}

theorem wtProj_comp_self (w : ℤ) : wtProj b wt w ∘ₗ wtProj b wt w = wtProj b wt w :=
  b.ext fun j => by by_cases h : wt j = w <;> simp [wtProj_basis, h]

variable (b wt) in
/-- `A` on the weight-`w` space, the identity on the others: `E_w A + (1 − E_w)`.  For `A`
commuting with `E_w`, its determinant is `det(A|_{V_w})`. -/
def wtBlock (w : ℤ) (A : V →ₗ[K] V) : V →ₗ[K] V :=
  wtProj b wt w ∘ₗ A + (LinearMap.id - wtProj b wt w)

theorem wtBlock_comp {w : ℤ} {A B : V →ₗ[K] V} (hA : A ∘ₗ wtProj b wt w = wtProj b wt w ∘ₗ A) :
    wtBlock b wt w A ∘ₗ wtBlock b wt w B = wtBlock b wt w (A ∘ₗ B) := by
  have hE : wtProj b wt w * wtProj b wt w = wtProj b wt w := wtProj_comp_self w
  have hA' : A * wtProj b wt w = wtProj b wt w * A := hA
  set E := wtProj b wt w
  change (E * A + (1 - E)) * (E * B + (1 - E)) = E * (A * B) + (1 - E)
  have hy : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
  have hy' : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have hyy : (1 - E) * (1 - E) = 1 - E := by rw [mul_sub, mul_one, hy', sub_zero]
  have h1 : E * A * (E * B) = E * (A * B) := by
    rw [mul_assoc, ← mul_assoc A E B, hA', mul_assoc, ← mul_assoc E E, hE]
  have h2 : E * A * (1 - E) = 0 := by
    rw [mul_assoc, mul_sub, mul_one, hA', mul_sub, ← mul_assoc E E A, hE, sub_self]
  have h3 : (1 - E) * (E * B) = 0 := by rw [← mul_assoc, hy', zero_mul]
  rw [add_mul, mul_add, mul_add, h1, h2, h3, hyy, add_zero, zero_add]

theorem wtBlock_id (w : ℤ) : wtBlock b wt w LinearMap.id = LinearMap.id := by
  simp [wtBlock]

variable {Q : QuadraticForm K V} [Invertible (2 : K)]

variable (b wt) in
/-- **The determinant character** `m ↦ det(m|_{V_w})` of the Levi subgroup `M_F` on the weight-`w`
space of the splitting (for `w > 0` the `GL(Z_i/Z_{i−1})`-factor of `M_F`, Asgari 2002 §2). -/
def wtDet (w : ℤ) : flagLevi (Q := Q) b wt →* Kˣ :=
  MonoidHom.toHomUnits
    { toFun := fun m => LinearMap.det (wtBlock b wt w (specP Q (m : GSpin Q) : V →ₗ[K] V))
      map_one' := by simp [wtBlock_id]
      map_mul' := fun m m' => by
        rw [← map_mul, Subgroup.coe_mul, map_mul]
        change _ = LinearMap.det (wtBlock b wt w _ ∘ₗ wtBlock b wt w _)
        rw [wtBlock_comp (m.2 w)]
        rfl }

theorem wtDet_apply (w : ℤ) (m : flagLevi (Q := Q) b wt) :
    ((wtDet (Q := Q) b wt w m : Kˣ) : K) =
      LinearMap.det (wtBlock b wt w (specP Q (m : GSpin Q) : V →ₗ[K] V)) := rfl

end WtDet

section WtDetContinuous

variable {K : Type*} [Field K] [Invertible (2 : K)] [TopologicalSpace K] [IsTopologicalRing K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [TopologicalSpace V]
  [IsModuleTopology K V]
variable {Q : QuadraticForm K V} {ι : Type*} [Finite ι] {b : Basis ι K V} {wt : ι → ℤ}

/-- The determinant characters are continuous. -/
theorem continuous_wtDet (w : ℤ) :
    Continuous fun m : flagLevi (Q := Q) b wt => ((wtDet (Q := Q) b wt w m : Kˣ) : K) := by
  classical
  have := Fintype.ofFinite ι
  simp_rw [wtDet_apply, ← LinearMap.det_toMatrix b]
  refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)
  simp only [LinearMap.toMatrix_apply, wtBlock, LinearMap.add_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, map_add, Finsupp.add_apply]
  refine Continuous.add ?_ continuous_const
  exact (IsModuleTopology.continuous_of_linearMap ((b.coord i) ∘ₗ wtProj b wt w)).comp
    (continuous_specP_apply continuous_subtypeVal (b j))

end WtDetContinuous

/-! ## 2. Levi subgroups of `P = P_{F_W} × P_{F_V}` -/

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

/-- **`M` is a Levi subgroup of `P = P_{F_W} × P_{F_V}`** (Thesis §5.1.2: `P = M N`;
Beuzart-Plessis §1.1): a closed subgroup of `P` complementary to the unipotent radical
`U = N_{F_W} × N_{F_V}`, i.e. `M ∩ U = 1` and `P = M U` (Mathlib's `Subgroup.IsComplement'`,
inside `P`).  `M` normalizes `U` because `U` is normal in `P` (`whittU_normal`).  The Levi
subgroups `flagLeviG` of splittings of the flags are examples (`FlagLeviDatum.isLevi`). -/
structure IsLevi (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) (M : Subgroup ↥d.G) :
    Prop where
  isClosed : IsClosed (M : Set ↥d.G)
  le : M ≤ d.whittB FW FV
  isComplement' : (M.subgroupOf (d.whittB FW FV)).IsComplement'
    ((d.whittU FW FV).subgroupOf (d.whittB FW FV))

variable {d}

namespace IsLevi

variable {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV} {M : Subgroup ↥d.G}

/-- `M ∩ U = 1`. -/
theorem inf_eq_bot (hL : d.IsLevi FW FV M) : M ⊓ d.whittU FW FV = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hm, hu⟩
  have := Subgroup.disjoint_def.1 hL.isComplement'.disjoint
    (x := ⟨g, hL.le hm⟩) hm hu
  simpa using congrArg Subtype.val this

/-- `P = M U`. -/
theorem exists_mul (hL : d.IsLevi FW FV M) {p : ↥d.G} (hp : p ∈ d.whittB FW FV) :
    ∃ m ∈ M, ∃ u ∈ d.whittU FW FV, p = m * u := by
  obtain ⟨⟨m, u⟩, he⟩ := hL.isComplement'.2 ⟨p, hp⟩
  exact ⟨m.1.1, m.2, u.1.1, u.2, by simpa using (congrArg Subtype.val he).symm⟩

/-- The projection `P → M`, `m u ↦ m`. -/
def proj (hL : d.IsLevi FW FV M) : ↥(d.whittB FW FV) →* ↥M :=
  (Subgroup.subgroupOfEquivOfLe hL.le).toMonoidHom.comp hL.isComplement'.proj

theorem proj_mul (hL : d.IsLevi FW FV M) (m : ↥M) {u : ↥d.G} (hu : u ∈ d.whittU FW FV) :
    hL.proj ⟨(m : ↥d.G) * u, (d.whittB FW FV).mul_mem (hL.le m.2) (d.whittU_le_whittB FW FV hu)⟩ =
      m := by
  have := hL.isComplement'.proj_mul ⟨⟨m, hL.le m.2⟩, m.2⟩
    (n := ⟨u, d.whittU_le_whittB FW FV hu⟩) hu
  simp only [proj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [show (⟨(m : ↥d.G) * u, _⟩ : ↥(d.whittB FW FV)) =
    ((⟨⟨m, hL.le m.2⟩, m.2⟩ : ↥(M.subgroupOf (d.whittB FW FV))) : ↥(d.whittB FW FV)) *
      ⟨u, d.whittU_le_whittB FW FV hu⟩ from rfl, this]
  rfl

/-- **`M ≅ P/U`**: a Levi subgroup is isomorphic to the Levi quotient `LeviQuot` used by `parInd`
(`Subgroup.IsComplement'.QuotientMulEquiv`). -/
def leviQuotEquiv (hL : d.IsLevi FW FV M) : ↥M ≃* d.LeviQuot FW FV :=
  (Subgroup.subgroupOfEquivOfLe hL.le).symm.trans hL.isComplement'.QuotientMulEquiv.symm

theorem leviQuotEquiv_apply (hL : d.IsLevi FW FV M) (m : ↥M) :
    hL.leviQuotEquiv m = QuotientGroup.mk ⟨(m : ↥d.G), hL.le m.2⟩ := rfl

/-- The projection `P → M` is continuous (open mapping theorem: `M` is σ-compact and `P/U` is
locally compact). -/
theorem continuous_proj (hL : d.IsLevi FW FV M) : Continuous hL.proj := by
  have hcl : IsClosed ((M.subgroupOf (d.whittB FW FV) : Subgroup ↥(d.whittB FW FV)) :
      Set ↥(d.whittB FW FV)) := hL.isClosed.preimage continuous_subtypeVal
  have : LocallyCompactSpace ↥(M.subgroupOf (d.whittB FW FV)) := hcl.locallyCompactSpace
  have : SecondCountableTopology ↥(d.whittB FW FV) := d.secondCountableTopology_whittB FW FV
  have : SecondCountableTopology ↥(M.subgroupOf (d.whittB FW FV)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : SigmaCompactSpace ↥(M.subgroupOf (d.whittB FW FV)) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have he : Continuous (Subgroup.subgroupOfEquivOfLe hL.le) :=
    (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
  have : T2Space (d.LeviQuot FW FV) := d.t2Space_leviQuot FW FV
  have : LocallyCompactSpace (d.LeviQuot FW FV) := inferInstance
  exact he.comp hL.isComplement'.continuous_proj

/-- Levi subgroups of the same parabolic are never properly nested. -/
theorem eq_of_le (hL : d.IsLevi FW FV M) {M' : Subgroup ↥d.G} (hL' : d.IsLevi FW FV M')
    (h : M ≤ M') : M = M' := by
  refine le_antisymm h fun x hx => ?_
  obtain ⟨m, hm, u, hu, rfl⟩ := hL.exists_mul (hL'.le hx)
  have hu' : u ∈ M' := by
    have := M'.mul_mem (M'.inv_mem (h hm)) hx
    rwa [inv_mul_cancel_left] at this
  have : u ∈ M' ⊓ d.whittU FW FV := ⟨hu', hu⟩
  rw [hL'.inf_eq_bot, Subgroup.mem_bot] at this
  rw [this, mul_one]; exact hm

end IsLevi

/-- **Elements of the unipotent radical generate relatively compact subgroups**: all powers of
`u ∈ U` lie in one compact set (`u − 1` is nilpotent in each Clifford factor,
`exists_isCompact_zpow_of_isNilpotent`). -/
theorem exists_isCompact_zpow_of_mem_whittU {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV}
    {u : ↥d.G} (hu : u ∈ d.whittU FW FV) : ∃ C : Set ↥d.G, IsCompact C ∧ ∀ k : ℤ, u ^ k ∈ C := by
  have := properSpace_F (F := F)
  have key : ∀ {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      [TopologicalSpace V] [IsModuleTopology F V] {Q : QuadraticForm F V} {g : GSpin Q},
      IsNilpotent (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1) →
      ∃ C : Set (GSpin Q), IsCompact C ∧ ∀ k : ℤ, g ^ k ∈ C := by
    intro V _ _ _ _ _ Q g hg
    have := t2Space_cliffordAlgebra Q
    obtain ⟨C, hC, hCu⟩ := exists_isCompact_zpow_of_isNilpotent (K := F) _ hg
    refine ⟨_, (isClosed_GSpin Q).isClosedEmbedding_subtypeVal.isCompact_preimage hC,
      fun k => ?_⟩
    show ((g ^ k : GSpin Q) : (CliffordAlgebra Q)ˣ) ∈ C
    rw [Subgroup.coe_zpow]; exact hCu k
  obtain ⟨CW, hCW, hW⟩ := key hu.1.2.2.2
  obtain ⟨CV, hCV, hV⟩ := key hu.2.2.2.2
  refine ⟨d.pair '' (CW ×ˢ CV), (hCW.prod hCV).image d.continuous_pair, fun k => ?_⟩
  refine ⟨(d.fst (u ^ k), d.snd (u ^ k)), ⟨?_, ?_⟩, d.pair_fst_snd _⟩
  · show d.fst (u ^ k) ∈ CW
    rw [map_zpow]; exact hW k
  · show d.snd (u ^ k) ∈ CV
    rw [map_zpow]; exact hV k

/-! ## 3. Flag Levi data, `𝒫(M)`, `a_M`, `H_M` and `H_P` -/

/-- `M_{F_W} × M_{F_V} ∩ N_{F_W} × N_{F_V} = 1`. -/
theorem flagLeviG_inf_whittU {ιW ιV : Type*} [Fintype ιW] [Fintype ιV] {FW : IsotropicFlag d.QW}
    {FV : IsotropicFlag d.QV} {bW : Basis ιW F (Fin d.m → F)} {wtW : ιW → ℤ}
    {bV : Basis ιV F d.V} {wtV : ιV → ℤ}
    (hsW : IsFlagSplitting FW bW wtW) (hsV : IsFlagSplitting FV bV wtV) :
    d.flagLeviG bW wtW bV wtV ⊓ d.whittU FW FV = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hm, hu⟩
  have h1 : d.fst g ∈ flagLevi (Q := d.QW) bW wtW ⊓ flagUnip FW := ⟨hm.1, hu.1⟩
  have h2 : d.snd g ∈ flagLevi (Q := d.QV) bV wtV ⊓ flagUnip FV := ⟨hm.2, hu.2⟩
  rw [hsW.flagLevi_inf_flagUnip d.nondeg, Subgroup.mem_bot] at h1
  rw [hsV.flagLevi_inf_flagUnip d.nondeg_QV, Subgroup.mem_bot] at h2
  rw [Subgroup.mem_bot, ← d.pair_fst_snd g, h1, h2]
  exact map_one d.pair

variable (d) in
/-- **A flag Levi datum** of `G`: isotropic flags `F_W`, `F_V` with splittings `(b_W, wt_W)`,
`(b_V, wt_V)` of their weight filtrations (`exists_flagSplitting`).  Its Levi subgroup is
`M = M_{F_W} × M_{F_V}` (`flagLeviG`), a Levi of `P = P_{F_W} × P_{F_V}` (`isLevi`). -/
structure FlagLeviDatum where
  FW : IsotropicFlag d.QW
  FV : IsotropicFlag d.QV
  ιW : Type
  ιV : Type
  [fintypeW : Fintype ιW]
  [fintypeV : Fintype ιV]
  bW : Basis ιW F (Fin d.m → F)
  wtW : ιW → ℤ
  bV : Basis ιV F d.V
  wtV : ιV → ℤ
  hsW : IsFlagSplitting FW bW wtW
  hsV : IsFlagSplitting FV bV wtV

namespace FlagLeviDatum

attribute [instance] fintypeW fintypeV

variable (L : d.FlagLeviDatum)

/-- The Levi subgroup `M = M_{F_W} × M_{F_V}`. -/
abbrev M : Subgroup ↥d.G := d.flagLeviG L.bW L.wtW L.bV L.wtV

/-- The parabolic subgroup `P = P_{F_W} × P_{F_V}`. -/
abbrev P : Subgroup ↥d.G := d.whittB L.FW L.FV

/-- The unipotent radical `U = N_{F_W} × N_{F_V}`. -/
abbrev U : Subgroup ↥d.G := d.whittU L.FW L.FV

/-- **`M` is a Levi subgroup of `P`** (Thesis §5.1.2: `P = M N`). -/
theorem isLevi : d.IsLevi L.FW L.FV L.M where
  isClosed := ((isClosed_flagLevi (Q := d.QW)).preimage d.continuous_fst).inter
    ((isClosed_flagLevi (Q := d.QV)).preimage d.continuous_snd)
  le := d.flagLeviG_le_whittB L.hsW L.hsV
  isComplement' := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hm hu
      have : (x : ↥d.G) ∈ L.M ⊓ L.U := ⟨hm, hu⟩
      rw [flagLeviG_inf_whittU L.hsW L.hsV, Subgroup.mem_bot] at this
      exact Subtype.ext this
    · refine Set.eq_univ_iff_forall.2 fun p => ?_
      obtain ⟨m, hm, u, hu, he⟩ := d.exists_mem_flagLeviG_mul L.hsW L.hsV p.2
      exact Set.mem_mul.2 ⟨⟨m, d.flagLeviG_le_whittB L.hsW L.hsV hm⟩, hm,
        ⟨u, d.whittU_le_whittB _ _ hu⟩, hu, Subtype.ext he.symm⟩

/-- **The opposite datum**: the opposite flags (`IsFlagSplitting.oppFlag`) with the same bases and
the negated weights.  Its parabolic is the opposite parabolic `P̄ = M Ū` (`opp_M`). -/
def opp : d.FlagLeviDatum where
  FW := L.hsW.oppFlag d.nondeg
  FV := L.hsV.oppFlag d.nondeg_QV
  ιW := L.ιW
  ιV := L.ιV
  bW := L.bW
  wtW := -L.wtW
  bV := L.bV
  wtV := -L.wtV
  hsW := L.hsW.isFlagSplitting_oppFlag d.nondeg
  hsV := L.hsV.isFlagSplitting_oppFlag d.nondeg_QV

/-- `P` and `P̄` have the same Levi subgroup. -/
theorem opp_M : L.opp.M = L.M := by
  simp only [M, opp, GGPData.flagLeviG, flagLevi_neg]

/-- The coordinates of `a_M`: the weights `1, …, len` of each flag (the `GL`-factors of `M`) and
one coordinate for each `GSpin`-factor. -/
abbrev Coord : Type := (Fin L.FW.len ⊕ Unit) ⊕ (Fin L.FV.len ⊕ Unit)

/-- **The real vector space `a_M`** (Thesis §2.1; Beuzart-Plessis §1.1:
`a_M = Hom(X^*(M)_F, ℝ)`), in coordinates given by the rational characters `char L c` of `M`:
for `M = ∏ GL(Z_i/Z_{i-1}) × GSpin(Z^⊥/Z)` in each factor (Asgari 2002 §2), the determinants of
the `GL`-blocks and the norm of the `GSpin`-factor (`detChar`, a power of the similitude
character) form a basis of `X^*(M)_F ⊗ ℚ`, so `λ ↦ (λ(χ_c))_c` identifies
`Hom(X^*(M)_F, ℝ)` with `Coord → ℝ`.  This needs `Z^⊥/Z` not to be a hyperbolic plane (then
`GSpin(Z^⊥/Z)` is a split torus of rank `2`): in that case the flag is refined by one of the two
isotropic lines of `Z^⊥/Z`, which gives the same `P` and `M`. -/
abbrev aM : Type := L.Coord → ℝ

/-- The characters of `M` giving the coordinates of `a_M`. -/
def char : L.Coord → (↥L.M →* Fˣ)
  | Sum.inl (Sum.inl i) => (wtDet (Q := d.QW) L.bW L.wtW ((i : ℤ) + 1)).comp
      ((d.fst.comp L.M.subtype).codRestrict _ fun m => m.2.1)
  | Sum.inl (Sum.inr _) => (detChar d.QW).comp (d.fst.comp L.M.subtype)
  | Sum.inr (Sum.inl i) => (wtDet (Q := d.QV) L.bV L.wtV ((i : ℤ) + 1)).comp
      ((d.snd.comp L.M.subtype).codRestrict _ fun m => m.2.2)
  | Sum.inr (Sum.inr _) => (detChar d.QV).comp (d.snd.comp L.M.subtype)

/-- **The Harish-Chandra map of `M`**, `H_M(m)(χ) = log |χ(m)|` (Thesis §2.1; Beuzart-Plessis
§1.1), in the coordinates of `aM`. -/
def HM (m : ↥L.M) : L.aM := fun c => Real.log ‖((L.char c m : Fˣ) : F)‖

theorem HM_mul (m m' : ↥L.M) : L.HM (m * m') = L.HM m + L.HM m' := by
  funext c
  simp only [HM, Pi.add_apply, map_mul, Units.val_mul, norm_mul]
  exact Real.log_mul (norm_ne_zero_iff.2 (L.char c m).ne_zero)
    (norm_ne_zero_iff.2 (L.char c m').ne_zero)

theorem HM_one : L.HM 1 = 0 := by
  funext c; simp [HM]

end FlagLeviDatum

variable (d) in
/-- **`𝒫(M)`, the parabolic subgroups with Levi component `M`** (Thesis §2.1; Beuzart-Plessis
§1.1): the subgroups `P_{F_W} × P_{F_V}` (every parabolic subgroup of `G` is of this form,
Thesis §5.1.2) of which `M` is a Levi subgroup. -/
def parabolics (M : Subgroup ↥d.G) : Set (Subgroup ↥d.G) :=
  {P | ∃ (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV), P = d.whittB FW FV ∧
    d.IsLevi FW FV M}

namespace FlagLeviDatum

variable (L : d.FlagLeviDatum)

theorem mem_parabolics : L.P ∈ d.parabolics L.M := ⟨L.FW, L.FV, rfl, L.isLevi⟩

/-- **The opposite parabolic** `P̄ ∈ 𝒫(M)`. -/
theorem opp_mem_parabolics : L.opp.P ∈ d.parabolics L.M :=
  ⟨L.opp.FW, L.opp.FV, rfl, L.opp_M ▸ L.opp.isLevi⟩

/-- **`𝒫(M)` is finite.**  Sketch: choose the splitting bases to be Witt bases (hyperbolic pairs
and an anisotropic kernel); the diagonal split torus `A` then lies in `M`, and contains an element
whose eigenvalues on the hyperbolic lines are pairwise distinct and `≠ 1`.  If `M ⊆ P_{F'}`, every
member of `F'` is `A`-stable, hence spanned by its intersections with the eigenspaces, i.e. by
basis vectors (the intersection with the anisotropic kernel is isotropic, hence `0`).  So `F'`
ranges over finitely many flags. -/
theorem finite_parabolics : (d.parabolics L.M).Finite := by
  sorry

end FlagLeviDatum

namespace FlagLeviDatum

variable (L : d.FlagLeviDatum)

theorem continuous_char (c : L.Coord) : Continuous fun m : ↥L.M => ((L.char c m : Fˣ) : F) := by
  classical
  rcases c with (i | _) | (i | _)
  · exact (continuous_wtDet (Q := d.QW) _).comp
      ((d.continuous_fst.comp continuous_subtypeVal).subtype_mk _)
  · exact (continuous_detChar d.QW).comp (d.continuous_fst.comp continuous_subtypeVal)
  · exact (continuous_wtDet (Q := d.QV) _).comp
      ((d.continuous_snd.comp continuous_subtypeVal).subtype_mk _)
  · exact (continuous_detChar d.QV).comp (d.continuous_snd.comp continuous_subtypeVal)

/-- **The map `H_P`** (Thesis §2.6, p. 29; Waldspurger 2003 §I.1; Beuzart-Plessis §1.10): for
`P = P_{F_W} × P_{F_V} ∈ 𝒫(M)` and a compact open subgroup `K` with `G = P K`,
`H_P(g) = H_M(m)` where `g = m u k` (`hP_mul`; well defined for every such `K`: `H_M` is trivial on
the compact group `M`-part of `P ∩ K`). -/
def hP {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV} (hL : d.IsLevi FW FV L.M)
    (K : Subgroup ↥d.G) (hKo : IsOpen (K : Set ↥d.G)) (hKc : IsCompact (K : Set ↥d.G))
    (hPK : ∀ g : ↥d.G, ∃ p ∈ d.whittB FW FV, ∃ k ∈ K, g = p * k) : ↥d.G → L.aM :=
  (IwasawaPair.mk (d.whittB FW FV) K (d.isClosed_whittB FW FV) hKo hKc hPK).extend
    fun p => L.HM (hL.proj p)

/-- **`H_P(m u k) = H_M(m)`.** -/
theorem hP_mul {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV} (hL : d.IsLevi FW FV L.M)
    {K : Subgroup ↥d.G} (hKo : IsOpen (K : Set ↥d.G)) (hKc : IsCompact (K : Set ↥d.G))
    (hPK : ∀ g : ↥d.G, ∃ p ∈ d.whittB FW FV, ∃ k ∈ K, g = p * k) (m : ↥L.M)
    {u : ↥d.G} (hu : u ∈ d.whittU FW FV) {k : ↥d.G} (hk : k ∈ K) :
    L.hP hL K hKo hKc hPK ((m : ↥d.G) * u * k) = L.HM m := by
  set I : IwasawaPair ↥d.G := IwasawaPair.mk (d.whittB FW FV) K (d.isClosed_whittB FW FV) hKo
    hKc hPK
  have hinv : ∀ p q : ↥I.P, (q : ↥d.G) ∈ I.K →
      L.HM (hL.proj (p * q)) = L.HM (hL.proj p) := by
    intro p q hq
    rw [map_mul, HM_mul, add_eq_left]
    funext c
    have hC : IsCompact ((Subtype.val : ↥(d.whittB FW FV) → ↥d.G) ⁻¹' (K : Set ↥d.G)) :=
      (d.isClosed_whittB FW FV).isClosedEmbedding_subtypeVal.isCompact_preimage hKc
    have := norm_char_eq_one_of_zpow_mem_compact ((L.char c).comp hL.proj)
      ((L.continuous_char c).comp hL.continuous_proj) hC
      (u := q) fun n => by simpa using K.zpow_mem hq n
    simp only [HM, Pi.zero_apply]
    rw [show (L.char c) (hL.proj q) = ((L.char c).comp hL.proj) q from rfl, this, Real.log_one]
  have := I.extend_mul (h := fun p => L.HM (hL.proj p)) hinv ⟨(m : ↥d.G) * u, (d.whittB FW FV).mul_mem (hL.le m.2)
    (d.whittU_le_whittB FW FV hu)⟩ hk
  simp only [hP]
  rw [this, hL.proj_mul m hu]

end FlagLeviDatum

end GGPData

end GSpinGGP
