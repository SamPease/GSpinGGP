/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.JointRankDescent
import GSpinGGP.GGP.RegularNilpotent
import GSpinGGP.Foundations.JordanAlgebra
import GSpinGGP.Foundations.RankSemicontinuity

/-!
# Regular semisimple elements of `𝔤_g`

Let `g ∈ GSpin(V)` and `Y ∈ gspin(V)_g` be semisimple (left multiplication by each is semisimple
on `C(V)`, as in `IsSS`). Then
`adV Y` is a semisimple skew map commuting with `P(g)` (`isSemisimple_adV`), and
`jointClauses_of_charZero` for the pair `(P(g), adV Y)` gives, for the centralizer
`gspin(V)_{g,Y}` (of dimension `1 + dim (so(V)_{P(g)} ⊓ so(V)_{adV Y})`):

* `le_finrank_lieCentralizer_gspin_of_isSemisimple`: `⌊dim V/2⌋ + 1 ≤ dim gspin(V)_{g,Y}`;
* `finrank_lieCentralizer_gspin_eq_iff_isLieAbelian`: equality iff `gspin(V)_{g,Y}` is abelian;
* `eq_zero_of_isNilpotent_mem_lieCentralizer_gspin`: in case of equality, its only nilpotent
  element is `0`.

For `𝔤 = gspin(W) × gspin(V)` and semisimple `g ∈ G(F)` the same holds for `𝔤_{g,Z}` with
`ℓ = (⌊dim W/2⌋ + 1) + (⌊dim V/2⌋ + 1)` (`lieClauses`). With the Jordan decomposition in `𝔤_g` and
upper semicontinuity of `dim ker (ad Z)^D`, this shows that the regular semisimple set of `𝔤_g` is
open (`isOpen_setOf_isRegularSS_lieCentralizer`).

Group version: if the generalized `1`-eigenspace of `Ad x` on `𝔤` (`x ∈ G(F)`) has dimension `≤ ℓ`,
then `x` is regular semisimple (`mem_regularSet_of_finrank_ker_le`). It uses the multiplicative
Jordan decomposition (`exists_jordan_G`), `ker (1 − Ad x)^k = ker (ad x)^k`
(`ker_one_sub_conjAd_pow`), and the unipotent clause of `JointClauses` lifted to `G(F)`
(`eq_one_of_isNilpotent_sub_one_of_lieClauses`): when `dim 𝔤_{g,Z} = ℓ`, the only unipotent element
of `G(F)` commuting with `g` and `Z` is `1`.
-/

noncomputable section

open Module CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

section Unipotent

variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]

open Polynomial in
/-- **`P(h)` is unipotent when `h ∈ GSpin(V)` is** (`h − 1` nilpotent): `ι ∘ (P(h) − 1)^k =
(Ad h − 1)^k ∘ ι` (`ι_aeval_specP`) and `Ad h − 1` is nilpotent (`isNilpotent_conj_sub_conj`,
`s = 1`). -/
theorem isNilpotent_specP_sub_one [FiniteDimensional K V] {Q : QuadraticForm K V} (h : GSpin Q)
    (hn : IsNilpotent (((h : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1)) :
    IsNilpotent ((specP Q h : Module.End K V) - 1) := by
  have h1 := (isNilpotent_conj_sub_conj (F := K) (x := (h : (CliffordAlgebra Q)ˣ)) (s := 1)
    (by rw [Units.val_one]; exact Subalgebra.one_mem _) (by rwa [Units.val_one])).1
  rw [inv_one, Units.val_one, LinearMap.mulLeft_one, LinearMap.mulRight_one, ← Module.End.one_eq_id,
    mul_one] at h1
  obtain ⟨k, hk⟩ := h1
  refine ⟨k, LinearMap.ext fun v => ι_injective Q ?_⟩
  have h2 := ι_aeval_specP h ((X - 1) ^ k) v
  simp only [map_pow, map_sub, aeval_X, map_one] at h2
  rw [h2, hk, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

end Unipotent

/-! ## Clauses for semisimple `g`, `Y` -/

section Factor

variable {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

variable {Q : QuadraticForm K V} (hQ : IsNondeg Q) (g : GSpin Q)
  (hg : Module.End.IsSemisimple
    (LinearMap.mulLeft K ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))
  {Y : CliffordAlgebra Q}
  (hY : Y ∈ lieCentralizer (gspin Q) ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
  (hs : Module.End.IsSemisimple (LinearMap.mulLeft K Y))
include hQ hg hY hs

/-- The four clauses for `(P(g), adV Y)`. -/
theorem jointClauses_specP_adV :
    JointClauses Q (specP Q g : Module.End K V) (adV Q Y) (finrank K V / 2) := by
  obtain ⟨hYg, hYx⟩ := mem_lieCentralizer.mp hY
  exact jointClauses_of_charZero hQ (fun u v => bform_specP g u v)
    (isSemisimple_specP_of_isSS Q g hg)
    (fun u v => bform_adV hYg u v) (isSemisimple_adV hYg hs)
    ((commute_iff_adV hQ g hYg).mp hYx).symm (det_specP g)

/-- **`⌊dim V/2⌋ + 1 ≤ dim gspin(V)_{g,Y}`**, for `g` and `Y` semisimple. -/
theorem le_finrank_lieCentralizer_gspin_of_isSemisimple :
    finrank K V / 2 + 1 ≤ finrank K (lieCentralizer (lieCentralizer (gspin Q)
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) Y) := by
  rw [finrank_lieCentralizer_lieCentralizer_gspin hQ g (mem_lieCentralizer.mp hY).1]
  exact Nat.add_le_add_right (jointClauses_specP_adV hQ g hg hY hs).1 1

/-- **`dim gspin(V)_{g,Y} = ⌊dim V/2⌋ + 1` iff `gspin(V)_{g,Y}` is abelian**, for `g` and `Y`
semisimple. -/
theorem finrank_lieCentralizer_gspin_eq_iff_isLieAbelian :
    finrank K (lieCentralizer (lieCentralizer (gspin Q)
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) Y) = finrank K V / 2 + 1 ↔
    IsLieAbelian (lieCentralizer (lieCentralizer (gspin Q)
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) Y) := by
  rw [finrank_lieCentralizer_lieCentralizer_gspin hQ g (mem_lieCentralizer.mp hY).1,
    isLieAbelian_lieCentralizer_gspin_iff hQ g (mem_lieCentralizer.mp hY).1,
    Nat.add_right_cancel_iff]
  exact (jointClauses_specP_adV hQ g hg hY hs).2.1

/-- **If `dim gspin(V)_{g,Y} = ⌊dim V/2⌋ + 1`, its only nilpotent element is `0`**, for `g` and `Y`
semisimple. -/
theorem eq_zero_of_isNilpotent_mem_lieCentralizer_gspin
    (he : finrank K (lieCentralizer (lieCentralizer (gspin Q)
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) Y) = finrank K V / 2 + 1)
    {Z : CliffordAlgebra Q}
    (hZ : Z ∈ lieCentralizer (lieCentralizer (gspin Q)
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) Y) (hn : IsNilpotent Z) : Z = 0 := by
  have hYg := (mem_lieCentralizer.mp hY).1
  have hZg := (mem_lieCentralizer.mp (mem_lieCentralizer.mp hZ).1).1
  rw [finrank_lieCentralizer_lieCentralizer_gspin hQ g hYg, Nat.add_right_cancel_iff] at he
  have h0 := (jointClauses_specP_adV hQ g hg hY hs).2.2.1 he _ (adV_mem_soCent_inf hQ g hYg hZ)
    (isNilpotent_adV hZg hn)
  obtain ⟨r, rfl⟩ := eq_algebraMap_of_adV_eq_zero hQ hZg h0
  obtain ⟨k, hk⟩ := hn
  rw [← map_pow] at hk
  have hr : IsNilpotent r :=
    ⟨k, (algebraMap K (CliffordAlgebra Q)).injective (hk.trans (map_zero _).symm)⟩
  rw [hr.eq_zero, map_zero]

/-- **If `dim gspin(V)_{g,Y} = ⌊dim V/2⌋ + 1`, the only unipotent `h ∈ GSpin(V)` commuting with `g`
and `Y` is `1`**, for `g` and `Y` semisimple: `P(h)` is a unipotent isometry commuting with `P(g)`
and `adV Y`, so `P(h) = 1`; then `h` is a scalar, and a unipotent scalar is `1`. -/
theorem eq_one_of_isNilpotent_sub_one_of_commute
    (he : finrank K (lieCentralizer (lieCentralizer (gspin Q)
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) Y) = finrank K V / 2 + 1)
    (h : GSpin Q) (hn : IsNilpotent (((h : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1))
    (hgh : Commute ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
      ((h : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
    (hhY : Commute ((h : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) Y) : h = 1 := by
  have hYg := (mem_lieCentralizer.mp hY).1
  rw [finrank_lieCentralizer_lieCentralizer_gspin hQ g hYg, Nat.add_right_cancel_iff] at he
  have hgh' : g * h = h * g := Subtype.ext (Units.ext hgh.eq)
  have hPg : Commute (specP Q g : Module.End K V) (specP Q h : Module.End K V) :=
    LinearMap.ext fun v => by
      simp only [Module.End.mul_apply, LinearEquiv.coe_coe, ← LinearEquiv.mul_apply, ← map_mul,
        hgh']
  have h1 := (jointClauses_specP_adV hQ g hg hY hs).2.2.2 he _ (fun u v => bform_specP h u v)
    (isNilpotent_specP_sub_one h hn) hPg ((commute_iff_adV hQ h hYg).mp hhY.eq).symm
  have hk : h ∈ (specP Q).ker :=
    MonoidHom.mem_ker.mpr (LinearEquiv.ext fun v => LinearMap.congr_fun h1 v)
  rw [ker_specP hQ] at hk
  obtain ⟨c, rfl⟩ := hk
  have hc : IsNilpotent ((c : K) - 1) := by
    obtain ⟨k, hk⟩ := hn
    refine ⟨k, (algebraMap K (CliffordAlgebra Q)).injective ?_⟩
    rw [map_pow, map_sub, map_one, map_zero]
    simpa [scalarGSpin] using hk
  rw [show c = 1 from Units.ext (sub_eq_zero.mp hc.eq_zero), map_one]

end Factor

section Assembly

variable {F : Type*} [NontriviallyNormedField F] [CompleteSpace F] [CharZero F] (d : GGPData F)

/-- The rank `ℓ = (⌊dim W/2⌋ + 1) + (⌊dim V/2⌋ + 1)` of `𝔤 = gspin(W) × gspin(V)` (the rank of
each factor is `lieRank_gspin`). -/
def lieRankNat : ℕ := (finrank F (Fin d.m → F) / 2 + 1) + (finrank F d.V / 2 + 1)

private theorem eq_and_eq_of_add_eq {A B p q : ℕ} (h1 : p ≤ A) (h2 : q ≤ B)
    (h : A + B = p + q) : A = p ∧ B = q := by
  omega

variable (g : ↥d.G) (hg : IsSS F ((g : d.ambientˣ) : d.ambient))
include hg

omit [CompleteSpace F] in
/-- The factors of `g ∈ G(F)` and of `Z ∈ 𝔤_g`, both semisimple, satisfy the hypotheses of the
factor clauses. -/
private theorem factor_hyps {Z : d.ambient}
    (hZ : Z ∈ lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) (hs : IsSS F Z) :
    IsSS F ((d.fst g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) ∧
      IsSS F ((d.snd g : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) ∧
      Z.1 ∈ lieCentralizer (gspin d.QW)
        ((d.fst g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) ∧
      Z.2 ∈ lieCentralizer (gspin d.QV)
        ((d.snd g : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) ∧
      IsSS F Z.1 ∧ IsSS F Z.2 := by
  obtain ⟨⟨hZW, hZV⟩, hZa⟩ := mem_lieCentralizer.mp hZ
  exact ⟨isSS_algHom (AlgHom.fst F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) hg,
    isSS_algHom (AlgHom.snd F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) hg,
    mem_lieCentralizer.mpr ⟨hZW, congrArg Prod.fst hZa⟩,
    mem_lieCentralizer.mpr ⟨hZV, congrArg Prod.snd hZa⟩,
    isSS_algHom (AlgHom.fst F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) hs,
    isSS_algHom (AlgHom.snd F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) hs⟩

omit [CompleteSpace F] in
/-- **The clauses for `𝔤_{g,Z}`**, `g ∈ G(F)` and `Z ∈ 𝔤_g` semisimple: `ℓ ≤ dim 𝔤_{g,Z}`; equality
iff `𝔤_{g,Z}` is abelian; and then `0` is its only nilpotent element. -/
theorem lieClauses {Z : d.ambient}
    (hZ : Z ∈ lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) (hs : IsSS F Z) :
    lieRankNat d ≤
      finrank F (lieCentralizer (lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) Z) ∧
    (finrank F (lieCentralizer (lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) Z) =
        lieRankNat d ↔
      IsLieAbelian (lieCentralizer (lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) Z)) ∧
    (finrank F (lieCentralizer (lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) Z) =
        lieRankNat d → ∀ X ∈ lieCentralizer (lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) Z,
      IsNilpotent X → X = 0) := by
  obtain ⟨hg1, hg2, hZ1, hZ2, hs1, hs2⟩ := factor_hyps d g hg hZ hs
  have l1 := le_finrank_lieCentralizer_gspin_of_isSemisimple d.nondeg (d.fst g) hg1 hZ1 hs1
  have l2 := le_finrank_lieCentralizer_gspin_of_isSemisimple d.nondeg_QV (d.snd g) hg2 hZ2 hs2
  have e1 := finrank_lieCentralizer_gspin_eq_iff_isLieAbelian d.nondeg (d.fst g) hg1 hZ1 hs1
  have e2 := finrank_lieCentralizer_gspin_eq_iff_isLieAbelian d.nondeg_QV (d.snd g) hg2 hZ2 hs2
  have n1 := eq_zero_of_isNilpotent_mem_lieCentralizer_gspin d.nondeg (d.fst g) hg1 hZ1 hs1
  have n2 := eq_zero_of_isNilpotent_mem_lieCentralizer_gspin d.nondeg_QV (d.snd g) hg2 hZ2 hs2
  have ha1 : ((g : d.ambientˣ) : d.ambient).1 =
      ((d.fst g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) := rfl
  have ha2 : ((g : d.ambientˣ) : d.ambient).2 =
      ((d.snd g : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) := rfl
  rw [← ha1] at l1 e1 n1
  rw [← ha2] at l2 e2 n2
  rw [finrank_lieCentralizer_lieCentralizer_lie, isLieAbelian_lieCentralizer_lieCentralizer_lie_iff,
    ← e1, ← e2]
  unfold lieRankNat
  have hle := @eq_and_eq_of_add_eq
  refine ⟨Nat.add_le_add l1 l2, ⟨fun he => ⟨(hle l1 l2 he).1, (hle l1 l2 he).2⟩,
    fun ⟨h1, h2⟩ => by rw [h1, h2]⟩, fun he X hX hn => ?_⟩
  rw [mem_lieCentralizer_lieCentralizer_lie] at hX
  obtain ⟨k, hk⟩ := hn
  exact Prod.ext (n1 (hle l1 l2 he).1 hX.1 ⟨k, by rw [← Prod.pow_fst, hk, Prod.fst_zero]⟩)
    (n2 (hle l1 l2 he).2 hX.2 ⟨k, by rw [← Prod.pow_snd, hk, Prod.snd_zero]⟩)

omit [CompleteSpace F] in
/-- **The unipotent clause for `𝔤_{g,Z}`**, `g ∈ G(F)` and `Z ∈ 𝔤_g` semisimple: if
`dim 𝔤_{g,Z} = ℓ`, the only unipotent `h ∈ G(F)` commuting with `g` and `Z` is `1`. -/
theorem eq_one_of_isNilpotent_sub_one_of_lieClauses {Z : d.ambient}
    (hZ : Z ∈ lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) (hs : IsSS F Z)
    (he : finrank F (lieCentralizer (lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) Z) =
      lieRankNat d)
    (h : ↥d.G) (hn : IsNilpotent (((h : d.ambientˣ) : d.ambient) - 1))
    (hgh : Commute ((g : d.ambientˣ) : d.ambient) ((h : d.ambientˣ) : d.ambient))
    (hhZ : Commute ((h : d.ambientˣ) : d.ambient) Z) : h = 1 := by
  obtain ⟨hg1, hg2, hZ1, hZ2, hs1, hs2⟩ := factor_hyps d g hg hZ hs
  have l1 := le_finrank_lieCentralizer_gspin_of_isSemisimple d.nondeg (d.fst g) hg1 hZ1 hs1
  have l2 := le_finrank_lieCentralizer_gspin_of_isSemisimple d.nondeg_QV (d.snd g) hg2 hZ2 hs2
  rw [finrank_lieCentralizer_lieCentralizer_lie] at he
  unfold lieRankNat at he
  obtain ⟨e1, e2⟩ := eq_and_eq_of_add_eq l1 l2 he
  obtain ⟨k, hk⟩ := hn
  have u1 := eq_one_of_isNilpotent_sub_one_of_commute d.nondeg (d.fst g) hg1 hZ1 hs1 e1 (d.fst h)
    ⟨k, by
      change (((h : d.ambientˣ) : d.ambient).1 - 1) ^ k = 0
      simpa using congrArg Prod.fst hk⟩
    (congrArg Prod.fst hgh.eq) (congrArg Prod.fst hhZ.eq)
  have u2 := eq_one_of_isNilpotent_sub_one_of_commute d.nondeg_QV (d.snd g) hg2 hZ2 hs2 e2 (d.snd h)
    ⟨k, by
      change (((h : d.ambientˣ) : d.ambient).2 - 1) ^ k = 0
      simpa using congrArg Prod.snd hk⟩
    (congrArg Prod.snd hgh.eq) (congrArg Prod.snd hhZ.eq)
  refine Subtype.ext (Units.ext (Prod.ext ?_ ?_))
  · exact congrArg (fun k : GSpin d.QW => ((k : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) u1
  · exact congrArg (fun k : GSpin d.QV => ((k : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) u2

/-- **The regular semisimple set of `𝔤_g` is open**, for `g ∈ G(F)` semisimple. Near a regular
semisimple `Z₀`, `dim ker (ad Z)^D ≤ dim ker (ad Z₀)^D = dim 𝔤_{g,Z₀} = ℓ` (semicontinuity;
`D = dim C(W) × C(V)`). For the Jordan decomposition `Z = s + n` (both in `𝔤_g`), `𝔤_{g,s}` lies in
`ker (ad Z)^D`, so `dim 𝔤_{g,s} = ℓ` (`lieClauses`): then `𝔤_{g,s}` is abelian and its nilpotent
element `n` is `0`, so `Z = s` is regular semisimple. -/
theorem isOpen_setOf_isRegularSS_lieCentralizer :
    IsOpen {Z : ↥(lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) |
      IsRegularSS (lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) (Z : d.ambient)} := by
  set a : d.ambient := ((g : d.ambientˣ) : d.ambient)
  set L := lieCentralizer d.lie a
  set D := finrank F d.ambient
  let ad : d.ambient → Module.End F d.ambient := fun Y => LieAlgebra.ad F d.ambient Y
  let f : ↥L → (↥L.toSubmodule →ₗ[F] d.ambient) := fun Z =>
    (ad (Z : d.ambient) ^ D) ∘ₗ L.toSubmodule.subtype
  -- continuity of `Z ↦ (ad Z)^D v`
  have hc : ∀ (k : ℕ) (w : d.ambient), Continuous fun Y : d.ambient => (ad Y ^ k) w := by
    intro k
    induction k with
    | zero => intro w; exact continuous_const
    | succ k ih =>
      intro w
      simp only [pow_succ', Module.End.mul_apply, ad, LieAlgebra.ad_apply, Ring.lie_def]
      exact (continuous_id.mul (ih w)).sub ((ih w).mul continuous_id)
  have hf : ∀ v, Continuous fun Z : ↥L => f Z v := fun v =>
    (hc D v).comp continuous_subtype_val
  -- `dim ker f Z = dim (𝔤_g ∩ ker (ad Z)^D)`
  have hker : ∀ Z : ↥L, finrank F (LinearMap.ker (f Z)) =
      finrank F ↥(L.toSubmodule ⊓ LinearMap.ker (ad (Z : d.ambient) ^ D)) := by
    intro Z
    rw [← Submodule.finrank_map_subtype_eq L.toSubmodule, LinearMap.ker_comp,
      Submodule.map_comap_subtype]
  have hD : 0 < D := Module.finrank_pos
  have hlie : ∀ Y, finrank F (lieCentralizer L Y) =
      finrank F ↥(L.toSubmodule ⊓ LinearMap.ker (ad Y)) := fun Y => by
    rw [← lieCentralizer_toSubmodule_eq]; rfl
  rw [isOpen_iff_mem_nhds]
  intro Z₀ hZ₀
  obtain ⟨hss₀, hab₀⟩ := hZ₀
  have hcl₀ := lieClauses d g hg Z₀.2 hss₀
  have h₀ : finrank F (LinearMap.ker (f Z₀)) = lieRankNat d := by
    rw [hker, ker_pow_eq_ker_of_isSemisimple
      (LieAlgebra.ad_isSemisimple_of_isSemisimple_mulLeft hss₀) hD, ← hlie]
    exact hcl₀.2.1.mpr hab₀
  filter_upwards [eventually_finrank_ker_le f hf Z₀] with Z hZ
  rw [h₀] at hZ
  -- the Jordan decomposition `Z = s + n`
  obtain ⟨hZl, hZa⟩ := mem_lieCentralizer.mp Z.2
  obtain ⟨s, hs, n, hn, hss, hnil, hZsn⟩ := exists_jordan_algebra (F := F) (Z : d.ambient)
  have hsZ : Commute (Z : d.ambient) s := Algebra.commute_of_mem_adjoin_self hs
  have hsn : Commute s n := Algebra.commute_of_mem_adjoin_singleton_of_commute hn hsZ.symm
  have hfst : s.1 ∈ Algebra.adjoin F {(Z : d.ambient).1} :=
    AlgHom.map_adjoin_singleton (AlgHom.fst F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) _ ▸
      Subalgebra.mem_map.mpr ⟨s, hs, rfl⟩
  have hsnd : s.2 ∈ Algebra.adjoin F {(Z : d.ambient).2} :=
    AlgHom.map_adjoin_singleton (AlgHom.snd F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) _ ▸
      Subalgebra.mem_map.mpr ⟨s, hs, rfl⟩
  obtain ⟨k, hk⟩ := hnil
  have hn1 : IsNilpotent ((Z : d.ambient).1 - s.1) :=
    ⟨k, by rw [hZsn, Prod.fst_add, add_sub_cancel_left, ← Prod.pow_fst, hk, Prod.fst_zero]⟩
  have hn2 : IsNilpotent ((Z : d.ambient).2 - s.2) :=
    ⟨k, by rw [hZsn, Prod.snd_add, add_sub_cancel_left, ← Prod.pow_snd, hk, Prod.snd_zero]⟩
  have hsL : s ∈ L := mem_lieCentralizer.mpr
    ⟨⟨mem_gspin_of_mem_adjoin hZl.1 hfst
        (isSS_algHom (AlgHom.fst F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) hss) hn1,
      mem_gspin_of_mem_adjoin hZl.2 hsnd
        (isSS_algHom (AlgHom.snd F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) hss) hn2⟩,
      Algebra.commute_of_mem_adjoin_singleton_of_commute hs hZa⟩
  have hnL : n ∈ L := by
    have := L.sub_mem Z.2 hsL
    rwa [hZsn, add_sub_cancel_left] at this
  -- `𝔤_{g,s} ⊆ ker (ad Z)^D`
  have hle : finrank F (lieCentralizer L s) ≤ lieRankNat d := by
    refine le_trans ?_ ((hker Z).symm.trans_le hZ)
    rw [hlie]
    refine Submodule.finrank_mono (inf_le_inf_left _ ?_)
    have had : ad (Z : d.ambient) = ad s + ad n := by
      simp only [ad, hZsn, map_add]
    rw [had]
    exact ker_le_ker_pow_add (LieAlgebra.commute_ad_of_commute hsn)
      (LieAlgebra.ad_nilpotent_of_nilpotent ⟨k, hk⟩)
  have hcl := lieClauses d g hg hsL hss
  have heq : finrank F (lieCentralizer L s) = lieRankNat d := le_antisymm hle hcl.1
  have hn0 : n = 0 := hcl.2.2 heq n (mem_lieCentralizer.mpr ⟨hnL, hsn.eq⟩) ⟨k, hk⟩
  change IsRegularSS L (Z : d.ambient)
  rw [hZsn, hn0, add_zero]
  exact ⟨hss, hcl.2.1.mp heq⟩

end Assembly

section GroupAssembly

variable {F : Type*} [NontriviallyNormedField F] [CharZero F] (d : GGPData F)

/-- **Jordan decomposition in `G(F)`**: every `x ∈ G(F)` has `x = s + n` with `s ∈ G(F) ∩ F[x]`
semisimple and `n = x − s` nilpotent (`mem_GSpin_of_mem_adjoin` on each factor). -/
theorem exists_jordan_G (x : ↥d.G) :
    ∃ s : ↥d.G, ((s : d.ambientˣ) : d.ambient) ∈ Algebra.adjoin F {((x : d.ambientˣ) : d.ambient)} ∧
      IsSS F ((s : d.ambientˣ) : d.ambient) ∧
      IsNilpotent (((x : d.ambientˣ) : d.ambient) - ((s : d.ambientˣ) : d.ambient)) := by
  set a : d.ambient := ((x : d.ambientˣ) : d.ambient)
  obtain ⟨s, hs, hss, hn⟩ := exists_jordan_unit (F := F) (x : d.ambientˣ)
  have hxG := x.2
  simp only [GGPData.G, Subgroup.mem_comap, Subgroup.mem_prod] at hxG
  have hsG : s ∈ d.G := by
    simp only [GGPData.G, Subgroup.mem_comap, Subgroup.mem_prod]
    exact ⟨mem_GSpin_of_mem_adjoin hxG.1
        (AlgHom.map_adjoin_singleton
          (AlgHom.fst F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) a ▸
          Subalgebra.mem_map.mpr ⟨s, hs, rfl⟩)
        (isSS_algHom (AlgHom.fst F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) hss)
        (by
          change IsNilpotent (a.1 - (s : d.ambient).1)
          simpa using hn.map (AlgHom.fst F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV))),
      mem_GSpin_of_mem_adjoin hxG.2
        (AlgHom.map_adjoin_singleton
          (AlgHom.snd F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) a ▸
          Subalgebra.mem_map.mpr ⟨s, hs, rfl⟩)
        (isSS_algHom (AlgHom.snd F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) hss)
        (by
          change IsNilpotent (a.2 - (s : d.ambient).2)
          simpa using hn.map (AlgHom.snd F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)))⟩
  exact ⟨⟨s, hsG⟩, hs, hss, hn⟩

/-- **Small generalized fixed space implies regular semisimple** (`x ∈ G(F)`): if the generalized
`1`-eigenspace `𝔤 ∩ ker (1 − Ad x)^D` of `Ad x` on `𝔤` has dimension `≤ ℓ` (`D = dim C(W) × C(V)`;
`ℓ = lieRankNat d`), then `x` is regular semisimple. Proof: for the Jordan decomposition `x = s + n`
(`s ∈ F[x]`), `s` is a unit in `G(F)` (`exists_jordan_G`) and
`𝔤_s ⊆ ker (ad x)^D = ker (1 − Ad x)^D`, so `dim 𝔤_s = ℓ` (`lieClauses` with `Z = 0`) and `𝔤_s` is
abelian; the unipotent `u = s⁻¹x ∈ G(F)` commutes with `s`, so `u = 1`
(`eq_one_of_isNilpotent_sub_one_of_lieClauses`) and `x = s`. -/
theorem mem_regularSet_of_finrank_ker_le (x : ↥d.G)
    (hx : finrank F ↥(d.lie.toSubmodule ⊓ LinearMap.ker
      ((1 - (conjAd F (x : d.ambientˣ)).toLinearEquiv.toLinearMap) ^ finrank F d.ambient)) ≤
      lieRankNat d) :
    x ∈ regularSet d.G d.lie := by
  set a : d.ambient := ((x : d.ambientˣ) : d.ambient)
  rw [ker_one_sub_conjAd_pow] at hx
  obtain ⟨sG, hs, hss, hn⟩ := exists_jordan_G d x
  set s : d.ambientˣ := (sG : d.ambientˣ)
  set n : d.ambient := a - s
  have hcs : Commute a s := Algebra.commute_of_mem_adjoin_self hs
  have hasn : a = s + n := (add_sub_cancel _ _).symm
  have hnm : n ∈ Algebra.adjoin F {a} :=
    Subalgebra.sub_mem _ (Algebra.self_mem_adjoin_singleton F a) hs
  -- `𝔤_s ⊆ ker (ad x)^D`
  have hle : finrank F (lieCentralizer d.lie (s : d.ambient)) ≤ lieRankNat d := by
    refine le_trans ?_ hx
    have hlie : finrank F (lieCentralizer d.lie (s : d.ambient)) =
        finrank F ↥(d.lie.toSubmodule ⊓
          LinearMap.ker (LieAlgebra.ad F d.ambient (s : d.ambient))) :=
      by rw [← lieCentralizer_toSubmodule_eq]; rfl
    rw [hlie]
    refine Submodule.finrank_mono (inf_le_inf_left _ ?_)
    have had : LieAlgebra.ad F d.ambient a =
        LieAlgebra.ad F d.ambient (s : d.ambient) + LieAlgebra.ad F d.ambient n := by
      rw [hasn, map_add]
    rw [had]
    exact ker_le_ker_pow_add (LieAlgebra.commute_ad_of_commute
        (commute_of_mem_adjoin_singleton hs hnm))
      (LieAlgebra.ad_nilpotent_of_nilpotent hn)
  -- `dim 𝔤_s = ℓ`, `𝔤_s` abelian
  have h0 : (0 : d.ambient) ∈ lieCentralizer d.lie ((sG : d.ambientˣ) : d.ambient) := zero_mem _
  have hss0 : IsSS F (0 : d.ambient) := isSS_zero F
  have hcl := lieClauses d sG hss h0 hss0
  rw [lieCentralizer_zero] at hcl
  have heq : finrank F (lieCentralizer d.lie (s : d.ambient)) = lieRankNat d :=
    le_antisymm hle hcl.1
  -- `u = s⁻¹x` is unipotent and commutes with `s`, so `u = 1`
  have hsa : Commute (s : d.ambient) a := hcs.symm
  have hu := eq_one_of_isNilpotent_sub_one_of_lieClauses d sG hss h0 hss0
    (by rw [lieCentralizer_zero]; exact heq) (sG⁻¹ * x) (by
      change IsNilpotent (((s⁻¹ * (x : d.ambientˣ) : d.ambientˣ) : d.ambient) - 1)
      have h : (((s⁻¹ * (x : d.ambientˣ) : d.ambientˣ) : d.ambient) - 1) =
          ((s⁻¹ : d.ambientˣ) : d.ambient) * (a - s) := by
        rw [mul_sub, Units.inv_mul, Units.val_mul]
      rw [h]
      exact ((hsa.sub_right (Commute.refl _)).units_inv_left).isNilpotent_mul_left hn)
    (by
      change Commute (s : d.ambient) (((s⁻¹ * (x : d.ambientˣ) : d.ambientˣ) : d.ambient))
      rw [Units.val_mul]
      exact (Commute.refl _).units_inv_right.mul_right hsa)
    (Commute.zero_right _)
  have hxs : x = sG := (inv_mul_eq_one.mp hu).symm
  change IsRegularSS d.lie ((x : d.ambientˣ) : d.ambient)
  rw [hxs]
  exact ⟨hss, hcl.2.1.mp heq⟩

end GroupAssembly

end GSpinGGP
