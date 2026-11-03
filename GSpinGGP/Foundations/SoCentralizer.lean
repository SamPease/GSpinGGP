/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.GSpin
import GSpinGGP.Foundations.LocalGroups
import GSpinGGP.Foundations.MatrixBaseChange

/-!
# Centralizers in `so(V)` and `gspin(V)`

For a nondegenerate quadratic space `(V, q)` over a field of characteristic `≠ 2`, `so(V)` is the
Lie algebra of endomorphisms that are skew for the bilinear form `b` (Mathlib's
`LinearMap.skewAdjointSubmodule`), and `adV : gspin(V) → so(V)`, `X ↦ [X, ·]|_V`, is onto with
kernel the scalars (Thesis Prop. 5.1.3.1). So the centralizer of `X ∈ gspin(V)` has dimension
`1 + dim so(V)_{adV X}` (`finrank_lieCentralizer_gspin`).

* `finrank_lieCentralizer_gspin_unit`, `exists_mem_lieCentralizer_adV_eq`,
  `commute_of_isLieAbelian_lieCentralizer`: the same for the centralizer of `g ∈ GSpin(V)`, with
  `so(V)_{P(g)}`; `commute_of_lift`: a lift of `M ∈ so(V)_{P(g)}` commutes with `g`.

* `finrank_lieCentralizer_fixed`: `dim gspin(V)_{y,Y}` through the fixed space `A = W'_y`;
  `soCent_inf_killSub_congr`: the part killing `A` only sees `adV Y` on `A^⊥` (so the
  `A`-component of `Y` can be changed freely: `exists_lieCentralizer_fixed_swap` in `SoSplit`).
* `finrank_soCent_le_of_chain`: an upper bound for `dim so(V)_N` when `N` has a long Jordan chain;
  `isTotallyIsotropic_span_pow`: the upper half of a Jordan chain of a skew `N` is totally isotropic.
* `linearIndependent_pow_apply`, `exists_pow_apply_ne_zero_of_isNilpotent`: Jordan chains of a
  nilpotent endomorphism.
* `soCentMat`, `soCentMat_toMatrix`: the same in matrix form; `ker_jointMatMap`: `so(J)_A ⊓ so(J)_C`
  is the kernel of a linear map of matrices. So `finrank_soCentMat_map`: its dimension does not
  change under extension of scalars; `soCentMat_map_eq_span`: over an extension it is spanned by
  its `F`-points.
-/

noncomputable section

open CliffordAlgebra Module

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

/-! ## `adV : gspin(V) → so(V)` -/

section AdV

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- `adV(ι a ι b) v = polar(b, v) a − polar(a, v) b`. -/
theorem adV_ι_mul_ι (Q : QuadraticForm K V) (a b v : V) :
    adV Q (ι Q a * ι Q b) v =
      QuadraticMap.polar Q b v • a - QuadraticMap.polar Q a v • b := by
  apply ι_injective Q
  rw [ι_adV (ι_mul_ι_mem_gspin Q a b), ι_mul_ι_commutator]

theorem adV_algebraMap (Q : QuadraticForm K V) (r : K) : adV Q (algebraMap K _ r) = 0 := by
  ext v; simp [adV_apply, Algebra.commutes]

/-- `adV` is a Lie algebra map on `gspin(V)`. -/
theorem adV_commutator {Q : QuadraticForm K V} {X Y : CliffordAlgebra Q} (hX : X ∈ gspin Q)
    (hY : Y ∈ gspin Q) : adV Q (X * Y - Y * X) = adV Q X * adV Q Y - adV Q Y * adV Q X := by
  have hXY : X * Y - Y * X ∈ gspin Q := by
    have := (gspin Q).lie_mem hX hY; rwa [Ring.lie_def] at this
  ext v
  apply ι_injective Q
  rw [ι_adV hXY, LinearMap.sub_apply, map_sub, Module.End.mul_apply, Module.End.mul_apply,
    ι_adV hX (adV Q Y v), ι_adV hY (adV Q X v), ι_adV hY v, ι_adV hX v]
  noncomm_ring

/-- The kernel of `adV` on `gspin(V)` is the scalars (`V` nondegenerate, finite-dimensional). -/
theorem eq_algebraMap_of_adV_eq_zero [Module.Finite K V] {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    {X : CliffordAlgebra Q} (hX : X ∈ gspin Q) (h0 : adV Q X = 0) :
    ∃ r : K, X = algebraMap K _ r := by
  refine eq_algebraMap_of_commute_ι hQ (by rw [← even_toSubmodule]; exact hX.1) fun v => ?_
  have := ι_adV hX v
  rw [h0, LinearMap.zero_apply, map_zero] at this
  exact (sub_eq_zero.mp this.symm).symm

/-- `so(V)_N`: the endomorphisms that are skew for `b` and commute with `N`. -/
def soCent (Q : QuadraticForm K V) (N : Module.End K V) : Submodule K (Module.End K V) :=
  (bform Q).skewAdjointSubmodule ⊓ (Subalgebra.centralizer K {N}).toSubmodule

theorem mem_soCent {Q : QuadraticForm K V} {N M : Module.End K V} :
    M ∈ soCent Q N ↔ (∀ u w, bform Q (M u) w = -bform Q u (M w)) ∧ M * N = N * M := by
  simp only [soCent, Submodule.mem_inf, LinearMap.mem_skewAdjointSubmodule,
    Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq, LinearMap.IsSkewAdjoint, LinearMap.IsAdjointPair, Pi.neg_apply, map_neg]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩

end AdV

section Trace

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The trace `x ↦ tr(L_x)` of left multiplication on `C(V)`. -/
abbrev cliffTrace [Module.Finite K V] (Q : QuadraticForm K V) (x : CliffordAlgebra Q) : K :=
  LinearMap.trace K _ (LinearMap.mulLeft K x)

omit [Invertible (2 : K)] in
theorem cliffTrace_add [Module.Finite K V] (Q : QuadraticForm K V) (x y : CliffordAlgebra Q) :
    cliffTrace Q (x + y) = cliffTrace Q x + cliffTrace Q y := by
  have e : LinearMap.mulLeft K (x + y) = LinearMap.mulLeft K x + LinearMap.mulLeft K y := by
    ext z; simp [add_mul]
  simp only [cliffTrace, e, map_add]

omit [Invertible (2 : K)] in
theorem cliffTrace_smul [Module.Finite K V] (Q : QuadraticForm K V) (c : K) (x : CliffordAlgebra Q) :
    cliffTrace Q (c • x) = c * cliffTrace Q x := by
  have e : LinearMap.mulLeft K (c • x) = c • LinearMap.mulLeft K x := by
    ext z; simp
  simp only [cliffTrace, e, map_smul, smul_eq_mul]

theorem cliffTrace_one [Module.Finite K V] (Q : QuadraticForm K V) :
    cliffTrace Q 1 = (finrank K (CliffordAlgebra Q) : K) := by
  simp only [cliffTrace, LinearMap.mulLeft_one]
  exact LinearMap.trace_id K _

omit [Invertible (2 : K)] in
theorem cliffTrace_commutator [Module.Finite K V] (Q : QuadraticForm K V) (x y : CliffordAlgebra Q) :
    cliffTrace Q (x * y - y * x) = 0 := by
  rw [sub_eq_add_neg, cliffTrace_add, ← neg_one_smul K (y * x), cliffTrace_smul,
    show cliffTrace Q (x * y) = cliffTrace Q (y * x) from trace_mulLeft_comm Q x y]
  ring

end Trace

section Centralizer

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **`adV` maps `gspin(V)` onto `so(V)`**: every `b`-skew `M` is `adV Y` for some `Y ∈ gspin(V)`
(a combination of bivectors, Tau Ceti's `soEquivQuadratic`). -/
theorem exists_mem_gspin_adV_eq {Q : QuadraticForm K V} (hQ : IsNondeg Q) (M : Module.End K V)
    (hMs : ∀ u w, bform Q (M u) w = -bform Q u (M w)) : ∃ Y ∈ gspin Q, adV Q Y = M := by
  obtain ⟨Y, hYq, hY⟩ := exists_mem_quadratic_commutator_eq hQ M hMs
  have hYg : Y ∈ gspin Q := by
    refine quadraticLieSubalgebra_toSubmodule_le_of_bivector_mem Q (P := (gspin Q).toSubmodule)
      (fun a b => ?_) hYq
    rw [bivector_def]
    exact (gspin Q).smul_mem _ (Submodule.sub_mem (gspin Q).toSubmodule
      (ι_mul_ι_mem_gspin Q a b) (ι_mul_ι_mem_gspin Q b a))
  exact ⟨Y, hYg, by ext v; apply ι_injective Q; rw [ι_adV hYg, hY]⟩

/-- **`dim gspin(V)_X = 1 + dim so(V)_{adV X}`** (Thesis Prop. 5.1.3.1: `gspin(V) = so(V) ⊕ K`).
`Y ↦ adV Y` maps `gspin(V)_X` onto `so(V)_{adV X}` with kernel the scalars: a lift `Y` of
`M ∈ so(V)_{adV X}` has `[Y, X]` scalar and traceless on `C(V)`, hence `0`. -/
theorem finrank_lieCentralizer_gspin {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    {X : CliffordAlgebra Q} (hX : X ∈ gspin Q) :
    finrank K (lieCentralizer (gspin Q) X) = finrank K (soCent Q (adV Q X)) + 1 := by
  have hcomm : ∀ Y : lieCentralizer (gspin Q) X, adV Q (Y : CliffordAlgebra Q) * adV Q X =
      adV Q X * adV Q (Y : CliffordAlgebra Q) := by
    intro ⟨Y, hY⟩
    obtain ⟨hYg, hYX⟩ := mem_lieCentralizer.mp hY
    have := adV_commutator hYg hX
    rw [hYX, sub_self, show adV Q 0 = 0 from map_zero (adV Q)] at this
    exact (sub_eq_zero.mp this.symm)
  let φ : lieCentralizer (gspin Q) X →ₗ[K] soCent Q (adV Q X) :=
    { toFun := fun Y => ⟨adV Q Y, mem_soCent.2 ⟨bform_adV (mem_lieCentralizer.mp Y.2).1, hcomm Y⟩⟩
      map_add' := fun Y Z => Subtype.ext (map_add (adV Q) Y.1 Z.1)
      map_smul' := fun c Y => Subtype.ext (map_smul (adV Q) c Y.1) }
  have hsurj : Function.Surjective φ := by
    rintro ⟨M, hM⟩
    obtain ⟨hMs, hMN⟩ := mem_soCent.mp hM
    obtain ⟨Y, hYg, hYM⟩ := exists_mem_gspin_adV_eq hQ M hMs
    have hC : Y * X - X * Y ∈ gspin Q := by
      have := (gspin Q).lie_mem hYg hX; rwa [Ring.lie_def] at this
    obtain ⟨r, hr⟩ := eq_algebraMap_of_adV_eq_zero hQ hC (by rw [adV_commutator hYg hX, hYM, hMN, sub_self])
    have htr : LinearMap.trace K _ (LinearMap.mulLeft K (Y * X - X * Y)) = 0 := by
      rw [show LinearMap.mulLeft K (Y * X - X * Y) =
          LinearMap.mulLeft K (Y * X) - LinearMap.mulLeft K (X * Y) by ext; simp [sub_mul, mul_assoc],
        map_sub, trace_mulLeft_comm, sub_self]
    have hsc : ∀ r : K, LinearMap.mulLeft K (algebraMap K (CliffordAlgebra Q) r) = r • LinearMap.id := by
      intro r; ext z; simp [Algebra.smul_def]
    rw [hr, hsc, map_smul, LinearMap.trace_id, smul_eq_mul] at htr
    have hr0 : r = 0 := (mul_eq_zero.mp htr).resolve_right (cast_finrank_cliffordAlgebra_ne_zero Q)
    rw [hr0, map_zero, sub_eq_zero] at hr
    exact ⟨⟨Y, mem_lieCentralizer.2 ⟨hYg, hr.symm⟩⟩, Subtype.ext hYM⟩
  have hker : finrank K (LinearMap.ker φ) = 1 := by
    have h1 : (1 : CliffordAlgebra Q) ∈ lieCentralizer (gspin Q) X :=
      mem_lieCentralizer.2 ⟨one_mem_gspin Q, by rw [one_mul, mul_one]⟩
    let e : LinearMap.ker φ := ⟨⟨1, h1⟩, Subtype.ext (by
      show adV Q 1 = 0
      rw [← map_one (algebraMap K (CliffordAlgebra Q)), adV_algebraMap])⟩
    have he : e ≠ 0 := fun h => one_ne_zero (congrArg (fun z : LinearMap.ker φ => ((z : _) : CliffordAlgebra Q)) h)
    refine (finrank_eq_one_iff_of_nonzero' e he).2 fun ⟨⟨Y, hY⟩, hYk⟩ => ?_
    have hY0 : adV Q Y = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hYk)
    obtain ⟨r, rfl⟩ := eq_algebraMap_of_adV_eq_zero hQ (mem_lieCentralizer.mp hY).1 hY0
    exact ⟨r, Subtype.ext (Subtype.ext (by simp [e, Algebra.algebraMap_eq_smul_one]))⟩
  rw [← LinearMap.finrank_range_add_finrank_ker φ, LinearMap.range_eq_top.2 hsurj, finrank_top, hker]

/-- **The lift commutes with `g`** when `P(g)` commutes with `Y`: `g Ŷ g⁻¹ − Ŷ` is even and commutes
with `ι(V)`, hence a scalar, and it is traceless. -/
theorem commute_of_lift {Q : QuadraticForm K V} (hQ : IsNondeg Q) (g : GSpin Q) {Y : Module.End K V}
    (hYc : Commute (specP Q g : V →ₗ[K] V) Y) {Yh : CliffordAlgebra Q} (hYh0 : Yh ∈ gspin Q)
    (hYh : ∀ v, Yh * ι Q v - ι Q v * Yh = ι Q (Y v)) :
    ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * Yh =
      Yh * ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  set a : CliffordAlgebra Q := ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  set b : CliffordAlgebra Q :=
    (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  have hba : b * a = 1 := Units.inv_mul _
  have hab : a * b = 1 := Units.mul_inv _
  have hb0 : b ∈ even Q := (g⁻¹ : GSpin Q).2.1
  set D := a * Yh * b - Yh with hD
  have hDc : ∀ v, ι Q v * D = D * ι Q v := by
    intro v
    set u := specP Q g⁻¹ v
    have hv : ι Q v = a * ι Q u * b := by
      rw [← ι_specP, specP_inv_apply_apply]
    have hYv : Y v = specP Q g (Y u) := by
      have := LinearMap.congr_fun hYc.eq u
      simp only [Module.End.mul_apply, LinearEquiv.coe_coe] at this
      rw [this, specP_inv_apply_apply]
    have e1 : a * Yh * b * (a * ι Q u * b) = a * (Yh * ι Q u) * b := by
      simp only [mul_assoc]; rw [← mul_assoc b a, hba, one_mul]
    have e2 : a * ι Q u * b * (a * Yh * b) = a * (ι Q u * Yh) * b := by
      simp only [mul_assoc]; rw [← mul_assoc b a, hba, one_mul]
    have h1 : a * Yh * b * ι Q v - ι Q v * (a * Yh * b) = ι Q (Y v) := by
      rw [hv, e1, e2, ← sub_mul, ← mul_sub, hYh, hYv, ι_specP]
    have h2 := hYh v
    rw [hD, mul_sub, sub_mul]
    rw [← sub_eq_zero]
    rw [show ι Q v * (a * Yh * b) - ι Q v * Yh - (a * Yh * b * ι Q v - Yh * ι Q v) =
      (Yh * ι Q v - ι Q v * Yh) - (a * Yh * b * ι Q v - ι Q v * (a * Yh * b)) by abel, h1, h2,
      sub_self]
  have hD0 : D ∈ evenOdd Q 0 := by
    rw [← even_toSubmodule]
    exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ g.2.1 hYh0.1) hb0)
      hYh0.1
  obtain ⟨r, hr⟩ := eq_algebraMap_of_commute_ι hQ hD0 hDc
  have htr : cliffTrace Q D = 0 := by
    rw [hD, sub_eq_add_neg, cliffTrace_add,
      show cliffTrace Q (a * Yh * b) = cliffTrace Q (b * (a * Yh)) from trace_mulLeft_comm Q _ _,
      ← mul_assoc, hba, one_mul, ← neg_one_smul K Yh, cliffTrace_smul]
    ring
  have hr0 : r = 0 := by
    rw [hr, Algebra.algebraMap_eq_smul_one, cliffTrace_smul, cliffTrace_one] at htr
    exact (mul_eq_zero.mp htr).resolve_right (cast_finrank_cliffordAlgebra_ne_zero Q)
  have hD' : a * Yh * b = Yh := by
    rw [← sub_eq_zero, ← hD, hr, hr0, map_zero]
  calc a * Yh = a * Yh * b * a := by rw [mul_assoc _ b, hba, mul_one]
    _ = Yh * a := by rw [hD']

/-- **Lifting `so(V)_{P(g)}` to `gspin(V)_g`**: for `g ∈ GSpin(V)`, every `M ∈ so(V)_{P(g)}` is
`adV Y` for some `Y ∈ gspin(V)` commuting with `g` (a lift by `exists_mem_gspin_adV_eq`,
which commutes with `g` by `commute_of_lift`). -/
theorem exists_mem_lieCentralizer_adV_eq {Q : QuadraticForm K V} (hQ : IsNondeg Q) (g : GSpin Q)
    {M : Module.End K V} (hM : M ∈ soCent Q (specP Q g : Module.End K V)) :
    ∃ Y ∈ lieCentralizer (gspin Q) ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q),
      adV Q Y = M := by
  obtain ⟨hMs, hMN⟩ := mem_soCent.mp hM
  obtain ⟨Y, hYg, rfl⟩ := exists_mem_gspin_adV_eq hQ M hMs
  exact ⟨Y, mem_lieCentralizer.2 ⟨hYg, commute_of_lift hQ g hMN.symm hYg
    fun v => (ι_adV hYg v).symm⟩, rfl⟩

/-- **`dim gspin(V)_g = 1 + dim so(V)_{P(g)}`** for `g ∈ GSpin(V)` (via Thesis Prop. 5.1.3.1,
`gspin(V) = so(V) ⊕ K`; `Ad g` acts as `P(g)` on `so(V)`): `Y ↦ adV Y` maps `gspin(V)_g` onto
`so(V)_{P(g)}` (`exists_mem_lieCentralizer_adV_eq`) with kernel the scalars. -/
theorem finrank_lieCentralizer_gspin_unit {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    (g : GSpin Q) :
    finrank K (lieCentralizer (gspin Q) ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) =
      finrank K (soCent Q (specP Q g : Module.End K V)) + 1 := by
  obtain ⟨u, hu⟩ : ∃ u : (CliffordAlgebra Q)ˣ, u = g := ⟨_, rfl⟩
  -- `adV` of a `g`-commuting element commutes with `P(g)`
  have hcomm : ∀ Y ∈ gspin Q, (u : CliffordAlgebra Q) * Y = Y * u →
      adV Q Y * (specP Q g : Module.End K V) = (specP Q g : Module.End K V) * adV Q Y := by
    intro Y hY hYu
    have hYu' : ((u⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * Y =
        Y * ((u⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
      rw [Units.inv_mul_eq_iff_eq_mul, ← mul_assoc, hYu, mul_assoc, Units.mul_inv, mul_one]
    ext v
    apply ι_injective Q
    simp only [Module.End.mul_apply, LinearEquiv.coe_coe]
    rw [ι_adV hY, ι_specP, ι_specP, ι_adV hY, ← hu]
    simp only [mul_sub, sub_mul, mul_assoc]
    rw [← mul_assoc Y (u : CliffordAlgebra Q), ← hYu, hYu', ← mul_assoc (u : CliffordAlgebra Q) Y]
  rw [← hu]
  let φ : lieCentralizer (gspin Q) (u : CliffordAlgebra Q) →ₗ[K]
      soCent Q (specP Q g : Module.End K V) :=
    { toFun := fun Y => ⟨adV Q Y, mem_soCent.2 ⟨bform_adV (mem_lieCentralizer.mp Y.2).1,
        hcomm Y (mem_lieCentralizer.mp Y.2).1 (mem_lieCentralizer.mp Y.2).2⟩⟩
      map_add' := fun Y Z => Subtype.ext (map_add (adV Q) Y.1 Z.1)
      map_smul' := fun c Y => Subtype.ext (map_smul (adV Q) c Y.1) }
  have hsurj : Function.Surjective φ := by
    rintro ⟨M, hM⟩
    obtain ⟨Y, hY, hYM⟩ := exists_mem_lieCentralizer_adV_eq hQ g hM
    rw [← hu] at hY
    exact ⟨⟨Y, hY⟩, Subtype.ext hYM⟩
  have hker : finrank K (LinearMap.ker φ) = 1 := by
    have h1 : (1 : CliffordAlgebra Q) ∈ lieCentralizer (gspin Q) (u : CliffordAlgebra Q) :=
      mem_lieCentralizer.2 ⟨one_mem_gspin Q, by rw [one_mul, mul_one]⟩
    let e : LinearMap.ker φ := ⟨⟨1, h1⟩, Subtype.ext (by
      change adV Q 1 = 0
      rw [← map_one (algebraMap K (CliffordAlgebra Q)), adV_algebraMap])⟩
    have he : e ≠ 0 := fun h =>
      one_ne_zero (congrArg (fun z : LinearMap.ker φ => ((z : _) : CliffordAlgebra Q)) h)
    refine (finrank_eq_one_iff_of_nonzero' e he).2 fun ⟨⟨Y, hY⟩, hYk⟩ => ?_
    have hY0 : adV Q Y = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hYk)
    obtain ⟨r, rfl⟩ := eq_algebraMap_of_adV_eq_zero hQ (mem_lieCentralizer.mp hY).1 hY0
    exact ⟨r, Subtype.ext (Subtype.ext (by simp [e, Algebra.algebraMap_eq_smul_one]))⟩
  rw [← LinearMap.finrank_range_add_finrank_ker φ, LinearMap.range_eq_top.2 hsurj, finrank_top,
    hker]

/-- If `gspin(V)_g` is abelian, so is `so(V)_{P(g)}`: `adV` maps `gspin(V)_g` onto it and preserves
commutators. -/
theorem commute_of_isLieAbelian_lieCentralizer {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    (g : GSpin Q)
    (hab : IsLieAbelian
      (lieCentralizer (gspin Q) ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))) :
    ∀ M₁ ∈ soCent Q (specP Q g : Module.End K V), ∀ M₂ ∈ soCent Q (specP Q g : Module.End K V),
      Commute M₁ M₂ := by
  intro M₁ h₁ M₂ h₂
  obtain ⟨Y₁, hY₁, rfl⟩ := exists_mem_lieCentralizer_adV_eq hQ g h₁
  obtain ⟨Y₂, hY₂, rfl⟩ := exists_mem_lieCentralizer_adV_eq hQ g h₂
  have h0 := congrArg Subtype.val (hab.trivial ⟨Y₁, hY₁⟩ ⟨Y₂, hY₂⟩)
  rw [LieSubalgebra.coe_bracket, Ring.lie_def] at h0
  have := adV_commutator (mem_lieCentralizer.mp hY₁).1 (mem_lieCentralizer.mp hY₂).1
  rw [h0, ZeroMemClass.coe_zero, map_zero, eq_comm, sub_eq_zero] at this
  exact this

/-- **Elements of `gspin(V)` commute iff their images in `so(V)` do**: the commutator is then a
scalar (`eq_algebraMap_of_adV_eq_zero`) with trace `0` on `C(V)`, hence `0`. -/
theorem commute_of_adV_commute {Q : QuadraticForm K V} (hQ : IsNondeg Q) {Z Y : CliffordAlgebra Q}
    (hZ : Z ∈ gspin Q) (hY : Y ∈ gspin Q) (h : adV Q Z * adV Q Y = adV Q Y * adV Q Z) :
    Z * Y = Y * Z := by
  have hC : Z * Y - Y * Z ∈ gspin Q := by
    have := (gspin Q).lie_mem hZ hY; rwa [Ring.lie_def] at this
  obtain ⟨r, hr⟩ := eq_algebraMap_of_adV_eq_zero hQ hC (by rw [adV_commutator hZ hY, h, sub_self])
  have htr : LinearMap.trace K _ (LinearMap.mulLeft K (Z * Y - Y * Z)) = 0 := by
    rw [show LinearMap.mulLeft K (Z * Y - Y * Z) =
        LinearMap.mulLeft K (Z * Y) - LinearMap.mulLeft K (Y * Z) by ext; simp [sub_mul, mul_assoc],
      map_sub, trace_mulLeft_comm, sub_self]
  have hsc : LinearMap.mulLeft K (algebraMap K (CliffordAlgebra Q) r) = r • LinearMap.id := by
    ext z; simp [Algebra.smul_def]
  rw [hr, hsc, map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  have hr0 : r = 0 := (mul_eq_zero.mp htr).resolve_right (cast_finrank_cliffordAlgebra_ne_zero Q)
  rw [hr0, map_zero, sub_eq_zero] at hr
  exact hr

omit [FiniteDimensional K V] in
/-- `adV(g A g⁻¹) = P(g) ∘ adV A ∘ P(g)⁻¹` for `g ∈ GSpin(V)`, `A ∈ gspin(V)`. -/
theorem adV_conj {Q : QuadraticForm K V} (g : GSpin Q) {A : CliffordAlgebra Q} (hA : A ∈ gspin Q)
    (v : V) :
    adV Q (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * A *
      (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) v =
      specP Q g (adV Q A (specP Q g⁻¹ v)) := by
  apply ι_injective Q
  rw [ι_adV (conj_mem_gspin Q g hA), ι_specP, ι_adV hA, ι_specP]
  simp only [Subgroup.coe_inv, inv_inv, mul_sub, sub_mul, mul_assoc, Units.mul_inv, mul_one,
    Units.mul_inv_cancel_left]

/-- For `A ∈ gspin(V)`: `A` commutes with `g ∈ GSpin(V)` iff `adV A` commutes with `P(g)`
(`⇐` is `commute_of_lift`). -/
theorem commute_iff_adV {Q : QuadraticForm K V} (hQ : IsNondeg Q) (g : GSpin Q)
    {A : CliffordAlgebra Q} (hA : A ∈ gspin Q) :
    ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * A =
        A * ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ↔
      (specP Q g : Module.End K V) * adV Q A = adV Q A * (specP Q g : Module.End K V) := by
  set u : (CliffordAlgebra Q)ˣ := (g : (CliffordAlgebra Q)ˣ)
  have hconj : ∀ v, adV Q ((u : CliffordAlgebra Q) * A * ((u⁻¹ : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q)) v = specP Q g (adV Q A (specP Q g⁻¹ v)) := adV_conj g hA
  have hinv : ∀ v, specP Q g⁻¹ (specP Q g v) = v := fun v => by simp
  constructor
  · intro h
    have e : (u : CliffordAlgebra Q) * A * ((u⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = A := by
      rw [h, mul_assoc, Units.mul_inv, mul_one]
    ext v
    have := hconj (specP Q g v)
    rw [e, hinv] at this
    exact this.symm
  · intro h
    exact commute_of_lift hQ g h hA fun v => (ι_adV hA v).symm

/-- `adV` maps `gspin(V)_{g,Y}` into `so(V)_{P(g)} ⊓ so(V)_{adV Y}`. -/
theorem adV_mem_soCent_inf {Q : QuadraticForm K V} (hQ : IsNondeg Q) (g : GSpin Q)
    {Y : CliffordAlgebra Q} (hYg : Y ∈ gspin Q) {Z : CliffordAlgebra Q}
    (hZ : Z ∈ lieCentralizer (lieCentralizer (gspin Q)
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) Y) :
    adV Q Z ∈ soCent Q (specP Q g : Module.End K V) ⊓ soCent Q (adV Q Y) := by
  obtain ⟨hZ', hYZ⟩ := mem_lieCentralizer.mp hZ
  obtain ⟨hZg, hxZ⟩ := mem_lieCentralizer.mp hZ'
  have hc := adV_commutator hZg hYg
  rw [← hYZ, sub_self, map_zero, eq_comm, sub_eq_zero] at hc
  exact Submodule.mem_inf.mpr
    ⟨mem_soCent.2 ⟨bform_adV hZg, ((commute_iff_adV hQ g hZg).mp hxZ).symm⟩,
      mem_soCent.2 ⟨bform_adV hZg, hc⟩⟩

/-- Every element of `so(V)_{P(g)} ⊓ so(V)_{adV Y}` is `adV Z` for some `Z ∈ gspin(V)_{g,Y}`. -/
theorem exists_mem_lieCentralizer_lieCentralizer_adV_eq {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    (g : GSpin Q) {Y : CliffordAlgebra Q} (hYg : Y ∈ gspin Q) {M : Module.End K V}
    (hM : M ∈ soCent Q (specP Q g : Module.End K V) ⊓ soCent Q (adV Q Y)) :
    ∃ Z ∈ lieCentralizer (lieCentralizer (gspin Q)
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) Y, adV Q Z = M := by
  obtain ⟨hMg, hMN⟩ := Submodule.mem_inf.mp hM
  obtain ⟨hMs, hMgc⟩ := mem_soCent.mp hMg
  obtain ⟨-, hMNc⟩ := mem_soCent.mp hMN
  obtain ⟨Z, hZg, rfl⟩ := exists_mem_gspin_adV_eq hQ M hMs
  have hZY : Z * Y = Y * Z := commute_of_adV_commute hQ hZg hYg hMNc
  have hxZ := (commute_iff_adV hQ g hZg).mpr hMgc.symm
  exact ⟨Z, mem_lieCentralizer.mpr ⟨mem_lieCentralizer.mpr ⟨hZg, hxZ⟩, hZY.symm⟩, rfl⟩

/-- `gspin(V)_{g,Y}` is abelian iff `so(V)_{P(g)} ⊓ so(V)_{adV Y}` is. -/
theorem isLieAbelian_lieCentralizer_gspin_iff {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    (g : GSpin Q) {Y : CliffordAlgebra Q} (hYg : Y ∈ gspin Q) :
    IsLieAbelian (lieCentralizer (lieCentralizer (gspin Q)
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) Y) ↔
    ∀ M₁ ∈ soCent Q (specP Q g : Module.End K V) ⊓ soCent Q (adV Q Y),
      ∀ M₂ ∈ soCent Q (specP Q g : Module.End K V) ⊓ soCent Q (adV Q Y), Commute M₁ M₂ := by
  rw [isLieAbelian_iff_forall_commute]
  constructor
  · intro hab M₁ h₁ M₂ h₂
    obtain ⟨Z₁, hZ₁, rfl⟩ := exists_mem_lieCentralizer_lieCentralizer_adV_eq hQ g hYg h₁
    obtain ⟨Z₂, hZ₂, rfl⟩ := exists_mem_lieCentralizer_lieCentralizer_adV_eq hQ g hYg h₂
    have := adV_commutator (mem_lieCentralizer.mp (mem_lieCentralizer.mp hZ₁).1).1
      (mem_lieCentralizer.mp (mem_lieCentralizer.mp hZ₂).1).1
    rw [hab _ hZ₁ _ hZ₂, sub_self, map_zero, eq_comm, sub_eq_zero] at this
    exact this
  · intro hab Z₁ h₁ Z₂ h₂
    exact commute_of_adV_commute hQ (mem_lieCentralizer.mp (mem_lieCentralizer.mp h₁).1).1
      (mem_lieCentralizer.mp (mem_lieCentralizer.mp h₂).1).1
      (hab _ (adV_mem_soCent_inf hQ g hYg h₁) _ (adV_mem_soCent_inf hQ g hYg h₂)).eq

/-- **`dim gspin(V)_{g,Y} = 1 + dim so(V)_{P(g), adV Y}`** for `g ∈ GSpin(V)` and `Y ∈ gspin(V)`:
`adV` maps the joint centralizer onto the joint centralizer of `P(g)` and `adV Y` in `so(V)`
(`commute_iff_adV`, `commute_of_adV_commute`), with kernel the scalars. -/
theorem finrank_lieCentralizer_lieCentralizer_gspin {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    (g : GSpin Q) {Y : CliffordAlgebra Q} (hY : Y ∈ gspin Q) :
    finrank K (lieCentralizer (lieCentralizer (gspin Q) ((g : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q)) Y) =
      finrank K ↥(soCent Q (specP Q g : Module.End K V) ⊓ soCent Q (adV Q Y)) + 1 := by
  set x : CliffordAlgebra Q := ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  have hmem : ∀ {Z}, Z ∈ lieCentralizer (lieCentralizer (gspin Q) x) Y ↔
      Z ∈ gspin Q ∧ x * Z = Z * x ∧ Y * Z = Z * Y := by
    intro Z; rw [mem_lieCentralizer, mem_lieCentralizer, and_assoc]
  let φ : lieCentralizer (lieCentralizer (gspin Q) x) Y →ₗ[K]
      ↥(soCent Q (specP Q g : Module.End K V) ⊓ soCent Q (adV Q Y)) :=
    { toFun := fun Z => ⟨adV Q Z, adV_mem_soCent_inf hQ g hY Z.2⟩
      map_add' := fun Y Z => Subtype.ext (map_add (adV Q) Y.1 Z.1)
      map_smul' := fun c Y => Subtype.ext (map_smul (adV Q) c Y.1) }
  have hsurj : Function.Surjective φ := by
    rintro ⟨M, hM⟩
    obtain ⟨Z, hZ, hZM⟩ := exists_mem_lieCentralizer_lieCentralizer_adV_eq hQ g hY hM
    exact ⟨⟨Z, hZ⟩, Subtype.ext hZM⟩
  have hker : finrank K (LinearMap.ker φ) = 1 := by
    have h1 : (1 : CliffordAlgebra Q) ∈ lieCentralizer (lieCentralizer (gspin Q) x) Y :=
      hmem.mpr ⟨one_mem_gspin Q, by rw [one_mul, mul_one], by rw [one_mul, mul_one]⟩
    let e : LinearMap.ker φ := ⟨⟨1, h1⟩, Subtype.ext (by
      show adV Q 1 = 0
      rw [← map_one (algebraMap K (CliffordAlgebra Q)), adV_algebraMap])⟩
    have he : e ≠ 0 := fun h =>
      one_ne_zero (congrArg (fun z : LinearMap.ker φ => (z.1.1 : CliffordAlgebra Q)) h)
    refine (finrank_eq_one_iff_of_nonzero' e he).2 fun ⟨⟨Z, hZ⟩, hZk⟩ => ?_
    have hZ0 : adV Q Z = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hZk)
    obtain ⟨r, rfl⟩ := eq_algebraMap_of_adV_eq_zero hQ (hmem.mp hZ).1 hZ0
    exact ⟨r, Subtype.ext (Subtype.ext (by simp [e, Algebra.algebraMap_eq_smul_one]))⟩
  rw [← LinearMap.finrank_range_add_finrank_ker φ, LinearMap.range_eq_top.2 hsurj, finrank_top, hker]

end Centralizer

/-! ## Splitting off the fixed space of an isometry -/

section Fixed

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The endomorphisms killing `A` (the kernel of `M ↦ M ∘ A.subtype`). -/
def killSub (A : Submodule K V) : Submodule K (Module.End K V) where
  carrier := {M | ∀ a ∈ A, M a = 0}
  add_mem' hM hN a ha := by rw [LinearMap.add_apply, hM a ha, hN a ha, add_zero]
  zero_mem' a _ := rfl
  smul_mem' c M hM a ha := by rw [LinearMap.smul_apply, hM a ha, smul_zero]

omit [FiniteDimensional K V] in
theorem bform_comp_subtype (Q : QuadraticForm K V) (A : Submodule K V) (a b : A) :
    bform (Q.comp A.subtype) a b = bform Q a b := by
  simp [bform, QuadraticMap.associated_comp]

/-- **`so(V)_{g,N} = so(A)_{N|A} ⊕ (the part killing A)`** for the fixed space `A = ker(g − 1)` of
an isometry `g` with `V = A ⊥ A^⊥`, and `N ∈ so(V)_g`: restriction to `A` maps `so(V)_{g,N}` onto
`so(A)_{N|A}` (extend by `0` on `A^⊥`), with kernel the elements killing `A`. -/
theorem finrank_soCent_inf_eq {Q : QuadraticForm K V} {g N : Module.End K V} {A : Submodule K V}
    (hA : IsCompl A ((bform Q).orthogonal A)) (hAg : ∀ v, v ∈ A ↔ g v = v)
    (hgB : ∀ b ∈ (bform Q).orthogonal A, g b ∈ (bform Q).orthogonal A)
    (hNs : ∀ u w, bform Q (N u) w = -bform Q u (N w)) (hNg : N * g = g * N) :
    finrank K ↥(soCent Q g ⊓ soCent Q N) =
      finrank K ↥(soCent (Q.comp A.subtype) (N.restrict (p := A) (q := A) fun a ha =>
        (hAg _).2 (by rw [← Module.End.mul_apply, ← hNg, Module.End.mul_apply, (hAg a).1 ha]))) +
      finrank K ↥(soCent Q g ⊓ soCent Q N ⊓ killSub A) := by
  set B := (bform Q).orthogonal A
  have hsymm : ∀ x y, bform Q x y = bform Q y x := fun x y => QuadraticMap.associated_isSymm K Q x y
  -- elements commuting with `g` preserve `A`
  have hpres : ∀ M : Module.End K V, M * g = g * M → ∀ a ∈ A, M a ∈ A := fun M hM a ha =>
    (hAg _).2 (by rw [← Module.End.mul_apply, ← hM, Module.End.mul_apply, (hAg a).1 ha])
  have hNA := hpres N hNg
  set NA : Module.End K A := N.restrict (p := A) (q := A) hNA
  -- the projection onto `A` along `B`
  set π := A.projectionOnto B hA
  have hπA : ∀ a (ha : a ∈ A), π a = ⟨a, ha⟩ := fun a ha =>
    Submodule.projectionOnto_apply_of_mem_left hA ha
  have hπB : ∀ b ∈ B, π b = 0 := fun b hb => Submodule.projectionOnto_apply_of_mem_right hA hb
  have hsplit : ∀ v, v - (π v : V) ∈ B := fun v => Submodule.sub_projection_mem hA v
  have hAB : ∀ a ∈ A, ∀ b ∈ B, bform Q a b = 0 := fun a ha b hb => hb a ha
  -- `bform Q ↑a v = bform Q ↑a ↑(π v)`
  have hbπ : ∀ (a : A) v, bform Q a v = bform Q a (π v : V) := by
    intro a v
    have := hAB a a.2 _ (hsplit v)
    rw [map_sub, sub_eq_zero] at this
    exact this
  have hbπ' : ∀ v (a : A), bform Q v a = bform Q (π v : V) a := fun v a => by
    rw [hsymm, hbπ, hsymm]
  have hgπ : ∀ v, π (g v) = π v := by
    intro v
    have e : g v = (π v : V) + g (v - π v) := by
      rw [map_sub, (hAg _).1 (π v).2]; abel
    rw [e, map_add, hπA _ (π v).2, hπB _ (hgB _ (hsplit v)), add_zero]
  have hNB : ∀ b ∈ B, N b ∈ B := fun b hb a ha => by
    change bform Q a (N b) = 0
    rw [← neg_eq_zero, ← hNs, hAB _ (hNA a ha) b hb]
  have hNπ : ∀ v, π (N v) = NA (π v) := by
    intro v
    have e : N v = N (π v : V) + N (v - π v) := by rw [map_sub]; abel
    rw [e, map_add, hπA _ (hNA _ (π v).2), hπB _ (hNB _ (hsplit v)), add_zero]
    rfl
  let ρ : ↥(soCent Q g ⊓ soCent Q N) →ₗ[K] ↥(soCent (Q.comp A.subtype) NA) :=
    { toFun := fun M => ⟨(M : Module.End K V).restrict (p := A) (q := A)
          (hpres M (mem_soCent.mp (Submodule.mem_inf.mp M.2).1).2), by
        obtain ⟨hMg, hMN⟩ := Submodule.mem_inf.mp M.2
        obtain ⟨hMs, -⟩ := mem_soCent.mp hMg
        obtain ⟨-, hMNc⟩ := mem_soCent.mp hMN
        refine mem_soCent.2 ⟨fun a b => ?_, ?_⟩
        · rw [bform_comp_subtype, bform_comp_subtype]; exact hMs a b
        · ext a
          simp only [Module.End.mul_apply, LinearMap.restrict_apply, NA]
          exact congrArg (fun T : Module.End K V => T a) hMNc⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsurj : Function.Surjective ρ := by
    rintro ⟨MA, hMA⟩
    obtain ⟨hMAs, hMAN⟩ := mem_soCent.mp hMA
    set M : Module.End K V := A.subtype ∘ₗ MA ∘ₗ π
    have hMv : ∀ v, M v = (MA (π v) : V) := fun v => rfl
    have hMs : ∀ u w, bform Q (M u) w = -bform Q u (M w) := by
      intro u w
      rw [hMv, hMv, hbπ, ← bform_comp_subtype, hMAs, bform_comp_subtype, hbπ' u (MA (π w))]
    have hMg : M * g = g * M := by
      ext v
      simp only [Module.End.mul_apply, hMv, hgπ]
      exact ((hAg _).1 (MA (π v)).2).symm
    have hMN : M * N = N * M := by
      ext v
      simp only [Module.End.mul_apply, hMv, hNπ]
      have := congrArg (fun T : Module.End K A => (T (π v) : V)) hMAN
      simpa [Module.End.mul_apply, NA] using this
    refine ⟨⟨M, Submodule.mem_inf.mpr ⟨mem_soCent.2 ⟨hMs, hMg⟩, mem_soCent.2 ⟨hMs, hMN⟩⟩⟩, ?_⟩
    apply Subtype.ext
    ext a
    show M a = (MA a : V)
    rw [hMv, hπA _ a.2]
  have hker : finrank K (LinearMap.ker ρ) = finrank K ↥(soCent Q g ⊓ soCent Q N ⊓ killSub A) := by
    have e : LinearMap.ker ρ = (soCent Q g ⊓ soCent Q N ⊓ killSub A).comap
        (soCent Q g ⊓ soCent Q N).subtype := by
      ext M
      simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]
      constructor
      · intro h
        refine ⟨Submodule.mem_inf.mp M.2, fun a ha => ?_⟩
        exact congrArg Subtype.val (LinearMap.congr_fun (congrArg Subtype.val h) ⟨a, ha⟩)
      · rintro ⟨-, hk⟩
        exact Subtype.ext (LinearMap.ext fun a => Subtype.ext (hk a a.2))
    rw [e, (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq]
  have hrn := LinearMap.finrank_range_add_finrank_ker (V₂ := ↥(soCent (Q.comp A.subtype) NA)) ρ
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, hker] at hrn
  exact hrn.symm

omit [FiniteDimensional K V] in
/-- If the elements of `so(V)_g` killing the fixed space `A` commute with each other (the moved part
is abelian), then every `N ∈ so(V)_g` centralizes them: write `N = N₁ + N₂` with `N₁` the extension
by `0` of `N|_A` (which has disjoint support from them) and `N₂` killing `A`. -/
theorem soCent_inf_killSub_eq {Q : QuadraticForm K V} {g N : Module.End K V} {A : Submodule K V}
    (hA : IsCompl A ((bform Q).orthogonal A)) (hAg : ∀ v, v ∈ A ↔ g v = v)
    (hgB : ∀ b ∈ (bform Q).orthogonal A, g b ∈ (bform Q).orthogonal A)
    (hNs : ∀ u w, bform Q (N u) w = -bform Q u (N w)) (hNg : N * g = g * N)
    (hab : ∀ M₁ ∈ soCent Q g ⊓ killSub A, ∀ M₂ ∈ soCent Q g ⊓ killSub A, M₁ * M₂ = M₂ * M₁) :
    soCent Q g ⊓ soCent Q N ⊓ killSub A = soCent Q g ⊓ killSub A := by
  set B := (bform Q).orthogonal A
  have hsymm : ∀ x y, bform Q x y = bform Q y x := fun x y => QuadraticMap.associated_isSymm K Q x y
  have hNA : ∀ a ∈ A, N a ∈ A := fun a ha =>
    (hAg _).2 (by rw [← Module.End.mul_apply, ← hNg, Module.End.mul_apply, (hAg a).1 ha])
  set π := A.projectionOnto B hA
  have hπA : ∀ a (ha : a ∈ A), π a = ⟨a, ha⟩ := fun a ha =>
    Submodule.projectionOnto_apply_of_mem_left hA ha
  have hπB : ∀ b ∈ B, π b = 0 := fun b hb => Submodule.projectionOnto_apply_of_mem_right hA hb
  have hsplit : ∀ v, v - (π v : V) ∈ B := fun v => Submodule.sub_projection_mem hA v
  have hAB : ∀ a ∈ A, ∀ b ∈ B, bform Q a b = 0 := fun a ha b hb => hb a ha
  have hbπ : ∀ (a : A) v, bform Q a v = bform Q a (π v : V) := by
    intro a v
    have := hAB a a.2 _ (hsplit v)
    rw [map_sub, sub_eq_zero] at this
    exact this
  have hgπ : ∀ v, π (g v) = π v := by
    intro v
    have e : g v = (π v : V) + g (v - π v) := by
      rw [map_sub, (hAg _).1 (π v).2]; abel
    rw [e, map_add, hπA _ (π v).2, hπB _ (hgB _ (hsplit v)), add_zero]
  -- `N₁ = ` extension of `N|_A` by `0`
  set N₁ : Module.End K V := A.subtype ∘ₗ (N.restrict hNA) ∘ₗ π
  have hN₁v : ∀ v, N₁ v = N (π v : V) := fun v => rfl
  have hN₁s : ∀ u w, bform Q (N₁ u) w = -bform Q u (N₁ w) := by
    intro u w
    rw [hN₁v, hN₁v]
    rw [show bform Q (N (π u : V)) w = bform Q (N (π u : V)) (π w : V) from
      hbπ ⟨_, hNA _ (π u).2⟩ w, hNs, hsymm u, hbπ ⟨_, hNA _ (π w).2⟩ u, hsymm]
  have hN₁g : N₁ * g = g * N₁ := by
    ext v
    simp only [Module.End.mul_apply, hN₁v, hgπ]
    exact ((hAg _).1 (hNA _ (π v).2)).symm
  set N₂ := N - N₁
  have hN₂ : N₂ ∈ soCent Q g ⊓ killSub A := by
    refine Submodule.mem_inf.mpr ⟨mem_soCent.2 ⟨fun u w => ?_, ?_⟩, fun a ha => ?_⟩
    · simp only [N₂, LinearMap.sub_apply, map_sub, LinearMap.sub_apply, hNs, hN₁s]; ring
    · rw [sub_mul, mul_sub, hNg, hN₁g]
    · simp only [N₂, LinearMap.sub_apply, hN₁v, hπA a ha, sub_self]
  apply le_antisymm
  · exact fun M hM => Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp (Submodule.mem_inf.mp hM).1).1,
      (Submodule.mem_inf.mp hM).2⟩
  · intro M hM
    obtain ⟨hMg, hMk⟩ := Submodule.mem_inf.mp hM
    obtain ⟨hMs, -⟩ := mem_soCent.mp hMg
    have hMB : ∀ v, M v ∈ B := fun v a ha => by
      change bform Q a (M v) = 0
      rw [← neg_eq_zero, ← hMs, hMk a ha, map_zero, LinearMap.zero_apply]
    have h1 : M * N₁ = N₁ * M := by
      ext v
      simp only [Module.End.mul_apply, hN₁v, hMk _ (hNA _ (π v).2), hπB _ (hMB v),
        Submodule.coe_zero, map_zero]
    have h2 := hab M hM N₂ hN₂
    have hMN : M * N = N * M := by
      have : N = N₁ + N₂ := by simp [N₂]
      rw [this, mul_add, add_mul, h1, h2]
    exact Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hMg, mem_soCent.2 ⟨hMs, hMN⟩⟩, hMk⟩

/-- The restriction of `q` to `A` is nondegenerate when `V = A ⊥ A^⊥`. -/
theorem isNondeg_comp_subtype_of_isCompl {Q : QuadraticForm K V} {A : Submodule K V}
    (hA : IsCompl A ((bform Q).orthogonal A)) : IsNondeg (Q.comp A.subtype) := by
  have h := (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
    (B := bform Q) (W := A)
    (LinearMap.IsSymm.isRefl (QuadraticForm.associated_isSymm (S := K) Q))).2 hA
  have e : bform (Q.comp A.subtype) = (bform Q).restrict A := by
    ext a b; exact bform_comp_subtype Q A a b
  unfold IsNondeg; rw [e]; exact h

/-- **A `gspin`-level abelian moved part gives an `so`-level one**: if elements of `gspin(V)_y`
acting trivially on `ι(A)`, `A = W'_y`, commute, then so do the elements of `so(V)_{P y}` killing
`A`. -/
theorem commute_of_movedPart {Q : QuadraticForm K V} (hQ : IsNondeg Q) (y : GSpin Q)
    (H : ∀ X ∈ lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q),
      ∀ Y ∈ lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q),
      (∀ v ∈ fixedSub y, ⁅X, ι Q v⁆ = 0) → (∀ v ∈ fixedSub y, ⁅Y, ι Q v⁆ = 0) → ⁅X, Y⁆ = 0) :
    ∀ M₁ ∈ soCent Q (specP Q y : Module.End K V) ⊓ killSub (fixedSub y),
      ∀ M₂ ∈ soCent Q (specP Q y : Module.End K V) ⊓ killSub (fixedSub y), M₁ * M₂ = M₂ * M₁ := by
  have lift : ∀ M ∈ soCent Q (specP Q y : Module.End K V) ⊓ killSub (fixedSub y),
      ∃ Z ∈ lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q),
        adV Q Z = M ∧ ∀ v ∈ fixedSub y, ⁅Z, ι Q v⁆ = 0 := by
    intro M hM
    obtain ⟨hMg, hMk⟩ := Submodule.mem_inf.mp hM
    obtain ⟨hMs, hMc⟩ := mem_soCent.mp hMg
    obtain ⟨Z, hZg, hZM⟩ := exists_mem_gspin_adV_eq hQ M hMs
    refine ⟨Z, mem_lieCentralizer.mpr ⟨hZg, (commute_iff_adV hQ y hZg).mpr (by rw [hZM]; exact hMc.symm)⟩,
      hZM, fun v hv => ?_⟩
    rw [Ring.lie_def, ← ι_adV hZg, hZM, hMk v hv, map_zero]
  intro M₁ hM₁ M₂ hM₂
  obtain ⟨Z₁, hZ₁, hZM₁, h₁⟩ := lift M₁ hM₁
  obtain ⟨Z₂, hZ₂, hZM₂, h₂⟩ := lift M₂ hM₂
  have h := H Z₁ hZ₁ Z₂ hZ₂ h₁ h₂
  rw [Ring.lie_def] at h
  have := adV_commutator (mem_lieCentralizer.mp hZ₁).1 (mem_lieCentralizer.mp hZ₂).1
  rw [h, map_zero, hZM₁, hZM₂] at this
  exact sub_eq_zero.mp this.symm

/-- **Dimension of `gspin(V)_{y,Y}` through the fixed space `A = W'_y`**: for `Y ∈ gspin(V)_y`,
`dim gspin(V)_{y,Y} = dim so(A)_{adV Y|_A} + dim (so(V)_{P y, adV Y} killing A) + 1`. -/
theorem finrank_lieCentralizer_fixed {Q : QuadraticForm K V} (hQ : IsNondeg Q) (y : GSpin Q)
    (hc : IsCompl (fixedSub y) ((bform Q).orthogonal (fixedSub y))) {Y : CliffordAlgebra Q}
    (hY : Y ∈ lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) :
    ∃ h : ∀ a ∈ fixedSub y, adV Q Y a ∈ fixedSub y,
      finrank K (lieCentralizer (lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q)) Y) =
      finrank K (soCent (Q.comp (fixedSub y).subtype) ((adV Q Y).restrict h)) +
        finrank K ↥(soCent Q (specP Q y : Module.End K V) ⊓ soCent Q (adV Q Y) ⊓
          killSub (fixedSub y)) + 1 := by
  obtain ⟨hYg, hYc⟩ := mem_lieCentralizer.mp hY
  have hNg : adV Q Y * (specP Q y : Module.End K V) = (specP Q y : Module.End K V) * adV Q Y :=
    ((commute_iff_adV hQ y hYg).mp hYc).symm
  have hgB : ∀ b ∈ (bform Q).orthogonal (fixedSub y),
      (specP Q y : Module.End K V) b ∈ (bform Q).orthogonal (fixedSub y) :=
    fun b hb => specP_mem_orthogonal_fixedSub y hb
  have e := finrank_soCent_inf_eq hc (mem_fixedSub_iff y) hgB (bform_adV hYg) hNg
  exact ⟨_, by rw [finrank_lieCentralizer_lieCentralizer_gspin hQ y hYg, e]⟩

omit [FiniteDimensional K V] in
/-- A skew `M` killing `A` maps `V` into `A^⊥`. -/
theorem mem_orthogonal_of_mem_killSub {Q : QuadraticForm K V} {A : Submodule K V}
    {M : Module.End K V} (hMs : ∀ u w, bform Q (M u) w = -bform Q u (M w)) (hMA : M ∈ killSub A)
    (v : V) : M v ∈ (bform Q).orthogonal A := by
  intro a ha
  change bform Q a (M v) = 0
  have hsymm : ∀ x y, bform Q x y = bform Q y x := fun x y => QuadraticMap.associated_isSymm K Q x y
  rw [hsymm, hMs, hsymm, hMA a ha, map_zero, LinearMap.zero_apply, neg_zero]

omit [FiniteDimensional K V] in
/-- **The part of `so(V)_{g,N}` killing `A` only sees `N` on `A^⊥`**: if `N`, `N'` preserve `A`
and agree on `A^⊥ = B`, with `V = A ⊕ B`, the two parts coincide. -/
theorem soCent_inf_killSub_congr {Q : QuadraticForm K V} {g N N' : Module.End K V}
    {A : Submodule K V} (hA : IsCompl A ((bform Q).orthogonal A)) (hNA : ∀ a ∈ A, N a ∈ A)
    (hN'A : ∀ a ∈ A, N' a ∈ A) (hNN' : ∀ b ∈ (bform Q).orthogonal A, N b = N' b) :
    soCent Q g ⊓ soCent Q N ⊓ killSub A = soCent Q g ⊓ soCent Q N' ⊓ killSub A := by
  have key : ∀ {N N' : Module.End K V}, (∀ a ∈ A, N a ∈ A) → (∀ a ∈ A, N' a ∈ A) →
      (∀ b ∈ (bform Q).orthogonal A, N b = N' b) →
      soCent Q g ⊓ soCent Q N ⊓ killSub A ≤ soCent Q g ⊓ soCent Q N' ⊓ killSub A := by
    intro N N' hNA hN'A hNN' M hM
    obtain ⟨⟨hMg, hMN⟩, hMA⟩ := hM
    obtain ⟨hMs, hMN⟩ := mem_soCent.1 hMN
    refine ⟨⟨hMg, mem_soCent.2 ⟨hMs, ?_⟩⟩, hMA⟩
    ext v
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hA.sup_eq_top ▸ Submodule.mem_top (x := v))
    have hMb := mem_orthogonal_of_mem_killSub hMs hMA b
    have hb' := congrArg (fun T : Module.End K V => T b) hMN
    simp only [Module.End.mul_apply] at hb' ⊢
    rw [map_add, map_add, map_add, map_add, hMA _ (hN'A a ha), hMA a ha, map_zero, ← hNN' b hb,
      ← hNN' _ hMb, hb']
  exact le_antisymm (key hNA hN'A hNN') (key hN'A hNA fun b hb => (hNN' b hb).symm)

/-- **Upper bound** for `dim gspin(V)_{y,Y}`: `≤ dim so(A)_{adV Y|_A} + dim (so(V)_{P y} killing A) + 1`. -/
theorem finrank_lieCentralizer_fixed_le {Q : QuadraticForm K V} (hQ : IsNondeg Q) (y : GSpin Q)
    (hc : IsCompl (fixedSub y) ((bform Q).orthogonal (fixedSub y))) {Y : CliffordAlgebra Q}
    (hY : Y ∈ lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
    (h : ∀ a ∈ fixedSub y, adV Q Y a ∈ fixedSub y) :
    finrank K (lieCentralizer (lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q)) Y) ≤
      finrank K (soCent (Q.comp (fixedSub y).subtype) ((adV Q Y).restrict h)) +
        finrank K ↥(soCent Q (specP Q y : Module.End K V) ⊓ killSub (fixedSub y)) + 1 := by
  obtain ⟨h', e⟩ := finrank_lieCentralizer_fixed hQ y hc hY
  rw [e]
  have hle := Submodule.finrank_mono (show soCent Q (specP Q y : Module.End K V) ⊓
      soCent Q (adV Q Y) ⊓ killSub (fixedSub y) ≤
      soCent Q (specP Q y : Module.End K V) ⊓ killSub (fixedSub y) from
    fun M hM => Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp (Submodule.mem_inf.mp hM).1).1,
      (Submodule.mem_inf.mp hM).2⟩)
  omega

end Fixed

/-! ## An upper bound from a Jordan chain -/

section Chain

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
/-- For `N` skew: `b(u, N^l w) = (-1)^l b(N^l u, w)`. -/
theorem bform_pow_skew {Q : QuadraticForm K V} {N : Module.End K V}
    (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w)) (l : ℕ) (u w : V) :
    bform Q u ((N ^ l) w) = (-1) ^ l * bform Q ((N ^ l) u) w := by
  induction l generalizing w with
  | zero => simp
  | succ l ih =>
    have e1 : (N ^ (l + 1)) w = (N ^ l) (N w) := by rw [pow_succ, Module.End.mul_apply]
    have e2 : (N ^ (l + 1)) u = N ((N ^ l) u) := by rw [pow_succ', Module.End.mul_apply]
    rw [e1, e2, ih, hN, pow_succ]
    ring

/-- **Upper bound for `dim so(V)_N` along a Jordan chain.** Let `N` be skew, `v₀ ∈ V` with
`v₀, N v₀, …, N^{m-1} v₀` linearly independent, spanning `U`, with `V = U + U^⊥` and
`dim U^⊥ ≤ 1`. Then `M ↦ M v₀` embeds `so(V)_N` into the orthogonal of the even part
`⟨N^{2j} v₀⟩` of the chain, so `dim so(V)_N ≤ dim V − ⌈m/2⌉`. -/
theorem finrank_soCent_le_of_chain {Q : QuadraticForm K V} (hQ : IsNondeg Q) {N : Module.End K V}
    (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w)) (v₀ : V) (m : ℕ)
    (hli : LinearIndependent K fun i : Fin m => (N ^ (i : ℕ)) v₀)
    (hsup : Submodule.span K (Set.range fun i : Fin m => (N ^ (i : ℕ)) v₀) ⊔
      (bform Q).orthogonal (Submodule.span K (Set.range fun i : Fin m => (N ^ (i : ℕ)) v₀)) = ⊤)
    (hperp : finrank K ((bform Q).orthogonal
      (Submodule.span K (Set.range fun i : Fin m => (N ^ (i : ℕ)) v₀))) ≤ 1) :
    finrank K (soCent Q N) ≤ finrank K V - (m + 1) / 2 := by
  set U := Submodule.span K (Set.range fun i : Fin m => (N ^ (i : ℕ)) v₀)
  -- the even part of the chain
  let ev : Fin ((m + 1) / 2) → Fin m := fun j => ⟨2 * j, by omega⟩
  have hev : Function.Injective ev := fun a b h => Fin.ext (by
    have := congrArg Fin.val h; simp only [ev] at this; omega)
  set E := Submodule.span K (Set.range fun j : Fin ((m + 1) / 2) => (N ^ (2 * (j : ℕ))) v₀)
  have hE : finrank K E = (m + 1) / 2 := by
    have := finrank_span_eq_card (hli.comp ev hev)
    rw [Fintype.card_fin] at this
    exact this
  have hsymm : ∀ x y, bform Q x y = bform Q y x := fun x y => QuadraticMap.associated_isSymm K Q x y
  have hcommpow : ∀ M ∈ soCent Q N, ∀ l : ℕ, M * N ^ l = N ^ l * M :=
    fun M hM l => (Commute.pow_right (mem_soCent.mp hM).2 l)
  -- `M v₀ ⊥ E`
  have hmemS : ∀ M ∈ soCent Q N, M v₀ ∈ (bform Q).orthogonal E := by
    intro M hM
    have hMs := (mem_soCent.mp hM).1
    have hle : E ≤ LinearMap.ker ((bform Q).flip (M v₀)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      change bform Q ((N ^ (2 * (j : ℕ))) v₀) (M v₀) = 0
      have h1 : bform Q (M v₀) ((N ^ (2 * (j : ℕ))) v₀) =
          -bform Q (M v₀) ((N ^ (2 * (j : ℕ))) v₀) := by
        conv_lhs => rw [hMs, ← Module.End.mul_apply, hcommpow M hM, Module.End.mul_apply,
          bform_pow_skew hN, pow_mul, neg_one_sq, one_pow, one_mul, hsymm]
      rw [hsymm]
      have h2 : (2 : K) * bform Q (M v₀) ((N ^ (2 * (j : ℕ))) v₀) = 0 := by
        rw [two_mul]; nth_rewrite 1 [h1]; ring
      exact (mul_eq_zero.mp h2).resolve_left (Invertible.ne_zero 2)
    intro w hw
    exact hle hw
  let ψ : soCent Q N →ₗ[K] (bform Q).orthogonal E :=
    { toFun := fun M => ⟨(M : Module.End K V) v₀, hmemS M M.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨M, hM⟩ h0
    have hv : M v₀ = 0 := congrArg Subtype.val h0
    have hMs := (mem_soCent.mp hM).1
    have hU : ∀ u ∈ U, M u = 0 := by
      have hle : U ≤ LinearMap.ker M := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        change M ((N ^ (i : ℕ)) v₀) = 0
        rw [← Module.End.mul_apply, hcommpow M hM, Module.End.mul_apply, hv, map_zero]
      exact fun u hu => hle hu
    obtain ⟨e, he⟩ := finrank_le_one_iff.mp hperp
    have hee : bform Q (M e) e = 0 := by
      have h1 := hMs e e
      rw [hsymm e] at h1
      have h2 : (2 : K) * bform Q (M e) e = 0 := by rw [two_mul]; nth_rewrite 1 [h1]; ring
      exact (mul_eq_zero.mp h2).resolve_left (Invertible.ne_zero 2)
    have hperp0 : ∀ w ∈ (bform Q).orthogonal U, M w = 0 := by
      intro w hw
      obtain ⟨c, hc⟩ := he ⟨w, hw⟩
      have hwc : w = c • (e : V) := (congrArg Subtype.val hc).symm
      refine (isNondeg_iff Q).mp hQ _ fun x => ?_
      have hx : x ∈ U ⊔ (bform Q).orthogonal U := hsup ▸ Submodule.mem_top
      obtain ⟨u, hu, w', hw', rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨c', hc'⟩ := he ⟨w', hw'⟩
      have hwc' : w' = c' • (e : V) := (congrArg Subtype.val hc').symm
      rw [map_add, hMs, hU u hu, map_zero, neg_zero, zero_add, hwc, hwc']
      simp [hee]
    ext x
    have hx : x ∈ U ⊔ (bform Q).orthogonal U := hsup ▸ Submodule.mem_top
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    simp [hU u hu, hperp0 w hw]
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [LinearMap.BilinForm.finrank_orthogonal hQ, hE] at h1
  exact h1

omit [FiniteDimensional K V] in
/-- **The upper half of a Jordan chain of a skew `N` is totally isotropic**: if `N^(m+1) v = 0` and
`m + 1 ≤ 2a`, then `b(N^(a+i) v, N^(a+j) v) = ± b(v, N^(2a+i+j) v) = 0`. -/
theorem isTotallyIsotropic_span_pow {Q : QuadraticForm K V} {N : Module.End K V}
    (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w)) {v : V} {m a : ℕ}
    (hm : (N ^ (m + 1)) v = 0) (ha : m + 1 ≤ 2 * a) (l : ℕ) :
    IsTotallyIsotropic Q (Submodule.span K (Set.range fun i : Fin l => (N ^ (a + i)) v)) := by
  set S := Submodule.span K (Set.range fun i : Fin l => (N ^ (a + i)) v)
  have hgen : ∀ i j : ℕ, bform Q ((N ^ (a + i)) v) ((N ^ (a + j)) v) = 0 := by
    intro i j
    rw [bform_pow_skew hN (a + j), ← Module.End.mul_apply, ← pow_add]
    rw [Module.End.pow_map_zero_of_le (by omega) hm, map_zero, LinearMap.zero_apply, mul_zero]
  have h1 : ∀ i : Fin l, S ≤ LinearMap.ker (bform Q ((N ^ (a + i)) v)) := fun i =>
    Submodule.span_le.2 <| by rintro _ ⟨j, rfl⟩; exact hgen i j
  intro u hu
  have h2 : S ≤ LinearMap.ker ((bform Q).flip u) :=
    Submodule.span_le.2 <| by rintro _ ⟨i, rfl⟩; exact h1 i hu
  rw [← QuadraticMap.associated_eq_self_apply K Q u]
  exact h2 hu

end Chain

/-! ## Jordan chains of a nilpotent endomorphism -/

section JordanChain

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- **A Jordan chain is linearly independent**: if `f^m v ≠ 0` and `f^(m+1) v = 0`, then
`v, f v, …, f^m v` are linearly independent. -/
theorem linearIndependent_pow_apply {f : Module.End K V} {v : V} {m : ℕ}
    (hm : (f ^ m) v ≠ 0) (hm' : (f ^ (m + 1)) v = 0) :
    LinearIndependent K fun i : Fin (m + 1) => (f ^ (i : ℕ)) v := by
  induction m generalizing v with
  | zero =>
    change LinearIndependent K fun i : Fin 1 => (f ^ (i : ℕ)) v
    exact linearIndependent_unique_iff.2 (by simpa using hm)
  | succ m ih =>
    have e : ∀ j, (f ^ (j + 1)) v = (f ^ j) (f v) := fun j => by
      rw [pow_succ, Module.End.mul_apply]
    rw [linearIndependent_finSucc]
    have ht : Fin.tail (fun i : Fin (m + 2) => (f ^ (i : ℕ)) v) =
        fun i : Fin (m + 1) => (f ^ (i : ℕ)) (f v) := funext fun i => e i
    rw [ht]
    refine ⟨ih (by rwa [← e]) (by rwa [← e]), fun hv => hm ?_⟩
    have hle : Submodule.span K (Set.range fun i : Fin (m + 1) => (f ^ (i : ℕ)) (f v)) ≤
        LinearMap.ker (f ^ (m + 1)) := Submodule.span_le.2 <| by
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_add, ← e]
      exact Module.End.pow_map_zero_of_le (by omega) hm'
    exact hle hv

/-- For `f` nilpotent and `f^m v ≠ 0` there is a Jordan chain through `v` of length at least
`m + 1`: some `k ≥ m` with `f^k v ≠ 0` and `f^(k+1) v = 0`. -/
theorem exists_pow_apply_ne_zero_of_isNilpotent {f : Module.End K V} (hf : IsNilpotent f)
    {v : V} {m : ℕ} (hm : (f ^ m) v ≠ 0) :
    ∃ k, m ≤ k ∧ (f ^ k) v ≠ 0 ∧ (f ^ (k + 1)) v = 0 := by
  classical
  have ex : ∃ k, (f ^ (k + 1)) v = 0 := by
    obtain ⟨n, hn⟩ := hf
    exact ⟨n, by rw [pow_succ, hn, zero_mul, LinearMap.zero_apply]⟩
  refine ⟨Nat.find ex, ?_, ?_, Nat.find_spec ex⟩
  · by_contra hlt
    exact hm (Module.End.pow_map_zero_of_le (by omega) (Nat.find_spec ex))
  · rcases Nat.eq_zero_or_eq_succ_pred (Nat.find ex) with h0 | hs
    · rw [h0, pow_zero, Module.End.one_apply]
      rintro rfl
      exact hm (map_zero _)
    · rw [hs]
      exact Nat.find_min ex (by omega)

end JordanChain

/-! ## Matrices, and extension of scalars -/

section Matrix

open scoped TensorProduct Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `so(J)_A` for matrices: the `J`-skew-adjoint matrices commuting with `A`. -/
def soCentMat {R : Type*} [CommRing R] (J A : Matrix n n R) : Submodule R (Matrix n n R) :=
  skewAdjointMatricesSubmodule J ⊓ (Subalgebra.centralizer R {A}).toSubmodule

/-- The linear map `B ↦ (Bᵀ J + J B, B A − A B)`, with kernel `so(J)_A`. -/
def soCentMatMap {R : Type*} [CommRing R] (J A : Matrix n n R) :
    Matrix n n R →ₗ[R] Matrix n n R × Matrix n n R where
  toFun B := (Bᵀ * J + J * B, B * A - A * B)
  map_add' B C := by
    refine Prod.ext ?_ ?_ <;>
      simp only [Matrix.transpose_add, add_mul, mul_add, Prod.fst_add, Prod.snd_add] <;> abel
  map_smul' c B := by
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, RingHom.id_apply,
      Prod.smul_mk, smul_add, smul_sub]

theorem soCentMat_eq_ker {R : Type*} [CommRing R] (J A : Matrix n n R) :
    soCentMat J A = LinearMap.ker (soCentMatMap J A) := by
  ext B
  simp only [soCentMat, Submodule.mem_inf, mem_skewAdjointMatricesSubmodule,
    Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Subalgebra.mem_toSubmodule,
    Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, LinearMap.mem_ker,
    soCentMatMap, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk_eq_zero, Matrix.mul_neg]
  rw [← eq_neg_iff_add_eq_zero, sub_eq_zero, eq_comm (a := B * A)]

/-- `B ↦ (Bᵀ J + J B, B A − A B, B C − C B)`, whose kernel is `so(J)_A ⊓ so(J)_C`. -/
def jointMatMap {R : Type*} [CommRing R] (J A C : Matrix n n R) :
    Matrix n n R →ₗ[R] (Fin 3 → Matrix n n R) where
  toFun B := ![B.transpose * J + J * B, B * A - A * B, B * C - C * B]
  map_add' B B' := by
    funext i; fin_cases i <;>
      simp [Matrix.transpose_add, add_mul, mul_add, sub_eq_add_neg, neg_add] <;> abel
  map_smul' c B := by
    funext i; fin_cases i <;> simp [Matrix.transpose_smul, smul_sub, smul_add]

theorem ker_jointMatMap {R : Type*} [CommRing R] (J A C : Matrix n n R) :
    LinearMap.ker (jointMatMap J A C) = soCentMat J A ⊓ soCentMat J C := by
  ext B
  simp only [LinearMap.mem_ker, Submodule.mem_inf, soCentMat_eq_ker, soCentMatMap,
    LinearMap.coe_mk, AddHom.coe_mk, jointMatMap, Prod.mk_eq_zero]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp at h0 h1 h2
    exact ⟨⟨h0, h1⟩, h0, h2⟩
  · rintro ⟨⟨h0, h1⟩, -, h2⟩
    funext i; fin_cases i <;> simp [h0, h1, h2]

theorem jointMatMap_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (J A C M : Matrix n n R) (i : Fin 3) :
    jointMatMap (J.map φ) (A.map φ) (C.map φ) (M.map φ) i = (jointMatMap J A C M i).map φ := by
  fin_cases i <;>
    simp [jointMatMap, ← Matrix.transpose_map, ← RingHom.mapMatrix_apply, map_mul, map_add,
      map_sub] <;>
    rfl

/-- **`dim so(J)_A` is unchanged by extension of scalars.** -/
theorem finrank_soCentMat_map {F K : Type*} [Field F] [Field K] [Algebra F K]
    (J A : Matrix n n F) :
    Module.finrank K (soCentMat (J.map (algebraMap F K)) (A.map (algebraMap F K))) =
      Module.finrank F (soCentMat J A) := by
  have h := finrank_ker_map_matrix _ _ (jointMatMap_map (algebraMap F K) J A A)
  rwa [ker_jointMatMap, ker_jointMatMap, inf_idem, inf_idem] at h

/-- **`so(J)_A` over `K` is spanned by `so(J)_A` over `F`.** -/
theorem soCentMat_map_eq_span {F K : Type*} [Field F] [Field K] [Algebra F K]
    (J A : Matrix n n F) :
    soCentMat (J.map (algebraMap F K)) (A.map (algebraMap F K)) =
      Submodule.span K ((fun M : Matrix n n F => M.map (algebraMap F K)) '' soCentMat J A) := by
  have h := ker_map_matrix_eq_span _ _ (jointMatMap_map (algebraMap F K) J A A)
  rwa [ker_jointMatMap, ker_jointMatMap, inf_idem, inf_idem] at h

end Matrix

section Endomorphisms

open scoped Matrix

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- In a basis `b`, `so(V)_N` is `so(J)_A` with `J` the Gram matrix of `b(·,·)` and `A` the matrix
of `N`. -/
theorem soCentMat_toMatrix (b : Basis n K V) (Q : QuadraticForm K V) (N : Module.End K V) :
    soCentMat (LinearMap.toMatrix₂ b b (bform Q)) (LinearMap.toMatrix b b N) =
      (soCent Q N).map (LinearMap.toMatrix b b).toLinearMap := by
  ext B
  rw [Submodule.mem_map_equiv, mem_soCent]
  set M := (LinearMap.toMatrix b b).symm B
  have hB : B = LinearMap.toMatrix b b M := by simp [M]
  rw [hB]
  simp only [soCentMat, Submodule.mem_inf, mem_skewAdjointMatricesSubmodule,
    Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  rw [Matrix.IsSkewAdjoint, ← isAdjointPair_toLinearMap₂ b b, Matrix.toLinearMap₂_toMatrix₂,
    ← map_neg, Matrix.toLin_toMatrix, Matrix.toLin_toMatrix, ← LinearMap.toMatrix_mul,
    ← LinearMap.toMatrix_mul, (LinearMap.toMatrix b b).injective.eq_iff]
  simp only [LinearMap.IsAdjointPair, LinearMap.neg_apply, map_neg]
  exact and_congr Iff.rfl eq_comm

end Endomorphisms

end GSpinGGP
