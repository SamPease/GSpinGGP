/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.GSpin
import GSpinGGP.Foundations.LocalGroups

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

* `finrank_soCent_le_of_chain`: an upper bound for `dim so(V)_N` when `N` has a long Jordan chain.
* `soCentMat`, `soCentMat_toMatrix`: the same in matrix form, and `finrank_soCentMat_map`: its
  dimension does not change under extension of scalars.
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

end Centralizer

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

end Chain

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

/-- `K ⊗[F] Mat_n(F) ≃ Mat_n(K)`, `K`-linearly: `a ⊗ M ↦ a • M.map (algebraMap F K)`. -/
def matrixBaseChangeEquiv (F K : Type*) [Field F] [Field K] [Algebra F K] :
    K ⊗[F] Matrix n n F ≃ₗ[K] Matrix n n K :=
  { (matrixEquivTensor n F K).symm.toLinearEquiv with
    map_smul' := fun c x => by
      change (matrixEquivTensor n F K).symm (c • x) = c • (matrixEquivTensor n F K).symm x
      induction x using TensorProduct.inductionOn with
      | tmul a M =>
        rw [TensorProduct.smul_tmul', matrixEquivTensor_apply_symm, matrixEquivTensor_apply_symm,
          smul_smul, smul_eq_mul]
      | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add] }

theorem matrixBaseChangeEquiv_tmul (F K : Type*) [Field F] [Field K] [Algebra F K] (a : K)
    (M : Matrix n n F) :
    matrixBaseChangeEquiv (n := n) F K (a ⊗ₜ M) = a • M.map (algebraMap F K) :=
  matrixEquivTensor_apply_symm _ _ _ _ _

/-- **`dim so(J)_A` is unchanged by extension of scalars.** -/
theorem finrank_soCentMat_map {F K : Type*} [Field F] [Field K] [Algebra F K]
    (J A : Matrix n n F) :
    Module.finrank K (soCentMat (J.map (algebraMap F K)) (A.map (algebraMap F K))) =
      Module.finrank F (soCentMat J A) := by
  set f := soCentMatMap J A
  let e1 := matrixBaseChangeEquiv (n := n) F K
  let e2 : K ⊗[F] (Matrix n n F × Matrix n n F) ≃ₗ[K] Matrix n n K × Matrix n n K :=
    (TensorProduct.prodRight F K K _ _).trans (e1.prodCongr e1)
  set g := soCentMatMap (J.map (algebraMap F K)) (A.map (algebraMap F K))
  have hcomm : ∀ x, g (e1 x) = e2 (f.baseChange K x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a M =>
      show g ((matrixEquivTensor n F K).symm (a ⊗ₜ M)) =
        ((matrixEquivTensor n F K).symm (a ⊗ₜ (f M).1), (matrixEquivTensor n F K).symm (a ⊗ₜ (f M).2))
      rw [matrixEquivTensor_apply_symm, matrixEquivTensor_apply_symm, matrixEquivTensor_apply_symm]
      simp only [g, f, soCentMatMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.transpose_smul,
        Matrix.smul_mul, Matrix.mul_smul, ← smul_add, ← smul_sub]
      rw [← Matrix.transpose_map]
      simp only [← RingHom.mapMatrix_apply, map_add, map_sub, map_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hg : g = e2.toLinearMap ∘ₗ f.baseChange K ∘ₗ e1.symm.toLinearMap := by
    ext y : 1
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ← hcomm,
      LinearEquiv.apply_symm_apply]
  have hker : LinearMap.ker g = (LinearMap.ker (f.baseChange K)).map e1.toLinearMap := by
    ext y
    rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker, hg]
    simp
  rw [soCentMat_eq_ker, soCentMat_eq_ker, hker, LinearEquiv.finrank_map_eq]
  exact (LinearMap.tensorKerEquiv K K f).finrank_eq.symm.trans Module.finrank_baseChange

/-- **`so(J)_A` over `K` is spanned by `so(J)_A` over `F`.** -/
theorem soCentMat_map_eq_span {F K : Type*} [Field F] [Field K] [Algebra F K]
    (J A : Matrix n n F) :
    soCentMat (J.map (algebraMap F K)) (A.map (algebraMap F K)) =
      Submodule.span K ((fun M : Matrix n n F => M.map (algebraMap F K)) '' soCentMat J A) := by
  set φ := algebraMap F K
  have hle : Submodule.span K ((fun M : Matrix n n F => M.map φ) '' soCentMat J A) ≤
      soCentMat (J.map φ) (A.map φ) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨M, hM, rfl⟩
    rw [SetLike.mem_coe, soCentMat_eq_ker, LinearMap.mem_ker] at hM ⊢
    have h1 := congrArg (fun p : Matrix n n F × Matrix n n F => p.1.map φ) hM
    have h2 := congrArg (fun p : Matrix n n F × Matrix n n F => p.2.map φ) hM
    simp only [soCentMatMap, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_zero, Prod.snd_zero,
      Matrix.map_zero _ (map_zero φ)] at h1 h2
    simp only [soCentMatMap, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk_eq_zero]
    rw [← Matrix.transpose_map]
    simp only [← RingHom.mapMatrix_apply, ← map_mul, ← map_add, ← map_sub] at h1 h2 ⊢
    exact ⟨h1, h2⟩
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  let b := Module.finBasis F (soCentMat J A)
  have hli : LinearIndependent K fun i => ((b i : Matrix n n F)).map φ := by
    have h1 := Module.Flat.linearIndependent_one_tmul (S := K)
      (b.linearIndependent.map' (soCentMat J A).subtype (Submodule.ker_subtype _))
    have h2 := h1.map' (matrixBaseChangeEquiv (n := n) F K).toLinearMap (LinearEquiv.ker _)
    simpa [Function.comp_def, matrixBaseChangeEquiv_tmul] using h2
  rw [finrank_soCentMat_map, Module.finrank_eq_card_basis b, ← finrank_span_eq_card hli]
  exact Submodule.finrank_mono (Submodule.span_mono (by
    rintro _ ⟨i, rfl⟩; exact ⟨_, (b i).2, rfl⟩))

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
