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

section Centralizer

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

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
    obtain ⟨Y, hYq, hY⟩ := exists_mem_quadratic_commutator_eq hQ M hMs
    have hYg : Y ∈ gspin Q := by
      refine quadraticLieSubalgebra_toSubmodule_le_of_bivector_mem Q (P := (gspin Q).toSubmodule)
        (fun a b => ?_) hYq
      rw [bivector_def]
      exact (gspin Q).smul_mem _ (Submodule.sub_mem (gspin Q).toSubmodule
        (ι_mul_ι_mem_gspin Q a b) (ι_mul_ι_mem_gspin Q b a))
    have hYM : adV Q Y = M := by
      ext v; apply ι_injective Q; rw [ι_adV hYg, hY]
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

/-- For `A ∈ gspin(V)`: `A` commutes with `g ∈ GSpin(V)` iff `adV A` commutes with `P(g)` (a
scalar difference `g A g⁻¹ − A` is traceless, hence `0`). -/
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
    have hC : (u : CliffordAlgebra Q) * A * ((u⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - A ∈
        gspin Q := sub_mem (conj_mem_gspin Q g hA) hA
    obtain ⟨r, hr⟩ := eq_algebraMap_of_adV_eq_zero hQ hC (by
      ext v
      have e := LinearMap.congr_fun h (specP Q g⁻¹ v)
      simp only [Module.End.mul_apply, LinearEquiv.coe_coe] at e
      rw [map_sub, LinearMap.sub_apply, hconj, e, specP_inv_apply_apply, sub_self,
        LinearMap.zero_apply])
    have htr : LinearMap.trace K _ (LinearMap.mulLeft K ((u : CliffordAlgebra Q) * A *
        ((u⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - A)) = 0 := by
      rw [show LinearMap.mulLeft K ((u : CliffordAlgebra Q) * A *
          ((u⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - A) =
          LinearMap.mulLeft K ((u : CliffordAlgebra Q) * (A *
          ((u⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))) - LinearMap.mulLeft K A by
            ext; simp [sub_mul, mul_assoc],
        map_sub, trace_mulLeft_comm, mul_assoc, Units.inv_mul, mul_one, sub_self]
    have hsc : LinearMap.mulLeft K (algebraMap K (CliffordAlgebra Q) r) = r • LinearMap.id := by
      ext z; simp [Algebra.smul_def]
    rw [hr, hsc, map_smul, LinearMap.trace_id, smul_eq_mul] at htr
    have hr0 : r = 0 := (mul_eq_zero.mp htr).resolve_right (cast_finrank_cliffordAlgebra_ne_zero Q)
    rw [hr0, map_zero, sub_eq_zero] at hr
    calc (u : CliffordAlgebra Q) * A
        = (u : CliffordAlgebra Q) * A * ((u⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
          (u : CliffordAlgebra Q) := by rw [mul_assoc _ _ (u : CliffordAlgebra Q), Units.inv_mul, mul_one]
      _ = A * u := by rw [hr]

/-- **`dim gspin(V)_{g,Y} = 1 + dim so(V)_{P(g), adV Y}`** for `g ∈ GSpin(V)` and `Y ∈ gspin(V)`:
`adV` maps the joint centralizer onto the joint centralizer of `P(g)` and `adV Y` in `so(V)`
(`commute_iff_adV`), with kernel the scalars. -/
theorem finrank_lieCentralizer_lieCentralizer_gspin {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    (g : GSpin Q) {Y : CliffordAlgebra Q} (hY : Y ∈ gspin Q) :
    finrank K (lieCentralizer (lieCentralizer (gspin Q) ((g : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q)) Y) =
      finrank K ↥(soCent Q (specP Q g : Module.End K V) ⊓ soCent Q (adV Q Y)) + 1 := by
  set x : CliffordAlgebra Q := ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  have hmem : ∀ {Z}, Z ∈ lieCentralizer (lieCentralizer (gspin Q) x) Y ↔
      Z ∈ gspin Q ∧ x * Z = Z * x ∧ Y * Z = Z * Y := by
    intro Z; rw [mem_lieCentralizer, mem_lieCentralizer, and_assoc]
  have hYcomm : ∀ {Z}, Z ∈ gspin Q → Y * Z = Z * Y → adV Q Z * adV Q Y = adV Q Y * adV Q Z := by
    intro Z hZ h
    have := adV_commutator hZ hY
    rw [← h, sub_self, map_zero] at this
    exact sub_eq_zero.mp this.symm
  let φ : lieCentralizer (lieCentralizer (gspin Q) x) Y →ₗ[K]
      ↥(soCent Q (specP Q g : Module.End K V) ⊓ soCent Q (adV Q Y)) :=
    { toFun := fun Z => ⟨adV Q Z, by
        obtain ⟨hZ, hx, hYZ⟩ := hmem.mp Z.2
        refine Submodule.mem_inf.mpr ⟨mem_soCent.2 ⟨bform_adV hZ, ?_⟩,
          mem_soCent.2 ⟨bform_adV hZ, hYcomm hZ hYZ⟩⟩
        exact ((commute_iff_adV hQ g hZ).mp hx).symm⟩
      map_add' := fun Y Z => Subtype.ext (map_add (adV Q) Y.1 Z.1)
      map_smul' := fun c Y => Subtype.ext (map_smul (adV Q) c Y.1) }
  have hsurj : Function.Surjective φ := by
    rintro ⟨M, hM⟩
    obtain ⟨hMg, hMN⟩ := Submodule.mem_inf.mp hM
    obtain ⟨hMs, hMgc⟩ := mem_soCent.mp hMg
    obtain ⟨-, hMNc⟩ := mem_soCent.mp hMN
    obtain ⟨Z, hZq, hZ⟩ := exists_mem_quadratic_commutator_eq hQ M hMs
    have hZg : Z ∈ gspin Q := by
      refine quadraticLieSubalgebra_toSubmodule_le_of_bivector_mem Q (P := (gspin Q).toSubmodule)
        (fun a b => ?_) hZq
      rw [bivector_def]
      exact (gspin Q).smul_mem _ (Submodule.sub_mem (gspin Q).toSubmodule
        (ι_mul_ι_mem_gspin Q a b) (ι_mul_ι_mem_gspin Q b a))
    have hZM : adV Q Z = M := by
      ext v; apply ι_injective Q; rw [ι_adV hZg, hZ]
    -- `Z` commutes with `Y` (traceless scalar commutator)
    have hC : Z * Y - Y * Z ∈ gspin Q := by
      have := (gspin Q).lie_mem hZg hY; rwa [Ring.lie_def] at this
    obtain ⟨r, hr⟩ := eq_algebraMap_of_adV_eq_zero hQ hC
      (by rw [adV_commutator hZg hY, hZM, hMNc, sub_self])
    have htr : LinearMap.trace K _ (LinearMap.mulLeft K (Z * Y - Y * Z)) = 0 := by
      rw [show LinearMap.mulLeft K (Z * Y - Y * Z) =
          LinearMap.mulLeft K (Z * Y) - LinearMap.mulLeft K (Y * Z) by ext; simp [sub_mul, mul_assoc],
        map_sub, trace_mulLeft_comm, sub_self]
    have hsc : ∀ r : K, LinearMap.mulLeft K (algebraMap K (CliffordAlgebra Q) r) = r • LinearMap.id := by
      intro r; ext z; simp [Algebra.smul_def]
    rw [hr, hsc, map_smul, LinearMap.trace_id, smul_eq_mul] at htr
    have hr0 : r = 0 := (mul_eq_zero.mp htr).resolve_right (cast_finrank_cliffordAlgebra_ne_zero Q)
    rw [hr0, map_zero, sub_eq_zero] at hr
    have hxZ : x * Z = Z * x := (commute_iff_adV hQ g hZg).mpr (by rw [hZM]; exact hMgc.symm)
    exact ⟨⟨Z, hmem.mpr ⟨hZg, hxZ, hr.symm⟩⟩, Subtype.ext hZM⟩
  have hker : finrank K (LinearMap.ker φ) = 1 := by
    have h1 : (1 : CliffordAlgebra Q) ∈ lieCentralizer (lieCentralizer (gspin Q) x) Y :=
      hmem.mpr ⟨one_mem_gspin Q, by rw [one_mul, mul_one], by rw [one_mul, mul_one]⟩
    let e : LinearMap.ker φ := ⟨⟨1, h1⟩, Subtype.ext (by
      show adV Q 1 = 0
      rw [← map_one (algebraMap K (CliffordAlgebra Q)), adV_algebraMap])⟩
    have he : e ≠ 0 := fun h => one_ne_zero (congrArg (fun z : LinearMap.ker φ => (z.1.1 : CliffordAlgebra Q)) h)
    refine (finrank_eq_one_iff_of_nonzero' e he).2 fun ⟨⟨Z, hZ⟩, hZk⟩ => ?_
    have hZ0 : adV Q Z = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hZk)
    obtain ⟨r, rfl⟩ := eq_algebraMap_of_adV_eq_zero hQ (hmem.mp hZ).1 hZ0
    exact ⟨r, Subtype.ext (Subtype.ext (by simp [e, Algebra.algebraMap_eq_smul_one]))⟩
  rw [← LinearMap.finrank_range_add_finrank_ker φ, LinearMap.range_eq_top.2 hsurj, finrank_top, hker]

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

/-- **`dim so(J)_A` is unchanged by extension of scalars.** -/
theorem finrank_soCentMat_map {F K : Type*} [Field F] [Field K] [Algebra F K]
    (J A : Matrix n n F) :
    Module.finrank K (soCentMat (J.map (algebraMap F K)) (A.map (algebraMap F K))) =
      Module.finrank F (soCentMat J A) := by
  set f := soCentMatMap J A
  -- `K ⊗ Mat_n(F) ≅ Mat_n(K)`, `K`-linearly
  let e1 : K ⊗[F] Matrix n n F ≃ₗ[K] Matrix n n K :=
    { (matrixEquivTensor n F K).symm.toLinearEquiv with
      map_smul' := fun c x => by
        show (matrixEquivTensor n F K).symm (c • x) = c • (matrixEquivTensor n F K).symm x
        induction x using TensorProduct.inductionOn with
        | tmul a M =>
          rw [TensorProduct.smul_tmul', matrixEquivTensor_apply_symm, matrixEquivTensor_apply_symm,
            smul_smul, smul_eq_mul]
        | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add] }
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
