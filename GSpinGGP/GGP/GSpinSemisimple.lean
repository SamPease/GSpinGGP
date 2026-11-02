/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.Steinberg
import TauCeti.RingTheory.Adjoin.Unit

/-!
# Semisimplicity in `GSpin(V)` is detected by `P`

Over a field of characteristic `0`, `x ∈ GSpin(V)` acts semisimply on `C(V)` as soon as
`P(x) ∈ SO(V)` is semisimple (`isSS_of_isSemisimple_specP_baseChange`); the converse is
`isSemisimple_specP_of_isSS`.

Proof.  Write `x = s + n` (additive Jordan–Chevalley decomposition of left multiplication by `x`,
`Module.End.exists_isNilpotent_isSemisimple`), with `s, n ∈ K[x]`, `s` semisimple and `n`
nilpotent; `s` is a unit.  Conjugation `c_x = L_x R_{x⁻¹}` on `C(V)` is then
`c_s + N` with `c_s = L_s R_{s⁻¹}` semisimple, `N` nilpotent and commuting with `c_s`; by uniqueness
of the decomposition `N` is a polynomial `q(c_x)`.  On `ι(V)`, `c_x` acts as `P(x)`, so
`N ∘ ι = ι ∘ q(P(x))`; `q(P(x))` is nilpotent and (over `K̄`) semisimple, hence `0`.  So
`x ι(v) x⁻¹ = s ι(v) s⁻¹`: the even element `s⁻¹ x` commutes with `ι(V)`, hence is a scalar `r`
(`eq_algebraMap_of_commute_ι`), and `x = r s` is semisimple.
-/

noncomputable section

open Module Polynomial CliffordAlgebra
open scoped TensorProduct

namespace GSpinGGP

variable {K : Type*} [Field K]

variable [CharZero K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [CharZero K] [FiniteDimensional K V] in
/-- `aeval q (c_x) ∘ ι = ι ∘ aeval q (P(x))`, where `c_x = L_x R_{x⁻¹}`. -/
theorem aeval_conj_ι {Q : QuadraticForm K V} (x : GSpin Q) (q : K[X]) (v : V) :
    aeval (LinearMap.mulLeft K ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        LinearMap.mulRight K (((x : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) :
          CliffordAlgebra Q)) q (ι Q v) =
      ι Q (aeval (specP Q x : V →ₗ[K] V) q v) := by
  set c := LinearMap.mulLeft K ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
    LinearMap.mulRight K (((x : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q) with hc
  have hpow : ∀ k : ℕ, ∀ w : V, (c ^ k) (ι Q w) = ι Q (((specP Q x : V →ₗ[K] V) ^ k) w) := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      have h1 : c (ι Q w) = ι Q ((specP Q x : V →ₗ[K] V) w) := by
        rw [hc, Module.End.mul_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
          show ((specP Q x : V →ₗ[K] V) w) = specP Q x w from rfl, ι_specP, mul_assoc]
      simp only [pow_succ, Module.End.mul_apply]
      rw [h1, ih]
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial k a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, hpow]

omit [CharZero K] [Invertible (2 : K)] in
/-- `L_a R_b` and `L_{a'} R_{b'}` commute when `a, a'` and `b, b'` do. -/
theorem commute_mulLeft_mul_mulRight {A : Type*} [Ring A] [Algebra K A] {a a' b b' : A}
    (ha : Commute a a') (hb : Commute b b') :
    Commute (LinearMap.mulLeft K a * LinearMap.mulRight K b)
      (LinearMap.mulLeft K a' * LinearMap.mulRight K b') := by
  refine LinearMap.ext fun z => ?_
  simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  simp only [mul_assoc]
  rw [show b' * b = b * b' from hb.eq.symm, ← mul_assoc a, ← mul_assoc a', ha.eq]

/-- **`x ∈ GSpin(V)` is semisimple if `P(x)` is** (over a field of characteristic `0`; the
hypothesis is semisimplicity over `K̄`, equivalent to that over `K`).  Converse of
`isSemisimple_specP_of_isSS`.  See the module docstring for the proof. -/
theorem isSS_of_isSemisimple_specP_baseChange {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    (x : GSpin Q)
    (hx : Module.End.IsSemisimple ((specP Q x : V →ₗ[K] V).baseChange (AlgebraicClosure K))) :
    Module.End.IsSemisimple
      (LinearMap.mulLeft K (((x : (CliffordAlgebra Q)ˣ)) : CliffordAlgebra Q)) := by
  set A := CliffordAlgebra Q
  set X : A := ((x : (CliffordAlgebra Q)ˣ) : A) with hXdef
  set B := Algebra.adjoin K {X} with hBdef
  have hXB : X ∈ B := Algebra.subset_adjoin (Set.mem_singleton X)
  -- elements of `K[X]` commute
  have hcommX : ∀ {a}, a ∈ B → Commute X a := fun ha =>
    Algebra.commute_of_mem_adjoin_singleton_of_commute ha (Commute.refl X)
  have hcomm : ∀ {a b}, a ∈ B → b ∈ B → Commute a b := fun ha hb =>
    (Algebra.commute_of_mem_adjoin_singleton_of_commute hb (hcommX ha).symm)
  have hL : Function.Injective (Algebra.lmul K A) := fun a b h => by
    simpa using congrArg (fun f : Module.End K A => f 1) h
  -- Jordan–Chevalley decomposition of `L_X`, transported to `K[X]`
  obtain ⟨n', hn', s', hs', hnil', hss', hsum'⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := LinearMap.mulLeft K X)
  have hmap : Algebra.adjoin K {LinearMap.mulLeft K X} = B.map (Algebra.lmul K A) := by
    rw [hBdef, AlgHom.map_adjoin_singleton]; rfl
  rw [hmap] at hn' hs'
  obtain ⟨n, hnB, rfl⟩ := hn'
  obtain ⟨s, hsB, rfl⟩ := hs'
  have hXns : X = n + s := hL (by rw [map_add]; exact hsum')
  have hnil : IsNilpotent n := by
    obtain ⟨k, hk⟩ := hnil'
    exact ⟨k, hL (by rw [map_pow, map_zero]; exact hk)⟩
  have hLs : Module.End.IsSemisimple (LinearMap.mulLeft K s) := hss'
  -- `s` is a unit, `s⁻¹ ∈ K[X]`, `X⁻¹ ∈ K[X]`
  set xU : Aˣ := (x : (CliffordAlgebra Q)ˣ) with hxU
  have hXn : Commute X n := hcommX hnB
  have hsU : IsUnit s := by
    have hm : IsNilpotent ((↑xU⁻¹ : A) * n) :=
      Commute.isNilpotent_mul_left (hXn.units_inv_left) hnil
    have : s = X * (1 - (↑xU⁻¹ : A) * n) := by
      rw [mul_sub, mul_one, ← mul_assoc, show X * (↑xU⁻¹ : A) = 1 from xU.mul_inv, one_mul, hXns,
        add_sub_cancel_left]
    rw [this]
    exact xU.isUnit.mul hm.isUnit_one_sub
  set sU := hsU.unit with hsUdef
  have hsUs : (sU : A) = s := hsU.unit_spec
  set si : A := ((sU⁻¹ : Aˣ) : A) with hsidef
  set xi : A := ((xU⁻¹ : Aˣ) : A) with hxidef
  have hsi_adj : si ∈ Algebra.adjoin K {s} := by
    have := TauCeti.Units.coe_inv_mem_adjoin sU (IsIntegral.of_finite K (sU : A))
    rwa [hsUs] at this
  have hsiB : si ∈ B := Algebra.adjoin_singleton_le hsB hsi_adj
  have hxiB : xi ∈ B := TauCeti.Units.coe_inv_mem_adjoin xU (IsIntegral.of_finite K (xU : A))
  have hssi : s * si = 1 := by rw [← hsUs]; exact sU.mul_inv
  have hxxi : xi * X = 1 := xU.inv_mul
  -- `c_s = L_s R_{s⁻¹}` is semisimple
  have hLsi : Module.End.IsSemisimple (LinearMap.mulLeft K si) := by
    refine hLs.of_mem_adjoin_singleton ?_
    have : (Algebra.adjoin K {s}).map (Algebra.lmul K A) =
        Algebra.adjoin K {LinearMap.mulLeft K s} := by
      rw [AlgHom.map_adjoin_singleton]; rfl
    rw [← this]
    exact ⟨si, hsi_adj, rfl⟩
  have hcs : Module.End.IsSemisimple (LinearMap.mulLeft K s * LinearMap.mulRight K si) :=
    Module.End.IsSemisimple.mul_of_commute (LinearMap.commute_mulLeft_right s si) hLs
      (isSemisimple_mulRight_of_mulLeft hLsi)
  -- the nilpotent part `N = c_x − c_s = L_n R_{X⁻¹} + L_s R_w`, `w = X⁻¹ − s⁻¹`
  set w : A := xi - si with hwdef
  have hwB : w ∈ B := B.sub_mem hxiB hsiB
  have hw : w = -(xi * n * si) := by
    have : xi * n * si = xi * (X - s) * si := by rw [hXns, add_sub_cancel_right]
    rw [this, mul_sub, sub_mul, mul_assoc xi s si, hssi, mul_one, hxxi, one_mul, neg_sub]
  have hwnil : IsNilpotent w := by
    rw [hw]
    refine IsNilpotent.neg ?_
    refine Commute.isNilpotent_mul_right ?_ ?_
    · exact (hcomm (B.mul_mem hxiB hnB) hsiB)
    · exact Commute.isNilpotent_mul_left (hcomm hxiB hnB) hnil
  set c := LinearMap.mulLeft K X * LinearMap.mulRight K xi with hcdef
  set cs := LinearMap.mulLeft K s * LinearMap.mulRight K si with hcsdef
  set T1 := LinearMap.mulLeft K n * LinearMap.mulRight K xi with hT1
  set T2 := LinearMap.mulLeft K s * LinearMap.mulRight K w with hT2
  have hcN : c = T1 + T2 + cs := by
    refine LinearMap.ext fun z => ?_
    simp only [hcdef, hT1, hT2, hcsdef, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.mulLeft_apply, LinearMap.mulRight_apply, hwdef, hXns]
    noncomm_ring
  have hT1nil : IsNilpotent T1 := by
    refine Commute.isNilpotent_mul_right (LinearMap.commute_mulLeft_right n xi) ?_
    obtain ⟨k, hk⟩ := hnil
    exact ⟨k, by rw [LinearMap.pow_mulLeft, hk, LinearMap.mulLeft_zero_eq_zero]⟩
  have hT2nil : IsNilpotent T2 := by
    refine Commute.isNilpotent_mul_left (LinearMap.commute_mulLeft_right s w) ?_
    obtain ⟨k, hk⟩ := hwnil
    exact ⟨k, by rw [LinearMap.pow_mulRight, hk, LinearMap.mulRight_zero_eq_zero]⟩
  have hNnil : IsNilpotent (T1 + T2) :=
    (commute_mulLeft_mul_mulRight (hcomm hnB hsB) (hcomm hxiB hwB)).isNilpotent_add hT1nil hT2nil
  have hNcs : Commute (T1 + T2) cs :=
    ((commute_mulLeft_mul_mulRight (hcomm hnB hsB) (hcomm hxiB hsiB))).add_left
      (commute_mulLeft_mul_mulRight (hcomm hsB hsB) (hcomm hwB hsiB))
  -- uniqueness of the Jordan–Chevalley decomposition: `N` is a polynomial in `c_x`
  obtain ⟨N0, hN0, S0, hS0, hN0nil, hS0ss, hc0⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := c)
  have hN0S0 : Commute N0 S0 :=
    (Algebra.commute_of_mem_adjoin_singleton_of_commute hS0
      (Algebra.commute_of_mem_adjoin_singleton_of_commute hN0 (Commute.refl c)).symm)
  have hNeq := (Module.End.isNilpotent_isSemisimple_unique hNnil hcs hN0nil hS0ss hNcs hN0S0
    (hcN.symm.trans hc0)).1
  rw [Algebra.adjoin_singleton_eq_range_aeval, ← hNeq] at hN0
  obtain ⟨q, hq⟩ := hN0
  replace hq : aeval c q = T1 + T2 := hq
  -- `q(P(x)) = 0`
  set P : Module.End K V := (specP Q x : V →ₗ[K] V) with hPdef
  have hFnil : IsNilpotent (aeval P q) := by
    obtain ⟨k, hk⟩ := hNnil
    refine ⟨k, LinearMap.ext fun v => ι_injective Q ?_⟩
    have := aeval_conj_ι x (q ^ k) v
    rw [map_pow, show (aeval (LinearMap.mulLeft K X * LinearMap.mulRight K xi)) q = T1 + T2
      from hq, hk] at this
    simpa using this.symm
  have hF : aeval P q = 0 := by
    have hbc : (aeval P q).baseChange (AlgebraicClosure K) =
        aeval (P.baseChange (AlgebraicClosure K)) q :=
      (aeval_algHom_apply (Module.End.baseChangeHom K (AlgebraicClosure K) V) P q).symm
    have h0 : (aeval P q).baseChange (AlgebraicClosure K) = 0 := by
      have hss := hx.aeval (q.map (algebraMap K (AlgebraicClosure K)))
      rw [aeval_map_algebraMap, ← hbc] at hss
      refine Module.End.eq_zero_of_isNilpotent_isSemisimple ?_ hss
      obtain ⟨k, hk⟩ := hFnil
      exact ⟨k, by rw [← LinearMap.baseChange_pow, hk, LinearMap.baseChange_zero]⟩
    refine LinearMap.ext fun v => Module.Flat.tensorProduct_mk_injective K V (AlgebraicClosure K) ?_
    have := LinearMap.congr_fun h0 (1 ⊗ₜ v)
    simpa using this
  -- so `X ι(v) X⁻¹ = s ι(v) s⁻¹`, and `u = s⁻¹ X` commutes with `ι(V)`
  have hNι : ∀ v, (T1 + T2) (ι Q v) = 0 := fun v => by
    rw [← hq, aeval_conj_ι x q v, hF, LinearMap.zero_apply, map_zero]
  have hu : ∀ v, ι Q v * (si * X) = (si * X) * ι Q v := by
    intro v
    have h1 := hNι v
    have h2 : c (ι Q v) = cs (ι Q v) := by rw [hcN, LinearMap.add_apply, h1, zero_add]
    simp only [hcdef, hcsdef, Module.End.mul_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply] at h2
    -- `X ι xi = s ι si` ⇒ `si X ι = ι si X`
    have hsis : si * s = 1 := by rw [← hsUs]; exact sU.inv_mul
    have h3 := congrArg (fun a => si * a * X) h2
    simp only [mul_assoc] at h3 ⊢
    rw [hxxi, mul_one, ← mul_assoc si s, hsis, one_mul] at h3
    exact h3.symm
  -- `s⁻¹ X` is even, hence a scalar `r`, and `X = r s`
  have heven : si * X ∈ evenOdd Q 0 := by
    rw [← even_toSubmodule]
    have hXe : X ∈ even Q := x.2.1
    have hBe : B ≤ even Q := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hXe)
    exact (even Q).mul_mem (hBe hsiB) hXe
  obtain ⟨r, hr⟩ := eq_algebraMap_of_commute_ι hQ heven hu
  have hXr : X = r • s := by
    have : X = s * (si * X) := by rw [← mul_assoc, hssi, one_mul]
    rw [this, hr, ← Algebra.commutes, Algebra.smul_def]
  rw [show LinearMap.mulLeft K X = r • LinearMap.mulLeft K s by
    rw [hXr]; ext z; simp]
  exact Module.End.IsSemisimple_smul r hLs

end GSpinGGP
