/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.Steinberg
import GSpinGGP.Foundations.JordanAlgebra

/-!
# Semisimplicity in `GSpin(V)` is detected by `P`

Over a field of characteristic `0`, `x ∈ GSpin(V)` acts semisimply on `C(V)` as soon as
`P(x) ∈ SO(V)` is semisimple (`isSS_of_isSemisimple_specP_baseChange`); the converse is
`isSemisimple_specP_of_isSS`.

Proof.  Write `x = s + n` (additive Jordan–Chevalley decomposition of left multiplication by `x`,
`exists_jordan_algebra`), with `s, n ∈ K[x]`, `s` semisimple and `n`
nilpotent; `s` is a unit.  Conjugation `c_x = L_x R_{x⁻¹}` on `C(V)` is then
`c_s + N` with `c_s = L_s R_{s⁻¹}` semisimple, `N` nilpotent and commuting with `c_s`
(`isNilpotent_conj_sub_conj`); by uniqueness of the decomposition `N` is a polynomial `q(c_x)`
(`conj_mem_adjoin_of_isSemisimple_mulLeft`).  On `ι(V)`, `c_x` acts as `P(x)`, so
`N ∘ ι = ι ∘ q(P(x))` (`ι_aeval_specP`); `q(P(x))` is nilpotent and (over `K̄`) semisimple, hence `0`.  So
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

/-- **`x ∈ GSpin(V)` is semisimple if `P(x)` is** (over a field of characteristic `0`; the
hypothesis is semisimplicity over `K̄`, equivalent to that over `K`).  Converse of
`isSemisimple_specP_of_isSS`.  See the module docstring for the proof. -/
theorem isSS_of_isSemisimple_specP_baseChange {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    (x : GSpin Q)
    (hx : Module.End.IsSemisimple ((specP Q x : V →ₗ[K] V).baseChange (AlgebraicClosure K))) :
    Module.End.IsSemisimple
      (LinearMap.mulLeft K (((x : (CliffordAlgebra Q)ˣ)) : CliffordAlgebra Q)) := by
  set A := CliffordAlgebra Q
  set xU : Aˣ := (x : (CliffordAlgebra Q)ˣ)
  set X : A := (xU : A)
  set B := Algebra.adjoin K {X}
  -- Jordan decomposition `X = s + n` in `K[X]`; `s` is a unit
  obtain ⟨s, hsB, n, -, hLs, hnil, hXsn⟩ := exists_jordan_algebra (F := K) X
  have hn : IsNilpotent (X - s) := by rwa [hXsn, add_sub_cancel_left]
  obtain ⟨sU, rfl⟩ := IsUnit.of_isNilpotent_sub xU.isUnit (Algebra.commute_of_mem_adjoin_self hsB) hn
  set s : A := (sU : A)
  set si : A := ((sU⁻¹ : Aˣ) : A)
  set xi : A := ((xU⁻¹ : Aˣ) : A)
  have hsiB : si ∈ B := Units.inv_mem_adjoin_of_mem_adjoin hsB
  have hssi : s * si = 1 := sU.mul_inv
  have hxxi : xi * X = 1 := xU.inv_mul
  -- `c_x = c_s + N` with `c_s` semisimple, `N` nilpotent commuting, and `N ∈ K[c_x]`
  set c := LinearMap.mulLeft K X * LinearMap.mulRight K xi
  set cs := LinearMap.mulLeft K s * LinearMap.mulRight K si
  obtain ⟨hNnil, -⟩ := isNilpotent_conj_sub_conj hsB hn
  have hN : c - cs ∈ Algebra.adjoin K {c} :=
    Subalgebra.sub_mem _ (Algebra.self_mem_adjoin_singleton K c)
      (conj_mem_adjoin_of_isSemisimple_mulLeft hsB hLs hn)
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hN
  obtain ⟨q, hq⟩ := hN
  replace hq : aeval c q = c - cs := hq
  -- `q(P(x)) = 0`
  set P : Module.End K V := (specP Q x : V →ₗ[K] V) with hPdef
  have hFnil : IsNilpotent (aeval P q) := by
    obtain ⟨k, hk⟩ := hNnil
    refine ⟨k, LinearMap.ext fun v => ι_injective Q ?_⟩
    have := ι_aeval_specP x (q ^ k) v
    simp only [map_pow] at this
    rw [show aeval (LinearMap.mulLeft K
        ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * LinearMap.mulRight K
        (((x : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) q =
        LinearMap.mulLeft K (xU : A) * LinearMap.mulRight K ((xU⁻¹ : Aˣ) : A) -
          LinearMap.mulLeft K (sU : A) * LinearMap.mulRight K ((sU⁻¹ : Aˣ) : A)
      from hq, hk] at this
    simpa using this
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
  have hNι : ∀ v, (c - cs) (ι Q v) = 0 := fun v => by
    rw [← hq, ← ι_aeval_specP x q v, hF, LinearMap.zero_apply, map_zero]
  have hu : ∀ v, ι Q v * (si * X) = (si * X) * ι Q v := by
    intro v
    have h1 := hNι v
    have h2 : c (ι Q v) = cs (ι Q v) := sub_eq_zero.mp h1
    simp only [c, cs, Module.End.mul_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply] at h2
    -- `X ι xi = s ι si` ⇒ `si X ι = ι si X`
    have hsis : si * s = 1 := sU.inv_mul
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
