/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.RealEmbedding
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.NumberTheory.Ostrowski
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Instances.Rat

/-!
# Archimedean local fields: existence of the real embedding and the cases `ℝ`, `ℂ`

A complete normed field `F` that is not ultrametric has a real embedding (`RealEmbedding F`): by
Ostrowski's theorem the norm restricted to `ℚ` is `|q| ^ c` for some `c > 0`, so `ℚ → F` is
uniformly continuous for the usual metric of `ℚ` and extends to a continuous ring homomorphism
`ℝ →+* F`. With `RealEmbedding.instIsEmpty` this gives the dichotomy for local fields: a
`LocalField` is ultrametric or has a real embedding, and not both.

A real embedding `φ` of a locally compact Hausdorff topological field `F` makes `F` a
finite-dimensional `ℝ`-algebra (Riesz's theorem), hence `ℝ` or `ℂ` (Frobenius, via the
fundamental theorem of algebra). Which case occurs is decided by whether `-1` is a square in `F`.

## Main results

* `charZero_of_not_isUltrametricDist`: a normed division ring that is not ultrametric has
  characteristic zero.
* `exists_norm_ratCast_eq_rpow`: in a normed field that is not ultrametric,
  `‖(q : F)‖ = |q| ^ c` for some `c > 0` (Ostrowski).
* `nonempty_realEmbedding_of_not_isUltrametricDist`: a complete normed field that is not
  ultrametric has a real embedding.
* `not_isUltrametricDist_iff_nonempty_realEmbedding`, `isUltrametricDist_or_nonempty_realEmbedding`:
  the dichotomy for complete normed fields, in particular for every `LocalField`.
* `RealEmbedding.isHomeomorph_of_not_isSquare_neg_one`: if `-1` is not a square, the real
  embedding is a bijective homeomorphism `ℝ → F`.
* `RealEmbedding.exists_ringEquiv_complex_of_isSquare_neg_one`: if `-1` is a square, there is a
  ring isomorphism `ℂ ≃+* F` that is a homeomorphism and extends the real embedding.
-/

namespace GSpinGGP

open Filter Topology

section CharZero

variable {F : Type*} [NormedDivisionRing F]

/-- A normed division ring that is not ultrametric has characteristic zero. Some `‖(m : F)‖` is
`> 1`, so the norms `‖(m ^ k : F)‖ = ‖(m : F)‖ ^ k` are unbounded; in characteristic `p > 0` every
`‖(n : F)‖ = ‖(n % p : F)‖` is at most `p`. -/
theorem charZero_of_not_isUltrametricDist (h : ¬ IsUltrametricDist F) : CharZero F := by
  rw [isUltrametricDist_iff_forall_norm_natCast_le_one] at h
  push Not at h
  obtain ⟨m, hm⟩ := h
  rcases CharP.char_is_prime_or_zero F (ringChar F) with hp | hp
  · exfalso
    set p := ringChar F
    have hbd : ∀ n : ℕ, ‖(n : F)‖ ≤ p := by
      intro n
      rw [CharP.cast_eq_mod F p n]
      refine (Nat.norm_cast_le _).trans ?_
      rw [norm_one, mul_one]
      exact_mod_cast (Nat.mod_lt n hp.pos).le
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (p : ℝ) hm
    have := hbd (m ^ k)
    rw [Nat.cast_pow, norm_pow] at this
    linarith
  · exact (CharP.charP_zero_iff_charZero F).1 (hp ▸ ringChar.charP F)

end CharZero

section Exists

variable {F : Type*} [NormedField F]

/-- **Ostrowski.** In a normed field of characteristic zero that is not ultrametric, the norm
restricted to `ℚ` is a power of the usual absolute value: `‖(q : F)‖ = |q| ^ c` with `c > 0`.
The norm on `ℚ` is unbounded on `ℕ` (`isUltrametricDist_iff_forall_norm_natCast_le_one`), hence
equivalent to the usual absolute value (`Rat.AbsoluteValue.equiv_real_of_unbounded`). -/
theorem exists_norm_ratCast_eq_rpow [CharZero F] (h : ¬ IsUltrametricDist F) :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℚ, ‖(q : F)‖ = |(q : ℝ)| ^ c := by
  let f : AbsoluteValue ℚ ℝ := (NormedField.toAbsoluteValue F).comp (Rat.castHom F).injective
  have hf : ∀ q : ℚ, f q = ‖(q : F)‖ := fun _ => rfl
  have notbdd : ¬ ∀ n : ℕ, f n ≤ 1 := by
    simpa [hf, isUltrametricDist_iff_forall_norm_natCast_le_one] using h
  obtain ⟨c, hc, hfc⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1
    (Rat.AbsoluteValue.equiv_real_of_unbounded notbdd).symm
  refine ⟨c, hc, fun q => ?_⟩
  have := congrFun hfc q
  simp only [Rat.AbsoluteValue.real_eq_abs, Rat.cast_abs] at this
  rw [← hf, ← this]

variable [CompleteSpace F]

/-- A complete normed field that is not ultrametric has a real embedding. It has characteristic
zero, and `‖(q : F)‖ = |q| ^ c` with `c > 0` (`exists_norm_ratCast_eq_rpow`), so the additive map
`ℚ → F` is continuous at `0`, hence uniformly continuous for the usual metric of `ℚ`; it extends
to a continuous ring homomorphism `ℝ →+* F` (`IsDenseInducing.extendRingHom`). -/
theorem nonempty_realEmbedding_of_not_isUltrametricDist (h : ¬ IsUltrametricDist F) :
    Nonempty (RealEmbedding F) := by
  have := charZero_of_not_isUltrametricDist h
  obtain ⟨c, hc, hnorm⟩ := exists_norm_ratCast_eq_rpow h
  have hcont : ContinuousAt (Rat.castHom F) 0 := by
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    have h0 : Tendsto (fun q : ℚ => |(q : ℝ)| ^ c) (𝓝 0) (𝓝 (|((0 : ℚ) : ℝ)| ^ c)) :=
      ((continuous_abs.comp Rat.continuous_coe_real).rpow_const
        (fun _ => Or.inr hc.le)).tendsto 0
    simp only [Rat.cast_zero, abs_zero, Real.zero_rpow hc.ne'] at h0
    simpa [hnorm] using h0
  have huc : UniformContinuous (Rat.castHom F) :=
    uniformContinuous_of_continuousAt_zero _ hcont
  have hue := Rat.isUniformEmbedding_coe_real.isUniformInducing
  refine ⟨⟨IsDenseInducing.extendRingHom (i := Rat.castHom ℝ) hue Rat.denseRange_cast huc, ?_⟩⟩
  exact (uniformContinuous_uniformly_extend hue Rat.denseRange_cast huc).continuous

variable (F) in
/-- A complete normed field is not ultrametric if and only if it has a real embedding. In
particular this holds for every `LocalField`. -/
theorem not_isUltrametricDist_iff_nonempty_realEmbedding :
    ¬ IsUltrametricDist F ↔ Nonempty (RealEmbedding F) :=
  ⟨nonempty_realEmbedding_of_not_isUltrametricDist, fun ⟨φ⟩ _ => IsEmpty.false φ⟩

variable (F) in
/-- A complete normed field (for instance a `LocalField`) is ultrametric or has a real embedding;
not both, by `not_isUltrametricDist_iff_nonempty_realEmbedding`. -/
theorem isUltrametricDist_or_nonempty_realEmbedding :
    IsUltrametricDist F ∨ Nonempty (RealEmbedding F) :=
  or_iff_not_imp_left.2 nonempty_realEmbedding_of_not_isUltrametricDist

end Exists

namespace RealEmbedding

section Algebra

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

/-- The `ℝ`-algebra structure on `F` given by a real embedding `φ`: `r • x = φ r * x`. Not an
instance. -/
abbrev toAlgebra (φ : RealEmbedding F) : Algebra ℝ F := φ.toRingHom.toAlgebra

/-- Scalar multiplication by `ℝ` through a real embedding is continuous. -/
theorem continuousSMul (φ : RealEmbedding F) :
    letI := φ.toAlgebra; ContinuousSMul ℝ F := by
  let := φ.toAlgebra
  refine ⟨?_⟩
  simp only [Algebra.smul_def]
  exact (φ.continuous.comp continuous_fst).mul continuous_snd

variable [T2Space F] [LocallyCompactSpace F]

/-- A locally compact Hausdorff topological field with a real embedding is finite-dimensional
over `ℝ` (Riesz's theorem, `FiniteDimensional.of_locallyCompactSpace`). -/
theorem finiteDimensional (φ : RealEmbedding F) :
    letI := φ.toAlgebra; FiniteDimensional ℝ F := by
  let := φ.toAlgebra
  have := φ.continuousSMul
  exact .of_locallyCompactSpace ℝ

/-- A locally compact Hausdorff topological field with a real embedding is, as an `ℝ`-algebra,
isomorphic to `ℝ` or to `ℂ` (`Real.nonempty_algEquiv_or`). -/
theorem nonempty_algEquiv_or (φ : RealEmbedding F) :
    letI := φ.toAlgebra; Nonempty (F ≃ₐ[ℝ] ℝ) ∨ Nonempty (F ≃ₐ[ℝ] ℂ) := by
  let := φ.toAlgebra
  have := φ.finiteDimensional
  exact Real.nonempty_algEquiv_or F

/-- If `-1` is not a square in `F`, a real embedding is bijective: `F` is not `ℂ`, so it is
`ℝ` as an `ℝ`-algebra. -/
theorem bijective_of_not_isSquare_neg_one (φ : RealEmbedding F) (h : ¬ IsSquare (-1 : F)) :
    Function.Bijective φ := by
  let := φ.toAlgebra
  have H : Nonempty (F ≃ₐ[ℝ] ℝ) ∨ Nonempty (F ≃ₐ[ℝ] ℂ) := φ.nonempty_algEquiv_or
  rcases H with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have he : ∀ r : ℝ, e.symm r = φ r := fun r => e.symm.commutes r
    refine ⟨φ.toRingHom.injective, fun x => ⟨e x, ?_⟩⟩
    rw [← he, e.symm_apply_apply]
  · refine absurd ⟨e.symm Complex.I, ?_⟩ h
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]

/-- If `-1` is not a square in `F`, a real embedding is a homeomorphism `ℝ → F`: it is a bijective
`ℝ`-linear map between finite-dimensional Hausdorff topological vector spaces. -/
theorem isHomeomorph_of_not_isSquare_neg_one (φ : RealEmbedding F) (h : ¬ IsSquare (-1 : F)) :
    IsHomeomorph φ := by
  let := φ.toAlgebra
  have := φ.continuousSMul
  let e : ℝ ≃ₗ[ℝ] F :=
    LinearEquiv.ofBijective (Algebra.linearMap ℝ F) (φ.bijective_of_not_isSquare_neg_one h)
  exact e.toContinuousLinearEquiv.toHomeomorph.isHomeomorph

/-- If `-1` is not a square in `F`, the real embedding is a ring isomorphism `ℝ ≃+* F` that is a
homeomorphism. -/
theorem exists_ringEquiv_real_of_not_isSquare_neg_one (φ : RealEmbedding F)
    (h : ¬ IsSquare (-1 : F)) :
    ∃ e : ℝ ≃+* F, IsHomeomorph e ∧ ∀ r : ℝ, e r = φ r :=
  ⟨RingEquiv.ofBijective φ.toRingHom (φ.bijective_of_not_isSquare_neg_one h),
    φ.isHomeomorph_of_not_isSquare_neg_one h, fun _ => rfl⟩

/-- If `-1` is a square in `F`, then `F` is `ℂ`: there is a ring isomorphism `ℂ ≃+* F` that is a
homeomorphism and restricts to the real embedding on `ℝ`. (`F` is not `ℝ`, where `-1` is not a
square; an `ℝ`-algebra isomorphism `ℂ ≃ₐ[ℝ] F` is continuous both ways, `F` being finite-dimensional
over `ℝ`.) -/
theorem exists_ringEquiv_complex_of_isSquare_neg_one (φ : RealEmbedding F)
    (h : IsSquare (-1 : F)) :
    ∃ e : ℂ ≃+* F, IsHomeomorph e ∧ ∀ r : ℝ, e r = φ r := by
  let := φ.toAlgebra
  have := φ.continuousSMul
  have := φ.finiteDimensional
  have H : Nonempty (F ≃ₐ[ℝ] ℝ) ∨ Nonempty (F ≃ₐ[ℝ] ℂ) := φ.nonempty_algEquiv_or
  rcases H with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · obtain ⟨x, hx⟩ := h
    have : (-1 : ℝ) = e x * e x := by rw [← map_mul, ← hx, map_neg, map_one]
    nlinarith [mul_self_nonneg (e x)]
  · refine ⟨e.symm.toRingEquiv, ?_, fun r => e.symm.commutes r⟩
    exact e.symm.toLinearEquiv.toContinuousLinearEquiv.toHomeomorph.isHomeomorph

end Algebra

end RealEmbedding

end GSpinGGP
