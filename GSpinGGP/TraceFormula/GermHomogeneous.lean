/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.JHatHomogeneous
import GSpinGGP.GGP.Germs
import GSpinGGP.Literature.KottwitzClay

/-!
# Homogeneity of `ĵ(O, ·)` on the centralizer of a semisimple element

For `x ∈ G(F)` semisimple, `O` a nilpotent orbit of `𝔤_x` and `t ∈ F^×`:
`ĵ(O, t² X) = |t|_F^{-dim O} ĵ(O, X)` for `X ∈ 𝔤_x` regular (`jHat_sq_smul_lieCentralizer`).
This is BP (1.8.5) (`jHat_smul_of_mem`) with `λ = t²`, together with `t² O = O`
(`kottwitz_nilpotent_sq_smul`, BP §1.8: "`λO = O` for all `λ ∈ F^{×2}`"); the hypotheses of
`jHat_smul_of_mem` hold for `(G_x, 𝔤_x)`: `b` is nondegenerate on `𝔤_x`
(`restrictForm_lieCentralizer_nondegenerate`), the regular set of `𝔤_x` is open
(`isOpen_setOf_isRegularSS_lieCentralizer`), orbit measures are unique (`isOrbitMeasure_unique`).
Here `dim O = dim 𝔤_x − dim 𝔤_{x,X₀}` for any `X₀ ∈ O`.
-/

noncomputable section

open MeasureTheory Filter Topology

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

theorem absFHalfPow_pow_two (t : F) (k : ℕ) : (absFHalfPow (t ^ 2) k : ℝ) = absF t ^ k := by
  rw [absFHalfPow_coe, absF_pow, ← pow_mul, mul_comm, pow_mul,
    Real.sqrt_sq (pow_nonneg (absF_nonneg _) _)]

/-- **`t² O = O`** for a nilpotent orbit `O` of `𝔤_x`, `x` semisimple
(`kottwitz_nilpotent_sq_smul`). -/
theorem nilScale_sq_eq (d : GGPData F) (x : ↥d.G) (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    {t : F} (ht : t ≠ 0)
    (O : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)))
    (hc𝔤 : ∀ Y ∈ lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient),
      algebraMap F d.ambient (t ^ 2) * Y ∈ lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) :
    nilScale (algebraMap F d.ambient (t ^ 2)) (Algebra.commutes (t ^ 2)) hc𝔤 O = O := by
  induction O using Quotient.inductionOn with | h N => ?_
  rw [nilScale_mk]
  obtain ⟨h, hhx, hhN⟩ := kottwitz_nilpotent_sq_smul d x hx N.2.1 N.2.2 ht
  refine Quotient.sound ⟨((h⁻¹ : ↥d.G) : d.ambientˣ), ⟨(h⁻¹).2, ?_⟩, ?_⟩
  · show ((h⁻¹ : ↥d.G) : d.ambientˣ) ∈ Subgroup.centralizer {((x : ↥d.G) : d.ambientˣ)}
    rw [Subgroup.mem_centralizer_iff]
    rintro m rfl
    have h' : (x : d.ambientˣ) * (h⁻¹ : ↥d.G) = ((h⁻¹ : ↥d.G) : d.ambientˣ) * x := by
      have e : x * h⁻¹ = h⁻¹ * x := by
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hhx, inv_mul_cancel_left]
      exact congrArg Subtype.val e
    exact h'
  · change ((h⁻¹ : ↥d.G) : d.ambientˣ).val * (algebraMap F d.ambient (t ^ 2) * N.1) *
      ((((h⁻¹ : ↥d.G) : d.ambientˣ))⁻¹ : d.ambientˣ).val = N.1
    rw [← Algebra.smul_def, ← hhN]
    simp [mul_assoc]

/-- **`ĵ(O, t² X) = |t|_F^{-dim O} ĵ(O, X)`** on `(G_x, 𝔤_x)`, `x` semisimple, `X ∈ 𝔤_x` regular,
`dim O = dim 𝔤_x − dim 𝔤_{x,X₀}` for any `X₀ ∈ O` (BP Astérisque 418, (1.8.5) and §1.8). -/
theorem jHat_sq_smul_lieCentralizer (d : GGPData F) (ψ : NontrivialAddChar F) (x : ↥d.G)
    (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    (O : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)))
    {X₀ : ↥(lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))} (hX₀ : X₀ ∈ nilOrbitSet O)
    {t : F} (ht : t ≠ 0) (X : d.ambient)
    (hX : X ∈ lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))
    (hXr : IsRegularSS (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) X) :
    jHat (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) d.bilin ψ O
        ((t ^ 2) • X) =
      (((absF t ^ (Module.finrank F ↥(lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) -
          Module.finrank F ↥(lieCentralizer (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))
            (X₀ : d.ambient))) : ℝ)⁻¹ : ℝ) : ℂ) *
        jHat (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))
          d.bilin ψ O X := by
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have hG : ∀ g ∈ grpCentralizer d.G x, ∀ Y ∈ lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient),
      (g : d.ambient) * Y * (↑g⁻¹ : d.ambient) ∈
        lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient) :=
    fun g hg Y hY => conj_mem_lieCentralizer d.conj_mem_lie_of_mem hg hY
  have h := jHat_smul_of_mem ψ ht2 hG (restrictForm_lieCentralizer_nondegenerate d x hx)
    (isOpen_setOf_isRegularSS_lieCentralizer d x hx)
    (fun O' μ ν hμ hν => isOrbitMeasure_unique d ψ x hx O' μ ν hμ hν) O hX₀ X hX hXr
  rw [h, nilScale_sq_eq d x hx ht, absFHalfPow_pow_two]

end GSpinGGP
