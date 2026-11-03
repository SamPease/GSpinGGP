/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.GSpin

/-!
# Hyperbolic planes in `GSpin`

For a hyperbolic pair `f, f'` (`Q f = Q f' = 0`, `polar f f' = 1`) in a quadratic space `V`
over a field (the facts about hyperbolic planes themselves are in `Foundations/QuadraticForms`):

* `hypGSpin t = f f' + t f' f ∈ GSpin(V)` lifts that torus: `P(h(t))` scales `f, f'` by `t⁻¹, t` and
  fixes `{f, f'}^⊥` (`specP_hypGSpin`), and `h(t)` commutes with every element of `GSpin(V)` that
  scales `f, f'` by inverse scalars (`commute_hypUnit`).
-/

noncomputable section

open CliffordAlgebra

namespace GSpinGGP

section HypLift

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- For a hyperbolic pair `f, f'` (`Q f = Q f' = 0`, `polar f f' = 1`), `ι f ι f'` and `ι f' ι f`
are complementary orthogonal idempotents. -/
theorem ι_hyperbolicPair_idempotents {f f' : V} (hf : Q f = 0) (hf' : Q f' = 0)
    (hp : QuadraticMap.polar Q f f' = 1) :
    ι Q f * ι Q f' + ι Q f' * ι Q f = 1 ∧
      (ι Q f * ι Q f') * (ι Q f' * ι Q f) = 0 ∧ (ι Q f' * ι Q f) * (ι Q f * ι Q f') = 0 := by
  refine ⟨by rw [ι_mul_ι_add_swap, hp, map_one], ?_, ?_⟩
  · rw [show ι Q f * ι Q f' * (ι Q f' * ι Q f) = ι Q f * (ι Q f' * ι Q f') * ι Q f by
      simp only [mul_assoc], ι_sq_scalar, hf', map_zero, mul_zero, zero_mul]
  · rw [show ι Q f' * ι Q f * (ι Q f * ι Q f') = ι Q f' * (ι Q f * ι Q f) * ι Q f' by
      simp only [mul_assoc], ι_sq_scalar, hf, map_zero, mul_zero, zero_mul]

theorem ι_mul_ι_mul_ι_of_isotropic {f f' : V} (hf : Q f = 0) (hp : QuadraticMap.polar Q f f' = 1) :
    ι Q f * ι Q f' * ι Q f = ι Q f := by
  have h := ι_mul_ι_add_swap (Q := Q) f f'
  rw [hp, map_one] at h
  have e1 : ι Q f' * ι Q f = 1 - ι Q f * ι Q f' := eq_sub_of_add_eq' h
  rw [mul_assoc, e1, mul_sub, mul_one, ← mul_assoc, ι_sq_scalar, hf, map_zero, zero_mul, sub_zero]

variable {f f' : V} (hf : Q f = 0) (hf' : Q f' = 0) (hp : QuadraticMap.polar Q f f' = 1)
include hf hf' hp

/-- `h(t) = f f' + t f' f`, a unit with inverse `h(t⁻¹)`. -/
def hypUnit (t : Kˣ) : (CliffordAlgebra Q)ˣ where
  val := ι Q f * ι Q f' + (t : K) • (ι Q f' * ι Q f)
  inv := ι Q f * ι Q f' + ((t⁻¹ : Kˣ) : K) • (ι Q f' * ι Q f)
  val_inv := by
    obtain ⟨h1, h2, h3⟩ := ι_hyperbolicPair_idempotents hf hf' hp
    have hpp : (ι Q f * ι Q f') * (ι Q f * ι Q f') = ι Q f * ι Q f' := by
      calc _ = (ι Q f * ι Q f') * (ι Q f * ι Q f' + ι Q f' * ι Q f) := by rw [mul_add, h2, add_zero]
        _ = _ := by rw [h1, mul_one]
    have hqq : (ι Q f' * ι Q f) * (ι Q f' * ι Q f) = ι Q f' * ι Q f := by
      calc _ = (ι Q f' * ι Q f) * (ι Q f * ι Q f' + ι Q f' * ι Q f) := by rw [mul_add, h3, zero_add]
        _ = _ := by rw [h1, mul_one]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hpp, hqq, h2, h3, smul_zero,
      add_zero, zero_add, smul_smul, Units.inv_mul, one_smul, h1]
  inv_val := by
    obtain ⟨h1, h2, h3⟩ := ι_hyperbolicPair_idempotents hf hf' hp
    have hpp : (ι Q f * ι Q f') * (ι Q f * ι Q f') = ι Q f * ι Q f' := by
      calc _ = (ι Q f * ι Q f') * (ι Q f * ι Q f' + ι Q f' * ι Q f) := by rw [mul_add, h2, add_zero]
        _ = _ := by rw [h1, mul_one]
    have hqq : (ι Q f' * ι Q f) * (ι Q f' * ι Q f) = ι Q f' * ι Q f := by
      calc _ = (ι Q f' * ι Q f) * (ι Q f * ι Q f' + ι Q f' * ι Q f) := by rw [mul_add, h3, zero_add]
        _ = _ := by rw [h1, mul_one]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hpp, hqq, h2, h3, smul_zero,
      add_zero, zero_add, smul_smul, Units.mul_inv, one_smul, h1]

theorem hypUnit_conj_ι_left (t : Kˣ) :
    (hypUnit hf hf' hp t : CliffordAlgebra Q) * ι Q f *
      ((hypUnit hf hf' hp t)⁻¹ : (CliffordAlgebra Q)ˣ) = ((t⁻¹ : Kˣ) : K) • ι Q f := by
  have k1 := ι_mul_ι_mul_ι_of_isotropic (Q := Q) hf hp
  have hff : ι Q f * ι Q f = 0 := by rw [ι_sq_scalar, hf, map_zero]
  have hA : (ι Q f * ι Q f' + (t : K) • (ι Q f' * ι Q f)) * ι Q f = ι Q f := by
    rw [add_mul, k1, smul_mul_assoc, mul_assoc, hff, mul_zero, smul_zero, add_zero]
  have hB : ι Q f * (ι Q f * ι Q f' + ((t⁻¹ : Kˣ) : K) • (ι Q f' * ι Q f)) =
      ((t⁻¹ : Kˣ) : K) • ι Q f := by
    rw [mul_add, ← mul_assoc, hff, zero_mul, zero_add, mul_smul_comm, ← mul_assoc, k1]
  change (ι Q f * ι Q f' + (t : K) • (ι Q f' * ι Q f)) * ι Q f *
    (ι Q f * ι Q f' + ((t⁻¹ : Kˣ) : K) • (ι Q f' * ι Q f)) = _
  rw [hA, hB]

theorem hypUnit_conj_ι_right (t : Kˣ) :
    (hypUnit hf hf' hp t : CliffordAlgebra Q) * ι Q f' *
      ((hypUnit hf hf' hp t)⁻¹ : (CliffordAlgebra Q)ˣ) = (t : K) • ι Q f' := by
  have hp' : QuadraticMap.polar Q f' f = 1 := by rw [QuadraticMap.polar_comm]; exact hp
  have k1 := ι_mul_ι_mul_ι_of_isotropic (Q := Q) hf' hp'
  have hff : ι Q f' * ι Q f' = 0 := by rw [ι_sq_scalar, hf', map_zero]
  have hA : (ι Q f * ι Q f' + (t : K) • (ι Q f' * ι Q f)) * ι Q f' = (t : K) • ι Q f' := by
    rw [add_mul, mul_assoc, hff, mul_zero, zero_add, smul_mul_assoc, k1]
  have hB : ι Q f' * (ι Q f * ι Q f' + ((t⁻¹ : Kˣ) : K) • (ι Q f' * ι Q f)) = ι Q f' := by
    rw [mul_add, ← mul_assoc, k1, mul_smul_comm, ← mul_assoc, hff, zero_mul, smul_zero, add_zero]
  change (ι Q f * ι Q f' + (t : K) • (ι Q f' * ι Q f)) * ι Q f' *
    (ι Q f * ι Q f' + ((t⁻¹ : Kˣ) : K) • (ι Q f' * ι Q f)) = _
  rw [hA, smul_mul_assoc, hB]

theorem hypUnit_comm_ι_of_orth (t : Kˣ) {w : V} (hw : QuadraticMap.polar Q f w = 0)
    (hw' : QuadraticMap.polar Q f' w = 0) :
    (hypUnit hf hf' hp t : CliffordAlgebra Q) * ι Q w = ι Q w * (hypUnit hf hf' hp t) := by
  have a1 : ι Q w * ι Q f = -(ι Q f * ι Q w) := by
    rw [ι_mul_ι_comm, QuadraticMap.polar_comm, hw, map_zero, zero_sub]
  have a2 : ι Q w * ι Q f' = -(ι Q f' * ι Q w) := by
    rw [ι_mul_ι_comm, QuadraticMap.polar_comm, hw', map_zero, zero_sub]
  change (ι Q f * ι Q f' + (t : K) • (ι Q f' * ι Q f)) * ι Q w =
    ι Q w * (ι Q f * ι Q f' + (t : K) • (ι Q f' * ι Q f))
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_assoc, ← mul_assoc (ι Q w), a1,
    a2, neg_mul, mul_neg, neg_neg]

/-- `h(t)` scales `f` by `t⁻¹`, `f'` by `t` and fixes `{f, f'}^⊥`. -/
theorem hypUnit_conj_ι (t : Kˣ) (v : V) :
    (hypUnit hf hf' hp t : CliffordAlgebra Q) * ι Q v *
      ((hypUnit hf hf' hp t)⁻¹ : (CliffordAlgebra Q)ˣ) =
      ι Q (v + (((t⁻¹ : Kˣ) : K) - 1) • (QuadraticMap.polar Q f' v • f) +
        ((t : K) - 1) • (QuadraticMap.polar Q f v • f')) := by
  set a := QuadraticMap.polar Q f' v
  set b := QuadraticMap.polar Q f v
  set w := v - a • f - b • f'
  have hff : QuadraticMap.polar Q f f = 0 := by rw [QuadraticMap.polar_self, hf, smul_zero]
  have hff' : QuadraticMap.polar Q f' f' = 0 := by rw [QuadraticMap.polar_self, hf', smul_zero]
  have hp' : QuadraticMap.polar Q f' f = 1 := by rw [QuadraticMap.polar_comm]; exact hp
  have hw : QuadraticMap.polar Q f w = 0 := by
    simp only [w, QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right, hff, hp, b]
    ring
  have hw' : QuadraticMap.polar Q f' w = 0 := by
    simp only [w, QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right, hff', hp', a]
    ring
  have hv : v = a • f + b • f' + w := by simp only [w]; abel
  have hcw : (hypUnit hf hf' hp t : CliffordAlgebra Q) * ι Q w *
      ((hypUnit hf hf' hp t)⁻¹ : (CliffordAlgebra Q)ˣ) = ι Q w := by
    rw [hypUnit_comm_ι_of_orth hf hf' hp t hw hw', mul_assoc, Units.mul_inv, mul_one]
  conv_lhs => rw [hv]
  rw [map_add, map_add, map_smul, map_smul, mul_add, mul_add, add_mul, add_mul, mul_smul_comm,
    mul_smul_comm, smul_mul_assoc, smul_mul_assoc, hypUnit_conj_ι_left, hypUnit_conj_ι_right, hcw,
    smul_smul, smul_smul]
  conv_rhs => rw [hv]
  simp only [map_add, map_smul]
  module

theorem hypUnit_inv (t : Kˣ) : (hypUnit hf hf' hp t)⁻¹ = hypUnit hf hf' hp t⁻¹ := by
  ext1; simp [hypUnit]

/-- `h(t) = f f' + t f' f ∈ GSpin(V)`. -/
def hypGSpin (t : Kˣ) : GSpin Q :=
  ⟨hypUnit hf hf' hp t, by
    have h1 : ι Q f * ι Q f' ∈ even Q := by
      rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]; exact ι_mul_ι_mem_evenOdd_zero Q _ _
    have h2 : ι Q f' * ι Q f ∈ even Q := by
      rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]; exact ι_mul_ι_mem_evenOdd_zero Q _ _
    exact add_mem h1 (Subalgebra.smul_mem _ h2 _),
    fun v => ⟨_, (hypUnit_conj_ι hf hf' hp t v).symm⟩,
    fun v => by
      have h := hypUnit_conj_ι hf hf' hp t⁻¹ v
      rw [hypUnit_inv, inv_inv] at h
      rw [hypUnit_inv]
      exact ⟨_, h.symm⟩⟩

theorem coe_hypGSpin (t : Kˣ) :
    ((hypGSpin hf hf' hp t : GSpin Q) : (CliffordAlgebra Q)ˣ) = hypUnit hf hf' hp t := rfl

/-- `P(h(t))`: `f ↦ t⁻¹ f`, `f' ↦ t f'`, identity on `{f, f'}^⊥`. -/
theorem specP_hypGSpin [Invertible (2 : K)] (t : Kˣ) (v : V) :
    specP Q (hypGSpin hf hf' hp t) v =
      v + (((t⁻¹ : Kˣ) : K) - 1) • (QuadraticMap.polar Q f' v • f) +
      ((t : K) - 1) • (QuadraticMap.polar Q f v • f') := by
  apply ι_injective Q
  rw [ι_specP]
  exact hypUnit_conj_ι hf hf' hp t v

/-- An element of `GSpin(V)` scaling `f` and `f'` by inverse scalars commutes with every `h(t)`. -/
theorem commute_hypUnit [Invertible (2 : K)] {g : GSpin Q} {s : Kˣ}
    (hgf : specP Q g f = (s : K) • f)
    (hgf' : specP Q g f' = ((s⁻¹ : Kˣ) : K) • f') (t : Kˣ) :
    Commute ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) (hypUnit hf hf' hp t) := by
  have hc : ∀ u u' : V, ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * (ι Q u * ι Q u') =
      ι Q (specP Q g u) * ι Q (specP Q g u') * (g : (CliffordAlgebra Q)ˣ) := fun u u' => by
    rw [ι_specP, ι_specP]
    simp only [mul_assoc, Units.inv_mul, mul_one, Units.inv_mul_cancel_left]
  have hss : (s : K) * ((s⁻¹ : Kˣ) : K) = 1 := Units.mul_inv s
  change _ * (ι Q f * ι Q f' + (t : K) • (ι Q f' * ι Q f)) =
    (ι Q f * ι Q f' + (t : K) • (ι Q f' * ι Q f)) * _
  rw [mul_add, mul_smul_comm, hc, hc, hgf, hgf', map_smul, map_smul, smul_mul_smul_comm,
    smul_mul_smul_comm, hss, mul_comm ((s⁻¹ : Kˣ) : K), hss, one_smul, one_smul, add_mul,
    smul_mul_assoc]

end HypLift


end GSpinGGP
