/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.GSpin

/-!
# Hyperbolic planes in `GSpin`

For a hyperbolic pair `f, f'` (`Q f = Q f' = 0`, `polar f f' = 1`) in a quadratic space `V`
over a field with `2` invertible:

* `exists_hyp_pair_of_isotropic`: a nondegenerate form with an isotropic vector has a hyperbolic
  pair; `linearIndependent_hyp_pair`;
* `exists_smul_of_isometry_det_one`: `SO` of a hyperbolic plane is the split torus scaling `f, f'`
  by `t⁻¹, t`;
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
theorem hyp_idem {f f' : V} (hf : Q f = 0) (hf' : Q f' = 0) (hp : QuadraticMap.polar Q f f' = 1) :
    ι Q f * ι Q f' + ι Q f' * ι Q f = 1 ∧
      (ι Q f * ι Q f') * (ι Q f' * ι Q f) = 0 ∧ (ι Q f' * ι Q f) * (ι Q f * ι Q f') = 0 := by
  refine ⟨by rw [ι_mul_ι_add_swap, hp, map_one], ?_, ?_⟩
  · rw [show ι Q f * ι Q f' * (ι Q f' * ι Q f) = ι Q f * (ι Q f' * ι Q f') * ι Q f by
      simp only [mul_assoc], ι_sq_scalar, hf', map_zero, mul_zero, zero_mul]
  · rw [show ι Q f' * ι Q f * (ι Q f * ι Q f') = ι Q f' * (ι Q f * ι Q f) * ι Q f' by
      simp only [mul_assoc], ι_sq_scalar, hf, map_zero, mul_zero, zero_mul]

theorem ι_mul_ι_mul_ι_of_polar {f f' : V} (hf : Q f = 0) (hp : QuadraticMap.polar Q f f' = 1) :
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
    obtain ⟨h1, h2, h3⟩ := hyp_idem hf hf' hp
    have hpp : (ι Q f * ι Q f') * (ι Q f * ι Q f') = ι Q f * ι Q f' := by
      calc _ = (ι Q f * ι Q f') * (ι Q f * ι Q f' + ι Q f' * ι Q f) := by rw [mul_add, h2, add_zero]
        _ = _ := by rw [h1, mul_one]
    have hqq : (ι Q f' * ι Q f) * (ι Q f' * ι Q f) = ι Q f' * ι Q f := by
      calc _ = (ι Q f' * ι Q f) * (ι Q f * ι Q f' + ι Q f' * ι Q f) := by rw [mul_add, h3, zero_add]
        _ = _ := by rw [h1, mul_one]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hpp, hqq, h2, h3, smul_zero,
      add_zero, zero_add, smul_smul, Units.inv_mul, one_smul, h1]
  inv_val := by
    obtain ⟨h1, h2, h3⟩ := hyp_idem hf hf' hp
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
  have k1 := ι_mul_ι_mul_ι_of_polar (Q := Q) hf hp
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
  have k1 := ι_mul_ι_mul_ι_of_polar (Q := Q) hf' hp'
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

section HypPair

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- A nondegenerate form with an isotropic vector `f ≠ 0` has a hyperbolic pair `f, f'`. -/
theorem exists_hyp_pair_of_isotropic (hQ : IsNondeg Q) {f : V} (hf0 : f ≠ 0) (hf : Q f = 0) :
    ∃ f', Q f' = 0 ∧ QuadraticMap.polar Q f f' = 1 := by
  have : ∃ u, QuadraticMap.polar Q f u ≠ 0 := by
    by_contra h
    push Not at h
    refine hf0 ((isNondeg_iff Q).mp hQ f fun u => ?_)
    have := QuadraticMap.associated_apply K Q f u
    rw [bform, this]
    have h2 := h u
    rw [QuadraticMap.polar] at h2
    rw [h2, smul_zero]
  obtain ⟨u, hu⟩ := this
  obtain ⟨u₁, hu₁⟩ : ∃ u₁, QuadraticMap.polar Q f u₁ = 1 :=
    ⟨(QuadraticMap.polar Q f u)⁻¹ • u, by
      rw [QuadraticMap.polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hu]⟩
  have hu₁' : QuadraticMap.polar Q u₁ f = 1 := by rw [QuadraticMap.polar_comm]; exact hu₁
  refine ⟨u₁ + (-Q u₁) • f, ?_, ?_⟩
  · have hpol : QuadraticMap.polar Q u₁ ((-Q u₁) • f) =
        Q (u₁ + (-Q u₁) • f) - Q u₁ - Q ((-Q u₁) • f) := rfl
    rw [QuadraticMap.polar_smul_right, hu₁', QuadraticMap.map_smul, hf] at hpol
    simp only [smul_eq_mul, mul_one, mul_zero, sub_zero] at hpol
    linear_combination -hpol
  · rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, QuadraticMap.polar_self, hf,
      smul_zero, smul_zero, add_zero, hu₁]

omit [Invertible (2 : K)] in
/-- A hyperbolic pair is linearly independent. -/
theorem linearIndependent_hyp_pair {f f' : V} (hf : Q f = 0) (hf' : Q f' = 0)
    (hp : QuadraticMap.polar Q f f' = 1) : LinearIndependent K ![f, f'] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hff : QuadraticMap.polar Q f f = 0 := by rw [QuadraticMap.polar_self, hf, smul_zero]
  have hff' : QuadraticMap.polar Q f' f' = 0 := by rw [QuadraticMap.polar_self, hf', smul_zero]
  have hp' : QuadraticMap.polar Q f' f = 1 := by rw [QuadraticMap.polar_comm]; exact hp
  have h1 := congrArg (QuadraticMap.polar Q f) hab
  have h2 := congrArg (QuadraticMap.polar Q f') hab
  simp only [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, hff, hp, hff', hp',
    smul_eq_mul, QuadraticMap.polar_zero_right] at h1 h2
  exact ⟨by simpa using h2, by simpa using h1⟩

/-- **`SO` of a hyperbolic plane is a split torus**: an isometry of determinant `1` of a plane with
hyperbolic pair `f, f'` scales `f` and `f'` by inverse scalars. -/
theorem exists_smul_of_isometry_det_one [FiniteDimensional K V] (hdim : Module.finrank K V = 2)
    {f f' : V} (hf : Q f = 0) (hf' : Q f' = 0) (hp : QuadraticMap.polar Q f f' = 1)
    (R : V →ₗ[K] V) (hR : ∀ v, Q (R v) = Q v) (hdet : LinearMap.det R = 1) :
    ∃ t : Kˣ, R f = ((t⁻¹ : Kˣ) : K) • f ∧ R f' = (t : K) • f' := by
  have hli := linearIndependent_hyp_pair hf hf' hp
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hb0 : b 0 = f := by simp [b]
  have hb1 : b 1 = f' := by simp [b]
  -- coordinates of `R f`, `R f'`
  set a := b.repr (R f) 0; set c := b.repr (R f) 1
  set a' := b.repr (R f') 0; set d := b.repr (R f') 1
  have hRf : R f = a • f + c • f' := by
    have := b.sum_repr (R f)
    rw [Fin.sum_univ_two, hb0, hb1] at this
    exact this.symm
  have hRf' : R f' = a' • f + d • f' := by
    have := b.sum_repr (R f')
    rw [Fin.sum_univ_two, hb0, hb1] at this
    exact this.symm
  have hff : QuadraticMap.polar Q f f = 0 := by rw [QuadraticMap.polar_self, hf, smul_zero]
  have hff' : QuadraticMap.polar Q f' f' = 0 := by rw [QuadraticMap.polar_self, hf', smul_zero]
  have hp' : QuadraticMap.polar Q f' f = 1 := by rw [QuadraticMap.polar_comm]; exact hp
  -- `Q(a f + c f') = a c`
  have hQ2 : ∀ x y : K, Q (x • f + y • f') = x * y := fun x y => by
    have h := QuadraticMap.polar Q (x • f) (y • f')
    have hpol : QuadraticMap.polar Q (x • f) (y • f') =
        Q (x • f + y • f') - Q (x • f) - Q (y • f') := rfl
    rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hp, QuadraticMap.map_smul,
      QuadraticMap.map_smul, hf, hf'] at hpol
    simp only [smul_eq_mul, mul_one, mul_zero, sub_zero] at hpol
    linear_combination -hpol
  have e1 : a * c = 0 := by rw [← hQ2, ← hRf, hR, hf]
  have e2 : a' * d = 0 := by rw [← hQ2, ← hRf', hR, hf']
  have e3 : a * d + c * a' = 1 := by
    have hpR : QuadraticMap.polar Q (R f) (R f') = QuadraticMap.polar Q f f' := by
      simp only [QuadraticMap.polar, ← map_add, hR]
    rw [hRf, hRf', hp] at hpR
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hff, hff', hp, hp',
      smul_eq_mul] at hpR
    linear_combination hpR
  have e4 : a * d - c * a' = 1 := by
    rw [← hdet, ← LinearMap.det_toMatrix b, Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply, hb0, hb1, a, c, a', d]
    ring
  have h2ne : (2 : K) ≠ 0 := Invertible.ne_zero 2
  have had : a * d = 1 := mul_left_cancel₀ h2ne (by linear_combination e3 + e4)
  have hc : c = 0 := by
    have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one had
    exact (mul_eq_zero.1 e1).resolve_left ha
  have ha' : a' = 0 := by
    have hd : d ≠ 0 := right_ne_zero_of_mul_eq_one had
    exact (mul_eq_zero.1 e2).resolve_right hd
  refine ⟨Units.mk0 d (right_ne_zero_of_mul_eq_one had), ?_, ?_⟩
  · rw [hRf, hc, zero_smul, add_zero, Units.val_inv_eq_inv_val, Units.val_mk0,
      eq_inv_of_mul_eq_one_left had]
  · rw [hRf', ha', zero_smul, zero_add, Units.val_mk0]

omit [Invertible (2 : K)] in
/-- On a plane with hyperbolic pair `f, f'`, a map scaling `f, f'` by `t⁻¹, t` is
`v ↦ v + (t⁻¹ − 1) polar(f', v) f + (t − 1) polar(f, v) f'`. -/
theorem apply_eq_of_smul_hyp_pair [FiniteDimensional K V] (hdim : Module.finrank K V = 2)
    {f f' : V} (hf : Q f = 0) (hf' : Q f' = 0) (hp : QuadraticMap.polar Q f f' = 1)
    (R : V →ₗ[K] V) {t : Kˣ} (hRf : R f = ((t⁻¹ : Kˣ) : K) • f) (hRf' : R f' = (t : K) • f')
    (v : V) : R v = v + (((t⁻¹ : Kˣ) : K) - 1) • (QuadraticMap.polar Q f' v • f) +
      ((t : K) - 1) • (QuadraticMap.polar Q f v • f') := by
  have hli := linearIndependent_hyp_pair hf hf' hp
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hb0 : b 0 = f := by simp [b]
  have hb1 : b 1 = f' := by simp [b]
  have hff : QuadraticMap.polar Q f f = 0 := by rw [QuadraticMap.polar_self, hf, smul_zero]
  have hff' : QuadraticMap.polar Q f' f' = 0 := by rw [QuadraticMap.polar_self, hf', smul_zero]
  have hp' : QuadraticMap.polar Q f' f = 1 := by rw [QuadraticMap.polar_comm]; exact hp
  let L : V →ₗ[K] V := LinearMap.id + (((t⁻¹ : Kˣ) : K) - 1) •
      ((QuadraticMap.polarBilin Q f').smulRight f) +
    ((t : K) - 1) • ((QuadraticMap.polarBilin Q f).smulRight f')
  have hL : R = L := b.ext fun i => by
    fin_cases i
    · simp [L, hb0, hRf, hff, hp']; module
    · simp [L, hb1, hRf', hff', hp]; module
  rw [hL]
  simp [L, smul_smul]

end HypPair

end GSpinGGP
