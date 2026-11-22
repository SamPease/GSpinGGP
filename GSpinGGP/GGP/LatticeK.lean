/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.WeightVM
import GSpinGGP.TraceFormula.WeakCartan
import GSpinGGP.Literature.GSpin

/-!
# Lattice stabilizers in `G = GSpin(W) × GSpin(V)`

For bases `e_W` of `W` and `e_V` of `V`, `GGPData.latticeK e_W e_V` is the subgroup of the
`g ∈ G` such that `P(g)` and `P(g)⁻¹` map the `𝒪_F`-lattices `Λ_e = {v : ‖e^*_i(v)‖ ≤ 1}` into
themselves and the characters `detChar` of both factors have norm `1` on `g`.  The second
condition cuts out the central scalars, which act trivially through `P`.

## Main results

* `mapsLattice_iff`: `A Λ_e ⊆ Λ_e` iff the matrix of `A` in `e` has entries in `𝒪_F`
  (ultrametric).
* `GGPData.isOpen_latticeK`, `GGPData.isCompact_latticeK`: `latticeK` is compact open.  Compact:
  its image in `SO(W) × SO(V)` is bounded, so it lies in `Z · C` for a compact `C` and the scalars
  `Z` (`exists_isCompact_lift`); the norm condition bounds the scalar part.
* `mapsLattice_quadReflection`, `norm_detChar_gspinPair`: for `u, w` in the lattice with
  `‖q(u)‖ = ‖q(w)‖ = 1` and `polar` integral on the lattice, `u w ∈ GSpin(V)` stabilizes the lattice
  and has `‖detChar‖ = 1` (`GGPData.inr_gspinPair_mem_latticeK`).
-/

noncomputable section

open Module

namespace GSpinGGP

/-! ## Lattices given by a basis -/

section MapsLattice

theorem le_one_mul_le_one {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  (mul_le_mul_of_nonneg_right ha hb0).trans (by rw [one_mul]; exact hb)

variable {F : Type*} [NontriviallyNormedField F] {V : Type*} [AddCommGroup V] [Module F V]
  {κ : Type*}

/-- **`A` maps the lattice `Λ_e = {v : ‖e^*_i(v)‖ ≤ 1 ∀ i}` into itself.** -/
def MapsLattice (e : Basis κ F V) (A : V →ₗ[F] V) : Prop :=
  ∀ v : V, (∀ i, ‖e.repr v i‖ ≤ 1) → ∀ i, ‖e.repr (A v) i‖ ≤ 1

theorem mapsLattice_id (e : Basis κ F V) : MapsLattice e LinearMap.id := fun _ hv => hv

theorem MapsLattice.comp {e : Basis κ F V} {A B : V →ₗ[F] V} (hA : MapsLattice e A)
    (hB : MapsLattice e B) : MapsLattice e (A ∘ₗ B) := fun v hv => hA _ (hB v hv)

theorem MapsLattice.mul {e : Basis κ F V} {A B : V →ₗ[F] V} (hA : MapsLattice e A)
    (hB : MapsLattice e B) : MapsLattice e (A * B) := hA.comp hB

/-- **The matrix criterion**: in an ultrametric field, `A Λ_e ⊆ Λ_e` iff every matrix entry
`e^*_i(A e_j)` has norm `≤ 1`. -/
theorem mapsLattice_iff [Fintype κ] [IsUltrametricDist F] (e : Basis κ F V) (A : V →ₗ[F] V) :
    MapsLattice e A ↔ ∀ i j, ‖e.repr (A (e j)) i‖ ≤ 1 := by
  classical
  refine ⟨fun h i j => h (e j) (fun k => ?_) i, fun h v hv i => ?_⟩
  · rw [e.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  · have hs : e.repr (A v) i = ∑ j, e.repr v j * e.repr (A (e j)) i := by
      conv_lhs => rw [← e.sum_repr v]
      simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [hs]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => by
      rw [norm_mul]; exact le_one_mul_le_one (hv j) (norm_nonneg _) (h i j)

/-- On a lattice preserved by `A`, the matrix of `A` has sup norm `≤ 1`. -/
theorem MapsLattice.basisOpNorm_le {n : ℕ} {e : Basis (Fin n) F V} {A : V →ₗ[F] V}
    (h : MapsLattice e A) : basisOpNorm e A ≤ 1 := by
  classical
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j =>
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [Basis.equivFun_apply]
  refine h (e j) (fun k => ?_) i
  rw [e.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

/-- **Reflections in unit vectors preserve integral lattices**: if `polar` is integral on `Λ_e`,
`u ∈ Λ_e` and `‖q(u)‖ = 1`, then `s_u Λ_e ⊆ Λ_e` (ultrametric). -/
theorem mapsLattice_quadReflection [IsUltrametricDist F] (e : Basis κ F V)
    (Q : QuadraticForm F V)
    (hpol : ∀ x y : V, (∀ i, ‖e.repr x i‖ ≤ 1) → (∀ i, ‖e.repr y i‖ ≤ 1) →
      ‖QuadraticMap.polar Q x y‖ ≤ 1)
    {u : V} (hu : ∀ i, ‖e.repr u i‖ ≤ 1) (hQu : ‖Q u‖ = 1) :
    MapsLattice e (quadReflection Q u) := by
  intro v hv i
  rw [quadReflection_apply, map_sub, map_smul, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
    Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
  refine (IsUltrametricDist.norm_sub_le_max _ _).trans (max_le (hv i) ?_)
  rw [norm_mul, norm_mul, norm_inv, hQu, inv_one, one_mul]
  exact le_one_mul_le_one (hpol u v hu hv) (norm_nonneg _) (hu i)

end MapsLattice

/-! ## The norm character on products of two vectors -/

section DetChar

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
  {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]

omit [PAdicField F] in
/-- `N(ι u)² = q(u)^{dim C(V)}`. -/
theorem norm_ι_sq (Q : QuadraticForm F V) (u : V) :
    Algebra.norm F (CliffordAlgebra.ι Q u) ^ 2 = Q u ^ finrank F (CliffordAlgebra Q) := by
  rw [sq, ← map_mul, CliffordAlgebra.ι_sq_scalar, Algebra.norm_algebraMap]

/-- **`‖N(u w)‖ = 1` for unit vectors**: `N(ι u)² = q(u)^{dim C(V)}`. -/
theorem norm_detChar_gspinPair (Q : QuadraticForm F V) {u w : V} (hu : Q u ≠ 0) (hw : Q w ≠ 0)
    (hu1 : ‖Q u‖ = 1) (hw1 : ‖Q w‖ = 1) :
    ‖((detChar Q (gspinPair Q hu hw) : Fˣ) : F)‖ = 1 := by
  have h1 : ∀ x : V, ‖Q x‖ = 1 → ‖Algebra.norm F (CliffordAlgebra.ι Q x)‖ = 1 := by
    intro x hx
    have h := congrArg norm (norm_ι_sq Q x)
    rw [norm_pow, norm_pow, hx, one_pow] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  rw [detChar_apply, coe_gspinPair, map_mul, norm_mul, h1 u hu1, h1 w hw1, one_mul]

end DetChar

/-! ## A split form of rank three: transitivity on isotropic lines -/

section Rank3

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
  {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]

omit [Module.Finite F V] in
/-- `P((u w)⁻¹) = s_w s_u`. -/
theorem specP_gspinPair_inv_apply
    (Q : QuadraticForm F V) {u w : V} (hu : Q u ≠ 0) (hw : Q w ≠ 0) (v : V) :
    specP Q (gspinPair Q hu hw)⁻¹ v = quadReflection Q w (quadReflection Q u v) := by
  have hinvol : ∀ x : V, Q x ≠ 0 → ∀ y, quadReflection Q x (quadReflection Q x y) = y := by
    intro x hx y
    simp only [quadReflection_apply, QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_self, smul_eq_mul, nsmul_eq_mul]
    have e : (Q x)⁻¹ * (QuadraticMap.polar Q x y - (Q x)⁻¹ * (QuadraticMap.polar Q x y *
        ((2 : ℕ) * Q x))) = -((Q x)⁻¹ * QuadraticMap.polar Q x y) := by
      field_simp; push_cast; ring
    rw [smul_smul, smul_smul, e, neg_smul, sub_neg_eq_add, sub_add_cancel]
  apply (specP Q (gspinPair Q hu hw)).injective
  rw [← specP_mul_apply, mul_inv_cancel, map_one]
  change v = (specP Q (gspinPair Q hu hw) : V →ₗ[F] V) _
  rw [specP_gspinPair, mul_apply_eq_comp, hinvol w hw, hinvol u hu]

/-- `P(k)^{±1}` preserve `Λ_e` and `‖detChar(k)‖ = 1`. -/
def IsLatticeSpin {κ : Type*} (Q : QuadraticForm F V) (e : Basis κ F V) (k : GSpin Q) : Prop :=
  MapsLattice e (specP Q k : V →ₗ[F] V) ∧ MapsLattice e (specP Q k⁻¹ : V →ₗ[F] V) ∧
    ‖((detChar Q k : Fˣ) : F)‖ = 1

omit [Module.Finite F V] in
theorem IsLatticeSpin.mul {κ : Type*} {Q : QuadraticForm F V} {e : Basis κ F V} {k k' : GSpin Q}
    (h : IsLatticeSpin Q e k) (h' : IsLatticeSpin Q e k') : IsLatticeSpin Q e (k * k') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [map_mul]; exact h.1.mul h'.1
  · rw [mul_inv_rev, map_mul]; exact h'.2.1.mul h.2.1
  · rw [map_mul, Units.val_mul, norm_mul, h.2.2, h'.2.2, one_mul]

omit [PAdicField F] [Module.Finite F V] in
/-- `s_u` fixes the vectors orthogonal to `u`. -/
theorem quadReflection_apply_of_polar_eq_zero (Q : QuadraticForm F V) {u x : V}
    (h : QuadraticMap.polar Q u x = 0) : quadReflection Q u x = x := by
  simp [quadReflection_apply, h]

omit [PAdicField F] [Module.Finite F V] in
/-- `q(x - y) = -polar(x, y)` for isotropic `x`, `y`. -/
theorem quadForm_sub_of_isotropic (Q : QuadraticForm F V) {x y : V} (hx : Q x = 0)
    (hy : Q y = 0) : Q (x - y) = -QuadraticMap.polar Q x y := by
  have h : QuadraticMap.polar Q x (-y) = -QuadraticMap.polar Q x y :=
    QuadraticMap.polar_neg_right Q x y
  rw [QuadraticMap.polar, QuadraticMap.map_neg, ← sub_eq_add_neg, hx, hy] at h
  linear_combination h

omit [PAdicField F] [Module.Finite F V] in
/-- **The reflection in `x - y` swaps isotropic `x` and `y`** when `polar(x, y) ≠ 0`. -/
theorem quadReflection_sub_apply_self (Q : QuadraticForm F V) {x y : V} (hx : Q x = 0)
    (hy : Q y = 0) (hxy : QuadraticMap.polar Q x y ≠ 0) : quadReflection Q (x - y) x = y := by
  have hp : QuadraticMap.polar Q (x - y) x = -QuadraticMap.polar Q x y := by
    rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_self, hx, QuadraticMap.polar_comm Q y x]
    simp
  rw [quadReflection_apply, hp, quadForm_sub_of_isotropic Q hx hy, smul_smul,
    inv_mul_cancel₀ (neg_ne_zero.2 hxy), one_smul, sub_sub_cancel]

variable (Q : QuadraticForm F V) (e : Basis (Fin 3) F V)
  (hQ : ∀ v, Q v = e.repr v 0 * e.repr v 2 + e.repr v 1 ^ 2)

include hQ

omit [PAdicField F] [Module.Finite F V] in
theorem polar_eq_of_rank3 (x y : V) : QuadraticMap.polar Q x y =
    e.repr x 0 * e.repr y 2 + e.repr y 0 * e.repr x 2 + 2 * (e.repr x 1 * e.repr y 1) := by
  simp only [QuadraticMap.polar, hQ, map_add, Finsupp.add_apply]; ring

omit [Module.Finite F V] in
/-- `polar` is integral on `Λ_e`. -/
theorem norm_polar_le_one_of_rank3 (x y : V) (hx : ∀ i, ‖e.repr x i‖ ≤ 1)
    (hy : ∀ i, ‖e.repr y i‖ ≤ 1) : ‖QuadraticMap.polar Q x y‖ ≤ 1 := by
  rw [polar_eq_of_rank3 Q e hQ]
  have h2 : ‖(2 : F)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one F 2
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)) ?_)
  · rw [norm_mul]; exact le_one_mul_le_one (hx 0) (norm_nonneg _) (hy 2)
  · rw [norm_mul]; exact le_one_mul_le_one (hy 0) (norm_nonneg _) (hx 2)
  · rw [norm_mul, norm_mul]
    exact le_one_mul_le_one h2 (by positivity)
      (le_one_mul_le_one (hx 1) (norm_nonneg _) (hy 1))

omit [PAdicField F] [Module.Finite F V] in
theorem quadForm_basis_one : Q (e 1) = 1 := by
  simp [hQ]

/-- **A swap in `latticeK`-form**: for isotropic `x, y ∈ Λ_e` with `‖polar(x, y)‖ = 1` and
`x ⊥ e₁`, the pair element `(x - y) e₁` maps `x` to `y`. -/
theorem exists_isLatticeSpin_swap {x y : V} (hx : Q x = 0) (hy : Q y = 0)
    (hxl : ∀ i, ‖e.repr x i‖ ≤ 1) (hyl : ∀ i, ‖e.repr y i‖ ≤ 1)
    (hxy : ‖QuadraticMap.polar Q x y‖ = 1) (hx1 : e.repr x 1 = 0) :
    ∃ k : GSpin Q, IsLatticeSpin Q e k ∧ specP Q k x = y := by
  have hpne : QuadraticMap.polar Q x y ≠ 0 := by
    intro h; rw [h, norm_zero] at hxy; exact zero_ne_one hxy
  have hu : Q (x - y) ≠ 0 := by
    rw [quadForm_sub_of_isotropic Q hx hy]; exact neg_ne_zero.2 hpne
  have hu1 : ‖Q (x - y)‖ = 1 := by rw [quadForm_sub_of_isotropic Q hx hy, norm_neg, hxy]
  have he1 : Q (e 1) = 1 := quadForm_basis_one Q e hQ
  have hw : Q (e 1) ≠ 0 := by rw [he1]; exact one_ne_zero
  have hw1 : ‖Q (e 1)‖ = 1 := by rw [he1, norm_one]
  have hpol := norm_polar_le_one_of_rank3 Q e hQ
  have hul : ∀ i, ‖e.repr (x - y) i‖ ≤ 1 := fun i => by
    rw [map_sub, Finsupp.sub_apply]
    exact (IsUltrametricDist.norm_sub_le_max _ _).trans (max_le (hxl i) (hyl i))
  have hwl : ∀ i, ‖e.repr (e 1) i‖ ≤ 1 := fun i => by
    rw [e.repr_self, Finsupp.single_apply]; split_ifs <;> simp
  have su := mapsLattice_quadReflection e Q hpol hul hu1
  have sw := mapsLattice_quadReflection e Q hpol hwl hw1
  refine ⟨gspinPair Q hu hw, ⟨?_, ?_, norm_detChar_gspinPair Q hu hw hu1 hw1⟩, ?_⟩
  · rw [specP_gspinPair]; exact su.mul sw
  · intro v hv i
    rw [LinearEquiv.coe_coe, specP_gspinPair_inv_apply]
    exact sw _ (su v hv) i
  · change (specP Q (gspinPair Q hu hw) : V →ₗ[F] V) x = y
    rw [specP_gspinPair, mul_apply_eq_comp]
    rw [quadReflection_apply_of_polar_eq_zero Q (u := e 1) (x := x) (by
      rw [polar_eq_of_rank3 Q e hQ, hx1]; simp)]
    exact quadReflection_sub_apply_self Q hx hy hpne

/-- **`GSpin` of the split rank-three form `ac + b²` is transitive on isotropic lines through
`Λ_e`-integral elements of unit norm**: for every isotropic `v ≠ 0` some `k` with
`P(k)^{±1} Λ_e ⊆ Λ_e` and `‖detChar(k)‖ = 1` maps `e₂` into `F^× v`.  Divide `v` by its larger
end coordinate (the middle one is then integral too, `b² = -ac`), and compose at most two swaps
(`exists_isLatticeSpin_swap`). -/
theorem exists_isLatticeSpin_apply_eq_smul {v : V} (hv : v ≠ 0) (hQv : Q v = 0) :
    ∃ k : GSpin Q, IsLatticeSpin Q e k ∧ ∃ t : F, t ≠ 0 ∧ specP Q k (e 2) = t • v := by
  set a := e.repr v 0
  set b := e.repr v 1
  set c := e.repr v 2
  have hab : a * c + b ^ 2 = 0 := by rw [← hQv, hQ]
  have hbsq : ‖b‖ ^ 2 = ‖a‖ * ‖c‖ := by
    rw [← norm_pow, ← norm_mul, show b ^ 2 = -(a * c) by linear_combination hab, norm_neg]
  have hrepr : ∀ (s : F) (i : Fin 3), e.repr (s • v) i = s * e.repr v i := fun s i => by simp
  have hQs : ∀ s : F, Q (s • v) = 0 := fun s => by rw [QuadraticMap.map_smul, hQv, smul_zero]
  have hself : ∀ i : Fin 3, ∀ j, ‖e.repr (e i) j‖ ≤ 1 := fun i j => by
    rw [e.repr_self, Finsupp.single_apply]; split_ifs <;> simp
  have hQe : ∀ i : Fin 3, i ≠ 1 → Q (e i) = 0 := fun i hi => by
    rw [hQ]; fin_cases i <;> simp_all [Finsupp.single_apply]
  have hv0 : ¬ (a = 0 ∧ c = 0) := by
    rintro ⟨ha, hc⟩
    have hb : b = 0 := by
      have : b ^ 2 = 0 := by rw [← hab, ha, zero_mul, zero_add]
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    apply hv
    refine e.repr.injective (Finsupp.ext fun i => ?_)
    fin_cases i <;> simp [ha, hb, hc, a, b, c]
  rcases le_or_gt ‖c‖ ‖a‖ with hca | hac
  · -- `a` is the larger end coordinate: one swap `e₂ ↦ a⁻¹ v`
    have ha : a ≠ 0 := fun ha => hv0 ⟨ha, norm_le_zero_iff.1 (by rw [ha, norm_zero] at hca; exact hca)⟩
    have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
    have hb : ‖b‖ ≤ ‖a‖ := by
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
      rw [hbsq, sq]; exact mul_le_mul_of_nonneg_left hca (norm_nonneg _)
    have hyl : ∀ i, ‖e.repr (a⁻¹ • v) i‖ ≤ 1 := fun i => by
      rw [hrepr, norm_mul, norm_inv, inv_mul_le_one₀ hna]
      fin_cases i
      · exact le_rfl
      · exact hb
      · exact hca
    obtain ⟨k, hk, hke⟩ := exists_isLatticeSpin_swap Q e hQ (hQe 2 (by decide)) (hQs a⁻¹)
      (hself 2) hyl (by rw [polar_eq_of_rank3 Q e hQ]; simp [ha, a])
      (by simp)
    exact ⟨k, hk, a⁻¹, inv_ne_zero ha, hke⟩
  · -- `c` is the larger end coordinate: `e₂ ↦ e₀ ↦ c⁻¹ v`
    have hnc : 0 < ‖c‖ := (norm_nonneg a).trans_lt hac
    have hc : c ≠ 0 := norm_pos_iff.1 hnc
    have hb : ‖b‖ ≤ ‖c‖ := by
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
      rw [hbsq, sq]; exact mul_le_mul_of_nonneg_right hac.le (norm_nonneg _)
    have hyl : ∀ i, ‖e.repr (c⁻¹ • v) i‖ ≤ 1 := fun i => by
      rw [hrepr, norm_mul, norm_inv, inv_mul_le_one₀ hnc]
      fin_cases i
      · exact hac.le
      · exact hb
      · exact le_rfl
    obtain ⟨k₁, hk₁, hke₁⟩ := exists_isLatticeSpin_swap Q e hQ (hQe 0 (by decide)) (hQs c⁻¹)
      (hself 0) hyl (by rw [polar_eq_of_rank3 Q e hQ]; simp [hc, c])
      (by simp)
    obtain ⟨k₀, hk₀, hke₀⟩ := exists_isLatticeSpin_swap Q e hQ (hQe 2 (by decide))
      (hQe 0 (by decide)) (hself 2) (hself 0)
      (by rw [polar_eq_of_rank3 Q e hQ]; simp)
      (by simp)
    refine ⟨k₁ * k₀, hk₁.mul hk₀, c⁻¹, inv_ne_zero hc, ?_⟩
    rw [specP_mul_apply, hke₀, hke₁]

end Rank3

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)
  {nW nV : ℕ} (eW : Basis (Fin nW) F (Fin d.m → F)) (eV : Basis (Fin nV) F d.V)

/-! ## The subgroup `latticeK` -/

/-- One half of the membership condition of `latticeK`: `P(g)` maps the lattices into themselves
and `‖detChar‖ = 1` on both factors. -/
def IsLatticeUnit (g : ↥d.G) : Prop :=
  MapsLattice eW (specP d.QW (d.fst g) : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) ∧
    MapsLattice eV (specP d.QV (d.snd g) : d.V →ₗ[F] d.V) ∧
    ‖((detChar d.QW (d.fst g) : Fˣ) : F)‖ = 1 ∧ ‖((detChar d.QV (d.snd g) : Fˣ) : F)‖ = 1

theorem isLatticeUnit_one : d.IsLatticeUnit eW eV 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [map_one, map_one]; exact mapsLattice_id eW
  · rw [map_one, map_one]; exact mapsLattice_id eV
  · simp
  · simp

theorem IsLatticeUnit.mul {g h : ↥d.G} (hg : d.IsLatticeUnit eW eV g)
    (hh : d.IsLatticeUnit eW eV h) : d.IsLatticeUnit eW eV (g * h) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [map_mul, map_mul]; exact hg.1.mul hh.1
  · rw [map_mul, map_mul]; exact hg.2.1.mul hh.2.1
  · rw [map_mul, map_mul, Units.val_mul, norm_mul, hg.2.2.1, hh.2.2.1, one_mul]
  · rw [map_mul, map_mul, Units.val_mul, norm_mul, hg.2.2.2, hh.2.2.2, one_mul]

/-- **The lattice stabilizer** `K(e_W, e_V)`: the `g ∈ G` such that `P(g)^{±1}` map `Λ_{e_W}`,
`Λ_{e_V}` into themselves and `‖detChar(g)‖ = 1` on both factors. -/
def latticeK : Subgroup ↥d.G where
  carrier := {g | d.IsLatticeUnit eW eV g ∧ d.IsLatticeUnit eW eV g⁻¹}
  one_mem' := ⟨d.isLatticeUnit_one eW eV, by rw [inv_one]; exact d.isLatticeUnit_one eW eV⟩
  mul_mem' := fun {g h} hg hh => ⟨hg.1.mul _ _ _ hh.1, by
    rw [mul_inv_rev]; exact hh.2.mul _ _ _ hg.2⟩
  inv_mem' := fun {g} hg => ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

variable {d eW eV} in
theorem mem_latticeK {g : ↥d.G} :
    g ∈ d.latticeK eW eV ↔ d.IsLatticeUnit eW eV g ∧ d.IsLatticeUnit eW eV g⁻¹ := Iff.rfl

/-- `{g | IsLatticeUnit g}` is clopen: matrix entries and `detChar` are continuous, and closed
balls and spheres are clopen in an ultrametric field. -/
theorem isClopen_setOf_isLatticeUnit : IsClopen {g : ↥d.G | d.IsLatticeUnit eW eV g} := by
  classical
  have hball : IsClopen (Metric.closedBall (0 : F) 1) :=
    IsUltrametricDist.isClopen_closedBall 0 one_ne_zero
  have hsph : IsClopen (Metric.sphere (0 : F) 1) :=
    IsUltrametricDist.isClopen_sphere 0 one_ne_zero
  have hW : ∀ i j, Continuous fun g : ↥d.G => eW.repr (specP d.QW (d.fst g) (eW j)) i := by
    intro i j
    exact ((eW.coord i).continuous_of_finiteDimensional).comp
      (continuous_specP_apply d.continuous_fst (eW j))
  have hV : ∀ i j, Continuous fun g : ↥d.G => eV.repr (specP d.QV (d.snd g) (eV j)) i := by
    intro i j
    exact ((eV.coord i).continuous_of_finiteDimensional).comp
      (continuous_specP_apply d.continuous_snd (eV j))
  have e : {g : ↥d.G | d.IsLatticeUnit eW eV g} =
      (⋂ i, ⋂ j, (fun g : ↥d.G => eW.repr (specP d.QW (d.fst g) (eW j)) i) ⁻¹'
        Metric.closedBall 0 1) ∩
      ((⋂ i, ⋂ j, (fun g : ↥d.G => eV.repr (specP d.QV (d.snd g) (eV j)) i) ⁻¹'
        Metric.closedBall 0 1) ∩
      ((fun g : ↥d.G => ((detChar d.QW (d.fst g) : Fˣ) : F)) ⁻¹' Metric.sphere 0 1 ∩
       (fun g : ↥d.G => ((detChar d.QV (d.snd g) : Fˣ) : F)) ⁻¹' Metric.sphere 0 1)) := by
    ext g
    simp only [IsLatticeUnit, mapsLattice_iff, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_preimage, Metric.mem_closedBall, Metric.mem_sphere, dist_zero_right]
    rfl
  rw [e]
  refine (isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j =>
    hball.preimage (hW i j)).inter ((isClopen_iInter_of_finite fun i =>
      isClopen_iInter_of_finite fun j => hball.preimage (hV i j)).inter
      ((hsph.preimage ((continuous_detChar d.QW).comp d.continuous_fst)).inter
        (hsph.preimage ((continuous_detChar d.QV).comp d.continuous_snd))))

theorem isClopen_latticeK : IsClopen (d.latticeK eW eV : Set ↥d.G) :=
  (d.isClopen_setOf_isLatticeUnit eW eV).inter
    ((d.isClopen_setOf_isLatticeUnit eW eV).preimage continuous_inv)

/-- **`latticeK` is open.** -/
theorem isOpen_latticeK : IsOpen (d.latticeK eW eV : Set ↥d.G) := (d.isClopen_latticeK eW eV).2

/-- On `latticeK` the log-norm of `P̄(g)` is bounded. -/
theorem exists_logNormSO_le_of_mem_latticeK :
    ∃ M, ∀ g ∈ d.latticeK eW eV, d.logNormSO (d.Pbar g) ≤ M := by
  obtain ⟨CW, hCW, hW⟩ := exists_norm_toContinuousLinearMap_le_basisOpNorm eW
  obtain ⟨CV, hCV, hV⟩ := exists_norm_toContinuousLinearMap_le_basisOpNorm eV
  refine ⟨1 + Real.log (max (max 1 CW) (max 1 CV)), fun g hg => ?_⟩
  have hgW : glMaxNorm (specP d.QW (d.fst g)) ≤ max 1 CW := by
    refine max_le (le_max_left _ _) (max_le ?_ ?_)
    · exact (hW _).trans ((mul_le_of_le_one_right hCW hg.1.1.basisOpNorm_le).trans
        (le_max_right _ _))
    · have h2 := hg.2.1
      rw [map_inv, map_inv] at h2
      exact (hW _).trans ((mul_le_of_le_one_right hCW h2.basisOpNorm_le).trans
        (le_max_right _ _))
  have hgV : glMaxNorm (specP d.QV (d.snd g)) ≤ max 1 CV := by
    refine max_le (le_max_left _ _) (max_le ?_ ?_)
    · exact (hV _).trans ((mul_le_of_le_one_right hCV hg.1.2.1.basisOpNorm_le).trans
        (le_max_right _ _))
    · have h2 := hg.2.2.1
      rw [map_inv, map_inv] at h2
      exact (hV _).trans ((mul_le_of_le_one_right hCV h2.basisOpNorm_le).trans
        (le_max_right _ _))
  unfold logNormSO
  rw [Pbar_fst, Pbar_snd]
  have h1 := d.one_le_max_glMaxNorm (d.Pbar g)
  rw [Pbar_fst, Pbar_snd] at h1
  linarith [Real.log_le_log (by linarith) (max_le_max hgW hgV)]

/-- A set of units `{c : ‖c‖^N ≤ B, 1 ≤ B' ‖c‖^N}` (`N ≥ 1`) is compact. -/
theorem isCompact_units_norm_pow {N : ℕ} (hN : 1 ≤ N) (B B' : ℝ) :
    IsCompact {c : Fˣ | ‖(c : F)‖ ^ N ≤ B ∧ 1 ≤ B' * ‖(c : F)‖ ^ N} := by
  have := properSpace_F (F := F)
  set A : Set F := {x | ‖x‖ ^ N ≤ B ∧ 1 ≤ B' * ‖x‖ ^ N}
  have hA : IsCompact A := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le (continuous_norm.pow N) continuous_const).inter
        (isClosed_le continuous_const (continuous_const.mul (continuous_norm.pow N)))
    · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨max 1 B, fun x hx => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      by_cases h1 : ‖x‖ ≤ 1
      · exact h1.trans (le_max_left _ _)
      · push Not at h1
        exact ((le_self_pow₀ h1.le (by omega)).trans hx.1).trans (le_max_right _ _)
  have hsub : A ⊆ Set.range (Units.val : Fˣ → F) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      have := hx.2
      rw [norm_zero, zero_pow (by omega), mul_zero] at this
      linarith
    exact ⟨Units.mk0 x hx0, rfl⟩
  exact (Units.isEmbedding_val₀.isInducing.isCompact_preimage_iff hsub).2 hA

omit [PAdicField F] in
theorem continuous_scalarGSpin {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (Q : QuadraticForm F V) : Continuous (scalarGSpin Q) := by
  refine continuous_induced_rng.2 ?_
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous fun c : Fˣ => algebraMap F (CliffordAlgebra Q) (c : F)
    exact (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F (CliffordAlgebra Q))).comp
      Units.continuous_val
  · change Continuous fun c : Fˣ => algebraMap F (CliffordAlgebra Q) ((c⁻¹ : Fˣ) : F)
    exact (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F (CliffordAlgebra Q))).comp
      Units.continuous_coe_inv

theorem continuous_scalarPair :
    Continuous fun c : Fˣ × Fˣ => d.scalarPair c.1 c.2 :=
  d.continuous_pair.comp (((continuous_scalarGSpin d.QW).comp _root_.continuous_fst).prodMk
    ((continuous_scalarGSpin d.QV).comp _root_.continuous_snd))

/-- **`latticeK` is compact.**  Its image in `SO(W) × SO(V)` is bounded
(`exists_logNormSO_le_of_mem_latticeK`), so `z g` lies in a compact `C` for some central scalar
`z = (c₁, c₂)` (`exists_isCompact_lift`); `‖detChar(z g)‖ = ‖c_i‖^{N_i}` is bounded above and below
on `C`, which confines `(c₁, c₂)` to a compact set. -/
theorem isCompact_latticeK : IsCompact (d.latticeK eW eV : Set ↥d.G) := by
  obtain ⟨M, hM⟩ := d.exists_logNormSO_le_of_mem_latticeK eW eV
  obtain ⟨C, hC, hlift⟩ := d.exists_isCompact_lift M
  set NW := finrank F (CliffordAlgebra d.QW)
  set NV := finrank F (CliffordAlgebra d.QV)
  have hNW : 1 ≤ NW := Module.finrank_pos
  have hNV : 1 ≤ NV := Module.finrank_pos
  have cW : Continuous fun x : ↥d.G => ‖((detChar d.QW (d.fst x) : Fˣ) : F)‖ :=
    ((continuous_detChar d.QW).comp d.continuous_fst).norm
  have cV : Continuous fun x : ↥d.G => ‖((detChar d.QV (d.snd x) : Fˣ) : F)‖ :=
    ((continuous_detChar d.QV).comp d.continuous_snd).norm
  obtain ⟨BW, hBW⟩ := hC.bddAbove_image cW.continuousOn
  obtain ⟨BV, hBV⟩ := hC.bddAbove_image cV.continuousOn
  obtain ⟨BW', hBW'⟩ := hC.bddAbove_image (cW.comp continuous_inv).continuousOn
  obtain ⟨BV', hBV'⟩ := hC.bddAbove_image (cV.comp continuous_inv).continuousOn
  set T := {c : Fˣ | ‖(c : F)‖ ^ NW ≤ BW ∧ 1 ≤ BW' * ‖(c : F)‖ ^ NW} ×ˢ
    {c : Fˣ | ‖(c : F)‖ ^ NV ≤ BV ∧ 1 ≤ BV' * ‖(c : F)‖ ^ NV}
  have hT : IsCompact T := (isCompact_units_norm_pow hNW _ _).prod (isCompact_units_norm_pow hNV _ _)
  have hS : IsCompact ((fun p : (Fˣ × Fˣ) × ↥d.G => (d.scalarPair p.1.1 p.1.2)⁻¹ * p.2) ''
      (T ×ˢ C)) :=
    (hT.prod hC).image (((d.continuous_scalarPair.comp _root_.continuous_fst).inv).mul _root_.continuous_snd)
  refine hS.of_isClosed_subset (d.isClopen_latticeK eW eV).1 fun g hg => ?_
  obtain ⟨z, ⟨c, rfl⟩, hzg⟩ := hlift g (hM g hg)
  have hzc : (d.pair.comp ((scalarGSpin d.QW).prodMap (scalarGSpin d.QV))) c =
      d.scalarPair c.1 c.2 := rfl
  rw [hzc] at hzg
  have dW : ‖((detChar d.QW (d.fst (d.scalarPair c.1 c.2 * g)) : Fˣ) : F)‖ =
      ‖(c.1 : F)‖ ^ NW := by
    rw [map_mul, map_mul, Units.val_mul, norm_mul, hg.1.2.2.1, mul_one]
    simp [scalarPair, fst_pair, detChar_scalarGSpin, NW]
  have dV : ‖((detChar d.QV (d.snd (d.scalarPair c.1 c.2 * g)) : Fˣ) : F)‖ =
      ‖(c.2 : F)‖ ^ NV := by
    rw [map_mul, map_mul, Units.val_mul, norm_mul, hg.1.2.2.2, mul_one]
    simp [scalarPair, snd_pair, detChar_scalarGSpin, NV]
  have inv1 : ∀ x : ↥d.G, ‖((detChar d.QW (d.fst x⁻¹) : Fˣ) : F)‖ *
      ‖((detChar d.QW (d.fst x) : Fˣ) : F)‖ = 1 := fun x => by
    rw [← norm_mul, ← Units.val_mul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
    simp
  have inv2 : ∀ x : ↥d.G, ‖((detChar d.QV (d.snd x⁻¹) : Fˣ) : F)‖ *
      ‖((detChar d.QV (d.snd x) : Fˣ) : F)‖ = 1 := fun x => by
    rw [← norm_mul, ← Units.val_mul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
    simp
  have hW1 := hBW ⟨_, hzg, rfl⟩
  have hW2 := hBW' ⟨_, hzg, rfl⟩
  have hV1 := hBV ⟨_, hzg, rfl⟩
  have hV2 := hBV' ⟨_, hzg, rfl⟩
  simp only [Function.comp_apply] at hW1 hW2 hV1 hV2
  have i1 := inv1 (d.scalarPair c.1 c.2 * g)
  have i2 := inv2 (d.scalarPair c.1 c.2 * g)
  rw [dW] at hW1 i1
  rw [dV] at hV1 i2
  refine ⟨(c, _), ⟨⟨⟨hW1, ?_⟩, ⟨hV1, ?_⟩⟩, hzg⟩, ?_⟩
  · calc (1 : ℝ) = _ := i1.symm
      _ ≤ BW' * ‖(c.1 : F)‖ ^ NW := mul_le_mul_of_nonneg_right hW2 (by positivity)
  · calc (1 : ℝ) = _ := i2.symm
      _ ≤ BV' * ‖(c.2 : F)‖ ^ NV := mul_le_mul_of_nonneg_right hV2 (by positivity)
  · simp only
    rw [← mul_assoc, inv_mul_cancel, one_mul]

/-! ## Elements of `latticeK` -/

/-- `fst (inr y) = 1`. -/
theorem fst_inr' (y : GSpin d.QV) : d.fst (d.inr y) = 1 := rfl

/-- **`(1, y) ∈ latticeK`** as soon as `P(y)^{±1}` preserve `Λ_{e_V}` and `‖detChar(y)‖ = 1`. -/
theorem inr_mem_latticeK {y : GSpin d.QV}
    (h1 : MapsLattice eV (specP d.QV y : d.V →ₗ[F] d.V))
    (h2 : MapsLattice eV (specP d.QV y⁻¹ : d.V →ₗ[F] d.V))
    (h3 : ‖((detChar d.QV y : Fˣ) : F)‖ = 1) : d.inr y ∈ d.latticeK eW eV := by
  have hinv : ‖((detChar d.QV y⁻¹ : Fˣ) : F)‖ = 1 := by
    rw [map_inv, Units.val_inv_eq_inv_val, norm_inv, h3, inv_one]
  refine ⟨⟨?_, h1, ?_, h3⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [fst_inr', map_one]; exact mapsLattice_id eW
  · rw [fst_inr']; simp
  · rw [map_inv, fst_inr', inv_one, map_one]; exact mapsLattice_id eW
  · rw [map_inv, snd_inr]; exact h2
  · rw [map_inv, fst_inr', inv_one]; simp
  · rw [map_inv, snd_inr]; exact hinv

/-- **Pairs of unit vectors give elements of `latticeK`**: for `u, w ∈ Λ_{e_V}` with
`‖q(u)‖ = ‖q(w)‖ = 1`, and `polar` integral on `Λ_{e_V}`, `(1, u w) ∈ latticeK`. -/
theorem inr_gspinPair_mem_latticeK
    (hpol : ∀ x y : d.V, (∀ i, ‖eV.repr x i‖ ≤ 1) → (∀ i, ‖eV.repr y i‖ ≤ 1) →
      ‖QuadraticMap.polar d.QV x y‖ ≤ 1)
    {u w : d.V} (hu : d.QV u ≠ 0) (hw : d.QV w ≠ 0) (hul : ∀ i, ‖eV.repr u i‖ ≤ 1)
    (hwl : ∀ i, ‖eV.repr w i‖ ≤ 1) (hu1 : ‖d.QV u‖ = 1) (hw1 : ‖d.QV w‖ = 1) :
    d.inr (gspinPair d.QV hu hw) ∈ d.latticeK eW eV := by
  have su := mapsLattice_quadReflection eV d.QV hpol hul hu1
  have sw := mapsLattice_quadReflection eV d.QV hpol hwl hw1
  refine d.inr_mem_latticeK eW eV ?_ ?_ (norm_detChar_gspinPair _ hu hw hu1 hw1)
  · rw [specP_gspinPair]; exact su.mul sw
  · intro v hv i
    rw [LinearEquiv.coe_coe, specP_gspinPair_inv_apply]
    exact sw _ (su v hv) i

end GGPData

end GSpinGGP
