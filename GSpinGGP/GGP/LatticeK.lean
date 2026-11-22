/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.WeightVM
import GSpinGGP.TraceFormula.WeakCartan
import GSpinGGP.Literature.GSpin

/-!
# Lattice stabilizers in `G = GSpin(W) × GSpin(V)`

For a basis `e` of `V`, `latticeSpin Q e ⊆ GSpin(V)` is the subgroup of the `k` such that `P(k)`
and `P(k)⁻¹` map the `𝒪_F`-lattice `Λ_e = {v : ‖e^*_i(v)‖ ≤ 1}` into itself (`MapsLattice`) and
`‖detChar(k)‖ = 1`.  On a central scalar `c` the character `detChar` is `c^{dim C(V)}`, so the
second condition leaves exactly the scalars in `𝒪_F^×`: without it the group would contain all
of `F^×` and would not be compact.  `GGPData.latticeK e_W e_V` is `latticeSpin` on both factors.

## Main results

* `mapsLattice_iff`: `A Λ_e ⊆ Λ_e` iff the matrix of `A` in `e` has entries in `𝒪_F`
  (ultrametric).
* `isClopen_latticeSpin`; `GGPData.isOpen_latticeK`, `GGPData.isCompact_latticeK`: `latticeK` is
  compact open.  Compact: its image in `SO(W) × SO(V)` is bounded, so it lies in `Z · C` for a
  compact `C` and the scalars `Z` (`exists_isCompact_lift`); the norm condition bounds the scalar
  part.
* `gspinPair_mem_latticeSpin`: for `u, w ∈ Λ_e` with `‖q(u)‖ = ‖q(w)‖ = 1` and `polar` integral on
  `Λ_e`, `u w ∈ latticeSpin Q e`.
* `exists_mem_latticeSpin_apply_eq_smul`: for the split rank-three form `ac + b²`, `latticeSpin`
  is transitive on the isotropic lines of `V`.
-/

noncomputable section

open Module

namespace GSpinGGP

/-! ## Lattices given by a basis -/

section MapsLattice

private theorem le_one_mul_le_one {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) :
    a * b ≤ 1 :=
  (mul_le_mul_of_nonneg_right ha hb0).trans (by rw [one_mul]; exact hb)

variable {F : Type*} [NontriviallyNormedField F] {V : Type*} [AddCommGroup V] [Module F V]
  {κ : Type*}

/-- The basis vectors lie in `Λ_e`. -/
theorem norm_repr_basis_le_one (e : Basis κ F V) (j i : κ) : ‖e.repr (e j) i‖ ≤ 1 := by
  classical
  rw [e.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

theorem mapsLattice_id (e : Basis κ F V) : MapsLattice e LinearMap.id := fun _ hv => hv

theorem MapsLattice.comp {e : Basis κ F V} {A B : V →ₗ[F] V} (hA : MapsLattice e A)
    (hB : MapsLattice e B) : MapsLattice e (A ∘ₗ B) := fun v hv => hA _ (hB v hv)

theorem MapsLattice.mul {e : Basis κ F V} {A B : V →ₗ[F] V} (hA : MapsLattice e A)
    (hB : MapsLattice e B) : MapsLattice e (A * B) := hA.comp hB

/-- **The matrix criterion**: in an ultrametric field, `A Λ_e ⊆ Λ_e` iff every matrix entry
`e^*_i(A e_j)` has norm `≤ 1`. -/
theorem mapsLattice_iff [Finite κ] [IsUltrametricDist F] (e : Basis κ F V) (A : V →ₗ[F] V) :
    MapsLattice e A ↔ ∀ i j, ‖e.repr (A (e j)) i‖ ≤ 1 := by
  classical
  have := Fintype.ofFinite κ
  refine ⟨fun h i j => h (e j) (norm_repr_basis_le_one e j) i, fun h v hv i => ?_⟩
  have hs : e.repr (A v) i = ∑ j, e.repr v j * e.repr (A (e j)) i := by
    conv_lhs => rw [← e.sum_repr v]
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [hs]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => by
    rw [norm_mul]; exact le_one_mul_le_one (hv j) (norm_nonneg _) (h i j)

/-- On a lattice preserved by `A`, the matrix of `A` has sup norm `≤ 1`. -/
theorem MapsLattice.basisOpNorm_le {n : ℕ} {e : Basis (Fin n) F V} {A : V →ₗ[F] V}
    (h : MapsLattice e A) : basisOpNorm e A ≤ 1 :=
  (basisOpNorm_le_iff zero_le_one).2 fun j =>
    (basisNorm_le_iff zero_le_one).2 (h (e j) (norm_repr_basis_le_one e j))

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

/-! ## The subgroup `latticeSpin` -/

section LatticeSpin

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
  {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] {κ : Type*}

/-- **The stabilizer of `Λ_e` in `GSpin(V)` with `‖detChar‖ = 1`**: the `k` such that `P(k)^{±1}`
map `Λ_e` into itself and `‖detChar(k)‖ = 1`. -/
def latticeSpin (Q : QuadraticForm F V) (e : Basis κ F V) : Subgroup (GSpin Q) where
  carrier := {k | MapsLattice e (specP Q k : V →ₗ[F] V) ∧
    MapsLattice e (specP Q k⁻¹ : V →ₗ[F] V) ∧ ‖((detChar Q k : Fˣ) : F)‖ = 1}
  one_mem' := ⟨by rw [map_one]; exact mapsLattice_id e,
    by rw [inv_one, map_one]; exact mapsLattice_id e, by simp⟩
  mul_mem' := fun {k k'} h h' => ⟨by rw [map_mul]; exact h.1.mul h'.1,
    by rw [mul_inv_rev, map_mul]; exact h'.2.1.mul h.2.1,
    by rw [map_mul, Units.val_mul, norm_mul, h.2.2, h'.2.2, one_mul]⟩
  inv_mem' := fun {k} h => ⟨h.2.1, by rw [inv_inv]; exact h.1,
    by rw [map_inv, Units.val_inv_eq_inv_val, norm_inv, h.2.2, inv_one]⟩

omit [Module.Finite F V] in
/-- **`latticeSpin` preserves the coordinate norm of `Λ_e`**: `‖P(k) v‖_e = ‖v‖_e` (`P(k)` and
`P(k)⁻¹` have matrices with entries in `𝒪_F`). -/
theorem basisNorm_specP_of_mem_latticeSpin {n : ℕ} {Q : QuadraticForm F V} {e : Basis (Fin n) F V}
    {k : GSpin Q} (hk : k ∈ latticeSpin Q e) (v : V) :
    basisNorm e (specP Q k v) = basisNorm e v := by
  have key : ∀ z ∈ latticeSpin Q e, ∀ w, basisNorm e (specP Q z w) ≤ basisNorm e w :=
    fun z hz w => (basisNorm_apply_le (specP Q z : V →ₗ[F] V) w).trans
      (mul_le_of_le_one_left (basisNorm_nonneg w) hz.1.basisOpNorm_le)
  refine le_antisymm (key k hk v) ?_
  have := key k⁻¹ (inv_mem hk) (specP Q k v)
  rw [← specP_mul_apply, inv_mul_cancel, map_one] at this
  exact this

/-- **`latticeSpin` is clopen**: matrix entries and `detChar` are continuous, and closed balls and
spheres are clopen in an ultrametric field. -/
theorem isClopen_latticeSpin [Finite κ] [TopologicalSpace V] [IsModuleTopology F V]
    (Q : QuadraticForm F V) (e : Basis κ F V) : IsClopen (latticeSpin Q e : Set (GSpin Q)) := by
  classical
  have := Fintype.ofFinite κ
  have hball : IsClopen (Metric.closedBall (0 : F) 1) :=
    IsUltrametricDist.isClopen_closedBall 0 one_ne_zero
  have hsph : IsClopen (Metric.sphere (0 : F) 1) :=
    IsUltrametricDist.isClopen_sphere 0 one_ne_zero
  have hA : IsClopen {k : GSpin Q | MapsLattice e (specP Q k : V →ₗ[F] V)} := by
    have h : {k : GSpin Q | MapsLattice e (specP Q k : V →ₗ[F] V)} =
        ⋂ i, ⋂ j, (fun k : GSpin Q => e.repr (specP Q k (e j)) i) ⁻¹' Metric.closedBall 0 1 := by
      ext k
      simp only [mapsLattice_iff, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage,
        Metric.mem_closedBall, dist_zero_right]
      rfl
    rw [h]
    exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j =>
      hball.preimage ((IsModuleTopology.continuous_of_linearMap (e.coord i)).comp
        (continuous_specP_apply continuous_id (e j)))
  have h : (latticeSpin Q e : Set (GSpin Q)) =
      {k : GSpin Q | MapsLattice e (specP Q k : V →ₗ[F] V)} ∩
        ((fun k => k⁻¹) ⁻¹' {k : GSpin Q | MapsLattice e (specP Q k : V →ₗ[F] V)} ∩
          (fun k : GSpin Q => ((detChar Q k : Fˣ) : F)) ⁻¹' Metric.sphere 0 1) := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Metric.mem_sphere,
      dist_zero_right]
    rfl
  rw [h]
  exact hA.inter ((hA.preimage continuous_inv).inter (hsph.preimage (continuous_detChar Q)))

omit [Module.Finite F V] in
/-- `P((u w)⁻¹) = s_w s_u`. -/
theorem specP_gspinPair_inv_apply
    (Q : QuadraticForm F V) {u w : V} (hu : Q u ≠ 0) (hw : Q w ≠ 0) (v : V) :
    specP Q (gspinPair Q hu hw)⁻¹ v = quadReflection Q w (quadReflection Q u v) := by
  apply (specP Q (gspinPair Q hu hw)).injective
  rw [← specP_mul_apply, mul_inv_cancel, map_one]
  change v = (specP Q (gspinPair Q hu hw) : V →ₗ[F] V) _
  rw [specP_gspinPair, mul_apply_eq_comp, quadReflection_quadReflection Q hw,
    quadReflection_quadReflection Q hu]

/-- **Pairs of unit vectors give elements of `latticeSpin`**: for `u, w ∈ Λ_e` with
`‖q(u)‖ = ‖q(w)‖ = 1`, and `polar` integral on `Λ_e`, `u w ∈ latticeSpin Q e`. -/
theorem gspinPair_mem_latticeSpin (Q : QuadraticForm F V) (e : Basis κ F V)
    (hpol : ∀ x y : V, (∀ i, ‖e.repr x i‖ ≤ 1) → (∀ i, ‖e.repr y i‖ ≤ 1) →
      ‖QuadraticMap.polar Q x y‖ ≤ 1)
    {u w : V} (hu : Q u ≠ 0) (hw : Q w ≠ 0) (hul : ∀ i, ‖e.repr u i‖ ≤ 1)
    (hwl : ∀ i, ‖e.repr w i‖ ≤ 1) (hu1 : ‖Q u‖ = 1) (hw1 : ‖Q w‖ = 1) :
    gspinPair Q hu hw ∈ latticeSpin Q e := by
  have su := mapsLattice_quadReflection e Q hpol hul hu1
  have sw := mapsLattice_quadReflection e Q hpol hwl hw1
  refine ⟨?_, ?_, norm_detChar_gspinPair Q hu hw hu1 hw1⟩
  · rw [specP_gspinPair]; exact su.mul sw
  · intro v hv i
    rw [LinearEquiv.coe_coe, specP_gspinPair_inv_apply]
    exact sw _ (su v hv) i

end LatticeSpin

/-! ## A split form of rank three: transitivity on isotropic lines -/

section Rank3

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
  {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]

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

/-- **A swap in `latticeSpin`**: for isotropic `x, y ∈ Λ_e` with `‖polar(x, y)‖ = 1` and
`x ⊥ e₁`, the pair element `(x - y) e₁` maps `x` to `y`. -/
theorem exists_mem_latticeSpin_swap {x y : V} (hx : Q x = 0) (hy : Q y = 0)
    (hxl : ∀ i, ‖e.repr x i‖ ≤ 1) (hyl : ∀ i, ‖e.repr y i‖ ≤ 1)
    (hxy : ‖QuadraticMap.polar Q x y‖ = 1) (hx1 : e.repr x 1 = 0) :
    ∃ k ∈ latticeSpin Q e, specP Q k x = y := by
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
  refine ⟨gspinPair Q hu hw, gspinPair_mem_latticeSpin Q e hpol hu hw hul
    (norm_repr_basis_le_one e 1) hu1 hw1, ?_⟩
  change (specP Q (gspinPair Q hu hw) : V →ₗ[F] V) x = y
  rw [specP_gspinPair, mul_apply_eq_comp]
  rw [quadReflection_apply_of_polar_eq_zero Q (u := e 1) (x := x) (by
    rw [polar_eq_of_rank3 Q e hQ, hx1]; simp)]
  exact quadReflection_sub_apply_self Q hx hy hpne

/-- **`latticeSpin` is transitive on isotropic lines** for the split rank-three form `ac + b²`:
the elements `k` used are integral (`P(k)^{±1} Λ_e ⊆ Λ_e`) with `‖detChar(k)‖ = 1`, and for every
isotropic `v ≠ 0` one of them maps `e₂` into `F^× v`.  Divide `v` by its larger end coordinate
(the middle one is then integral too, `b² = -ac`), and compose at most two swaps
(`exists_mem_latticeSpin_swap`). -/
theorem exists_mem_latticeSpin_apply_eq_smul {v : V} (hv : v ≠ 0) (hQv : Q v = 0) :
    ∃ k ∈ latticeSpin Q e, ∃ t : F, t ≠ 0 ∧ specP Q k (e 2) = t • v := by
  set a := e.repr v 0
  set b := e.repr v 1
  set c := e.repr v 2
  have hab : a * c + b ^ 2 = 0 := by rw [← hQv, hQ]
  have hbsq : ‖b‖ ^ 2 = ‖a‖ * ‖c‖ := by
    rw [← norm_pow, ← norm_mul, show b ^ 2 = -(a * c) by linear_combination hab, norm_neg]
  have hrepr : ∀ (s : F) (i : Fin 3), e.repr (s • v) i = s * e.repr v i := fun s i => by simp
  have hQs : ∀ s : F, Q (s • v) = 0 := fun s => by rw [QuadraticMap.map_smul, hQv, smul_zero]
  have hself : ∀ i : Fin 3, ∀ j, ‖e.repr (e i) j‖ ≤ 1 := norm_repr_basis_le_one e
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
    have ha : a ≠ 0 := fun ha =>
      hv0 ⟨ha, norm_le_zero_iff.1 (by rw [ha, norm_zero] at hca; exact hca)⟩
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
    obtain ⟨k, hk, hke⟩ := exists_mem_latticeSpin_swap Q e hQ (hQe 2 (by decide)) (hQs a⁻¹)
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
    obtain ⟨k₁, hk₁, hke₁⟩ := exists_mem_latticeSpin_swap Q e hQ (hQe 0 (by decide)) (hQs c⁻¹)
      (hself 0) hyl (by rw [polar_eq_of_rank3 Q e hQ]; simp [hc, c])
      (by simp)
    obtain ⟨k₀, hk₀, hke₀⟩ := exists_mem_latticeSpin_swap Q e hQ (hQe 2 (by decide))
      (hQe 0 (by decide)) (hself 2) (hself 0)
      (by rw [polar_eq_of_rank3 Q e hQ]; simp)
      (by simp)
    refine ⟨k₁ * k₀, mul_mem hk₁ hk₀, c⁻¹, inv_ne_zero hc, ?_⟩
    rw [specP_mul_apply, hke₀, hke₁]

end Rank3

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)
  {nW nV : ℕ} (eW : Basis (Fin nW) F (Fin d.m → F)) (eV : Basis (Fin nV) F d.V)

/-! ## The subgroup `latticeK` -/

/-- **The lattice stabilizer** `K(e_W, e_V) = latticeSpin(W, e_W) × latticeSpin(V, e_V)`: the
`g ∈ G` such that `P(g)^{±1}` map `Λ_{e_W}`, `Λ_{e_V}` into themselves and `‖detChar(g)‖ = 1` on
both factors. -/
def latticeK : Subgroup ↥d.G :=
  (latticeSpin d.QW eW).comap d.fst ⊓ (latticeSpin d.QV eV).comap d.snd

theorem isClopen_latticeK : IsClopen (d.latticeK eW eV : Set ↥d.G) :=
  ((isClopen_latticeSpin d.QW eW).preimage d.continuous_fst).inter
    ((isClopen_latticeSpin d.QV eV).preimage d.continuous_snd)

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
    · have h2 := hg.1.2.1
      rw [map_inv] at h2
      exact (hW _).trans ((mul_le_of_le_one_right hCW h2.basisOpNorm_le).trans
        (le_max_right _ _))
  have hgV : glMaxNorm (specP d.QV (d.snd g)) ≤ max 1 CV := by
    refine max_le (le_max_left _ _) (max_le ?_ ?_)
    · exact (hV _).trans ((mul_le_of_le_one_right hCV hg.2.1.basisOpNorm_le).trans
        (le_max_right _ _))
    · have h2 := hg.2.2.1
      rw [map_inv] at h2
      exact (hV _).trans ((mul_le_of_le_one_right hCV h2.basisOpNorm_le).trans
        (le_max_right _ _))
  unfold logNormSO
  rw [Pbar_fst, Pbar_snd]
  have h1 := d.one_le_max_glMaxNorm (d.Pbar g)
  rw [Pbar_fst, Pbar_snd] at h1
  linarith [Real.log_le_log (by linarith) (max_le_max hgW hgV)]

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
  have hT : IsCompact T :=
    (isCompact_units_norm_pow hNW _ _).prod (isCompact_units_norm_pow hNV _ _)
  have hS : IsCompact ((fun p : (Fˣ × Fˣ) × ↥d.G => (d.scalarPair p.1.1 p.1.2)⁻¹ * p.2) ''
      (T ×ˢ C)) :=
    (hT.prod hC).image (((d.continuous_scalarPair.comp _root_.continuous_fst).inv).mul
      _root_.continuous_snd)
  refine hS.of_isClosed_subset (d.isClopen_latticeK eW eV).1 fun g hg => ?_
  obtain ⟨z, ⟨c, rfl⟩, hzg⟩ := hlift g (hM g hg)
  have hzc : (d.pair.comp ((scalarGSpin d.QW).prodMap (scalarGSpin d.QV))) c =
      d.scalarPair c.1 c.2 := rfl
  rw [hzc] at hzg
  have dW : ‖((detChar d.QW (d.fst (d.scalarPair c.1 c.2 * g)) : Fˣ) : F)‖ =
      ‖(c.1 : F)‖ ^ NW := by
    rw [map_mul, map_mul, Units.val_mul, norm_mul, hg.1.2.2, mul_one]
    simp [scalarPair, fst_pair, detChar_scalarGSpin, NW]
  have dV : ‖((detChar d.QV (d.snd (d.scalarPair c.1 c.2 * g)) : Fˣ) : F)‖ =
      ‖(c.2 : F)‖ ^ NV := by
    rw [map_mul, map_mul, Units.val_mul, norm_mul, hg.2.2.2, mul_one]
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

/-- **`(1, y) ∈ latticeK`** for `y ∈ latticeSpin(V, e_V)`. -/
theorem inr_mem_latticeK {y : GSpin d.QV} (hy : y ∈ latticeSpin d.QV eV) :
    d.inr y ∈ d.latticeK eW eV :=
  ⟨show d.fst (d.inr y) ∈ latticeSpin d.QW eW by rw [fst_inr_eq_one]; exact one_mem _, hy⟩

end GGPData

end GSpinGGP
