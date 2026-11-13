/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.SpecialOrthogonal

/-!
# Coordinate norms for a basis, and bounded subsets of orthogonal groups

For a basis `b` of a finite-dimensional space `V` over a normed field, `basisNorm b x` is the
sup-norm of the coordinates of `x`, and `basisOpNorm b f` the sup-norm of the matrix of `f`. Over
an ultrametric field these are the lattice norm of `⊕ 𝒪 bᵢ` and its operator norm.

For an orthogonal basis of a quadratic space the coordinates are `polar Q x bᵢ / polar Q bᵢ bᵢ`,
which gives the estimates used for the weak Cartan decomposition (Thesis Prop. 8.3.1): `polar Q`
and `Q` are bounded, and an isometry and its inverse have comparable operator norms.

The topology on `V ≃ₗ[F] V` is the forward-and-inverse topology (`instTopologicalSpaceLinearEquiv`).
On the orthogonal group the inverse is the adjoint, so this is the subspace topology of
`Module.End F V`: a subset of `O(Q)` is relatively compact exactly when its operator norms are
bounded (`isCompact_orthogonal_setOf_basisOpNorm_le`, `exists_basisOpNorm_le_of_isCompact`).

* `basisNorm`, `basisOpNorm`, `basisNorm_apply_le`, `basisOpNorm_mul_le`: the norms.
* `repr_eq_polar_div`, `norm_polar_le`, `norm_apply_le`: an orthogonal basis.
* `basisOpNorm_symm_le`: `‖g⁻¹‖ ≤ κ ‖g‖` on the orthogonal group.
* `isCompact_orthogonal_setOf_basisOpNorm_le`,
  `isCompact_specialOrthogonal_setOf_basisOpNorm_le`: bounded sets are relatively compact.
* `exists_basisOpNorm_le_of_isCompact`: compact sets are bounded.
-/

noncomputable section

open Module

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F]
variable {V : Type*} [AddCommGroup V] [Module F V] {n : ℕ} (b : Module.Basis (Fin n) F V)

/-! ## The coordinate norms -/

/-- The sup-norm of the coordinates of `x` in the basis `b`. -/
def basisNorm (x : V) : ℝ := ‖b.equivFun x‖

/-- The sup-norm of the matrix of `f` in the basis `b`. -/
def basisOpNorm (f : V →ₗ[F] V) : ℝ := ‖fun i => b.equivFun (f (b i))‖

variable {b}

theorem basisNorm_nonneg (x : V) : 0 ≤ basisNorm b x := norm_nonneg _

theorem basisOpNorm_nonneg (f : V →ₗ[F] V) : 0 ≤ basisOpNorm b f := norm_nonneg _

theorem norm_repr_le_basisNorm (x : V) (i : Fin n) : ‖b.repr x i‖ ≤ basisNorm b x := by
  simpa [basisNorm] using norm_le_pi_norm (b.equivFun x) i

theorem basisNorm_le_iff {x : V} {r : ℝ} (hr : 0 ≤ r) :
    basisNorm b x ≤ r ↔ ∀ i, ‖b.repr x i‖ ≤ r := by
  simp [basisNorm, pi_norm_le_iff_of_nonneg hr]

theorem basisOpNorm_le_iff {f : V →ₗ[F] V} {r : ℝ} (hr : 0 ≤ r) :
    basisOpNorm b f ≤ r ↔ ∀ i, basisNorm b (f (b i)) ≤ r := by
  simp [basisOpNorm, basisNorm, pi_norm_le_iff_of_nonneg hr]

theorem basisNorm_apply_basis_le_basisOpNorm (f : V →ₗ[F] V) (i : Fin n) :
    basisNorm b (f (b i)) ≤ basisOpNorm b f :=
  (basisOpNorm_le_iff (basisOpNorm_nonneg f)).1 le_rfl i

@[simp]
theorem basisNorm_zero : basisNorm b (0 : V) = 0 := by simp [basisNorm]

theorem basisNorm_smul (c : F) (x : V) : basisNorm b (c • x) = ‖c‖ * basisNorm b x := by
  simp [basisNorm, norm_smul]

theorem basisNorm_neg (x : V) : basisNorm b (-x) = basisNorm b x := by
  simp [basisNorm]

@[simp]
theorem basisNorm_basis (i : Fin n) : basisNorm b (b i) = 1 := by
  have : b.equivFun (b i) = Pi.single i 1 := by
    ext j; simp [Pi.single_apply, eq_comm]
  rw [basisNorm, this]
  rw [Pi.norm_single, norm_one]

/-- A vector is determined by its coordinates; two vectors with the same coordinates in the
basis are equal. -/
theorem basisNorm_eq_zero {x : V} : basisNorm b x = 0 ↔ x = 0 := by
  simp [basisNorm]

section Ultra

variable [IsUltrametricDist F]

theorem basisNorm_add_le (x y : V) :
    basisNorm b (x + y) ≤ max (basisNorm b x) (basisNorm b y) := by
  simpa [basisNorm] using IsUltrametricDist.norm_add_le_max (b.equivFun x) (b.equivFun y)

theorem basisNorm_sub_le (x y : V) :
    basisNorm b (x - y) ≤ max (basisNorm b x) (basisNorm b y) := by
  rw [sub_eq_add_neg, ← basisNorm_neg y]
  exact basisNorm_add_le x (-y)

theorem basisNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → V) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i ∈ s, basisNorm b (f i) ≤ C) : basisNorm b (∑ i ∈ s, f i) ≤ C := by
  rw [basisNorm, map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC h

/-- The strict ultrametric inequality: the dominant summand determines the norm. -/
theorem basisNorm_add_eq_left {x y : V} (h : basisNorm b y < basisNorm b x) :
    basisNorm b (x + y) = basisNorm b x := by
  simpa [basisNorm] using IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne' |>.trans
    (max_eq_left h.le)

theorem basisNorm_apply_le (f : V →ₗ[F] V) (x : V) :
    basisNorm b (f x) ≤ basisOpNorm b f * basisNorm b x := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul]
  refine basisNorm_sum_le _ _ (mul_nonneg (basisOpNorm_nonneg f) (basisNorm_nonneg x))
    fun i _ => ?_
  rw [basisNorm_smul, mul_comm]
  exact mul_le_mul (basisNorm_apply_basis_le_basisOpNorm f i) (norm_repr_le_basisNorm x i)
    (norm_nonneg _) (basisOpNorm_nonneg f)

theorem basisOpNorm_comp_le (f g : V →ₗ[F] V) :
    basisOpNorm b (f ∘ₗ g) ≤ basisOpNorm b f * basisOpNorm b g :=
  (basisOpNorm_le_iff (mul_nonneg (basisOpNorm_nonneg f) (basisOpNorm_nonneg g))).2 fun i =>
    (basisNorm_apply_le f (g (b i))).trans
      (mul_le_mul_of_nonneg_left (basisNorm_apply_basis_le_basisOpNorm g i)
        (basisOpNorm_nonneg f))

theorem basisOpNorm_mul_le (f g : V ≃ₗ[F] V) :
    basisOpNorm b ((f * g : V ≃ₗ[F] V) : V →ₗ[F] V) ≤
      basisOpNorm b (f : V →ₗ[F] V) * basisOpNorm b (g : V →ₗ[F] V) :=
  basisOpNorm_comp_le (f : V →ₗ[F] V) g

end Ultra

theorem basisOpNorm_id_le : basisOpNorm b (LinearMap.id : V →ₗ[F] V) ≤ 1 :=
  (basisOpNorm_le_iff zero_le_one).2 fun i => by simp

/-! ## Orthogonal bases of a quadratic space -/

section Orthogonal

variable [CharZero F] {Q : QuadraticForm F V}

/-- The basis `b` is orthogonal for `Q` and consists of anisotropic vectors. -/
structure IsOrthoBasis (Q : QuadraticForm F V) (b : Module.Basis (Fin n) F V) : Prop where
  polar_eq_zero : ∀ i j, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0
  apply_ne_zero : ∀ i, Q (b i) ≠ 0

variable (hb : IsOrthoBasis Q b)
include hb

theorem IsOrthoBasis.polar_self_ne_zero (i : Fin n) :
    QuadraticMap.polar Q (b i) (b i) ≠ 0 := by
  rw [QuadraticMap.polar_self, two_nsmul]
  intro h
  exact hb.apply_ne_zero i (by
    have : (2 : F) * Q (b i) = 0 := by rw [two_mul]; exact h
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero)

omit [CharZero F] in
theorem IsOrthoBasis.polar_basis_right (x : V) (i : Fin n) :
    QuadraticMap.polar Q x (b i) = b.repr x i * QuadraticMap.polar Q (b i) (b i) := by
  rw [← QuadraticMap.polarBilin_apply_apply]
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    QuadraticMap.polarBilin_apply_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [hb.polar_eq_zero j i hj, mul_zero])
    (by simp)]

/-- Coordinates in an orthogonal basis: `xᵢ = polar Q x bᵢ / polar Q bᵢ bᵢ`. -/
theorem IsOrthoBasis.repr_eq_polar_div (x : V) (i : Fin n) :
    b.repr x i = QuadraticMap.polar Q x (b i) / QuadraticMap.polar Q (b i) (b i) := by
  rw [hb.polar_basis_right, mul_div_cancel_right₀ _ (hb.polar_self_ne_zero i)]

omit [CharZero F] in
theorem IsOrthoBasis.polar_eq_sum (x y : V) :
    QuadraticMap.polar Q x y =
      ∑ i, b.repr x i * b.repr y i * QuadraticMap.polar Q (b i) (b i) := by
  rw [← QuadraticMap.polarBilin_apply_apply]
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    QuadraticMap.polarBilin_apply_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [QuadraticMap.polar_comm, hb.polar_basis_right, mul_assoc]

theorem IsOrthoBasis.apply_eq_sum (x : V) :
    Q x = ∑ i, b.repr x i ^ 2 * Q (b i) := by
  have h := hb.polar_eq_sum x x
  rw [QuadraticMap.polar_self, two_nsmul] at h
  have h2 : (2 : F) * Q x = 2 * ∑ i, b.repr x i ^ 2 * Q (b i) := by
    rw [two_mul, h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [QuadraticMap.polar_self, two_nsmul]; ring
  exact mul_left_cancel₀ two_ne_zero h2

/-- The bound for `polar Q`: `‖polar Q x y‖ ≤ cₚ ‖x‖ ‖y‖`. -/
def polarBound (Q : QuadraticForm F V) (b : Module.Basis (Fin n) F V) : ℝ :=
  ‖fun i => QuadraticMap.polar Q (b i) (b i)‖

/-- The bound for `Q`: `‖Q x‖ ≤ c_Q ‖x‖²`. -/
def formBound (Q : QuadraticForm F V) (b : Module.Basis (Fin n) F V) : ℝ :=
  ‖fun i => Q (b i)‖

omit hb [CharZero F] in
theorem norm_polar_basis_le (i : Fin n) :
    ‖QuadraticMap.polar Q (b i) (b i)‖ ≤ polarBound Q b :=
  norm_le_pi_norm (fun i => QuadraticMap.polar Q (b i) (b i)) i

omit hb [CharZero F] in
theorem norm_apply_basis_le (i : Fin n) : ‖Q (b i)‖ ≤ formBound Q b :=
  norm_le_pi_norm (fun i => Q (b i)) i

/-- The constant `κ` with `‖g⁻¹‖ ≤ κ ‖g‖` on the orthogonal group. -/
def adjBound (Q : QuadraticForm F V) (b : Module.Basis (Fin n) F V) : ℝ :=
  formBound Q b * ‖fun i => (Q (b i))⁻¹‖

/-- The inverse of an isometry is its adjoint: in an orthogonal basis its matrix entries are those
of `g`, transposed and rescaled by `Q bₖ / Q bᵢ`. -/
theorem IsOrthoBasis.repr_symm_apply (g : V ≃ₗ[F] V) (hg : ∀ x, Q (g x) = Q x) (i k : Fin n) :
    b.repr (g.symm (b k)) i = b.repr (g (b i)) k * Q (b k) / Q (b i) := by
  have hpol : ∀ x y, QuadraticMap.polar Q (g x) (g y) = QuadraticMap.polar Q x y := by
    intro x y; simp only [QuadraticMap.polar, ← map_add, hg]
  rw [hb.repr_eq_polar_div, hb.repr_eq_polar_div,
    ← hpol (g.symm (b k)) (b i), LinearEquiv.apply_symm_apply, QuadraticMap.polar_comm]
  have h1 := hb.polar_self_ne_zero i
  have h2 := hb.polar_self_ne_zero k
  have hQi := hb.apply_ne_zero i
  have hQk := hb.apply_ne_zero k
  simp only [QuadraticMap.polar_self, two_nsmul] at h1 h2 ⊢
  field_simp

theorem IsOrthoBasis.basisOpNorm_symm_le (g : V ≃ₗ[F] V) (hg : ∀ x, Q (g x) = Q x) :
    basisOpNorm b (g.symm : V →ₗ[F] V) ≤ adjBound Q b * basisOpNorm b (g : V →ₗ[F] V) := by
  have h0 : 0 ≤ adjBound Q b * basisOpNorm b (g : V →ₗ[F] V) :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (basisOpNorm_nonneg _)
  refine (basisOpNorm_le_iff h0).2 fun k => (basisNorm_le_iff h0).2 fun i => ?_
  rw [LinearEquiv.coe_coe, hb.repr_symm_apply g hg, mul_div_assoc, norm_mul, div_eq_mul_inv,
    norm_mul, adjBound]
  calc ‖b.repr (g (b i)) k‖ * (‖Q (b k)‖ * ‖(Q (b i))⁻¹‖)
      ≤ basisOpNorm b (g : V →ₗ[F] V) * (formBound Q b * ‖fun i => (Q (b i))⁻¹‖) :=
        mul_le_mul ((norm_repr_le_basisNorm _ k).trans
            (basisNorm_apply_basis_le_basisOpNorm (g : V →ₗ[F] V) i))
          (mul_le_mul (norm_apply_basis_le k) (norm_le_pi_norm (fun i => (Q (b i))⁻¹) i)
            (norm_nonneg _) (norm_nonneg _)) (by positivity) (basisOpNorm_nonneg _)
    _ = _ := by ring

variable [IsUltrametricDist F]

omit [CharZero F] in
theorem IsOrthoBasis.norm_polar_le (x y : V) :
    ‖QuadraticMap.polar Q x y‖ ≤ polarBound Q b * basisNorm b x * basisNorm b y := by
  rw [hb.polar_eq_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (mul_nonneg (norm_nonneg _) (basisNorm_nonneg x)) (basisNorm_nonneg y))
    fun i _ => ?_
  rw [norm_mul, norm_mul]
  calc ‖b.repr x i‖ * ‖b.repr y i‖ * ‖QuadraticMap.polar Q (b i) (b i)‖
      ≤ basisNorm b x * basisNorm b y * polarBound Q b :=
        mul_le_mul (mul_le_mul (norm_repr_le_basisNorm x i) (norm_repr_le_basisNorm y i)
          (norm_nonneg _) (basisNorm_nonneg x)) (norm_polar_basis_le i) (norm_nonneg _)
          (mul_nonneg (basisNorm_nonneg x) (basisNorm_nonneg y))
    _ = _ := by ring

theorem IsOrthoBasis.norm_apply_le (x : V) :
    ‖Q x‖ ≤ formBound Q b * basisNorm b x ^ 2 := by
  rw [hb.apply_eq_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (norm_nonneg _) (pow_nonneg (basisNorm_nonneg x) 2)) fun i _ => ?_
  rw [norm_mul, norm_pow, mul_comm]
  exact mul_le_mul (norm_apply_basis_le i)
    (pow_le_pow_left₀ (norm_nonneg _) (norm_repr_le_basisNorm x i) 2) (by positivity)
    (norm_nonneg _)

end Orthogonal

/-! ## Bounded subsets of the orthogonal group are relatively compact -/

section Compact

variable (b)

/-- The matrix of an endomorphism in the basis `b`, row `i` being the coordinates of `f bᵢ`. -/
def basisMatrix : Module.End F V →ₗ[F] (Fin n → Fin n → F) where
  toFun f i := b.equivFun (f (b i))
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp

/-- The endomorphism with a given matrix. -/
def basisMatrixInv : (Fin n → Fin n → F) →ₗ[F] Module.End F V where
  toFun M := b.constr F fun i => b.equivFun.symm (M i)
  map_add' M N := by ext x; simp [add_smul, Finset.sum_add_distrib]
  map_smul' c M := by
    ext x
    simp [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ring

variable {b}

theorem basisOpNorm_eq (f : V →ₗ[F] V) : basisOpNorm b f = ‖basisMatrix b f‖ := rfl

theorem basisMatrixInv_basisMatrix (f : Module.End F V) :
    basisMatrixInv b (basisMatrix b f) = f :=
  b.ext fun i => by simp [basisMatrixInv, basisMatrix]

theorem continuous_basisOpNorm :
    Continuous fun f : Module.End F V => basisOpNorm b f :=
  continuous_norm.comp (IsModuleTopology.continuous_of_linearMap (basisMatrix b))

variable [FiniteDimensional F V]

/-- A closed ball for the operator norm is compact in `Module.End F V`. -/
theorem isCompact_setOf_basisOpNorm_le [LocallyCompactSpace F] (M : ℝ) :
    IsCompact {f : Module.End F V | basisOpNorm b f ≤ M} := by
  have : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  refine ((isCompact_closedBall (0 : Fin n → Fin n → F) M).image
    (IsModuleTopology.continuous_of_linearMap (basisMatrixInv b))).of_isClosed_subset
    (isClosed_le continuous_basisOpNorm continuous_const) fun f hf => ?_
  exact ⟨basisMatrix b f, by simpa [basisOpNorm_eq] using hf, basisMatrixInv_basisMatrix f⟩

/-- **Bounded subsets of `O(Q)` are relatively compact.** For an orthogonal basis `b`, the
isometries of operator norm at most `M` form a compact subset of `V ≃ₗ[F] V`. The inverse of an
isometry is bounded through `basisOpNorm_symm_le`, so the forward-and-inverse topology of
`V ≃ₗ[F] V` agrees on `O(Q)` with the topology of `Module.End F V`. -/
theorem isCompact_orthogonal_setOf_basisOpNorm_le [CharZero F] [LocallyCompactSpace F]
    {Q : QuadraticForm F V} (hb : IsOrthoBasis Q b) (M : ℝ) :
    IsCompact {g : V ≃ₗ[F] V | g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      basisOpNorm b (g : V →ₗ[F] V) ≤ M} := by
  set M' := max M (adjBound Q b * M)
  let C : Set (Module.End F V) := {f | basisOpNorm b f ≤ M'}
  have hC : IsCompact C := isCompact_setOf_basisOpNorm_le M'
  let T : Set (Module.End F V × Module.End F V) :=
    (C ×ˢ C) ∩ {p | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1}
  have hT : IsCompact T :=
    (hC.prod hC).inter_right
      ((isClosed_eq (continuous_fst.mul continuous_snd) continuous_const).inter
        (isClosed_eq (continuous_snd.mul continuous_fst) continuous_const))
  have : CompactSpace T := isCompact_iff_compactSpace.mp hT
  let Φ : T → V ≃ₗ[F] V := fun p => LinearEquiv.ofLinearMap p.1.1 p.1.2 p.2.2.1 p.2.2.2
  have hΦ : Continuous Φ := TauCeti.continuous_linearEquiv_iff.mpr
    ⟨(continuous_fst.comp continuous_subtype_val).congr fun p => by simp [Φ],
      (continuous_snd.comp continuous_subtype_val).congr fun p =>
        LinearMap.ext fun x => by simp [Φ]⟩
  have hclosed : IsClosed {g : V ≃ₗ[F] V | g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      basisOpNorm b (g : V →ₗ[F] V) ≤ M} :=
    (TauCeti.QuadraticMap.isClosed_orthogonalGroup Q).inter
      (isClosed_le (continuous_basisOpNorm.comp TauCeti.continuous_linearEquiv_toLinearMap)
        continuous_const)
  refine (isCompact_range hΦ).of_isClosed_subset hclosed fun g ⟨hg, hgM⟩ => ?_
  have hg' : ∀ x, Q (g x) = Q x := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hg
  have hinvM : basisOpNorm b (g.symm : V →ₗ[F] V) ≤ M' :=
    (hb.basisOpNorm_symm_le g hg').trans <| (mul_le_mul_of_nonneg_left hgM
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans (le_max_right _ _)
  refine ⟨⟨((g : Module.End F V), (g.symm : Module.End F V)),
    ⟨hgM.trans (le_max_left _ _), hinvM⟩,
    LinearMap.ext fun x => by simp, LinearMap.ext fun x => by simp⟩,
    LinearEquiv.ext fun x => by simp [Φ]⟩

/-- **Bounded subsets of `SO(Q)` are relatively compact** (Fact 1.3 of the weak Cartan
decomposition). -/
theorem isCompact_specialOrthogonal_setOf_basisOpNorm_le [CharZero F] [LocallyCompactSpace F]
    {Q : QuadraticForm F V} (hb : IsOrthoBasis Q b) (M : ℝ) :
    IsCompact {g : V ≃ₗ[F] V | g ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q ∧
      basisOpNorm b (g : V →ₗ[F] V) ≤ M} := by
  refine (isCompact_orthogonal_setOf_basisOpNorm_le hb M).of_isClosed_subset
    ((TauCeti.QuadraticMap.isClosed_specialOrthogonalGroup Q).inter
      (isClosed_le (continuous_basisOpNorm.comp TauCeti.continuous_linearEquiv_toLinearMap)
        continuous_const)) fun g ⟨hg, hgM⟩ =>
    ⟨TauCeti.QuadraticMap.specialOrthogonalGroup_le_orthogonalGroup Q hg, hgM⟩

omit [FiniteDimensional F V] in
/-- **Compact sets are bounded.** -/
theorem exists_basisOpNorm_le_of_isCompact {K : Set (V ≃ₗ[F] V)} (hK : IsCompact K) :
    ∃ M, ∀ g ∈ K, basisOpNorm b (g : V →ₗ[F] V) ≤ M := by
  obtain ⟨M, hM⟩ := (hK.image (continuous_basisOpNorm.comp
    TauCeti.continuous_linearEquiv_toLinearMap)).isBounded.bddAbove
  exact ⟨M, fun g hg => hM ⟨g, hg, rfl⟩⟩

end Compact

end GSpinGGP
