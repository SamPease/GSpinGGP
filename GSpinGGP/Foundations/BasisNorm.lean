/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.SpecialOrthogonal
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

/-!
# Coordinate norms for a basis, and bounded subsets of orthogonal groups

For a basis `b` of a finite-dimensional space `V` over a normed field, `basisNorm b x` is the
sup-norm of the coordinates of `x`, and `basisOpNorm b f` the sup-norm of the matrix of `f`. Over
an ultrametric field these are the lattice norm of `⊕ 𝒪 bᵢ` and its operator norm.

For an orthogonal basis of a quadratic space the coordinates are `polar Q bᵢ x / (2 Q bᵢ)`
(Tau Ceti's `QuadraticMap.polar_basis_left`), which gives the estimates used for the weak Cartan
decomposition (Thesis Prop. 8.3.1): `polar Q` and `Q` are bounded, and an isometry and its inverse
have comparable operator norms.

The topology on `V ≃ₗ[F] V` is the forward-and-inverse topology (`instTopologicalSpaceLinearEquiv`).
On the orthogonal group the inverse is the adjoint, so this is the subspace topology of
`Module.End F V`: a subset of `O(Q)` has compact closure if and only if its operator norms are
bounded (`isCompact_orthogonal_setOf_basisOpNorm_le`, `exists_basisOpNorm_le_of_isCompact`).

* `basisNorm`, `basisOpNorm`, `basisNorm_apply_le`, `basisOpNorm_mul_le`: the norms.
* `IsOrthoBasis`, `exists_isOrthoBasis`, `repr_eq_polar_div`, `norm_polar_le`, `norm_apply_le`:
  an orthogonal basis; `IsOrthoBasis.unitsSMul`: rescaling it by units;
  `exists_isOrthoBasis_append`: an orthogonal family of anisotropic vectors in a nondegenerate
  space extends to such a basis.
* `basisOpNorm_symm_le`: `‖g⁻¹‖ ≤ κ ‖g‖` on the orthogonal group.
* `isCompact_orthogonal_setOf_basisOpNorm_le`,
  `isCompact_specialOrthogonal_setOf_basisOpNorm_le`: bounded sets are relatively compact.
* `exists_basisOpNorm_le_of_isCompact`: compact sets are bounded.
* `polar_apply_eq_mul_conj`, `norm_polar_le_of_eigen`, `norm_polar_le_of_fixed`: for eigenvectors
  `x`, `y` of an isometry `A`, `polar(h x, y)` is controlled by the norm of `A h A⁻¹`.
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

/-- Only the zero vector has coordinate norm zero. -/
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
  isOrtho : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j)
  apply_ne_zero : ∀ i, Q (b i) ≠ 0

omit [CharZero F] in
/-- A nondegenerate quadratic space has an orthogonal basis of anisotropic vectors (Tau Ceti's
`QuadraticMap.Nondegenerate.exists_orthogonal_basis`). -/
theorem exists_isOrthoBasis [NeZero (2 : F)] [FiniteDimensional F V] (Q : QuadraticForm F V)
    (hQ : Q.Nondegenerate) :
    ∃ b : Module.Basis (Fin (Module.finrank F V)) F V, IsOrthoBasis Q b := by
  let _ : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨b, hb, hb0⟩ := hQ.exists_orthogonal_basis
  exact ⟨b, hb, hb0⟩

omit [CharZero F] in
/-- `Q (wᵢ bᵢ) = wᵢ² Q bᵢ`. -/
theorem apply_unitsSMul (w : Fin n → Fˣ) (i : Fin n) :
    Q (b.unitsSMul w i) = (w i : F) ^ 2 * Q (b i) := by
  rw [Module.Basis.unitsSMul_apply, Units.smul_def, QuadraticMap.map_smul, smul_eq_mul, _root_.sq]

omit [CharZero F] in
/-- Rescaling the vectors of an orthogonal basis by units (`Module.Basis.unitsSMul`) gives an
orthogonal basis. -/
theorem IsOrthoBasis.unitsSMul (hb : IsOrthoBasis Q b) (w : Fin n → Fˣ) :
    IsOrthoBasis Q (b.unitsSMul w) where
  isOrtho i j hij := by
    rw [← QuadraticMap.isOrtho_polarBilin, QuadraticMap.polarBilin_apply_apply,
      Module.Basis.unitsSMul_apply, Module.Basis.unitsSMul_apply, Units.smul_def, Units.smul_def,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
      (hb.isOrtho i j hij).polar_eq_zero, smul_zero, smul_zero]
  apply_ne_zero i := by
    rw [apply_unitsSMul]
    exact mul_ne_zero (pow_ne_zero _ (w i).ne_zero) (hb.apply_ne_zero i)

omit [CharZero F] in
/-- **Extension to an orthogonal basis.** In a nondegenerate quadratic space, an orthogonal
family `w₀, …, w_{k-1}` of anisotropic vectors is the beginning of an orthogonal basis of
anisotropic vectors: the span `U` of the `wᵢ` is nondegenerate, hence so is `U^⊥`, and
`V = U ⊕ U^⊥` (Tau Ceti's `QuadraticMap.Nondegenerate.nondegenerate_restrict_orthogonal`,
`isCompl_orthogonal`); an orthogonal basis of `U^⊥`
(`QuadraticMap.Nondegenerate.exists_orthogonal_basis`) completes the family. -/
theorem exists_isOrthoBasis_append [NeZero (2 : F)] [FiniteDimensional F V] (hQ : Q.Nondegenerate)
    {k : ℕ} {w : Fin k → V} (hw : ∀ i j, i ≠ j → Q.IsOrtho (w i) (w j)) (hw0 : ∀ i, Q (w i) ≠ 0) :
    ∃ (m : ℕ) (c : Fin m → V) (b : Module.Basis (Fin (k + m)) F V),
      IsOrthoBasis Q b ∧ ⇑b = Fin.append w c := by
  let _ : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have hself : ∀ x, Q x ≠ 0 → Q.polarBilin x x ≠ 0 := fun x hx => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul, ← two_mul]
    exact mul_ne_zero two_ne_zero hx
  have hli : LinearIndependent F w := LinearMap.BilinForm.linearIndependent_of_iIsOrtho
    (fun i j hij => QuadraticMap.isOrtho_polarBilin.mpr (hw i j hij)) fun i => hself _ (hw0 i)
  set U := Submodule.span F (Set.range w)
  have hres : ∀ (N : Submodule F V) (x y : N), (Q.restrict N).IsOrtho x y ↔ Q.IsOrtho x y := by
    intro N x y; simp [QuadraticMap.isOrtho_def]
  have hU : (Q.restrict U).Nondegenerate := by
    refine QuadraticMap.nondegenerate_of_isOrthoᵢ (b := Module.Basis.span hli)
      (fun i j hij => QuadraticMap.associated_isOrtho.mpr ?_) fun i => ?_
    · rw [hres, Module.Basis.coe_span_apply, Module.Basis.coe_span_apply]; exact hw i j hij
    · rw [QuadraticMap.restrict_apply, Module.Basis.coe_span_apply]; exact hw0 i
  set U' := LinearMap.BilinForm.orthogonal Q.polarBilin U
  obtain ⟨bc, hbc, hbc0⟩ := (hQ.nondegenerate_restrict_orthogonal hU).exists_orthogonal_basis
  have hc : IsCompl U U' := hU.isCompl_orthogonal
  let c : Fin (finrank F U') → V := fun i => bc i
  have hortho : ∀ i j, i ≠ j → Q.IsOrtho (Fin.append w c i) (Fin.append w c j) := by
    have hwc : ∀ i j, Q.IsOrtho (w i) (c j) := fun i j =>
      QuadraticMap.isOrtho_polarBilin.mp ((bc j).2 (w i) (Submodule.subset_span ⟨i, rfl⟩))
    intro i j hij
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp only [Fin.append_left, Fin.append_right]
    · exact hw _ _ fun h => hij (by rw [h])
    · exact hwc _ _
    · exact QuadraticMap.isOrtho_comm.mp (hwc _ _)
    · exact (hres _ _ _).mp (hbc _ _ fun h => hij (by rw [h]))
  have hani : ∀ i, Q (Fin.append w c i) ≠ 0 := by
    intro i
    induction i using Fin.addCases <;> simp only [Fin.append_left, Fin.append_right]
    · exact hw0 _
    · exact hbc0 _
  have hli' : LinearIndependent F (Fin.append w c) :=
    LinearMap.BilinForm.linearIndependent_of_iIsOrtho
      (fun i j hij => QuadraticMap.isOrtho_polarBilin.mpr (hortho i j hij))
      fun i => hself _ (hani i)
  have hcard : Fintype.card (Fin (k + finrank F U')) = finrank F V := by
    rw [Fintype.card_fin, ← Submodule.finrank_add_eq_of_isCompl hc, finrank_span_eq_card hli,
      Fintype.card_fin]
  refine ⟨_, c, basisOfLinearIndependentOfCardEqFinrank' _ hli' hcard, ?_, by simp⟩
  exact ⟨fun i j hij => by simpa using hortho i j hij, fun i => by simpa using hani i⟩

variable (hb : IsOrthoBasis Q b)
include hb

omit [CharZero F] in
theorem IsOrthoBasis.polar_eq_zero (i j : Fin n) (hij : i ≠ j) :
    QuadraticMap.polar Q (b i) (b j) = 0 :=
  (hb.isOrtho i j hij).polar_eq_zero

theorem IsOrthoBasis.polar_self_ne_zero (i : Fin n) :
    QuadraticMap.polar Q (b i) (b i) ≠ 0 := by
  rw [QuadraticMap.polar_self, two_nsmul, ← two_mul]
  exact mul_ne_zero two_ne_zero (hb.apply_ne_zero i)

/-- Coordinates in an orthogonal basis: `xᵢ = polar Q bᵢ x / (2 Q bᵢ)`. -/
theorem IsOrthoBasis.repr_eq_polar_div (x : V) (i : Fin n) :
    b.repr x i = QuadraticMap.polar Q (b i) x / (2 * Q (b i)) := by
  rw [QuadraticMap.polar_basis_left Q b hb.isOrtho, mul_div_cancel_left₀ _
    (mul_ne_zero two_ne_zero (hb.apply_ne_zero i))]

omit [CharZero F] in
theorem IsOrthoBasis.polar_eq_sum (x y : V) :
    QuadraticMap.polar Q x y =
      ∑ i, b.repr x i * b.repr y i * QuadraticMap.polar Q (b i) (b i) := by
  rw [← QuadraticMap.polarBilin_apply_apply]
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    QuadraticMap.polarBilin_apply_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [QuadraticMap.polar_basis_left Q b hb.isOrtho, QuadraticMap.polar_self, two_nsmul]
  ring

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
of `g`, transposed and rescaled by `Q bₖ / Q bᵢ` (Tau Ceti's
`basis_value_mul_repr_orthogonal_eq_basis_value_mul_repr_inv`), so `‖g⁻¹‖ ≤ κ ‖g‖`. -/
theorem IsOrthoBasis.basisOpNorm_symm_le {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    basisOpNorm b (g.symm : V →ₗ[F] V) ≤ adjBound Q b * basisOpNorm b (g : V →ₗ[F] V) := by
  have h0 : 0 ≤ adjBound Q b * basisOpNorm b (g : V →ₗ[F] V) :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (basisOpNorm_nonneg _)
  refine (basisOpNorm_le_iff h0).2 fun k => (basisNorm_le_iff h0).2 fun i => ?_
  have hid := QuadraticMap.basis_value_mul_repr_orthogonal_eq_basis_value_mul_repr_inv Q b
    hb.isOrtho ⟨g, hg⟩ k i
  have hQi : (2 : F) * Q (b i) ≠ 0 := mul_ne_zero two_ne_zero (hb.apply_ne_zero i)
  have he : b.repr (g.symm (b k)) i = 2 * Q (b k) * b.repr (g (b i)) k / (2 * Q (b i)) := by
    rw [hid, mul_div_cancel_left₀ _ hQi]; rfl
  rw [LinearEquiv.coe_coe, he, mul_comm (2 * Q (b k)), mul_div_assoc, norm_mul, adjBound]
  have hq : ‖2 * Q (b k) / (2 * Q (b i))‖ = ‖Q (b k)‖ * ‖(Q (b i))⁻¹‖ := by
    rw [mul_div_mul_left _ _ (two_ne_zero (α := F)), norm_div, norm_inv, div_eq_mul_inv]
  rw [hq]
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

/-- The matrix of an endomorphism in the basis `b`, transposed: row `i` holds the coordinates of
`f bᵢ`. -/
def basisMatrix : Module.End F V ≃ₗ[F] (Fin n → Fin n → F) :=
  (LinearMap.toMatrix b b).trans (Matrix.transposeLinearEquiv (Fin n) (Fin n) F F)

variable {b}

theorem basisOpNorm_eq (f : V →ₗ[F] V) : basisOpNorm b f = ‖basisMatrix b f‖ := by
  rw [basisOpNorm]; congr 1; ext i j
  exact (LinearMap.toMatrix_apply b b f j i).symm

theorem continuous_basisOpNorm :
    Continuous fun f : Module.End F V => basisOpNorm b f := by
  simp_rw [basisOpNorm_eq]
  exact continuous_norm.comp
    (IsModuleTopology.continuous_of_linearMap (basisMatrix b).toLinearMap)

variable [FiniteDimensional F V]

/-- A closed ball for the operator norm is compact in `Module.End F V`. -/
theorem isCompact_setOf_basisOpNorm_le [LocallyCompactSpace F] (M : ℝ) :
    IsCompact {f : Module.End F V | basisOpNorm b f ≤ M} := by
  have : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have h : {f : Module.End F V | basisOpNorm b f ≤ M} =
      (basisMatrix b).symm '' Metric.closedBall 0 M := by
    ext f
    refine ⟨fun hf => ⟨basisMatrix b f, by simpa [basisOpNorm_eq] using hf, by simp⟩, ?_⟩
    rintro ⟨x, hx, rfl⟩
    simpa [basisOpNorm_eq] using hx
  rw [h]
  exact (isCompact_closedBall _ _).image
    (IsModuleTopology.continuous_of_linearMap (basisMatrix b).symm.toLinearMap)

/-- Linear automorphisms with the forward and the inverse map in a compact set `C` of
endomorphisms form a compact set (the argument of Tau Ceti's `isCompact_orthogonalGroup`). -/
theorem isCompact_setOf_coe_mem_inv_mem [T2Space F] {C : Set (Module.End F V)}
    (hC : IsCompact C) :
    IsCompact {g : V ≃ₗ[F] V | (g : Module.End F V) ∈ C ∧
      ((g⁻¹ : V ≃ₗ[F] V) : Module.End F V) ∈ C} := by
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
  convert isCompact_range hΦ using 1
  ext g
  refine ⟨fun ⟨h1, h2⟩ => ⟨⟨((g : Module.End F V), ((g⁻¹ : V ≃ₗ[F] V) : Module.End F V)),
    ⟨h1, h2⟩, LinearMap.ext fun x => by simp, LinearMap.ext fun x => by simp⟩,
    LinearEquiv.ext fun x => by simp [Φ]⟩, ?_⟩
  rintro ⟨p, rfl⟩
  refine ⟨by simpa [Φ] using p.2.1.1, ?_⟩
  convert p.2.1.2 using 1
  exact LinearMap.ext fun x => rfl

/-- **Bounded subsets of `O(Q)` are relatively compact.** For an orthogonal basis `b`, the
isometries of operator norm at most `M` form a compact subset of `V ≃ₗ[F] V`. The inverse of an
isometry is bounded through `basisOpNorm_symm_le`, so the forward-and-inverse topology of
`V ≃ₗ[F] V` agrees on `O(Q)` with the topology of `Module.End F V`. -/
theorem isCompact_orthogonal_setOf_basisOpNorm_le [CharZero F] [LocallyCompactSpace F]
    {Q : QuadraticForm F V} (hb : IsOrthoBasis Q b) (M : ℝ) :
    IsCompact {g : V ≃ₗ[F] V | g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      basisOpNorm b (g : V →ₗ[F] V) ≤ M} := by
  set M' := max M (adjBound Q b * M)
  refine (isCompact_setOf_coe_mem_inv_mem
    (isCompact_setOf_basisOpNorm_le (b := b) M')).of_isClosed_subset
    ((TauCeti.QuadraticMap.isClosed_orthogonalGroup Q).inter
      (isClosed_le (continuous_basisOpNorm.comp TauCeti.continuous_linearEquiv_toLinearMap)
        continuous_const)) fun g ⟨hg, hgM⟩ => ⟨hgM.trans (le_max_left _ _), ?_⟩
  exact (hb.basisOpNorm_symm_le hg).trans <| (mul_le_mul_of_nonneg_left hgM
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans (le_max_right _ _)

/-- **Bounded subsets of `SO(Q)` are relatively compact** (used for Thesis Prop. 8.3.1). -/
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

/-! ## Conjugation by an isometry with eigenvectors -/

section Conj

open QuadraticMap

variable {Q : QuadraticForm F V}

/-- If `A x = α x` and `A y = β y` for an isometry `A`, then
`polar(h x, y) = α β polar((A h A⁻¹) x, y)`. -/
theorem polar_apply_eq_mul_conj {A : V ≃ₗ[F] V}
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h : V ≃ₗ[F] V) {x y : V} {α β : F}
    (hx : A x = α • x) (hy : A y = β • y) :
    polar Q (h x) y = α * β * polar Q ((A * h * A⁻¹) x) y := by
  have h1 : (A * h * A⁻¹) (A x) = A (h x) := by
    simp only [LinearEquiv.mul_apply]
    rw [show A⁻¹ (A x) = x from A.symm_apply_apply x]
  rw [← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hA (h x) y, ← h1, hx, hy,
    map_smul, polar_smul_left, polar_smul_right, smul_eq_mul, smul_eq_mul]
  ring

variable [IsUltrametricDist F]

theorem IsOrthoBasis.norm_polar_apply_le (hb : IsOrthoBasis Q b) (g : V ≃ₗ[F] V) (x y : V) :
    ‖polar Q (g x) y‖ ≤
      polarBound Q b * basisOpNorm b (g : V →ₗ[F] V) * basisNorm b x * basisNorm b y := by
  refine (hb.norm_polar_le _ _).trans ?_
  have h1 := basisNorm_apply_le (b := b) (g : V →ₗ[F] V) x
  have hp : 0 ≤ polarBound Q b := norm_nonneg _
  calc polarBound Q b * basisNorm b (g x) * basisNorm b y
      ≤ polarBound Q b * (basisOpNorm b (g : V →ₗ[F] V) * basisNorm b x) * basisNorm b y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hp) (basisNorm_nonneg y)
    _ = _ := by ring

/-- The basic estimate: for eigenvectors `x`, `y` of an isometry `A`, of norm `≤ 1` and with
eigenvalues `α`, `β` such that `|α β| ≤ 1`, the coefficient `polar(h x, y)` is bounded by the
norm of `A h A⁻¹`. -/
theorem norm_polar_le_of_eigen (hb : IsOrthoBasis Q b) {A : V ≃ₗ[F] V}
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h : V ≃ₗ[F] V) {x y : V} {α β : F}
    (hx : A x = α • x) (hy : A y = β • y) (hαβ : ‖α * β‖ ≤ 1) (hxn : basisNorm b x ≤ 1)
    (hyn : basisNorm b y ≤ 1) :
    ‖polar Q (h x) y‖ ≤
      polarBound Q b * basisOpNorm b ((A * h * A⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) := by
  set N := basisOpNorm b ((A * h * A⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V)
  have hp : 0 ≤ polarBound Q b * N := mul_nonneg (norm_nonneg _) (basisOpNorm_nonneg _)
  have hxy : basisNorm b x * basisNorm b y ≤ 1 := by
    nlinarith [basisNorm_nonneg (b := b) x, basisNorm_nonneg (b := b) y]
  have h2 : ‖polar Q ((A * h * A⁻¹) x) y‖ ≤ polarBound Q b * N := by
    refine (hb.norm_polar_apply_le (A * h * A⁻¹) x y).trans ?_
    calc polarBound Q b * N * basisNorm b x * basisNorm b y
        = (polarBound Q b * N) * (basisNorm b x * basisNorm b y) := by ring
      _ ≤ (polarBound Q b * N) * 1 := mul_le_mul_of_nonneg_left hxy hp
      _ = _ := mul_one _
  rw [polar_apply_eq_mul_conj hA h hx hy, norm_mul]
  calc ‖α * β‖ * ‖polar Q ((A * h * A⁻¹) x) y‖ ≤ 1 * (polarBound Q b * N) :=
        mul_le_mul hαβ h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- A fixed vector pair: if an isometry `T` fixes `x` and `y`, `polar(h x, y)` is bounded by the
norm of `T h T⁻¹`. -/
theorem norm_polar_le_of_fixed (hb : IsOrthoBasis Q b) {T : V ≃ₗ[F] V}
    (hT : T ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h : V ≃ₗ[F] V) {x y : V} (hx : T x = x)
    (hy : T y = y) (hxn : basisNorm b x ≤ 1) (hyn : basisNorm b y ≤ 1) :
    ‖polar Q (h x) y‖ ≤
      polarBound Q b * basisOpNorm b ((T * h * T⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) :=
  norm_polar_le_of_eigen hb hT h (α := 1) (β := 1) (by rw [one_smul]; exact hx)
    (by rw [one_smul]; exact hy) (by simp) hxn hyn

end Conj

end GSpinGGP
