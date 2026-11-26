/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Sanity.GL2SpecialK
import GSpinGGP.Sanity.GL2Weight
import GSpinGGP.TraceFormula.ThetaFBP

/-!
# `IsMx` at a proper Levi subgroup: the torus of `GSpin₃ ≅ GL₂`

At `gl2Data` (`W = 0`, `V` split of dimension `3`, `q = ac + b²` in the basis `z₋₁, z₀, ½ z₁` of
`gl2Basis`; `G = GL₁ × GSpin₃`) let `x = inr t` with `t = gl2Torus c`, which acts by `c, 1, c⁻¹`
(Beuzart-Plessis §5.2: `M(x)` is the centralizer of `A_{G_x}`).

* `gl2Torus_val`: in `C(V)`, `t = 1 + (c − 1) e` for the idempotent `e = ι(z₋₁) ι(½ z₁)`
  (`gl2E_mul_self`); so `(t − 1)(t − c) = 0` and the torus is commutative (`gl2Torus_commute`).
* **Regularity** (`gl2_torus_mem_regularSet`, `c ≠ 1`): `x` is semisimple (`(X − 1)(X − c)` is
  squarefree) and `𝔤_x` is abelian: on `gspin(V)` the skew maps commuting with `P(t)` are
  diagonal in `gl2Basis` (`gl2_soCent_diag`), so their lifts commute
  (`commute_of_adV_commute`); `C(W) = C(0)` is commutative.  `c = −1` is allowed (`diag(1, −1)` is
  regular in `GL₂`).
* **`gl2_isMx`**: `gl2Levi.IsMx x` for `c ≠ 1`.  `G_x(F) ⊆ M(F)` (`centG_le_M`) and
  `M(F) = A_M(F)` (`gl2_M_le_AMF`: an element of `M` acts by `e₀, 1, e₀⁻¹`, the middle eigenvalue
  being `1` since `det P = 1`, `gl2Eig_one`), so `A_M(F)\G_x(F)` is a point.
  `gl2_exists_special_isMx`: with `gl2GoodK_isSpecial` this is a special presentation of `M(x)`
  with `M ≠ G` (`gl2_M_ne_top`), the `∃` half of `IsBPThetaF` at `x`.
* **`gl2TopLevi_not_isMx`**: the datum with empty flags and weights `0` (`gl2TopLevi`, `M = G`)
  is not `M(x)`, for every `c`: there `A_M(F) = A_G(F)` acts trivially on `V`, while
  `|eigenvalue on ½ z₁|` is continuous on `G_x(F)`, constant on `A_G(F)`-cosets and unbounded on
  the torus `⊆ G_x(F)`; so `A_G(F)\G_x(F)` is not compact.  So `IsMx` rejects at least this Levi
  subgroup containing `x` that is not `M(x)`.

Nothing here uses an axiom or `sorry`.
-/

noncomputable section

open Module GSpinGGP.Sanity CliffordAlgebra

set_option linter.style.numericProjections false

namespace GSpinGGP.GGPData

/-- In a ring, `a² = 0` and `ba = 1 − ab` make `ab` idempotent. -/
theorem mul_self_of_swap {R : Type*} [Ring R] {a b : R} (h0 : a * a = 0) (h : b * a = 1 - a * b) :
    a * b * (a * b) = a * b := by
  calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
    _ = a * b := by rw [h, mul_sub, mul_one, sub_mul, ← mul_assoc a a, h0, zero_mul, zero_mul,
          sub_zero]

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝔾" => (gl2Data (F := F))
local notation "𝐟" => (gl2Basis (F := F))
local notation "𝕃" => (gl2Levi (F := F))

theorem gl2_Q_f0 : (𝔾).QV (𝐟 0) = 0 := by rw [gl2_QV_eq]; simp
theorem gl2_Q_f2 : (𝔾).QV (𝐟 2) = 0 := by rw [gl2_QV_eq]; simp
theorem gl2_polar_f2_f0 : QuadraticMap.polar (𝔾).QV (𝐟 2) (𝐟 0) = 1 := by rw [gl2_polar]; simp

/-- The idempotent `e = ι(z₋₁) ι(½ z₁)` of `C(V)`. -/
def gl2E : CliffordAlgebra (𝔾).QV := ι (𝔾).QV (𝐟 0) * ι (𝔾).QV (𝐟 2)

theorem gl2_swap : ι (𝔾).QV (𝐟 2) * ι (𝔾).QV (𝐟 0) = 1 - gl2E := by
  have h := ι_mul_ι_add_swap (Q := (𝔾).QV) (𝐟 2) (𝐟 0)
  rw [gl2_polar_f2_f0, map_one] at h
  rw [gl2E, ← h, add_sub_cancel_right]

theorem gl2_sq_f0 : ι (𝔾).QV (𝐟 0) * ι (𝔾).QV (𝐟 0) = 0 := by
  rw [ι_sq_scalar, gl2_Q_f0, RingHom.map_zero]

theorem gl2_sq_f2 : ι (𝔾).QV (𝐟 2) * ι (𝔾).QV (𝐟 2) = 0 := by
  rw [ι_sq_scalar, gl2_Q_f2, RingHom.map_zero]

theorem gl2E_mul_self : gl2E (F := F) * gl2E = gl2E :=
  mul_self_of_swap gl2_sq_f0 gl2_swap

theorem gl2Torus_val (c : Fˣ) :
    ((gl2Torus c : (CliffordAlgebra (𝔾).QV)ˣ) : CliffordAlgebra (𝔾).QV) =
      1 + ((c : F) - 1) • gl2E := by
  have h0 := gl2_sq_f0 (F := F)
  have h2 := gl2_sq_f2 (F := F)
  change ι (𝔾).QV (𝐟 0 + 𝐟 2) * ι (𝔾).QV (𝐟 0 + (c : F) • 𝐟 2) = _
  simp only [map_add, map_smul, add_mul, mul_add, mul_smul_comm, h0, h2, gl2_swap]
  rw [← gl2E]
  module


open Polynomial in
/-- `(X − 1)(X − c)` kills `gl2Torus c`, in `C(V)`. -/
theorem gl2Torus_aeval (c : Fˣ) :
    (((gl2Torus c : (CliffordAlgebra (𝔾).QV)ˣ) : CliffordAlgebra (𝔾).QV) - 1) *
      (((gl2Torus c : (CliffordAlgebra (𝔾).QV)ˣ) : CliffordAlgebra (𝔾).QV) -
        algebraMap F _ (c : F)) = 0 := by
  rw [gl2Torus_val, Algebra.algebraMap_eq_smul_one]
  have he := gl2E_mul_self (F := F)
  simp only [add_sub_cancel_left, sub_mul, mul_sub, mul_add, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one, he, smul_smul]
  module

theorem gl2_inr_val (y : GSpin (𝔾).QV) :
    ((((𝔾).inr y : ↥(𝔾).G) : (𝔾).ambientˣ) : (𝔾).ambient) =
      (1, ((y : (CliffordAlgebra (𝔾).QV)ˣ) : CliffordAlgebra (𝔾).QV)) := rfl

open Polynomial in
theorem gl2_isSS_torus {c : Fˣ} (hc : (c : F) ≠ 1) :
    IsSS F ((((𝔾).inr (gl2Torus c) : ↥(𝔾).G) : (𝔾).ambientˣ) : (𝔾).ambient) := by
  have hcop : IsCoprime (X - C (1 : F)) (X - C (c : F)) :=
    isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hc.symm).isUnit
  refine isSS_of_aeval_eq_zero (p := (X - C 1) * (X - C (c : F)))
    (separable_X_sub_C.mul separable_X_sub_C hcop).squarefree ?_
  rw [gl2_inr_val]
  simp only [map_mul, map_sub, aeval_X, aeval_C, map_one]
  refine Prod.ext ?_ ?_
  · simp
  · simpa [Prod.algebraMap_apply] using gl2Torus_aeval c


/-- **The skew endomorphisms commuting with `P(gl2Torus c)`, `c ≠ 1`, are diagonal** in `𝐟`: on
the `1`-eigenline `⟨z₀⟩` they vanish (commuting kills the `z₋₁`, `z₁` components, skewness the
`z₀` one), and skewness against `z₋₁`, `z₀`, `z₁` makes them diagonal on `⟨z₋₁, z₁⟩`. -/
theorem gl2_soCent_diag {c : Fˣ} (hc : (c : F) ≠ 1) {M : Module.End F (𝔾).V}
    (hM : M ∈ soCent (𝔾).QV (specP (𝔾).QV (gl2Torus c) : Module.End F (𝔾).V)) (i : Fin 3) :
    M (𝐟 i) = 𝐟.repr (M (𝐟 i)) i • 𝐟 i := by
  obtain ⟨hskew, hcomm⟩ := mem_soCent.mp hM
  have hpol : ∀ u w, QuadraticMap.polar (𝔾).QV (M u) w = -QuadraticMap.polar (𝔾).QV u (M w) := by
    intro u w
    have h := hskew u w
    simp only [QuadraticMap.associated_apply] at h
    have h2 : (⅟2 : F) ≠ 0 := by simp
    have := mul_left_cancel₀ h2 (h.trans (neg_mul_eq_mul_neg _ _))
    simpa [QuadraticMap.polar] using this
  -- commuting on `z₀`
  have e : specP (𝔾).QV (gl2Torus c) (M (𝐟 1)) = M (𝐟 1) := by
    have := LinearMap.congr_fun hcomm (𝐟 1)
    simp only [mul_apply_eq_comp, LinearEquiv.coe_coe, gl2_torus_apply] at this
    simpa using this.symm
  have h1 : ∀ j, (![(c : F), 1, (c : F)⁻¹] : Fin 3 → F) j * 𝐟.repr (M (𝐟 1)) j =
      𝐟.repr (M (𝐟 1)) j := fun j => by rw [← gl2_torus_repr, e]
  have hci : (c : F)⁻¹ ≠ 1 := by rwa [ne_eq, inv_eq_one]
  have r10 : 𝐟.repr (M (𝐟 1)) 0 = 0 := (mul_left_eq_self₀.mp (by simpa using h1 0)).resolve_left hc
  have r12 : 𝐟.repr (M (𝐟 1)) 2 = 0 := (mul_left_eq_self₀.mp (by simpa using h1 2)).resolve_left hci
  have p := fun a b => hpol (𝐟 a) (𝐟 b)
  simp only [gl2_polar, Basis.repr_self, Finsupp.single_apply] at p
  have p11 := p 1 1
  have p00 := p 0 0
  have p01 := p 0 1
  have p22 := p 2 2
  have p21 := p 2 1
  simp at p11 p00 p01 p22 p21
  rw [r12, neg_zero] at p01
  rw [r10, neg_zero] at p21
  have r11 : 𝐟.repr (M (𝐟 1)) 1 = 0 := by
    have := CharZero.eq_neg_self_iff.mp p11; simpa using this
  have r02 := CharZero.eq_neg_self_iff.mp p00
  have r20 := CharZero.eq_neg_self_iff.mp p22
  have r01 : 𝐟.repr (M (𝐟 0)) 1 = 0 := by simpa using p01
  have r21 : 𝐟.repr (M (𝐟 2)) 1 = 0 := by simpa using p21
  clear p p11 p00 p01 p22 p21 h1 e hpol hskew hcomm hM
  refine 𝐟.ext_elem fun j => ?_
  rw [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [r10, r12, r11, r02, r20, r01, r21]


/-- Two endomorphisms that are diagonal in `𝐟` commute. -/
theorem gl2_diag_commute {M₁ M₂ : Module.End F (𝔾).V}
    (h₁ : ∀ i, ∃ a : F, M₁ (𝐟 i) = a • 𝐟 i) (h₂ : ∀ i, ∃ b : F, M₂ (𝐟 i) = b • 𝐟 i) :
    M₁ * M₂ = M₂ * M₁ :=
  𝐟.ext fun i => by
    obtain ⟨a, ha⟩ := h₁ i
    obtain ⟨b, hb⟩ := h₂ i
    rw [mul_apply_eq_comp, mul_apply_eq_comp, hb, map_smul, ha, map_smul, hb, smul_smul,
      smul_smul, mul_comm b a]

/-- **`gspin(V)_t` is abelian** for `t = gl2Torus c`, `c ≠ 1`. -/
theorem gl2_isLieAbelian_torus {c : Fˣ} (hc : (c : F) ≠ 1) :
    IsLieAbelian (lieCentralizer (gspin (𝔾).QV)
      ((gl2Torus c : (CliffordAlgebra (𝔾).QV)ˣ) : CliffordAlgebra (𝔾).QV)) := by
  rw [isLieAbelian_iff_forall_commute]
  intro X₁ h₁ X₂ h₂
  obtain ⟨hX₁, hx₁⟩ := mem_lieCentralizer.mp h₁
  obtain ⟨hX₂, hx₂⟩ := mem_lieCentralizer.mp h₂
  have hM : ∀ {X}, X ∈ gspin (𝔾).QV →
      ((gl2Torus c : (CliffordAlgebra (𝔾).QV)ˣ) : CliffordAlgebra (𝔾).QV) * X =
        X * ((gl2Torus c : (CliffordAlgebra (𝔾).QV)ˣ) : CliffordAlgebra (𝔾).QV) →
      adV (𝔾).QV X ∈ soCent (𝔾).QV (specP (𝔾).QV (gl2Torus c) : Module.End F (𝔾).V) :=
    fun hX hxX => mem_soCent.2 ⟨bform_adV hX, ((commute_iff_adV (𝔾).nondeg_QV _ hX).mp hxX).symm⟩
  exact commute_of_adV_commute (𝔾).nondeg_QV hX₁ hX₂
    (gl2_diag_commute (fun i => ⟨_, gl2_soCent_diag hc (hM hX₁ hx₁) i⟩)
      (fun i => ⟨_, gl2_soCent_diag hc (hM hX₂ hx₂) i⟩))

/-- **`inr (gl2Torus c)` is regular semisimple** for `c ≠ 1`. -/
theorem gl2_torus_mem_regularSet {c : Fˣ} (hc : (c : F) ≠ 1) :
    (𝔾).inr (gl2Torus c) ∈ regularSet (𝔾).G (𝔾).lie := by
  refine ⟨gl2_isSS_torus hc, ?_⟩
  rw [isLieAbelian_iff_forall_commute]
  intro X₁ h₁ X₂ h₂
  rw [mem_lieCentralizer_prod (𝔤₁ := gspin (𝔾).QW) (𝔤₂ := gspin (𝔾).QV) (fun _ => Iff.rfl),
    gl2_inr_val] at h₁ h₂
  have hV := (isLieAbelian_iff_forall_commute.mp (gl2_isLieAbelian_torus hc)) _ h₁.2 _ h₂.2
  exact Prod.ext (toyData_cliffW_comm (K := F) X₁.1 X₂.1).eq hV


/-- **The middle eigenvalue is `1`** on the Levi subgroup: `det P(y) = 1` and the outer
eigenvalues are inverse (`gl2Eig_zero_mul_two`). -/
theorem gl2Eig_one {y : GSpin (𝔾).QV} (hy : y ∈ flagLevi (Q := (𝔾).QV) (𝔾).stdBasis (𝔾).stdWt) :
    gl2Eig y 1 = 1 := by
  have hdiag : LinearMap.toMatrix 𝐟 𝐟 (specP (𝔾).QV y : (𝔾).V →ₗ[F] (𝔾).V) =
      Matrix.diagonal (gl2Eig y) := by
    ext i j
    rw [LinearMap.toMatrix_apply, LinearEquiv.coe_coe, gl2_levi_apply hy, map_smul,
      Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, Matrix.diagonal_apply,
      smul_eq_mul]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]
  have hdet := det_specP y
  rw [← LinearMap.det_toMatrix 𝐟, hdiag, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have h02 := gl2Eig_zero_mul_two hy
  linear_combination hdet - gl2Eig y 1 * h02

/-- An element of the Levi subgroup of `⟨z₁⟩` acts by `e₀, 1, e₀⁻¹`, so lies in the split centre. -/
theorem gl2_levi_mem_wtScalar {y : GSpin (𝔾).QV}
    (hy : y ∈ flagLevi (Q := (𝔾).QV) (𝔾).stdBasis (𝔾).stdWt) :
    y ∈ wtScalar (𝔾).QV (𝔾).stdBasis (𝔾).stdWt := by
  refine ⟨fun w => if w = -1 then gl2Eig y 0 else if w = 1 then gl2Eig y 2 else 1, by simp,
    fun j => ?_⟩
  rcases j with j | j
  · exact j.elim0
  rw [flagLevi_apply_basis_eq_smul gl2_stdWt_injective hy]
  change gl2Eig y j • _ = _
  fin_cases j
  · simp [stdWt]
  · simp [stdWt, gl2Eig_one hy]
  · simp [stdWt]

/-- **`M(F) = A_M(F)` for the torus `gl2Levi`**: an element of `M` acts by `e₀, 1, e₀⁻¹`. -/
theorem gl2_M_le_AMF : (𝕃).M ≤ (𝕃).AMF := fun _ hg =>
  ((𝕃).mem_AMF_iff).2 ⟨⟨1, rfl, fun j => j.elim0⟩, gl2_levi_mem_wtScalar hg.2⟩


/-- If `G_x(F) ⊆ A_M(F)`, the space `A_M(F)\G_x(F)` is a point. -/
theorem subsingleton_cosetSpace_AGx {d : GGPData F} (L : d.ReducedLeviDatum) {x : ↥d.G}
    (h : d.centG x ≤ L.AMF) : Subsingleton (CosetSpace (L.AGx x).subtype) := by
  refine ⟨fun a b => ?_⟩
  induction a using CosetSpace.ind with | h g => ?_
  induction b using CosetSpace.ind with | h k => ?_
  rw [CosetSpace.mk_eq_mk_iff, CosetSpace.rel_iff]
  exact ⟨⟨k * g⁻¹, ReducedLeviDatum.mem_AGx.2 (h (k * g⁻¹).2)⟩, by simp⟩

/-- **`G_x(F) ⊆ A_M(F)`** at `x = inr (gl2Torus c)`, `c ≠ 1`: `G_x(F) ⊆ M(F)` (`centG_le_M`) and
`M(F) = A_M(F)` (`gl2_M_le_AMF`). -/
theorem gl2_centG_le_AMF {c : Fˣ} (hc : (c : F) ≠ 1) :
    (𝔾).centG ((𝔾).inr (gl2Torus c)) ≤ (𝕃).AMF :=
  (centG_le_M (𝕃).toFlagLeviDatum (gl2_torus_mem_regularSet hc) (gl2_torus_mem_M c)).trans
    gl2_M_le_AMF

/-- **`L.M = M(x)` at a proper Levi subgroup**: for `c ≠ 1`, the torus datum `gl2Levi` is `M(x)`
of `x = inr (gl2Torus c)`; `A_M(F)\G_x(F)` is a point. -/
theorem gl2_isMx {c : Fˣ} (hc : (c : F) ≠ 1) : (𝕃).IsMx ((𝔾).inr (gl2Torus c)) where
  regular := gl2_torus_mem_regularSet hc
  mem := gl2_torus_mem_M c
  compact := by
    have := subsingleton_cosetSpace_AGx (𝕃) (gl2_centG_le_AMF hc)
    infer_instance

/-- **`M ≠ G`** for the torus datum: `n̄(1)⁻¹` moves `½ z₁` off its line. -/
theorem gl2_M_ne_top : (𝕃).M ≠ ⊤ := by
  intro h
  have hm : (gl2Nbar (1 : F))⁻¹ ∈ (𝕃).M := h ▸ trivial
  have key := gl2_nbar_inv_two (1 : F)
  rw [← map_inv, gl2_levi_apply hm.2 2] at key
  have := congrArg (fun x => 𝐟.repr x 1) key
  simp at this

/-- **The `∃` half of `IsBPThetaF` at a proper Levi subgroup**: a special presentation of `M(x)`
with `M ≠ G`. -/
theorem gl2_exists_special_isMx {c : Fˣ} (hc : (c : F) ≠ 1) :
    ∃ (L : (𝔾).ReducedLeviDatum) (K : (𝔾).GoodK L.toFlagLeviDatum),
      L.IsMx ((𝔾).inr (gl2Torus c)) ∧ K.IsSpecial ∧ L.M ≠ ⊤ :=
  ⟨𝕃, gl2GoodK, gl2_isMx hc, gl2GoodK_isSpecial, gl2_M_ne_top⟩


/-! ## (b) The datum with `M = G` is not `M(x)` -/

/-- Elements of the torus commute: `gl2Torus c = 1 + (c − 1) e` (`gl2Torus_val`). -/
theorem gl2Torus_commute (c c' : Fˣ) : Commute (gl2Torus c) (gl2Torus c') := by
  have hA : ∀ a : F, Commute (1 + a • gl2E (F := F)) gl2E := fun a =>
    (Commute.one_left _).add_left ((Commute.refl _).smul_left a)
  have h : Commute (1 + ((c : F) - 1) • gl2E (F := F)) (1 + ((c' : F) - 1) • gl2E) :=
    (Commute.one_right _).add_right ((hA _).smul_right _)
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul, gl2Torus_val]
  exact h.eq

/-- The torus lies in `G_x(F)`. -/
theorem gl2_torus_mem_centG (c c' : Fˣ) :
    (𝔾).inr (gl2Torus c') ∈ (𝔾).centG ((𝔾).inr (gl2Torus c)) :=
  Subgroup.mem_centralizer_singleton_iff.2 ((gl2Torus_commute c' c).map (𝔾).inr).eq

/-- A grading with all weights `0` (length `0`). -/
theorem isWtGrading_zero {V ι : Type*} [AddCommGroup V] [Module F V] [Fintype ι]
    (Q : QuadraticForm F V) (b : Basis ι F V) : IsWtGrading Q b (0 : ι → ℤ) 0 where
  orth _ _ h := (h (by simp)).elim
  sum_wt := by simp
  wt_le _ := le_rfl
  exists_wt_eq _ h1 h2 := absurd (h1.trans h2) (by norm_num)

theorem gl2_wtSpan_zero :
    wtSpan (𝔾).stdBasis (0 : Fin (𝔾).m ⊕ Fin (2 * (𝔾).r + 1) → ℤ) 0 = ⊤ := by
  rw [wtSpan, show {j | (0 : (Fin (𝔾).m ⊕ Fin (2 * (𝔾).r + 1)) → ℤ) j = 0} = Set.univ from
    Set.eq_univ_of_forall fun _ => rfl, Set.image_univ, Basis.span_eq]

/-- **The datum with `M = G`** at `gl2Data`: empty flags, all weights `0`. -/
def gl2TopLevi : (𝔾).ReducedLeviDatum :=
  ReducedLeviDatum.ofGrading (Pi.basisFun F (Fin 0)) 0 (isWtGrading_zero _ _) (𝔾).stdBasis 0
    (isWtGrading_zero _ _)
    (not_isHypPlane_comp_of_finrank_le _ _ (by rw [Module.finrank_fin_fun]; simp))
    (fun hp => by
      have h2 := hp.1
      rw [gl2_wtSpan_zero, finrank_top, gl2Data_finrank_V] at h2
      omega)

theorem gl2TopLevi_M : (gl2TopLevi (F := F)).M = ⊤ :=
  ReducedLeviDatum.M_eq_top_of_len_eq_zero _ rfl rfl

/-- On `A_G(F)` (weights `0`), `P(a_V) = 1`. -/
theorem gl2TopLevi_specP_eq_one {a : ↥(𝔾).G} (ha : a ∈ (gl2TopLevi (F := F)).AMF) (v : (𝔾).V) :
    specP (𝔾).QV ((𝔾).snd a) v = v := by
  obtain ⟨-, t, ht0, ht⟩ := ((gl2TopLevi (F := F)).mem_AMF_iff).1 ha
  have h : ∀ j, specP (𝔾).QV ((𝔾).snd a) ((𝔾).stdBasis j) = (𝔾).stdBasis j := fun j => by
    rw [show (𝔾).stdBasis j = (gl2TopLevi (F := F)).bV j from rfl, ht j]
    change t 0 • _ = _
    rw [ht0, one_smul]
  have := (𝔾).stdBasis.ext (f₁ := (specP (𝔾).QV ((𝔾).snd a) : (𝔾).V →ₗ[F] (𝔾).V))
    (f₂ := LinearMap.id) fun j => h j
  exact LinearMap.congr_fun this v

/-- **The datum with `M = G` is not `M(x)`** at `x = inr (gl2Torus c)`: `|e₁|`, the absolute value
of the eigenvalue on `½ z₁`, is continuous on `G_x(F)`, constant on `A_G(F)`-cosets
(`P = 1` on `A_G(F)`), and unbounded on the torus `⊆ G_x(F)`, so `A_G(F)\G_x(F)` is not
compact. -/
theorem gl2TopLevi_not_isMx (c : Fˣ) : ¬ (gl2TopLevi (F := F)).IsMx ((𝔾).inr (gl2Torus c)) := by
  intro h
  have hc := h.compact
  set x := (𝔾).inr (gl2Torus c)
  set φ : ↥((𝔾).centG x) → ℝ := fun g => ‖𝐟.repr (specP (𝔾).QV ((𝔾).snd (g : ↥(𝔾).G)) (𝐟 2)) 2‖
  have hφ : Continuous φ :=
    continuous_norm.comp (((𝐟.coord 2).continuous_of_finiteDimensional).comp
      (continuous_specP_apply ((𝔾).continuous_snd.comp continuous_subtypeVal) _))
  have hrel : ∀ g k : ↥((𝔾).centG x),
      QuotientGroup.rightRel ((gl2TopLevi (F := F)).AGx x).subtype.range g k → φ g = φ k := by
    intro g k hgk
    obtain ⟨a, rfl⟩ := (CosetSpace.rel_iff _ g k).1 hgk
    have hk : (((((gl2TopLevi (F := F)).AGx x).subtype a * g : ↥((𝔾).centG x)) : ↥(𝔾).G)) =
        ((a : ↥((𝔾).centG x)) : ↥(𝔾).G) * g := rfl
    simp only [φ]
    rw [hk, (𝔾).snd.map_mul, specP_mul_apply,
      gl2TopLevi_specP_eq_one (ReducedLeviDatum.mem_AGx.1 a.2)]
  let ψ : CosetSpace ((gl2TopLevi (F := F)).AGx x).subtype → ℝ :=
    Quotient.lift (s := QuotientGroup.rightRel ((gl2TopLevi (F := F)).AGx x).subtype.range) φ hrel
  have hψ : Continuous ψ := CosetSpace.continuous_of_comp_mk _ hφ
  obtain ⟨B, hB⟩ := (isCompact_range hψ).bddAbove
  obtain ⟨a, ha⟩ := NormedField.exists_lt_norm F B
  have ha0 : a ≠ 0 := by
    rintro rfl
    have := hB ⟨CosetSpace.mk _ 1, rfl⟩
    have h0 : 0 ≤ ψ (CosetSpace.mk _ 1) := norm_nonneg _
    simp only [norm_zero] at ha
    linarith
  have hmem := gl2_torus_mem_centG c (Units.mk0 a ha0)⁻¹
  have := hB ⟨CosetSpace.mk _ ⟨_, hmem⟩, rfl⟩
  change φ ⟨_, hmem⟩ ≤ B at this
  simp only [φ, snd_inr, gl2_torus_apply, map_smul, Basis.repr_self] at this
  simp at this
  linarith

end GSpinGGP.GGPData