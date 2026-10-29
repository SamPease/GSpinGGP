/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Basic

/-!
# The spinor norms and the Harish-Chandra map `H_G`

The Harish-Chandra map `H_G : G(F) → Hom(X^*(G)_F, ℝ)` of
Thesis §2.1, in the concrete form needed for the cutoff `κ` along `A_G(F)`
(`exists_isAGCutoff`, `ThetaF.lean`).

For each factor `U ∈ {W, V}` we use two `F`-rational characters `χ₁, χ₂ : GSpin(U) → G_m`
(`gspinChar₁`, `gspinChar₂`):
* if `U` is not a hyperbolic plane, `χ₁(g) = det(L_g | C(U))` (left multiplication on the
  Clifford algebra; it equals `N(g)^{2^{n-1}}` for the spinor norm `N(g) = g ḡ`, `n = dim U ≥ 1`,
  and is used instead of `N` because it is visibly a continuous homomorphism) and `χ₂ = 1`;
* if `U` is a hyperbolic plane, `GSpin(U) ⊆ C⁺(U) ≅ F × F` and `χ₁, χ₂` are the two coordinates:
  `g ε₊ = χ₁(g) ε₊`, `g ε₋ = χ₂(g) ε₋` for the idempotents `ε± = (1 ± r⁻¹ω)/2` of `C⁺(U)`
  (`ω = e₀e₁`, `ω² = r²`).  Both coordinates are needed: `A_{GSpin(U)} = GSpin(U)` is then a
  two-dimensional split torus.

`hcMap Q g = (log‖χ₁ g‖, log‖χ₂ g‖)` and `H_G(g) = (hcMap(g_W), hcMap(g_V))` (`hcG`).  Proved:
* `hcG` is a homomorphism to a commutative group (so conjugation invariant) and locally constant
  (`isLocallyConstant_hcG`);
* it is trivial on unipotent radicals `whittU` (`hcG_eq_one_of_mem_whittU`: powers of a unipotent
  element stay in a compact set, and a continuous character is then of norm `1`);
* `A_G(F) ∩ ker H_G` is compact (`isCompact_AG_inter_ker_hcG`).

Only these properties are used; any positive multiple of the thesis's `H_G` (e.g. with the spinor
norm itself) would do equally well.
-/

noncomputable section

open MeasureTheory Topology Filter CliffordAlgebra
open scoped Pointwise

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-! ## `log ‖·‖` on `F^×` -/

/-- `a ↦ log ‖a‖`, a homomorphism `F^× → ℝ` (written multiplicatively). -/
def logAbs : Fˣ →* Multiplicative ℝ where
  toFun a := Multiplicative.ofAdd (Real.log ‖(a : F)‖)
  map_one' := by simp
  map_mul' a b := by
    rw [Units.val_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 a.ne_zero)
      (norm_ne_zero_iff.2 b.ne_zero), ofAdd_add]

theorem logAbs_apply (a : Fˣ) : logAbs a = Multiplicative.ofAdd (Real.log ‖(a : F)‖) := rfl

theorem logAbs_eq_one_iff (a : Fˣ) : logAbs a = 1 ↔ ‖(a : F)‖ = 1 := by
  rw [logAbs_apply, ← ofAdd_zero, Multiplicative.ofAdd.apply_eq_iff_eq, Real.log_eq_zero]
  have h0 : ‖(a : F)‖ ≠ 0 := norm_ne_zero_iff.2 a.ne_zero
  have hpos : 0 ≤ ‖(a : F)‖ := norm_nonneg _
  constructor
  · rintro (h | h | h)
    · exact absurd h h0
    · exact h
    · linarith
  · exact fun h => Or.inr (Or.inl h)

/-- On a nonarchimedean field the norm is locally constant on `F ∖ {0}`, so `x ↦ log ‖f x‖` is
locally constant for continuous nonvanishing `f`. -/
theorem isLocallyConstant_norm_comp {X : Type*} [TopologicalSpace X] {f : X → F}
    (hf : Continuous f) (h0 : ∀ x, f x ≠ 0) : IsLocallyConstant (fun x => ‖f x‖) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hpos : 0 < ‖f x‖ := norm_pos_iff.2 (h0 x)
  have : ∀ᶠ y in 𝓝 x, dist (f y) (f x) < ‖f x‖ :=
    (hf.continuousAt.eventually (Metric.ball_mem_nhds (f x) hpos))
  filter_upwards [this] with y hy
  rw [dist_eq_norm] at hy
  have hne : ‖f y - f x‖ ≠ ‖f x‖ := hy.ne
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [sub_add_cancel] at this
  rw [this, max_eq_right hy.le]

/-- If all powers `a^k` (`k ∈ ℤ`) of `a ∈ F^×` have norms in a compact subset of `(0, ∞)`, i.e.
are bounded above and below, then `‖a‖ = 1`. -/
theorem norm_eq_one_of_zpow_bounded {a : F} (ha : a ≠ 0) {ε R : ℝ} (_hε : 0 < ε)
    (h : ∀ k : ℤ, ε ≤ ‖a ^ k‖ ∧ ‖a ^ k‖ ≤ R) : ‖a‖ = 1 := by
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha
  rcases lt_trichotomy ‖a‖ 1 with hlt | heq | hgt
  · exfalso
    have ht : 1 < ‖a‖⁻¹ := one_lt_inv_iff₀.2 ⟨hpos, hlt⟩
    obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt ht).eventually_gt_atTop R |>.exists
    have := (h (-(n : ℤ))).2
    rw [zpow_neg, zpow_natCast, norm_inv, norm_pow, ← inv_pow] at this
    linarith
  · exact heq
  · exfalso
    obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop R |>.exists
    have := (h (n : ℤ)).2
    rw [zpow_natCast, norm_pow] at this
    linarith

/-- A continuous character `χ : X → F^×` (continuous as an `F`-valued map) of a topological group
has norm `1` at every element whose powers lie in a compact set. -/
theorem norm_char_eq_one_of_zpow_mem_compact {X : Type*} [Group X] [TopologicalSpace X]
    (χ : X →* Fˣ) (hχ : Continuous (fun x => ((χ x : Fˣ) : F))) {u : X} {C : Set X}
    (hC : IsCompact C) (hu : ∀ k : ℤ, u ^ k ∈ C) : ‖((χ u : Fˣ) : F)‖ = 1 := by
  have hcont : ContinuousOn (fun x => ‖((χ x : Fˣ) : F)‖) C := (continuous_norm.comp hχ).continuousOn
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact absurd (hu 0) (Set.notMem_empty _)
  obtain ⟨x₁, hx₁, hmin⟩ := hC.exists_isMinOn hne hcont
  obtain ⟨x₂, hx₂, hmax⟩ := hC.exists_isMaxOn hne hcont
  refine norm_eq_one_of_zpow_bounded (χ u).ne_zero (R := ‖((χ x₂ : Fˣ) : F)‖)
    (norm_pos_iff.2 (χ x₁).ne_zero) fun k => ?_
  have e : ((χ u : Fˣ) : F) ^ k = ((χ (u ^ k) : Fˣ) : F) := by
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rw [e]
  exact ⟨hmin (hu k), hmax (hu k)⟩

/-! ## Eigen-characters on a stable line of `C(V)` -/

section Eigen

variable {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]

/-- Elements of `GSpin(V)` acting on a nonzero `e ∈ C(V)` by left multiplication with a scalar
eigenvalue give a character (used for the two coordinates of a hyperbolic plane). -/
def eigenVal (Q : QuadraticForm F V) (e : CliffordAlgebra Q)
    (he : ∀ g : GSpin Q, ∃ a : F, ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * e = a • e)
    (g : GSpin Q) : F :=
  (he g).choose

theorem eigenVal_spec (Q : QuadraticForm F V) (e : CliffordAlgebra Q)
    (he : ∀ g : GSpin Q, ∃ a : F, ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * e = a • e)
    (g : GSpin Q) :
    ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * e = eigenVal Q e he g • e :=
  (he g).choose_spec

theorem eigenVal_unique (Q : QuadraticForm F V) {e : CliffordAlgebra Q} (he0 : e ≠ 0)
    (he : ∀ g : GSpin Q, ∃ a : F, ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * e = a • e)
    {g : GSpin Q} {a : F} (ha : ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * e = a • e) :
    eigenVal Q e he g = a :=
  smul_left_injective F he0 ((eigenVal_spec Q e he g).symm.trans ha)

theorem eigenVal_ne_zero (Q : QuadraticForm F V) {e : CliffordAlgebra Q} (he0 : e ≠ 0)
    (he : ∀ g : GSpin Q, ∃ a : F, ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * e = a • e)
    (g : GSpin Q) : eigenVal Q e he g ≠ 0 := by
  intro h0
  apply he0
  have h := eigenVal_spec Q e he g
  rw [h0, zero_smul] at h
  calc e = ((((g : (CliffordAlgebra Q)ˣ))⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * e) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = 0 := by rw [h, mul_zero]

/-- The eigen-character `GSpin(V) → F^×` on a stable line `F e`. -/
def eigenChar (Q : QuadraticForm F V) {e : CliffordAlgebra Q} (he0 : e ≠ 0)
    (he : ∀ g : GSpin Q, ∃ a : F, ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * e = a • e) :
    GSpin Q →* Fˣ where
  toFun g := Units.mk0 (eigenVal Q e he g) (eigenVal_ne_zero Q he0 he g)
  map_one' := by
    ext
    simp only [Units.val_mk0, Units.val_one]
    exact eigenVal_unique Q he0 he (by simp)
  map_mul' g h := by
    ext
    simp only [Units.val_mk0, Units.val_mul]
    refine eigenVal_unique Q he0 he ?_
    rw [Subgroup.coe_mul, Units.val_mul, mul_assoc, eigenVal_spec Q e he h, mul_smul_comm,
      eigenVal_spec Q e he g, smul_smul, mul_comm]

theorem eigenChar_apply (Q : QuadraticForm F V) {e : CliffordAlgebra Q} (he0 : e ≠ 0)
    (he : ∀ g : GSpin Q, ∃ a : F, ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * e = a • e)
    (g : GSpin Q) :
    ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * e = ((eigenChar Q he0 he g : Fˣ) : F) • e :=
  eigenVal_spec Q e he g

theorem continuous_eigenChar (Q : QuadraticForm F V) {e : CliffordAlgebra Q} (he0 : e ≠ 0)
    (he : ∀ g : GSpin Q, ∃ a : F, ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * e = a • e) :
    Continuous (fun g => ((eigenChar Q he0 he g : Fˣ) : F)) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual F (CliffordAlgebra Q), φ e ≠ 0 := by
    by_contra h
    push Not at h
    exact he0 ((Module.forall_dual_apply_eq_zero_iff F e).1 h)
  set ℓ : CliffordAlgebra Q →ₗ[F] F := (φ e)⁻¹ • φ
  have hℓ : ℓ e = 1 := by simp [ℓ, inv_mul_cancel₀ hφ]
  have key : (fun g => ((eigenChar Q he0 he g : Fˣ) : F)) =
      fun g : GSpin Q => ℓ (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * e) := by
    funext g
    rw [eigenChar_apply, map_smul, hℓ, smul_eq_mul, mul_one]
  rw [key]
  exact (IsModuleTopology.continuous_of_linearMap ℓ).comp
    ((Units.continuous_val.comp continuous_subtype_val).mul continuous_const)

end Eigen

/-! ## The hyperbolic plane -/

section Plane

/-- The two-dimensional even Clifford algebra of a hyperbolic plane is split: with an orthogonal
basis `e₀, e₁`, `ω = e₀e₁` has `ω² = -q(e₀)q(e₁) = r²` for some `r ≠ 0`. -/
theorem exists_sq_eq_of_isHypPlane {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    {Q : QuadraticForm F V} (hQ : IsHypPlane Q) (e : Module.Basis (Fin 2) F V)
    (he : ∀ i j, i ≠ j → bform Q (e i) (e j) = 0) :
    ∃ r : F, r ≠ 0 ∧ r ^ 2 = -(Q (e 0) * Q (e 1)) := by
  obtain ⟨-, hnd, hw⟩ := hQ
  -- an isotropic line
  have hbdd : BddAbove {n | ∃ U : Submodule F V, IsTotallyIsotropic Q U ∧ Module.finrank F U = n} :=
    ⟨Module.finrank F V, fun n ⟨U, _, hU⟩ => hU ▸ Submodule.finrank_le U⟩
  have hne : {n | ∃ U : Submodule F V, IsTotallyIsotropic Q U ∧ Module.finrank F U = n}.Nonempty :=
    ⟨0, ⊥, fun u hu => by rw [(Submodule.mem_bot F).mp hu, map_zero], finrank_bot F V⟩
  obtain ⟨U, hiso, hU⟩ := Nat.sSup_mem hne hbdd
  have hU1 : Module.finrank F U = 1 := by rw [hU]; exact hw
  have hUne : U ≠ ⊥ := by
    rintro rfl; rw [finrank_bot] at hU1; exact zero_ne_one hU1
  obtain ⟨v, hvU, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  have hQv : Q v = 0 := hiso v hvU
  -- `q(e_i) ≠ 0`
  have hb : ∀ i, bform Q (e i) (e i) = Q (e i) := fun i => QuadraticMap.associated_eq_self_apply F Q _
  have hQe : ∀ i, Q (e i) ≠ 0 := by
    intro i hi
    have hrad : ∀ y, bform Q (e i) y = 0 := by
      intro y
      rw [← e.sum_repr y, Fin.sum_univ_two, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue] at hi ⊢
        rw [hb, hi, he 0 1 (by decide)]; ring
      · simp only [Fin.mk_one, Fin.isValue] at hi ⊢
        rw [hb, hi, he 1 0 (by decide)]; ring
    exact e.ne_zero i (hnd.1 _ hrad)
  set x := e.repr v 0
  set y := e.repr v 1
  have hv : v = x • e 0 + y • e 1 := by
    rw [← e.sum_repr v, Fin.sum_univ_two]
  have hQxy : x ^ 2 * Q (e 0) + y ^ 2 * Q (e 1) = 0 := by
    have : Q (x • e 0 + y • e 1) = 0 := hv ▸ hQv
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right] at this
    have hpol : QuadraticMap.polar Q (e 0) (e 1) = 0 := by
      rw [polar_eq_two_mul_bform, he 0 1 (by decide), mul_zero]
    rw [hpol] at this
    simpa [smul_eq_mul, pow_two, mul_comm, mul_assoc, mul_left_comm] using this
  have hy : y ≠ 0 := by
    intro hy0
    have hx0 : x = 0 := by
      have : x ^ 2 * Q (e 0) = 0 := by simpa [hy0] using hQxy
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        ((mul_eq_zero.mp this).resolve_right (hQe 0))
    exact hv0 (by rw [hv, hx0, hy0, zero_smul, zero_smul, add_zero])
  have hx : x ≠ 0 := by
    intro hx0
    have : y ^ 2 * Q (e 1) = 0 := by simpa [hx0] using hQxy
    exact hy (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      ((mul_eq_zero.mp this).resolve_right (hQe 1)))
  refine ⟨x * Q (e 0) / y, div_ne_zero (mul_ne_zero hx (hQe 0)) hy, ?_⟩
  have hQ1 : Q (e 1) = -(x ^ 2 * Q (e 0)) / y ^ 2 := by
    field_simp
    linear_combination hQxy
  rw [hQ1]
  field_simp


variable {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]

open CliffordAlgebra in
/-- **The two idempotents of `C⁺(U)` for a hyperbolic plane `U`** (`ε₊ = (1 + r⁻¹ω)/2`,
`ε₋ = 1 − ε₊`): both are nonzero and every `g ∈ GSpin(U) ⊆ C⁺(U) = F ⊕ Fω` acts on each by a
scalar (`ωε± = ±r ε±`). -/
theorem exists_planeIdempotent {Q : QuadraticForm F V} (hQ : IsHypPlane Q) :
    ∃ ε : CliffordAlgebra Q, ε ≠ 0 ∧ 1 - ε ≠ 0 ∧
      (∀ g : GSpin Q, ∃ a : F, ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ε = a • ε) ∧
      (∀ g : GSpin Q, ∃ a : F,
        ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * (1 - ε) = a • (1 - ε)) := by
  obtain ⟨e, he⟩ := exists_orthogonal_basis_fin_two Q hQ.1
  obtain ⟨r, hr0, hr⟩ := exists_sq_eq_of_isHypPlane hQ e he
  set ω : CliffordAlgebra Q := ι Q (e 0) * ι Q (e 1) with hω
  have h10 : ι Q (e 1) * ι Q (e 0) = -ω := by
    have h1 := ι_mul_ι_add_swap (Q := Q) (e 1) (e 0)
    have hb : bform Q (e 1) (e 0) = 0 := he 1 0 (by decide)
    rw [polar_eq_two_mul_bform, hb, mul_zero, (algebraMap F (CliffordAlgebra Q)).map_zero] at h1
    exact eq_neg_of_add_eq_zero_left h1
  have hsq : ∀ i, ι Q (e i) * ι Q (e i) = Q (e i) • (1 : CliffordAlgebra Q) := fun i => by
    rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one]
  have hωω : ω * ω = (r ^ 2) • (1 : CliffordAlgebra Q) := by
    calc ω * ω = ι Q (e 0) * (ι Q (e 1) * ι Q (e 0)) * ι Q (e 1) := by
          simp only [ω, mul_assoc]
      _ = -((ι Q (e 0) * ι Q (e 0)) * (ι Q (e 1) * ι Q (e 1))) := by
          rw [h10]; simp only [ω, mul_neg, neg_mul, mul_assoc]
      _ = _ := by rw [hsq, hsq, smul_mul_smul_comm, one_mul, hr, neg_smul]
  -- `ω` is not a scalar
  have hωne : ∀ c : F, c ≠ 0 → ω ≠ c • (1 : CliffordAlgebra Q) := by
    intro c hc0 hc
    have h1 : ω * ι Q (e 1) = Q (e 1) • ι Q (e 0) := by
      rw [hω, mul_assoc, hsq, mul_smul_comm, mul_one]
    rw [hc, smul_mul_assoc, one_mul, ← LinearMap.map_smul, ← LinearMap.map_smul] at h1
    have h2 := congrArg (fun v => e.repr v 1) (ι_injective Q h1)
    exact hc0 (by simpa [Module.Basis.repr_self] using h2)
  set ε : CliffordAlgebra Q := (2⁻¹ : F) • (1 + r⁻¹ • ω)
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hωε : ω * ε = r • ε := by
    have : ω * ε = (2⁻¹ : F) • (ω + r⁻¹ • (r ^ 2 • (1 : CliffordAlgebra Q))) := by
      rw [← hωω]; simp only [ε, mul_smul_comm, mul_add, mul_one]
    rw [this]
    simp only [ε]
    match_scalars <;> field_simp
  have hωε' : ω * (1 - ε) = (-r) • (1 - ε) := by
    rw [mul_sub, mul_one, hωε]
    simp only [ε]
    match_scalars <;> field_simp <;> ring
  refine ⟨ε, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply hωne (-r) (neg_ne_zero.2 hr0)
    have : (2⁻¹ : F) • (1 + r⁻¹ • ω) = 0 := h0
    rw [smul_eq_zero] at this
    rcases this with h | h
    · exact absurd h (inv_ne_zero h2)
    · have h' : r⁻¹ • ω = -(1 : CliffordAlgebra Q) := eq_neg_of_add_eq_zero_right h
      calc ω = r • (r⁻¹ • ω) := by rw [smul_smul, mul_inv_cancel₀ hr0, one_smul]
        _ = (-r) • (1 : CliffordAlgebra Q) := by rw [h', smul_neg, neg_smul]
  · intro h0
    apply hωne r hr0
    have h' : (1 : CliffordAlgebra Q) = (2⁻¹ : F) • (1 + r⁻¹ • ω) := sub_eq_zero.1 h0
    have h'' : r⁻¹ • ω = (1 : CliffordAlgebra Q) := by
      have := congrArg (fun x => (2 : F) • x) h'
      simp only [smul_smul, mul_inv_cancel₀ h2, one_smul, smul_add, two_smul] at this
      have h3 := (add_left_cancel this).symm
      rwa [← mul_assoc, mul_inv_cancel₀ h2, one_mul] at h3
    calc ω = r • (r⁻¹ • ω) := by rw [smul_smul, mul_inv_cancel₀ hr0, one_smul]
      _ = r • (1 : CliffordAlgebra Q) := by rw [h'']
  · intro g
    obtain ⟨α, β, hab⟩ := exists_eq_smul_one_add_smul_of_even e he _
      (by rw [← even_toSubmodule]; exact g.2.1)
    refine ⟨α + β * r, ?_⟩
    rw [hab, ← hω]
    calc (α • (1 : CliffordAlgebra Q) + β • ω) * ε = α • ε + β • (ω * ε) := by
          rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
      _ = (α + β * r) • ε := by rw [hωε, add_smul, mul_smul]
  · intro g
    obtain ⟨α, β, hab⟩ := exists_eq_smul_one_add_smul_of_even e he _
      (by rw [← even_toSubmodule]; exact g.2.1)
    refine ⟨α + β * (-r), ?_⟩
    rw [hab, ← hω]
    calc (α • (1 : CliffordAlgebra Q) + β • ω) * (1 - ε) = α • (1 - ε) + β • (ω * (1 - ε)) := by
          rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
      _ = (α + β * (-r)) • (1 - ε) := by rw [hωε', add_smul, mul_smul]

open CliffordAlgebra in
/-- **`GSpin` of a hyperbolic plane preserves every isotropic line**: for `q(v) = 0`,
`P(g) v ∈ F v`.  With an orthogonal basis `e₀, e₁` and `ω = e₀e₁`, an isotropic `v` satisfies
`ω v = c v = −v ω`, and `g = α + βω`. -/
theorem exists_specP_eq_smul_of_isHypPlane {Q : QuadraticForm F V} (hQ : IsHypPlane Q)
    (g : GSpin Q) {v : V} (hv : Q v = 0) : ∃ t : F, specP Q g v = t • v := by
  obtain ⟨e, he⟩ := exists_orthogonal_basis_fin_two Q hQ.1
  set ω : CliffordAlgebra Q := ι Q (e 0) * ι Q (e 1) with hω
  set a := e.repr v 0
  set b := e.repr v 1
  have hv' : v = a • e 0 + b • e 1 := by rw [← e.sum_repr v, Fin.sum_univ_two]
  have hpol : QuadraticMap.polar Q (e 0) (e 1) = 0 := by
    rw [polar_eq_two_mul_bform, he 0 1 (by decide), mul_zero]
  have hQv : a ^ 2 * Q (e 0) + b ^ 2 * Q (e 1) = 0 := by
    have : Q (a • e 0 + b • e 1) = 0 := hv' ▸ hv
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hpol] at this
    simpa [smul_eq_mul, pow_two, mul_comm, mul_assoc, mul_left_comm] using this
  have h10 : ι Q (e 1) * ι Q (e 0) = -ω := by
    have h1 := ι_mul_ι_add_swap (Q := Q) (e 1) (e 0)
    rw [QuadraticMap.polar_comm, hpol, (algebraMap F (CliffordAlgebra Q)).map_zero] at h1
    exact eq_neg_of_add_eq_zero_left h1
  have hsq : ∀ i, ι Q (e i) * ι Q (e i) = Q (e i) • (1 : CliffordAlgebra Q) := fun i => by
    rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one]
  have ωe0 : ω * ι Q (e 0) = -(Q (e 0) • ι Q (e 1)) := by
    rw [hω, mul_assoc, h10, mul_neg, ← mul_assoc, hsq, smul_mul_assoc, one_mul]
  have e0ω : ι Q (e 0) * ω = Q (e 0) • ι Q (e 1) := by
    rw [hω, ← mul_assoc, hsq, smul_mul_assoc, one_mul]
  have ωe1 : ω * ι Q (e 1) = Q (e 1) • ι Q (e 0) := by
    rw [hω, mul_assoc, hsq, mul_smul_comm, mul_one]
  have e1ω : ι Q (e 1) * ω = -(Q (e 1) • ι Q (e 0)) := by
    rw [hω, ← mul_assoc, h10, neg_mul, ωe1]
  -- `ω v = ι(b q₁ e₀ − a q₀ e₁)` and `v ω = −ω v`
  have hωv : ω * ι Q v = ι Q (b • Q (e 1) • e 0 - a • Q (e 0) • e 1) := by
    rw [hv', map_add, map_smul, map_smul, mul_add, mul_smul_comm, mul_smul_comm, ωe0, ωe1]
    simp only [map_sub, map_smul]
    module
  have hvω : ι Q v * ω = -(ω * ι Q v) := by
    rw [hωv, hv', map_add, map_smul, map_smul, add_mul, smul_mul_assoc, smul_mul_assoc, e0ω, e1ω]
    simp only [map_sub, map_smul]
    module
  -- the eigenvalue `c`
  obtain ⟨c, hc⟩ : ∃ c : F, b • Q (e 1) • e 0 - a • Q (e 0) • e 1 = c • v := by
    by_cases ha : a = 0
    · have hbq : b * Q (e 1) = 0 := by
        have : b ^ 2 * Q (e 1) = 0 := by simpa [ha] using hQv
        rcases mul_eq_zero.1 this with h | h
        · simp [pow_eq_zero_iff two_ne_zero |>.1 h]
        · simp [h]
      refine ⟨0, ?_⟩
      rw [zero_smul, ha, zero_smul, sub_zero, smul_smul, hbq, zero_smul]
    · refine ⟨b * Q (e 1) / a, ?_⟩
      rw [hv', smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
      have h1 : b * Q (e 1) / a * a = b * Q (e 1) := by field_simp
      have h2 : b * Q (e 1) / a * b = -(a * Q (e 0)) := by
        field_simp; linear_combination hQv
      rw [h1, h2, neg_smul, sub_eq_add_neg]
  have hωv' : ω * ι Q v = c • ι Q v := by rw [hωv, hc, map_smul]
  have hvω' : ι Q v * ω = (-c) • ι Q v := by rw [hvω, hωv', neg_smul]
  -- `g = α + βω`, `g⁻¹ = α' + β'ω`
  obtain ⟨α, β, hab⟩ := exists_eq_smul_one_add_smul_of_even e he _
    (by rw [← even_toSubmodule]; exact g.2.1)
  obtain ⟨α', β', hab'⟩ := exists_eq_smul_one_add_smul_of_even e he
    ((((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
    (by rw [← even_toSubmodule]; exact (g⁻¹ : GSpin Q).2.1)
  have hgv : ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q v = (α + β * c) • ι Q v := by
    rw [hab, ← hω, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hωv', smul_smul, add_smul]
  have hvg : ι Q v * ((((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) =
      (α' + β' * (-c)) • ι Q v := by
    rw [hab', ← hω, mul_add, mul_smul_comm, mul_smul_comm, mul_one, hvω', smul_smul, add_smul]
  refine ⟨(α + β * c) * (α' + β' * (-c)), ι_injective Q ?_⟩
  rw [ι_specP, hgv, smul_mul_assoc, hvg, smul_smul, map_smul]

/-- **The split centre lies in every parabolic subgroup**: `A_{GSpin(U)} ≤ P_F` for every isotropic
flag `F` (scalars act trivially on `U`; for a hyperbolic plane every element preserves each
isotropic line, `exists_specP_eq_smul_of_isHypPlane`). -/
theorem splitCentralGSpin_le_flagStab (Q : QuadraticForm F V) (Fl : IsotropicFlag Q) :
    splitCentralGSpin Q ≤ flagStab Fl := by
  classical
  intro g hg
  rw [mem_flagStab_iff]
  intro i v hv
  unfold splitCentralGSpin at hg
  split_ifs at hg with hQ
  · obtain ⟨t, ht⟩ := exists_specP_eq_smul_of_isHypPlane hQ g (Fl.isotropic i v hv)
    rw [ht]; exact Submodule.smul_mem _ t hv
  · obtain ⟨c, rfl⟩ := hg
    rw [specP_scalarGSpin_eq_one]; exact hv

end Plane

/-! ## The two characters of `GSpin(U)` and the factor map `hcMap` -/

section Factor

variable {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]

/-- `ProperSpace F` (a locally compact normed field). -/
theorem properSpace_F : ProperSpace F :=
  .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F

/-- `C(V)` (module topology) is Hausdorff. -/
theorem t2Space_cliffordAlgebra (Q : QuadraticForm F V) : T2Space (CliffordAlgebra Q) :=
  IsTopologicalAddGroup.t2Space_iff_zero_closed.mpr
    (by simpa using isClosed_submodule_of_moduleTopology (⊥ : Submodule F (CliffordAlgebra Q)))

/-- The character `g ↦ N_{C(V)/F}(g) = det(L_g | C(V))` of `GSpin(V)` (the algebra norm of
`C(V)` over `F`).  On the scalars it is `c ↦ c^{2^{dim V}}`. -/
def detChar (Q : QuadraticForm F V) : GSpin Q →* Fˣ :=
  (Units.map (Algebra.norm F : CliffordAlgebra Q →* F)).comp (GSpin Q).subtype

theorem detChar_apply (Q : QuadraticForm F V) (g : GSpin Q) :
    ((detChar Q g : Fˣ) : F) =
      Algebra.norm F (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) := rfl

theorem continuous_detChar (Q : QuadraticForm F V) :
    Continuous (fun g => ((detChar Q g : Fˣ) : F)) := by
  classical
  set b := Module.finBasis F (CliffordAlgebra Q)
  have key : (fun g => ((detChar Q g : Fˣ) : F)) =
      fun g : GSpin Q => (Algebra.leftMulMatrix b
        (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))).det := by
    funext g
    rw [detChar_apply, Algebra.norm_eq_matrix_det b]
  rw [key]
  refine Continuous.matrix_det ?_
  exact (IsModuleTopology.continuous_of_linearMap
    (Algebra.leftMulMatrix b).toLinearMap).comp (Units.continuous_val.comp continuous_subtype_val)

theorem detChar_scalarGSpin (Q : QuadraticForm F V) (c : Fˣ) :
    ((detChar Q (scalarGSpin Q c) : Fˣ) : F) = (c : F) ^ Module.finrank F (CliffordAlgebra Q) :=
  Algebra.norm_algebraMap _

/-- The first coordinate `ε₊`-character of `GSpin` of a hyperbolic plane. -/
def planeChar₁ (Q : QuadraticForm F V) (hQ : IsHypPlane Q) : GSpin Q →* Fˣ :=
  eigenChar Q (exists_planeIdempotent hQ).choose_spec.1 (exists_planeIdempotent hQ).choose_spec.2.2.1

/-- The second coordinate `ε₋`-character of `GSpin` of a hyperbolic plane. -/
def planeChar₂ (Q : QuadraticForm F V) (hQ : IsHypPlane Q) : GSpin Q →* Fˣ :=
  eigenChar Q (exists_planeIdempotent hQ).choose_spec.2.1
    (exists_planeIdempotent hQ).choose_spec.2.2.2

/-- `g = χ₁(g) ε₊ + χ₂(g) ε₋` on a hyperbolic plane. -/
theorem coe_eq_planeChar (Q : QuadraticForm F V) (hQ : IsHypPlane Q) (g : GSpin Q) :
    ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      ((planeChar₁ Q hQ g : Fˣ) : F) • (exists_planeIdempotent hQ).choose +
        ((planeChar₂ Q hQ g : Fˣ) : F) • (1 - (exists_planeIdempotent hQ).choose) := by
  set h := exists_planeIdempotent hQ
  have e1 := eigenChar_apply Q h.choose_spec.1 h.choose_spec.2.2.1 g
  have e2 := eigenChar_apply Q h.choose_spec.2.1 h.choose_spec.2.2.2 g
  calc ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
        ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * h.choose +
          ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * (1 - h.choose) := by
          rw [← mul_add, add_sub_cancel, mul_one]
    _ = _ := by rw [e1, e2]; rfl

open scoped Classical in
/-- The first character `χ₁` of `GSpin(U)` used for `H_G`: `ε₊`-coordinate on a hyperbolic plane,
the algebra norm `det(L_g)` otherwise. -/
def gspinChar₁ (Q : QuadraticForm F V) : GSpin Q →* Fˣ :=
  if hQ : IsHypPlane Q then planeChar₁ Q hQ else detChar Q

open scoped Classical in
/-- The second character `χ₂`: `ε₋`-coordinate on a hyperbolic plane, trivial otherwise. -/
def gspinChar₂ (Q : QuadraticForm F V) : GSpin Q →* Fˣ :=
  if hQ : IsHypPlane Q then planeChar₂ Q hQ else 1

theorem continuous_gspinChar₁ (Q : QuadraticForm F V) :
    Continuous (fun g => ((gspinChar₁ Q g : Fˣ) : F)) := by
  classical
  unfold gspinChar₁
  split_ifs with hQ
  · exact continuous_eigenChar Q _ _
  · exact continuous_detChar Q

theorem continuous_gspinChar₂ (Q : QuadraticForm F V) :
    Continuous (fun g => ((gspinChar₂ Q g : Fˣ) : F)) := by
  classical
  unfold gspinChar₂
  split_ifs with hQ
  · exact continuous_eigenChar Q _ _
  · simpa using continuous_const

/-- **The factor map** `hcMap(g) = (log‖χ₁ g‖, log‖χ₂ g‖)` (the `GSpin(U)`-component of the
Harish-Chandra map `H_G`, Thesis §2.1). -/
def hcMap (Q : QuadraticForm F V) : GSpin Q →* Multiplicative ℝ × Multiplicative ℝ :=
  (logAbs.comp (gspinChar₁ Q)).prod (logAbs.comp (gspinChar₂ Q))

theorem hcMap_eq_one_iff (Q : QuadraticForm F V) (g : GSpin Q) :
    hcMap Q g = 1 ↔ ‖((gspinChar₁ Q g : Fˣ) : F)‖ = 1 ∧ ‖((gspinChar₂ Q g : Fˣ) : F)‖ = 1 := by
  rw [Prod.ext_iff]
  exact and_congr (logAbs_eq_one_iff _) (logAbs_eq_one_iff _)

theorem isLocallyConstant_hcMap (Q : QuadraticForm F V) : IsLocallyConstant (hcMap Q) := by
  have h1 := (isLocallyConstant_norm_comp (continuous_gspinChar₁ Q) fun g => (gspinChar₁ Q g).ne_zero)
  have h2 := (isLocallyConstant_norm_comp (continuous_gspinChar₂ Q) fun g => (gspinChar₂ Q g).ne_zero)
  exact (h1.comp fun t => Multiplicative.ofAdd (Real.log t)).prodMk
    (h2.comp fun t => Multiplicative.ofAdd (Real.log t))

/-- `hcMap` is trivial at elements whose powers stay in a compact set. -/
theorem hcMap_eq_one_of_zpow_mem_compact (Q : QuadraticForm F V) {u : GSpin Q} {C : Set (GSpin Q)}
    (hC : IsCompact C) (hu : ∀ k : ℤ, u ^ k ∈ C) : hcMap Q u = 1 :=
  (hcMap_eq_one_iff Q u).2 ⟨norm_char_eq_one_of_zpow_mem_compact _ (continuous_gspinChar₁ Q) hC hu,
    norm_char_eq_one_of_zpow_mem_compact _ (continuous_gspinChar₂ Q) hC hu⟩

/-- `hcMap` is trivial on unipotent elements (`u − 1` nilpotent in `C(V)`): their powers stay in a
compact set (`exists_isCompact_zpow_of_isNilpotent`, `F` non-archimedean). -/
theorem hcMap_eq_one_of_isNilpotent (Q : QuadraticForm F V) {u : GSpin Q}
    (hu : IsNilpotent (((u : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1)) : hcMap Q u = 1 := by
  have := properSpace_F (F := F)
  have := t2Space_cliffordAlgebra Q
  obtain ⟨C, hC, hCu⟩ := exists_isCompact_zpow_of_isNilpotent (K := F) _ hu
  refine hcMap_eq_one_of_zpow_mem_compact Q
    ((isClosed_GSpin Q).isClosedEmbedding_subtypeVal.isCompact_preimage hC) fun k => ?_
  show ((u ^ k : GSpin Q) : (CliffordAlgebra Q)ˣ) ∈ C
  rw [Subgroup.coe_zpow]; exact hCu k

/-- The compact set `{c ∈ F^× : ‖c‖ = 1}`. -/
theorem isCompact_unitSphere : IsCompact {c : Fˣ | ‖(c : F)‖ = 1} := by
  have := properSpace_F (F := F)
  have e : {c : Fˣ | ‖(c : F)‖ = 1} = Units.embedProduct F ⁻¹'
      (Metric.sphere (0 : F) 1 ×ˢ (MulOpposite.op '' Metric.sphere (0 : F) 1)) := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
      mem_sphere_iff_norm, sub_zero, Set.mem_image]
    constructor
    · intro h
      refine ⟨h, _, ?_, rfl⟩
      rw [Units.val_inv_eq_inv_val, norm_inv, h, inv_one]
    · exact fun h => h.1
  rw [e]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    ((isCompact_sphere _ _).prod ((isCompact_sphere _ _).image MulOpposite.continuous_op))

/-- **`A_{GSpin(U)} ∩ ker hcMap` is compact**: the scalars of norm `1` if `U` is not a hyperbolic
plane (`det(L_c) = c^{2^n}`), and `{g : ‖χ₁ g‖ = ‖χ₂ g‖ = 1}` (contained in the compact set
`{a ε₊ + b ε₋ : ‖a‖, ‖b‖ ≤ 1}` together with its inverse) if it is. -/
theorem isCompact_splitCentral_inter_ker_hcMap (Q : QuadraticForm F V) :
    IsCompact ((splitCentralGSpin Q : Set (GSpin Q)) ∩ {g | hcMap Q g = 1}) := by
  classical
  have := properSpace_F (F := F)
  have := t2Space_cliffordAlgebra Q
  have hcl : IsClosed ((splitCentralGSpin Q : Set (GSpin Q)) ∩ {g | hcMap Q g = 1}) :=
    (isClosed_splitCentralGSpin Q).inter ((isLocallyConstant_hcMap Q).isClopen_fiber 1).isClosed
  by_cases hQ : IsHypPlane Q
  · -- the hyperbolic plane: a closed subset of a compact set
    set ε := (exists_planeIdempotent hQ).choose
    set S : Set (CliffordAlgebra Q) := (fun p : F × F => p.1 • ε + p.2 • (1 - ε)) ''
        (Metric.closedBall (0 : F) 1 ×ˢ Metric.closedBall (0 : F) 1)
    have hS : IsCompact S :=
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image (by fun_prop)
    have h1 : gspinChar₁ Q = planeChar₁ Q hQ := by simp [gspinChar₁, hQ]
    have h2 : gspinChar₂ Q = planeChar₂ Q hQ := by simp [gspinChar₂, hQ]
    have hmem : ∀ g : GSpin Q, hcMap Q g = 1 →
        ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ S := by
      intro g hg
      rw [hcMap_eq_one_iff, h1, h2] at hg
      exact ⟨(((planeChar₁ Q hQ g : Fˣ) : F), ((planeChar₂ Q hQ g : Fˣ) : F)),
        ⟨by simp [hg.1], by simp [hg.2]⟩, (coe_eq_planeChar Q hQ g).symm⟩
    have hK : IsCompact ((Subtype.val : GSpin Q → (CliffordAlgebra Q)ˣ) ⁻¹'
        (Units.embedProduct (CliffordAlgebra Q) ⁻¹' (S ×ˢ (MulOpposite.op '' S)))) :=
      (isClosed_GSpin Q).isClosedEmbedding_subtypeVal.isCompact_preimage
        (Units.isClosedEmbedding_embedProduct.isCompact_preimage
          (hS.prod (hS.image MulOpposite.continuous_op)))
    refine hK.of_isClosed_subset hcl fun g hg => ?_
    have hgi : hcMap Q g⁻¹ = 1 := by rw [map_inv, hg.2, inv_one]
    simp only [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image]
    exact ⟨hmem g hg.2, _, hmem g⁻¹ hgi, rfl⟩
  · -- otherwise: the scalars of norm one
    have hA : (splitCentralGSpin Q : Set (GSpin Q)) = Set.range (scalarGSpin Q) := by
      simp [splitCentralGSpin, hQ]
    have hcont : Continuous (scalarGSpin Q) :=
      continuous_induced_rng.2 (Units.continuous_map (continuous_algebraMap F (CliffordAlgebra Q)))
    refine (isCompact_unitSphere.image hcont).of_isClosed_subset hcl ?_
    rintro g ⟨hgA, hg⟩
    rw [hA] at hgA
    obtain ⟨c, rfl⟩ := hgA
    refine ⟨c, ?_, rfl⟩
    have h1 : gspinChar₁ Q = detChar Q := by simp [gspinChar₁, hQ]
    have hg' := ((hcMap_eq_one_iff Q _).1 hg).1
    rw [h1, detChar_scalarGSpin, norm_pow] at hg'
    have hN : Module.finrank F (CliffordAlgebra Q) ≠ 0 := by
      rw [finrank_cliffordAlgebra]; positivity
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN).1 hg'

end Factor

/-! ## The Harish-Chandra map `H_G` of `G = GSpin(W) × GSpin(V)` -/

/-- The value group of `H_G`: `(ℝ²) × (ℝ²)`, written multiplicatively. -/
abbrev HCVal : Type := (Multiplicative ℝ × Multiplicative ℝ) × (Multiplicative ℝ × Multiplicative ℝ)

namespace GGPData

variable (d : GGPData F)

/-- **The Harish-Chandra map** `H_G(g) = (hcMap(g_W), hcMap(g_V))` (Thesis §2.1; see the module docstring for the characters used). -/
def hcG : ↥d.G →* HCVal := ((hcMap d.QW).comp d.fst).prod ((hcMap d.QV).comp d.snd)

/-- `H_G` is locally constant. -/
theorem isLocallyConstant_hcG : IsLocallyConstant d.hcG :=
  ((isLocallyConstant_hcMap d.QW).comp_continuous d.continuous_fst).prodMk
    ((isLocallyConstant_hcMap d.QV).comp_continuous d.continuous_snd)

/-- `H_G` is conjugation invariant (its values lie in a commutative group). -/
theorem hcG_conj (x g : ↥d.G) : d.hcG (x * g * x⁻¹) = d.hcG g := by
  rw [map_mul, map_mul, map_inv, mul_comm (d.hcG x), mul_assoc, mul_inv_cancel, mul_one]

/-- `H_G` is trivial on the unipotent radicals `U = N_{F_W} × N_{F_V}`. -/
theorem hcG_eq_one_of_mem_whittU {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV} {u : ↥d.G}
    (hu : u ∈ d.whittU FW FV) : d.hcG u = 1 :=
  Prod.ext (hcMap_eq_one_of_isNilpotent d.QW hu.1.2.2.2)
    (hcMap_eq_one_of_isNilpotent d.QV hu.2.2.2.2)

/-- `H_G(p u) = H_G(p)` for `u` in a unipotent radical. -/
theorem hcG_mul_whittU {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV} (p : ↥d.G) {u : ↥d.G}
    (hu : u ∈ d.whittU FW FV) : d.hcG (p * u) = d.hcG p := by
  rw [map_mul, d.hcG_eq_one_of_mem_whittU hu, mul_one]

/-- **`A_G(F) ∩ ker H_G` is compact** (Thesis §2.1: `H_G(A_G(F))` is a lattice and the kernel on
`A_G(F)` is its maximal compact subgroup). -/
theorem isCompact_AG_inter_ker_hcG :
    IsCompact ((d.AG : Set ↥d.G) ∩ {g | d.hcG g = 1}) := by
  have hKW := isCompact_splitCentral_inter_ker_hcMap d.QW
  have hKV := isCompact_splitCentral_inter_ker_hcMap d.QV
  have hcl : IsClosed ((d.AG : Set ↥d.G) ∩ {g | d.hcG g = 1}) :=
    d.isClosed_AG.inter (d.isLocallyConstant_hcG.isClopen_fiber 1).isClosed
  refine ((hKW.prod hKV).image d.continuous_pair).of_isClosed_subset hcl ?_
  rintro g ⟨⟨p, ⟨hp1, hp2⟩, rfl⟩, hg⟩
  have hg' : d.hcG (d.pair p) = (hcMap d.QW p.1, hcMap d.QV p.2) := rfl
  rw [Set.mem_ofPred_eq, hg', Prod.ext_iff] at hg
  exact ⟨p, ⟨⟨hp1, hg.1⟩, ⟨hp2, hg.2⟩⟩, rfl⟩

/-- `A_G(F)` lies in every parabolic subgroup `P_{F_W} × P_{F_V}` (Thesis §5.1.2). -/
theorem AG_le_whittB (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) :
    d.AG ≤ d.whittB FW FV := by
  rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
  exact ⟨splitCentralGSpin_le_flagStab _ FW hp1, splitCentralGSpin_le_flagStab _ FV hp2⟩

/-- `A_G(F) · C` is closed for compact `C` (helper; pointwise products on `G(F)` are slow to
elaborate under the Lie-algebra local instances of later files). -/
theorem isClosed_AG_mul {C : Set ↥d.G} (hC : IsCompact C) : IsClosed ((d.AG : Set ↥d.G) * C) :=
  d.isClosed_AG.mul_right_of_isCompact hC

/-- `b K · C` is compact for `K ⊆ A_G(F)`, `C ⊆ G(F)` compact (helper, as `isClosed_AG_mul`). -/
theorem isCompact_image_mul {C : Set ↥d.G} (hC : IsCompact C) {K : Set ↥d.AG} (hK : IsCompact K)
    (b : ↥d.AG) :
    IsCompact ((Subtype.val : ↥d.AG → ↥d.G) '' ((fun a => b * a) '' K) * C) :=
  ((hK.image (Homeomorph.mulLeft b).continuous).image continuous_subtype_val).mul hC

end GGPData

end GSpinGGP
