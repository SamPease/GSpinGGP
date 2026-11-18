/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Analytic
import GSpinGGP.TraceFormula.GoodParabolic

/-!
# The weak Cartan decomposition of `G` and the reduction from `G` to `G₀`

Scratch header; rewritten at the end.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Module QuadraticMap

namespace GSpinGGP

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

open WeakCartan

/-! ## 1. The datum `(W, V₀)` and `SO(V₀) ⊆ SO(V)` -/

/-- The GGP datum of the codimension-one pair `(W, V₀)`, `V₀ = W ⊕ ⟨z₀⟩`: the same `W` and `ν`,
with `r = 0`. Its space `V` is `d.V0` and its form is `d.Q0` (both by definition). -/
abbrev base : GGPData F where
  m := d.m
  QW := d.QW
  nondeg := d.nondeg
  r := 0
  ν := d.ν

example : d.base.V = d.V0 := rfl
example : d.base.QV = d.Q0 := rfl
example : d.base.r = 0 := rfl

/-- `g ↦ g ⊕ 1` on `V = V₀ ⊕ ⟨z_{±1}, …, z_{±r}⟩` (underlying linear map of `extV0`):
`v ↦ v + ι₀(g(π₀ v) − π₀ v)`. -/
def extV0Fun (g : d.V0 ≃ₗ[F] d.V0) : d.V →ₗ[F] d.V :=
  LinearMap.id + d.iota0 ∘ₗ ((g : d.V0 →ₗ[F] d.V0) - LinearMap.id) ∘ₗ d.pi0

theorem extV0Fun_apply (g : d.V0 ≃ₗ[F] d.V0) (v : d.V) :
    d.extV0Fun g v = v + d.iota0 (g (d.pi0 v) - d.pi0 v) := rfl

theorem pi0_extV0Fun (g : d.V0 ≃ₗ[F] d.V0) (v : d.V) :
    d.pi0 (d.extV0Fun g v) = g (d.pi0 v) := by
  rw [extV0Fun_apply, map_add, pi0_iota0]; abel

theorem extV0Fun_mul (g h : d.V0 ≃ₗ[F] d.V0) (v : d.V) :
    d.extV0Fun (g * h) v = d.extV0Fun g (d.extV0Fun h v) := by
  rw [d.extV0Fun_apply g, d.pi0_extV0Fun, d.extV0Fun_apply h, d.extV0Fun_apply,
    LinearEquiv.mul_apply, add_assoc, ← map_add]
  congr 2; abel

theorem extV0Fun_one (v : d.V) : d.extV0Fun 1 v = v := by
  simp [extV0Fun_apply]

/-- **`SO(V₀) ⊆ SO(V)`**: `g ↦ g ⊕ 1` on `V = V₀ ⊕ ⟨z_{±1}, …, z_{±r}⟩` (as a homomorphism of
the groups of linear automorphisms; it maps `SO(V₀)` into `SO(V)`, `extV0_mem_SOGrp`). -/
def extV0 : (d.V0 ≃ₗ[F] d.V0) →* (d.V ≃ₗ[F] d.V) where
  toFun g := LinearEquiv.ofLinearMap (d.extV0Fun g) (d.extV0Fun g⁻¹)
    (LinearMap.ext fun v => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply, ← extV0Fun_mul, mul_inv_cancel,
        extV0Fun_one])
    (LinearMap.ext fun v => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply, ← extV0Fun_mul, inv_mul_cancel,
        extV0Fun_one])
  map_one' := LinearEquiv.ext fun v => d.extV0Fun_one v
  map_mul' g h := LinearEquiv.ext fun v => d.extV0Fun_mul g h v

theorem extV0_apply (g : d.V0 ≃ₗ[F] d.V0) (v : d.V) :
    d.extV0 g v = v + d.iota0 (g (d.pi0 v) - d.pi0 v) := rfl

theorem pi0_extV0 (g : d.V0 ≃ₗ[F] d.V0) (v : d.V) : d.pi0 (d.extV0 g v) = g (d.pi0 v) :=
  d.pi0_extV0Fun g v

theorem extV0_iota0 (g : d.V0 ≃ₗ[F] d.V0) (x : d.V0) : d.extV0 g (d.iota0 x) = d.iota0 (g x) := by
  rw [extV0_apply, pi0_iota0, ← map_add]; congr 1; abel

/-! ## 2. The split torus `A` of the Levi `M = G₀ A` -/

/-- The coefficient of the torus element `a(τ)` on the coordinate `z_{i - r}`:
`τ_k` on `z_{k+1}`, `τ_k⁻¹` on `z_{-(k+1)}`, `1` on `z₀`. -/
def torusCoeff (τ : Fin d.r → Fˣ) (i : Fin (2 * d.r + 1)) : Fˣ :=
  if h : d.r < (i : ℕ) then τ ⟨i - d.r - 1, by omega⟩
  else if h' : (i : ℕ) < d.r then (τ ⟨d.r - 1 - i, by omega⟩)⁻¹ else 1

/-- **The split torus `A ≅ GL₁^r`** of the Levi `M = G₀ × A` of the stabilizer `P` of
`⟨z_r⟩ ⊂ ⋯ ⊂ ⟨z_r, …, z_1⟩` (Thesis §8.3, before Lemma 8.3.2), at the level of `SO(V)`:
`a(τ)` acts on `z_k` by `τ_{k-1}` and on `z_{-k}` by `τ_{k-1}⁻¹` (`1 ≤ k ≤ r`), and trivially on
`V₀ = W ⊕ ⟨z₀⟩`. -/
def torusZ (τ : Fin d.r → Fˣ) : d.V ≃ₗ[F] d.V :=
  (LinearEquiv.refl F _).prodCongr
    (LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfUnit (d.torusCoeff τ i))

theorem torusZ_apply (τ : Fin d.r → Fˣ) (v : d.V) :
    d.torusZ τ v = (v.1, fun i => (d.torusCoeff τ i : F) * v.2 i) := rfl

theorem torusCoeff_inv (τ : Fin d.r → Fˣ) (i : Fin (2 * d.r + 1)) :
    d.torusCoeff τ⁻¹ i = (d.torusCoeff τ i)⁻¹ := by
  unfold torusCoeff
  split_ifs <;> simp

theorem torusZ_inv (τ : Fin d.r → Fˣ) : (d.torusZ τ)⁻¹ = d.torusZ τ⁻¹ := by
  rw [inv_eq_iff_mul_eq_one]
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, torusZ_apply, torusZ_apply]
  refine Prod.ext rfl (funext fun i => ?_)
  simp only [torusCoeff_inv, ← mul_assoc, ← Units.val_mul, LinearEquiv.coe_one, id_eq]
  rw [mul_inv_cancel, Units.val_one, one_mul]

theorem torusCoeff_r (τ : Fin d.r → Fˣ) : d.torusCoeff τ ⟨d.r, by omega⟩ = 1 := by
  simp [torusCoeff]

theorem torusCoeff_pos (τ : Fin d.r → Fˣ) (j : Fin d.r) :
    d.torusCoeff τ ⟨d.r + j + 1, by omega⟩ = τ j := by
  rw [torusCoeff, dif_pos (by simp)]
  congr 1; ext; simp; omega

theorem pi0_torusZ (τ : Fin d.r → Fˣ) (v : d.V) : d.pi0 (d.torusZ τ v) = d.pi0 v := by
  simp only [pi0, LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, torusZ_apply, torusCoeff_r, Units.val_one, one_mul]

theorem torusZ_iota0 (τ : Fin d.r → Fˣ) (x : d.V0) : d.torusZ τ (d.iota0 x) = d.iota0 x := by
  rw [torusZ_apply, iota0_apply]
  refine Prod.ext rfl (funext fun i => ?_)
  by_cases hi : (i : ℕ) = d.r
  · have hlt : d.r < 2 * d.r + 1 := by omega
    obtain rfl : i = ⟨d.r, hlt⟩ := Fin.ext hi
    show (d.torusCoeff τ ⟨d.r, hlt⟩ : F) * _ = _
    rw [torusCoeff_r, Units.val_one, one_mul]
  · simp [zvec, show ¬ ((i : ℤ) - d.r = 0) by omega]

theorem torusZ_coord (τ : Fin d.r → Fˣ) (j : Fin d.r) (v : d.V) :
    (d.torusZ τ v).2 ⟨d.r + j + 1, by omega⟩ = (τ j : F) * v.2 ⟨d.r + j + 1, by omega⟩ := by
  rw [torusZ_apply]
  show (d.torusCoeff τ ⟨d.r + j + 1, by omega⟩ : F) * _ = _
  rw [torusCoeff_pos]

theorem extV0_coord (g : d.V0 ≃ₗ[F] d.V0) (j : Fin d.r) (v : d.V) :
    (d.extV0 g v).2 ⟨d.r + j + 1, by omega⟩ = v.2 ⟨d.r + j + 1, by omega⟩ := by
  rw [extV0_apply, Prod.snd_add, Pi.add_apply, iota0_apply]
  simp only [Prod.snd_sub, Prod.smul_snd, Pi.sub_apply, Pi.smul_apply, zvec, smul_eq_mul]
  rw [if_neg (by push_cast; omega)]; simp

theorem zV_coord (j : Fin d.r) : (d.zV ((j : ℤ) + 1)).2 ⟨d.r + j + 1, by omega⟩ = 1 := by
  simp only [zV, zvec]
  rw [if_pos (by push_cast; ring)]

/-! ## 3. Compression of `P̄(h) a` to `G₀` and its diagonal entries on `Z₊` -/

theorem pi0_eq_zero_of_mem_flag (i : Fin (d.r + 1)) {v : d.V} (hv : v ∈ d.flag.sub i) :
    d.pi0 v = 0 := by
  have h := d.span_flag_le _ hv
  have h2 := h.2 ⟨d.r, by omega⟩ (by have := i.2; simp; omega)
  simp only [pi0, LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, h.1, h2, zero_smul]
  rfl

theorem iota0_mem_orthogonal_top (x : d.V0) :
    d.iota0 x ∈ (bform d.QV).orthogonal d.flag.top := by
  have e : d.iota0 x = ((x.1, 0) : d.V) + x.2 0 • d.zV 0 := by
    rw [iota0_apply, zV]; ext <;> simp
  rw [e]
  exact add_mem (d.inl_mem_orthogonal_top _) (Submodule.smul_mem _ _ d.zV_zero_mem_orthogonal_top)

/-- `N` acts trivially on `Z_r^⊥ / Z_r ≅ V₀`: `π₀(n ι₀(x)) = x`. -/
theorem pi0_specP_N_iota0 {n : GSpin d.QV} (hn : n ∈ d.N) (x : d.V0) :
    d.pi0 (specP d.QV n (d.iota0 x)) = x := by
  have h := hn.2.2.1 _ (d.iota0_mem_orthogonal_top x)
  have h0 := d.pi0_eq_zero_of_mem_flag _ h
  rw [map_sub, pi0_iota0, sub_eq_zero] at h0
  exact h0

/-- `N` is unipotent on the flag: the `z_{j+1}`-coordinate of `n z_{j+1} − z_{j+1}` vanishes. -/
theorem specP_N_zV_sub_coord {n : GSpin d.QV} (hn : n ∈ d.N) (j : Fin d.r) :
    (specP d.QV n (d.zV ((j : ℤ) + 1)) - d.zV ((j : ℤ) + 1)).2 ⟨d.r + j + 1, by omega⟩ = 0 := by
  set i : Fin d.flag.len := ⟨d.r - j - 1, by change _ < d.r; omega⟩
  have hz : d.zV ((j : ℤ) + 1) ∈ d.flag.sub i.succ := by
    refine Submodule.subset_span ⟨⟨d.r - j - 1, by simp [i]⟩, ?_⟩
    simp only
    congr 1; have := j.2; push_cast [show d.r - j.val - 1 ≤ d.r by omega,
      show j.val + 1 ≤ d.r by omega] <;> omega
  have hm := d.span_flag_le _ (hn.2.1 i _ hz)
  exact hm.2 _ (by simp only [i, Fin.val_castSucc]; omega)

/-- The `z_{j+1}`-coordinate of `n v` equals that of `v` for `v` a multiple of `z_{j+1}`
plus a vector with vanishing coordinates up to `z_{j+1}`. -/
theorem specP_N_coord {n : GSpin d.QV} (hn : n ∈ d.N) (j : Fin d.r) (c : F) :
    (specP d.QV n (c • d.zV ((j : ℤ) + 1))).2 ⟨d.r + j + 1, by omega⟩ = c := by
  have h := d.specP_N_zV_sub_coord hn j
  rw [Prod.snd_sub, Pi.sub_apply, zV_coord, sub_eq_zero] at h
  rw [map_smul, Prod.smul_snd, Pi.smul_apply, h, smul_eq_mul, mul_one]

/-- For `h ∈ H`: `P(h_V) = (P(h_W) ⊕ 1) · P(n)` with `n = nPart h ∈ N`. -/
theorem specP_snd_of_mem_H {h : d.G} :
    specP d.QV (d.snd h) = d.extZ (specP d.QW (d.fst h)) * specP d.QV (d.nPart h) := by
  have hs : d.snd h = d.incl (d.fst h) * d.nPart h := by simp [nPart]
  rw [hs, map_mul]
  congr 1
  exact LinearEquiv.ext fun v => d.specP_incl_apply _ v.1 v.2

theorem pi0_extZ (f : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) (v : d.V) :
    d.pi0 (d.extZ f v) = d.base.extZ f (d.pi0 v) := rfl

theorem extZ_iota0 (f : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) (x : d.V0) :
    d.extZ f (d.iota0 x) = d.iota0 (d.base.extZ f x) := rfl

theorem extZ_coord (f : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) (v : d.V) :
    (d.extZ f v).2 = v.2 := rfl

section Compress

variable {h : d.G} (hh : h ∈ d.H) (τ : Fin d.r → Fˣ) (y0 : d.V0 ≃ₗ[F] d.V0)

include hh in
/-- **Compression to `V₀`** (forward): for `h ∈ H` and `a = a(τ) (y₀ ⊕ 1)`,
`π₀ ∘ P(h_V) a ∘ ι₀ = (P(h_W) ⊕ 1) y₀` on `V₀`. -/
theorem pi0_compress (x : d.V0) :
    d.pi0 ((specP d.QV (d.snd h) * (d.torusZ τ * d.extV0 y0)) (d.iota0 x)) =
      d.base.extZ (specP d.QW (d.fst h)) (y0 x) := by
  rw [specP_snd_of_mem_H]
  simp only [LinearEquiv.mul_apply, extV0_iota0, torusZ_iota0, pi0_extZ]
  rw [d.pi0_specP_N_iota0 hh]

include hh in
/-- **Compression to `V₀`** (inverse). -/
theorem pi0_compress_inv (x : d.V0) :
    d.pi0 ((specP d.QV (d.snd h) * (d.torusZ τ * d.extV0 y0))⁻¹ (d.iota0 x)) =
      y0⁻¹ ((d.base.extZ (specP d.QW (d.fst h)))⁻¹ x) := by
  rw [specP_snd_of_mem_H, mul_inv_rev, mul_inv_rev, mul_inv_rev, ← map_inv d.extZ,
    ← map_inv (specP d.QV), ← map_inv d.extV0, torusZ_inv]
  simp only [LinearEquiv.mul_apply, extZ_iota0, pi0_extV0, pi0_torusZ]
  rw [d.pi0_specP_N_iota0 (d.N.inv_mem hh), map_inv]

include hh in
/-- **Diagonal entries on `Z₊`** (forward): the `z_{j+1}`-coordinate of `P(h_V) a z_{j+1}` is
`τ_j`. -/
theorem compress_coord (j : Fin d.r) :
    ((specP d.QV (d.snd h) * (d.torusZ τ * d.extV0 y0)) (d.zV ((j : ℤ) + 1))).2
      ⟨d.r + j + 1, by omega⟩ = τ j := by
  rw [specP_snd_of_mem_H]
  have e1 : d.extV0 y0 (d.zV ((j : ℤ) + 1)) = d.zV ((j : ℤ) + 1) := by
    rw [extV0_apply, d.pi0_zV (by omega), map_zero, sub_zero, map_zero, add_zero]
  have e2 : d.torusZ τ (d.zV ((j : ℤ) + 1)) = (τ j : F) • d.zV ((j : ℤ) + 1) := by
    refine Prod.ext (by simp [zV, torusZ_apply]) (funext fun i => ?_)
    by_cases hi : (i : ℕ) = d.r + j + 1
    · have hlt : d.r + j + 1 < 2 * d.r + 1 := by omega
      obtain rfl : i = ⟨d.r + j + 1, hlt⟩ := Fin.ext hi
      exact d.torusZ_coord τ j _
    · simp [torusZ_apply, zV, zvec, show ¬ ((i : ℤ) - d.r = j + 1) by omega]
  simp only [LinearEquiv.mul_apply, e1, e2, extZ_coord]
  exact d.specP_N_coord hh j _

include hh in
/-- **Diagonal entries on `Z₊`** (inverse): the `z_{j+1}`-coordinate of
`(P(h_V) a)⁻¹ z_{j+1}` is `τ_j⁻¹`. -/
theorem compress_coord_inv (j : Fin d.r) :
    ((specP d.QV (d.snd h) * (d.torusZ τ * d.extV0 y0))⁻¹ (d.zV ((j : ℤ) + 1))).2
      ⟨d.r + j + 1, by omega⟩ = ((τ j)⁻¹ : Fˣ) := by
  rw [specP_snd_of_mem_H, mul_inv_rev, mul_inv_rev, mul_inv_rev, ← map_inv d.extZ,
    ← map_inv (specP d.QV), ← map_inv d.extV0, torusZ_inv]
  have e1 : d.extZ (specP d.QW (d.fst h))⁻¹ (d.zV ((j : ℤ) + 1)) = d.zV ((j : ℤ) + 1) := by
    simp [zV, extZ]
  simp only [LinearEquiv.mul_apply, e1, extV0_coord, torusZ_coord]
  have := d.specP_N_coord (d.N.inv_mem hh) j 1
  rw [one_smul] at this
  rw [this, mul_one, Pi.inv_apply]

end Compress

/-! ## 4. Norm bounds -/

section GLNormAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace F E] [FiniteDimensional F E]

theorem norm_apply_le_glMaxNorm (f : E ≃ₗ[F] E) (v : E) : ‖f v‖ ≤ glMaxNorm f * ‖v‖ := by
  have := (LinearMap.toContinuousLinearMap (f : E →ₗ[F] E)).le_opNorm v
  rw [LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe] at this
  exact this.trans (mul_le_mul_of_nonneg_right (norm_le_glMaxNorm f) (norm_nonneg _))

theorem norm_inv_apply_le_glMaxNorm (f : E ≃ₗ[F] E) (v : E) : ‖f⁻¹ v‖ ≤ glMaxNorm f * ‖v‖ := by
  have := norm_apply_le_glMaxNorm f⁻¹ v
  rwa [glMaxNorm_inv] at this

theorem glMaxNorm_le_of_bound (f : E ≃ₗ[F] E) {M : ℝ} (hM : 1 ≤ M) (h1 : ∀ v, ‖f v‖ ≤ M * ‖v‖)
    (h2 : ∀ v, ‖f⁻¹ v‖ ≤ M * ‖v‖) : glMaxNorm f ≤ M := by
  refine max_le hM (max_le ?_ ?_) <;>
    refine ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hM) fun v => ?_ <;>
    rw [LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe]
  · exact h1 v
  · exact h2 v

end GLNormAux

theorem norm_zvec_le (r : ℕ) (k : ℤ) : ‖(zvec r k : Fin (2 * r + 1) → F)‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
    unfold zvec; split_ifs <;> simp

theorem norm_pi0_le (v : d.V) : ‖d.pi0 v‖ ≤ ‖v‖ := by
  simp only [pi0, LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, Prod.norm_def]
  refine max_le_max le_rfl ?_
  rw [norm_smul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (norm_zvec_le 0 0)).trans (norm_le_pi_norm _ _)

theorem norm_iota0_le (x : d.V0) : ‖d.iota0 x‖ ≤ ‖x‖ := by
  rw [iota0_apply, Prod.norm_def, Prod.norm_def]
  refine max_le_max le_rfl ?_
  rw [norm_smul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (norm_zvec_le _ _)).trans (norm_le_pi_norm _ _)

theorem norm_zV_le (k : ℤ) : ‖d.zV k‖ ≤ 1 := by
  rw [zV, Prod.norm_def, norm_zero]
  exact max_le zero_le_one (norm_zvec_le _ _)

theorem norm_coord_le (v : d.V) (i : Fin (2 * d.r + 1)) : ‖v.2 i‖ ≤ ‖v‖ :=
  (norm_le_pi_norm _ _).trans (norm_snd_le v)

/-- `glMax(g ⊕ 1) ≤ 3 glMax(g)` for `g ∈ GL(V₀)`. -/
theorem glMaxNorm_extV0_le (g : d.V0 ≃ₗ[F] d.V0) :
    glMaxNorm (d.extV0 g) ≤ 3 * glMaxNorm g := by
  have hg := one_le_glMaxNorm g
  have key : ∀ f : d.V0 ≃ₗ[F] d.V0, glMaxNorm f ≤ glMaxNorm g → ∀ v,
      ‖d.extV0 f v‖ ≤ 3 * glMaxNorm g * ‖v‖ := by
    intro f hf v
    rw [extV0_apply]
    have h1 := d.norm_iota0_le (f (d.pi0 v) - d.pi0 v)
    have h2 := norm_apply_le_glMaxNorm f (d.pi0 v)
    have h3 := d.norm_pi0_le v
    have h4 := norm_sub_le (f (d.pi0 v)) (d.pi0 v)
    have h5 := norm_add_le v (d.iota0 (f (d.pi0 v) - d.pi0 v))
    have hv := norm_nonneg v
    have h6 : glMaxNorm f * ‖d.pi0 v‖ ≤ glMaxNorm g * ‖v‖ :=
      mul_le_mul hf h3 (norm_nonneg _) (by linarith)
    nlinarith
  refine glMaxNorm_le_of_bound _ (by linarith) (key g le_rfl) fun v => ?_
  rw [← map_inv]
  exact key g⁻¹ (glMaxNorm_inv g).le v

/-- `glMax(a(τ)) ≤ M` when all `‖τ_j^{±1}‖ ≤ M`. -/
theorem glMaxNorm_torusZ_le (τ : Fin d.r → Fˣ) {M : ℝ} (hM : 1 ≤ M)
    (h : ∀ j, ‖(τ j : F)‖ ≤ M ∧ ‖((τ j)⁻¹ : Fˣ).val‖ ≤ M) : glMaxNorm (d.torusZ τ) ≤ M := by
  have hc : ∀ (σ : Fin d.r → Fˣ), (∀ j, ‖(σ j : F)‖ ≤ M ∧ ‖((σ j)⁻¹ : Fˣ).val‖ ≤ M) →
      ∀ i, ‖(d.torusCoeff σ i : F)‖ ≤ M := by
    intro σ hσ i
    unfold torusCoeff
    split_ifs
    · exact (hσ _).1
    · exact (hσ _).2
    · simpa using hM
  have hb : ∀ (σ : Fin d.r → Fˣ), (∀ j, ‖(σ j : F)‖ ≤ M ∧ ‖((σ j)⁻¹ : Fˣ).val‖ ≤ M) →
      ∀ v, ‖d.torusZ σ v‖ ≤ M * ‖v‖ := by
    intro σ hσ v
    rw [torusZ_apply, Prod.norm_def]
    have hv := norm_nonneg v
    refine max_le ((norm_fst_le v).trans (le_mul_of_one_le_left hv hM)) ?_
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [norm_mul]
    exact mul_le_mul (hc σ hσ i) (d.norm_coord_le v i) (norm_nonneg _) (by linarith)
  refine glMaxNorm_le_of_bound _ hM (hb τ h) fun v => ?_
  rw [torusZ_inv]
  exact hb τ⁻¹ (fun j => by simpa [and_comm] using h j) v

/-! ## 5. The first inequality of Thesis Prop. 8.1.1(iii) for `G`: reduction to `G₀` -/

section Cone

variable {n l : ℕ} {b : Basis (Fin n) F d.V0} (hb : IsOrthoBasis d.Q0 b) {ν : F}
  (hf : IsFrame d.Q0 b ν l)

include hb in
theorem inv_multiTorus_mem_SOGrp (j : ℕ) (t : List Fˣ) :
    (multiTorus hb hf j t)⁻¹ ∈ SOGrp d.Q0 := by
  rw [SOGrp_eq_specialOrthogonalGroup]
  exact inv_mem (multiTorus_mem_fixer hb hf t j).1

/-- Elements of `GGPData.G₀`'s image in `SO(W) × SO(V₀)` built from a `G`-element's `W`-part. -/
def coneBase (y1 : SOGrp d.QW) (t : List Fˣ) : d.base.GbarGrp :=
  (y1, ⟨(multiTorus hb hf 0 t)⁻¹, d.inv_multiTorus_mem_SOGrp hb hf 0 t⟩)

-- The products in `SO(W) × SO(V)` make instance search slow here.
set_option maxHeartbeats 800000 in
include hb in
/-- **Thesis Prop. 8.1.1(iii), first inequality (BP (6.4.1)), for `G`, at the level of
`SO(W) × SO(V)`**, on the cone `A₀⁺ A`: for `h ∈ H` and `y = (y_W, y_V)` with
`y_V = a(τ) (y₀ ⊕ 1)`, `a(τ)` in the split torus `A` of the Levi `G₀ A` (any `τ`, no chamber
condition) and `y₀ = (multiTorus hb hf 0 t)⁻¹` in the expanding chamber of `SO(V₀)`
(`InChamber`), and `y_W` arbitrary: `σ_{SO}(P̄ h) + σ_{SO}(y) ≤ C σ_{SO}(P̄(h) y)`.

Proof (Thesis proof of Prop. 8.1.1(iii), reduction to `G₀`): `P̄(h) y` preserves the flag
`Z_•`; its compression to `Z_r^⊥ / Z_r ≅ V₀` is the `G₀`-element `(P(h_W) ⊕ 1) y₀`
(`pi0_compress`), and its diagonal entries on `z_1, …, z_r` are `τ` (`compress_coord`); so
`σ(a(τ))` and `σ_{SO}` of the `G₀`-element are `≪ σ_{SO}(P̄(h) y)`, and the codimension-one case
(`logNormSO_add_le_of_chamber` for the datum `d.base` of `(W, V₀)`) bounds `σ(y₀)`. -/
theorem logNormSO_add_le_of_cone (hb0 : ∀ i : Fin n, (i : ℕ) = 0 → (b i).1 = 0) :
    ∃ C, 0 ≤ C ∧ ∀ h ∈ d.H, ∀ y : d.GbarGrp, ∀ (τ : Fin d.r → Fˣ) (t : List Fˣ),
      InChamber n l 0 t →
      (y.2 : d.V ≃ₗ[F] d.V) = d.torusZ τ * d.extV0 (multiTorus hb hf 0 t)⁻¹ →
      d.logNormSO (d.Pbar h) + d.logNormSO y ≤ C * d.logNormSO (d.Pbar h * y) := by
  obtain ⟨C₀, hC₀, hI⟩ := d.base.logNormSO_add_le_of_chamber hb hf rfl hb0
  refine ⟨1 + 2 * (3 + C₀), by positivity, fun h hh y τ t ht hy => ?_⟩
  set y0 : d.V0 ≃ₗ[F] d.V0 := (multiTorus hb hf 0 t)⁻¹
  set g : d.V ≃ₗ[F] d.V := ((d.Pbar h * y).2 : d.V ≃ₗ[F] d.V)
  have hg : g = specP d.QV (d.snd h) * (d.torusZ τ * d.extV0 y0) := by
    rw [← hy]; rfl
  have hM := one_le_glMaxNorm g
  -- the torus part
  have hτ : ∀ j, ‖(τ j : F)‖ ≤ glMaxNorm g ∧ ‖((τ j)⁻¹ : Fˣ).val‖ ≤ glMaxNorm g := by
    intro j
    have hz := d.norm_zV_le ((j : ℤ) + 1)
    constructor
    · have e := d.compress_coord hh τ y0 j
      rw [← hg] at e
      rw [← e]
      refine (d.norm_coord_le _ _).trans ((norm_apply_le_glMaxNorm g _).trans ?_)
      exact mul_le_of_le_one_right (by linarith) hz
    · have e := d.compress_coord_inv hh τ y0 j
      rw [← hg] at e
      rw [← e]
      refine (d.norm_coord_le _ _).trans ((norm_inv_apply_le_glMaxNorm g _).trans ?_)
      exact mul_le_of_le_one_right (by linarith) hz
  have hT := d.glMaxNorm_torusZ_le τ hM hτ
  -- the `G₀` part
  set h₀ : d.base.G := d.base.diag (d.fst h)
  have hh₀ : h₀ ∈ d.base.H := d.base.diag_mem_H _
  set y₀ := d.coneBase hb hf y.1 t
  have key := hI h₀ hh₀ y₀ t ht rfl
  have e2 : (((d.base.Pbar h₀ * y₀).2 : d.V0 ≃ₗ[F] d.V0)) =
      d.base.extZ (specP d.QW (d.fst h)) * y0 := by
    have := d.base.Pbar_snd_of_mem_H rfl hh₀
    show ((d.base.Pbar h₀).2 : d.V0 ≃ₗ[F] d.V0) * y0 = _
    rw [this]; rfl
  have hV0 : glMaxNorm ((d.base.Pbar h₀ * y₀).2 : d.V0 ≃ₗ[F] d.V0) ≤ glMaxNorm g := by
    rw [e2]
    refine glMaxNorm_le_of_bound _ hM (fun x => ?_) (fun x => ?_)
    · rw [LinearEquiv.mul_apply, ← d.pi0_compress hh τ y0 x, ← hg]
      exact (d.norm_pi0_le _).trans ((norm_apply_le_glMaxNorm g _).trans
        (mul_le_mul_of_nonneg_left (d.norm_iota0_le x) (by linarith)))
    · rw [mul_inv_rev, LinearEquiv.mul_apply, ← d.pi0_compress_inv hh τ y0 x, ← hg]
      exact (d.norm_pi0_le _).trans ((norm_inv_apply_le_glMaxNorm g _).trans
        (mul_le_mul_of_nonneg_left (d.norm_iota0_le x) (by linarith)))
  have e1 : (((d.base.Pbar h₀ * y₀).1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))) =
      (((d.Pbar h * y).1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))) := rfl
  -- logs
  set B := max (glMaxNorm (((d.Pbar h * y).1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))))
    (glMaxNorm g)
  have hB : 1 ≤ B := le_max_of_le_right hM
  have hσ : d.logNormSO (d.Pbar h * y) = 1 + Real.log B := rfl
  have hσ₀ : d.base.logNormSO (d.base.Pbar h₀ * y₀) ≤ 1 + Real.log B := by
    unfold logNormSO
    rw [e1]
    have h1 : 1 ≤ max (glMaxNorm (((d.Pbar h * y).1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))))
        (glMaxNorm ((d.base.Pbar h₀ * y₀).2 : d.V0 ≃ₗ[F] d.V0)) :=
      le_max_of_le_left (one_le_glMaxNorm _)
    have := Real.log_le_log (by linarith) (max_le_max le_rfl hV0)
    linarith
  set A₀ := max (glMaxNorm (y.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))) (glMaxNorm y0)
  have hA₀ : 1 ≤ A₀ := le_max_of_le_left (one_le_glMaxNorm _)
  have hy₀ : d.base.logNormSO y₀ = 1 + Real.log A₀ := rfl
  have hA : max (glMaxNorm (y.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)))
      (glMaxNorm (y.2 : d.V ≃ₗ[F] d.V)) ≤ 3 * glMaxNorm g * A₀ := by
    have hy2 : glMaxNorm (y.2 : d.V ≃ₗ[F] d.V) ≤ glMaxNorm g * (3 * glMaxNorm y0) := by
      rw [hy]
      exact (glMaxNorm_mul_le _ _).trans (mul_le_mul hT (d.glMaxNorm_extV0_le y0)
        (zero_le_one.trans (one_le_glMaxNorm _)) (by linarith))
    refine max_le ?_ (hy2.trans ?_)
    · calc glMaxNorm (y.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) ≤ A₀ := le_max_left _ _
        _ = 1 * 1 * A₀ := by ring
        _ ≤ 3 * glMaxNorm g * A₀ := by gcongr <;> linarith
    · calc glMaxNorm g * (3 * glMaxNorm y0) = 3 * glMaxNorm g * glMaxNorm y0 := by ring
        _ ≤ 3 * glMaxNorm g * A₀ := by gcongr; exact le_max_right _ _
  have hlogy : d.logNormSO y ≤ Real.log 3 + Real.log (glMaxNorm g) + d.base.logNormSO y₀ := by
    rw [hy₀]
    unfold logNormSO
    have h1 : 1 ≤ max (glMaxNorm (y.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)))
        (glMaxNorm (y.2 : d.V ≃ₗ[F] d.V)) := le_max_of_le_left (one_le_glMaxNorm _)
    have := Real.log_le_log (by linarith) hA
    rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by norm_num) (by linarith)]
      at this
    linarith
  have hlogM : Real.log (glMaxNorm g) ≤ Real.log B := Real.log_le_log (by linarith) (le_max_right _ _)
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have hlogB := Real.log_nonneg hB
  have hy₀' : d.base.logNormSO y₀ ≤ C₀ * (1 + Real.log B) := by
    have h0 := d.base.one_le_logNormSO (d.base.Pbar h₀)
    calc d.base.logNormSO y₀ ≤ C₀ * d.base.logNormSO (d.base.Pbar h₀ * y₀) := by linarith
      _ ≤ C₀ * (1 + Real.log B) := mul_le_mul_of_nonneg_left hσ₀ hC₀
  have hyfin : d.logNormSO y ≤ (3 + C₀) * d.logNormSO (d.Pbar h * y) := by
    rw [hσ]; nlinarith
  have hh' : d.logNormSO (d.Pbar h) ≤ d.logNormSO (d.Pbar h * y) + d.logNormSO y := by
    have := d.logNormSO_mul_le (d.Pbar h * y) y⁻¹
    rwa [mul_inv_cancel_right, logNormSO_inv] at this
  have h1 := d.one_le_logNormSO (d.Pbar h * y)
  nlinarith

end Cone

end GGPData

end GSpinGGP
