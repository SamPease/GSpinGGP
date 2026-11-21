/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Analytic
import GSpinGGP.TraceFormula.GoodParabolic
import TauCeti.LinearAlgebra.Determinant.Basic
import GSpinGGP.Foundations.LogNormCompact
import GSpinGGP.GGP.Cocharacter

/-!
# The weak Cartan decomposition of `G` and the reduction from `G` to `G₀`

Let `d` be a GGP datum, `V = W ⊕ ⟨z₀⟩ ⊕ ⟨z_{±1}, …, z_{±r}⟩`, `V₀ = W ⊕ ⟨z₀⟩` (`GGPData.V0`,
`iota0 : V₀ → V`, `pi0 : V → V₀`), `G₀ = GSpin(W) × GSpin(V₀)` (the datum `GGPData.base`, with
`r = 0`), `P = GSpin(W) × P_V` the stabilizer of `⟨z_r⟩ ⊂ ⋯ ⊂ ⟨z_r, …, z_1⟩` and `P = M N` with
`M = G₀ A` (Thesis §5.2, §8.3). Everything is done at the level of `Ḡ = SO(W) × SO(V)`
(`GGPData.Pbar`, kernel the central scalars) and pulled back to `G`.

* `GGPData.extV0`: `SO(V₀) ⊆ SO(V)`, `g ↦ g ⊕ 1`; `GGPData.torusZ`: the split torus `A ≅ GL₁^r`
  of the Levi, `a(τ) z_{±k} = τ_{k-1}^{±1} z_{±k}`.
* **Reduction from `G` to `G₀`** (Thesis proof of Prop. 8.1.1(iii), Section 8):
  `GGPData.logNormSO_add_le_of_cone` is the first inequality of Thesis Prop. 8.1.1(iii)
  (BP (6.4.1)) for `G` on the cone `A₀⁺ A(F)`. For `h ∈ H` and `y` in the cone, `P̄(h) y`
  preserves the flag; its compression to `Z_r^⊥/Z_r ≅ V₀` is a `G₀`-element (`pi0_compress`) and
  its diagonal entries on `z_1, …, z_r` are the torus coordinates (`compress_coord`), so the
  codimension-one case `logNormSO_add_le_of_chamber` (for `d.base`) applies.
  `GGPData.logNormModAG_le_of_cone` and `GGPData.logNormModAG_le_fiberInf_of_cone` are the forms
  modulo `A_G` and `σ_{A_G\G} ≪ σ_{H\G}` (Thesis Prop. 8.4.1(ii)(b), nontrivial half).
* `GGPData.exists_isCompact_lift`: bounded subsets of `Ḡ` lift to compact subsets of `G(F)`
  modulo the scalars (log-norm balls are compact, `isCompact_logNorm_le`).
* **Weak Cartan decomposition** (Thesis Lemma 8.3.2(ii)): `GGPData.exists_weakCartan` for `G`,
  from its `SO`-level form `GGPData.exists_weakCartan_SO` (`sorry`, with a proof sketch).
* `GGPData.weakCartanData`: the `WeakCartanData d.mkHG d.logNormModAG` with cone
  `S = A_G A₀⁺ A(F)` (`GGPData.cone`), taking the polynomial growth of the cone modulo `A_G`
  (BP (6.7.12)) as hypotheses; `GGPData.prop_6_7_1_iii_of_growth` feeds it to
  `prop_6_7_1_iii_of_weakCartanData`.

The good pair is the explicit one of `weakCartan_G0_SO` (frame `b` of `V₀` with `b 0 ∈ ⟨z₀⟩`).
Only `F` `p`-adic is treated.
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

/-- `polar(ι₀ x, u) = 0` when `π₀ u = 0` (`u ∈ ⟨z_{±1}, …, z_{±r}⟩`). -/
theorem polar_iota0_of_pi0_eq_zero (x : d.V0) {u : d.V} (hu : d.pi0 u = 0) :
    polar d.QV (d.iota0 x) u = 0 := by
  have hu1 : u.1 = 0 := congrArg Prod.fst hu
  have hu2 : u.2 ⟨d.r, by omega⟩ = 0 := by
    have := congrFun (congrArg Prod.snd hu) 0
    simpa [pi0, zvec] using this
  have e : d.iota0 x = ((x.1, 0) : d.V) + x.2 0 • d.zV 0 := by
    rw [iota0_apply, zV]; ext <;> simp
  rw [e, polar_add_left, polar_smul_left, polar_eq_two_mul_bform d.QV (d.zV 0),
    bform_comm, bform_zV_eq _ _ (by simp)]
  simp only [polar_prod, hu1, polar_zero_right, polar_zero_left, add_zero, sub_zero]
  rw [show (⟨(d.r : ℤ).toNat, by omega⟩ : Fin (2 * d.r + 1)) = ⟨d.r, by omega⟩ from
    Fin.ext (by simp), hu2]
  simp

theorem QV_iota0_add (x : d.V0) {u : d.V} (hu : d.pi0 u = 0) :
    d.QV (d.iota0 x + u) = d.Q0 x + d.QV u := by
  rw [QuadraticMap.map_add d.QV, d.polar_iota0_of_pi0_eq_zero x hu, add_zero, QV_iota0]

/-- `g ⊕ 1 ∈ SO(V)` for `g ∈ SO(V₀)`. -/
theorem extV0_mem_SOGrp {g : d.V0 ≃ₗ[F] d.V0} (hg : g ∈ SOGrp d.Q0) : d.extV0 g ∈ SOGrp d.QV := by
  refine ⟨fun v => ?_, ?_⟩
  · have hu : d.pi0 (v - d.iota0 (d.pi0 v)) = 0 := by rw [map_sub, pi0_iota0, sub_self]
    have e1 : d.extV0 g v = d.iota0 (g (d.pi0 v)) + (v - d.iota0 (d.pi0 v)) := by
      rw [extV0_apply, map_sub]; abel
    have e2 : v = d.iota0 (d.pi0 v) + (v - d.iota0 (d.pi0 v)) := by abel
    rw [e1, d.QV_iota0_add _ hu, hg.1]
    conv_rhs => rw [e2, d.QV_iota0_add _ hu]
  · have e : ((d.extV0 g : d.V ≃ₗ[F] d.V) : d.V →ₗ[F] d.V) =
        1 + d.iota0 ∘ₗ (((g : d.V0 →ₗ[F] d.V0) - LinearMap.id) ∘ₗ d.pi0) := rfl
    rw [e, LinearMap.det_one_add_comp_comm]
    have e2 : ((g : d.V0 →ₗ[F] d.V0) - LinearMap.id) ∘ₗ d.pi0 ∘ₗ d.iota0 =
        (g : d.V0 →ₗ[F] d.V0) - 1 := by
      ext x <;> simp [pi0_iota0]
    rw [LinearMap.comp_assoc, e2, add_sub_cancel]
    exact hg.2

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

theorem torusCoeff_mul_rev (τ : Fin d.r → Fˣ) (i : Fin (2 * d.r + 1)) :
    d.torusCoeff τ i * d.torusCoeff τ i.rev = 1 := by
  unfold torusCoeff
  have := i.2
  simp only [Fin.val_rev]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 <;> first
    | omega
    | (rw [mul_inv_eq_one]; congr 1; ext; simp only [Fin.val_mk]; omega)
    | (rw [inv_mul_eq_one]; congr 1; ext; simp only [Fin.val_mk]; omega)
    | (simp; done)

/-- `a(τ) ∈ SO(V)`. -/
theorem torusZ_mem_SOGrp (τ : Fin d.r → Fˣ) : d.torusZ τ ∈ SOGrp d.QV := by
  refine ⟨fun v => ?_, ?_⟩
  · change d.QW v.1 + d.QZ (fun i => (d.torusCoeff τ i : F) * v.2 i) = d.QW v.1 + d.QZ v.2
    congr 1
    simp only [QZ, splitOddForm, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    unfold splitOddMatrix
    split_ifs with hac
    · have hc : c = a.rev := Fin.ext (by simp [Fin.val_rev]; omega)
      subst hc
      have := d.torusCoeff_mul_rev τ a
      have h' : (d.torusCoeff τ a : F) * (d.torusCoeff τ a.rev : F) = 1 := by
        rw [← Units.val_mul, this, Units.val_one]
      linear_combination (v.2 a * (d.ν : F) * v.2 a.rev) * h'
    · simp
  · have e : ((d.torusZ τ : d.V ≃ₗ[F] d.V) : d.V →ₗ[F] d.V) = LinearMap.prodMap LinearMap.id
        (Matrix.toLin' (Matrix.diagonal fun i => (d.torusCoeff τ i : F))) := by
      refine LinearMap.ext fun v => Prod.ext rfl (funext fun i => ?_)
      simp [torusZ_apply, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
    rw [e, LinearMap.det_prodMap, LinearMap.det_id, one_mul, LinearMap.det_toLin',
      Matrix.det_diagonal]
    refine Finset.prod_involution (fun i _ => i.rev)
      (fun i _ => by rw [← Units.val_mul, d.torusCoeff_mul_rev, Units.val_one])
      (fun i _ hi h => hi ?_) (fun _ _ => Finset.mem_univ _) (fun i _ => Fin.rev_rev i)
    have hlt : d.r < 2 * d.r + 1 := by omega
    have : (i : ℕ) = d.r := by
      have := congrArg Fin.val h; simp only [Fin.val_rev] at this; omega
    rw [show i = ⟨d.r, hlt⟩ from Fin.ext this, torusCoeff_r, Units.val_one]

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
theorem specP_snd_eq_extZ_mul_nPart {h : d.G} :
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
  rw [specP_snd_eq_extZ_mul_nPart]
  simp only [LinearEquiv.mul_apply, extV0_iota0, torusZ_iota0, pi0_extZ]
  rw [d.pi0_specP_N_iota0 hh]

include hh in
/-- **Compression to `V₀`** (inverse). -/
theorem pi0_compress_inv (x : d.V0) :
    d.pi0 ((specP d.QV (d.snd h) * (d.torusZ τ * d.extV0 y0))⁻¹ (d.iota0 x)) =
      y0⁻¹ ((d.base.extZ (specP d.QW (d.fst h)))⁻¹ x) := by
  rw [specP_snd_eq_extZ_mul_nPart, mul_inv_rev, mul_inv_rev, mul_inv_rev, ← map_inv d.extZ,
    ← map_inv (specP d.QV), ← map_inv d.extV0, torusZ_inv]
  simp only [LinearEquiv.mul_apply, extZ_iota0, pi0_extV0, pi0_torusZ]
  rw [d.pi0_specP_N_iota0 (d.N.inv_mem hh), map_inv]

include hh in
/-- **Diagonal entries on `Z₊`** (forward): the `z_{j+1}`-coordinate of `P(h_V) a z_{j+1}` is
`τ_j`. -/
theorem compress_coord (j : Fin d.r) :
    ((specP d.QV (d.snd h) * (d.torusZ τ * d.extV0 y0)) (d.zV ((j : ℤ) + 1))).2
      ⟨d.r + j + 1, by omega⟩ = τ j := by
  rw [specP_snd_eq_extZ_mul_nPart]
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
  rw [specP_snd_eq_extZ_mul_nPart, mul_inv_rev, mul_inv_rev, mul_inv_rev, ← map_inv d.extZ,
    ← map_inv (specP d.QV), ← map_inv d.extV0, torusZ_inv]
  have e1 : d.extZ (specP d.QW (d.fst h))⁻¹ (d.zV ((j : ℤ) + 1)) = d.zV ((j : ℤ) + 1) := by
    simp [zV, extZ]
  simp only [LinearEquiv.mul_apply, e1, extV0_coord, torusZ_coord]
  have := d.specP_N_coord (d.N.inv_mem hh) j 1
  rw [one_smul] at this
  rw [this, mul_one, Pi.inv_apply]

end Compress

/-! ## 4. Norm bounds -/

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

/-- The element `(y₁, (multiTorus hb hf 0 t)⁻¹)` of `SO(W) × SO(V₀)` (the group `Ḡ₀` of the datum
`d.base`): the `G₀`-part of a point of the cone with `W`-component `y₁`. -/
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

The Thesis proof of Prop. 8.1.1(iii) reduces (6.4.1) to `G₀` through the inequality
`σ(n) + σ(a) + σ(h₀a₀) ≪ σ(n h₀ a a₀)` (`a ∈ A(F)`, `a₀ ∈ A₀⁺`); the `σ(a) + σ(h₀a₀)` part is
proved here as follows. `P̄(h) y` preserves the flag
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

include hb in
/-- **Thesis Prop. 8.1.1(iii), first inequality, for `G`, modulo `A_G`**, on the cone
`A₀⁺ A`, in the form used for Thesis Prop. 8.4.1(ii)(b) (BP (6.7.6)):
`σ_{A_G\G}(x) ≤ C σ_{A_G\G}(h x)` for `h ∈ H` and `x ∈ G` with
`P̄(x)_V = a(τ) (y₀ ⊕ 1)`, `y₀ = (multiTorus hb hf 0 t)⁻¹` in the expanding chamber of
`SO(V₀)`, `τ` arbitrary (no condition on the `W`-component). For `r = 0` this is
`logNormModAG_le_of_chamber` in the coordinates of `V₀ ⊆ V`. -/
theorem logNormModAG_le_of_cone (hb0 : ∀ i : Fin n, (i : ℕ) = 0 → (b i).1 = 0) :
    ∃ C, 0 ≤ C ∧ ∀ h ∈ d.H, ∀ x : d.G, ∀ (τ : Fin d.r → Fˣ) (t : List Fˣ),
      InChamber n l 0 t →
      ((d.Pbar x).2 : d.V ≃ₗ[F] d.V) = d.torusZ τ * d.extV0 (multiTorus hb hf 0 t)⁻¹ →
      infLeft (logNorm F d.G) d.AG x ≤ C * infLeft (logNorm F d.G) d.AG (h * x) := by
  obtain ⟨C₀, hC₀, hI⟩ := d.logNormSO_add_le_of_cone hb hf hb0
  obtain ⟨C, hC, h⟩ := d.logNormModAG_le_of_logNormSO
    (P := fun g => ∃ (τ : Fin d.r → Fˣ) (t : List Fˣ), InChamber n l 0 t ∧
      g = d.torusZ τ * d.extV0 (multiTorus hb hf 0 t)⁻¹) hC₀
    fun h hh y ⟨τ, t, ht, hy⟩ => hI h hh y τ t ht hy
  exact ⟨C, hC, fun h' hh x τ t ht hx => h h' hh x ⟨τ, t, ht, hx⟩⟩

include hb in
/-- **`σ_{A_G\G} ≪ σ_{H\G}` on the cone** (the nontrivial half of Thesis Prop. 8.4.1(ii)(b),
BP Prop. 6.7.1(ii)(b)), in the form of the field `le_fiberInf` of `WeakCartanData`:
`σ_{A_G\G}(x) ≤ C σ_{H\G}(x)` for `x` as in `logNormModAG_le_of_cone`, with
`σ_{H\G} = fiberInf σ_{A_G\G} mkHG` (`logNormHG_eq_fiberInf_logNormModAG`). -/
theorem logNormModAG_le_fiberInf_of_cone (hb0 : ∀ i : Fin n, (i : ℕ) = 0 → (b i).1 = 0) :
    ∃ C, 0 ≤ C ∧ ∀ x : d.G, ∀ (τ : Fin d.r → Fˣ) (t : List Fˣ), InChamber n l 0 t →
      ((d.Pbar x).2 : d.V ≃ₗ[F] d.V) = d.torusZ τ * d.extV0 (multiTorus hb hf 0 t)⁻¹ →
      d.logNormModAG x ≤ C * fiberInf d.logNormModAG d.mkHG (d.mkHG x) := by
  obtain ⟨C, hC, hI⟩ := d.logNormModAG_le_of_cone hb hf hb0
  refine ⟨C, hC, fun x τ t ht hx => ?_⟩
  rw [← logNormHG_eq_fiberInf_logNormModAG]
  exact d.logNormModAG_le_logNormHG_of_forall hC fun h hh => hI h hh x τ t ht hx

end Cone

/-! ## 6. The lift of bounded sets from `Ḡ` -/

/-- **Lift of bounded sets along `P̄ : G → Ḡ`**: for `M`, there is a compact `K ⊆ G(F)` such that
every `g` with `σ_{Ḡ}(P̄ g) ≤ M` is `z⁻¹ k` with `z` a central scalar and `k ∈ K`
(`exists_logNorm_scalars_mul_le`). -/
theorem exists_isCompact_lift (M : ℝ) :
    ∃ K : Set d.G, IsCompact K ∧ ∀ g : d.G, d.logNormSO (d.Pbar g) ≤ M →
      ∃ z ∈ d.scalars, z * g ∈ K := by
  obtain ⟨C, hC, hz⟩ := d.exists_logNorm_scalars_mul_le
  refine ⟨{g | logNorm F d.G g ≤ C * M}, isCompact_logNorm_le d.isClosed_G _, fun g hg => ?_⟩
  obtain ⟨z, hz, hzg⟩ := hz g
  exact ⟨z, hz, hzg.trans (mul_le_mul_of_nonneg_left hg hC)⟩

/-! ## 6b. The Levi decomposition of `P_V` in coordinates -/

/-- The standard basis of `V = W × Z` (`W = F^m`, `Z = F^{2r+1}`). -/
def stdBasis : Basis (Fin d.m ⊕ Fin (2 * d.r + 1)) F d.V :=
  (Pi.basisFun F (Fin d.m)).prod (Pi.basisFun F (Fin (2 * d.r + 1)))

/-- The weights of the standard basis for the flag `⟨z_r⟩ ⊂ ⋯ ⊂ ⟨z_r, …, z_1⟩`: `z_k` has
weight `k`, and `W` weight `0`. -/
def stdWt : Fin d.m ⊕ Fin (2 * d.r + 1) → ℤ := Sum.elim (fun _ => 0) fun i => (i : ℤ) - d.r

theorem stdBasis_inr (i : Fin (2 * d.r + 1)) : d.stdBasis (Sum.inr i) = d.zV ((i : ℤ) - d.r) := by
  refine Prod.ext (Basis.prod_apply_inr_fst _ _ _) ?_
  rw [stdBasis, Basis.prod_apply_inr_snd, Pi.basisFun_apply, zV]
  ext j
  simp only [zvec, Pi.single_apply]
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; apply h2; omega) | (exfalso; apply h1; ext; omega)

theorem stdBasis_inl (j : Fin d.m) : d.stdBasis (Sum.inl j) = (Pi.single j 1, 0) :=
  Prod.ext (by rw [stdBasis, Basis.prod_apply_inl_fst, Pi.basisFun_apply])
    (Basis.prod_apply_inl_snd _ _ _)

theorem flag_sub_eq_flagWt (i : Fin (d.flag.len + 1)) :
    d.flag.sub i = flagWt d.flag ((d.flag.len : ℤ) + 1 - i) := by
  have hi2 := i.2
  by_cases hi : (i : ℕ) = 0
  · rw [show i = 0 from Fin.ext hi, d.flag.sub_zero, d.flag.flagWt_eq_bot (by simp)]
  · rw [d.flag.flagWt_of_pos (by omega)]
    congr 1
    ext
    simp only [IsotropicFlag.idx]
    omega

theorem mem_flag_sub_of_le {k : ℕ} (hk : 1 ≤ k) (hkr : k ≤ d.r) {i : Fin (d.flag.len + 1)}
    (hi : d.r - k < (i : ℕ)) : d.zV (k : ℤ) ∈ d.flag.sub i :=
  Submodule.subset_span ⟨⟨d.r - k, hi⟩, by simp only; congr 1; push_cast [hkr]; ring⟩

/-- The standard basis splits the weight filtration of `d.flag`. -/
theorem isFlagSplitting_stdBasis : IsFlagSplitting d.flag d.stdBasis d.stdWt where
  mem := by
    have hl : d.flag.len = d.r := rfl
    rintro (j | i)
    · rw [stdBasis_inl, stdWt, Sum.elim_inl, d.flag.flagWt_zero]
      exact d.inl_mem_orthogonal_top _
    · rw [stdBasis_inr, stdWt, Sum.elim_inr]
      have hi := i.2
      rcases lt_trichotomy (i : ℤ) d.r with h | h | h
      · -- negative weight: `z_k ⊥ Z_{r+k}`
        rw [d.flag.flagWt_of_nonpos (by omega), LinearMap.BilinForm.mem_orthogonal_iff]
        intro u hu
        refine Submodule.span_induction (p := fun u _ => bform d.QV u (d.zV ((i : ℤ) - d.r)) = 0)
          ?_ (by simp) (fun x y _ _ hx hy => by simp only [map_add, LinearMap.add_apply, hx, hy,
            add_zero]) (fun c x _ hx => by simp only [map_smul, LinearMap.smul_apply, hx,
            smul_zero]) hu
        rintro _ ⟨j, rfl⟩
        have hj := j.2
        simp only [IsotropicFlag.idx] at hj
        rw [bform_QV_zV, bform_splitOddForm_zvec _ _ (by rw [abs_le]; constructor <;> omega)
          (by rw [abs_le]; constructor <;> omega), if_neg (by omega)]
      · rw [show (i : ℤ) - d.r = 0 by omega, d.flag.flagWt_zero]
        exact d.zV_zero_mem_orthogonal_top
      · rw [d.flag.flagWt_of_pos (by omega)]
        have := d.mem_flag_sub_of_le (k := (i : ℕ) - d.r) (by omega) (by omega)
          (i := d.flag.idx (d.flag.len + 1 - ((i : ℤ) - d.r)))
          (by simp only [IsotropicFlag.idx]; change _ < min _ d.r; omega)
        rwa [show (((i : ℕ) - d.r : ℕ) : ℤ) = (i : ℤ) - d.r by omega] at this
  repr_eq_zero := by
    have hl : d.flag.len = d.r := rfl
    intro w v hv i hi
    rcases i with j | i
    · simp only [stdWt, Sum.elim_inl] at hi
      rw [stdBasis, Basis.prod_repr_inl]
      rw [d.flag.flagWt_of_pos (show 1 ≤ w by omega)] at hv
      have := d.span_flag_le _ hv
      rw [this.1]; simp
    · simp only [stdWt, Sum.elim_inr] at hi
      rw [stdBasis, Basis.prod_repr_inr, Pi.basisFun_repr]
      by_cases hw : 1 ≤ w
      · rw [d.flag.flagWt_of_pos hw] at hv
        have := d.span_flag_le _ hv
        refine this.2 i ?_
        simp only [IsotropicFlag.idx]
        change (i : ℕ) < 2 * d.r + 1 - min _ d.r
        omega
      · rw [d.flag.flagWt_of_nonpos (by omega), LinearMap.BilinForm.mem_orthogonal_iff] at hv
        have hk : |(d.r : ℤ) - i| ≤ d.r := by rw [abs_le]; have := i.2; constructor <;> omega
        have hmem : d.zV ((d.r : ℤ) - i) ∈ d.flag.sub (d.flag.idx (d.flag.len + w)) :=
          Submodule.subset_span ⟨⟨i, by simp only [IsotropicFlag.idx]; change _ < min _ d.r; omega⟩,
            rfl⟩
        have h0 := hv _ hmem
        rw [bform_comm, bform_zV_eq _ _ hk] at h0
        have e : (⟨((d.r : ℤ) - ((d.r : ℤ) - i)).toNat, by omega⟩ : Fin (2 * d.r + 1)) = i :=
          Fin.ext (by simp)
        rw [e] at h0
        exact (mul_eq_zero.mp h0).resolve_left d.ν.ne_zero
  orth := by
    rintro (j | i) (j' | i') hne
    · simp [stdWt] at hne
    · rw [stdBasis_inl, stdBasis_inr, zV, bform_prod]; simp
    · rw [stdBasis_inl, stdBasis_inr, zV, bform_prod]; simp
    · simp only [stdWt, Sum.elim_inr] at hne
      have hi := i.2; have hi' := i'.2
      rw [stdBasis_inr, stdBasis_inr, bform_QV_zV, bform_splitOddForm_zvec _ _
        (by rw [abs_le]; constructor <;> omega) (by rw [abs_le]; constructor <;> omega),
        if_neg hne]
  sum_wt := by
    rw [Fintype.sum_sum_type]
    simp only [stdWt, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, zero_add]
    refine Finset.sum_involution (fun i _ => i.rev) (fun i _ => by simp [Fin.val_rev]; omega)
      (fun i _ hi h => hi ?_) (fun _ _ => Finset.mem_univ _) (fun i _ => Fin.rev_rev i)
    have := congrArg Fin.val h; simp only [Fin.val_rev] at this; omega

/-! ## 7. The weak Cartan decomposition of `G` (Thesis Lemma 8.3.2(ii)) and the weak Cartan
data of `H\G/A_G` -/

section WeakCartanG

variable {n l : ℕ} {b : Basis (Fin n) F d.V0} (hb : IsOrthoBasis d.Q0 b) {ν : F}
  (hf : IsFrame d.Q0 b ν l)

/-- **The cone `A₀⁺ A(F)` in `SO(W) × SO(V)`** (Thesis §8.3, Lemma 8.3.2(ii)), for the good minimal
parabolic `P̄₀ = P̄_W × P̄_{V₀}` of `G₀` defined by the frame `b` of `V₀` (as in
`weakCartan_G0_SO`) and the split torus `A` of the Levi `G₀ A` (`torusZ`): the `y = (y_W, y_V)`
with `y_W ⊕ 1 = (multiTorus hb hf 1 s)⁻¹` on `V₀` and `y_V = a(τ) (y₀ ⊕ 1)`,
`y₀ = (multiTorus hb hf 0 t)⁻¹`, `s`, `t` in the contracting chambers and `τ` arbitrary. -/
def coneSO : Set d.GbarGrp :=
  {y | ∃ (s t : List Fˣ) (τ : Fin d.r → Fˣ), InChamber n l 1 s ∧ InChamber n l 0 t ∧
    d.base.extZ (y.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) = (multiTorus hb hf 1 s)⁻¹ ∧
    (y.2 : d.V ≃ₗ[F] d.V) = d.torusZ τ * d.extV0 (multiTorus hb hf 0 t)⁻¹}

/-- **The cone `A_G A₀⁺ A(F)` of `G(F)`**: the preimage of `coneSO` under `P̄`. It contains the
central scalars `Z(F) = ker P̄`, and `A_G · cone = cone` in all cases: if neither `W` nor `V` is a
hyperbolic plane then `P̄(A_G) = 1`; if `W` is a hyperbolic plane then `P̄(A_G) = SO(W) × 1` is the
split torus of `SO(W)`, which has no chamber condition; if `V` is a hyperbolic plane (then `r = 0`,
`dim W = 1`, `l = 1`) then `P̄(A_G) = 1 × SO(V)` and the single coordinate `t₀` of the cone is
unconstrained. -/
def cone : Set d.G := d.Pbar ⁻¹' d.coneSO hb hf

/-! ### Ingredients of the weak Cartan decomposition of `Ḡ` -/

omit hb hf in
/-- `glMax` is continuous on `GL(E)` (for the topology of `E ≃ₗ[F] E` induced by `(g, g⁻¹)`). -/
theorem continuous_glMaxNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace F E]
    [FiniteDimensional F E] : Continuous (glMaxNorm : (E ≃ₗ[F] E) → ℝ) := by
  haveI : IsModuleTopology F (Module.End F E) := ⟨rfl⟩
  have h0 : Continuous fun f : Module.End F E => LinearMap.toContinuousLinearMap f :=
    IsModuleTopology.continuous_of_linearMap
      (LinearMap.toContinuousLinearMap : (E →ₗ[F] E) ≃ₗ[F] (E →L[F] E)).toLinearMap
  have h1 : Continuous fun g : E ≃ₗ[F] E => LinearMap.toContinuousLinearMap (g : E →ₗ[F] E) :=
    h0.comp TauCeti.continuous_linearEquiv_toLinearMap
  have h2 : Continuous fun g : E ≃ₗ[F] E =>
      LinearMap.toContinuousLinearMap ((g⁻¹ : E ≃ₗ[F] E) : E →ₗ[F] E) :=
    h1.comp continuous_inv
  exact continuous_const.max (h1.norm.max h2.norm)

omit hb hf in
/-- `g ↦ g ⊕ 1` on `V₀ = W ⊕ ⟨z₀⟩` is injective. -/
theorem base_extZ_injective : Function.Injective (d.base.extZ) := fun f g h =>
  LinearEquiv.ext fun w => congrArg Prod.fst (LinearEquiv.congr_fun h ((w, 0) : d.V0))

omit hb hf in
/-- `(g ⊕ 1_{z₀}) ⊕ 1 = g ⊕ 1` on `V`. -/
theorem extV0_base_extZ (f : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) :
    d.extV0 (d.base.extZ f) = d.extZ f := by
  refine LinearEquiv.ext fun v => ?_
  rw [extV0_apply, extZ_apply]
  refine Prod.ext ?_ ?_
  · simp [pi0, iota0_apply, extZ_apply]
  · simp [pi0, iota0_apply, extZ_apply]

omit hb hf in
theorem torusZ_mul_extZ (τ : Fin d.r → Fˣ) (f : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) :
    d.torusZ τ * d.extZ f = d.extZ f * d.torusZ τ := by
  refine LinearEquiv.ext fun v => ?_
  rfl

include hb hf in
/-- **`fixer Q₀ b 1 = SO(W) ⊕ 1`** (converse of `extZ_mem_fixer`): an element of `SO(V₀)` fixing
`w₀ = b 0 ∈ ⟨z₀⟩` is `g_W ⊕ 1` with `g_W ∈ SO(W)`. -/
theorem exists_extZ_of_mem_fixer (hb0 : ∀ i : Fin n, (i : ℕ) = 0 → (b i).1 = 0)
    {g : d.V0 ≃ₗ[F] d.V0} (hg : g ∈ fixer d.Q0 b 1) :
    ∃ gW : SOGrp d.QW, d.base.extZ (gW : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) = g := by
  have hSO : ∀ {g : d.V0 ≃ₗ[F] d.V0}, g ∈ fixer d.Q0 b 1 → g ∈ SOGrp d.Q0 := fun hg => by
    rw [SOGrp_eq_specialOrthogonalGroup]; exact hg.1
  have hn : 0 < n := hf.idx_lt (Nat.zero_le l)
  -- `g` fixes `z₀`
  have hz : ∀ {g : d.V0 ≃ₗ[F] d.V0}, g ∈ fixer d.Q0 b 1 → g d.z00 = d.z00 := by
    intro g hg
    set i0 : Fin n := ⟨0, hn⟩
    have hfix : g (b i0) = b i0 := hg.2 i0 (by simp [i0])
    have h1 : (b i0).1 = 0 := hb0 i0 rfl
    have he : b i0 = (b i0).2 0 • d.z00 := by
      refine Prod.ext (by simp [h1, z00]) ?_
      simp only [z00, Prod.smul_snd]
      exact fin_one_eq _
    have hc : (b i0).2 0 ≠ 0 := by
      intro h0; rw [h0, zero_smul] at he; exact b.ne_zero i0 he
    rw [he, map_smul] at hfix
    exact smul_right_injective _ hc hfix
  -- `g` preserves `W × 0`
  have hW : ∀ {g : d.V0 ≃ₗ[F] d.V0}, g ∈ fixer d.Q0 b 1 → ∀ w : Fin d.m → F,
      (g ((w, 0) : d.V0)).2 = 0 := by
    intro g hg w
    apply d.snd_eq_zero_of_polar_z00
    have hiso := (hSO hg).1
    have : polar d.Q0 (g d.z00) (g ((w, 0) : d.V0)) = polar d.Q0 d.z00 (w, 0) := by
      simp only [polar, ← map_add, hiso]
    rw [hz hg] at this
    rw [this, polar_comm, polar_Q0_of_snd rfl]
    simp [z00]
  have hgi := inv_mem hg
  let f : (Fin d.m → F) →ₗ[F] (Fin d.m → F) :=
    LinearMap.fst F _ _ ∘ₗ (g : d.V0 →ₗ[F] d.V0) ∘ₗ LinearMap.inl F _ _
  let f' : (Fin d.m → F) →ₗ[F] (Fin d.m → F) :=
    LinearMap.fst F _ _ ∘ₗ ((g⁻¹ : d.V0 ≃ₗ[F] d.V0) : d.V0 →ₗ[F] d.V0) ∘ₗ LinearMap.inl F _ _
  have hf1 : ∀ w, g ((w, 0) : d.V0) = (f w, 0) := fun w => Prod.ext rfl (hW hg w)
  have hf2 : ∀ w, g⁻¹ ((w, 0) : d.V0) = (f' w, 0) := fun w => Prod.ext rfl (hW hgi w)
  let gW : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F) := LinearEquiv.ofLinearMap f f'
    (LinearMap.ext fun w => by
      have h := hf1 (f' w)
      rw [← hf2, show g ((g⁻¹ : d.V0 ≃ₗ[F] d.V0) ((w, 0) : d.V0)) = (w, 0) by
        rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl] at h
      exact (congrArg Prod.fst h).symm)
    (LinearMap.ext fun w => by
      have h := hf2 (f w)
      rw [← hf1, show (g⁻¹ : d.V0 ≃ₗ[F] d.V0) (g ((w, 0) : d.V0)) = (w, 0) by
        rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl] at h
      exact (congrArg Prod.fst h).symm)
  have hext : d.base.extZ gW = g := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨w, c⟩ := v
    have e : ((w, c) : d.V0) = (w, 0) + c 0 • d.z00 := by
      refine Prod.ext (by simp [z00]) ?_
      simp only [z00, Prod.snd_add, Prod.smul_snd, zero_add]
      exact fin_one_eq c
    rw [e, map_add, map_add, map_smul, map_smul, hz hg, hf1]
    simp only [extZ_apply, z00, map_zero]
    rfl
  refine ⟨⟨gW, fun w => ?_, ?_⟩, hext⟩
  · have := (hSO hg).1 ((w, 0) : d.V0)
    rw [hf1] at this
    show d.QW (f w) = d.QW w
    simpa [Q0] using this
  · have h1 := (hSO hg).2
    rw [← hext] at h1
    change LinearMap.det ((gW.prodCongr (LinearEquiv.refl F _) : d.V0 ≃ₗ[F] d.V0) :
      d.V0 →ₗ[F] d.V0) = 1 at h1
    rwa [LinearEquiv.coe_prodCongr, LinearMap.det_prodMap, LinearEquiv.refl_toLinearMap,
      LinearMap.det_id, mul_one] at h1

/-- **Iwasawa decomposition for `P = GSpin(W) × P_V`** at the level of `Ḡ`: `Ḡ = P̄(P) K̄`
with `K̄` bounded for `σ_{SO}`. -/
theorem exists_iwasawa_SO :
    ∃ M, ∀ y : d.GbarGrp, ∃ p : d.G, d.snd p ∈ flagStab d.flag ∧
      ∃ k : d.GbarGrp, d.logNormSO k ≤ M ∧ y = d.Pbar p * k := by
  sorry

/-- **Levi decomposition of `P_V` at the level of `SO(V)`** (Thesis §5.1.2, §8.3): for `p` in the
stabilizer of `⟨z_r⟩ ⊂ ⋯ ⊂ ⟨z_r, …, z_1⟩`, `P(p) = P(n) a(τ) (m ⊕ 1)` with `n ∈ N`,
`m ∈ SO(V₀)`. -/
theorem exists_levi_SO {p : GSpin d.QV} (hp : p ∈ flagStab d.flag) :
    ∃ nn ∈ d.N, ∃ (τ : Fin d.r → Fˣ) (m : d.V0 ≃ₗ[F] d.V0), m ∈ SOGrp d.Q0 ∧
      specP d.QV p = specP d.QV nn * (d.torusZ τ * d.extV0 m) := by
  sorry

-- The products in `SO(W) × SO(V)` make elaboration slow here.
set_option maxHeartbeats 1600000 in
include hb in
/-- **Thesis Lemma 8.3.2(ii) at the level of `SO(W) × SO(V)`** (BP Lemma 6.6.2(ii)), for the
explicit good pair of `weakCartan_G0_SO`: `Ḡ = P̄(H) · A₀⁺A(F) · K̄` with `K̄` bounded for
`σ_{SO}` (equivalently, relatively compact). Own work; not proved here.

Proof sketch (BP's proof of Lemma 6.6.2(ii)): (a) Iwasawa: `Ḡ = P̄(P) K₁` for the stabilizer
`P = GSpin(W) × P_V` of `⟨z_r⟩ ⊂ ⋯ ⊂ ⟨z_r, …, z_1⟩` (from `tits_iwasawa` for full flags
extending that flag, e.g. `z_r, …, z_1, u₁, u₂, …`); (b) Levi decomposition at the level of
`SO(V)`: every element of `P̄_V` is `P(n) a(τ) (m ⊕ 1)` with `n ∈ N`, `m ∈ SO(V₀)`; (c)
`weakCartan_G0_SO` for `(W ⊆ V₀, b)` applied to `(P(p_W) ⊕ 1, m)`, the converse of
`extZ_mem_fixer` (`fixer Q₀ b 1 = SO(W) ⊕ 1`), and `a(τ)` commuting with `SO(V₀) ⊕ 1`. -/
theorem exists_weakCartan_SO (hb0 : ∀ i : Fin n, (i : ℕ) = 0 → (b i).1 = 0) :
    ∃ M, ∀ y : d.GbarGrp, ∃ h ∈ d.H, ∃ x ∈ d.coneSO hb hf, ∃ k : d.GbarGrp,
      d.logNormSO k ≤ M ∧ y = d.Pbar h * x * k := by
  obtain ⟨M₁, hI⟩ := d.exists_iwasawa_SO
  obtain ⟨C_H, C, hCH, hCHs, hC, hCs, hWC⟩ := weakCartan_G0_SO hb hf
  obtain ⟨BH, hBH⟩ := hCH.bddAbove_image continuous_glMaxNorm.continuousOn
  obtain ⟨BC, hBC⟩ := hC.bddAbove_image continuous_glMaxNorm.continuousOn
  set B := max (max 1 BH) (3 * max 1 BC)
  have hB1 : 1 ≤ B := le_max_of_le_left (le_max_left _ _)
  refine ⟨M₁ + (1 + Real.log B), fun y => ?_⟩
  obtain ⟨p, hp, k₁, hk₁, rfl⟩ := hI y
  obtain ⟨nn, hnn, τ, m₀, hm₀, hpV⟩ := d.exists_levi_SO hp
  have hx0 := d.base.extZ_mem_fixer (b := b) hb0 (d.Pbar p).1
  have hm₀' : m₀ ∈ TauCeti.QuadraticMap.specialOrthogonalGroup d.Q0 := by
    rw [← SOGrp_eq_specialOrthogonalGroup]; exact hm₀
  obtain ⟨h', hh', s, hs, t, ht, kH, hkH, k, hk, hxe, hye⟩ := hWC _ hx0 m₀ hm₀'
  obtain ⟨a', ha'⟩ := d.exists_extZ_of_mem_fixer hb hf hb0 hh'
  obtain ⟨sW, hsW⟩ := d.exists_extZ_of_mem_fixer hb hf hb0
    (inv_mem (multiTorus_mem_fixer hb hf s 1))
  obtain ⟨kW, hkW⟩ := d.exists_extZ_of_mem_fixer hb hf hb0 (hCHs hkH)
  -- the `W`-part
  have hW : ((d.Pbar p).1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) =
      (a' : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) * sW * kW := by
    apply d.base_extZ_injective
    rw [hxe, map_mul, map_mul, ha', hsW, hkW]
  -- lifts
  obtain ⟨ã, hã⟩ : ∃ ã : GSpin d.QW, specP d.QW ã = a' := by
    have hmem : ((a' : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))) ∈ (specP d.QW).range := by
      rw [range_specP_eq_SOGrp d.nondeg]; exact a'.2
    exact hmem
  set h : d.G := d.pair (ã, nn * d.incl ã)
  have hh : h ∈ d.H := by
    show (d.incl (d.fst h))⁻¹ * d.snd h ∈ d.N
    have e : (d.incl (d.fst h))⁻¹ * d.snd h = (d.incl ã)⁻¹ * nn * ((d.incl ã)⁻¹)⁻¹ := by
      simp only [h, fst_pair, snd_pair, inv_inv, mul_assoc]
    rw [e]
    exact flagUnip_conj ((flagStab _).inv_mem (d.incl_mem_flagStab ã)) hnn
  have hPincl : specP d.QV (d.incl ã) = d.extZ a' := by
    refine LinearEquiv.ext fun v => ?_
    rw [d.specP_incl_apply, extZ_apply, hã]
  set y0 : d.V0 ≃ₗ[F] d.V0 := (multiTorus hb hf 0 t)⁻¹
  have hxV : d.torusZ τ * d.extV0 y0 ∈ SOGrp d.QV :=
    mul_mem (d.torusZ_mem_SOGrp τ) (d.extV0_mem_SOGrp (d.inv_multiTorus_mem_SOGrp hb hf 0 t))
  have hkV : d.extV0 k ∈ SOGrp d.QV := d.extV0_mem_SOGrp (by
    rw [SOGrp_eq_specialOrthogonalGroup]; exact hCs hk)
  set x : d.GbarGrp := (sW, ⟨_, hxV⟩)
  set kk : d.GbarGrp := (kW, ⟨_, hkV⟩)
  refine ⟨h, hh, x, ⟨s, t, τ, hs, ht, hsW, rfl⟩, kk * k₁, ?_, ?_⟩
  · -- the bound
    have hkk : d.logNormSO kk ≤ 1 + Real.log B := by
      unfold logNormSO
      have hgW : glMaxNorm (kW : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) ≤ max 1 BH := by
        have := glMaxNorm_prodCongr_refl (Z := Fin (2 * 0 + 1) → F)
          (kW : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))
        rw [← this]
        exact le_max_of_le_right (hBH ⟨kH, hkH, by rw [← hkW]; rfl⟩)
      have hgV : glMaxNorm (d.extV0 k) ≤ 3 * max 1 BC :=
        (d.glMaxNorm_extV0_le k).trans (by
          have := hBC ⟨k, hk, rfl⟩
          have : glMaxNorm k ≤ max 1 BC := le_max_of_le_right this
          linarith)
      have h1 : 1 ≤ max (glMaxNorm (kW : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)))
          (glMaxNorm (d.extV0 k)) := le_max_of_le_left (one_le_glMaxNorm _)
      have := Real.log_le_log (by linarith) (max_le_max (hgW.trans (le_max_left _ _))
        (hgV.trans (le_max_right _ _)) |>.trans (max_self B).le)
      show 1 + Real.log (max (glMaxNorm (kW : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)))
          (glMaxNorm (d.extV0 k))) ≤ _
      linarith
    have := d.logNormSO_mul_le kk k₁
    linarith
  · -- the identity
    rw [← mul_assoc]
    congr 1
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show ((d.Pbar p).1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) = specP d.QW ã * sW * kW
      rw [hW, hã]
    · show specP d.QV (d.snd p) = specP d.QV (nn * d.incl ã) * (d.torusZ τ * d.extV0 y0) *
        d.extV0 k
      rw [hpV, hye, map_mul (specP d.QV) nn, hPincl, map_mul d.extV0, map_mul d.extV0, ← ha',
        extV0_base_extZ]
      simp only [mul_assoc]
      rw [← mul_assoc (d.torusZ τ), torusZ_mul_extZ, mul_assoc]

include hb in
/-- **Thesis Lemma 8.3.2(ii)** (BP Lemma 6.6.2(ii)) for `G = GSpin(W) × GSpin(V)`, for the
explicit good pair of `weakCartan_G0_SO`: `G(F) = H(F) · A₀⁺A(F) · K` with `K` compact, where
the cone `A₀⁺A(F)` is taken modulo the central scalars (`cone`, the preimage of `coneSO`).
From `exists_weakCartan_SO` by lifting along `P̄` (kernel the central scalars, absorbed into the
cone; bounded sets lift to compact sets, `exists_isCompact_lift`). -/
theorem exists_weakCartan (hb0 : ∀ i : Fin n, (i : ℕ) = 0 → (b i).1 = 0) :
    ∃ K : Set d.G, IsCompact K ∧ ∀ g : d.G, ∃ h ∈ d.H, ∃ x ∈ d.cone hb hf, ∃ k ∈ K,
      g = h * x * k := by
  obtain ⟨M, hM⟩ := d.exists_weakCartan_SO hb hf hb0
  obtain ⟨K, hK, hKl⟩ := d.exists_isCompact_lift M
  refine ⟨K, hK, fun g => ?_⟩
  obtain ⟨h, hh, x, hx, k, hk, he⟩ := hM (d.Pbar g)
  obtain ⟨x₁, rfl⟩ := d.Pbar_surjective x
  obtain ⟨k₁, rfl⟩ := d.Pbar_surjective k
  obtain ⟨z, hz, hzk⟩ := hKl k₁ hk
  have hzker : d.Pbar z = 1 := by rw [d.scalars_eq_ker] at hz; exact hz
  set w := (h * (x₁ * z⁻¹) * (z * k₁))⁻¹ * g
  have hw : w ∈ d.scalars := by
    rw [d.scalars_eq_ker, MonoidHom.mem_ker]
    simp only [w, map_mul, map_inv, he, hzker]
    group
  have hwc := Subgroup.mem_center_iff.mp (d.AG_le_center (d.scalars_le_AG hw))
  refine ⟨h, hh, x₁ * z⁻¹ * w, ?_, z * k₁, hzk, ?_⟩
  · show d.Pbar (x₁ * z⁻¹ * w) ∈ d.coneSO hb hf
    have hwk : d.Pbar w = 1 := by rw [d.scalars_eq_ker] at hw; exact hw
    rwa [map_mul, map_mul, hwk, map_inv, hzker, inv_one, mul_one, mul_one]
  · have : g = h * (x₁ * z⁻¹) * (z * k₁) * w := by simp only [w, mul_inv_cancel_left]
    rw [this, mul_assoc _ (z * k₁), hwc (z * k₁)]
    group

include hb in
/-- **The weak Cartan data of `H(F)\G(F)/A_G(F)`** (`WeakCartanData`, the input of BP's proof of
Prop. 6.7.1(iii) = Thesis Prop. 8.4.1(iii)), with cone `S = A_G A₀⁺ A(F)` (`cone`), from
* the weak Cartan decomposition `exists_weakCartan` (Thesis Lemma 8.3.2(ii)),
* `σ_{A_G\G} ≪ σ_{H\G}` on the cone (`logNormModAG_le_fiberInf_of_cone`, Thesis Prop.
  8.4.1(ii)(b), via the reduction from `G` to `G₀`),
* and, **taken as hypotheses here**, the polynomial growth of the cone modulo `A_G` (BP (6.7.12)):
  `CS`, `M`, `N` and `growth`, stated exactly as the field `WeakCartanData.growth` for `S = cone`. -/
def weakCartanData (hb0 : ∀ i : Fin n, (i : ℕ) = 0 → (b i).1 = 0) (CS : Set d.G)
    (hCS : IsCompact CS) (M : ℝ) (N : ℕ)
    (growth : ∀ R : ℝ, 1 ≤ R → ∃ t : Finset d.G, (t.card : ℝ) ≤ M * (1 + R) ^ N ∧
      d.mkHG '' {s ∈ d.cone hb hf | d.logNormModAG s < R} ⊆ ⋃ j ∈ t, d.mkHG '' ((j * ·) '' CS)) :
    WeakCartanData d.mkHG d.logNormModAG where
  S := d.cone hb hf
  K := (d.exists_weakCartan hb hf hb0).choose
  isCompact_K := (d.exists_weakCartan hb hf hb0).choose_spec.1
  exists_eq_mul g := by
    obtain ⟨h, hh, x, hx, k, hk, he⟩ := (d.exists_weakCartan hb hf hb0).choose_spec.2 g
    refine ⟨x, hx, k, hk, ((d.mkHG_eq_mkHG_iff (x * k) g).2 ⟨h, hh, 1, one_mem _, ?_⟩).symm⟩
    rw [he, mul_one, mul_assoc]
  c := (d.logNormModAG_le_fiberInf_of_cone hb hf hb0).choose
  le_fiberInf s hs := by
    obtain ⟨s', t, τ, -, ht, -, hτ⟩ := hs
    exact (d.logNormModAG_le_fiberInf_of_cone hb hf hb0).choose_spec.2 s τ t ht hτ
  CS := CS
  isCompact_CS := hCS
  M := M
  N := N
  growth := growth

include hb in
/-- **Thesis Prop. 8.4.1(iii) from the polynomial growth of the cone** (BP Prop. 6.7.1(iii)):
`prop_6_7_1_iii_of_weakCartanData` applied to `weakCartanData`. The remaining hypothesis is the
polynomial growth (BP (6.7.12)) of the cone modulo `A_G`. -/
theorem prop_6_7_1_iii_of_growth (hb0 : ∀ i : Fin n, (i : ℕ) = 0 → (b i).1 = 0)
    (CS : Set d.G) (hCS : IsCompact CS) (M : ℝ) (N : ℕ)
    (growth : ∀ R : ℝ, 1 ≤ R → ∃ t : Finset d.G, (t.card : ℝ) ≤ M * (1 + R) ^ N ∧
      d.mkHG '' {s ∈ d.cone hb hf | d.logNormModAG s < R} ⊆ ⋃ j ∈ t, d.mkHG '' ((j * ·) '' CS))
    (C₀ : Set d.G) (hC₀ : IsCompact C₀) (hC₀' : (interior C₀).Nonempty) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ MeasureTheory.Integrable
      (fun q : d.HGQuot => d.xiHG C₀ q ^ 2 * d.logNormHG q ^ (-d₀)) d.weilMeasureHG :=
  d.prop_6_7_1_iii_of_weakCartanData C₀ hC₀ hC₀'
    (d.weakCartanData hb hf hb0 CS hCS M N growth)

end WeakCartanG

end GGPData

end GSpinGGP
