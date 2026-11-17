/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.NormDescent
import GSpinGGP.HarmonicAnalysis.LogNorm

/-!
# The log-norm of `G` modulo the scalars and the log-norm of `SO(W) × SO(V)`

Let `G = GSpin(W) × GSpin(V)`, `p = (P_W, P_V) : G → SO(W) × SO(V)` (`GGPData.pSO`), and
`Z = F^× × F^×` the central scalars, which form the kernel of `p` (`GGPData.scalars_eq_ker`).
Since `G/Z` embeds in `SO(W) × SO(V)`, the log-norm of `Z(F)\G(F)` is equivalent to the
log-norm of `SO(W) × SO(V)` composed with `p` (BP §1.2; Kottwitz, Clay Math. Proc. 4, Prop. 18.3):

`σ_{Z\G} ∼ σ_{SO} ∘ p` (`GGPData.logNormModScalars_equiv`),

and hence, for every subgroup `S ⊇ Z` (for instance `S = A_G`), `σ_{S\G}(g) ∼ σ_{p(S)\SO}(p(g))`,
where `σ_{p(S)\SO}(p(g)) = inf_{s ∈ S} σ_{SO}(p(s g))` (`GGPData.infLeft_equiv_of_scalars_le`,
`GGPData.logNormModAG_equiv`). The modulus `Z` cannot be dropped: if `W` (or `V`) is a hyperbolic
plane then `A_G ⊇ GSpin(W)`, and `σ_{SO} ∘ p` is unbounded on `GSpin(W)` (`SO(W) ≅ F^×`).

Here `σ_G = logNorm F d.G` is `1 + log max(1, ‖g‖, ‖g⁻¹‖)` with `‖·‖` the norm of left
multiplication on `C(W) × C(V)`, and `σ_{SO}(h₁, h₂) = 1 + log max(1, ‖hᵢ‖, ‖hᵢ⁻¹‖)` with the
operator norms on `W = F^m` and `V = W ⊕ Z` (sup norms) (`GGPData.logNormSO`).

## Main results

* `glMaxNorm`, `glLogNorm` (for `GL(E)`), `GGPData.logNormSO`: `≥ 1`, subadditive, symmetric.
* `GGPData.exists_logNormSO_pSO_le`: `σ_{SO}(p(g)) ≤ c σ_G(g)`.
* `GGPData.exists_logNorm_scalars_mul_le`: some `z ∈ Z` has `σ_G(z g) ≤ C σ_{SO}(p(g))`.
* `GGPData.logNormModScalars_equiv`, `GGPData.infLeft_equiv_of_scalars_le`,
  `GGPData.logNormModAG_equiv`: the comparisons above.

The proofs are for a `p`-adic field `F` (the setting of `logNorm`).
-/

noncomputable section

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

/-! ### Log-norm on `GL(E)` -/

section GLNorm

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace F E] [FiniteDimensional F E]

/-- `max(1, ‖f‖, ‖f⁻¹‖)` for `f ∈ GL(E)` (operator norms). -/
def glMaxNorm (f : E ≃ₗ[F] E) : ℝ := max 1 (max (linEquivNorm f) (linEquivNorm f⁻¹))

theorem one_le_glMaxNorm (f : E ≃ₗ[F] E) : 1 ≤ glMaxNorm f := le_max_left _ _

theorem linEquivNorm_le_glMaxNorm (f : E ≃ₗ[F] E) : linEquivNorm f ≤ glMaxNorm f :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem linEquivNorm_inv_le_glMaxNorm (f : E ≃ₗ[F] E) : linEquivNorm f⁻¹ ≤ glMaxNorm f :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem glMaxNorm_inv (f : E ≃ₗ[F] E) : glMaxNorm f⁻¹ = glMaxNorm f := by
  unfold glMaxNorm; rw [inv_inv, max_comm (linEquivNorm f⁻¹)]

theorem glMaxNorm_mul_le (f g : E ≃ₗ[F] E) : glMaxNorm (f * g) ≤ glMaxNorm f * glMaxNorm g := by
  have hf := one_le_glMaxNorm f
  have hg := one_le_glMaxNorm g
  refine max_le (by nlinarith) (max_le ?_ ?_)
  · exact (linEquivNorm_mul_le f g).trans (mul_le_mul (linEquivNorm_le_glMaxNorm f)
      (linEquivNorm_le_glMaxNorm g) (linEquivNorm_nonneg _) (by linarith))
  · rw [mul_inv_rev, mul_comm (glMaxNorm f)]
    exact (linEquivNorm_mul_le _ _).trans (mul_le_mul (linEquivNorm_inv_le_glMaxNorm g)
      (linEquivNorm_inv_le_glMaxNorm f) (linEquivNorm_nonneg _) (by linarith))

end GLNorm

/-! ### `G → SO(W) × SO(V)` -/

namespace GGPData

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F] [Invertible (2 : F)]
variable (d : GGPData F)

/-- The group `GL(W) × GL(V)`, containing `SO(W) × SO(V)`. -/
abbrev GLWV : Type _ := ((Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) × (d.V ≃ₗ[F] d.V)

/-- `p = (P_W, P_V) : G = GSpin(W) × GSpin(V) → SO(W) × SO(V)` (Thesis §5.1.2, §5.2). -/
def pSO : d.G →* d.GLWV := ((specP d.QW).comp d.fst).prod ((specP d.QV).comp d.snd)

@[simp] theorem pSO_fst (g : d.G) : (d.pSO g).1 = specP d.QW (d.fst g) := rfl

@[simp] theorem pSO_snd (g : d.G) : (d.pSO g).2 = specP d.QV (d.snd g) := rfl

/-- The log-norm of `SO(W) × SO(V)` (BP §1.2, Thesis §2.2):
`σ_{SO}(h) = 1 + log max(1, ‖h₁‖, ‖h₁⁻¹‖, ‖h₂‖, ‖h₂⁻¹‖)`, with the operator norms on
`W = F^m` and `V = W ⊕ Z` (sup norms). It is defined on `GL(W) × GL(V)`. -/
def logNormSO (h : d.GLWV) : ℝ := 1 + Real.log (max (glMaxNorm h.1) (glMaxNorm h.2))

theorem one_le_max_glMaxNorm (h : d.GLWV) : 1 ≤ max (glMaxNorm h.1) (glMaxNorm h.2) :=
  le_max_of_le_left (one_le_glMaxNorm _)

/-- `σ_{SO} ≥ 1`. -/
theorem one_le_logNormSO (h : d.GLWV) : 1 ≤ d.logNormSO h := by
  unfold logNormSO; linarith [Real.log_nonneg (d.one_le_max_glMaxNorm h)]

/-- `σ_{SO}(h⁻¹) = σ_{SO}(h)`. -/
theorem logNormSO_inv (h : d.GLWV) : d.logNormSO h⁻¹ = d.logNormSO h := by
  simp [logNormSO, glMaxNorm_inv]

/-- `σ_{SO}` is subadditive. -/
theorem logNormSO_mul_le (h k : d.GLWV) :
    d.logNormSO (h * k) ≤ d.logNormSO h + d.logNormSO k := by
  have hh := d.one_le_max_glMaxNorm h
  have hk := d.one_le_max_glMaxNorm k
  have hmax : max (glMaxNorm (h * k).1) (glMaxNorm (h * k).2) ≤
      max (glMaxNorm h.1) (glMaxNorm h.2) * max (glMaxNorm k.1) (glMaxNorm k.2) := by
    refine max_le ((glMaxNorm_mul_le _ _).trans ?_) ((glMaxNorm_mul_le _ _).trans ?_)
    · exact mul_le_mul (le_max_left _ _) (le_max_left _ _)
        (zero_le_one.trans (one_le_glMaxNorm _)) (by linarith)
    · exact mul_le_mul (le_max_right _ _) (le_max_right _ _)
        (zero_le_one.trans (one_le_glMaxNorm _)) (by linarith)
  have := Real.log_le_log (by linarith [d.one_le_max_glMaxNorm (h * k)]) hmax
  rw [Real.log_mul (by linarith) (by linarith)] at this
  unfold logNormSO; linarith

/-! ### The scalars -/

/-- The central scalars `Z(F) = F^× × F^× ⊆ G(F)`: pairs `(c₁, c₂)` of scalars of `C(W)`, `C(V)`.
This is `ker p` (`scalars_eq_ker`). -/
def scalars : Subgroup d.G := (d.pair.comp ((scalarGSpin d.QW).prodMap (scalarGSpin d.QV))).range

theorem pair_mem_scalars (c₁ c₂ : Fˣ) :
    d.pair (scalarGSpin d.QW c₁, scalarGSpin d.QV c₂) ∈ d.scalars := ⟨(c₁, c₂), rfl⟩

theorem pair_fst_snd (g : d.G) : d.pair (d.fst g, d.snd g) = g := rfl

/-- `Z = ker p` (`ker_specP`). -/
theorem scalars_eq_ker : d.scalars = d.pSO.ker := by
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    simp [MonoidHom.mem_ker, pSO, fst_pair, snd_pair, specP_scalarGSpin_eq_one, Prod.ext_iff]
  · intro hg
    rw [MonoidHom.mem_ker, Prod.ext_iff] at hg
    have h1 : d.fst g ∈ (specP d.QW).ker := hg.1
    have h2 : d.snd g ∈ (specP d.QV).ker := hg.2
    rw [ker_specP d.nondeg] at h1
    rw [ker_specP d.nondeg_QV] at h2
    obtain ⟨c₁, hc₁⟩ := h1
    obtain ⟨c₂, hc₂⟩ := h2
    refine ⟨(c₁, c₂), ?_⟩
    change d.pair (scalarGSpin d.QW c₁, scalarGSpin d.QV c₂) = g
    rw [hc₁, hc₂]
    exact d.pair_fst_snd g

theorem pSO_eq_of_mem_scalars {z : d.G} (hz : z ∈ d.scalars) (g : d.G) :
    d.pSO (z * g) = d.pSO g := by
  rw [d.scalars_eq_ker, MonoidHom.mem_ker] at hz
  rw [map_mul, hz, one_mul]

/-- `Z ⊆ A_G`. -/
theorem scalars_le_AG : d.scalars ≤ d.AG := by
  rintro _ ⟨c, rfl⟩
  exact ⟨(scalarGSpin d.QW c.1, scalarGSpin d.QV c.2),
    ⟨scalarGSpin_mem_splitCentralGSpin _ _, scalarGSpin_mem_splitCentralGSpin _ _⟩, rfl⟩

/-! ### Norms on `C(W) × C(V)` -/

theorem coe_fst (g : d.G) : ((g : d.ambientˣ) : d.ambient).1 =
    ((d.fst g : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) := rfl

theorem coe_snd (g : d.G) : ((g : d.ambientˣ) : d.ambient).2 =
    ((d.snd g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) := rfl

theorem coe_inv_fst (g : d.G) : (((g⁻¹ : d.G) : d.ambientˣ) : d.ambient).1 =
    ((((d.fst g : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) :
      CliffordAlgebra d.QW) := rfl

theorem coe_inv_snd (g : d.G) : (((g⁻¹ : d.G) : d.ambientˣ) : d.ambient).2 =
    ((((d.snd g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ)⁻¹ : (CliffordAlgebra d.QV)ˣ) :
      CliffordAlgebra d.QV) := rfl

theorem lmulPi_prod_injective :
    Function.Injective ((lmulPiₗ F ∘ₗ LinearMap.fst F _ _).prod
      (lmulPiₗ F ∘ₗ LinearMap.snd F _ _) : d.ambient →ₗ[F] _) := by
  intro x y hxy
  have h1 := congrArg Prod.fst hxy
  have h2 := congrArg Prod.snd hxy
  exact Prod.ext (lmulPi_injective F h1) (lmulPi_injective F h2)

/-- `‖(x₁, x₂)‖ ≪ max(‖x₁‖, ‖x₂‖)` for the norms of left multiplication. -/
theorem exists_norm_lmulPi_ambient_le : ∃ C, 0 ≤ C ∧ ∀ x : d.ambient,
    ‖lmulPi F x‖ ≤ C * max ‖lmulPi F x.1‖ ‖lmulPi F x.2‖ := by
  obtain ⟨C, hC, h⟩ := LinearMap.exists_norm_le_mul_norm_of_injective _ (lmulPiₗ F)
    d.lmulPi_prod_injective
  exact ⟨C, hC, fun x => (h x).trans_eq (by rw [Prod.norm_def]; rfl)⟩

/-- `max(‖x₁‖, ‖x₂‖) ≪ ‖(x₁, x₂)‖` for the norms of left multiplication. -/
theorem exists_max_norm_lmulPi_le : ∃ C, 0 ≤ C ∧ ∀ x : d.ambient,
    max ‖lmulPi F x.1‖ ‖lmulPi F x.2‖ ≤ C * ‖lmulPi F x‖ := by
  obtain ⟨C, hC, h⟩ := LinearMap.exists_norm_le_mul_norm_of_injective (lmulPiₗ F)
    ((lmulPiₗ F ∘ₗ LinearMap.fst F _ _).prod (lmulPiₗ F ∘ₗ LinearMap.snd F _ _) :
      d.ambient →ₗ[F] _) (lmulPi_injective F (A := d.ambient))
  exact ⟨C, hC, fun x => (le_of_eq (by rw [Prod.norm_def]; rfl)).trans (h x)⟩

/-- `1 + log A ≤ (1 + log K + n)(1 + log B)` when `1 ≤ A ≤ K Bⁿ`, `1 ≤ K`, `1 ≤ B`. -/
theorem one_add_log_le_of_le_mul_pow {A B K : ℝ} {n : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hK : 1 ≤ K)
    (h : A ≤ K * B ^ n) : 1 + Real.log A ≤ (1 + Real.log K + n) * (1 + Real.log B) := by
  have hlA := Real.log_le_log (by linarith) h
  rw [Real.log_mul (by linarith) (by positivity), Real.log_pow] at hlA
  have hK0 := Real.log_nonneg hK
  have hB0 := Real.log_nonneg hB
  nlinarith

/-! ### The comparison -/

/-- **`σ_{SO}(p(g)) ≪ σ_G(g)`** (the easy half; `exists_norm_specP_le`). -/
theorem exists_logNormSO_pSO_le :
    ∃ c, 0 ≤ c ∧ ∀ g : d.G, d.logNormSO (d.pSO g) ≤ c * logNorm F d.G g := by
  obtain ⟨Cb, hCb, hb⟩ := d.exists_max_norm_lmulPi_le
  obtain ⟨CW, hCW, hW⟩ := exists_norm_specP_le (F := F) (Q := d.QW)
  obtain ⟨CV, hCV, hV⟩ := exists_norm_specP_le (F := F) (Q := d.QV)
  set K := 1 + (CW + CV) * Cb ^ 2
  have hK : 1 ≤ K := by have : 0 ≤ (CW + CV) * Cb ^ 2 := by positivity
                        linarith
  refine ⟨1 + Real.log K + (2 : ℕ), add_nonneg (add_nonneg zero_le_one (Real.log_nonneg hK))
    (Nat.cast_nonneg _), fun g => ?_⟩
  set m := maxNorm F d.G g
  have hm : 1 ≤ m := one_le_maxNorm _ _
  have hg : ‖lmulPi F ((g : d.ambientˣ) : d.ambient)‖ ≤ m :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hgi : ‖lmulPi F (((g⁻¹ : d.G) : d.ambientˣ) : d.ambient)‖ ≤ m :=
    (le_max_right _ _).trans (le_max_right _ _)
  have b1 := hb ((g : d.ambientˣ) : d.ambient)
  have b2 := hb (((g⁻¹ : d.G) : d.ambientˣ) : d.ambient)
  rw [coe_fst, coe_snd] at b1
  rw [coe_inv_fst, coe_inv_snd] at b2
  -- the four factor norms are `≤ Cb m`
  have f1 : ‖lmulPi F ((d.fst g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)‖ ≤ Cb * m :=
    (le_max_left _ _).trans (b1.trans (mul_le_mul_of_nonneg_left hg hCb))
  have f2 : ‖lmulPi F ((d.snd g : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)‖ ≤ Cb * m :=
    (le_max_right _ _).trans (b1.trans (mul_le_mul_of_nonneg_left hg hCb))
  have f3 : ‖lmulPi F (((d.fst g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) :
      CliffordAlgebra d.QW)‖ ≤ Cb * m :=
    (le_max_left _ _).trans (b2.trans (mul_le_mul_of_nonneg_left hgi hCb))
  have f4 : ‖lmulPi F (((d.snd g : (CliffordAlgebra d.QV)ˣ)⁻¹ : (CliffordAlgebra d.QV)ˣ) :
      CliffordAlgebra d.QV)‖ ≤ Cb * m :=
    (le_max_right _ _).trans (b2.trans (mul_le_mul_of_nonneg_left hgi hCb))
  have hCbm : 0 ≤ Cb * m := by positivity
  have key : ∀ (C a b : ℝ), 0 ≤ C → C ≤ CW + CV → 0 ≤ a → 0 ≤ b → a ≤ Cb * m →
      b ≤ Cb * m → C * (a * b) ≤ K * m ^ 2 := by
    intro C a b hC hCle ha hb' haa hbb
    have h1 : C * (a * b) ≤ C * ((Cb * m) * (Cb * m)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul haa hbb hb' hCbm) hC
    have h2 : C * ((Cb * m) * (Cb * m)) ≤ (CW + CV) * Cb ^ 2 * m ^ 2 := by
      have : C * ((Cb * m) * (Cb * m)) = C * (Cb ^ 2 * m ^ 2) := by ring
      rw [this, mul_assoc]
      exact mul_le_mul_of_nonneg_right hCle (by positivity)
    have h3 : (CW + CV) * Cb ^ 2 * m ^ 2 ≤ K * m ^ 2 :=
      mul_le_mul_of_nonneg_right (by simp [K]) (by positivity)
    linarith
  have hKm : 1 ≤ K * m ^ 2 := one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hm)
  have hPW : glMaxNorm (specP d.QW (d.fst g)) ≤ K * m ^ 2 := by
    refine max_le hKm (max_le ?_ ?_)
    · exact (hW (d.fst g)).trans (key _ _ _ hCW (by linarith) (norm_nonneg _) (norm_nonneg _) f1 f3)
    · rw [← map_inv]
      refine (hW (d.fst g)⁻¹).trans ?_
      simp only [Subgroup.coe_inv, inv_inv]
      rw [mul_comm (‖_‖)]
      exact key _ _ _ hCW (by linarith) (norm_nonneg _) (norm_nonneg _) f1 f3
  have hPV : glMaxNorm (specP d.QV (d.snd g)) ≤ K * m ^ 2 := by
    refine max_le hKm (max_le ?_ ?_)
    · exact (hV (d.snd g)).trans (key _ _ _ hCV (by linarith) (norm_nonneg _) (norm_nonneg _) f2 f4)
    · rw [← map_inv]
      refine (hV (d.snd g)⁻¹).trans ?_
      simp only [Subgroup.coe_inv, inv_inv]
      rw [mul_comm (‖_‖)]
      exact key _ _ _ hCV (by linarith) (norm_nonneg _) (norm_nonneg _) f2 f4
  exact one_add_log_le_of_le_mul_pow (d.one_le_max_glMaxNorm _) hm hK (max_le hPW hPV)

/-- **Norm descent: some `z ∈ Z` has `σ_G(z g) ≪ σ_{SO}(p(g))`** (the hard half;
`exists_scalar_norm_le` on each factor). -/
theorem exists_logNorm_scalars_mul_le :
    ∃ C, 0 ≤ C ∧ ∀ g : d.G, ∃ z ∈ d.scalars,
      logNorm F d.G (z * g) ≤ C * d.logNormSO (d.pSO g) := by
  obtain ⟨Ca, hCa, ha⟩ := d.exists_norm_lmulPi_ambient_le
  have hfs : ∀ (x : d.G) (a : GSpin d.QW) (b : GSpin d.QV), d.fst x = a → d.snd x = b →
      ‖lmulPi F ((x : d.ambientˣ) : d.ambient)‖ ≤ Ca * max
        ‖lmulPi F ((a : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)‖
        ‖lmulPi F ((b : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)‖ ∧
      ‖lmulPi F (((x⁻¹ : d.G) : d.ambientˣ) : d.ambient)‖ ≤ Ca * max
        ‖lmulPi F (((a : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) :
          CliffordAlgebra d.QW)‖
        ‖lmulPi F (((b : (CliffordAlgebra d.QV)ˣ)⁻¹ : (CliffordAlgebra d.QV)ˣ) :
          CliffordAlgebra d.QV)‖ := by
    intro x a b hxa hxb
    subst hxa hxb
    exact ⟨ha _, ha _⟩
  obtain ⟨CW, NW, hCW, hW⟩ := exists_scalar_norm_le (F := F) d.nondeg
  obtain ⟨CV, NV, hCV, hV⟩ := exists_scalar_norm_le (F := F) d.nondeg_QV
  obtain ⟨K, hKd⟩ : ∃ K, K = 1 + Ca * max CW CV := ⟨_, rfl⟩
  have hK : 1 ≤ K := by
    have : 0 ≤ Ca * max CW CV := mul_nonneg hCa (le_max_of_le_left hCW)
    linarith
  refine ⟨1 + Real.log K + ((NW + NV : ℕ) : ℝ), add_nonneg (add_nonneg zero_le_one
    (Real.log_nonneg hK)) (Nat.cast_nonneg _), fun g => ?_⟩
  obtain ⟨c₁, hc₁, hc₁'⟩ := hW (d.fst g)
  obtain ⟨c₂, hc₂, hc₂'⟩ := hV (d.snd g)
  refine ⟨_, d.pair_mem_scalars c₁ c₂, ?_⟩
  have hM : 1 ≤ max (glMaxNorm (specP d.QW (d.fst g))) (glMaxNorm (specP d.QV (d.snd g))) :=
    le_max_of_le_left (one_le_glMaxNorm _)
  have hMW : max 1 (linEquivNorm (specP d.QW (d.fst g))) ≤
      max (glMaxNorm (specP d.QW (d.fst g))) (glMaxNorm (specP d.QV (d.snd g))) :=
    le_max_of_le_left (max_le (one_le_glMaxNorm _) (linEquivNorm_le_glMaxNorm _))
  have hMV : max 1 (linEquivNorm (specP d.QV (d.snd g))) ≤
      max (glMaxNorm (specP d.QW (d.fst g))) (glMaxNorm (specP d.QV (d.snd g))) :=
    le_max_of_le_right (max_le (one_le_glMaxNorm _) (linEquivNorm_le_glMaxNorm _))
  rw [logNormSO, pSO_fst, pSO_snd, logNorm]
  generalize max (glMaxNorm (specP d.QW (d.fst g))) (glMaxNorm (specP d.QV (d.snd g))) = M
    at hM hMW hMV ⊢
  have hp : ∀ (x : ℝ) (n : ℕ), n ≤ NW + NV → 1 ≤ x → x ≤ M → x ^ n ≤ M ^ (NW + NV) :=
    fun x n hn hx hxM => (pow_le_pow_left₀ (zero_le_one.trans hx) hxM n).trans
      (pow_le_pow_right₀ hM hn)
  have hMN : 1 ≤ M ^ (NW + NV) := one_le_pow₀ hM
  -- bounds for the two factors of `z g` and of `(z g)⁻¹`
  have bnd : ∀ (C a x : ℝ) (n : ℕ), C ≤ max CW CV → 0 ≤ C → n ≤ NW + NV → 1 ≤ x → x ≤ M →
      a ≤ C * x ^ n → a ≤ max CW CV * M ^ (NW + NV) := fun C a x n hC hC0 hn hx hxM ha =>
    ha.trans (mul_le_mul hC (hp x n hn hx hxM) (by positivity) (le_max_of_le_left hCW))
  have b1 := bnd _ _ _ _ (le_max_left _ _) hCW (Nat.le_add_right _ _) (le_max_left _ _) hMW hc₁
  have b2 := bnd _ _ _ _ (le_max_right _ _) hCV (Nat.le_add_left _ _) (le_max_left _ _) hMV hc₂
  have b3 := bnd _ _ _ _ (le_max_left _ _) hCW (Nat.le_add_right _ _) (le_max_left _ _) hMW hc₁'
  have b4 := bnd _ _ _ _ (le_max_right _ _) hCV (Nat.le_add_left _ _) (le_max_left _ _) hMV hc₂'
  have e1 : d.fst (d.pair (scalarGSpin d.QW c₁, scalarGSpin d.QV c₂) * g) =
      scalarGSpin d.QW c₁ * d.fst g := by rw [map_mul]; rfl
  have e2 : d.snd (d.pair (scalarGSpin d.QW c₁, scalarGSpin d.QV c₂) * g) =
      scalarGSpin d.QV c₂ * d.snd g := by rw [map_mul]; rfl
  obtain ⟨hamb, hamb'⟩ := hfs _ _ _ e1 e2
  have hmax : maxNorm F d.G (d.pair (scalarGSpin d.QW c₁, scalarGSpin d.QV c₂) * g) ≤
      K * M ^ (NW + NV) := by
    have hKN : Ca * (max CW CV * M ^ (NW + NV)) ≤ K * M ^ (NW + NV) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (by rw [hKd]; linarith) (by positivity)
    refine max_le (one_le_mul_of_one_le_of_one_le hK hMN) (max_le ?_ ?_)
    · exact hamb.trans ((mul_le_mul_of_nonneg_left (max_le b1 b2) hCa).trans hKN)
    · exact hamb'.trans ((mul_le_mul_of_nonneg_left (max_le b3 b4) hCa).trans hKN)
  exact one_add_log_le_of_le_mul_pow (one_le_maxNorm _ _) hM hK hmax

/-- **`σ_{S\G}(g) ∼ σ_{p(S)\SO}(p(g))` for `S ⊇ Z`**: with `σ_{p(S)\SO}(p(g)) =
inf_{s ∈ S} σ_{SO}(p(s g))` (the push-forward of `σ_{SO}` to `p(S)\SO(W) × SO(V)`, as in BP §1.2),
there are `c, C ≥ 0` with
`σ_{p(S)\SO}(p(g)) ≤ c σ_{S\G}(g)` and `σ_{S\G}(g) ≤ C σ_{p(S)\SO}(p(g))`. -/
theorem infLeft_equiv_of_scalars_le {S : Subgroup d.G} (hS : d.scalars ≤ S) :
    ∃ c C, 0 ≤ c ∧ 0 ≤ C ∧ ∀ g : d.G,
      infLeft (d.logNormSO ∘ d.pSO) S g ≤ c * infLeft (logNorm F d.G) S g ∧
      infLeft (logNorm F d.G) S g ≤ C * infLeft (d.logNormSO ∘ d.pSO) S g := by
  obtain ⟨c, hc, hcle⟩ := d.exists_logNormSO_pSO_le
  obtain ⟨C, hC, hCle⟩ := d.exists_logNorm_scalars_mul_le
  have hτ : ∀ g, 0 ≤ (d.logNormSO ∘ d.pSO) g := fun g => zero_le_one.trans (d.one_le_logNormSO _)
  have hσ : ∀ g, 0 ≤ logNorm F d.G g := fun g => zero_le_one.trans (one_le_logNorm _ _)
  refine ⟨c, C, hc, hC, fun g => ⟨?_, ?_⟩⟩
  · refine le_mul_infLeft S hc fun s hs => ?_
    exact (infLeft_le_of_nonneg S hτ hs g).trans (hcle _)
  · refine le_mul_infLeft S hC fun s hs => ?_
    obtain ⟨z, hz, hzle⟩ := hCle (s * g)
    have := infLeft_le_of_nonneg S hσ (S.mul_mem (hS hz) hs) g
    rw [mul_assoc] at this
    exact this.trans hzle

/-- **`σ_{Z\G} ∼ σ_{SO} ∘ p`** (Kottwitz, Clay Math. Proc. 4, Prop. 18.3; BP §1.2): the log-norm
of `Z(F)\G(F)`, `σ_{Z\G}(g) = inf_{z ∈ Z} σ_G(z g)`, is equivalent to `σ_{SO}(p(g))`. -/
theorem logNormModScalars_equiv :
    ∃ c C, 0 ≤ c ∧ 0 ≤ C ∧ ∀ g : d.G,
      d.logNormSO (d.pSO g) ≤ c * infLeft (logNorm F d.G) d.scalars g ∧
      infLeft (logNorm F d.G) d.scalars g ≤ C * d.logNormSO (d.pSO g) := by
  obtain ⟨c, C, hc, hC, h⟩ := d.infLeft_equiv_of_scalars_le le_rfl
  have hconst : ∀ g, infLeft (d.logNormSO ∘ d.pSO) d.scalars g = d.logNormSO (d.pSO g) := by
    intro g
    have : ∀ s : d.scalars, (d.logNormSO ∘ d.pSO) ((s : d.G) * g) = d.logNormSO (d.pSO g) :=
      fun s => by simp only [Function.comp_apply, d.pSO_eq_of_mem_scalars s.2]
    simp only [infLeft, this, ciInf_const]
  exact ⟨c, C, hc, hC, fun g => by simpa only [hconst] using h g⟩

/-- **`σ_{A_G\G}(g) ∼ σ_{p(A_G)\SO}(p(g))`**: the log-norm `σ_{A_G\G}` of
`𝒞(A_G(F)\G(F), χ⁻¹)` (`GGPData.logNormModAG` is `infLeft (logNorm F d.G) d.AG`) is equivalent to
`inf_{a ∈ A_G} σ_{SO}(p(a g))`, the log-norm of `p(A_G)\SO(W) × SO(V)` at `p(g)`; here `p(A_G)` is
trivial unless `W` or `V` is a hyperbolic plane `U`, when it contains `SO(U)`. -/
theorem logNormModAG_equiv :
    ∃ c C, 0 ≤ c ∧ 0 ≤ C ∧ ∀ g : d.G,
      infLeft (d.logNormSO ∘ d.pSO) d.AG g ≤ c * infLeft (logNorm F d.G) d.AG g ∧
      infLeft (logNorm F d.G) d.AG g ≤ C * infLeft (d.logNormSO ∘ d.pSO) d.AG g :=
  d.infLeft_equiv_of_scalars_le d.scalars_le_AG

end GGPData

end GSpinGGP
