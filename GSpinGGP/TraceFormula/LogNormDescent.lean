/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.NormDescent
import GSpinGGP.GGP.Descent
import GSpinGGP.HarmonicAnalysis.LogNorm

/-!
# The log-norm of `G` modulo the scalars and the log-norm of `SO(W) × SO(V)`

Let `G = GSpin(W) × GSpin(V)`, `P̄ = (P_W, P_V) : G → Ḡ = SO(W) × SO(V)` (`GGPData.Pbar`), and
`Z = F^× × F^×` the central scalars, which form the kernel of `P̄` (`GGPData.scalars_eq_ker`).
Since `G/Z` embeds in `Ḡ`, the log-norm of `Z(F)\G(F)` is equivalent to the log-norm of `Ḡ`
composed with `P̄` (BP §1.2; Kottwitz, Clay Math. Proc. 4, Prop. 18.3):

`σ_{Z\G} ∼ σ_{Ḡ} ∘ P̄` (`GGPData.logNormModScalars_equiv`),

and hence, for every subgroup `S ⊇ Z`, `σ_{S\G}(g) ∼ σ_{P̄(S)\Ḡ}(P̄(g))`, where
`σ_{P̄(S)\Ḡ}(h) = inf_{s ∈ P̄(S)} σ_{Ḡ}(s h)` is the push-forward of `σ_{Ḡ}`
(`GGPData.infLeft_equiv_of_scalars_le`); for `S = A_G` this is `σ_{A_G\G} ∼ σ_{Ā_G\Ḡ} ∘ P̄`
with `Ā_G = P̄(A_G)` (`GGPData.logNormModAG_equiv`; `GGPData.logNormModAG` is by definition
`infLeft (logNorm F d.G) d.AG`). The modulus `Z` cannot be dropped: if `W` (or `V`) is a
hyperbolic plane then `A_G ⊇ GSpin(W)`, and `σ_{Ḡ} ∘ P̄` is unbounded on `GSpin(W)`.
These results do not cover `GGPData.logNormMod`, the log-norm modulo the diagonal scalars
`A_{G,H} ⊊ Z`, which also sees `|log |c₁/c₂||` on `Z ∋ (c₁, c₂)`.

Here `σ_G = logNorm F d.G` is `1 + log max(1, ‖g‖, ‖g⁻¹‖)` with `‖·‖` the norm of left
multiplication on `C(W) × C(V)`, and `σ_{Ḡ}(h₁, h₂) = 1 + log max(1, ‖hᵢ‖, ‖hᵢ⁻¹‖)` with the
operator norms on `W = F^m` and `V = W ⊕ Z` (sup norms) (`GGPData.logNormSO`). Operator norms are
what the proof produces; they are equivalent to the matrix norms `basisOpNorm b`
(`exists_norm_toContinuousLinearMap_le_basisOpNorm`), and so to any other norm on `End(W) × End(V)`.

## Main results

* `entryMaxNorm`, `logNorm_equiv_entryMaxNorm`: `σ` ≍ `1 + log` of the largest matrix entry of
  `L_g`, `L_{g⁻¹}` in a basis (Kottwitz's norm (18.2.1) for these coordinates).
* `glMaxNorm` (for `GL(E)`), `GGPData.logNormSO`: `≥ 1`, subadditive, symmetric.
* `GGPData.exists_logNormSO_Pbar_le`: `σ_{Ḡ}(P̄(g)) ≤ c σ_G(g)`.
* `GGPData.exists_logNorm_scalars_mul_le`: some `z ∈ Z` has `σ_G(z g) ≤ C σ_{Ḡ}(P̄(g))`.
* `GGPData.logNormModScalars_equiv`, `GGPData.infLeft_equiv_of_scalars_le`,
  `GGPData.logNormModAG_equiv`: the comparisons above.

The proofs are for a `p`-adic field `F` (the setting of `logNorm`).
-/

noncomputable section

open Module CliffordAlgebra

namespace GSpinGGP

/-! ### Log-norm on `GL(E)` -/

section GLNorm

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace F E] [FiniteDimensional F E]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace F Z] [FiniteDimensional F Z]

/-- `max(1, ‖f‖, ‖f⁻¹‖)` for `f ∈ GL(E)` (operator norms). -/
def glMaxNorm (f : E ≃ₗ[F] E) : ℝ :=
  max 1 (max ‖LinearMap.toContinuousLinearMap (f : E →ₗ[F] E)‖
    ‖LinearMap.toContinuousLinearMap ((f⁻¹ : E ≃ₗ[F] E) : E →ₗ[F] E)‖)

theorem one_le_glMaxNorm (f : E ≃ₗ[F] E) : 1 ≤ glMaxNorm f := le_max_left _ _

theorem norm_le_glMaxNorm (f : E ≃ₗ[F] E) :
    ‖LinearMap.toContinuousLinearMap (f : E →ₗ[F] E)‖ ≤ glMaxNorm f :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem norm_inv_le_glMaxNorm (f : E ≃ₗ[F] E) :
    ‖LinearMap.toContinuousLinearMap ((f⁻¹ : E ≃ₗ[F] E) : E →ₗ[F] E)‖ ≤ glMaxNorm f :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem glMaxNorm_inv (f : E ≃ₗ[F] E) : glMaxNorm f⁻¹ = glMaxNorm f := by
  unfold glMaxNorm; rw [inv_inv, max_comm ‖LinearMap.toContinuousLinearMap
    ((f⁻¹ : E ≃ₗ[F] E) : E →ₗ[F] E)‖]

theorem glMaxNorm_mul_le (f g : E ≃ₗ[F] E) : glMaxNorm (f * g) ≤ glMaxNorm f * glMaxNorm g := by
  have hf := one_le_glMaxNorm f
  have hg := one_le_glMaxNorm g
  refine max_le (by nlinarith) (max_le ?_ ?_)
  · exact (norm_toContinuousLinearMap_mul_le f g).trans (mul_le_mul (norm_le_glMaxNorm f)
      (norm_le_glMaxNorm g) (norm_nonneg _) (by linarith))
  · rw [mul_inv_rev, mul_comm (glMaxNorm f)]
    exact (norm_toContinuousLinearMap_mul_le _ _).trans (mul_le_mul (norm_inv_le_glMaxNorm g)
      (norm_inv_le_glMaxNorm f) (norm_nonneg _) (by linarith))

/-- `max(1, ‖1‖, ‖1⁻¹‖) = 1`. -/
theorem glMaxNorm_one : glMaxNorm (1 : E ≃ₗ[F] E) = 1 :=
  le_antisymm (max_le le_rfl (max_le ContinuousLinearMap.norm_id_le
    ContinuousLinearMap.norm_id_le)) (le_max_left _ _)

/-- `‖f ⊕ 1‖ ≤ max(‖f‖, 1)` for the operator norm on `E × Z` (sup norm). -/
theorem norm_prodCongr_refl_le (f : E ≃ₗ[F] E) :
    ‖LinearMap.toContinuousLinearMap
        ((f.prodCongr (LinearEquiv.refl F Z) : (E × Z) ≃ₗ[F] (E × Z)) : (E × Z) →ₗ[F] (E × Z))‖ ≤
      max ‖LinearMap.toContinuousLinearMap (f : E →ₗ[F] E)‖ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (le_max_right _ _))
    fun x => ?_
  have hf := (LinearMap.toContinuousLinearMap (f : E →ₗ[F] E)).le_opNorm x.1
  rw [LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe] at hf
  rw [LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, Prod.norm_def, Prod.norm_def]
  have hM : 0 ≤ max ‖LinearMap.toContinuousLinearMap (f : E →ₗ[F] E)‖ 1 :=
    zero_le_one.trans (le_max_right _ _)
  refine max_le (hf.trans (mul_le_mul (le_max_left _ _) (le_max_left _ _) (norm_nonneg _) hM)) ?_
  calc ‖x.2‖ = 1 * ‖x.2‖ := (one_mul _).symm
    _ ≤ _ := mul_le_mul (le_max_right _ _) (le_max_right _ _) (norm_nonneg _) hM

/-- `‖f‖ ≤ ‖f ⊕ 1‖`. -/
theorem norm_le_norm_prodCongr_refl (f : E ≃ₗ[F] E) :
    ‖LinearMap.toContinuousLinearMap (f : E →ₗ[F] E)‖ ≤
      ‖LinearMap.toContinuousLinearMap
        ((f.prodCongr (LinearEquiv.refl F Z) : (E × Z) ≃ₗ[F] (E × Z)) : (E × Z) →ₗ[F] (E × Z))‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun e => ?_
  have := (LinearMap.toContinuousLinearMap
    ((f.prodCongr (LinearEquiv.refl F Z) : (E × Z) ≃ₗ[F] (E × Z)) : (E × Z) →ₗ[F] (E × Z))).le_opNorm
      (e, 0)
  rw [LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, Prod.norm_def, Prod.norm_def, norm_zero,
    max_eq_left (norm_nonneg _), max_eq_left (norm_nonneg _)] at this
  rw [LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe]
  exact this

/-- `max(1, ‖f ⊕ 1‖, ‖(f ⊕ 1)⁻¹‖) = max(1, ‖f‖, ‖f⁻¹‖)`. -/
theorem glMaxNorm_prodCongr_refl (f : E ≃ₗ[F] E) :
    glMaxNorm (f.prodCongr (LinearEquiv.refl F Z)) = glMaxNorm f := by
  have hinv : ((f.prodCongr (LinearEquiv.refl F Z))⁻¹ : (E × Z) ≃ₗ[F] (E × Z)) =
      (f⁻¹ : E ≃ₗ[F] E).prodCongr (LinearEquiv.refl F Z) := by
    ext x <;> rfl
  unfold glMaxNorm
  rw [hinv]
  apply le_antisymm
  · refine max_le (le_max_left _ _) (max_le ?_ ?_)
    · exact (norm_prodCongr_refl_le f).trans
        (max_le (le_max_of_le_right (le_max_left _ _)) (le_max_left _ _))
    · exact (norm_prodCongr_refl_le (f⁻¹ : E ≃ₗ[F] E)).trans
        (max_le (le_max_of_le_right (le_max_right _ _)) (le_max_left _ _))
  · refine max_le (le_max_left _ _) (max_le ?_ ?_)
    · exact (norm_le_norm_prodCongr_refl (Z := Z) f).trans
        (le_max_of_le_right (le_max_left _ _))
    · exact (norm_le_norm_prodCongr_refl (Z := Z) (f⁻¹ : E ≃ₗ[F] E)).trans
        (le_max_of_le_right (le_max_right _ _))

/-- `‖f v‖ ≤ glMax(f) ‖v‖`. -/
theorem norm_apply_le_glMaxNorm (f : E ≃ₗ[F] E) (v : E) : ‖f v‖ ≤ glMaxNorm f * ‖v‖ := by
  have := (LinearMap.toContinuousLinearMap (f : E →ₗ[F] E)).le_opNorm v
  rw [LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe] at this
  exact this.trans (mul_le_mul_of_nonneg_right (norm_le_glMaxNorm f) (norm_nonneg _))

/-- `‖f⁻¹ v‖ ≤ glMax(f) ‖v‖`. -/
theorem norm_inv_apply_le_glMaxNorm (f : E ≃ₗ[F] E) (v : E) : ‖f⁻¹ v‖ ≤ glMaxNorm f * ‖v‖ := by
  have := norm_apply_le_glMaxNorm f⁻¹ v
  rwa [glMaxNorm_inv] at this

/-- `glMax(f) ≤ M` from pointwise bounds on `f` and `f⁻¹` (`M ≥ 1`). -/
theorem glMaxNorm_le_of_bound (f : E ≃ₗ[F] E) {M : ℝ} (hM : 1 ≤ M) (h1 : ∀ v, ‖f v‖ ≤ M * ‖v‖)
    (h2 : ∀ v, ‖f⁻¹ v‖ ≤ M * ‖v‖) : glMaxNorm f ≤ M := by
  refine max_le hM (max_le ?_ ?_) <;>
    refine ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hM) fun v => ?_ <;>
    rw [LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe]
  · exact h1 v
  · exact h2 v

/-- `glMax` is continuous on `GL(E)` (for the topology of `E ≃ₗ[F] E` induced by `(g, g⁻¹)`). -/
theorem continuous_glMaxNorm : Continuous (glMaxNorm : (E ≃ₗ[F] E) → ℝ) := by
  have : IsModuleTopology F (Module.End F E) := ⟨rfl⟩
  have h0 : Continuous fun f : Module.End F E => LinearMap.toContinuousLinearMap f :=
    IsModuleTopology.continuous_of_linearMap
      (LinearMap.toContinuousLinearMap : (E →ₗ[F] E) ≃ₗ[F] (E →L[F] E)).toLinearMap
  have h1 : Continuous fun g : E ≃ₗ[F] E => LinearMap.toContinuousLinearMap (g : E →ₗ[F] E) :=
    h0.comp TauCeti.continuous_linearEquiv_toLinearMap
  have h2 : Continuous fun g : E ≃ₗ[F] E =>
      LinearMap.toContinuousLinearMap ((g⁻¹ : E ≃ₗ[F] E) : E →ₗ[F] E) :=
    h1.comp continuous_inv
  exact continuous_const.max (h1.norm.max h2.norm)

omit [PAdicField F] in
/-- The basis vectors `z_k` of `Z = F^{2r+1}` have sup norm `≤ 1`. -/
theorem norm_zvec_le (r : ℕ) (k : ℤ) : ‖(zvec r k : Fin (2 * r + 1) → F)‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
    unfold zvec; split_ifs <;> simp

end GLNorm

section Basis

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace F V] [FiniteDimensional F V]
  {n : ℕ} {b : Basis (Fin n) F V} {Q : QuadraticForm F V}

/-- On the orthogonal group, `max(1, ‖g‖, ‖g⁻¹‖)` (operator norms) and `max(1, ‖g‖_b)` (the matrix
norm in an orthogonal basis) are equivalent: `‖g⁻¹‖_b ≤ κ ‖g‖_b`
(`IsOrthoBasis.basisOpNorm_symm_le`). -/
theorem IsOrthoBasis.exists_glMaxNorm_equiv (hb : IsOrthoBasis Q b) :
    ∃ K, 1 ≤ K ∧ ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      glMaxNorm g ≤ K * max 1 (basisOpNorm b (g : V →ₗ[F] V)) ∧
      max 1 (basisOpNorm b (g : V →ₗ[F] V)) ≤ K * glMaxNorm g := by
  obtain ⟨C, hC, hCb⟩ := exists_norm_toContinuousLinearMap_le_basisOpNorm b
  obtain ⟨c, hc, hcb⟩ := exists_basisOpNorm_le_norm_toContinuousLinearMap b
  set κ := max 1 (adjBound Q b)
  have hκ : 1 ≤ κ := le_max_left _ _
  refine ⟨max 1 (max (C * κ) c), le_max_left _ _, fun g hg => ⟨?_, ?_⟩⟩
  · set M := max 1 (basisOpNorm b (g : V →ₗ[F] V))
    have hM : 1 ≤ M := le_max_left _ _
    have hK : C * κ ≤ max 1 (max (C * κ) c) := le_max_of_le_right (le_max_left _ _)
    have hgM : basisOpNorm b (g : V →ₗ[F] V) ≤ M := le_max_right _ _
    have h1 : ‖LinearMap.toContinuousLinearMap (g : V →ₗ[F] V)‖ ≤ C * κ * M :=
      (hCb _).trans (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          ((hgM.trans_eq (one_mul M).symm).trans (mul_le_mul_of_nonneg_right hκ
            (zero_le_one.trans hM))) hC)
    have h2 : ‖LinearMap.toContinuousLinearMap ((g⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V)‖ ≤ C * κ * M := by
      refine (hCb _).trans ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ((hb.basisOpNorm_symm_le hg).trans ?_) hC
      exact mul_le_mul (le_max_right _ _) hgM (basisOpNorm_nonneg _) (zero_le_one.trans hκ)
    unfold glMaxNorm
    refine max_le ?_ (max_le ?_ ?_)
    · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) hM
    · exact h1.trans (mul_le_mul_of_nonneg_right hK (zero_le_one.trans hM))
    · exact h2.trans (mul_le_mul_of_nonneg_right hK (zero_le_one.trans hM))
  · have hG : 1 ≤ glMaxNorm g := one_le_glMaxNorm g
    refine max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hG) ?_
    refine (hcb _).trans (mul_le_mul (le_max_of_le_right (le_max_right _ _))
      (norm_le_glMaxNorm g) (norm_nonneg _) (zero_le_one.trans (le_max_left _ _)))

end Basis

/-! ### `σ` and the matrix entries of `g` and `g⁻¹`

`logNorm F G g = 1 + log max(1, ‖g‖, ‖g⁻¹‖)` uses operator norms of left multiplication on `A`.
In Waldspurger 2003 (§I.1 p. 242) and Kottwitz 2005 (§18.2, (18.2.1)) the norm of `g` is the
largest absolute value of a coordinate function among a set of generators of the coordinate ring
of `G`; for `G ⊆ GL(A)` acting by left multiplication, the matrix entries of `L_g` and `L_{g⁻¹}`
in a basis `b` of `A` are such generators, and their norm is `entryMaxNorm b`. The two log-norms
are equivalent (`logNorm_equiv_entryMaxNorm`). -/

section EntryNorm

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
  {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A]
  [IsModuleTopology F A] {n : ℕ} (b : Basis (Fin n) F A)

/-- `max(1, sup_{i,j} |(L_g)_{ij}|, sup_{i,j} |(L_{g⁻¹})_{ij}|)`: the largest absolute value of a
matrix entry of left multiplication by `g` or by `g⁻¹` on `A`, in the basis `b`. When these
entries generate the coordinate ring of `G ⊆ GL(A)` (e.g. `G = GSpin(W) × GSpin(V)` in
`A = C(W) × C(V)`), this is a norm in the sense of Kottwitz 2005, (18.2.1), and Waldspurger's
`‖g‖` (2003, §I.1 p. 242) for `τ(g) = L_g`. -/
def entryMaxNorm (G : Subgroup Aˣ) (g : ↥G) : ℝ :=
  max 1 (max (basisOpNorm b (LinearMap.mulLeft F ((g : Aˣ) : A)))
    (basisOpNorm b (LinearMap.mulLeft F (((g⁻¹ : ↥G) : Aˣ) : A))))

omit [PAdicField F] [Module.Finite F A] [TopologicalSpace A] [IsModuleTopology F A] in
theorem one_le_entryMaxNorm (G : Subgroup Aˣ) (g : ↥G) : 1 ≤ entryMaxNorm b G g :=
  le_max_left _ _

/-- The matrix of `lmulPi a` in the transported basis is the matrix of `L_a` in `b`. -/
theorem basisOpNorm_lmulPi (a : A) :
    basisOpNorm (b.map (toPiCLE F A).toLinearEquiv) (lmulPi F a : _ →ₗ[F] _) =
      basisOpNorm b (LinearMap.mulLeft F a) := by
  simp [basisOpNorm, lmulPi_apply, Basis.map_equivFun]

/-- **`max(1, ‖g‖, ‖g⁻¹‖)` and `entryMaxNorm b g` are equivalent**: operator norms and sup norms
of matrices on the finite-dimensional space `A ≅ F^d` are equivalent. -/
theorem exists_maxNorm_equiv_entryMaxNorm (G : Subgroup Aˣ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ g : ↥G,
      maxNorm F G g ≤ C * entryMaxNorm b G g ∧ entryMaxNorm b G g ≤ C * maxNorm F G g := by
  set b' := b.map (toPiCLE F A).toLinearEquiv
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_toContinuousLinearMap_le_basisOpNorm b'
  obtain ⟨C₂, hC₂, h₂⟩ := exists_basisOpNorm_le_norm_toContinuousLinearMap b'
  set C := max 1 (max C₁ C₂)
  have hC : 1 ≤ C := le_max_left _ _
  have hC1 : C₁ ≤ C := le_max_of_le_right (le_max_left _ _)
  have hC2 : C₂ ≤ C := le_max_of_le_right (le_max_right _ _)
  -- `‖lmulPi a‖ ≤ C₁ ‖L_a‖_b` and `‖L_a‖_b ≤ C₂ ‖lmulPi a‖`
  have e1 : ∀ a : A, ‖lmulPi F a‖ ≤ C₁ * basisOpNorm b (LinearMap.mulLeft F a) := fun a => by
    have := h₁ (lmulPi F a : _ →ₗ[F] _)
    rwa [basisOpNorm_lmulPi,
      (LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap _ _).2 rfl] at this
  have e2 : ∀ a : A, basisOpNorm b (LinearMap.mulLeft F a) ≤ C₂ * ‖lmulPi F a‖ := fun a => by
    have := h₂ (lmulPi F a : _ →ₗ[F] _)
    rwa [basisOpNorm_lmulPi,
      (LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap _ _).2 rfl] at this
  refine ⟨C, hC, fun g => ⟨?_, ?_⟩⟩
  · have hE := one_le_entryMaxNorm b G g
    have hE0 : 0 ≤ entryMaxNorm b G g := zero_le_one.trans hE
    have k : ∀ x, x ≤ entryMaxNorm b G g → C₁ * x ≤ C * entryMaxNorm b G g := fun x hx =>
      (mul_le_mul_of_nonneg_left hx hC₁).trans (mul_le_mul_of_nonneg_right hC1 hE0)
    refine max_le (one_le_mul_of_one_le_of_one_le hC hE) (max_le ?_ ?_)
    · exact (e1 _).trans (k _ (le_max_of_le_right (le_max_left _ _)))
    · exact (e1 _).trans (k _ (le_max_of_le_right (le_max_right _ _)))
  · have hM := one_le_maxNorm (F := F) G g
    have hM0 : 0 ≤ maxNorm F G g := zero_le_one.trans hM
    have k : ∀ x, x ≤ maxNorm F G g → C₂ * x ≤ C * maxNorm F G g := fun x hx =>
      (mul_le_mul_of_nonneg_left hx hC₂).trans (mul_le_mul_of_nonneg_right hC2 hM0)
    refine max_le (one_le_mul_of_one_le_of_one_le hC hM) (max_le ?_ ?_)
    · exact (e2 _).trans (k _ (le_max_of_le_right (le_max_left _ _)))
    · exact (e2 _).trans (k _ (le_max_of_le_right (le_max_right _ _)))

/-- **`σ` and the log of the matrix-entry norm are equivalent**: there is `C` with
`logNorm F G g ≤ C (1 + log entryMaxNorm b g)` and `1 + log entryMaxNorm b g ≤ C logNorm F G g`
for all `g`. -/
theorem logNorm_equiv_entryMaxNorm (G : Subgroup Aˣ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ↥G,
      logNorm F G g ≤ C * (1 + Real.log (entryMaxNorm b G g)) ∧
        1 + Real.log (entryMaxNorm b G g) ≤ C * logNorm F G g := by
  obtain ⟨C, hC, h⟩ := exists_maxNorm_equiv_entryMaxNorm b G
  refine ⟨1 + Real.log C + 1, by linarith [Real.log_nonneg hC], fun g => ⟨?_, ?_⟩⟩
  · have := one_add_log_le_of_le_mul_pow (n := 1) (one_le_maxNorm (F := F) G g)
      (one_le_entryMaxNorm b G g) hC (by simpa using (h g).1)
    simpa [logNorm] using this
  · have := one_add_log_le_of_le_mul_pow (n := 1) (one_le_entryMaxNorm b G g)
      (one_le_maxNorm (F := F) G g) hC (by simpa using (h g).2)
    simpa [logNorm] using this

end EntryNorm

/-! ### `G → Ḡ = SO(W) × SO(V)` -/

namespace GGPData

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
variable (d : GGPData F)

/-- The log-norm of `Ḡ = SO(W) × SO(V)` (BP §1.2, Thesis §2.2):
`σ_{Ḡ}(h) = 1 + log max(1, ‖h₁‖, ‖h₁⁻¹‖, ‖h₂‖, ‖h₂⁻¹‖)`, with the operator norms on
`W = F^m` and `V = W ⊕ Z` (sup norms). -/
def logNormSO (h : d.GbarGrp) : ℝ :=
  1 + Real.log (max (glMaxNorm (h.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)))
    (glMaxNorm (h.2 : d.V ≃ₗ[F] d.V)))

/-- `σ_{SO}(g₁, g₂) = 1 + log max(glMax(g₁ ⊕ 1), glMax(g₂))`: everything on `V`. -/
theorem logNormSO_eq (g : d.GbarGrp) :
    d.logNormSO g = 1 + Real.log (max (glMaxNorm (d.extZ (g.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))))
      (glMaxNorm (g.2 : d.V ≃ₗ[F] d.V))) := by
  rw [logNormSO]
  congr 3
  exact (glMaxNorm_prodCongr_refl (Z := d.Z) _).symm

/-- `σ_{SO}(1) = 1`. -/
theorem logNormSO_one : d.logNormSO 1 = 1 := by
  simp only [logNormSO, Prod.fst_one, Prod.snd_one, OneMemClass.coe_one, glMaxNorm_one, max_self,
    Real.log_one, add_zero]

theorem one_le_max_glMaxNorm (h : d.GbarGrp) :
    1 ≤ max (glMaxNorm (h.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)))
      (glMaxNorm (h.2 : d.V ≃ₗ[F] d.V)) :=
  le_max_of_le_left (one_le_glMaxNorm _)

/-- `σ_{Ḡ} ≥ 1`. -/
theorem one_le_logNormSO (h : d.GbarGrp) : 1 ≤ d.logNormSO h := by
  unfold logNormSO; linarith [Real.log_nonneg (d.one_le_max_glMaxNorm h)]

/-- `σ_{Ḡ}(h⁻¹) = σ_{Ḡ}(h)`. -/
theorem logNormSO_inv (h : d.GbarGrp) : d.logNormSO h⁻¹ = d.logNormSO h := by
  simp only [logNormSO, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv, glMaxNorm_inv]

/-- `σ_{Ḡ}` is subadditive. -/
theorem logNormSO_mul_le (h k : d.GbarGrp) :
    d.logNormSO (h * k) ≤ d.logNormSO h + d.logNormSO k := by
  have hh := d.one_le_max_glMaxNorm h
  have hk := d.one_le_max_glMaxNorm k
  have hmax : max (glMaxNorm ((h * k).1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)))
      (glMaxNorm ((h * k).2 : d.V ≃ₗ[F] d.V)) ≤
      max (glMaxNorm (h.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))) (glMaxNorm (h.2 : d.V ≃ₗ[F] d.V)) *
        max (glMaxNorm (k.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)))
          (glMaxNorm (k.2 : d.V ≃ₗ[F] d.V)) := max_le
    ((glMaxNorm_mul_le (h.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) k.1).trans
      (mul_le_mul (le_max_left _ _) (le_max_left _ _)
        (zero_le_one.trans (one_le_glMaxNorm _)) (by linarith)))
    ((glMaxNorm_mul_le (h.2 : d.V ≃ₗ[F] d.V) k.2).trans
      (mul_le_mul (le_max_right _ _) (le_max_right _ _)
        (zero_le_one.trans (one_le_glMaxNorm _)) (by linarith)))
  have := Real.log_le_log (by linarith [d.one_le_max_glMaxNorm (h * k)]) hmax
  rw [Real.log_mul (by linarith) (by linarith)] at this
  unfold logNormSO; linarith

/-! ### The scalars -/

/-- The central scalars `Z(F) = F^× × F^× ⊆ G(F)`: the elements `scalarPair c₁ c₂`.
This is `ker P̄` (`scalars_eq_ker`). -/
def scalars : Subgroup d.G := (d.pair.comp ((scalarGSpin d.QW).prodMap (scalarGSpin d.QV))).range

theorem scalarPair_mem_scalars (c₁ c₂ : Fˣ) : d.scalarPair c₁ c₂ ∈ d.scalars :=
  ⟨(c₁, c₂), rfl⟩

/-- `Z = ker P̄` (`exists_scalarPair_of_specP_eq`). -/
theorem scalars_eq_ker : d.scalars = d.Pbar.ker := by
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    rw [MonoidHom.mem_ker]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact specP_scalarGSpin_eq_one c.1
    · exact specP_scalarGSpin_eq_one c.2
  · intro hg
    rw [MonoidHom.mem_ker] at hg
    have h1 : specP d.QW (d.fst g) = specP d.QW (d.fst 1) := by
      rw [map_one, map_one]; exact congrArg
        (fun x : d.GbarGrp => (x.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))) hg
    have h2 : specP d.QV (d.snd g) = specP d.QV (d.snd 1) := by
      rw [map_one, map_one]; exact congrArg (fun x : d.GbarGrp => (x.2 : d.V ≃ₗ[F] d.V)) hg
    obtain ⟨c₁, c₂, hc⟩ := d.exists_scalarPair_of_specP_eq h1 h2
    rw [hc, one_mul]
    exact d.scalarPair_mem_scalars c₁ c₂

theorem Pbar_eq_of_mem_scalars {z : d.G} (hz : z ∈ d.scalars) (g : d.G) :
    d.Pbar (z * g) = d.Pbar g := by
  rw [d.scalars_eq_ker, MonoidHom.mem_ker] at hz
  rw [map_mul, hz, one_mul]

/-- `Z ⊆ A_G`. -/
theorem scalars_le_AG : d.scalars ≤ d.AG := by
  rintro _ ⟨c, rfl⟩
  exact d.scalarPair_mem_AG c.1 c.2

/-- `A_{G,H} ⊆ Z`: the diagonal scalars are scalars. -/
theorem AGH_le_scalars : d.AGH ≤ d.scalars := by
  rintro _ ⟨c, rfl⟩
  refine ⟨(c, c), ?_⟩
  simp [diag, incl_scalarGSpin]

/-! ### Norms on `C(W) × C(V)` -/

/-- The underlying first component of `g⁻¹`. -/
theorem val_inv_fst (g : d.G) : (((g⁻¹ : d.G) : d.ambientˣ) : d.ambient).1 =
    ((((d.fst g : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) :
      CliffordAlgebra d.QW) := rfl

/-- The underlying second component of `g⁻¹`. -/
theorem val_inv_snd (g : d.G) : (((g⁻¹ : d.G) : d.ambientˣ) : d.ambient).2 =
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

/-! ### The comparison -/

/-- **`σ_{Ḡ}(P̄(g)) ≪ σ_G(g)`** (the easy half; `exists_norm_specP_le`). -/
theorem exists_logNormSO_Pbar_le :
    ∃ c, 0 ≤ c ∧ ∀ g : d.G, d.logNormSO (d.Pbar g) ≤ c * logNorm F d.G g := by
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
  rw [val_fst, val_snd] at b1
  rw [val_inv_fst, val_inv_snd] at b2
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
      mul_le_mul_of_nonneg_right (by simp only [K]; linarith) (by positivity)
    linarith
  have hKm : 1 ≤ K * m ^ 2 := one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hm)
  have hPW : glMaxNorm (specP d.QW (d.fst g)) ≤ K * m ^ 2 := by
    refine max_le hKm (max_le ?_ ?_)
    · exact (hW (d.fst g)).trans
        (key _ _ _ hCW (by linarith) (norm_nonneg _) (norm_nonneg _) f1 f3)
    · rw [← map_inv]
      refine (hW (d.fst g)⁻¹).trans ?_
      simp only [Subgroup.coe_inv, inv_inv]
      rw [mul_comm (‖_‖)]
      exact key _ _ _ hCW (by linarith) (norm_nonneg _) (norm_nonneg _) f1 f3
  have hPV : glMaxNorm (specP d.QV (d.snd g)) ≤ K * m ^ 2 := by
    refine max_le hKm (max_le ?_ ?_)
    · exact (hV (d.snd g)).trans
        (key _ _ _ hCV (by linarith) (norm_nonneg _) (norm_nonneg _) f2 f4)
    · rw [← map_inv]
      refine (hV (d.snd g)⁻¹).trans ?_
      simp only [Subgroup.coe_inv, inv_inv]
      rw [mul_comm (‖_‖)]
      exact key _ _ _ hCV (by linarith) (norm_nonneg _) (norm_nonneg _) f2 f4
  exact one_add_log_le_of_le_mul_pow (d.one_le_max_glMaxNorm _) hm hK (max_le hPW hPV)

/-- **Norm descent: some `z ∈ Z` has `σ_G(z g) ≪ σ_{Ḡ}(P̄(g))`** (the hard half;
`exists_scalar_norm_le` on each factor). -/
theorem exists_logNorm_scalars_mul_le :
    ∃ C, 0 ≤ C ∧ ∀ g : d.G, ∃ z ∈ d.scalars,
      logNorm F d.G (z * g) ≤ C * d.logNormSO (d.Pbar g) := by
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
  refine ⟨_, d.scalarPair_mem_scalars c₁ c₂, ?_⟩
  have hM : 1 ≤ max (glMaxNorm (specP d.QW (d.fst g))) (glMaxNorm (specP d.QV (d.snd g))) :=
    le_max_of_le_left (one_le_glMaxNorm _)
  have hMW : max 1 ‖LinearMap.toContinuousLinearMap (specP d.QW (d.fst g) :
      (Fin d.m → F) →ₗ[F] (Fin d.m → F))‖ ≤
      max (glMaxNorm (specP d.QW (d.fst g))) (glMaxNorm (specP d.QV (d.snd g))) :=
    le_max_of_le_left (max_le (one_le_glMaxNorm _) (norm_le_glMaxNorm _))
  have hMV : max 1 ‖LinearMap.toContinuousLinearMap (specP d.QV (d.snd g) :
      d.V →ₗ[F] d.V)‖ ≤
      max (glMaxNorm (specP d.QW (d.fst g))) (glMaxNorm (specP d.QV (d.snd g))) :=
    le_max_of_le_right (max_le (one_le_glMaxNorm _) (norm_le_glMaxNorm _))
  rw [logNormSO, Pbar_fst, Pbar_snd, logNorm]
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
  have e1 : d.fst (d.scalarPair c₁ c₂ * g) =
      scalarGSpin d.QW c₁ * d.fst g := by rw [map_mul]; rfl
  have e2 : d.snd (d.scalarPair c₁ c₂ * g) =
      scalarGSpin d.QV c₂ * d.snd g := by rw [map_mul]; rfl
  obtain ⟨hamb, hamb'⟩ := hfs _ _ _ e1 e2
  have hmax : maxNorm F d.G (d.scalarPair c₁ c₂ * g) ≤
      K * M ^ (NW + NV) := by
    have hKN : Ca * (max CW CV * M ^ (NW + NV)) ≤ K * M ^ (NW + NV) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (by rw [hKd]; linarith) (by positivity)
    refine max_le (one_le_mul_of_one_le_of_one_le hK hMN) (max_le ?_ ?_)
    · exact hamb.trans ((mul_le_mul_of_nonneg_left (max_le b1 b2) hCa).trans hKN)
    · exact hamb'.trans ((mul_le_mul_of_nonneg_left (max_le b3 b4) hCa).trans hKN)
  exact one_add_log_le_of_le_mul_pow (one_le_maxNorm _ _) hM hK hmax

/-- `σ_{S\G} ∼ σ_{Ḡ} ∘ P̄` pushed forward to `S\G`, for `S ⊇ Z` (helper for
`infLeft_equiv_of_scalars_le`). -/
theorem infLeft_comp_equiv_of_scalars_le {S : Subgroup d.G} (hS : d.scalars ≤ S) :
    ∃ c C, 0 ≤ c ∧ 0 ≤ C ∧ ∀ g : d.G,
      infLeft (d.logNormSO ∘ d.Pbar) S g ≤ c * infLeft (logNorm F d.G) S g ∧
      infLeft (logNorm F d.G) S g ≤ C * infLeft (d.logNormSO ∘ d.Pbar) S g := by
  obtain ⟨c, hc, hcle⟩ := d.exists_logNormSO_Pbar_le
  obtain ⟨C, hC, hCle⟩ := d.exists_logNorm_scalars_mul_le
  have hτ : ∀ g, 0 ≤ (d.logNormSO ∘ d.Pbar) g :=
    fun g => zero_le_one.trans (d.one_le_logNormSO _)
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
      d.logNormSO (d.Pbar g) ≤ c * infLeft (logNorm F d.G) d.scalars g ∧
      infLeft (logNorm F d.G) d.scalars g ≤ C * d.logNormSO (d.Pbar g) := by
  obtain ⟨c, C, hc, hC, h⟩ := d.infLeft_comp_equiv_of_scalars_le le_rfl
  have hconst : ∀ g, infLeft (d.logNormSO ∘ d.Pbar) d.scalars g = d.logNormSO (d.Pbar g) := by
    intro g
    have : ∀ s : d.scalars, (d.logNormSO ∘ d.Pbar) ((s : d.G) * g) = d.logNormSO (d.Pbar g) :=
      fun s => by simp only [Function.comp_apply, d.Pbar_eq_of_mem_scalars s.2]
    simp only [infLeft, this, ciInf_const]
  exact ⟨c, C, hc, hC, fun g => by simpa only [hconst] using h g⟩

/-- **`σ_{S\G}(g) ∼ σ_{P̄(S)\Ḡ}(P̄(g))` for `S ⊇ Z`**: with `σ_{P̄(S)\Ḡ}(h) =
inf_{s ∈ P̄(S)} σ_{Ḡ}(s h)` (the push-forward of `σ_{Ḡ}` to `P̄(S)\Ḡ`), there are `c, C ≥ 0` with
`σ_{P̄(S)\Ḡ}(P̄(g)) ≤ c σ_{S\G}(g)` and `σ_{S\G}(g) ≤ C σ_{P̄(S)\Ḡ}(P̄(g))`. -/
theorem infLeft_equiv_of_scalars_le {S : Subgroup d.G} (hS : d.scalars ≤ S) :
    ∃ c C, 0 ≤ c ∧ 0 ≤ C ∧ ∀ g : d.G,
      infLeft d.logNormSO (S.map d.Pbar) (d.Pbar g) ≤ c * infLeft (logNorm F d.G) S g ∧
      infLeft (logNorm F d.G) S g ≤ C * infLeft d.logNormSO (S.map d.Pbar) (d.Pbar g) := by
  obtain ⟨c, C, hc, hC, h⟩ := d.infLeft_comp_equiv_of_scalars_le hS
  have e : ∀ g, infLeft d.logNormSO (S.map d.Pbar) (d.Pbar g) =
      infLeft (d.logNormSO ∘ d.Pbar) S g :=
    infLeft_map S d.Pbar fun x => zero_le_one.trans (d.one_le_logNormSO x)
  exact ⟨c, C, hc, hC, fun g => by simpa only [e] using h g⟩

/-- **`σ_{A_G\G} ∼ σ_{Ā_G\Ḡ} ∘ P̄`**: the log-norm `σ_{A_G\G}` of `𝒞(A_G(F)\G(F), χ⁻¹)`
(`GGPData.logNormModAG` is by definition `infLeft (logNorm F d.G) d.AG`) is equivalent to the
push-forward of `σ_{Ḡ}` to `Ā_G\Ḡ` (`Ā_G = P̄(A_G)`, `GGPData.AGbar`) at `P̄(g)`. -/
theorem logNormModAG_equiv :
    ∃ c C, 0 ≤ c ∧ 0 ≤ C ∧ ∀ g : d.G,
      infLeft d.logNormSO d.AGbar (d.Pbar g) ≤ c * infLeft (logNorm F d.G) d.AG g ∧
      infLeft (logNorm F d.G) d.AG g ≤ C * infLeft d.logNormSO d.AGbar (d.Pbar g) :=
  d.infLeft_equiv_of_scalars_le d.scalars_le_AG

end GGPData

end GSpinGGP
