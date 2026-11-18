/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.GoodParabolicSO
import GSpinGGP.TraceFormula.LogNormDescent

/-!
# The estimates of the good minimal parabolic of `G₀`, lifted to `GSpin`

Let `d` be a GGP datum with `r = 0`, so that `G = G₀ = GSpin(W) × GSpin(V₀)` with
`V₀ = W ⊕ F z₀`, and `H = H₀ = GSpin(W)` embedded diagonally (Thesis §5.2, §8.1). Let `b` be an
orthogonal basis of `V₀` whose first `l + 1` vectors form a maximal frame `w₀ = b 0, …, w_l`
(`IsFrame`), with `w₀ ∈ F z₀`. Then `SO(W)`, acting on `V₀` by `g ↦ g ⊕ 1`
(`GGPData.extZ`), is the stabilizer `fixer Q b 1` of `w₀`, and the split tori and chambers of the
good minimal parabolic `P̄₀ = P̄_W × P̄_{V₀}` of the proof of Thesis Prop. 8.1.1(i) are those of
`GSpinGGP.Foundations.GoodParabolicSO`: `A₀⁺` consists of the `(a_W, a_V)` with
`a_W ⊕ 1 = (multiTorus hb hf 1 s)⁻¹`, `a_V = (multiTorus hb hf 0 t)⁻¹`, `s`, `t` in the contracting
chambers `InChamber`.

Since `P̄ : G → SO(W) × SO(V₀)` has central kernel the scalars `Z = F^× × F^×`
(`GGPData.scalars_eq_ker`), the roots of the split torus of `G₀` factor through `P̄`, so the
expanding chamber of `G₀` is the preimage under `P̄` of the chamber above. The two inequalities of
Thesis Prop. 8.1.1(iii) (BP Prop. 6.4.1(iii)) for `G₀` are proved here for this preimage:

* (I) `σ(h) + σ(a) ≪ σ(h a)`: at the level of `SO` (`GGPData.logNormSO_add_le_of_chamber`,
  for `σ_{SO}`, with any `W`-component), modulo the scalars (`GGPData.logNormModScalars_add_le`)
  and modulo `A_G` (`GGPData.logNormModAG_le_of_chamber`, the form `σ_{A_G\G}(a) ≪ σ_{A_G\G}(h a)`
  used in Thesis Prop. 8.4.1(ii)(b), BP (6.7.6));
* (II) `σ(h) ≪ σ(a⁻¹ h a)`: at the level of `SO` (`GGPData.logNormSO_le_conj_of_chamber`) and
  modulo the scalars (`GGPData.logNormModScalars_le_conj`).

The thesis states (I), (II) for the log-norm modulo `A_{G,H}` (the diagonal scalars). Modulo the
full scalars `Z ⊋ A_{G,H}` the statements are weaker by the term `|log |μ||`, `μ = N(g₂)/N(g₁)`
(`(P̄, μ)` has finite kernel on `G₀/A_{G,H}`); `μ` is trivial on `H`, so this term does not affect
the use modulo `A_G` in Thesis Prop. 8.4.1. It is not formalised here.

Only `F` `p`-adic (`PAdicField`) is treated. The reduction from `G` to `G₀` (Thesis proof of
Prop. 8.1.1(iii), first part) is not formalised here.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Module

namespace GSpinGGP

/-! ## Extension by the identity -/

section ProdCongr

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
  {E Z : Type*} [NormedAddCommGroup E] [NormedSpace F E] [FiniteDimensional F E]
  [NormedAddCommGroup Z] [NormedSpace F Z] [FiniteDimensional F Z]

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

end ProdCongr

/-! ## Operator norms and matrix norms on the orthogonal group -/

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

namespace GGPData

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
variable (d : GGPData F)

open WeakCartan

/-! ## `SO(W) ⊆ SO(V₀)` and `H₀` -/

/-- `SO(W) → GL(V)`, `g ↦ g ⊕ 1` on `V = W ⊕ Z`. -/
def extZ : ((Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) →* (d.V ≃ₗ[F] d.V) where
  toFun f := f.prodCongr (LinearEquiv.refl F d.Z)
  map_one' := by ext x <;> rfl
  map_mul' f g := by ext x <;> rfl

theorem extZ_apply (f : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) (v : d.V) :
    d.extZ f v = (f v.1, v.2) := rfl

/-- `σ_{SO}(g₁, g₂) = 1 + log max(glMax(g₁ ⊕ 1), glMax(g₂))`: everything on `V`. -/
theorem logNormSO_eq (g : d.GbarGrp) :
    d.logNormSO g = 1 + Real.log (max (glMaxNorm (d.extZ (g.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))))
      (glMaxNorm (g.2 : d.V ≃ₗ[F] d.V))) := by
  rw [logNormSO]
  congr 3
  exact (glMaxNorm_prodCongr_refl (Z := d.Z) _).symm

/-- For `r = 0` (so `N = 1`), the `V`-component of `P̄(h)`, `h ∈ H`, is the `W`-component extended
by the identity on `Z`: `H = GSpin(W)` acts on `V₀ = W ⊕ Z` through `SO(W)`. -/
theorem Pbar_snd_of_mem_H (hr : d.r = 0) {h : d.G} (hh : h ∈ d.H) :
    ((d.Pbar h).2 : d.V ≃ₗ[F] d.V) = d.extZ ((d.Pbar h).1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) := by
  have htop : d.flag.top = ⊥ := by
    change Submodule.span F (Set.range fun j : Fin d.r => d.zV ((d.r : ℤ) - (j : ℕ))) = ⊥
    rw [Submodule.span_eq_bot]
    rintro _ ⟨j, rfl⟩
    exact absurd j.2 (by omega)
  have hn : specP d.QV (d.nPart h) = 1 := by
    obtain ⟨-, -, h3, -⟩ := hh
    refine LinearEquiv.ext fun v => ?_
    have := h3 v (by rw [htop]; simp)
    rw [htop, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  have hs : d.snd h = d.incl (d.fst h) * d.nPart h := by simp [nPart]
  rw [Pbar_snd, Pbar_fst, hs, map_mul, hn, mul_one]
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨w, z⟩ := v
  have e : ((w, z) : d.V) = (w, 0) + (0, z) := by simp
  rw [e, map_add, map_add, d.specP_incl_inl, d.specP_incl_inr, extZ_apply, extZ_apply]
  simp

variable {n : ℕ} {b : Basis (Fin n) F d.V} (hb : IsOrthoBasis d.QV b) {ν : F} {l : ℕ}
  (hf : IsFrame d.QV b ν l)

/-- The image of an element of `SO(W)` in `SO(V)` fixes `w₀ = b 0` when `w₀ ∈ Z`. -/
theorem extZ_mem_fixer (hb0 : ∀ i : Fin n, (i : ℕ) = 0 → (b i).1 = 0)
    (g : SOGrp d.QW) : d.extZ (g : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) ∈ fixer d.QV b 1 := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [← SOGrp_eq_specialOrthogonalGroup]
    refine ⟨fun v => ?_, ?_⟩
    · rw [extZ_apply]
      change d.QW ((g : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) v.1) + d.QZ v.2 = d.QW v.1 + d.QZ v.2
      rw [g.2.1]
    · show LinearMap.det ((g : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)).prodCongr
        (LinearEquiv.refl F d.Z) : d.V →ₗ[F] d.V) = 1
      rw [LinearEquiv.coe_prodCongr, LinearMap.det_prodMap, g.2.2]
      simp
  · have h0 := hb0 i (by omega)
    rw [extZ_apply]
    exact Prod.ext (by simp only [h0, map_zero]) rfl

/-! ## Inequality (I) -/

-- The products in `SO(W) × SO(V)` make instance search slow here.
set_option maxHeartbeats 400000 in
include hb in
/-- **Thesis Prop. 8.1.1(iii), first inequality, for `SO(W) × SO(V₀)` in log-norm form**
(BP Prop. 6.4.1(iii), (6.4.1)): with `σ_{SO} = logNormSO`, for `h ∈ H` and `y = (y_W, y_V)` with
`y_V = (multiTorus hb hf 0 t)⁻¹`, `t` in the contracting chamber of the `V₀`-torus, and `y_W`
arbitrary, `σ_{SO}(P̄ h) + σ_{SO}(y) ≤ C σ_{SO}(P̄(h) y)`. (No condition on the `W`-component is
needed: `‖y_W‖ ≤ ‖h⁻¹‖ ‖h y_W‖`, `norm_le_of_mem_chamber`.) Here `G = G₀` (`r = 0`), and the frame
starts at `w₀ = b 0 ∈ Z`. -/
theorem logNormSO_add_le_of_chamber (hr : d.r = 0) (hb0 : ∀ i : Fin n, (i : ℕ) = 0 → (b i).1 = 0) :
    ∃ C, 0 ≤ C ∧ ∀ h ∈ d.H, ∀ y : d.GbarGrp, ∀ t : List Fˣ, InChamber n l 0 t →
      (y.2 : d.V ≃ₗ[F] d.V) = (multiTorus hb hf 0 t)⁻¹ →
      d.logNormSO (d.Pbar h) + d.logNormSO y ≤ C * d.logNormSO (d.Pbar h * y) := by
  obtain ⟨C₀, N, hCN⟩ := norm_le_of_mem_chamber hb hf
  obtain ⟨K, hK, hKe⟩ := hb.exists_glMaxNorm_equiv
  set C₁ := max 1 C₀
  have hC₁ : 1 ≤ C₁ := le_max_left _ _
  set K' := K * C₁ * K ^ N
  have hK' : 1 ≤ K' := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hK hC₁) (one_le_pow₀ hK)
  set c := 1 + Real.log K' + (N : ℝ)
  have hc : 0 ≤ c := by have := Real.log_nonneg hK'; positivity
  refine ⟨2 * c, by positivity, fun h hh y t ht hy => ?_⟩
  set hV : d.V ≃ₗ[F] d.V := ((d.Pbar h).2 : d.V ≃ₗ[F] d.V)
  have hVe : hV = d.extZ ((d.Pbar h).1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) :=
    d.Pbar_snd_of_mem_H hr hh
  have hVfix : hV ∈ fixer d.QV b 1 := hVe ▸ d.extZ_mem_fixer hb0 _
  set aW := d.extZ (y.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))
  set aV : d.V ≃ₗ[F] d.V := (y.2 : d.V ≃ₗ[F] d.V)
  have hO : ∀ g : SOGrp d.QV, (g : d.V ≃ₗ[F] d.V) ∈ TauCeti.QuadraticMap.orthogonalGroup d.QV :=
    fun g => TauCeti.QuadraticMap.specialOrthogonalGroup_le_orthogonalGroup _
      (SOGrp_eq_specialOrthogonalGroup d.QV ▸ g.2)
  have hOW : ∀ g : SOGrp d.QW, d.extZ (g : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) ∈
      TauCeti.QuadraticMap.orthogonalGroup d.QV := fun g =>
    mem_orthogonalGroup_of_mem_fixer (d.extZ_mem_fixer hb0 g)
  -- the multiplicative inequality
  have key := hCN hV hVfix aW t ht
  rw [← hy] at key
  set M := max 1 (max (basisOpNorm b ((hV * aW : d.V ≃ₗ[F] d.V) : d.V →ₗ[F] d.V))
    (basisOpNorm b ((hV * aV : d.V ≃ₗ[F] d.V) : d.V →ₗ[F] d.V)))
  have hM : 1 ≤ M := le_max_left _ _
  -- `M ≤ K Φ(P̄(h) y)`
  set B := max (glMaxNorm (d.extZ ((d.Pbar h * y).1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))))
    (glMaxNorm ((d.Pbar h * y).2 : d.V ≃ₗ[F] d.V))
  have hB : 1 ≤ B := le_max_of_le_left (one_le_glMaxNorm _)
  have e1 : d.extZ ((d.Pbar h * y).1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) = hV * aW := by
    rw [hVe, ← map_mul, Prod.fst_mul, Subgroup.coe_mul]
  have e2 : ((d.Pbar h * y).2 : d.V ≃ₗ[F] d.V) = hV * aV := by
    rw [Prod.snd_mul, Subgroup.coe_mul]
  have hMB : M ≤ K * B := by
    have m1 := (hKe (hV * aW) (by rw [← e1]; exact hOW (d.Pbar h * y).1)).2
    have m2 := (hKe (hV * aV) (by rw [← e2]; exact hO (d.Pbar h * y).2)).2
    have hK0 : 0 ≤ K := zero_le_one.trans hK
    refine max_le (one_le_mul_of_one_le_of_one_le hK hB) (max_le ?_ ?_)
    · refine ((le_max_right _ _).trans m1).trans (mul_le_mul_of_nonneg_left ?_ hK0)
      rw [← e1]; exact le_max_left _ _
    · refine ((le_max_right _ _).trans m2).trans (mul_le_mul_of_nonneg_left ?_ hK0)
      rw [← e2]; exact le_max_right _ _
  have hMN : C₁ * M ^ N ≤ C₁ * K ^ N * B ^ N := by
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hM) hMB N)
      (zero_le_one.trans hC₁)
  have hC₀M : C₀ * M ^ N ≤ C₁ * M ^ N :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (zero_le_one.trans hM) _)
  -- a bound `glMax g ≤ K' B^N` for each `g` controlled by `key`
  have bound : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup d.QV,
      basisOpNorm b (g : d.V →ₗ[F] d.V) ≤ C₀ * M ^ N → glMaxNorm g ≤ K' * B ^ N := by
    intro g hg hgb
    have : max 1 (basisOpNorm b (g : d.V →ₗ[F] d.V)) ≤ C₁ * K ^ N * B ^ N :=
      max_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC₁
        (one_le_pow₀ hK)) (one_le_pow₀ hB)) ((hgb.trans hC₀M).trans hMN)
    calc glMaxNorm g ≤ K * max 1 (basisOpNorm b (g : d.V →ₗ[F] d.V)) := (hKe g hg).1
      _ ≤ K * (C₁ * K ^ N * B ^ N) := mul_le_mul_of_nonneg_left this (zero_le_one.trans hK)
      _ = K' * B ^ N := by ring
  have bh := bound hV (hO _) ((le_max_left _ _).trans key)
  have bW := bound aW (hOW _) ((le_max_left _ _).trans ((le_max_right _ _).trans key))
  have bV := bound aV (hO _) ((le_max_right _ _).trans ((le_max_right _ _).trans key))
  have lh : d.logNormSO (d.Pbar h) ≤ c * d.logNormSO (d.Pbar h * y) := by
    rw [logNormSO_eq, logNormSO_eq, ← hVe]
    rw [max_self]
    exact one_add_log_le_of_le_mul_pow (one_le_glMaxNorm _) hB hK' bh
  have ly : d.logNormSO y ≤ c * d.logNormSO (d.Pbar h * y) := by
    rw [logNormSO_eq, logNormSO_eq]
    exact one_add_log_le_of_le_mul_pow (le_max_of_le_left (one_le_glMaxNorm _)) hB hK'
      (max_le bW bV)
  linarith

/-! ## Inequality (II) -/

include hb in
/-- **Thesis Prop. 8.1.1(iii), second inequality, for `SO(W) × SO(V₀)` in log-norm form**
(BP Prop. 6.4.1(iii), (6.4.2)): for `h ∈ H` and `y = (y_W, y_V)` with
`y_W ⊕ 1 = (multiTorus hb hf 1 s)⁻¹`, `y_V = (multiTorus hb hf 0 t)⁻¹` and `s`, `t` in the
contracting chambers, `σ_{SO}(P̄ h) ≤ C σ_{SO}(y⁻¹ P̄(h) y)`. Here `G = G₀` (`r = 0`), and the
frame starts at `w₀ = b 0 ∈ Z`. -/
theorem logNormSO_le_conj_of_chamber (hr : d.r = 0)
    (hb0 : ∀ i : Fin n, (i : ℕ) = 0 → (b i).1 = 0) :
    ∃ C, 0 ≤ C ∧ ∀ h ∈ d.H, ∀ y : d.GbarGrp, ∀ s t : List Fˣ, InChamber n l 1 s →
      InChamber n l 0 t →
      d.extZ (y.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) = (multiTorus hb hf 1 s)⁻¹ →
      (y.2 : d.V ≃ₗ[F] d.V) = (multiTorus hb hf 0 t)⁻¹ →
      d.logNormSO (d.Pbar h) ≤ C * d.logNormSO (y⁻¹ * d.Pbar h * y) := by
  obtain ⟨C₀, hCN⟩ := norm_le_conj_of_mem_chamber hb hf
  obtain ⟨K, hK, hKe⟩ := hb.exists_glMaxNorm_equiv
  set C₁ := max 1 C₀
  have hC₁ : 1 ≤ C₁ := le_max_left _ _
  set K' := K * C₁ * K
  have hK' : 1 ≤ K' := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hK hC₁) hK
  set c := 1 + Real.log K' + ((1 : ℕ) : ℝ)
  have hc : 0 ≤ c := by have := Real.log_nonneg hK'; positivity
  refine ⟨c, hc, fun h hh y s t hs ht hyW hyV => ?_⟩
  set hV : d.V ≃ₗ[F] d.V := ((d.Pbar h).2 : d.V ≃ₗ[F] d.V)
  have hVe : hV = d.extZ ((d.Pbar h).1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) :=
    d.Pbar_snd_of_mem_H hr hh
  have hVfix : hV ∈ fixer d.QV b 1 := hVe ▸ d.extZ_mem_fixer hb0 _
  have hO : ∀ g : SOGrp d.QV, (g : d.V ≃ₗ[F] d.V) ∈ TauCeti.QuadraticMap.orthogonalGroup d.QV :=
    fun g => TauCeti.QuadraticMap.specialOrthogonalGroup_le_orthogonalGroup _
      (SOGrp_eq_specialOrthogonalGroup d.QV ▸ g.2)
  have hOW : ∀ g : SOGrp d.QW, d.extZ (g : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) ∈
      TauCeti.QuadraticMap.orthogonalGroup d.QV := fun g =>
    mem_orthogonalGroup_of_mem_fixer (d.extZ_mem_fixer hb0 g)
  have key := hCN hV hVfix s t hs ht
  set z := y⁻¹ * d.Pbar h * y
  have e1 : d.extZ (z.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) =
      multiTorus hb hf 1 s * hV * (multiTorus hb hf 1 s)⁻¹ := by
    have : (z.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) = (y.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))⁻¹ *
        ((d.Pbar h).1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) * (y.1 : _) := rfl
    rw [this, map_mul, map_mul, map_inv, hyW, ← hVe, inv_inv]
  have e2 : (z.2 : d.V ≃ₗ[F] d.V) = multiTorus hb hf 0 t * hV * (multiTorus hb hf 0 t)⁻¹ := by
    have : (z.2 : d.V ≃ₗ[F] d.V) = (y.2 : d.V ≃ₗ[F] d.V)⁻¹ * hV * (y.2 : _) := rfl
    rw [this, hyV, inv_inv]
  set B := max (glMaxNorm (d.extZ (z.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))))
    (glMaxNorm (z.2 : d.V ≃ₗ[F] d.V))
  have hB : 1 ≤ B := le_max_of_le_left (one_le_glMaxNorm _)
  set M := max 1 (max
    (basisOpNorm b ((multiTorus hb hf 0 t * hV * (multiTorus hb hf 0 t)⁻¹ : d.V ≃ₗ[F] d.V) :
      d.V →ₗ[F] d.V))
    (basisOpNorm b ((multiTorus hb hf 1 s * hV * (multiTorus hb hf 1 s)⁻¹ : d.V ≃ₗ[F] d.V) :
      d.V →ₗ[F] d.V)))
  have hM : 1 ≤ M := le_max_left _ _
  have hMB : M ≤ K * B := by
    have m1 := (hKe _ (hOW z.1)).2
    have m2 := (hKe _ (hO z.2)).2
    rw [e1] at m1
    rw [e2] at m2
    have hK0 : 0 ≤ K := zero_le_one.trans hK
    refine max_le (one_le_mul_of_one_le_of_one_le hK hB) (max_le ?_ ?_)
    · refine ((le_max_right _ _).trans m2).trans (mul_le_mul_of_nonneg_left ?_ hK0)
      rw [← e2]; exact le_max_right _ _
    · refine ((le_max_right _ _).trans m1).trans (mul_le_mul_of_nonneg_left ?_ hK0)
      rw [← e1]; exact le_max_left _ _
  have hbh : glMaxNorm hV ≤ K' * B ^ 1 := by
    have h1 : max 1 (basisOpNorm b (hV : d.V →ₗ[F] d.V)) ≤ C₁ * M :=
      max_le (one_le_mul_of_one_le_of_one_le hC₁ hM)
        (key.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans hM)))
    calc glMaxNorm hV ≤ K * max 1 (basisOpNorm b (hV : d.V →ₗ[F] d.V)) := (hKe hV (hO _)).1
      _ ≤ K * (C₁ * (K * B)) := mul_le_mul_of_nonneg_left
          (h1.trans (mul_le_mul_of_nonneg_left hMB (zero_le_one.trans hC₁)))
          (zero_le_one.trans hK)
      _ = K' * B ^ 1 := by ring
  rw [logNormSO_eq, logNormSO_eq, ← hVe, max_self]
  exact one_add_log_le_of_le_mul_pow (one_le_glMaxNorm _) hB hK' hbh

/-! ## The lift to `G = GSpin(W) × GSpin(V₀)` -/

/-- `σ_{SO}(1) = 1`. -/
theorem logNormSO_one : d.logNormSO 1 = 1 := by
  simp only [logNormSO, Prod.fst_one, Prod.snd_one, OneMemClass.coe_one, glMaxNorm_one, max_self,
    Real.log_one, add_zero]

include hb in
/-- **Thesis Prop. 8.1.1(iii), first inequality, for `G₀`, modulo the scalars** (BP (6.4.1)):
`σ_{Z\G}(h) + σ_{Z\G}(x) ≤ C σ_{Z\G}(h x)` for `h ∈ H` and `x ∈ G` whose `V₀`-component
`P̄(x)_V = (multiTorus hb hf 0 t)⁻¹` lies in the expanding chamber (`t` in the contracting chamber;
no condition on the `W`-component). Here `σ_{Z\G}(g) = inf_{z ∈ Z} σ_G(z g)`, `Z` the central
scalars. -/
theorem logNormModScalars_add_le (hr : d.r = 0)
    (hb0 : ∀ i : Fin n, (i : ℕ) = 0 → (b i).1 = 0) :
    ∃ C, 0 ≤ C ∧ ∀ h ∈ d.H, ∀ x : d.G, ∀ t : List Fˣ, InChamber n l 0 t →
      ((d.Pbar x).2 : d.V ≃ₗ[F] d.V) = (multiTorus hb hf 0 t)⁻¹ →
      infLeft (logNorm F d.G) d.scalars h + infLeft (logNorm F d.G) d.scalars x ≤
        C * infLeft (logNorm F d.G) d.scalars (h * x) := by
  obtain ⟨C₀, hC₀, hI⟩ := d.logNormSO_add_le_of_chamber hb hf hr hb0
  obtain ⟨c, C, hc, hC, he⟩ := d.logNormModScalars_equiv
  refine ⟨C * C₀ * c, by positivity, fun h hh x t ht hx => ?_⟩
  have key := hI h hh (d.Pbar x) t ht hx
  rw [← map_mul] at key
  have e1 := (he h).2
  have e2 := (he x).2
  have e3 := (he (h * x)).1
  calc infLeft (logNorm F d.G) d.scalars h + infLeft (logNorm F d.G) d.scalars x
      ≤ C * (d.logNormSO (d.Pbar h) + d.logNormSO (d.Pbar x)) := by linarith
    _ ≤ C * (C₀ * d.logNormSO (d.Pbar (h * x))) := mul_le_mul_of_nonneg_left key hC
    _ ≤ C * (C₀ * (c * infLeft (logNorm F d.G) d.scalars (h * x))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e3 hC₀) hC
    _ = C * C₀ * c * infLeft (logNorm F d.G) d.scalars (h * x) := by ring

-- The products in `SO(W) × SO(V)` make instance search slow here.
set_option maxHeartbeats 400000 in
include hb in
/-- **Thesis Prop. 8.1.1(iii), first inequality, for `G₀`, modulo `A_G`**, in the form used for
Thesis Prop. 8.4.1(ii)(b) (BP (6.7.6): `σ_{H\G}(a) ∼ σ_G(a)` on the chamber):
`σ_{A_G\G}(x) ≤ C σ_{A_G\G}(h x)` for `h ∈ H` and `x ∈ G` whose `V₀`-component
`P̄(x)_V = (multiTorus hb hf 0 t)⁻¹` lies in the expanding chamber (no condition on the
`W`-component). Here `σ_{A_G\G}(g) = inf_{a ∈ A_G} σ_G(a g)` (`GGPData.logNormModAG`).
If `V₀` is a hyperbolic plane then `A_G` maps onto `SO(W) × SO(V₀)` and both sides are
constant; otherwise `P̄(A_G)` acts trivially on `V₀` and the chamber condition is preserved. -/
theorem logNormModAG_le_of_chamber (hr : d.r = 0)
    (hb0 : ∀ i : Fin n, (i : ℕ) = 0 → (b i).1 = 0) :
    ∃ C, 0 ≤ C ∧ ∀ h ∈ d.H, ∀ x : d.G, ∀ t : List Fˣ, InChamber n l 0 t →
      ((d.Pbar x).2 : d.V ≃ₗ[F] d.V) = (multiTorus hb hf 0 t)⁻¹ →
      infLeft (logNorm F d.G) d.AG x ≤ C * infLeft (logNorm F d.G) d.AG (h * x) := by
  obtain ⟨C₀, hC₀, hI⟩ := d.logNormSO_add_le_of_chamber hb hf hr hb0
  obtain ⟨c, C, hc, hC, he⟩ := d.logNormModAG_equiv
  set C₁ := max 1 C₀
  have hC₁ : 1 ≤ C₁ := le_max_left _ _
  refine ⟨C * C₁ * c, by positivity, fun h hh x t ht hx => ?_⟩
  have hτ : ∀ g, 0 ≤ d.logNormSO g := fun g => zero_le_one.trans (d.one_le_logNormSO g)
  -- the comparison on `Ā_G\Ḡ`
  have hSO : infLeft d.logNormSO d.AGbar (d.Pbar x) ≤
      C₁ * infLeft d.logNormSO d.AGbar (d.Pbar h * d.Pbar x) := by
    refine le_mul_infLeft _ (zero_le_one.trans hC₁) fun z hz => ?_
    by_cases hV : IsHypPlane d.QV
    · -- `V₀` a hyperbolic plane: `dim W = 1`, `SO(W) = 1`, `A_G ⊇ 1 × GSpin(V₀)`
      have hm : Module.finrank F (Fin d.m → F) ≤ 1 := by
        have h2 := hV.1
        have : Module.finrank F d.V = d.m + (2 * d.r + 1) := by simp
        rw [Module.finrank_fin_fun]; omega
      have hx1 : ((d.Pbar x).1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) = 1 := by
        have := eq_id_of_det_eq_one_of_finrank_le_one hm (d.Pbar x).1.2.2
        exact LinearEquiv.ext fun w => congr($this w)
      have hmem : (d.Pbar x)⁻¹ ∈ d.AGbar := by
        refine ⟨d.pair (1, (d.snd x)⁻¹), ⟨(1, (d.snd x)⁻¹),
          ⟨one_mem _, by unfold splitCentralGSpin; simp only [hV, ↓reduceIte]; trivial⟩, rfl⟩, ?_⟩
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · show specP d.QW 1 = (((d.Pbar x)⁻¹).1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))
          rw [map_one, Prod.fst_inv, Subgroup.coe_inv, hx1, inv_one]
        · show specP d.QV (d.snd x)⁻¹ = (((d.Pbar x)⁻¹).2 : d.V ≃ₗ[F] d.V)
          rw [map_inv]; rfl
      have h1 : infLeft d.logNormSO d.AGbar (d.Pbar x) ≤ 1 := by
        have := infLeft_le_of_nonneg d.AGbar hτ hmem (d.Pbar x)
        rwa [inv_mul_cancel, logNormSO_one] at this
      exact h1.trans (one_le_mul_of_one_le_of_one_le hC₁ (d.one_le_logNormSO _))
    · -- otherwise `P̄(A_G)` is trivial on `V₀` and central
      obtain ⟨a, ha, rfl⟩ := hz
      have hz2 : ((d.Pbar a).2 : d.V ≃ₗ[F] d.V) = 1 := by
        obtain ⟨p, hp, rfl⟩ := ha
        have hp2 := hp.2
        unfold splitCentralGSpin at hp2
        simp only [hV, ↓reduceIte] at hp2
        obtain ⟨c, hc⟩ := hp2
        show specP d.QV p.2 = 1
        rw [← hc, specP_scalarGSpin_eq_one]
      have hcen : ∀ g : d.GbarGrp, d.Pbar a * g = g * d.Pbar a := by
        intro g
        obtain ⟨g', rfl⟩ := d.Pbar_surjective g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (d.AG_le_center ha) g']
      obtain ⟨y, hyd⟩ : ∃ y, y = d.Pbar a * d.Pbar x := ⟨_, rfl⟩
      have hy : (y.2 : d.V ≃ₗ[F] d.V) = (multiTorus hb hf 0 t)⁻¹ := by
        rw [hyd, Prod.snd_mul, Subgroup.coe_mul, hz2, one_mul, hx]
      have key := hI h hh y t ht hy
      have e : d.Pbar a * (d.Pbar h * d.Pbar x) = d.Pbar h * y := by
        rw [hyd, ← mul_assoc, hcen, mul_assoc]
      rw [e]
      calc infLeft d.logNormSO d.AGbar (d.Pbar x) ≤ d.logNormSO y := by
            rw [hyd]; exact infLeft_le_of_nonneg d.AGbar hτ ⟨a, ha, rfl⟩ _
        _ ≤ C₀ * d.logNormSO (d.Pbar h * y) := by linarith [hτ (d.Pbar h)]
        _ ≤ C₁ * d.logNormSO (d.Pbar h * y) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (hτ _)
  have e1 := (he x).2
  have e2 := (he (h * x)).1
  rw [map_mul] at e2
  calc infLeft (logNorm F d.G) d.AG x ≤ C * infLeft d.logNormSO d.AGbar (d.Pbar x) := e1
    _ ≤ C * (C₁ * infLeft d.logNormSO d.AGbar (d.Pbar h * d.Pbar x)) :=
        mul_le_mul_of_nonneg_left hSO hC
    _ ≤ C * (C₁ * (c * infLeft (logNorm F d.G) d.AG (h * x))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e2 (zero_le_one.trans hC₁)) hC
    _ = C * C₁ * c * infLeft (logNorm F d.G) d.AG (h * x) := by ring

include hb in
/-- **Thesis Prop. 8.1.1(iii), second inequality, for `G₀`, modulo the scalars** (BP (6.4.2)):
`σ_{Z\G}(h) ≤ C σ_{Z\G}(x⁻¹ h x)` for `h ∈ H` and `x ∈ G` with `P̄(x)` in the expanding chamber
`A₀⁺`: `P̄(x)_W ⊕ 1 = (multiTorus hb hf 1 s)⁻¹`, `P̄(x)_V = (multiTorus hb hf 0 t)⁻¹`, `s`, `t`
in the contracting chambers. -/
theorem logNormModScalars_le_conj (hr : d.r = 0)
    (hb0 : ∀ i : Fin n, (i : ℕ) = 0 → (b i).1 = 0) :
    ∃ C, 0 ≤ C ∧ ∀ h ∈ d.H, ∀ x : d.G, ∀ s t : List Fˣ, InChamber n l 1 s → InChamber n l 0 t →
      d.extZ ((d.Pbar x).1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) = (multiTorus hb hf 1 s)⁻¹ →
      ((d.Pbar x).2 : d.V ≃ₗ[F] d.V) = (multiTorus hb hf 0 t)⁻¹ →
      infLeft (logNorm F d.G) d.scalars h ≤ C * infLeft (logNorm F d.G) d.scalars (x⁻¹ * h * x) := by
  obtain ⟨C₀, hC₀, hII⟩ := d.logNormSO_le_conj_of_chamber hb hf hr hb0
  obtain ⟨c, C, hc, hC, he⟩ := d.logNormModScalars_equiv
  refine ⟨C * C₀ * c, by positivity, fun h hh x s t hs ht hxW hxV => ?_⟩
  have key := hII h hh (d.Pbar x) s t hs ht hxW hxV
  rw [← map_inv, ← map_mul, ← map_mul] at key
  calc infLeft (logNorm F d.G) d.scalars h ≤ C * d.logNormSO (d.Pbar h) := (he h).2
    _ ≤ C * (C₀ * d.logNormSO (d.Pbar (x⁻¹ * h * x))) := mul_le_mul_of_nonneg_left key hC
    _ ≤ C * (C₀ * (c * infLeft (logNorm F d.G) d.scalars (x⁻¹ * h * x))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (he _).1 hC₀) hC
    _ = C * C₀ * c * infLeft (logNorm F d.G) d.scalars (x⁻¹ * h * x) := by ring

end GGPData

end GSpinGGP
