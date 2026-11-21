/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.Determinant
import GSpinGGP.Foundations.LocalGroups

/-!
# Trailing coefficients of characteristic polynomials along a degenerating family

The linear algebra behind `D^G(x e^{cX}) = D^G(x) |c|^{δ} D^{G_x}(X)` for small `c ≠ 0`
(BP Astérisque 418, §3.3; Harish-Chandra).

* `charpoly_eq_mul_of_isCompl`: `charpoly M = charpoly(M|_P) charpoly(M|_R)` for `E = P ⊕ R`,
  both `M`-stable;
* `trailingCoeff_charpoly_of_det_ne_zero`: `trailing(charpoly f) = (−1)^{dim} det f` if
  `det f ≠ 0`;
* `tendsto_det_comp_comp_subtype`: determinants of compressions converge when the family converges
  pointwise (read through an injective linear map into a space with its module topology);
* `eventually_absF_eq_of_tendsto`: `|·|_F` is locally constant away from `0` (ultrametric `F`);
* `eventually_absF_trailingCoeff_charpoly`: let `S`, `D` be commuting semisimple endomorphisms
  of `E` and `N_c` (`c ∈ F`) endomorphisms commuting with `S` and `D`, vanishing on
  `ker S ∩ ker D`, with `N_c → S` and `c⁻¹ N_c → −D` on `ker S` as `c → 0`. Then for small
  `c ≠ 0`,
  `|trail charpoly N_c| = |trail charpoly S| · |c|^{dim ker S − dim ker D'} ·
  |trail charpoly D'|`, where `D' = D|_{ker S}`.
-/

noncomputable section

open Filter Topology Polynomial

set_option linter.unusedSectionVars false

namespace GSpinGGP

section Algebra

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- **Characteristic polynomial of a block-diagonal endomorphism**: for `E = P ⊕ R` with both
summands `M`-stable, `charpoly M = charpoly(M|_P) charpoly(M|_R)`. -/
theorem charpoly_eq_mul_of_isCompl {M : Module.End K E} {P R : Submodule K E} (h : IsCompl P R)
    (hP : ∀ v ∈ P, M v ∈ P) (hR : ∀ v ∈ R, M v ∈ R) :
    M.charpoly = (M.restrict hP).charpoly * (M.restrict hR).charpoly := by
  obtain ⟨e, he⟩ : ∃ e : (P × R) ≃ₗ[K] E, ∀ q : P × R, e q = (q.1 : E) + (q.2 : E) :=
    ⟨Submodule.prodEquivOfIsCompl P R h, Submodule.coe_prodEquivOfIsCompl' P R h⟩
  have hφ : e.symm.conj M = (M.restrict hP).prodMap (M.restrict hR) := by
    refine LinearMap.ext fun q => e.injective ?_
    change e (e.symm (M (e q))) = _
    rw [LinearEquiv.apply_symm_apply, he, he, map_add]
    simp [LinearMap.coe_restrict_apply]
  rw [← LinearEquiv.charpoly_conj e.symm M, hφ, LinearMap.charpoly_prodMap]

/-- If `det f ≠ 0`, the trailing coefficient of `charpoly f` is `(−1)^{dim} det f`. -/
theorem trailingCoeff_charpoly_of_det_ne_zero {f : Module.End K E} (h : LinearMap.det f ≠ 0) :
    f.charpoly.trailingCoeff = (-1) ^ Module.finrank K E * LinearMap.det f := by
  have hc0 : f.charpoly.coeff 0 ≠ 0 := by
    intro h0
    have := LinearMap.det_eq_sign_charpoly_coeff f
    rw [h0, mul_zero] at this
    exact h this
  rw [Polynomial.trailingCoeff_eq_coeff_zero hc0, LinearMap.det_eq_sign_charpoly_coeff, ← mul_assoc,
    ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- The trailing coefficient of the characteristic polynomial of `0` is `1`. -/
theorem trailingCoeff_charpoly_zero :
    (0 : Module.End K E).charpoly.trailingCoeff = 1 := by
  rw [LinearMap.charpoly_zero, Polynomial.trailingCoeff, Polynomial.natTrailingDegree_X_pow,
    Polynomial.coeff_X_pow_self]

end Algebra

section Limits

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **`|·|_F` is locally constant away from `0`**: if `f → a ≠ 0`, then eventually
`|f|_F = |a|_F`. -/
theorem eventually_absF_eq_of_tendsto {α : Type*} {l : Filter α} {f : α → F} {a : F}
    (hf : Tendsto f l (𝓝 a)) (ha : a ≠ 0) : ∀ᶠ c in l, absF (f c) = absF a := by
  have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  filter_upwards [hf (Metric.ball_mem_nhds a hpos)] with c hc
  rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hc
  refine absF_eq_of_norm_eq ha ?_
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hc)
  rwa [add_sub_cancel, max_eq_left hc.le] at this

/-- `|a^n|_F = |a|_F^n`. -/
theorem absF_pow' (a : F) (n : ℕ) : absF (a ^ n) = absF a ^ n := by
  induction n with
  | zero => simp [absF_one]
  | succ n ih => rw [pow_succ, absF_mul, ih, pow_succ]

/-- `|(−1)^n z|_F = |z|_F`. -/
theorem absF_neg_one_pow_mul (n : ℕ) (z : F) : absF ((-1) ^ n * z) = absF z := by
  rw [absF_mul, absF_eq_one_of_norm_eq_one (by simp), one_mul]

variable {E A : Type*} [AddCommGroup E] [Module F E] [FiniteDimensional F E]
  [AddCommGroup A] [Module F A] [TopologicalSpace A] [IsModuleTopology F A]

/-- **Determinants of compressions converge** when the family converges pointwise, read through an
injective linear map `ι` into a space with its module topology. -/
theorem tendsto_det_comp_comp_subtype (ι : E →ₗ[F] A) (hι : Function.Injective ι)
    (P : Submodule F E) (π : E →ₗ[F] P) {α : Type*} {l : Filter α} (M : α → Module.End F E)
    (M₀ : Module.End F E) (h : ∀ v ∈ P, Tendsto (fun a => ι (M a v)) l (𝓝 (ι (M₀ v)))) :
    Tendsto (fun a => LinearMap.det (π ∘ₗ M a ∘ₗ P.subtype)) l
      (𝓝 (LinearMap.det (π ∘ₗ M₀ ∘ₗ P.subtype))) := by
  classical
  let b := Module.Free.chooseBasis F P
  obtain ⟨ψ', hψ'⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.mpr hι)
  simp_rw [← LinearMap.det_toMatrix b]
  refine ((continuous_id.matrix_det).tendsto _).comp ?_
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  simp only [LinearMap.toMatrix_apply, LinearMap.comp_apply, Submodule.subtype_apply]
  have hL : ∀ v : E, b.repr (π v) i = (b.coord i ∘ₗ π ∘ₗ ψ') (ι v) := fun v => by
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply]
    rw [← LinearMap.comp_apply ψ' ι, hψ', LinearMap.id_apply]
  simp_rw [hL]
  exact ((IsModuleTopology.continuous_of_linearMap _).tendsto _).comp (h _ (b j).property)

end Limits

section Main

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
variable {E A : Type*} [AddCommGroup E] [Module F E] [FiniteDimensional F E]
  [AddCommGroup A] [Module F A] [TopologicalSpace A] [IsModuleTopology F A]

/-- **Trailing coefficients along a degenerating family.** Let `S`, `D` be commuting semisimple
endomorphisms of `E`, and `N_c` (`c ∈ F`) endomorphisms which for small `c ≠ 0` commute with `S`
and `D` and vanish on `ker S ∩ ker D`, such that `N_c → S` and, on `ker S`, `c⁻¹ N_c → −D`
(pointwise, read through an injective linear map `ι` into a space with its module topology).
Then for small `c ≠ 0`,
`|trail charpoly N_c|_F = |trail charpoly S|_F · |c|_F^{dim ker S − dim ker D'} ·
|trail charpoly D'|_F`, where `D' = D|_{ker S}`.

Proof. `E = ker S ⊕ Im S` and `ker S = ker D' ⊕ Im D'` (semisimplicity), all stable under `N_c`.
On `Im S`, `det N_c → det S ≠ 0`; on `C = Im D'`, `det(c⁻¹ N_c) → det(−D') ≠ 0`; on `ker D'`,
`N_c = 0`. The absolute values of the limits are attained for small `c`
(`eventually_absF_eq_of_tendsto`). -/
theorem eventually_absF_trailingCoeff_charpoly (ι : E →ₗ[F] A) (hι : Function.Injective ι)
    {S D : Module.End F E} (hS : S.IsSemisimple) (hD : D.IsSemisimple)
    (N : F → Module.End F E)
    (hNS : ∀ᶠ c in 𝓝[≠] (0 : F), Commute (N c) S)
    (hND : ∀ᶠ c in 𝓝[≠] (0 : F), Commute (N c) D)
    (hK : ∀ᶠ c in 𝓝[≠] (0 : F), ∀ v, S v = 0 → D v = 0 → N c v = 0)
    (hlim : ∀ v, Tendsto (fun c => ι (N c v)) (𝓝[≠] 0) (𝓝 (ι (S v))))
    (hder : ∀ v, S v = 0 →
      Tendsto (fun c => ι (c⁻¹ • N c v)) (𝓝[≠] 0) (𝓝 (ι (-D v))))
    (hDK : ∀ v ∈ LinearMap.ker S, D v ∈ LinearMap.ker S) :
    ∀ᶠ c in 𝓝[≠] (0 : F), absF (N c).charpoly.trailingCoeff =
      absF S.charpoly.trailingCoeff *
        absF c ^ (Module.finrank F ↥(LinearMap.ker S) -
          Module.finrank F ↥(LinearMap.ker (D.restrict hDK))) *
        absF (D.restrict hDK).charpoly.trailingCoeff := by
  classical
  -- stability of kernels and ranges under commuting endomorphisms
  have stabK : ∀ {M T : Module.End F E}, Commute M T →
      ∀ v ∈ LinearMap.ker T, M v ∈ LinearMap.ker T := fun {M T} h v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← mul_apply_eq_comp, ← h.eq, mul_apply_eq_comp, hv, map_zero]
  have stabR : ∀ {M T : Module.End F E}, Commute M T →
      ∀ v ∈ LinearMap.range T, M v ∈ LinearMap.range T := fun {M T} h v hv => by
    obtain ⟨w, rfl⟩ := hv
    exact ⟨M w, by rw [← mul_apply_eq_comp, ← h.eq, mul_apply_eq_comp]⟩
  -- `E = ker S ⊕ Im S`
  set K₁ := LinearMap.ker S with hK₁
  set Q := LinearMap.range S with hQ
  have h1 : IsCompl K₁ Q := isCompl_ker_range_of_isSemisimple hS
  have hSQ : ∀ v ∈ Q, S v ∈ Q := fun v _ => LinearMap.mem_range_self S v
  obtain ⟨hdetSQ, htrS⟩ := trailingCoeff_charpoly_of_isCompl h1 rfl hSQ
  -- `ker S = ker D' ⊕ Im D'`
  set D₁ := D.restrict hDK with hD₁def
  have hD₁ : Module.End.IsSemisimple D₁ := hD.restrict ((Module.End.mem_invtSubmodule _).mpr hDK)
  set K₂ := LinearMap.ker D₁ with hK₂
  set C₁ := LinearMap.range D₁ with hC₁
  have h2 : IsCompl K₂ C₁ := isCompl_ker_range_of_isSemisimple hD₁
  have hD₁C : ∀ w ∈ C₁, D₁ w ∈ C₁ := fun w _ => LinearMap.mem_range_self _ _
  obtain ⟨hdetD₁, htrD⟩ := trailingCoeff_charpoly_of_isCompl h2 rfl hD₁C
  set C := C₁.map K₁.subtype with hC
  have hDC : ∀ v ∈ C, D v ∈ C := fun v hv => by
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨D₁ w, hD₁C w hw, rfl⟩
  have hdetDC : LinearMap.det (D.restrict hDC) = LinearMap.det (D₁.restrict hD₁C) :=
    (det_restrict_restrict hDK hD₁C hDC).symm
  have hCK : ∀ v ∈ C, S v = 0 := fun v hv => by
    obtain ⟨w, -, rfl⟩ := hv
    exact w.property
  -- projections onto `Q` and `C`
  obtain ⟨πQ, hπQ⟩ := LinearMap.exists_leftInverse_of_injective Q.subtype Q.ker_subtype
  obtain ⟨πC, hπC⟩ := LinearMap.exists_leftInverse_of_injective C.subtype C.ker_subtype
  have hπQ' : ∀ w : Q, πQ w = w := fun w => LinearMap.congr_fun hπQ w
  have hπC' : ∀ w : C, πC w = w := fun w => LinearMap.congr_fun hπC w
  -- the limits of the determinants
  have hdetQ : Tendsto (fun c => LinearMap.det (πQ ∘ₗ N c ∘ₗ Q.subtype)) (𝓝[≠] 0)
      (𝓝 (LinearMap.det (S.restrict hSQ))) := by
    rw [← comp_comp_subtype_eq_restrict hπQ' hSQ]
    exact tendsto_det_comp_comp_subtype ι hι Q πQ N S fun v _ => hlim v
  have hdetC : Tendsto (fun c => LinearMap.det (πC ∘ₗ (c⁻¹ • N c) ∘ₗ C.subtype)) (𝓝[≠] 0)
      (𝓝 (LinearMap.det ((-D).restrict (fun v hv => by
        simpa using C.neg_mem (hDC v hv))))) := by
    rw [← comp_comp_subtype_eq_restrict hπC' (M := -D)]
    exact tendsto_det_comp_comp_subtype ι hι C πC (fun c => c⁻¹ • N c) (-D)
      fun v hv => by simpa using hder v (hCK v hv)
  have hnegD : LinearMap.det ((-D).restrict (fun v hv => by
        simpa using C.neg_mem (hDC v hv)) : Module.End F C) =
      (-1) ^ Module.finrank F C * LinearMap.det (D.restrict hDC) := by
    rw [show ((-D).restrict (fun v hv => by simpa using C.neg_mem (hDC v hv)) :
        Module.End F C) = (-1 : F) • D.restrict hDC from LinearMap.ext fun v => by
      ext; simp [LinearMap.coe_restrict_apply], LinearMap.det_smul]
  have hDC0 : LinearMap.det (D.restrict hDC) ≠ 0 := hdetDC ▸ hdetD₁
  have hnegD0 : (-1) ^ Module.finrank F C * LinearMap.det (D.restrict hDC) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) hDC0
  -- dimensions
  have hdimC : Module.finrank F C = Module.finrank F K₁ - Module.finrank F K₂ := by
    have e1 : Module.finrank F C = Module.finrank F C₁ :=
      (Submodule.equivMapOfInjective _ K₁.injective_subtype C₁).finrank_eq.symm
    have e2 := LinearMap.finrank_range_add_finrank_ker D₁
    have e3 : Module.finrank F ↥(LinearMap.range D₁) = Module.finrank F C₁ := rfl
    have e4 : Module.finrank F ↥(LinearMap.ker D₁) = Module.finrank F K₂ := rfl
    omega
  filter_upwards [hNS, hND, hK, eventually_absF_eq_of_tendsto hdetQ hdetSQ,
    eventually_absF_eq_of_tendsto hdetC (hnegD ▸ hnegD0), self_mem_nhdsWithin]
    with c hcS hcD hcK hcQ hcC hc0
  have hc0' : c ≠ 0 := hc0
  have hNK : ∀ v ∈ K₁, N c v ∈ K₁ := stabK hcS
  have hNQ : ∀ v ∈ Q, N c v ∈ Q := stabR hcS
  have hNC : ∀ v ∈ C, N c v ∈ C := fun v hv => by
    obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨u, rfl⟩ := hw
    refine ⟨D₁ ((N c).restrict hNK u), LinearMap.mem_range_self _ _, ?_⟩
    simp only [Submodule.subtype_apply, D₁, LinearMap.coe_restrict_apply]
    rw [← mul_apply_eq_comp, ← hcD.eq, mul_apply_eq_comp]
  -- the restriction to `ker S`
  set NK := (N c).restrict hNK with hNKdef
  have hNKC : ∀ w ∈ C₁, NK w ∈ C₁ := fun w hw => by
    obtain ⟨u, rfl⟩ := hw
    refine ⟨NK u, Subtype.ext ?_⟩
    simp only [NK, D₁, LinearMap.coe_restrict_apply]
    rw [← mul_apply_eq_comp, ← hcD.eq, mul_apply_eq_comp]
  have hNKK : ∀ w ∈ K₂, NK w ∈ K₂ := fun w hw => by
    have : NK w = 0 :=
      Subtype.ext (hcK w w.property (congrArg Subtype.val (LinearMap.mem_ker.mp hw)))
    rw [this]; exact K₂.zero_mem
  have hNK0 : NK.restrict hNKK = 0 := LinearMap.ext fun w => Subtype.ext (Subtype.ext
    (hcK _ (w : K₁).property (congrArg Subtype.val (LinearMap.mem_ker.mp w.property))))
  -- determinants on `C` and `Q`
  have hdetNC : LinearMap.det (NK.restrict hNKC) = LinearMap.det ((N c).restrict hNC) :=
    det_restrict_restrict hNK hNKC hNC
  have hsmulC : πC ∘ₗ (c⁻¹ • N c) ∘ₗ C.subtype = c⁻¹ • (N c).restrict hNC := by
    rw [← comp_comp_subtype_eq_restrict hπC' hNC]
    ext v; simp
  have habsC : absF (LinearMap.det ((N c).restrict hNC)) =
      absF c ^ Module.finrank F C * absF (LinearMap.det (D.restrict hDC)) := by
    have := hcC
    rw [hsmulC, LinearMap.det_smul, hnegD, absF_mul, absF_neg_one_pow_mul, absF_pow', absF_inv]
      at this
    have hcpos : 0 < absF c ^ Module.finrank F C := pow_pos (absF_pos hc0') _
    rw [inv_pow] at this
    rw [← this, ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
  have hdetNC0 : LinearMap.det ((N c).restrict hNC) ≠ 0 := by
    intro h0
    rw [h0, absF_zero] at habsC
    exact (mul_pos (pow_pos (absF_pos hc0') _) (absF_pos hDC0)).ne' habsC.symm
  have hdetNQ : LinearMap.det (πQ ∘ₗ N c ∘ₗ Q.subtype) = LinearMap.det ((N c).restrict hNQ) := by
    rw [comp_comp_subtype_eq_restrict hπQ' hNQ]
  have hdetNQ0 : LinearMap.det ((N c).restrict hNQ) ≠ 0 := by
    intro h0
    rw [hdetNQ, h0, absF_zero] at hcQ
    exact (absF_pos hdetSQ).ne' hcQ.symm
  -- assemble
  rw [charpoly_eq_mul_of_isCompl h1 hNK hNQ, Polynomial.trailingCoeff_mul,
    charpoly_eq_mul_of_isCompl h2 hNKK hNKC, Polynomial.trailingCoeff_mul, hNK0,
    trailingCoeff_charpoly_zero, one_mul,
    trailingCoeff_charpoly_of_det_ne_zero (hdetNC ▸ hdetNC0),
    trailingCoeff_charpoly_of_det_ne_zero hdetNQ0, htrS, htrD, absF_mul, absF_neg_one_pow_mul,
    absF_neg_one_pow_mul, absF_neg_one_pow_mul, absF_neg_one_pow_mul, hdetNC, habsC,
    ← hdetNQ, hcQ, ← hdetDC, ← hdimC]
  ring

end Main

end GSpinGGP
