/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.ExpHaar
import GSpinGGP.Foundations.Determinant
import GSpinGGP.Foundations.TorusIntegrability

/-!
# Determinants of `A e^Y − 1` near `Y = 0`

For a semisimple endomorphism `A` of a finite-dimensional vector space over a `p`-adic field and
`Y` commuting with `A`, `|det(A e^Y − 1)|_F` is comparable near `Y = 0` to
`|det(Y|_{ker(A − 1)})|_F` (`exists_absF_det_mul_expA_sub_one`). This is the step reducing
BP Astérisque 418, Lemma B.1.2(i) to B.1.2(ii) near a point `t₀` of a torus (the eigencharacters
`λ` with `λ(t₀) = 1` contribute `|dλ(X)|`, the others a unit); BP states B.1.2 without proof.
The linear algebra used is in `Foundations/Determinant.lean`.
-/

noncomputable section

open MeasureTheory Topology Filter

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- **`|det(A e^Y − 1)| ≍ |det(Y|_{ker(A−1)})|` near `Y = 0`** for a semisimple `A` and `Y`
commuting with `A` (`p`-adic `F`). With `K = ker(A − 1)` and `R = im(A − 1)`, `V = K ⊕ R`,
both stable under `Y`; on `K`, `A e^Y − 1 = e^Y − 1 = Y u(Y)` with `u(Y) → 1`
(`exists_expA_sub_one_eq_mul`), and on `R`, `A e^Y − 1 → A − 1`, invertible there. -/
theorem exists_absF_det_mul_expA_sub_one [TopologicalSpace (Module.End F V)]
    [IsModuleTopology F (Module.End F V)] {A : Module.End F V} (hA : A.IsSemisimple) :
    ∃ c C C' : ℝ, 0 < c ∧ ∀ᶠ Y in 𝓝 (0 : Module.End F V), Commute A Y →
      ∀ hY : (∀ v ∈ LinearMap.ker (A - 1), Y v ∈ LinearMap.ker (A - 1)),
        c * absF (LinearMap.det (Y.restrict hY)) ≤ absF (LinearMap.det (A * expA F Y - 1)) ∧
        absF (LinearMap.det (A * expA F Y - 1)) ≤ C * absF (LinearMap.det (Y.restrict hY)) ∧
        absF (LinearMap.det (A * expA F Y - 1)) ≤ C' := by
  classical
  letI := isTopologicalRing_of_moduleTopology F (Module.End F V)
  set K := LinearMap.ker (A - 1) with hKdef
  set R := LinearMap.range (A - 1) with hRdef
  have hss : (A - 1).IsSemisimple :=
    Module.End.IsSemisimple.sub_of_commute (Commute.one_right _) hA Module.End.isSemisimple_id
  have hcompl : IsCompl K R := isCompl_ker_range_of_isSemisimple hss
  set πK := Submodule.projectionOnto K R hcompl
  set πR := Submodule.projectionOnto R K hcompl.symm
  have hπK : ∀ w : K, πK w = w := fun w => Submodule.projectionOnto_apply_left hcompl w
  have hπR : ∀ w : R, πR w = w := fun w => Submodule.projectionOnto_apply_left hcompl.symm w
  set g₁ := fun M : Module.End F V => LinearMap.det (πK ∘ₗ M ∘ₗ K.subtype)
  set g₂ := fun M : Module.End F V => LinearMap.det (πR ∘ₗ M ∘ₗ R.subtype)
  have hg₁ : Continuous g₁ := continuous_det_comp_comp_subtype K πK
  have hg₂ : Continuous g₂ := continuous_det_comp_comp_subtype R πR
  -- stability under endomorphisms commuting with `A`
  have hstK : ∀ M : Module.End F V, Commute A M → ∀ v ∈ K, M v ∈ K :=
    fun M hM => mapsTo_ker_sub_one_of_commute hM
  have hstR : ∀ M : Module.End F V, Commute A M → ∀ v ∈ R, M v ∈ R :=
    fun M hM => mapsTo_range_sub_one_of_commute hM
  -- the two factors near `0`
  obtain ⟨u, hu0c, hu0, hev⟩ := exists_expA_sub_one_eq_mul F (A := Module.End F V)
  have hg₁1 : g₁ 1 = 1 := by
    show LinearMap.det (πK ∘ₗ (1 : Module.End F V) ∘ₗ K.subtype) = 1
    rw [comp_comp_subtype_eq_restrict hπK (M := 1) (fun v hv => hv)]
    have : (1 : Module.End F V).restrict (p := K) (q := K) (fun v hv => hv) = 1 := by
      ext w; rfl
    rw [this, map_one]
  have hT1 : Tendsto (fun Y => absF (g₁ (u Y))) (𝓝 0) (𝓝 1) := by
    have ht : Tendsto (fun Y => g₁ (u Y)) (𝓝 0) (𝓝 1) := by
      have := (hg₁.tendsto (u 0)).comp hu0c.tendsto
      rwa [hu0, hg₁1] at this
    have := (continuousAt_absF (F := F) one_ne_zero).tendsto.comp ht
    rwa [absF_one] at this
  obtain ⟨Ue, hUe, hUeo, hUec⟩ := exists_nhds_continuousOn_expA F (A := Module.End F V)
  have hec : ContinuousAt (expA F : Module.End F V → Module.End F V) 0 :=
    hUec.continuousAt hUe
  set d₂ := g₂ (A - 1)
  have hd₂ : d₂ ≠ 0 := by
    show LinearMap.det (πR ∘ₗ (A - 1) ∘ₗ R.subtype) ≠ 0
    rw [comp_comp_subtype_eq_restrict hπR (hstR _ (Commute.sub_right (Commute.refl A) (Commute.one_right A)))]
    rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    have hw' : (A - 1) (w : V) = 0 := congrArg Subtype.val hw
    have : (w : V) ∈ K ⊓ R := ⟨LinearMap.mem_ker.mpr hw', w.2⟩
    rw [hcompl.disjoint.eq_bot, Submodule.mem_bot] at this
    exact (Submodule.mem_bot F).mpr (Subtype.ext this)
  set m := absF d₂
  have hm : 0 < m := absF_pos hd₂
  have hT2 : Tendsto (fun Y => absF (g₂ (A * expA F Y - 1))) (𝓝 0) (𝓝 m) := by
    have hM : ContinuousAt (fun Y : Module.End F V => A * expA F Y - 1) 0 :=
      (continuousAt_const.mul hec).sub continuousAt_const
    have e : A * expA F (0 : Module.End F V) - 1 = A - 1 := by rw [expA_zero_eq_one, mul_one]
    have ht : Tendsto (fun Y => g₂ (A * expA F Y - 1)) (𝓝 0) (𝓝 d₂) := by
      have := (hg₂.tendsto _).comp hM.tendsto
      rwa [e] at this
    exact (continuousAt_absF (F := F) hd₂).tendsto.comp ht
  have hT0 : Tendsto (fun Y => absF (g₁ Y)) (𝓝 0) (𝓝 (absF (g₁ 0))) :=
    (continuous_absF.comp hg₁).tendsto 0
  have hb0 := hT0.eventually (gt_mem_nhds (lt_add_one (absF (g₁ 0))))
  refine ⟨1 / 2 * (m / 2), 2 * (2 * m), (absF (g₁ 0) + 1) * 2 * (2 * m), by positivity, ?_⟩
  have hb1 := hT1.eventually (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2))
  have hb2 := hT2.eventually (Ioo_mem_nhds (by linarith : m / 2 < m) (by linarith : m < 2 * m))
  filter_upwards [hev, hb1, hb2, hb0] with Y ⟨hYe, hYc⟩ ⟨h1l, h1u⟩ ⟨h2l, h2u⟩ h0 hAY hY
  have hAu : Commute A (u Y) := hYc A hAY
  have hexp : expA F Y = 1 + Y * u Y := by rw [← hYe]; abel
  have hAe : Commute A (expA F Y) := by
    rw [hexp]; exact (Commute.one_right A).add_right (hAY.mul_right hAu)
  set M := A * expA F Y - 1 with hMdef
  have hAM : Commute A M := (Commute.refl A |>.mul_right hAe).sub_right (Commute.one_right A)
  have hMK := hstK M hAM
  have hMR := hstR M hAM
  have huK := hstK (u Y) hAu
  have hdet := det_eq_det_restrict_mul_det_restrict hcompl hMK hMR
  have hMKeq : M.restrict hMK = Y.restrict hY * (u Y).restrict huK := by
    ext w
    have hw : A (w : V) = w := by
      have h0 : (A - 1) (w : V) = 0 := LinearMap.mem_ker.mp w.2
      rwa [LinearMap.sub_apply, one_apply_eq_self, sub_eq_zero] at h0
    simp only [LinearMap.coe_restrict_apply, mul_apply_eq_comp, hMdef, LinearMap.sub_apply,
      one_apply_eq_self]
    rw [← mul_apply_eq_comp A (expA F Y), hAe.eq, mul_apply_eq_comp, hw, hexp]
    simp [mul_apply_eq_comp]
  have hK1 : LinearMap.det ((u Y).restrict huK) = g₁ (u Y) :=
    (congrArg LinearMap.det (comp_comp_subtype_eq_restrict hπK huK)).symm
  have hR2 : LinearMap.det (M.restrict hMR) = g₂ M :=
    (congrArg LinearMap.det (comp_comp_subtype_eq_restrict hπR hMR)).symm
  have hval : absF (LinearMap.det M) =
      absF (LinearMap.det (Y.restrict hY)) * absF (g₁ (u Y)) * absF (g₂ M) := by
    rw [hdet, hMKeq, map_mul, hK1, hR2, absF_mul, absF_mul]
  have hn := absF_nonneg (LinearMap.det (Y.restrict hY))
  have hY0 : LinearMap.det (Y.restrict hY) = g₁ Y :=
    (congrArg LinearMap.det (comp_comp_subtype_eq_restrict hπK hY)).symm
  rw [hval]
  refine ⟨?_, ?_, ?_⟩
  · calc 1 / 2 * (m / 2) * absF (LinearMap.det (Y.restrict hY))
        = absF (LinearMap.det (Y.restrict hY)) * (1 / 2) * (m / 2) := by ring
      _ ≤ _ := by gcongr
  · calc _ ≤ absF (LinearMap.det (Y.restrict hY)) * 2 * (2 * m) := by
          gcongr <;> first | exact absF_nonneg _ | linarith
      _ = _ := by ring
  · rw [hY0] at hn ⊢
    calc _ ≤ (absF (g₁ 0) + 1) * 2 * (2 * m) := by
          gcongr <;> first | exact absF_nonneg _ | linarith
      _ = _ := by ring

end GSpinGGP
