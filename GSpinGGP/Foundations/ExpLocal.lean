/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalGroups

/-!
# Local properties of the exponential `expA`

* `expA_add_of_commute`: `e^{X+Y} = e^X e^Y` for commuting `X, Y` near `0`;
* `exists_localInverse_exp`: in a complete normed algebra over a nontrivially normed field of
  characteristic `0` in which the exponential series has positive radius (any `p`-adic or real
  Banach algebra), `exp` has a continuous local inverse `L` at `1`, injective domain included;
* `commute_of_commute_exp`: on an injectivity domain of `exp`, `Y` commutes with everything
  commuting with `exp Y` (so the local inverse `L(c)` commutes with the commutant of `c`);
* `eventually_map_expA`: `φ(e^X) = e^{φ X}` near `0` for linear maps preserving powers;
* `exists_logA`: a local logarithm `log`, continuous at `1`, with `e^{log u} = u` near `1`
  (no logarithm series: the local inverse of `exp` on `End(F^d)` restricted to `A`).
-/

noncomputable section

open Topology Filter

namespace GSpinGGP

variable (F : Type*) [NontriviallyNormedField F] [PAdicField F] {A : Type*} [Ring A] [Algebra F A]
  [Module.Finite F A] [TopologicalSpace A] [IsModuleTopology F A]

/-- **`e^{X+Y} = e^X e^Y` for commuting `X, Y` near `0`** (Mathlib's
`exp_add_of_commute_of_mem_ball`, transported along `lmulPi`). -/
lemma expA_add_of_commute :
    ∃ U ∈ 𝓝 (0 : A), ∀ X ∈ U, ∀ Y ∈ U, Commute X Y →
      expA F (X + Y) = expA F X * expA F Y := by
  have := isTopologicalRing_of_moduleTopology F A
  obtain ⟨U, hU, -, h⟩ := expA_aux F (A := A)
  obtain ⟨V, hV, hVU⟩ := exists_nhds_zero_half hU
  refine ⟨V ∩ U, inter_mem hV hU, fun X hX Y hY hXY => ?_⟩
  obtain ⟨hbX, -, heX⟩ := h X hX.2
  obtain ⟨hbY, -, heY⟩ := h Y hY.2
  obtain ⟨-, -, heXY⟩ := h (X + Y) (hVU X hX.1 Y hY.1)
  have hc : Commute (lmulPi F X) (lmulPi F Y) := by
    show lmulPi F X * lmulPi F Y = lmulPi F Y * lmulPi F X
    rw [← lmulPi_mul, ← lmulPi_mul, hXY.eq]
  have hadd := NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := F) hc hbX hbY
  have hl : lmulPi F (X + Y) = lmulPi F X + lmulPi F Y := map_add (lmulPiₗ F) X Y
  have key : lmulPi F (expA F (X + Y)) = lmulPi F (expA F X * expA F Y) := by
    rw [heXY, hl, hadd, lmulPi_mul, heX, heY]
  calc expA F (X + Y) = lmulPiInv F (lmulPi F (expA F (X + Y))) := (lmulPiInv_lmulPi F _).symm
    _ = expA F X * expA F Y := by rw [key, lmulPiInv_lmulPi]

local notation "VA" => (Fin (Module.finrank F A) → F)

section LocalInverse

open NormedSpace

variable {𝕂 E : Type*} [NontriviallyNormedField 𝕂] [CharZero 𝕂] [NormedRing E] [NormedAlgebra 𝕂 E]
  [CompleteSpace E]

/-- **Local inverse of `exp` at `1`** (inverse function theorem): there are open `s ∋ 0` (inside the
ball of convergence) and `t ∋ 1` and `L : E → E`, continuous at `1` with `L 1 = 0`, such that
`L(c) ∈ s` and `exp(L c) = c` for `c ∈ t`, and `exp` is injective on `s`. -/
theorem exists_localInverse_exp (hr : 0 < (expSeries 𝕂 E).radius) :
    ∃ s t : Set E, IsOpen s ∧ (0 : E) ∈ s ∧ s ⊆ Metric.eball (0 : E) (expSeries 𝕂 E).radius ∧
      IsOpen t ∧ (1 : E) ∈ t ∧ Set.InjOn exp s ∧ ∃ L : E → E, ContinuousAt L 1 ∧ L 1 = 0 ∧
        ∀ c ∈ t, L c ∈ s ∧ exp (L c) = c := by
  have h := hasStrictFDerivAt_exp_zero_of_radius_pos hr
  have h' : HasStrictFDerivAt (exp : E → E) ((ContinuousLinearEquiv.refl 𝕂 E : E ≃L[𝕂] E) :
      E →L[𝕂] E) 0 := by
    convert h using 1
    exact ContinuousLinearMap.ext fun x => rfl
  set φ := h'.toOpenPartialHomeomorph exp
  have h0 : (0 : E) ∈ φ.source := h'.mem_toOpenPartialHomeomorph_source
  have h1 : (1 : E) ∈ φ.target := by
    have := h'.image_mem_toOpenPartialHomeomorph_target
    rwa [exp_zero] at this
  have hφ0 : φ.symm 1 = 0 := by
    have := φ.left_inv h0
    rwa [show φ 0 = 1 from exp_zero] at this
  set s := φ.source ∩ Metric.eball (0 : E) (expSeries 𝕂 E).radius
  have hs : IsOpen s := φ.open_source.inter Metric.isOpen_eball
  set t := φ.target ∩ φ.symm ⁻¹' s
  refine ⟨s, t, hs, ⟨h0, Metric.mem_eball_self hr⟩, Set.inter_subset_right,
    φ.isOpen_inter_preimage_symm hs, ⟨h1, by
      show φ.symm 1 ∈ s
      rw [hφ0]
      exact ⟨h0, Metric.mem_eball_self hr⟩⟩, φ.injOn.mono Set.inter_subset_left, φ.symm,
    φ.continuousAt_symm h1, hφ0, fun c hc => ⟨hc.2, φ.right_inv hc.1⟩⟩

/-- **The local inverse of `exp` commutes with the commutant**: if `exp` is injective on the open
set `s` (inside the ball of convergence), `Y ∈ s` and `z` commutes with `exp Y`, then `z` commutes
with `Y`.  Conjugate by `1 + εz` for small `ε ≠ 0`: it fixes `exp Y` and keeps `Y` in `s`. -/
theorem commute_of_commute_exp {s : Set E} (hs : IsOpen s)
    (hsr : s ⊆ Metric.eball (0 : E) (expSeries 𝕂 E).radius) (hinj : Set.InjOn exp s) {Y : E}
    (hY : Y ∈ s) {z : E} (hz : Commute z (exp Y)) : Commute z Y := by
  -- `ε ↦ 1 + εz` is a unit near `0`, and conjugation by it is continuous at `0`
  have hlim : Tendsto (fun ε : 𝕂 => ε • z) (𝓝[≠] 0) (𝓝 0) := by
    have : Continuous fun ε : 𝕂 => ε • z := continuous_id.smul continuous_const
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ ε in 𝓝[≠] (0 : 𝕂), ‖-(ε • z)‖ < 1 := by
    have := hlim.eventually (Metric.ball_mem_nhds (0 : E) one_pos)
    filter_upwards [this] with ε hε
    simpa using hε
  -- the conjugate of `Y` tends to `Y`
  have hconj : Tendsto (fun ε : 𝕂 => (1 + ε • z) * Y * Ring.inverse (1 + ε • z)) (𝓝[≠] 0) (𝓝 Y) := by
    have h1 : Tendsto (fun ε : 𝕂 => 1 + ε • z) (𝓝[≠] 0) (𝓝 1) := by
      simpa using tendsto_const_nhds.add hlim
    have h2 : Tendsto (fun ε : 𝕂 => Ring.inverse (1 + ε • z)) (𝓝[≠] 0) (𝓝 1) := by
      have := (NormedRing.inverse_continuousAt (1 : Eˣ)).tendsto.comp h1
      simpa [Function.comp_def] using this
    simpa using (h1.mul tendsto_const_nhds).mul h2
  obtain ⟨ε, ⟨hε1, hεs⟩, hε0⟩ := ((hsmall.and (hconj.eventually (hs.mem_nhds hY))).and
    self_mem_nhdsWithin).exists
  set g : Eˣ := Units.oneSub (-(ε • z)) hε1 with hg
  have hgv : (g : E) = 1 + ε • z := by simp [hg, Units.oneSub, sub_neg_eq_add]
  have hginv : Ring.inverse (1 + ε • z) = ↑g⁻¹ := by rw [← hgv, Ring.inverse_unit]
  rw [hginv, ← hgv] at hεs
  have hgc : Commute (g : E) (exp Y) := by rw [hgv]; exact (Commute.one_left _).add_left (hz.smul_left ε)
  -- conjugation by `g` is a continuous ring homomorphism, so it commutes with `exp`
  set φ := MulSemiringAction.toRingHom (ConjAct Eˣ) E (ConjAct.toConjAct g)
  have hφ : ∀ x : E, φ x = (g : E) * x * ↑g⁻¹ := fun x => by
    simp [φ, ConjAct.units_smul_def]
  have hφc : Continuous φ := by
    rw [show (φ : E → E) = fun x => (g : E) * x * ↑g⁻¹ from funext hφ]
    fun_prop
  have hexp : exp ((g : E) * Y * ↑g⁻¹) = exp Y := by
    rw [← hφ, ← map_exp_of_mem_ball (𝕂 := 𝕂) φ hφc Y (hsr hY), hφ, hgc.eq, mul_assoc,
      Units.mul_inv, mul_one]
  have hYeq := hinj hεs hY hexp
  have h3 : (g : E) * Y = Y * g := by
    calc (g : E) * Y = (g : E) * Y * ↑g⁻¹ * g := by rw [mul_assoc _ (↑g⁻¹ : E), Units.inv_mul, mul_one]
      _ = Y * g := by rw [hYeq]
  rw [hgv, add_mul, mul_add, one_mul, mul_one, add_right_inj, smul_mul_assoc, mul_smul_comm] at h3
  exact smul_right_injective _ hε0 h3

end LocalInverse

section Log

variable {F}

/-- **`expA` commutes with linear maps preserving powers** near `0` (algebra homomorphisms, right
multiplication, projections of a product): `φ(e^X) = e^{φ X}`. -/
lemma eventually_map_expA {B : Type*} [Ring B] [Algebra F B] [Module.Finite F B]
    [TopologicalSpace B] [IsModuleTopology F B] (φ : A →ₗ[F] B)
    (hφ : ∀ (X : A) (n : ℕ), φ (X ^ n) = φ X ^ n) :
    ∀ᶠ X in 𝓝 (0 : A), φ (expA F X) = expA F (φ X) := by
  letI := isTopologicalRing_of_moduleTopology F A
  letI := isTopologicalRing_of_moduleTopology F B
  obtain ⟨U, hU, hA⟩ := expA_hasSum F (A := A)
  obtain ⟨V, hV, hB⟩ := expA_hasSum F (A := B)
  have hφc : Continuous φ := IsModuleTopology.continuous_of_linearMap φ
  have hV' : φ ⁻¹' V ∈ 𝓝 (0 : A) :=
    hφc.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  haveI := t2Space_of_moduleTopology F B
  filter_upwards [hU, hV'] with X hX hX'
  have h1 := (hA X hX).map φ hφc
  refine h1.unique ?_
  convert hB (φ X) hX' using 1
  funext n
  simp [map_smul, hφ]

variable (F)

/-- An endomorphism of `F^d` commuting with all right multiplications is a left multiplication. -/
lemma eq_lmulPi_of_commute_rmulPi (Z : VA →L[F] VA) (h : ∀ a : A, Commute (rmulPi F a) Z) :
    Z = lmulPi F (lmulPiInv F Z) := by
  ext1 v
  set a := (toPiCLE F A).symm v
  have hv : rmulPi F a (toPiCLE F A 1) = v := by simp [rmulPi_apply, a]
  have h1 : Z v = rmulPi F a (Z (toPiCLE F A 1)) := by
    rw [← hv]
    exact (congrArg (fun W : VA →L[F] VA => W (toPiCLE F A 1)) (h a).eq).symm
  rw [h1, rmulPi_apply, lmulPi_apply]
  rfl

/-- **A local logarithm** on a finite-dimensional algebra over a `p`-adic field: a function
`log`, continuous at `1` with `log 1 = 0`, such that `e^{log u} = u` for `u` near `1`.  It is the
local inverse of `exp` on `End(F^d)` (`exists_localInverse_exp`), which preserves left
multiplications since it commutes with the commutant (`commute_of_commute_exp`). -/
theorem exists_logA : ∃ log : A → A, ContinuousAt log 1 ∧ log 1 = 0 ∧
    ∀ᶠ u in 𝓝 (1 : A), expA F (log u) = u := by
  obtain ⟨s, t, hs, -, hsr, ht, ht1, hinj, Lg, hLc, hL1, hLt⟩ :=
    exists_localInverse_exp (𝕂 := F) (E := VA →L[F] VA) (expSeries_radius_pos_of_pAdic F _)
  obtain ⟨U, hU, -, h⟩ := expA_aux F (A := A)
  set log : A → A := fun u => lmulPiInv F (Lg (lmulPi F u)) with hlog
  have hcont : ContinuousAt log 1 :=
    (lmulPiInv F).continuous.continuousAt.comp
      (ContinuousAt.comp_of_eq hLc (continuous_lmulPi F).continuousAt (lmulPi_one F))
  have hlog1 : log 1 = 0 := by simp [hlog, lmulPi_one, hL1]
  refine ⟨log, hcont, hlog1, ?_⟩
  have ht' : lmulPi F ⁻¹' t ∈ 𝓝 (1 : A) :=
    (continuous_lmulPi F).continuousAt.preimage_mem_nhds (by rw [lmulPi_one]; exact ht.mem_nhds ht1)
  have hU' : log ⁻¹' U ∈ 𝓝 (1 : A) := hcont.preimage_mem_nhds (by rwa [hlog1])
  filter_upwards [ht', hU'] with u hu hlu
  obtain ⟨hZs, hZe⟩ := hLt _ hu
  have hcomm : ∀ a : A, Commute (rmulPi F a) (Lg (lmulPi F u)) := by
    intro a
    refine commute_of_commute_exp hs hsr hinj hZs ?_
    rw [hZe]
    ext1 v
    simp [rmulPi_apply, lmulPi_apply, mul_assoc]
  have hZ := eq_lmulPi_of_commute_rmulPi F _ hcomm
  have hkey : lmulPi F (expA F (log u)) = lmulPi F u := by
    rw [(h _ hlu).2.2, show lmulPi F (log u) = Lg (lmulPi F u) from hZ.symm, hZe]
  have := congrArg (lmulPiInv F) hkey
  rwa [lmulPiInv_lmulPi, lmulPiInv_lmulPi] at this

end Log

end GSpinGGP
