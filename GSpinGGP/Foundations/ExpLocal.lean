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
* `eventually_map_expA`: `φ(e^X) = e^{φ X}` near `0` for linear maps preserving powers
  (pointwise form `eventually_map_expA_of_pow`);
* `exists_nhds_expA_sub_expA_mem`: `e^Y − e^X ∈ I` near `0` when `Yⁿ − Xⁿ ∈ I` for all `n`;
* `stabSubalgebra`, `expA_ad_eq`: `e^{ad Y} = Ad(e^Y)` near `0` in `End(A)`;
* `exists_nhds_expA_conj_mem`: `e^X r e^{-X}` stays in any `ad X`-stable subspace for `X` near `0`;
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

/-- **`φ(e^X) = e^{φ X}` near `0`** for a linear map `φ` that preserves the powers of `X` (only
of this `X`): both exponential series converge near `0`, and `φ` is continuous. -/
lemma eventually_map_expA_of_pow {B : Type*} [Ring B] [Algebra F B] [Module.Finite F B]
    [TopologicalSpace B] [IsModuleTopology F B] (φ : A →ₗ[F] B) :
    ∀ᶠ X in 𝓝 (0 : A), (∀ n : ℕ, φ (X ^ n) = φ X ^ n) → φ (expA F X) = expA F (φ X) := by
  letI := isTopologicalRing_of_moduleTopology F A
  letI := isTopologicalRing_of_moduleTopology F B
  obtain ⟨U, hU, hA⟩ := expA_hasSum F (A := A)
  obtain ⟨V, hV, hB⟩ := expA_hasSum F (A := B)
  have hφc : Continuous φ := IsModuleTopology.continuous_of_linearMap φ
  have hV' : φ ⁻¹' V ∈ 𝓝 (0 : A) :=
    hφc.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  haveI := t2Space_of_moduleTopology F B
  filter_upwards [hU, hV'] with X hX hX' hφ
  have h1 := (hA X hX).map φ hφc
  refine h1.unique ?_
  convert hB (φ X) hX' using 1
  funext n
  simp [map_smul, hφ]

/-- **`expA` commutes with linear maps preserving powers** near `0` (algebra homomorphisms, right
multiplication, projections of a product): `φ(e^X) = e^{φ X}`. -/
lemma eventually_map_expA {B : Type*} [Ring B] [Algebra F B] [Module.Finite F B]
    [TopologicalSpace B] [IsModuleTopology F B] (φ : A →ₗ[F] B)
    (hφ : ∀ (X : A) (n : ℕ), φ (X ^ n) = φ X ^ n) :
    ∀ᶠ X in 𝓝 (0 : A), φ (expA F X) = expA F (φ X) :=
  (eventually_map_expA_of_pow φ).mono fun X h => h (hφ X)

/-- **`e^Y − e^X ∈ I` near `0`** when `Yⁿ − Xⁿ ∈ I` for every `n`: the difference of the two
convergent exponential series has its partial sums in `I`, which is closed (finite-dimensional). -/
lemma exists_nhds_expA_sub_expA_mem (I : Submodule F A) :
    ∃ U ∈ 𝓝 (0 : A), ∀ X ∈ U, ∀ Y ∈ U, (∀ n : ℕ, Y ^ n - X ^ n ∈ I) →
      expA F Y - expA F X ∈ I := by
  letI := isTopologicalRing_of_moduleTopology F A
  haveI := t2Space_of_moduleTopology F A
  obtain ⟨U, hU, h⟩ := expA_hasSum F (A := A)
  refine ⟨U, hU, fun X hX Y hY hI => ?_⟩
  have hs := ((h Y hY).sub (h X hX)).tendsto_sum_nat
  refine I.closed_of_finiteDimensional.mem_of_tendsto hs (Eventually.of_forall fun n => ?_)
  refine I.sum_mem fun k _ => ?_
  rw [← smul_sub]
  exact I.smul_mem _ (hI k)

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

/-- The endomorphisms of `M` preserving the submodule `p`, as a subalgebra of `End(M)`. -/
def stabSubalgebra {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (p : Submodule R M) :
    Subalgebra R (Module.End R M) where
  carrier := {f | ∀ v ∈ p, f v ∈ p}
  mul_mem' hf hg v hv := hf _ (hg v hv)
  add_mem' hf hg v hv := p.add_mem (hf v hv) (hg v hv)
  algebraMap_mem' c v hv := by
    simpa [Module.algebraMap_end_apply] using p.smul_mem c hv

theorem mem_stabSubalgebra {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {p : Submodule R M} {f : Module.End R M} : f ∈ stabSubalgebra p ↔ ∀ v ∈ p, f v ∈ p :=
  Iff.rfl

section Ad

variable {F} {B : Type*} [Ring B] [Algebra F B]

/-- Right multiplication as a linear map `B → End(B)`. -/
def mulRightₗ : B →ₗ[F] Module.End F B := (LinearMap.mul F B).flip

omit [PAdicField F] in
theorem mulRightₗ_apply (a : B) : mulRightₗ (F := F) a = LinearMap.mulRight F a := rfl

variable [Module.Finite F B] [TopologicalSpace B] [IsModuleTopology F B]

variable (F) in
/-- **`e^{ad Y} = Ad(e^Y)`** for `Y` near `0`, in `End(B)` with its module topology:
`ad Y = L_Y − R_Y` with commuting `L_Y`, `R_Y`, and `e^{L_Y} = L_{e^Y}`, `e^{−R_Y} = R_{e^{−Y}}`. -/
theorem expA_ad_eq [TopologicalSpace (Module.End F B)] [IsModuleTopology F (Module.End F B)] :
    ∀ᶠ Y in 𝓝 (0 : B), expA F (LinearMap.mulLeft F Y - LinearMap.mulRight F Y) =
      LinearMap.mulLeft F (expA F Y) * LinearMap.mulRight F (expA F (-Y)) := by
  letI := isTopologicalRing_of_moduleTopology F B
  letI := isTopologicalRing_of_moduleTopology F (Module.End F B)
  obtain ⟨UB, hUB, hadd⟩ := expA_add_of_commute F (A := Module.End F B)
  have hl := eventually_map_expA (F := F) (A := B) (B := Module.End F B)
    (Algebra.lmul F B).toLinearMap (fun X n => map_pow (Algebra.lmul F B) X n)
  have hr := eventually_map_expA (F := F) (A := B) (B := Module.End F B) mulRightₗ
    (fun X n => by rw [mulRightₗ_apply, mulRightₗ_apply, LinearMap.pow_mulRight])
  have hcl : Continuous ((Algebra.lmul F B).toLinearMap : B → Module.End F B) :=
    IsModuleTopology.continuous_of_linearMap _
  have hcr : Continuous (mulRightₗ (F := F) : B → Module.End F B) :=
    IsModuleTopology.continuous_of_linearMap _
  have h1 : (fun Y : B => (Algebra.lmul F B).toLinearMap Y) ⁻¹' UB ∈ 𝓝 (0 : B) :=
    hcl.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  have h2 : (fun Y : B => -mulRightₗ (F := F) Y) ⁻¹' UB ∈ 𝓝 (0 : B) :=
    hcr.neg.continuousAt.preimage_mem_nhds (by simpa using hUB)
  have hr' : ∀ᶠ Y in 𝓝 (0 : B), mulRightₗ (F := F) (expA F (-Y)) = expA F (mulRightₗ (-Y)) :=
    (continuous_neg.tendsto' (0 : B) 0 neg_zero).eventually hr
  filter_upwards [hl, hr', h1, h2] with Y hlY hrY h1Y h2Y
  have hc : Commute (LinearMap.mulLeft F Y) (-LinearMap.mulRight F Y) :=
    (LinearMap.commute_mulLeft_right Y Y).neg_right
  have h1Y' : LinearMap.mulLeft F Y ∈ UB := h1Y
  have h2Y' : -LinearMap.mulRight F Y ∈ UB := h2Y
  rw [sub_eq_add_neg, hadd _ h1Y' _ h2Y' hc]
  congr 1
  · exact hlY.symm
  · rw [mulRightₗ_apply, map_neg, mulRightₗ_apply] at hrY
    exact hrY.symm

end Ad

/-- **`e^X r e^{-X}` stays in an `ad X`-stable subspace** for `X` near `0`: in `End(A)`,
`L_{e^X} R_{e^{-X}} = e^{ad X}` (`expA_ad_eq`), and `e^{ad X} ∈ F[ad X]` preserves `R`. -/
lemma exists_nhds_expA_conj_mem :
    ∃ U ∈ 𝓝 (0 : A), ∀ X ∈ U, ∀ R : Submodule F A, (∀ r ∈ R, X * r - r * X ∈ R) →
      ∀ r ∈ R, expA F X * r * expA F (-X) ∈ R := by
  letI : TopologicalSpace (Module.End F A) := moduleTopology F (Module.End F A)
  haveI : IsModuleTopology F (Module.End F A) := ⟨rfl⟩
  letI := isTopologicalRing_of_moduleTopology F A
  letI := isTopologicalRing_of_moduleTopology F (Module.End F A)
  obtain ⟨UB, hUB, hadj⟩ := exists_nhds_expA_mem_adjoin F (A := Module.End F A)
  obtain ⟨U, hU, hAd⟩ := (expA_ad_eq F (B := A)).exists_mem
  set ad : A →ₗ[F] Module.End F A := (Algebra.lmul F A).toLinearMap - mulRightₗ with had
  have h3 : ad ⁻¹' UB ∈ 𝓝 (0 : A) :=
    (IsModuleTopology.continuous_of_linearMap ad).continuousAt.preimage_mem_nhds
      (by rwa [map_zero])
  refine ⟨U ∩ ad ⁻¹' UB, inter_mem hU h3, fun X hX R hR r hr => ?_⟩
  have hadR : ad X ∈ stabSubalgebra R := fun r hr => by
    simpa [had, mulRightₗ_apply] using hR r hr
  have hmem : expA F (ad X) ∈ stabSubalgebra R :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hadR) (hadj _ hX.2)
  have := hmem r hr
  rw [show ad X = LinearMap.mulLeft F X - LinearMap.mulRight F X from rfl, hAd X hX.1] at this
  simpa [mul_assoc] using this

/-! ## `exp` detects skew endomorphisms near `0` -/

section SkewExp

variable {F}

variable {U : Type*} [AddCommGroup U] [Module F U] [Module.Finite F U]

/-- The pairs `(T, T')` adjoint for `B` (`B(T u, v) = B(u, T' v)`), as a subalgebra of
`End U × End Uᵐᵒᵖ`. -/
def adjointPairSubalgebra (B : LinearMap.BilinForm F U) :
    Subalgebra F (Module.End F U × (Module.End F U)ᵐᵒᵖ) where
  carrier := {Z | LinearMap.IsAdjointPair B B ⇑Z.1 ⇑(MulOpposite.unop Z.2 : Module.End F U)}
  mul_mem' := fun {_ _} hZ hW => hZ.mul hW
  add_mem' := fun {_ _} hZ hW => hZ.add hW
  algebraMap_mem' := fun r => by
    change LinearMap.IsAdjointPair B B ⇑(r • (1 : Module.End F U)) ⇑(r • (1 : Module.End F U))
    rw [LinearMap.coe_smul]
    exact (LinearMap.isAdjointPair_one (B := B)).smul r

/-- **`exp` detects skew endomorphisms near `0`**: if `e^Y` is an isometry of `B` and `Y` is
near `0`, then `(Y, −Y)` is an adjoint pair, i.e. `Y` is skew for `B`.  In
`End U × End Uᵐᵒᵖ`, `e^{(Y, −Y)} = (e^Y, e^{−Y})` is an adjoint pair (`e^{−Y} = (e^Y)⁻¹`), and
`exp` detects subalgebras near `0` (`exists_nhds_mem_of_expA_mem`). -/
theorem eventually_isAdjointPair_neg_of_isOrthogonal_expA
    [TopologicalSpace (Module.End F U)] [IsModuleTopology F (Module.End F U)]
    (B : LinearMap.BilinForm F U) :
    ∀ᶠ Y in 𝓝 (0 : Module.End F U), LinearMap.IsOrthogonal B ⇑(expA F Y : Module.End F U) →
      LinearMap.IsAdjointPair B B ⇑Y ⇑(-Y) := by
  let E := Module.End F U
  let A₂ := E × Eᵐᵒᵖ
  let _ : TopologicalSpace A₂ := moduleTopology F A₂
  have : IsModuleTopology F A₂ := ⟨rfl⟩
  have := IsModuleTopology.toContinuousAdd F A₂
  have := IsModuleTopology.toContinuousAdd F E
  obtain ⟨V, hV, hmem⟩ := exists_nhds_mem_of_expA_mem F (A := A₂)
  have h1 := eventually_map_expA (F := F) (A := A₂) (B := E) (LinearMap.fst F E Eᵐᵒᵖ)
    (fun Z n => Prod.pow_fst Z n)
  have h2 := eventually_map_expA (F := F) (A := A₂) (B := E)
    ((MulOpposite.opLinearEquiv F).symm.toLinearMap ∘ₗ LinearMap.snd F E Eᵐᵒᵖ)
    (fun Z n => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        MulOpposite.coe_opLinearEquiv_symm]
      change MulOpposite.unop ((Z ^ n : E × Eᵐᵒᵖ).2) = MulOpposite.unop (Z : E × Eᵐᵒᵖ).2 ^ n
      rw [Prod.pow_snd, MulOpposite.unop_pow])
  let j : E →ₗ[F] A₂ :=
    LinearMap.prod LinearMap.id ((MulOpposite.opLinearEquiv F).toLinearMap ∘ₗ (-LinearMap.id))
  have hj : Continuous j := IsModuleTopology.continuous_of_linearMap j
  have hjt : Filter.Tendsto j (𝓝 0) (𝓝 0) := hj.tendsto' 0 0 (map_zero j)
  obtain ⟨Ui, hUi, hinv⟩ := expA_mul_expA_neg F (A := E)
  filter_upwards [hjt hV, hjt.eventually h1, hjt.eventually h2, hUi] with Y hYV hY1 hY2 hYi horth
  have e1 : (expA F (j Y)).1 = expA F Y := hY1
  have e2 : MulOpposite.unop (expA F (j Y)).2 = expA F (-Y) := hY2
  have hP : expA F (j Y) ∈ adjointPairSubalgebra B := by
    intro u v
    change B ((expA F (j Y)).1 u) v = B u ((MulOpposite.unop (expA F (j Y)).2) v)
    rw [e1, e2]
    have hv : expA F Y (expA F (-Y) v) = v := by
      rw [← Module.End.mul_apply, hinv Y hYi, Module.End.one_apply]
    conv_lhs => rw [← hv]
    exact horth u _
  exact hmem (j Y) hYV _ hP

end SkewExp

end GSpinGGP
