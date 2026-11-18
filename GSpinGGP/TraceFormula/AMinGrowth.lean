/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LogNormDescent
import GSpinGGP.Foundations.HypTorusNorm
import GSpinGGP.Foundations.LogNormCompact
import GSpinGGP.HarmonicAnalysis.LatticeGrowth

/-!
# Polynomial growth of the split torus `A_min` modulo `A_G` (BP (6.7.12))

Beuzart-Plessis (Astérisque 418, proof of Prop. 6.7.1(iii), p. 152; Thesis Prop. 8.4.1(iii))
reduces the polynomial growth of `H(F)\G(F)` to the following fact, "not hard to prove and left
to the reader":

> (6.7.12) Let `C_min ⊆ A_min(F)` be a compact subset with nonempty interior. Then there is
> `N > 0` such that for all `R ≥ 1` the set `{a ∈ A_min(F) ; σ_G(a) < R}` may be covered by
> fewer than `(1 + R)^N` subsets `a C_min`, `a ∈ A_min(F)`.

BP's groups have compact centre. For `G = GSpin(W) × GSpin(V)` the split centre `A_G` is not
compact, and the statement is made modulo `A_G`, for the log-norm `σ_{A_G\G}` of `A_G(F)\G(F)`
(`infLeft (logNorm F d.G) d.AG`, which is `GGPData.logNormModAG` by definition): the set
`{a ; σ_{A_G\G}(a) < R}` is covered by `≪ (1 + R)^N` sets `A_G(F) j C`, for a fixed compact
`C ⊆ G(F)`. This is the form required by `WeakCartanData.growth`
(`HarmonicAnalysis/PolynomialGrowth.lean`).

## The torus

A maximal split torus of `GSpin(V)` is the preimage of one of `SO(V)` (the kernel `G_m` is a split
torus). We work with the preimage under `P̄ : G → SO(W) × SO(V)` of the split tori of two
hyperbolic frames (`hypTorus`, `Foundations/HypFrame.lean`), both in `V`: the `W`-factor acts on
`V = W ⊕ Z` through `g ↦ g ⊕ 1` (`GGPData.extZ`), as in `TraceFormula/GoodParabolicLift.lean`.
The frames need not be maximal; for the frames of a weak Cartan decomposition the tori
`multiTorus` lie in these (`WeakCartan.multiTorus_mem_hypTorus`).

## Proof

The coordinates of `a` are the integers `⌊log ‖tᵢ‖⌋` of its eigenvalues `tᵢ` on the frames
(`hypParam`). They are bounded by `σ_{A_G\G}(a)` (`‖tᵢ^{±1}‖ ≤ ‖P̄(a)‖` and the easy half of the
norm comparison, `exists_logNormSO_Pbar_le`), and two elements with the same coordinates differ by
an element of `A_G` times an element of a fixed log-norm ball (the parameters of the quotient lie
in a fixed annulus, `IsHypFrame.exists_norm_le_of_mem_hypTorus`, then norm descent
`exists_logNorm_scalars_mul_le`); the count is `exists_finset_cover_of_intCoord`.

When `W` (or `V`) is a hyperbolic plane, `A_G` contains all of `GSpin(W)` and `σ_{A_G\G}` does not
see the `W`-component; that factor is then absorbed into `A_G` and carries no coordinates.

## Main results

* `GGPData.frameTorus`: `P̄⁻¹` of the product of the two frame tori.
* `GGPData.exists_cover_frameTorus`: (6.7.12) modulo `A_G`, as a covering by sets `z j e`,
  `z ∈ A_G`, `j` in a finite set of size `≤ M (1 + R)^N`, `e` in a compact set.
* `GGPData.exists_growth_frameTorus`: the same in the form of `WeakCartanData.growth`, for any
  `S ⊆ A_G · frameTorus` and any `π` invariant under left multiplication by `A_G`.
-/

noncomputable section

open Set QuadraticMap
open scoped Pointwise

namespace GSpinGGP

namespace GGPData

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
variable (d : GGPData F)

/-! ## The torus -/

/-- `g ↦ P(g_W) ⊕ 1 ∈ GL(V)`, the `W`-component of `P̄` acting on `V = W ⊕ Z`. -/
def PbarW : d.G →* (d.V ≃ₗ[F] d.V) :=
  d.extZ.comp ((SOGrp d.QW).subtype.comp ((MonoidHom.fst _ _).comp d.Pbar))

/-- `g ↦ P(g_V) ∈ GL(V)`, the `V`-component of `P̄`. -/
def PbarV : d.G →* (d.V ≃ₗ[F] d.V) :=
  (SOGrp d.QV).subtype.comp ((MonoidHom.snd _ _).comp d.Pbar)

theorem PbarW_apply (g : d.G) :
    d.PbarW g = d.extZ ((d.Pbar g).1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) := rfl

theorem PbarV_apply (g : d.G) : d.PbarV g = ((d.Pbar g).2 : d.V ≃ₗ[F] d.V) := rfl

theorem glMaxNorm_extZ (f : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) :
    glMaxNorm (d.extZ f) = glMaxNorm f :=
  glMaxNorm_prodCongr_refl (Z := d.Z) f

variable {n₁ n₂ : ℕ} (W₁ W₂ : Submodule F d.V) (e₁ f₁ : Fin n₁ → d.V) (e₂ f₂ : Fin n₂ → d.V)

/-- **The split torus of two frames**: the `g ∈ G(F)` with `P(g_W) ⊕ 1` in the torus of the
frame `(e₁, f₁)` and `P(g_V)` in the torus of the frame `(e₂, f₂)` (both frames in `V`). For maximal
frames this is `A_min(F)`; it contains the scalars `Z(F) = ker P̄`. -/
def frameTorus : Subgroup d.G :=
  (hypTorus W₁ e₁ f₁).comap d.PbarW ⊓ (hypTorus W₂ e₂ f₂).comap d.PbarV

theorem mem_frameTorus {g : d.G} :
    g ∈ d.frameTorus W₁ W₂ e₁ f₁ e₂ f₂ ↔
      d.PbarW g ∈ hypTorus W₁ e₁ f₁ ∧ d.PbarV g ∈ hypTorus W₂ e₂ f₂ := Iff.rfl

/-! ## `A_G` and the two factors -/

/-- If `W` is not a hyperbolic plane, `A_G` has trivial image in `SO(W)`. -/
theorem Pbar_fst_eq_one_of_mem_AG (hW : ¬ IsHypPlane d.QW) {z : d.G} (hz : z ∈ d.AG) :
    (d.Pbar z).1 = 1 := by
  obtain ⟨⟨a, b⟩, ⟨ha, -⟩, rfl⟩ := hz
  have ha' : a ∈ (scalarGSpin d.QW).range := by
    unfold splitCentralGSpin at ha; rwa [ite_eq_right_of_eq_false _ _ (eq_false hW)] at ha
  obtain ⟨c, rfl⟩ := ha'
  exact Subtype.ext (specP_scalarGSpin_eq_one c)

/-- If `V` is not a hyperbolic plane, `A_G` has trivial image in `SO(V)`. -/
theorem Pbar_snd_eq_one_of_mem_AG (hV : ¬ IsHypPlane d.QV) {z : d.G} (hz : z ∈ d.AG) :
    (d.Pbar z).2 = 1 := by
  obtain ⟨⟨a, b⟩, ⟨-, hb⟩, rfl⟩ := hz
  have hb' : b ∈ (scalarGSpin d.QV).range := by
    unfold splitCentralGSpin at hb; rwa [ite_eq_right_of_eq_false _ _ (eq_false hV)] at hb
  obtain ⟨c, rfl⟩ := hb'
  exact Subtype.ext (specP_scalarGSpin_eq_one c)

theorem PbarW_mul_of_mem_AG (hW : ¬ IsHypPlane d.QW) {z : d.G} (hz : z ∈ d.AG) (g : d.G) :
    d.PbarW (z * g) = d.PbarW g := by
  rw [map_mul, d.PbarW_apply z, d.Pbar_fst_eq_one_of_mem_AG hW hz]
  simp

theorem PbarV_mul_of_mem_AG (hV : ¬ IsHypPlane d.QV) {z : d.G} (hz : z ∈ d.AG) (g : d.G) :
    d.PbarV (z * g) = d.PbarV g := by
  rw [map_mul, d.PbarV_apply z, d.Pbar_snd_eq_one_of_mem_AG hV hz]
  simp

open Classical in
/-- The element of `A_G` absorbing the hyperbolic-plane factors of `g`: its `W`-component is `g_W`
if `W` is a hyperbolic plane (then `A_{GSpin(W)} = GSpin(W)`) and `1` otherwise; the same for
`V`. -/
def hypPart (g : d.G) : d.G :=
  d.pair (if IsHypPlane d.QW then d.fst g else 1, if IsHypPlane d.QV then d.snd g else 1)

theorem hypPart_mem_AG (g : d.G) : d.hypPart g ∈ d.AG := by
  classical
  refine ⟨_, ⟨?_, ?_⟩, rfl⟩
  · change (if IsHypPlane d.QW then d.fst g else 1) ∈ splitCentralGSpin d.QW
    by_cases hW : IsHypPlane d.QW
    · simp only [hW, ite_true, splitCentralGSpin]; exact Subgroup.mem_top _
    · simp only [hW, ite_false]; exact one_mem _
  · change (if IsHypPlane d.QV then d.snd g else 1) ∈ splitCentralGSpin d.QV
    by_cases hV : IsHypPlane d.QV
    · simp only [hV, ite_true, splitCentralGSpin]; exact Subgroup.mem_top _
    · simp only [hV, ite_false]; exact one_mem _

theorem PbarW_hypPart_inv_mul (hW : IsHypPlane d.QW) (g : d.G) :
    d.PbarW ((d.hypPart g)⁻¹ * g) = 1 := by
  classical
  have : d.fst ((d.hypPart g)⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, hypPart, fst_pair]; simp [hW]
  rw [PbarW_apply]
  have h1 : (d.Pbar ((d.hypPart g)⁻¹ * g)).1 = 1 := Subtype.ext (by
    change specP d.QW (d.fst _) = 1
    rw [this, map_one])
  rw [h1]; simp

theorem PbarV_hypPart_inv_mul (hV : IsHypPlane d.QV) (g : d.G) :
    d.PbarV ((d.hypPart g)⁻¹ * g) = 1 := by
  classical
  have : d.snd ((d.hypPart g)⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, hypPart, snd_pair]; simp [hV]
  rw [PbarV_apply]
  have h1 : (d.Pbar ((d.hypPart g)⁻¹ * g)).2 = 1 := Subtype.ext (by
    change specP d.QV (d.snd _) = 1
    rw [this, map_one])
  rw [h1]; rfl

/-! ## Norm estimates -/

omit [PAdicField F] in
/-- `|log ‖t‖| ≤ log M` when `‖t‖, ‖t⁻¹‖ ≤ M`. -/
theorem abs_log_norm_le_log {t : F} (ht : t ≠ 0) {M : ℝ} (h1 : ‖t‖ ≤ M) (h2 : ‖t⁻¹‖ ≤ M) :
    |Real.log ‖t‖| ≤ Real.log M := by
  have ht' : 0 < ‖t‖ := norm_pos_iff.2 ht
  have hti : 0 < ‖t⁻¹‖ := norm_pos_iff.2 (inv_ne_zero ht)
  rw [abs_le]
  constructor
  · have := Real.log_le_log hti h2
    rw [norm_inv, Real.log_inv] at this
    linarith
  · exact Real.log_le_log ht' h1

variable {W₁ W₂ e₁ f₁ e₂ f₂}

/-- The coordinates of a torus element: `|⌊log ‖tᵢ‖⌋| ≤ log ‖y‖_{GL} + 1`. -/
theorem abs_floor_log_hypParam_le {n : ℕ} {W' : Submodule F d.V} {e f : Fin n → d.V}
    (hF : IsHypFrame d.QV W' e f) {y : d.V ≃ₗ[F] d.V} (hy : y ∈ hypTorus W' e f) (i : Fin n) :
    |(⌊Real.log ‖hypParam d.QV e f y i‖⌋ : ℝ)| ≤ Real.log (glMaxNorm y) + 1 := by
  refine (abs_floor_log_norm_le _).trans ?_
  gcongr
  exact abs_log_norm_le_log (hF.apply_e_of_mem_hypTorus hy i).2.2
    ((hF.norm_hypParam_le hy i).trans (norm_le_glMaxNorm y))
    ((hF.norm_inv_hypParam_le hy i).trans (norm_le_glMaxNorm y))

/-- Torus elements whose parameters lie in the annulus `e⁻¹ < ‖tᵢ‖ < e` are bounded in `GL(V)`. -/
theorem exists_glMaxNorm_le_of_hypParam {n : ℕ} {W' : Submodule F d.V} {e f : Fin n → d.V}
    (hF : IsHypFrame d.QV W' e f) :
    ∃ C, 1 ≤ C ∧ ∀ y ∈ hypTorus W' e f,
      (∀ i, ‖hypParam d.QV e f y i‖ ≤ Real.exp 1 ∧ ‖(hypParam d.QV e f y i)⁻¹‖ ≤ Real.exp 1) →
      glMaxNorm y ≤ C := by
  obtain ⟨C, hC, h⟩ := hF.exists_norm_le_of_mem_hypTorus
  refine ⟨max 1 (C * (1 + Real.exp 1)), le_max_left _ _, fun y hy hp => ?_⟩
  have hyi : y⁻¹ ∈ hypTorus W' e f := (hypTorus W' e f).inv_mem hy
  have hpi : ∀ i, ‖hypParam d.QV e f y⁻¹ i‖ ≤ Real.exp 1 ∧
      ‖(hypParam d.QV e f y⁻¹ i)⁻¹‖ ≤ Real.exp 1 := fun i => by
    rw [hF.hypParam_inv hy, inv_inv]; exact ⟨(hp i).2, (hp i).1⟩
  refine max_le (le_max_left _ _) (max_le ?_ ?_)
  · exact (h y hy _ (Real.exp_pos 1).le hp).trans (le_max_right _ _)
  · exact (h _ hyi _ (Real.exp_pos 1).le hpi).trans (le_max_right _ _)

/-! ## The covering -/

open Classical in
/-- The integer coordinates of `g` on the frame tori: `⌊log ‖tᵢ‖⌋` for the eigenvalues `tᵢ` of
`P̄(g)`, on each factor that is not a hyperbolic plane (`0` on a hyperbolic-plane factor). -/
def frameCoord (e₁ f₁ : Fin n₁ → d.V) (e₂ f₂ : Fin n₂ → d.V) (g : d.G) :
    Fin n₁ ⊕ Fin n₂ → ℤ :=
  Sum.elim
    (fun i => if IsHypPlane d.QW then 0 else ⌊Real.log ‖hypParam d.QV e₁ f₁ (d.PbarW g) i‖⌋)
    (fun i => if IsHypPlane d.QV then 0 else ⌊Real.log ‖hypParam d.QV e₂ f₂ (d.PbarV g) i‖⌋)

/-- The elements whose `P̄`-image lies in the frame tori on the factors that are not hyperbolic
planes; this set contains `A_G · frameTorus` and is stable under `A_G`. -/
def frameTorusModAG (W₁ W₂ : Submodule F d.V) (e₁ f₁ : Fin n₁ → d.V) (e₂ f₂ : Fin n₂ → d.V) :
    Set d.G :=
  {g | (¬ IsHypPlane d.QW → d.PbarW g ∈ hypTorus W₁ e₁ f₁) ∧
    (¬ IsHypPlane d.QV → d.PbarV g ∈ hypTorus W₂ e₂ f₂)}

theorem AG_mul_frameTorus_subset :
    (d.AG : Set d.G) * (d.frameTorus W₁ W₂ e₁ f₁ e₂ f₂ : Set d.G) ⊆
      d.frameTorusModAG W₁ W₂ e₁ f₁ e₂ f₂ := by
  rintro _ ⟨z, hz, g, ⟨hgW, hgV⟩, rfl⟩
  exact ⟨fun hW => by rw [d.PbarW_mul_of_mem_AG hW hz]; exact hgW,
    fun hV => by rw [d.PbarV_mul_of_mem_AG hV hz]; exact hgV⟩

/-- `σ_{A_G\G}` bounds `log ‖P(g_W)‖_{GL}` when `W` is not a hyperbolic plane (and the same for
`V`): from `σ_{Ḡ} ∘ P̄ ≪ σ_G` and `A_G ↦ 1` on that factor. -/
theorem exists_log_glMaxNorm_le :
    ∃ c, 0 ≤ c ∧ ∀ g : d.G,
      (¬ IsHypPlane d.QW → Real.log (glMaxNorm (d.PbarW g)) ≤
        c * (infLeft (logNorm F d.G) d.AG g + 1)) ∧
      (¬ IsHypPlane d.QV → Real.log (glMaxNorm (d.PbarV g)) ≤
        c * (infLeft (logNorm F d.G) d.AG g + 1)) := by
  obtain ⟨c, hc, hle⟩ := d.exists_logNormSO_Pbar_le
  refine ⟨c, hc, fun g => ?_⟩
  have hne : Nonempty d.AG := ⟨1⟩
  obtain ⟨⟨z, hz⟩, hzlt⟩ := exists_lt_of_ciInf_lt (f := fun s : d.AG => logNorm F d.G (s * g))
    (show infLeft (logNorm F d.G) d.AG g < infLeft (logNorm F d.G) d.AG g + 1 by linarith)
  have hSO := hle (z * g)
  have hM := d.one_le_max_glMaxNorm (d.Pbar (z * g))
  have hlogSO : ∀ x, 1 ≤ x → x ≤ max (glMaxNorm ((d.Pbar (z * g)).1 :
      (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))) (glMaxNorm ((d.Pbar (z * g)).2 : d.V ≃ₗ[F] d.V)) →
      Real.log x ≤ c * (infLeft (logNorm F d.G) d.AG g + 1) := by
    intro x hx hxM
    have h1 := Real.log_le_log (by linarith) hxM
    have : d.logNormSO (d.Pbar (z * g)) ≤ c * (infLeft (logNorm F d.G) d.AG g + 1) :=
      hSO.trans (mul_le_mul_of_nonneg_left hzlt.le hc)
    rw [logNormSO] at this
    linarith
  refine ⟨fun hW => ?_, fun hV => ?_⟩
  · rw [← d.PbarW_mul_of_mem_AG hW hz, PbarW_apply, glMaxNorm_extZ]
    exact hlogSO _ (one_le_glMaxNorm _) (le_max_left _ _)
  · rw [← d.PbarV_mul_of_mem_AG hV hz, PbarV_apply]
    exact hlogSO _ (one_le_glMaxNorm _) (le_max_right _ _)

/-- **The coordinates are bounded by `σ_{A_G\G}`**: `|vᵢ(a)| ≤ c (σ_{A_G\G}(a) + 2)` on
`frameTorusModAG`. -/
theorem exists_abs_frameCoord_le (hF₁ : IsHypFrame d.QV W₁ e₁ f₁)
    (hF₂ : IsHypFrame d.QV W₂ e₂ f₂) :
    ∃ c, 1 ≤ c ∧ ∀ a ∈ d.frameTorusModAG W₁ W₂ e₁ f₁ e₂ f₂, ∀ i,
      c⁻¹ * |(d.frameCoord e₁ f₁ e₂ f₂ a i : ℝ)| ≤ infLeft (logNorm F d.G) d.AG a + 2 := by
  classical
  obtain ⟨c, hc, hlog⟩ := d.exists_log_glMaxNorm_le
  refine ⟨max c 1, le_max_right _ _, fun a ha i => ?_⟩
  set τ := infLeft (logNorm F d.G) d.AG a
  have hτ0 : 0 ≤ τ := le_ciInf fun s => zero_le_one.trans (one_le_logNorm _ _)
  have key : ∀ L : ℝ, L ≤ c * (τ + 1) → ∀ x : ℝ, |x| ≤ L + 1 → (max c 1)⁻¹ * |x| ≤ τ + 2 := by
    intro L hL x hx
    rw [inv_mul_le_iff₀ (zero_lt_one.trans_le (le_max_right _ _))]
    have h1 : c * (τ + 1) ≤ max c 1 * (τ + 1) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    have h2 : 1 ≤ max c 1 := le_max_right _ _
    nlinarith
  cases i with
  | inl i =>
    by_cases hW : IsHypPlane d.QW
    · simp only [frameCoord, Sum.elim_inl, hW, ite_true, Int.cast_zero, abs_zero, mul_zero]
      linarith
    · simp only [frameCoord, Sum.elim_inl, hW, ite_false]
      exact key _ ((hlog a).1 hW) _ (d.abs_floor_log_hypParam_le hF₁ (ha.1 hW) i)
  | inr i =>
    by_cases hV : IsHypPlane d.QV
    · simp only [frameCoord, Sum.elim_inr, hV, ite_true, Int.cast_zero, abs_zero, mul_zero]
      linarith
    · simp only [frameCoord, Sum.elim_inr, hV, ite_false]
      exact key _ ((hlog a).2 hV) _ (d.abs_floor_log_hypParam_le hF₂ (ha.2 hV) i)

/-- Two torus elements with the same coordinates `⌊log ‖tᵢ‖⌋` differ by a bounded torus element. -/
theorem glMaxNorm_inv_mul_le_of_floor_eq {n : ℕ} {W' : Submodule F d.V}
    {e f : Fin n → d.V} (hF : IsHypFrame d.QV W' e f) {C : ℝ}
    (hb : ∀ y ∈ hypTorus W' e f, (∀ i, ‖hypParam d.QV e f y i‖ ≤ Real.exp 1 ∧
      ‖(hypParam d.QV e f y i)⁻¹‖ ≤ Real.exp 1) → glMaxNorm y ≤ C)
    {y y' : d.V ≃ₗ[F] d.V} (hy : y ∈ hypTorus W' e f) (hy' : y' ∈ hypTorus W' e f)
    (hc : ∀ i, ⌊Real.log ‖hypParam d.QV e f y i‖⌋ = ⌊Real.log ‖hypParam d.QV e f y' i‖⌋) :
    glMaxNorm (y⁻¹ * y') ≤ C := by
  have hyi := (hypTorus W' e f).inv_mem hy
  refine hb _ (mul_mem hyi hy') fun i => ?_
  have hp := (hF.apply_e_of_mem_hypTorus hy i).2.2
  have hp' := (hF.apply_e_of_mem_hypTorus hy' i).2.2
  rw [hF.hypParam_mul hyi hy', hF.hypParam_inv hy, mul_inv, inv_inv]
  constructor
  · rw [mul_comm, ← div_eq_mul_inv]
    exact (norm_div_lt_exp_of_floor_log_norm_eq hp' hp (hc i).symm).le
  · rw [← div_eq_mul_inv]
    exact (norm_div_lt_exp_of_floor_log_norm_eq hp hp' (hc i)).le

/-- **Same coordinates, bounded quotient modulo `A_G`**: there is `B` such that two elements
`a, a'` of `frameTorusModAG` with the same coordinates have
`σ_{Ḡ}(P̄(z₀⁻¹ a⁻¹ a')) ≤ B` for some `z₀ ∈ A_G`. -/
theorem exists_logNormSO_le_of_frameCoord_eq (hF₁ : IsHypFrame d.QV W₁ e₁ f₁)
    (hF₂ : IsHypFrame d.QV W₂ e₂ f₂) :
    ∃ B, ∀ a ∈ d.frameTorusModAG W₁ W₂ e₁ f₁ e₂ f₂, ∀ a' ∈ d.frameTorusModAG W₁ W₂ e₁ f₁ e₂ f₂,
      d.frameCoord e₁ f₁ e₂ f₂ a = d.frameCoord e₁ f₁ e₂ f₂ a' →
      d.logNormSO (d.Pbar ((d.hypPart (a⁻¹ * a'))⁻¹ * (a⁻¹ * a'))) ≤ B := by
  classical
  obtain ⟨C₁, hC₁, hb₁⟩ := d.exists_glMaxNorm_le_of_hypParam hF₁
  obtain ⟨C₂, hC₂, hb₂⟩ := d.exists_glMaxNorm_le_of_hypParam hF₂
  refine ⟨1 + Real.log (max C₁ C₂), fun a ha a' ha' hcoord => ?_⟩
  set g := a⁻¹ * a'
  have hz₀ : d.hypPart g ∈ d.AG := d.hypPart_mem_AG g
  have hW0 : glMaxNorm (d.PbarW ((d.hypPart g)⁻¹ * g)) ≤ max C₁ C₂ := by
    by_cases hW : IsHypPlane d.QW
    · rw [d.PbarW_hypPart_inv_mul hW, glMaxNorm_one]; exact hC₁.trans (le_max_left _ _)
    · rw [d.PbarW_mul_of_mem_AG hW (d.AG.inv_mem hz₀), map_mul, map_inv]
      refine (d.glMaxNorm_inv_mul_le_of_floor_eq hF₁ hb₁ (ha.1 hW) (ha'.1 hW) fun i => ?_).trans
        (le_max_left _ _)
      have := congrFun hcoord (Sum.inl i)
      simpa only [frameCoord, Sum.elim_inl, hW, ite_false] using this
  have hV0 : glMaxNorm (d.PbarV ((d.hypPart g)⁻¹ * g)) ≤ max C₁ C₂ := by
    by_cases hV : IsHypPlane d.QV
    · rw [d.PbarV_hypPart_inv_mul hV, glMaxNorm_one]; exact hC₁.trans (le_max_left _ _)
    · rw [d.PbarV_mul_of_mem_AG hV (d.AG.inv_mem hz₀), map_mul, map_inv]
      refine (d.glMaxNorm_inv_mul_le_of_floor_eq hF₂ hb₂ (ha.2 hV) (ha'.2 hV) fun i => ?_).trans
        (le_max_right _ _)
      have := congrFun hcoord (Sum.inr i)
      simpa only [frameCoord, Sum.elim_inr, hV, ite_false] using this
  rw [PbarW_apply, glMaxNorm_extZ] at hW0
  rw [PbarV_apply] at hV0
  have h1 := Real.log_le_log (zero_lt_one.trans_le (d.one_le_max_glMaxNorm _)) (max_le hW0 hV0)
  rw [logNormSO]
  linarith

/-- **BP (6.7.12) modulo `A_G`**, covering form: for two hyperbolic frames of `V` there are a
compact `C ⊆ G(F)` and `M`, `N` such that for every `R ≥ 1` some finite `t ⊆ frameTorusModAG` of
size `≤ M (1 + R)^N` has: every `a ∈ A_G(F) · frameTorus` (more generally every
`a ∈ frameTorusModAG`) with `σ_{A_G\G}(a) < R` is `z j e` with `z ∈ A_G(F)`, `j ∈ t`, `e ∈ C`.
(`N` is the number of pairs in the two frames.) -/
theorem exists_cover_frameTorus (hF₁ : IsHypFrame d.QV W₁ e₁ f₁)
    (hF₂ : IsHypFrame d.QV W₂ e₂ f₂) :
    ∃ CS : Set d.G, IsCompact CS ∧ ∃ (M : ℝ) (N : ℕ), ∀ R : ℝ, 1 ≤ R →
      ∃ t : Finset d.G, (t : Set d.G) ⊆ d.frameTorusModAG W₁ W₂ e₁ f₁ e₂ f₂ ∧
        (t.card : ℝ) ≤ M * (1 + R) ^ N ∧
        ∀ a ∈ d.frameTorusModAG W₁ W₂ e₁ f₁ e₂ f₂, infLeft (logNorm F d.G) d.AG a < R →
          ∃ z ∈ d.AG, ∃ j ∈ t, ∃ e ∈ CS, a = z * (j * e) := by
  obtain ⟨B, hB⟩ := d.exists_logNormSO_le_of_frameCoord_eq hF₁ hF₂
  obtain ⟨Cd, -, hdesc⟩ := d.exists_logNorm_scalars_mul_le
  obtain ⟨c, hc, hv⟩ := d.exists_abs_frameCoord_le hF₁ hF₂
  set CS : Set d.G := {g | logNorm F d.G g ≤ Cd * B}
  have hE : ∀ a ∈ d.frameTorusModAG W₁ W₂ e₁ f₁ e₂ f₂,
      ∀ a' ∈ d.frameTorusModAG W₁ W₂ e₁ f₁ e₂ f₂,
      d.frameCoord e₁ f₁ e₂ f₂ a = d.frameCoord e₁ f₁ e₂ f₂ a' →
      ∃ z ∈ (d.AG : Set d.G), ∃ e ∈ CS, a' = z * (a * e) := by
    intro a ha a' ha' hcoord
    have hz₀ := d.hypPart_mem_AG (a⁻¹ * a')
    obtain ⟨ζ, hζ, hζle⟩ := hdesc ((d.hypPart (a⁻¹ * a'))⁻¹ * (a⁻¹ * a'))
    have hzA : d.hypPart (a⁻¹ * a') * ζ⁻¹ ∈ d.AG :=
      d.AG.mul_mem hz₀ (d.AG.inv_mem (d.scalars_le_AG hζ))
    refine ⟨_, hzA, _, hζle.trans (mul_le_mul_of_nonneg_left (hB a ha a' ha' hcoord) ?_), ?_⟩
    · have := d.one_le_logNormSO (d.Pbar ((d.hypPart (a⁻¹ * a'))⁻¹ * (a⁻¹ * a')))
      have h0 := zero_le_one.trans (one_le_logNorm (F := F) d.G
        (ζ * ((d.hypPart (a⁻¹ * a'))⁻¹ * (a⁻¹ * a'))))
      by_contra hneg
      push Not at hneg
      have : Cd * d.logNormSO (d.Pbar ((d.hypPart (a⁻¹ * a'))⁻¹ * (a⁻¹ * a'))) < 0 :=
        mul_neg_of_neg_of_pos hneg (by linarith)
      linarith
    · rw [← mul_assoc, ← (Subgroup.mem_center_iff.1 (d.AG_le_center hzA) a), mul_assoc]
      group
  obtain ⟨M, hM⟩ := exists_finset_cover_of_intCoord (d.frameCoord e₁ f₁ e₂ f₂)
    (inv_pos.2 (zero_lt_one.trans_le hc)) hv hE
  exact ⟨CS, isCompact_logNorm_le d.isClosed_G _, M, _, hM⟩

/-- **BP (6.7.12) modulo `A_G`, in the form of `WeakCartanData.growth`**: for two hyperbolic
frames of `V` and any `π : G(F) → X` invariant under left multiplication by `A_G(F)` (e.g.
`G(F) → H(F)\G(F)/A_G(F)`), there are a compact `C_S` and `M`, `N` such that for every
`S ⊆ A_G(F) · frameTorus` and `R ≥ 1` the image under `π` of `{s ∈ S ; σ_{A_G\G}(s) < R}` is
covered by `≤ M (1 + R)^N` sets `π(j C_S)`. -/
theorem exists_growth_frameTorus (hF₁ : IsHypFrame d.QV W₁ e₁ f₁)
    (hF₂ : IsHypFrame d.QV W₂ e₂ f₂) {X : Type*} (π : d.G → X)
    (hπ : ∀ z ∈ d.AG, ∀ g, π (z * g) = π g) :
    ∃ CS : Set d.G, IsCompact CS ∧ ∃ (M : ℝ) (N : ℕ),
      ∀ S ⊆ (d.AG : Set d.G) * (d.frameTorus W₁ W₂ e₁ f₁ e₂ f₂ : Set d.G),
      ∀ R : ℝ, 1 ≤ R → ∃ t : Finset d.G, (t.card : ℝ) ≤ M * (1 + R) ^ N ∧
        π '' {s ∈ S | infLeft (logNorm F d.G) d.AG s < R} ⊆ ⋃ j ∈ t, π '' ((j * ·) '' CS) := by
  obtain ⟨CS, hCS, M, N, h⟩ := d.exists_cover_frameTorus hF₁ hF₂
  refine ⟨CS, hCS, M, N, fun S hS R hR => ?_⟩
  obtain ⟨t, -, ht, hcov⟩ := h R hR
  refine ⟨t, ht, ?_⟩
  rintro _ ⟨s, ⟨hs, hsR⟩, rfl⟩
  obtain ⟨z, hz, j, hj, e, he, rfl⟩ := hcov s (d.AG_mul_frameTorus_subset (hS hs)) hsR
  exact mem_iUnion₂.2 ⟨j, hj, ⟨j * e, ⟨e, he, rfl⟩, (hπ z hz _).symm⟩⟩

end GGPData

end GSpinGGP
