/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.DescentNbhd

/-!
# Descent from `G` to `𝔤⁰` near `1`: the slices of Thesis Prop 12.4.1(i) and Prop 12.1.1(iv)

`exists_lie_descent` (`TraceFormula/Lie.lean`) says: for triples without a hyperbolic-plane factor
there is an open, closed, invariant, `A_G(F)`-stable `Ω ∋ 1` such that every `f ∈ 𝒞_scusp`
supported in `Ω` has a strongly cuspidal `F` on `𝔤⁰(F)` with `J(f) = J^Lie(F)` and
`m_geom(θ_f) = m^Lie_geom(θ_F)`.  This file fixes the construction of the thesis
(Thesis §12.4, BP §3.3, §11.7): `Ω = A_G(F)·exp(ω)` for a `G(F)`-excellent neighbourhood `ω` of `0`
in `𝔤⁰(F)`, and `F = f_ω`, `f_ω(X) = f(e^X)` on `ω` and `0` off `ω` (`liftLie`).  (In the `p`-adic
case `j_G^H = 1` on a small enough `ω`, so `(j_G^H)^{1/2} f_ω = f_ω`.)  It then proves
`exists_lie_descent` (as `exists_lie_descent_of_slices`) from four separate statements:

* `exists_isLieDescentNbhd` (proved, `TraceFormula/DescentNbhd.lean`, where `IsLieDescentNbhd` and
  `IsConjSmall` are defined): such neighbourhoods exist inside every `ω₀^{G(F)}` (Waldspurger 2010 §3.1 for `𝔤 = 𝔷 ⊕ 𝔤⁰`, BP §3.3);
* `kernelK_eq_kernelLie_liftLie` (SORRY): the kernels agree, `K(f, x) = K^Lie(f_ω, x)` for every
  `x ∈ G(F)` (BP (3.3.2) on `H`, Thesis Prop 12.4.1(i)); hence `J(f) = J^Lie(f_ω)`
  (`distribJ_eq_distribJLie_liftLie`, proved);
* `isLieScusp_liftLie` (SORRY): `f_ω ∈ S_scusp(𝔤⁰(F))` (Thesis §12.4);
* `torusIntegral_eq_torusIntegralLie_liftLie` (SORRY): torus by torus, for every `s > 0`,
  `∫_{T(F)/A_{G,H}(F)} D^G(t)^{1/2} c_{θ_f,O_t}(t) Δ(t)^{s−1/2} dt =
  ∫_{𝔱⁰(F)} D^G(X)^{1/2} c_{θ_F,O_X}(X) Δ(X)^{s−1/2} dX` (Thesis (12.1.10), torus by torus,
  with `j_G^H = 1`); hence `m_{geom,s}(θ_f) = m^Lie_{geom,s}(θ_F)` for every `s > 0` and
  `m_geom(θ_f) = m^Lie_geom(θ_F)` (`mGeom_eq_mGeomLie_of_torusIntegral`, proved: no convergence is needed,
  the two functions of `s` agree on `s > 0`).

Each of the four is stated in the form "there is a neighbourhood `ω₀` of `0` such that the claim
holds for every descent neighbourhood `ω ⊆ ω₀^{G(F)}`", so that the smallness conditions of the
slices can be intersected.

The existence of `θ_F` for every `F ∈ S_scusp(𝔤⁰(F))`, needed by the last slice, is
`exists_isThetaFLie` (`TraceFormula/LuoClass.lean`, from Luo Thm 7.3.3).
-/

noncomputable section

open MeasureTheory Topology Filter

open scoped Pointwise

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

/-! ## 1. Descent neighbourhoods and the lift `f ↦ f_ω` -/

open Classical in
/-- **`f_ω`** (Thesis §12.4): `f_ω(X) = f(e^X)` for `X ∈ ω` (when `e^X ∈ G(F)`), `0` otherwise. -/
def liftLie (ω : Set ↥d.lieZero) (f : ↥d.G → ℂ) (X : ↥d.lieZero) : ℂ :=
  if h : X ∈ ω ∧ ∃ g : ↥d.G, ((g : d.ambientˣ) : d.ambient) = expA F ((X : ↥d.lieZero) : d.ambient)
  then f h.2.choose else 0

theorem liftLie_eq {ω : Set ↥d.lieZero} (f : ↥d.G → ℂ) {X : ↥d.lieZero} (hX : X ∈ ω) {g : ↥d.G}
    (hg : ((g : d.ambientˣ) : d.ambient) = expA F ((X : ↥d.lieZero) : d.ambient)) :
    d.liftLie ω f X = f g := by
  classical
  have h : X ∈ ω ∧ ∃ g : ↥d.G, ((g : d.ambientˣ) : d.ambient) =
      expA F ((X : ↥d.lieZero) : d.ambient) := ⟨hX, g, hg⟩
  unfold liftLie
  rw [dite_eq_left_of_eq_true (eq_true h)]
  congr 1
  exact Subtype.ext (Units.ext (h.2.choose_spec.trans hg.symm))

theorem liftLie_of_notMem {ω : Set ↥d.lieZero} (f : ↥d.G → ℂ) {X : ↥d.lieZero} (hX : X ∉ ω) :
    d.liftLie ω f X = 0 := by
  classical
  unfold liftLie
  rw [dite_eq_right_of_eq_false (eq_false (fun h => hX h.1))]

/-! ## 1b. `f_ω` is a test function -/

/-- `liftLie ω f` is locally constant when `ω` is a descent neighbourhood and `f` is locally
constant: on the clopen `ω` it is `f ∘ exp`, off `ω` it is `0`. -/
theorem IsLieDescentNbhd.isLocallyConstant_liftLie {ω : Set ↥d.lieZero} {Ω₀ : Set ↥d.G}
    (hω : d.IsLieDescentNbhd ω Ω₀) {f : ↥d.G → ℂ} (hf : IsLocallyConstant f) :
    IsLocallyConstant (d.liftLie ω f) := by
  obtain ⟨e, he⟩ := hω.exp_homeo
  set φ : ↥ω → ℂ := fun X => f ((e X : ↥Ω₀) : ↥d.G) with hφ
  have hφc : IsLocallyConstant φ :=
    hf.comp_continuous (continuous_subtypeVal.comp e.continuous)
  have hlift : ∀ X : ↥ω, d.liftLie ω f X = φ X := fun X => d.liftLie_eq f X.2 (he X)
  rw [IsLocallyConstant.iff_exists_open]
  intro X
  by_cases hX : X ∈ ω
  · refine ⟨Subtype.val '' {v : ↥ω | φ v = φ ⟨X, hX⟩},
      hω.isOpen.isOpenMap_subtypeVal _ (hφc.isOpen_fiber _), ⟨⟨X, hX⟩, rfl, rfl⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [hlift v, hlift ⟨X, hX⟩]
    exact hv
  · refine ⟨ωᶜ, hω.isClosed.isOpen_compl, hX, fun X' hX' => ?_⟩
    rw [d.liftLie_of_notMem f hX', d.liftLie_of_notMem f hX]

/-- **`f_ω` is a test function** (locally constant and compactly supported) for `f` locally
constant and compactly supported modulo `A_G(F)`, when `ω` is a descent neighbourhood inside
`ω₀^{G(F)}` for a small `ω₀`.  Choose `ω₀` inside a neighbourhood `O` with `O ∩ 𝔤 ⊆ ω₁` for a good
neighbourhood `ω₁` (`waldspurger_goodNbhd_one`), so that `ω ⊆ ω₁` and `Ω₀ = exp(ω)` is closed in
`G(F)` (a closed subset of `ω₁` carried by the homeomorphism onto the closed `exp(ω₁)`), and with
`H_G(e^Y) = 0` for `Y ∈ ω₀`.  If `e^X = a c` with `X ∈ ω`, `a ∈ A_G(F)` and `c` in a compact `C`, then
`H_G(a) = −H_G(c)` takes finitely many values, so `a` lies in a compact set
(`isCompact_AG_inter_hcG_mem`) and `e^X` in a compact subset of the closed set `Ω₀`. -/
theorem exists_isTestFn_liftLie :
    ∃ ω₀ ∈ 𝓝 (0 : d.ambient), ∀ (ω : Set ↥d.lieZero) (Ω₀ : Set ↥d.G),
      d.IsLieDescentNbhd ω Ω₀ → d.IsConjSmall ω₀ ω →
        ∀ f : ↥d.G → ℂ, IsLocallyConstant f → HasCompactSupportModAG d f →
          IsTestFn (d.liftLie ω f) := by
  have := t2Space_of_moduleTopology F d.ambient
  obtain ⟨ω₁, Ω₁, -, h0ω₁, hω₁o, -, hω₁inv, -, -, hΩ₁c, -, ⟨e₁, he₁⟩, -⟩ :=
    waldspurger_goodNbhd_one d Filter.univ_mem
  obtain ⟨O, hO, hOω₁⟩ := d.exists_nhds_of_isOpen_lie hω₁o h0ω₁
  have hH := eventually_mem_of_eq_mul_expA d 1
    (d.isLocallyConstant_hcG.isOpen_fiber (d.hcG 1)) rfl
  refine ⟨O ∩ {Y | ∀ y : ↥d.G, ((y : d.ambientˣ) : d.ambient) =
      (((1 : ↥d.G) : d.ambientˣ) : d.ambient) * expA F Y → d.hcG y = d.hcG 1},
    inter_mem hO hH, fun ω Ω₀ hω hsmall f hf hfC =>
      ⟨IsLieDescentNbhd.isLocallyConstant_liftLie d hω hf, ?_⟩⟩
  obtain ⟨e, he⟩ := hω.exp_homeo
  have hval : ∀ (X : ↥ω) (g : ↥d.G), ((g : d.ambientˣ) : d.ambient) =
      expA F ((X : ↥d.lieZero) : d.ambient) → g = (e X : ↥d.G) :=
    fun X g hg => Subtype.ext (Units.ext (hg.trans (he X).symm))
  -- every element of `ω` is a conjugate `h Y h⁻¹` of some `Y ∈ ω₀ ∩ 𝔤⁰`
  have hconj : ∀ X : ↥ω, ∃ (h : ↥d.G) (Y : d.ambient), Y ∈ O ∧
      (∀ y : ↥d.G, ((y : d.ambientˣ) : d.ambient) =
        (((1 : ↥d.G) : d.ambientˣ) : d.ambient) * expA F Y → d.hcG y = d.hcG 1) ∧ Y ∈ d.lie ∧
      ((X : ↥d.lieZero) : d.ambient) =
        ((h : d.ambientˣ) : d.ambient) * Y * ((h⁻¹ : d.ambientˣ) : d.ambient) := by
    intro X
    obtain ⟨h, Y, ⟨hYO, hYH⟩, hXY⟩ := hsmall X X.2
    refine ⟨h, Y, hYO, hYH, ?_, hXY⟩
    have := d.conj_mem_lie0 h⁻¹ (d.mem_lieZero.1 (X : ↥d.lieZero).2)
    rw [hXY] at this
    exact d.lie0_le_lie (by simpa [mul_assoc] using this)
  -- `ω ⊆ ω₁`
  have hsub : ∀ X : ↥ω, ((X : ↥d.lieZero) : d.ambient) ∈ ω₁ := by
    intro X
    obtain ⟨h, Y, hYO, -, hYl, hXY⟩ := hconj X
    rw [hXY]; exact hω₁inv h _ (hOω₁ _ hYO hYl)
  -- `H_G(e^X) = 0` on `ω`
  have hH1 : ∀ X : ↥ω, d.hcG (e X : ↥d.G) = d.hcG 1 := by
    intro X
    obtain ⟨h, Y, -, hYH, -, hXY⟩ := hconj X
    have hy : (((h⁻¹ * (e X : ↥d.G) * h : ↥d.G) : d.ambientˣ) : d.ambient) =
        (((1 : ↥d.G) : d.ambientˣ) : d.ambient) * expA F Y := by
      simp only [Subgroup.coe_inv, Units.val_mul, OneMemClass.coe_one, Units.val_one,
        one_mul, Subgroup.coe_mul]
      rw [he X, hXY, expA_conj_G d h Y]
      simp [mul_assoc]
    have := hYH _ hy
    rwa [show h⁻¹ * (e X : ↥d.G) * h = h⁻¹ * (e X : ↥d.G) * h⁻¹⁻¹ by rw [inv_inv],
      d.hcG_conj] at this
  -- `Ω₀` is closed in `G(F)`
  have hΩ₀c : IsClosed Ω₀ := by
    set L : Set d.ambient := Subtype.val '' ω
    have hL : IsClosed L :=
      d.isClosed_lieZero.isClosedEmbedding_subtypeVal.isClosedMap ω hω.isClosed
    have heq : Ω₀ = Subtype.val '' (e₁ '' {Y : ↥ω₁ | (Y : d.ambient) ∈ L}) := by
      ext g
      constructor
      · intro hg
        set X := e.symm ⟨g, hg⟩
        refine ⟨e₁ ⟨_, hsub X⟩, ⟨⟨_, hsub X⟩, ⟨(X : ↥d.lieZero), X.2, rfl⟩, rfl⟩, ?_⟩
        have h1 := hval X (e₁ ⟨_, hsub X⟩) (he₁ _)
        rw [h1]; simp [X]
      · rintro ⟨_, ⟨Y, ⟨X, hX, hXY⟩, rfl⟩, rfl⟩
        have h1 := hval ⟨X, hX⟩ (e₁ Y) (by rw [he₁, ← hXY])
        rw [h1]; exact (e ⟨X, hX⟩).2
    rw [heq]
    exact hΩ₁c.isClosedEmbedding_subtypeVal.isClosedMap _
      (e₁.isClosed_image.2 (hL.preimage continuous_subtypeVal))
  -- the compact set
  obtain ⟨C, hC, hfC⟩ := hfC
  set R : Set HCVal := (fun s => s⁻¹) '' (d.hcG '' C)
  have hKA := d.isCompact_AG_inter_hcG_mem ((d.finite_image_hcG hC).image _ : R.Finite)
  have hKC : IsCompact (((d.AG : Set ↥d.G) ∩ {g | d.hcG g ∈ R}) * C) := hKA.mul hC
  have hKω : IsCompact (e ⁻¹' {g : ↥Ω₀ | (g : ↥d.G) ∈
      ((d.AG : Set ↥d.G) ∩ {g | d.hcG g ∈ R}) * C}) :=
    e.isCompact_preimage.2 (hΩ₀c.isClosedEmbedding_subtypeVal.isCompact_preimage hKC)
  refine HasCompactSupport.intro (hKω.image continuous_subtypeVal) fun X hX => ?_
  by_contra hne
  by_cases hXω : X ∈ ω
  · rw [d.liftLie_eq f hXω (he ⟨X, hXω⟩)] at hne
    obtain ⟨a, ha, c, hc, hac⟩ := hfC (Function.mem_support.2 hne)
    refine hX ⟨⟨X, hXω⟩, ?_, rfl⟩
    refine ⟨a, ⟨ha, (d.hcG c), ⟨c, hc, rfl⟩, ?_⟩, c, hc, hac⟩
    have h1 := hH1 ⟨X, hXω⟩
    rw [← hac, map_mul, map_one] at h1
    exact (eq_inv_of_mul_eq_one_left h1).symm
  · exact hne (d.liftLie_of_notMem f hXω)

/-! ## 2. The slices (Thesis Prop 12.4.1(i), Prop 12.1.1(iv)) -/

variable (ψ : NontrivialAddChar F)

/-- **The kernels agree near `1`** (Thesis Prop 12.4.1(i), BP (3.3.2) on `H`): for a small descent
neighbourhood `ω` and `f ∈ 𝒞_scusp` supported in `Ω = A_G(F)·Ω₀`,
`K(f, x) = ∫_{H(F)/A_{G,H}(F)} f(x⁻¹hx) ξ(h) dh = ∫_{𝔥⁰(F)} f_ω(x⁻¹Xx) ξ(X) dX = K^Lie(f_ω, x)`
for every `x ∈ G(F)`.

Proof sketch (not formalized): `x⁻¹hx ∈ Ω` iff `h ∈ Ω`, and `H(F) ∩ A_G(F)·exp(ω) =
A_{G,H}(F)·exp(ω ∩ 𝔥⁰(F))` (if `h = a e^X ∈ H(F)` then `e^{p^k X} ∈ A_G(F) H(F)` with `p^k X → 0`,
so `p^k X ∈ 𝔥⁰ + 𝔷` by the logarithm near `1`, `eventually_exists_sub_algebraMap_mem_lieH0`,
and `X ∈ 𝔥⁰` as `X ∈ 𝔤⁰`; `A_G ∩ H = A_{G,H}` without hyperbolic planes);
`f(x⁻¹ a e^X x) = f_ω(x⁻¹Xx)` for `a ∈ A_{G,H}(F)` (`χ` is trivial there); `ξ(e^X) = ψ(λ(X))`;
and `exp` carries `dX` on `ω ∩ 𝔥⁰(F)` to `dh` on its image in `H(F)/A_{G,H}(F)`
(`measH0_eq_haar_image_of_conj_small`). -/
theorem kernelK_eq_kernelLie_liftLie (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    (χ : CentralCharOn d) :
    ∃ ω₀ ∈ 𝓝 (0 : d.ambient), ∀ (ω : Set ↥d.lieZero) (Ω₀ : Set ↥d.G),
      d.IsLieDescentNbhd ω Ω₀ → d.IsConjSmall ω₀ ω →
      ∀ f ∈ ScuspTestFn d χ, Function.support f ⊆ (d.AG : Set ↥d.G) * Ω₀ →
        ∀ x : ↥d.G, kernelK d ψ f x = d.kernelLie ψ (d.liftLie ω f) x := by
  sorry

/-- **`f_ω` is strongly cuspidal** (Thesis §12.4, BP §3.3, §11.7): for a small descent
neighbourhood `ω` and `f ∈ 𝒞_scusp` supported in `Ω = A_G(F)·Ω₀`, `f_ω ∈ S_scusp(𝔤⁰(F))`.

Proof sketch (partly formalized): `f_ω` is a test function (`exists_isTestFn_liftLie`, proved).
For a proper parabolic `P = MU` and `X ∈ 𝔭⁰(F)`,
reduce to `X ∈ 𝔪(F) ∩ ω`; then `N ↦ e^{−X} e^{X + N}` is a measure-preserving bijection of
`𝔲(F)` onto `U(F)` (Waldspurger 2010 §8.2), so `∫_{𝔲(F)} f_ω(X + N) dN = ∫_{U(F)} f(e^X u) du = 0`. -/
theorem isLieScusp_liftLie (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    (χ : CentralCharOn d) :
    ∃ ω₀ ∈ 𝓝 (0 : d.ambient), ∀ (ω : Set ↥d.lieZero) (Ω₀ : Set ↥d.G),
      d.IsLieDescentNbhd ω Ω₀ → d.IsConjSmall ω₀ ω →
      ∀ f ∈ ScuspTestFn d χ, Function.support f ⊆ (d.AG : Set ↥d.G) * Ω₀ →
        d.IsLieScusp (d.liftLie ω f) := by
  sorry

/-- **(12.1.10) torus by torus** (Thesis Prop 12.1.1(iv), with `j_G^H = 1` on a small `ω`): for a
small descent neighbourhood `ω`, `f ∈ 𝒞_scusp` supported in `Ω = A_G(F)·Ω₀`, every torus class
`c` and every `s > 0`,
`∫_{T(F)/A_{G,H}(F)} D^G(t)^{1/2} c_{θ_f,O_t}(t) Δ(t)^{s−1/2} dt
  = ∫_{𝔱⁰(F)} D^G(X)^{1/2} c_{θ_F,O_X}(X) Δ(X)^{s−1/2} dX` with `F = f_ω`.

Proof sketch (not formalized): `θ_f` vanishes off `Ω` and `θ_F` off `ω` on the regular sets, so both
integrands vanish off `exp(ω ∩ 𝔱⁰(F))` resp. `ω ∩ 𝔱⁰(F)` (`germ_unique`); `θ_F = θ_f ∘ exp` on
`ω ∩ 𝔤⁰_reg(F)` (both represent the orbital pairing of `f_ω`, the Haar measure of `G(F)` being
`da·dX` on `A_G(F)·exp(ω)`; `isThetaFLie_eqOn_regular`); for `t = e^X`, `X ∈ ω ∩ 𝔱⁰_♮(F)`:
`D^G(e^X) = D^G(X)`, `Δ(e^X) = Δ(X)`, the fixed space of `e^X` is `ker X`, `G_{e^X} = G_X`,
`𝔤_{e^X} = 𝔷 ⊕ 𝔤⁰_X`, and `c_{θ_f,O}(e^X) = c_{θ_F,O}(X)` (from the definition of germs by local
expansions, BP §4.1, §4.5, and `θ_F = θ_f ∘ exp`: `θ_f(e^X e^Y) = θ_F(X + Y)` for `Y ∈ 𝔤⁰_X` small);
the orbits picked by `orbitChoice` at `e^X` and by `orbitChoiceLie` at `X` correspond (an obligation of
this slice: both are characterized by the same condition on `ker X`, unique by the results of `TraceFormula/OrbitSpecUnique.lean`);
finally `exp`
carries the measure of `𝔱⁰(F)` to the probability measure of `T(F)/A_{G,H}(F)` on
`ω ∩ 𝔱⁰(F)` (`IsExpCompatT`, extended from a neighbourhood of `0` to the subgroup of elements with
small eigenvalues, on which `exp` is a homomorphism). -/
theorem torusIntegral_eq_torusIntegralLie_liftLie (hW : ¬ IsHypPlane d.QW)
    (hV : ¬ IsHypPlane d.QV) (χ : CentralCharOn d) :
    ∃ ω₀ ∈ 𝓝 (0 : d.ambient), ∀ (ω : Set ↥d.lieZero) (Ω₀ : Set ↥d.G),
      d.IsLieDescentNbhd ω Ω₀ → d.IsConjSmall ω₀ ω →
      ∀ f ∈ ScuspTestFn d χ, Function.support f ⊆ (d.AG : Set ↥d.G) * Ω₀ →
        ∀ (c : GammaClass d) (s : ℝ), 0 < s →
          torusIntegral ψ d (thetaF d f) (Quot.out c).1 s =
            d.torusIntegralLie ψ (d.thetaFLie ψ (d.liftLie ω f)) (Quot.out c).1 s := by
  sorry

/-! ## 3. Consequences of the slices -/

/-- **`J(f) = J^Lie(f_ω)`** (Thesis Prop 12.4.1(i)), from the kernel identity. -/
theorem distribJ_eq_distribJLie_liftLie {f : ↥d.G → ℂ} {ω : Set ↥d.lieZero}
    (hK : ∀ x : ↥d.G, kernelK d ψ f x = d.kernelLie ψ (d.liftLie ω f) x) :
    distribJ d ψ f = d.distribJLie ψ (d.liftLie ω f) := by
  unfold distribJ distribJLie
  simp_rw [hK]

/-- **`m_geom(θ) = m^Lie_geom(θ')`** as soon as `m_{geom,s}(θ) = m^Lie_{geom,s}(θ')` torus by torus
for every `s > 0` (Thesis Prop 12.1.1(iv)): both are limits as `s → 0⁺` of the same function. -/
theorem mGeom_eq_mGeomLie_of_torusIntegral {θ : ↥d.G → ℂ} {θ' : ↥d.lieZero → ℂ}
    (h : ∀ (c : GammaClass d) (s : ℝ), 0 < s →
      torusIntegral ψ d θ (Quot.out c).1 s = d.torusIntegralLie ψ θ' (Quot.out c).1 s) :
    mGeom ψ d θ = d.mGeomLie ψ θ' := by
  have hev : mGeomS ψ d θ =ᶠ[𝓝[>] (0 : ℝ)] d.mGeomLieS ψ θ' := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    unfold mGeomS mGeomLieS
    congr 1
    funext c
    rw [h c s hs]
  unfold mGeom mGeomLie limUnder
  rw [Filter.map_congr hev]

/-- **Descent to the Lie algebra near `1`** (Thesis Prop 12.4.1(i), Prop 12.1.1(iv)), assembled from
the slices: `Ω = A_G(F)·exp(ω)` for a small descent neighbourhood `ω` and `F = f_ω`.  This is the
statement of `exists_lie_descent` (`TraceFormula/Lie.lean`). -/
theorem exists_lie_descent_of_slices (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    (χ : CentralCharOn d) :
    ∃ Ω : Set ↥d.G, IsInvariantClopen d Ω ∧ (1 : ↥d.G) ∈ Ω ∧
      ∀ f ∈ ScuspTestFn d χ, Function.support f ⊆ Ω →
        ∃ F : ↥d.lieZero → ℂ, d.IsLieScusp F ∧ distribJ d ψ f = d.distribJLie ψ F ∧
          mGeom ψ d (thetaF d f) = d.mGeomLie ψ (d.thetaFLie ψ F) := by
  obtain ⟨ω₁, hω₁, hK⟩ := d.kernelK_eq_kernelLie_liftLie ψ hW hV χ
  obtain ⟨ω₂, hω₂, hS⟩ := d.isLieScusp_liftLie hW hV χ
  obtain ⟨ω₃, hω₃, hT⟩ := d.torusIntegral_eq_torusIntegralLie_liftLie ψ hW hV χ
  obtain ⟨ω, Ω₀, hω, hsmall⟩ :=
    d.exists_isLieDescentNbhd hW hV (Filter.inter_mem hω₁ (Filter.inter_mem hω₂ hω₃))
  refine ⟨(d.AG : Set ↥d.G) * Ω₀, hω.isInvariantClopen, hω.one_mem, fun f hf hs => ?_⟩
  refine ⟨d.liftLie ω f, hS ω Ω₀ hω (hsmall.of_inter_right.of_inter_left) f hf hs,
    d.distribJ_eq_distribJLie_liftLie ψ (hK ω Ω₀ hω hsmall.of_inter_left f hf hs),
    d.mGeom_eq_mGeomLie_of_torusIntegral ψ
      (hT ω Ω₀ hω (hsmall.of_inter_right.of_inter_right) f hf hs)⟩

end GGPData

end GSpinGGP
