/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LuoClass
import GSpinGGP.TraceFormula.Interface

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

* `exists_isLieDescentNbhd` (SORRY): such neighbourhoods exist inside every `ω₀^{G(F)}`
  (Waldspurger 2010 §3.1 for `𝔤 = 𝔷 ⊕ 𝔤⁰`, BP §3.3);
* `kernelK_eq_kernelLie_liftLie` (SORRY): the kernels agree, `K(f, x) = K^Lie(f_ω, x)` for every
  `x ∈ G(F)` (BP (3.3.2) on `H`, Thesis Prop 12.4.1(i)); hence `J(f) = J^Lie(f_ω)`
  (`distribJ_eq_distribJLie_liftLie`, proved);
* `isLieScusp_liftLie` (SORRY): `f_ω ∈ S_scusp(𝔤⁰(F))` (Thesis §12.4);
* `torusIntegral_eq_torusIntegralLie_liftLie` (SORRY): torus by torus, for every `s > 0`,
  `∫_{T(F)/A_{G,H}(F)} D^G(t)^{1/2} c_{θ_f,O_t}(t) Δ(t)^{s−1/2} dt =
  ∫_{𝔱⁰(F)} D^G(X)^{1/2} c_{θ_F,O_X}(X) Δ(X)^{s−1/2} dX` (Thesis (12.1.14), torus by torus,
  with `j_G^H = 1`); hence `m_{geom,s}(θ_f) = m^Lie_{geom,s}(θ_F)` for every `s > 0` and
  `m_geom(θ_f) = m^Lie_geom(θ_F)` (`mGeom_eq_mGeomLie_liftLie`, proved: no convergence is needed,
  the two functions of `s` agree on `s > 0`).

Each of the four is stated in the form "there is a neighbourhood `ω₀` of `0` such that the claim
holds for every descent neighbourhood `ω ⊆ ω₀^{G(F)}`", so that the smallness conditions of the
slices can be intersected.

Also proved here: the existence of `θ_F` for every `F ∈ S_scusp(𝔤⁰(F))` (`exists_isThetaFLie`),
from Luo Thm 7.3.3 for the special orthogonal triple (the axiom `luo_lie_geomExpansion_SO`,
transported to `𝔤⁰` by `isThetaFLie_of_SO`).
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

/-- **A descent neighbourhood of `0` in `𝔤⁰(F)`** (Thesis §12.4, BP §3.3, Waldspurger 2010 §3.1):
`ω ⊆ 𝔤⁰(F)` open and closed, containing `0`, invariant under `G(F)`, compact modulo conjugation;
`exp` is a homeomorphism of `ω` onto `Ω₀ ⊆ G(F)`; two elements of `Ω₀` that differ by an element of
`A_G(F)` are equal; and `Ω = A_G(F)·Ω₀` is open, closed, invariant and `A_G(F)`-stable.  This is the
thesis's `G(F)`-excellent neighbourhood `ω` with `Ω = A_G(F)·exp(ω)`, written for `𝔤⁰` (Thesis
§12.4 uses `𝔤 = Lie(A_G) ⊕ 𝔤⁰`). -/
structure IsLieDescentNbhd (ω : Set ↥d.lieZero) (Ω₀ : Set ↥d.G) : Prop where
  isOpen : IsOpen ω
  isClosed : IsClosed ω
  zero_mem : (0 : ↥d.lieZero) ∈ ω
  adLie0_mem : ∀ (g : ↥d.G) (X : ↥d.lieZero), X ∈ ω → d.adLie0 g X ∈ ω
  compact_mod_conj : ∃ Γ : Set ↥d.lieZero, IsCompact Γ ∧
    ∀ X ∈ ω, ∃ g : ↥d.G, ∃ Y ∈ Γ, X = d.adLie0 g Y
  exp_homeo : ∃ e : ↥ω ≃ₜ ↥Ω₀, ∀ X : ↥ω,
    ((((e X : ↥Ω₀) : ↥d.G) : d.ambientˣ) : d.ambient) = expA F ((X : ↥d.lieZero) : d.ambient)
  eq_of_mul_AG : ∀ g ∈ Ω₀, ∀ g' ∈ Ω₀, ∀ a ∈ d.AG, g = a * g' → g = g'
  isInvariantClopen : IsInvariantClopen d ((d.AG : Set ↥d.G) * Ω₀)

/-- Every element of `ω` is `G(F)`-conjugate into `ω₀` (`ω ⊆ ω₀^{G(F)}`, Waldspurger 2010 §3.1). -/
def IsConjSmall (ω₀ : Set d.ambient) (ω : Set ↥d.lieZero) : Prop :=
  ∀ X ∈ ω, ∃ g : ↥d.G, ∃ Y ∈ ω₀,
    ((X : ↥d.lieZero) : d.ambient) = ((g : d.ambientˣ) : d.ambient) * Y * ((g⁻¹ : d.ambientˣ) : d.ambient)

theorem IsConjSmall.mono {ω₀ ω₁ : Set d.ambient} {ω : Set ↥d.lieZero} (h : d.IsConjSmall ω₀ ω)
    (h01 : ω₀ ⊆ ω₁) : d.IsConjSmall ω₁ ω := fun X hX => by
  obtain ⟨g, Y, hY, e⟩ := h X hX
  exact ⟨g, Y, h01 hY, e⟩

theorem IsConjSmall.of_inter_left {ω₀ ω₁ : Set d.ambient} {ω : Set ↥d.lieZero}
    (h : d.IsConjSmall (ω₀ ∩ ω₁) ω) : d.IsConjSmall ω₀ ω := h.mono _ Set.inter_subset_left

theorem IsConjSmall.of_inter_right {ω₀ ω₁ : Set d.ambient} {ω : Set ↥d.lieZero}
    (h : d.IsConjSmall (ω₀ ∩ ω₁) ω) : d.IsConjSmall ω₁ ω := h.mono _ Set.inter_subset_right

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

/-- `1 = e^0 ∈ Ω = A_G(F)·Ω₀`. -/
theorem IsLieDescentNbhd.one_mem {ω : Set ↥d.lieZero} {Ω₀ : Set ↥d.G}
    (h : d.IsLieDescentNbhd ω Ω₀) : (1 : ↥d.G) ∈ (d.AG : Set ↥d.G) * Ω₀ := by
  obtain ⟨e, he⟩ := h.exp_homeo
  have h0 := he ⟨0, h.zero_mem⟩
  rw [show (((⟨0, h.zero_mem⟩ : ↥ω) : ↥d.lieZero) : d.ambient) = 0 from rfl,
    expA_zero_eq_one] at h0
  have h1 : ((e ⟨0, h.zero_mem⟩ : ↥Ω₀) : ↥d.G) = 1 := Subtype.ext (Units.ext h0)
  exact ⟨1, d.AG.one_mem, _, h1 ▸ (e ⟨0, h.zero_mem⟩).2, one_mul _⟩

/-! ## 2. The slices (Thesis Prop 12.4.1(i), Prop 12.1.1(iv)) -/

/-- **Descent neighbourhoods exist inside every `ω₀^{G(F)}`** (Waldspurger 2010 §3.1 at `x = 1`,
applied to `𝔤 = 𝔷 ⊕ 𝔤⁰`; BP §3.3), when neither `W` nor `V` is a hyperbolic plane (so `A_G(F)` is
the group of pairs of scalars and `Lie(A_G) = 𝔷`).

Proof sketch (not formalized): take a good neighbourhood `ω'` of `0` in `𝔤(F)` inside a small
`ω₀'^{G(F)}` (`waldspurger_goodNbhd_one`) and `ω = ω' ∩ 𝔤⁰(F)`, `Ω₀ = exp(ω)`.  Since `𝔷` is
central, `e^{Z + X} = e^Z e^X` with `e^Z ∈ A_G(F)` for small `Z ∈ 𝔷`, so `A_G(F)·Ω₀ = A_G(F)·exp(ω')`
when `ω₀'` is a product of small balls of `𝔷` and `𝔤⁰`; that set is open, closed, invariant and
`A_G(F)`-stable (`isInvariantClopen_AG_mul` applied to `exp(ω')`).  If `e^X = a e^{X'}` with
`X, X' ∈ ω`, `a ∈ A_G(F)`, then `a` is close to `1` (the eigenvalues of `e^X`, `e^{X'}` are), so
`a = e^z` with `z ∈ 𝔷` small, and `X = X' + z` by injectivity of `exp` on elements with small
eigenvalues; `X − X'` has trace `0` in each factor, so `z = 0`. -/
theorem exists_isLieDescentNbhd (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    {ω₀ : Set d.ambient} (hω₀ : ω₀ ∈ 𝓝 (0 : d.ambient)) :
    ∃ (ω : Set ↥d.lieZero) (Ω₀ : Set ↥d.G), d.IsLieDescentNbhd ω Ω₀ ∧ d.IsConjSmall ω₀ ω := by
  sorry

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

Proof sketch (not formalized): `f_ω` is locally constant (`f` is, `exp : ω → Ω₀` is a homeomorphism,
`ω` is open and closed) and compactly supported (`f` is compactly supported modulo `A_G(F)` and
`exp` is injective modulo `A_G(F)` on `ω`).  For a proper parabolic `P = MU` and `X ∈ 𝔭⁰(F)`,
reduce to `X ∈ 𝔪(F) ∩ ω`; then `N ↦ e^{−X} e^{X + N}` is a measure-preserving bijection of
`𝔲(F)` onto `U(F)` (Waldspurger 2010 §8.2), so `∫_{𝔲(F)} f_ω(X + N) dN = ∫_{U(F)} f(e^X u) du = 0`. -/
theorem isLieScusp_liftLie (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    (χ : CentralCharOn d) :
    ∃ ω₀ ∈ 𝓝 (0 : d.ambient), ∀ (ω : Set ↥d.lieZero) (Ω₀ : Set ↥d.G),
      d.IsLieDescentNbhd ω Ω₀ → d.IsConjSmall ω₀ ω →
      ∀ f ∈ ScuspTestFn d χ, Function.support f ⊆ (d.AG : Set ↥d.G) * Ω₀ →
        d.IsLieScusp (d.liftLie ω f) := by
  sorry

/-- **(12.1.14) torus by torus** (Thesis Prop 12.1.1(iv), with `j_G^H = 1` on a small `ω`): for a
small descent neighbourhood `ω`, `f ∈ 𝒞_scusp` supported in `Ω = A_G(F)·Ω₀`, every torus class
`c` and every `s > 0`,
`∫_{T(F)/A_{G,H}(F)} D^G(t)^{1/2} c_{θ_f,O_t}(t) Δ(t)^{s−1/2} dt
  = ∫_{𝔱⁰(F)} D^G(X)^{1/2} c_{θ_F,O_X}(X) Δ(X)^{s−1/2} dX` with `F = f_ω`.

Proof sketch (not formalized): `θ_f` vanishes off `Ω` and `θ_F` off `ω` on the regular sets, so both
integrands vanish off `exp(ω ∩ 𝔱⁰(F))` resp. `ω ∩ 𝔱⁰(F)` (`germ_unique`); `θ_F = θ_f ∘ exp` on
`ω ∩ 𝔤⁰_reg(F)` (both represent the orbital pairing of `f_ω`, the Haar measure of `G(F)` being
`da·dX` on `A_G(F)·exp(ω)`; `isThetaFLie_eqOn_regular`); for `t = e^X`, `X ∈ ω ∩ 𝔱⁰_♮(F)`:
`D^G(e^X) = D^G(X)`, `Δ(e^X) = Δ(X)`, the fixed space of `e^X` is `ker X`, `G_{e^X} = G_X`,
`𝔤_{e^X} = 𝔷 ⊕ 𝔤⁰_X`, and `c_{θ_f,O}(e^X) = c_{θ_F,O}(X)` (BP Prop 4.5.1.1(iv)); finally `exp`
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

/-- **`θ_F` exists on `𝔤⁰`**: every `F ∈ S_scusp(𝔤⁰(F))` has a function `θ_F` representing its
orbital pairing (`IsThetaFLie`), when neither `W` nor `V` is a hyperbolic plane.  From Luo
Thm 7.3.3 for the special orthogonal triple (`luo_lie_geomExpansion_SO`, which provides `θ_F` for
`SO(W) × SO(V)`), transported to `𝔤⁰` (`isThetaFLie_of_SO`); BP §5.5–5.6, Lie-algebra case. -/
theorem exists_isThetaFLie (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    {f : ↥d.lieZero → ℂ} (hf : d.IsLieScusp f) : ∃ θ, d.IsThetaFLie ψ f θ := by
  have := d.muG_isHaarMeasure hW hV
  obtain ⟨μH, μ𝔥, m, hμH, h𝔥, hm, -⟩ := d.exists_JLie_transfer ψ hW hV
  obtain ⟨e, hen, -⟩ := d.gammaClass_equiv hW hV
  obtain ⟨μT, hμT, -⟩ := d.torusIntegralLie_toSO ψ hW hV e hen
  obtain ⟨θ, ⟨h1, h2, h3⟩, -, -⟩ :=
    luo_lie_geomExpansion_SO d.luoOf hW hV ψ d.muG μH μ𝔥 h𝔥 m hm μT hμT
      (f ∘ d.toSO.symm) (d.isScusp_toSO hf)
  exact ⟨_, d.isThetaFLie_of_SO ψ hW hV hf h1 h2 h3⟩

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
