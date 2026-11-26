/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.RegularCentralizer
import GSpinGGP.TraceFormula.StronglyCuspidal

/-!
# `Γ(G)` with its measure, the kernel `K^A`, `J^A`, and the Weyl integration formula

Beuzart-Plessis, Astérisque 418, §1.7 (p. 32) and §5.5 (pp. 115–116), for `G = GSpin(W) × GSpin(V)`.

## `Γ(G)` and its measure (BP §1.7, p. 32)

`Γ(G)` is the set of semisimple conjugacy classes of `G(F)`.  For a set `𝒯(G)` of representatives
of the `G(F)`-conjugacy classes of maximal tori, BP equips `Γ(G)` with the measure
`∫_{Γ(G)} φ(x) dx = Σ_{T ∈ 𝒯(G)} |W(G,T)|⁻¹ ∫_{T(F)} φ(t) dt`.

* **Maximal tori** (`MaxTorus`): the subgroups `T(F) = G_x(F)` (`centG x`) for `x ∈ G_reg(F)`
  (`regularSet`).  Identification: for regular semisimple `x` the centralizer `Z_G(x)` is a maximal
  torus (`𝔤_x` abelian), connected by Steinberg's theorem (the derived group `Spin × Spin` is
  simply connected); conversely every maximal torus `T` is `Z_G(x)` for any regular `x ∈ T(F)`, and
  `T(F)` contains regular elements (`T(F)` is Zariski dense in `T`, `F` of characteristic `0`, and
  `T_reg` is open dense).  `centG_eq_of_mem_regularSet` checks that the torus does not depend on
  the regular element chosen in it.
* **Classes** (`MaxTorusClass`): `G(F)`-conjugacy classes, as `EllTorusClass`
  (`TraceFormula/Spectral.lean`) does for the elliptic ones (`EllTorus.toMaxTorus`).  The index
  set `GammaClass` of `Γ(G,H)` (`GGP/Triple.lean`) cannot be reused: it classifies the tori `T_x`
  of `GSpin(W)` attached to the GGP triple, not the maximal tori of `G`.
* **`|W(G,T)|`** is `weylCardG d T = |N_{G(F)}(T(F))/T(F)|`, BP's
  `W(G,T) = Norm_{G(F)}(T)/T(F)`.
* **The measure `dt` on `T(F)`.**  BP §1.6 (p. 30) gives `T(F)` the exp-lift of the autodual
  measure of `𝔱(F)` (the `dt` of §1.7, not `d_c t`; `ν(T)` only enters the measure of
  `Γ_ani(G)`).  That measure is not formalized, so `gammaIntegral` takes a family of measures
  `μ T` on the tori as an argument.  Every statement here pairs the `T`-integral with the orbital
  integrals `J_G(t, ·)` for the quotient measure `dg / μ T` on `T(F)\G(F)`: replacing `μ T` by
  `c • μ T` multiplies the `T`-integral by `c` and `J_G` by `c⁻¹` (as in
  `weightedOrbitalIntegral_smul_measure`), so these statements do not depend on the choice, and
  BP's `dt` is one admissible choice.
* The sum is a `tsum`: there are finitely many classes of maximal tori for `p`-adic `F` (not
  proved here), and a `tsum` over a finite type is the finite sum.

## The kernel `K^A` and `J^A` (BP §5.5, pp. 115–116)

`K^A_{f,f'}(g₁, g₂) = ∫_{G(F)} f(g₁⁻¹ g g₂) f'(g) dg` (`kernelA`) and
`J^A(f, f') = ∫_{A_G(F)\G(F)} K^A_{f,f'}(x, x) dx` (`jA`).  `A_G` is central, so `A_G(F)\G(F)`
is the quotient group `G(F)/A_G(F)` (`GmodAG`), with the measure `measGmodAG = dg / d_c a`
(`d_c a` gives the maximal compact subgroup of `A_G(F)` mass `1`): BP §1.6's general rule would
give `A_G(F)` the exp-lifted measure; we use `d_c a`, the convention of Arthur, Publ. IHÉS 73
(1991), §1, p. 11, and Waldspurger, J. reine angew. Math. 465 (1995), §1.4, p. 45.  It is the one
Haar measure on `A_G(F)` for
which BP Thm 5.5.1(iv) can hold: `J^A` scales as `1/da_G`, and the right side of (iv) has no `A_G`
parameter (`θ_f` carries `ν(G_x)⁻¹`, i.e. `d_c t`).  Tested at the toy datum with BP's `θ_f`
(`toyD_jA_geom`, `Sanity/GammaGAudit.lean`).
`J^A` is the orbital pairing already used for `θ_f`: `jA_eq_orbitalPairing` (`rfl`).

**Integrability.**  BP Thm 5.5.1(ii) (printed without proof; BP defers it to its reference [18])
makes `x ↦ K^A(x, x)` integrable for strongly cuspidal `f`.  `jA` is the Lean integral, which is
`0` when the integrand is not integrable.  For `f ∈ C_c^∞(G(F))` strongly cuspidal and
`f' ∈ C_c^∞(G(F))`, integrability is the existing literature axiom `bp_integrable_kernel_scusp`
(`integrable_kernelA_diag_scusp`).

## The Weyl integration formula (BP §1.7, p. 32)

`∫_{G(F)} f(g) dg = ∫_{Γ(G)} D^G(x)^{1/2} J_G(x, f) dx` for `f ∈ C_c^∞(G(F))`, with
`J_G(x, f) = D^G(x)^{1/2} ∫_{G_x(F)\G(F)} f(g⁻¹ x g) dg` (BP §1.8).
The right side does not depend on the Haar measures chosen on the tori
(`gammaIntegral_weylIntegrand_eq`).  The formula itself is the literature axiom
`weyl_integration_exists` (`Literature/WeylIntegration.lean`; BP states it without proof), and
`weyl_integration` (`TraceFormula/WeylIntegration.lean`) gives it for every family of Haar
measures on the maximal tori.  At the commutative toy datum it is proved without the axiom
(`Sanity/GammaGAudit.lean`).

## Main definitions

* `GGPData.MaxTorus`, `GGPData.MaxTorusClass`, `GGPData.gammaIntegral`.
* `GGPData.weylIntegrand`: `t ↦ D^G(t)^{1/2} J_G(t, f)` on `T(F)`, `0` off `G_reg(F)`.
* `GGPData.kernelA`, `GGPData.jA`.

## Main statements

* `GGPData.gammaIntegral_weylIntegrand_eq`: `∫_{Γ(G)} D^{1/2} J_G(·, f)` does not depend on the
  Haar measures on the tori.
-/

noncomputable section

open MeasureTheory Topology

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- `|W(G,T)| = |N_G(T)(F)/T(F)|`, for any subgroup `T` of `G(F)` (used for all maximal tori in
`gammaIntegral`, and for the elliptic tori in `TraceFormula/Spectral.lean`). -/
def weylCardG (d : GGPData F) (T : Subgroup ↥d.G) : ℕ :=
  Nat.card (↥(Subgroup.normalizer (T : Set ↥d.G)) ⧸
    T.subgroupOf (Subgroup.normalizer (T : Set ↥d.G)))

namespace GGPData

variable (d : GGPData F)

/-! ## 2. Maximal tori and `Γ(G)` -/

/-- **The maximal tori of `G`**, as the subgroups `T(F) = G_x(F)` of `G(F)` for `x ∈ G_reg(F)`
(see the module docstring for the identification with BP's maximal tori). -/
def MaxTorus : Type _ :=
  {T : Subgroup ↥d.G // ∃ x ∈ regularSet d.G d.lie, T = d.centG x}

/-- `G(F)`-conjugacy of maximal tori. -/
def MaxTorus.Conj (T T' : d.MaxTorus) : Prop :=
  ∃ g : ↥d.G, T'.1 = T.1.map (MulAut.conj g).toMonoidHom

/-- **`𝒯(G)`**: the `G(F)`-conjugacy classes of maximal tori (BP §1.7, p. 32). -/
def MaxTorusClass : Type _ := Quot (MaxTorus.Conj d)

variable {d}

/-- **A maximal torus is commutative** (`commute_of_mem_centG`). -/
theorem MaxTorus.commute (T : d.MaxTorus) {g h : ↥d.G} (hg : g ∈ T.1) (hh : h ∈ T.1) :
    Commute g h := by
  obtain ⟨x, hx, hT⟩ := T.2
  rw [hT] at hg hh
  exact commute_of_mem_centG hx hg hh

theorem MaxTorus.isClosed (T : d.MaxTorus) : IsClosed (T.1 : Set ↥d.G) := by
  obtain ⟨x, -, hT⟩ := T.2
  rw [hT]
  exact d.isClosed_centG x

/-- **The torus does not depend on the regular element chosen in it**: for `x, t ∈ G_reg(F)` with
`t ∈ G_x(F)`, `G_t(F) = G_x(F)` (both are commutative, `commute_of_mem_centG`). -/
theorem centG_eq_of_mem_regularSet {x t : ↥d.G} (hx : x ∈ regularSet d.G d.lie)
    (ht : t ∈ regularSet d.G d.lie) (htx : t ∈ d.centG x) : d.centG t = d.centG x := by
  have hxt : x ∈ d.centG t :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 htx).symm
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · exact Subgroup.mem_centralizer_singleton_iff.2 (commute_of_mem_centG ht hg hxt).eq
  · exact Subgroup.mem_centralizer_singleton_iff.2 (commute_of_mem_centG hx hg htx).eq

/-- Every left Haar measure on a maximal torus is right invariant (`MaxTorus.commute`). -/
theorem MaxTorus.isMulRightInvariant (T : d.MaxTorus) (μ : Measure ↥T.1) [μ.IsMulLeftInvariant] :
    μ.IsMulRightInvariant :=
  isMulRightInvariant_of_forall_commute
    (fun a b => Subtype.ext (T.commute a.prop b.prop).eq) μ

/-- **`dg / μ` on `T(F)\G(F)` is the Weil measure** for a maximal torus `T` and any Haar measure `μ`
on `T(F)`. -/
theorem MaxTorus.quotMeasureOn_spec (T : d.MaxTorus) (μ : Measure ↥T.1) [μ.IsHaarMeasure] :
    IsWeilMeasure T.1.subtype Measure.haar μ (d.quotMeasureOn T.1 μ) := by
  have := T.isMulRightInvariant μ
  exact d.quotMeasureOn_spec T.1 T.isClosed μ

/-- `J_G(t, f)` is a function on `T(F)\G(F)`: for `t ∈ T(F)` the integrand `g ↦ f(g⁻¹ t g)` is left
`T(F)`-invariant (`T(F)` is commutative), so `orbitalIntegralOn` does not depend on the
representatives `CosetSpace.out`. -/
theorem MaxTorus.conj_mul_left (T : d.MaxTorus) {t c : ↥d.G} (ht : t ∈ T.1) (hc : c ∈ T.1)
    (f : ↥d.G → ℂ) (g : ↥d.G) : f ((c * g)⁻¹ * t * (c * g)) = f (g⁻¹ * t * g) := by
  have e : (c * g)⁻¹ * t * (c * g) = g⁻¹ * (c⁻¹ * t * c) * g := by group
  rw [e, (T.commute (T.1.inv_mem hc) ht).eq, mul_assoc t, inv_mul_cancel, mul_one]

variable (d)

/-- **The integral over `Γ(G)`** (BP §1.7, p. 32):
`∫_{Γ(G)} φ(x) dx = Σ_{T ∈ 𝒯(G)} |W(G,T)|⁻¹ ∫_{T(F)} φ_T(t) dμ_T(t)`,
summing over the classes `MaxTorusClass` with their chosen representatives, `|W(G,T)|` =
`weylCardG d T` = `|N_{G(F)}(T(F))/T(F)|`.  The measures `μ T` on the tori are an argument (BP's
`dt` is the exp-lift of the autodual measure on `𝔱(F)`, not formalized; see the module docstring),
and so is the dependence of the integrand on the torus (`φ T`): integrands such as
`D^{1/2} J_G(·, f)` involve the measure on `T(F)` through `J_G`.  For a class function, take
`φ` constant in `T`. -/
def gammaIntegral (μ : ∀ T : Subgroup ↥d.G, Measure ↥T) (φ : Subgroup ↥d.G → ↥d.G → ℂ) : ℂ :=
  ∑' c : d.MaxTorusClass, ((weylCardG d (Quot.out c).1 : ℂ))⁻¹ *
    ∫ t : ↥(Quot.out c).1, φ (Quot.out c).1 t ∂μ (Quot.out c).1

/-- `gammaIntegral` only sees the integrand on maximal tori. -/
theorem gammaIntegral_congr (μ : ∀ T : Subgroup ↥d.G, Measure ↥T)
    {φ ψ : Subgroup ↥d.G → ↥d.G → ℂ} (h : ∀ T : d.MaxTorus, ∀ t ∈ T.1, φ T.1 t = ψ T.1 t) :
    d.gammaIntegral μ φ = d.gammaIntegral μ ψ := by
  unfold gammaIntegral
  refine tsum_congr fun c => ?_
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => h _ t t.prop)

open scoped Classical in
/-- **The integrand of the Weyl integration formula** on `T(F)`:
`t ↦ D^G(t)^{1/2} J_G(t, f)`, with `J_G(t, f)` for `dg / μ T` on `T(F)\G(F)` (`orbitalIntegralOn`;
so the integrand is `D^G(t) ∫_{T(F)\G(F)} f(g⁻¹ t g) dg`), and `0` off `G_reg(F)` (BP defines
`J_G` on the regular set; the singular elements of `T(F)` form a null set). -/
def weylIntegrand (μ : ∀ T : Subgroup ↥d.G, Measure ↥T) (f : ↥d.G → ℂ) (T : Subgroup ↥d.G)
    (t : ↥d.G) : ℂ :=
  if t ∈ regularSet d.G d.lie then
    (Real.sqrt (weylDisc d.lie (t : d.ambientˣ)) : ℂ) * d.orbitalIntegralOn T (μ T) t f
  else 0

/-- **The Weyl integrand under rescaling of one torus measure**: if `μ' T = c • μ T`,
`0 < c < ∞`, on a maximal torus `T`, then `D^{1/2} J_G(t, f)` is divided by `c` on `T(F)`
(`orbitalIntegralOn_smul_measure`). -/
theorem weylIntegrand_of_eq_smul {μ μ' : ∀ T : Subgroup ↥d.G, Measure ↥T} (T : d.MaxTorus)
    [(μ T.1).IsHaarMeasure] {c : ENNReal} (hc0 : c ≠ 0) (hc : c ≠ ⊤) (h : μ' T.1 = c • μ T.1)
    (f : ↥d.G → ℂ) (t : ↥d.G) :
    d.weylIntegrand μ' f T.1 t = ((c⁻¹).toReal : ℂ) * d.weylIntegrand μ f T.1 t := by
  have := T.isMulRightInvariant (μ T.1)
  unfold weylIntegrand
  split_ifs
  · rw [h, d.orbitalIntegralOn_smul_measure T.1 T.isClosed (μ T.1) hc0 hc]
    ring
  · rw [mul_zero]

/-- **The right side of the Weyl integration formula does not depend on the Haar measures of the
tori**: for two families `μ`, `μ'` of Haar measures on the maximal tori,
`∫_{Γ(G)} D^{1/2} J_G(·, f)` is the same.  On each torus `μ' T = c μ T` with `0 < c < ∞`
(uniqueness of Haar measure); the `T`-integral is multiplied by `c` and `J_G` divided by `c`
(`weylIntegrand_of_eq_smul`).  No integrability or summability is needed: the terms of the sum
agree one by one. -/
theorem gammaIntegral_weylIntegrand_eq (μ μ' : ∀ T : Subgroup ↥d.G, Measure ↥T)
    (hμ : ∀ T : d.MaxTorus, (μ T.1).IsHaarMeasure) (hμ' : ∀ T : d.MaxTorus, (μ' T.1).IsHaarMeasure)
    (f : ↥d.G → ℂ) :
    d.gammaIntegral μ (d.weylIntegrand μ f) = d.gammaIntegral μ' (d.weylIntegrand μ' f) := by
  unfold gammaIntegral
  refine tsum_congr fun c => ?_
  congr 1
  set T : d.MaxTorus := Quot.out c
  have := hμ T
  have := hμ' T
  have : LocallyCompactSpace ↥T.1 := T.isClosed.locallyCompactSpace
  have : SecondCountableTopology ↥T.1 := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  set k := Measure.haarScalarFactor (μ' T.1) (μ T.1)
  have hk : μ' T.1 = (k : ENNReal) • μ T.1 := by
    rw [Measure.isMulLeftInvariant_eq_smul (μ' T.1) (μ T.1)]
    rfl
  have hk0 : (k : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  have hpt : ∀ t : ↥T.1, d.weylIntegrand μ' f T.1 t =
      (((k : ENNReal)⁻¹).toReal : ℂ) * d.weylIntegrand μ f T.1 t := fun t =>
    d.weylIntegrand_of_eq_smul T hk0 ENNReal.coe_ne_top hk f t
  simp_rw [hpt]
  rw [hk, integral_smul_measure, integral_const_mul, Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul, ← ENNReal.toReal_mul, ENNReal.mul_inv_cancel hk0 ENNReal.coe_ne_top,
    ENNReal.toReal_one, Complex.ofReal_one, one_mul]

/-! ## 3. `K^A` and `J^A` (BP §5.5, pp. 115–116) -/

/-- **The kernel `K^A_{f,f'}(g₁, g₂) = ∫_{G(F)} f(g₁⁻¹ g g₂) f'(g) dg`** (BP §5.5, p. 115), for
`dg = Measure.haar`. -/
def kernelA (f f' : ↥d.G → ℂ) (g₁ g₂ : ↥d.G) : ℂ :=
  ∫ g : ↥d.G, f (g₁⁻¹ * g * g₂) * f' g ∂Measure.haar

/-- The diagonal of `K^A` is the inner integral of the orbital pairing. -/
theorem kernelA_diag (f f' : ↥d.G → ℂ) (y : ↥d.G) :
    d.kernelA f f' y y = orbitalInner d f f' y := rfl

/-- **`J^A(f, f') = ∫_{A_G(F)\G(F)} K^A_{f,f'}(x, x) dx`** (BP §5.5, p. 116), integrating over the
quotient group `G(F)/A_G(F)` (`= A_G(F)\G(F)`, `A_G` central) with `measGmodAG = dg / d_c a`
(Arthur 1991, §1, p. 11, rather than BP §1.6's exp-lifted measure on `A_G(F)`), at the
representatives
`Quotient.out` (`K^A(x a, x a) = K^A(x, x)` for `a ∈ A_G(F)`: `orbitalInner_mul_AG`).  It is the
Lean integral: `0` when `x ↦ K^A(x, x)` is not integrable.  BP Thm 5.5.1(ii) gives integrability
for strongly cuspidal `f` (`integrable_kernelA_diag_scusp`). -/
def jA (f f' : ↥d.G → ℂ) : ℂ :=
  ∫ x : d.GmodAG, d.kernelA f f' (Quotient.out x) (Quotient.out x) ∂d.measGmodAG

/-- **`J^A` is the orbital pairing** used to define `θ_f` (`IsThetaF`). -/
theorem jA_eq_orbitalPairing (f f' : ↥d.G → ℂ) : d.jA f f' = orbitalPairing d f f' := rfl

/-- **Integrability of `x ↦ K^A(x, x)` on `G(F)/A_G(F)`** for `f ∈ C_c^∞(G(F))` strongly cuspidal
and `f' ∈ C_c^∞(G(F))` (BP Thm 5.5.1(ii)), from the literature axiom `bp_integrable_kernel_scusp`;
the measure `measGmodAG` is a positive multiple of `Measure.haar`. -/
theorem integrable_kernelA_diag_scusp (f : ↥d.G → ℂ) (hf : f ∈ testFunctions ↥d.G)
    (hcusp : IsStronglyCuspidalInline d f)
    (f' : ↥d.G → ℂ) (hf' : f' ∈ testFunctions ↥d.G) :
    Integrable (fun x : d.GmodAG => d.kernelA f f' (Quotient.out x) (Quotient.out x))
      d.measGmodAG :=
  d.integrable_measGmodAG (LitTF.bp_integrable_kernel_scusp d f hf hcusp f' hf')

end GGPData

end GSpinGGP
