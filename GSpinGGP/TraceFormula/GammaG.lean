/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.RegularCentralizer
import GSpinGGP.TraceFormula.Spectral

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
* **`|W(G,T)|`** is `ellWeylCard d T = |N_{G(F)}(T(F))/T(F)|` (`Spectral.lean`), BP's
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
(`d_c a` gives the maximal compact subgroup of `A_G(F)` mass `1`): BP leaves the measure on
`A_G(F)` unstated, and we read it with Arthur's convention (Arthur, *A local trace formula*, Publ.
IHÉS 73 (1991), §1, p. 11), the only Haar measure on `A_G(F)` for which BP Thm 5.5.1(iv) can hold.
`J^A` is the orbital pairing already used for `θ_f`: `jA_eq_orbitalPairing` (`rfl`).

**Integrability.**  BP Thm 5.5.1(ii) (printed without proof; BP defers it to its reference [18])
makes `x ↦ K^A(x, x)` integrable for strongly cuspidal `f`.  `jA` is the Lean integral, which is
`0` when the integrand is not integrable.  For `f ∈ C_c^∞(G(F))` strongly cuspidal and
`f' ∈ C_c^∞(G(F))`, integrability is the existing literature axiom `bp_integrable_kernel_scusp`
(`integrable_kernelA_diag_scusp`).

## The Weyl integration formula (BP §1.7, p. 32)

`∫_{G(F)} f(g) dg = ∫_{Γ(G)} D^G(x)^{1/2} J_G(x, f) dx` for `f ∈ C_c^∞(G(F))`, with
`J_G(x, f) = D^G(x)^{1/2} ∫_{G_x(F)\G(F)} f(g⁻¹ x g) dg` (BP §1.8).  `weyl_integration` states it
for every family of Haar measures on the maximal tori; it is a `sorry` (proof sketch in its
docstring), off the path of the main theorem.  At the commutative toy datum it is proved
(`Sanity/GammaGAudit.lean`).

## Main definitions

* `GGPData.quotMeasureOn T μ`, `GGPData.orbitalIntegralOn T μ t f`: `dg/μ` on `T(F)\G(F)` and
  `J_G(t, f)` for a closed subgroup `T`, indexed by `T` rather than by `t`; at `T = G_x(F)` they are
  `orbQuotMeasure` and `orbitalIntegral` (`rfl`).
* `GGPData.MaxTorus`, `GGPData.MaxTorusClass`, `GGPData.gammaIntegral`.
* `GGPData.weylIntegrand`: `t ↦ D^G(t)^{1/2} J_G(t, f)` on `T(F)`, `0` off `G_reg(F)`.
* `GGPData.kernelA`, `GGPData.jA`.
-/

noncomputable section

open MeasureTheory Topology

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

/-! ## 1. Orbital integrals indexed by the torus -/

section OnSubgroup

variable (T : Subgroup ↥d.G)

open scoped Classical in
/-- **The quotient measure `dg/μ` on `T(F)\G(F)`** for a subgroup `T` of `G(F)` and a measure `μ` on
`T(F)` (Weil's formula against `dg = Measure.haar`), chosen by the epsilon pattern; `0` if there is
none.  At `T = G_x(F)` this is `orbQuotMeasure x μ` (`orbQuotMeasure_eq_quotMeasureOn`); indexing by
`T` lets one quotient serve every `t ∈ T(F)`. -/
def quotMeasureOn (μ : Measure ↥T) : Measure (CosetSpace T.subtype) :=
  if h : ∃ m, IsWeilMeasure T.subtype (Measure.haar : Measure ↥d.G) μ m then h.choose else 0

theorem orbQuotMeasure_eq_quotMeasureOn (x : ↥d.G) (μ : Measure ↥(d.centG x)) :
    d.orbQuotMeasure x μ = d.quotMeasureOn (d.centG x) μ := rfl

/-- **`dg/μ` is the Weil measure** for a closed subgroup `T` and a right invariant Haar measure `μ`
(from `weil_quotient`). -/
theorem quotMeasureOn_spec (hT : IsClosed (T : Set ↥d.G)) (μ : Measure ↥T) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] :
    IsWeilMeasure T.subtype Measure.haar μ (d.quotMeasureOn T μ) := by
  classical
  have : LocallyCompactSpace ↥T := hT.locallyCompactSpace
  have : SecondCountableTopology ↥T := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have h := (weil_quotient T.subtype continuous_subtypeVal hT.isClosedEmbedding_subtypeVal
    Measure.haar μ).exists
  unfold quotMeasureOn
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

/-- **The normalized orbital integral `J_G(t, f)` with `G_t(F) = T(F)`**:
`D^G(t)^{1/2} ∫_{T(F)\G(F)} f(g⁻¹ t g) dg` for the quotient measure `dg/μ` (`quotMeasureOn`),
integrating over the representatives `CosetSpace.out`.  For `t` regular with `centG t = T` it is
BP's `J_G(t, f)` (§1.8, p. 33); at `T = centG x`, `t = x` it is `orbitalIntegral x μ f`
(`orbitalIntegral_eq_orbitalIntegralOn`). -/
def orbitalIntegralOn (μ : Measure ↥T) (t : ↥d.G) (f : ↥d.G → ℂ) : ℂ :=
  (Real.sqrt (weylDisc d.lie (t : d.ambientˣ)) : ℂ) *
    ∫ q, f ((CosetSpace.out _ q)⁻¹ * t * CosetSpace.out _ q) ∂d.quotMeasureOn T μ

theorem orbitalIntegral_eq_orbitalIntegralOn (x : ↥d.G) (μ : Measure ↥(d.centG x))
    (f : ↥d.G → ℂ) : d.orbitalIntegral x μ f = d.orbitalIntegralOn (d.centG x) μ x f := rfl

end OnSubgroup

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

/-- An elliptic maximal torus (`EllTorus`, `TraceFormula/Spectral.lean`) is a maximal torus. -/
def EllTorus.toMaxTorus (T : EllTorus d) : d.MaxTorus :=
  ⟨T.1, by
    obtain ⟨x, hx, hT⟩ := T.2
    exact ⟨x, d.ellRegSet_subset_regularSet hx, hT⟩⟩

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
`ellWeylCard d T` = `|N_{G(F)}(T(F))/T(F)|`.  The measures `μ T` on the tori are an argument (BP's
`dt` is the exp-lift of the autodual measure on `𝔱(F)`, not formalized; see the module docstring),
and so is the dependence of the integrand on the torus (`φ T`): integrands such as
`D^{1/2} J_G(·, f)` involve the measure on `T(F)` through `J_G`.  For a class function, take
`φ` constant in `T`. -/
def gammaIntegral (μ : ∀ T : Subgroup ↥d.G, Measure ↥T) (φ : Subgroup ↥d.G → ↥d.G → ℂ) : ℂ :=
  ∑' c : d.MaxTorusClass, ((ellWeylCard d (Quot.out c).1 : ℂ))⁻¹ *
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

/-- **The Weyl integration formula** (BP §1.7, p. 32; Harish-Chandra): for `f ∈ C_c^∞(G(F))`,
`∫_{G(F)} f(g) dg = ∫_{Γ(G)} D^G(x)^{1/2} J_G(x, f) dx
  = Σ_{T ∈ 𝒯(G)} |W(G,T)|⁻¹ ∫_{T(F)} D^G(t)^{1/2} J_G(t, f) dt`,
for every family `μ` of Haar measures on the maximal tori (`J_G(t, ·)` taken for `dg / μ T`; the
right-hand side does not depend on `μ`, see the module docstring).

**Status: `sorry`, off the path of the main theorem.**  BP states it without proof, as standard.
Proof sketch (Harish-Chandra; e.g. Kottwitz, *Harmonic analysis on reductive p-adic groups and Lie
algebras*, Clay Math. Proc. 4 (2005)): (1) `G_reg(F)` is open and conull in `G(F)` (complement of the zero set of the
nonzero polynomial `D^G`), so `∫_G f = ∫_{G_reg} f`.  (2) `G_reg(F)` is the disjoint union over
`T ∈ 𝒯(G)` of the open sets `G_reg(F) ∩ ⋃_g g T(F) g⁻¹`.  (3) For each `T`, the map
`T(F)\G(F) × T_reg(F) → G(F)`, `(g, t) ↦ g⁻¹ t g`, is a local analytic isomorphism, `|W(G,T)|`-to-one
onto its image, with Jacobian `D^G(t)` for the measures `dg/dt` and `dt` (the differential is
`1 − Ad(t⁻¹)` on `𝔤/𝔱`).  (4) The change of variables then gives
`∫_{image} f = |W(G,T)|⁻¹ ∫_{T(F)} D^G(t) ∫_{T(F)\G(F)} f(g⁻¹ t g) dg dt`.  Missing here: the
finiteness of `𝒯(G)`, the `p`-adic analytic change of variables formula and the Jacobian
computation, and `T(F) = G_t(F)` for regular `t ∈ T(F)` with `T` a maximal torus (the last is
`centG_eq_of_mem_regularSet`). -/
theorem weyl_integration (μ : ∀ T : Subgroup ↥d.G, Measure ↥T)
    (hμ : ∀ T : d.MaxTorus, (μ T.1).IsHaarMeasure) (f : ↥d.G → ℂ)
    (hf : f ∈ testFunctions ↥d.G) :
    ∫ g, f g ∂Measure.haar = d.gammaIntegral μ (d.weylIntegrand μ f) := by
  sorry

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
(Arthur 1991, §1, p. 11; BP leaves the measure on `A_G(F)` unstated), at the representatives
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
    (hcusp : ∀ (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV), d.IsProperFlagPair FW FV →
      ∀ p ∈ d.whittB FW FV, ∫ u : ↥(d.whittU FW FV), f (p * u) ∂Measure.haar = 0)
    (f' : ↥d.G → ℂ) (hf' : f' ∈ testFunctions ↥d.G) :
    Integrable (fun x : d.GmodAG => d.kernelA f f' (Quotient.out x) (Quotient.out x))
      d.measGmodAG :=
  d.integrable_measGmodAG (LitTF.bp_integrable_kernel_scusp d f hf hcusp f' hf')

end GGPData

end GSpinGGP
