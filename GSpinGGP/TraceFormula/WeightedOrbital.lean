/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Basic
import GSpinGGP.GGP.WeightVM
import GSpinGGP.GGP.Germs

/-!
# Orbital integrals and Arthur's weighted orbital integrals

For `x ∈ G(F)` with centralizer `G_x(F)`, and `f : G(F) → ℂ`,

* the (normalized) orbital integral (Beuzart-Plessis, Astérisque 418, §1.8, p. 33)
  `J_G(x, f) = D^G(x)^{1/2} ∫_{G_x(F)\G(F)} f(g⁻¹ x g) dg`;
* for a Levi subgroup `M ∋ x` and a good compact subgroup `K`, the weighted orbital integral
  (Beuzart-Plessis §1.10, p. 36; Waldspurger, Compos. Math. 146 (2010), §2.3; Thesis §2.6)
  `J_M(x, f) = D^G(x)^{1/2} ∫_{G_x(F)\G(F)} f(g⁻¹ x g) v_M(g) dg`, with `v_M` of
  `GGP/WeightVM.lean`.

**Measures.** `dg` on `G(F)` is `Measure.haar`, and the Haar measure `μ` on `G_x(F)` is an
explicit argument; `dg/μ` is the Weil quotient measure on the right coset space `G_x(F)\G(F)`
(`orbQuotMeasure`, from `weil_quotient`).  Beuzart-Plessis (§1.6) and Waldspurger (§1.2) fix both
through the exponential map and the autodual measures on `𝔤(F)`, `𝔤_x(F)`; neither is used here.
Replacing `μ` by `c • μ` multiplies `J_M` by `c⁻¹` (`weightedOrbitalIntegral_smul_measure`);
in `θ_f = (−1)^{a_G − a_{M(x)}} ν(G_x)⁻¹ D^G(x)^{−1/2} J_{M(x)}(x, f)` (Beuzart-Plessis §5.2) the
factor `ν(G_x)⁻¹` (defined by `d_c t = ν(G_x) dt`, Beuzart-Plessis §1.6) cancels the dependence on
the measure of `G_x(F)` (equivalently: take `μ = d_c t`).  It does not cancel the choice of `dg`:
`Measure.haar` on `G(F)` differs from Beuzart-Plessis' measure by a positive constant, by which
`J_M` (and `θ_f`) then differ from the sources' (linearly in `dg`); statements comparing with the
sources must account for it.

**Where the integral makes sense.** The integrand is evaluated at the chosen representatives
`CosetSpace.out` of the cosets.  It is a function on `G_x(F)\G(F)` when `G_x(F) ⊆ M(F)`
(`weightedIntegrand_mul_left`), which is the case for `x ∈ M(F) ∩ G_reg(F)` (Waldspurger 2010,
§2.3: `G_x = M_x ⊂ M`, for `G_x = Z_G(x)⁰`, which is the full centralizer `centG x` here, as
`Z_G(x)` is connected by Steinberg's theorem, `Spin` being simply connected); the results below carry `G_x(F) ⊆ M(F)` as a hypothesis, as
Beuzart-Plessis' definition does.  For `x ∈ M(F) ∩ G_reg(F)` it holds (`centG_le_M`), and every
Haar measure on `G_x(F)` is right invariant (`isMulRightInvariant_of_mem_regularSet`), in
`TraceFormula/RegularCentralizer.lean`.

## Main definitions

* `GGPData.centG x`: `G_x(F)` as a closed subgroup of `G(F)`; `GGPData.CentQuot x`:
  `G_x(F)\G(F)`.
* `GGPData.quotMeasureOn T μ`, `GGPData.orbitalIntegralOn T μ t f`: `dg/μ` on `T(F)\G(F)` and
  `J_G(t, f)` for a subgroup `T` with `G_t(F) = T(F)`.
* `GGPData.orbQuotMeasure x μ`: the quotient measure `dg/μ` on `G_x(F)\G(F)` (`T = G_x(F)`).
* `GGPData.orbitalIntegral x μ f`: `J_G(x, f)` (`T = G_x(F)`, `t = x`).
* `GGPData.weightedOrbitalIntegral L K x μ f`: `J_M(x, f)`.

## Main results

* `orbQuotMeasure_spec`: `dg/μ` is the Weil measure, for `μ` Haar and right invariant (`G_x(F)`
  unimodular; for regular `x` it is a torus).
* `integral_out_mulRight`: `dg/μ` is right invariant, as an integral formula.
* `integrable_weight`: `f(g⁻¹ x g) φ(g)` is integrable on `G_x(F)\G(F)` for continuous left
  `M(F)`-invariant `φ` (same hypotheses as below).
* `integrable_weightedIntegrand`: the integrand is integrable for continuous compactly
  supported `f`, `x` semisimple and `G_x(F) ⊆ M(F)`, from `exists_isCompact_conj_mem` (closed
  orbits; not yet proved).
* `weightedOrbitalIntegral_eq_orbitalIntegral_of_aG_eq_top`: `J_M = J_G` when `a_M = a_G`
  (`v_G = 1`), e.g. `M = G`.
* `weightedOrbitalIntegral_conj_K`: `J_M(x, f(k · k⁻¹)) = J_M(x, f)` for `k ∈ K`.
* `weightedOrbitalIntegral_conj`: `J_M(m x m⁻¹, f) = J_M(x, f)` for `m ∈ M(F)`, with the Haar
  measure on `G_{m x m⁻¹}(F)` transported from `G_x(F)`.
-/

noncomputable section

open MeasureTheory Topology

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

/-! ## 0. The quotient by a closed subgroup -/

section OnSubgroup

variable (T : Subgroup ↥d.G)

open scoped Classical in
/-- **The quotient measure `dg/μ` on `T(F)\G(F)`** for a subgroup `T` of `G(F)` and a measure `μ`
on `T(F)` (Weil's formula against `dg = Measure.haar`), chosen by the epsilon pattern; `0` if
there is none.  `orbQuotMeasure x μ` is the case `T = G_x(F)`; indexing by `T` lets one quotient
serve every `t ∈ T(F)` (as in the Weyl integration formula, `TraceFormula/GammaG.lean`). -/
def quotMeasureOn (μ : Measure ↥T) : Measure (CosetSpace T.subtype) :=
  if h : ∃ m, IsWeilMeasure T.subtype (Measure.haar : Measure ↥d.G) μ m then h.choose else 0

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

/-- **Rescaling the measure on `T(F)`**: `dg/(c μ) = c⁻¹ (dg/μ)` on `T(F)\G(F)` for `0 < c < ∞`,
a closed subgroup `T` and a right invariant Haar measure `μ` (`IsWeilMeasure.smul_right` and the
uniqueness of the Weil measure). -/
theorem quotMeasureOn_smul (hT : IsClosed (T : Set ↥d.G)) (μ : Measure ↥T) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] {c : ENNReal} (hc0 : c ≠ 0) (hc : c ≠ ⊤) :
    d.quotMeasureOn T (c • μ) = c⁻¹ • d.quotMeasureOn T μ := by
  have : (c • μ).IsHaarMeasure := Measure.IsHaarMeasure.smul μ hc0 hc
  have : LocallyCompactSpace ↥T := hT.locallyCompactSpace
  have : SecondCountableTopology ↥T := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  exact IsWeilMeasure.unique continuous_subtypeVal hT.isClosedEmbedding_subtypeVal
    (d.quotMeasureOn_spec T hT (c • μ)) ((d.quotMeasureOn_spec T hT μ).smul_right hc0 hc)

/-- **The normalized orbital integral `J_G(t, f)` with `G_t(F) = T(F)`**:
`D^G(t)^{1/2} ∫_{T(F)\G(F)} f(g⁻¹ t g) dg` for the quotient measure `dg/μ` (`quotMeasureOn`),
integrating over the representatives `CosetSpace.out`.  For `t` regular with `centG t = T` it is
Beuzart-Plessis' `J_G(t, f)` (§1.8, p. 33); `orbitalIntegral x μ f` is the case `T = G_x(F)`,
`t = x`. -/
def orbitalIntegralOn (μ : Measure ↥T) (t : ↥d.G) (f : ↥d.G → ℂ) : ℂ :=
  (Real.sqrt (weylDisc d.lie (t : d.ambientˣ)) : ℂ) *
    ∫ q, f ((CosetSpace.out _ q)⁻¹ * t * CosetSpace.out _ q) ∂d.quotMeasureOn T μ

/-- **Dependence of `J_G(t, f)` on the measure of `T(F)`**: replacing `μ` by `c • μ`,
`0 < c < ∞`, divides it by `c` (`quotMeasureOn_smul`). -/
theorem orbitalIntegralOn_smul_measure (hT : IsClosed (T : Set ↥d.G)) (μ : Measure ↥T)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {c : ENNReal} (hc0 : c ≠ 0) (hc : c ≠ ⊤)
    (t : ↥d.G) (f : ↥d.G → ℂ) :
    d.orbitalIntegralOn T (c • μ) t f = ((c⁻¹).toReal : ℂ) * d.orbitalIntegralOn T μ t f := by
  unfold orbitalIntegralOn
  rw [d.quotMeasureOn_smul T hT μ hc0 hc, integral_smul_measure, Complex.real_smul]
  ring

end OnSubgroup

/-! ## 1. `G_x(F)\G(F)` and its measure -/

section Quotient

variable (x : ↥d.G)

/-- **The centralizer `G_x(F)`** of `x`, as a subgroup of `G(F)` (Thesis §2.1; the same group as
`grpCentralizer d.G x`, `mem_centG_iff`).  Beuzart-Plessis (p. 27) writes `G_x` for the neutral
component `Z_G(x)⁰`; for semisimple `x` the full centralizer is the same here, since the derived
group `Spin × Spin` of `G` is simply connected, so centralizers of semisimple elements are
connected (Steinberg; Humphreys, *Conjugacy classes in semisimple algebraic groups*, Thm 2.11). -/
abbrev centG : Subgroup ↥d.G := Subgroup.centralizer {x}

/-- `centG x` is `grpCentralizer d.G x` read inside `G(F)`. -/
theorem mem_centG_iff {g : ↥d.G} :
    g ∈ d.centG x ↔ (g : d.ambientˣ) ∈ grpCentralizer d.G (x : d.ambientˣ) := by
  rw [Subgroup.mem_centralizer_singleton_iff, grpCentralizer, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => ⟨g.prop, congrArg Subtype.val h.eq⟩, fun h => Subtype.ext h.2.eq⟩

/-- **Conjugating `x` by `c g` with `c ∈ G_x(F)`** is conjugating by `g`:
`(c g)⁻¹ x (c g) = g⁻¹ x g`. -/
theorem conj_mul_of_mem_centG {c : ↥d.G} (hc : c ∈ d.centG x) (g : ↥d.G) :
    (c * g)⁻¹ * x * (c * g) = g⁻¹ * x * g := by
  have hcx : c⁻¹ * x * c = x := by
    rw [mul_assoc, ← (Subgroup.mem_centralizer_singleton_iff.1 hc).eq, inv_mul_cancel_left]
  calc (c * g)⁻¹ * x * (c * g) = g⁻¹ * (c⁻¹ * x * c) * g := by group
    _ = g⁻¹ * x * g := by rw [hcx]

/-- **`G_{a x}(F) = G_x(F)` for `a ∈ A_G(F)`** (`A_G` is central in `G`). -/
theorem centG_mul_AG {a : ↥d.G} (ha : a ∈ d.AG) : d.centG (a * x) = d.centG x := by
  have hc : ∀ y : ↥d.G, y * a = a * y := fun y =>
    Subgroup.mem_center_iff.mp (d.AG_le_center ha) y
  ext y
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    calc x * y = a⁻¹ * (a * x * y) := by group
      _ = a⁻¹ * (y * (a * x)) := by rw [h]
      _ = a⁻¹ * (a * (y * x)) := by rw [← mul_assoc y, hc y, mul_assoc]
      _ = y * x := by group
  · intro h
    rw [mul_assoc, h, ← mul_assoc, ← hc y, mul_assoc]

/-- **A left `G_x(F)`-invariant function at the chosen representative** of the coset of `g` is
its value at `g`. -/
theorem apply_out_mk_of_mul_left {α : Type*} {Φ : ↥d.G → α}
    (hΦ : ∀ c ∈ d.centG x, ∀ g, Φ (c * g) = Φ g) (g : ↥d.G) :
    Φ (CosetSpace.out _ (CosetSpace.mk (d.centG x).subtype g)) = Φ g := by
  obtain ⟨c, hc⟩ := CosetSpace.exists_out_mk (d.centG x).subtype g
  conv_rhs => rw [hc]
  exact (hΦ c c.2 _).symm

theorem isClosed_centG : IsClosed (d.centG x : Set ↥d.G) := Set.isClosed_centralizer _

instance locallyCompactSpace_centG : LocallyCompactSpace ↥(d.centG x) :=
  (d.isClosed_centG x).locallyCompactSpace

instance secondCountableTopology_centG : SecondCountableTopology ↥(d.centG x) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

theorem isClosedEmbedding_centG : IsClosedEmbedding (d.centG x).subtype :=
  (d.isClosed_centG x).isClosedEmbedding_subtypeVal

instance isClosed_range_centG : IsClosed ((d.centG x).subtype.range : Set ↥d.G) := by
  rw [Subgroup.range_subtype]; exact d.isClosed_centG x

/-- **`G_x(F)\G(F)`**, the space of right cosets `G_x(F) g`. -/
abbrev CentQuot : Type := CosetSpace (d.centG x).subtype

/-- **The quotient measure `dg/μ` on `G_x(F)\G(F)`** (Beuzart-Plessis §1.8, §1.10): for
`dg = Measure.haar` on `G(F)` and a measure `μ` on `G_x(F)`, the measure `m` with
`∫_G φ dg = ∫_{G_x\G} ∫_{G_x} φ(c g) dμ(c) dm(g)` for `φ ∈ C_c(G(F))` (`IsWeilMeasure`):
`quotMeasureOn (G_x(F)) μ`.  For `μ` Haar and right invariant it exists and is unique
(`orbQuotMeasure_spec`, `orbQuotMeasure_eq`). -/
def orbQuotMeasure (μ : Measure ↥(d.centG x)) : Measure (d.CentQuot x) :=
  d.quotMeasureOn (d.centG x) μ

variable {x} (μ : Measure ↥(d.centG x)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

/-- **`dg/μ` is the Weil measure** (from `weil_quotient`, `quotMeasureOn_spec`): `G(F)` is
unimodular (`isMulRightInvariant_haar_G`), and `G_x(F)` is closed. -/
theorem orbQuotMeasure_spec :
    IsWeilMeasure (d.centG x).subtype Measure.haar μ (d.orbQuotMeasure x μ) :=
  d.quotMeasureOn_spec _ (d.isClosed_centG x) μ

/-- Uniqueness: any Weil measure for `dg` and `μ` is `orbQuotMeasure x μ`. -/
theorem orbQuotMeasure_eq {m : Measure (d.CentQuot x)}
    (hm : IsWeilMeasure (d.centG x).subtype Measure.haar μ m) : d.orbQuotMeasure x μ = m :=
  IsWeilMeasure.unique continuous_subtypeVal (d.isClosedEmbedding_centG x)
    (d.orbQuotMeasure_spec μ) hm

instance isFiniteMeasureOnCompacts_orbQuotMeasure :
    IsFiniteMeasureOnCompacts (d.orbQuotMeasure x μ) :=
  (d.orbQuotMeasure_spec μ).isFiniteMeasureOnCompacts continuous_subtypeVal
    (d.isClosedEmbedding_centG x)

/-- **`dg/μ` is right invariant**: right translation by `γ` on `G_x(F)\G(F)` preserves it. -/
theorem map_mulRight_orbQuotMeasure (γ : ↥d.G) :
    (d.orbQuotMeasure x μ).map (CosetSpace.mulRight (d.centG x).subtype γ) =
      d.orbQuotMeasure x μ :=
  (d.orbQuotMeasure_eq μ ((d.orbQuotMeasure_spec μ).map_mulRight γ)).symm

/-- **Right translation on `G_x(F)\G(F)`**: for `Φ` left `G_x(F)`-invariant,
`∫ Φ(g γ) dg = ∫ Φ(g) dg` (`map_mulRight_orbQuotMeasure`). -/
theorem integral_out_mulRight {Φ : ↥d.G → ℂ} (hΦ : ∀ c ∈ d.centG x, ∀ g, Φ (c * g) = Φ g)
    (γ : ↥d.G) :
    ∫ q, Φ (CosetSpace.out _ q * γ) ∂d.orbQuotMeasure x μ =
      ∫ q, Φ (CosetSpace.out _ q) ∂d.orbQuotMeasure x μ := by
  set ι := (d.centG x).subtype
  conv_rhs => rw [← d.map_mulRight_orbQuotMeasure μ γ]
  rw [show (d.orbQuotMeasure x μ).map (CosetSpace.mulRight ι γ) =
      (d.orbQuotMeasure x μ).map (CosetSpace.mulRight ι γ).toMeasurableEquiv from rfl,
    integral_map_equiv]
  congr 1
  funext q
  change _ = Φ (CosetSpace.out ι (CosetSpace.mulRight ι γ q))
  conv_rhs => rw [← CosetSpace.mk_out ι q, CosetSpace.mulRight_mk, d.apply_out_mk_of_mul_left x hΦ]

end Quotient

/-! ## 2. The integrals -/

section Integrals

variable (L : d.ReducedLeviDatum) (K : d.IwasawaK L.toFlagLeviDatum) (x : ↥d.G)

/-- The integrand `g ↦ f(g⁻¹ x g) v_M(g)` of `J_M(x, f)`, on `G(F)`. -/
def weightedIntegrand (f : ↥d.G → ℂ) (g : ↥d.G) : ℂ :=
  f (g⁻¹ * x * g) * (L.vM K g : ℂ)

/-- **The normalized orbital integral** `J_G(x, f) = D^G(x)^{1/2} ∫_{G_x(F)\G(F)} f(g⁻¹ x g) dg`
(Beuzart-Plessis §1.8, p. 33; Thesis §2.6), for the quotient measure `dg/μ`
(`orbQuotMeasure`), integrating over the representatives `CosetSpace.out` (the integrand is
left `G_x(F)`-invariant): `orbitalIntegralOn (G_x(F)) μ x f`. -/
def orbitalIntegral (μ : Measure ↥(d.centG x)) (f : ↥d.G → ℂ) : ℂ :=
  d.orbitalIntegralOn (d.centG x) μ x f

/-- `orbitalIntegral` unfolded, with the quotient measure written as `orbQuotMeasure`. -/
theorem orbitalIntegral_eq (μ : Measure ↥(d.centG x)) (f : ↥d.G → ℂ) :
    d.orbitalIntegral x μ f = (Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) : ℂ) *
      ∫ q, f ((CosetSpace.out _ q)⁻¹ * x * CosetSpace.out _ q) ∂d.orbQuotMeasure x μ := rfl

/-- **Arthur's weighted orbital integral** (Beuzart-Plessis §1.10, p. 36; Waldspurger 2010, §2.3;
Thesis §2.6): for a Levi subgroup `M` (the reduced Levi datum `L`), a compact subgroup `K` with
`G = P K` for `P ∈ 𝒫(M)` (`IwasawaK`; the sources take `K` special, a `GoodK`) and `x ∈ G(F)`,
`J_M(x, f) = D^G(x)^{1/2} ∫_{G_x(F)\G(F)} f(g⁻¹ x g) v_M(g) dg`,
for the quotient measure `dg/μ` (`orbQuotMeasure`), integrating over the representatives
`CosetSpace.out`.  The sources define it for `x ∈ M(F) ∩ G_reg(F)`, where `G_x(F) ⊆ M(F)` and the
integrand is a function on `G_x(F)\G(F)` (`weightedIntegrand_mul_left`); elsewhere the value
depends on the choice of representatives and has no meaning.  The measures are discussed in the
module docstring. -/
def weightedOrbitalIntegral (μ : Measure ↥(d.centG x)) (f : ↥d.G → ℂ) : ℂ :=
  (Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) : ℂ) *
    ∫ q, d.weightedIntegrand L K x f (CosetSpace.out _ q) ∂d.orbQuotMeasure x μ

variable {d L K x}

/-- **The integrand is left `G_x(F)`-invariant when `G_x(F) ⊆ M(F)`**: `c` commutes with `x`, and
`v_M` is left `M(F)`-invariant (`vM_mul_left`). -/
theorem weightedIntegrand_mul_left (hM : d.centG x ≤ L.M) (f : ↥d.G → ℂ) {c : ↥d.G}
    (hc : c ∈ d.centG x) (g : ↥d.G) :
    d.weightedIntegrand L K x f (c * g) = d.weightedIntegrand L K x f g := by
  unfold weightedIntegrand
  rw [d.conj_mul_of_mem_centG x hc, show c * g = ((⟨c, hM hc⟩ : ↥L.M) : ↥d.G) * g from rfl, L.vM_mul_left]

/-- `J_M = J_G` when `a_M = a_G`, e.g. for `M = G` (`v_G = 1`, `vM_eq_one_of_aG_eq_top`). -/
theorem weightedOrbitalIntegral_eq_orbitalIntegral_of_aG_eq_top (hG : L.aG = ⊤)
    (μ : Measure ↥(d.centG x)) (f : ↥d.G → ℂ) :
    d.weightedOrbitalIntegral L K x μ f = d.orbitalIntegral x μ f := by
  simp [weightedOrbitalIntegral, orbitalIntegral, orbitalIntegralOn, orbQuotMeasure,
    weightedIntegrand,
    L.vM_eq_one_of_aG_eq_top hG]

/-- **`J_G = J_M` for `M = G`** given by empty flags (`vM_eq_one_of_len_eq_zero`). -/
theorem weightedOrbitalIntegral_eq_orbitalIntegral_of_len_eq_zero (hW : L.FW.len = 0)
    (hV : L.FV.len = 0) (μ : Measure ↥(d.centG x)) (f : ↥d.G → ℂ) :
    d.weightedOrbitalIntegral L K x μ f = d.orbitalIntegral x μ f :=
  weightedOrbitalIntegral_eq_orbitalIntegral_of_aG_eq_top (L.aG_eq_top_of_len_eq_zero hW hV) μ f

/-- The integrand at the chosen representative of the coset of `g` is the integrand at `g`, when
`G_x(F) ⊆ M(F)`. -/
theorem weightedIntegrand_out_mk (hM : d.centG x ≤ L.M) (f : ↥d.G → ℂ) (g : ↥d.G) :
    d.weightedIntegrand L K x f (CosetSpace.out _ (CosetSpace.mk (d.centG x).subtype g)) =
      d.weightedIntegrand L K x f g :=
  d.apply_out_mk_of_mul_left x (fun _ hc g => weightedIntegrand_mul_left hM f hc g) g

/-- **Semisimple orbits are closed, and `G_x(F)\G(F)` is homeomorphic to the orbit**, in the
form: for semisimple `x` and compact `C ⊆ G(F)`, the `g` with `g⁻¹ x g ∈ C` lie in `G_x(F) C'`
for a compact `C' ⊆ G(F)`.  This is what makes orbital integrals of compactly supported
functions finite (Beuzart-Plessis §1.8, §1.10; Waldspurger 2010, §2.3).

Not yet proved.  Sketch: (1) the conjugacy class `O_x = {g⁻¹ x g}` of a semisimple element is
closed in `G(F)`: the geometric class `𝒪` of a semisimple element of the connected reductive
group `G` is Zariski closed (Steinberg), so `𝒪(F)` is closed in `G(F)`; in characteristic `0`
the orbit map `G → 𝒪` is smooth, so by the implicit function theorem each `G(F)`-orbit in `𝒪(F)`
is open in `𝒪(F)`; there are finitely many (finiteness of Galois cohomology over a `p`-adic
field, Borel–Serre), so each is also closed.  (2) `G(F)` is `σ`-compact and acts continuously
and transitively on the closed, hence locally compact and Baire, space `O_x`; by the open mapping
theorem (`isOpenMap_smul_of_sigmaCompact`) the orbit map is open, so `G_x(F)\G(F) → O_x` is a
homeomorphism.  (3) `C ∩ O_x` is compact, so its preimage in `G_x(F)\G(F)` is compact and lifts
to a compact `C' ⊆ G(F)` (`CosetSpace.exists_isCompact_image_superset`).  A printed alternative
for regular `x` is the bound `σ_T(g) ≤ c(1 + |log D^G(x)|)` for `g⁻¹ x g ∈ Γ` (Arthur 1991,
Lemma 4.2, quoted in Waldspurger 2010, §2.3, (1)). -/
theorem exists_isCompact_conj_mem (hx : IsSS F ((x : d.ambientˣ) : d.ambient)) {C : Set ↥d.G}
    (hC : IsCompact C) :
    ∃ C' : Set ↥d.G, IsCompact C' ∧
      ∀ g : ↥d.G, g⁻¹ * x * g ∈ C → ∃ c ∈ d.centG x, ∃ c' ∈ C', g = c * c' := by
  sorry

/-- **`f(g⁻¹ x g) φ(g)` is integrable on `G_x(F)\G(F)`** for `x` semisimple with
`G_x(F) ⊆ M(F)`, `f` continuous with compact support and `φ` continuous and left
`M(F)`-invariant: on `G_x(F)\G(F)` it is continuous and supported in the image of a compact set
(`exists_isCompact_conj_mem`), and `dg/μ` is finite on compact sets. -/
theorem integrable_weight (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    (hM : d.centG x ≤ L.M) {f : ↥d.G → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {φ : ↥d.G → ℝ} (hφ : Continuous φ) (hφM : ∀ m ∈ L.M, ∀ g, φ (m * g) = φ g)
    (μ : Measure ↥(d.centG x)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    Integrable (fun q => f ((CosetSpace.out _ q)⁻¹ * x * CosetSpace.out _ q) *
      (φ (CosetSpace.out _ q) : ℂ)) (d.orbQuotMeasure x μ) := by
  set ι := (d.centG x).subtype
  set Φ : ↥d.G → ℂ := fun g => f (g⁻¹ * x * g) * (φ g : ℂ)
  have hcont : Continuous Φ :=
    (hf.comp (by fun_prop)).mul (Complex.continuous_ofReal.comp hφ)
  have hinv : ∀ c ∈ d.centG x, ∀ g, Φ (c * g) = Φ g := fun c hc g => by
    simp only [Φ, d.conj_mul_of_mem_centG x hc, hφM c (hM hc)]
  have hΦ : Continuous fun q : d.CentQuot x => Φ (CosetSpace.out ι q) := by
    refine CosetSpace.continuous_of_comp_mk ι ?_
    have : (fun q : d.CentQuot x => Φ (CosetSpace.out ι q)) ∘ CosetSpace.mk ι = Φ :=
      funext (d.apply_out_mk_of_mul_left x hinv)
    rw [this]; exact hcont
  obtain ⟨C', hC', hsub⟩ := exists_isCompact_conj_mem hx hfc
  refine hΦ.integrable_of_hasCompactSupport (HasCompactSupport.intro (hC'.image
    (CosetSpace.continuous_mk ι)) fun q hq => ?_)
  show Φ (CosetSpace.out ι q) = 0
  by_contra hne
  obtain ⟨c, hc, c', hc', he⟩ := hsub (CosetSpace.out ι q)
    (subset_tsupport f (left_ne_zero_of_mul hne))
  refine hq ⟨c', hc', ?_⟩
  rw [← CosetSpace.mk_out ι q, CosetSpace.mk_eq_mk_iff, CosetSpace.rel_iff]
  exact ⟨⟨c, hc⟩, he⟩

/-- **The integrand of `J_M(x, f)` is integrable** for `x` semisimple with `G_x(F) ⊆ M(F)` and `f`
continuous with compact support (e.g. `f ∈ C_c^∞(G(F))`), for any Haar measure `μ` on the
unimodular group `G_x(F)` (`integrable_weight` with `φ = v_M`, continuous for `K` open). -/
theorem integrable_weightedIntegrand {K : d.GoodK L.toFlagLeviDatum}
    (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    (hM : d.centG x ≤ L.M) {f : ↥d.G → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (μ : Measure ↥(d.centG x)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    Integrable (fun q => d.weightedIntegrand L K x f (CosetSpace.out _ q))
      (d.orbQuotMeasure x μ) :=
  integrable_weight hx hM hf hfc (L.continuous_vM K) (fun m hm g => L.vM_mul_left K ⟨m, hm⟩ g) μ

/-- **Dependence on the Haar measure of `G_x(F)`**: replacing `μ` by `c • μ`, `0 < c < ∞`,
divides the quotient measure, hence `J_M(x, f)`, by `c` (`IsWeilMeasure.smul_right`). -/
theorem weightedOrbitalIntegral_smul_measure (μ : Measure ↥(d.centG x)) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] {c : ENNReal} (hc0 : c ≠ 0) (hc : c ≠ ⊤) (f : ↥d.G → ℂ) :
    d.weightedOrbitalIntegral L K x (c • μ) f =
      ((c⁻¹).toReal : ℂ) * d.weightedOrbitalIntegral L K x μ f := by
  have hq : d.orbQuotMeasure x (c • μ) = c⁻¹ • d.orbQuotMeasure x μ :=
    d.quotMeasureOn_smul _ (d.isClosed_centG x) μ hc0 hc
  unfold weightedOrbitalIntegral
  rw [hq, integral_smul_measure, Complex.real_smul]
  ring

/-- With the zero measure on `G_x(F)` there is no quotient measure: the Weil formula would make
every integral over `G(F)` vanish. -/
theorem orbQuotMeasure_zero : d.orbQuotMeasure x 0 = 0 := by
  classical
  have h : ¬ ∃ m, IsWeilMeasure (d.centG x).subtype (Measure.haar : Measure ↥d.G) 0 m :=
    fun ⟨_, hm⟩ => not_isWeilMeasure_zero hm
  unfold orbQuotMeasure quotMeasureOn
  rw [dite_eq_right_of_eq_false (eq_false h)]

theorem weightedOrbitalIntegral_zero_measure (f : ↥d.G → ℂ) :
    d.weightedOrbitalIntegral L K x 0 f = 0 := by
  simp [weightedOrbitalIntegral, orbQuotMeasure_zero]

/-! ### Invariance -/

/-- **`J_M(x, ·)` is invariant under conjugation of `f` by `K`** (Waldspurger 2010, §2.3:
`v_M` is right `K`-invariant): `J_M(x, f(k · k⁻¹)) = J_M(x, f)` for `k ∈ K`, by the change of
variables `g ↦ g k⁻¹` on `G_x(F)\G(F)` (`integral_out_mulRight`). -/
theorem weightedOrbitalIntegral_conj_K (hM : d.centG x ≤ L.M) (μ : Measure ↥(d.centG x))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {k : ↥d.G} (hk : k ∈ K.K) (f : ↥d.G → ℂ) :
    d.weightedOrbitalIntegral L K x μ (fun g => f (k * g * k⁻¹)) =
      d.weightedOrbitalIntegral L K x μ f := by
  have hpt : ∀ g, d.weightedIntegrand L K x (fun g => f (k * g * k⁻¹)) g =
      d.weightedIntegrand L K x f (g * k⁻¹) := by
    intro g
    unfold weightedIntegrand
    rw [L.vM_mul_right K g (K.K.inv_mem hk)]
    congr 2
    group
  unfold weightedOrbitalIntegral
  congr 1
  rw [← d.integral_out_mulRight μ (fun c hc g => weightedIntegrand_mul_left hM f hc g) k⁻¹]
  congr 1
  funext q
  exact hpt _

end Integrals

/-! ## 3. Conjugation by `M(F)` -/

section Conj

/-- Conjugation `g ↦ m g m⁻¹` of `G(F)`, as an isomorphism of topological groups. -/
def conjG (m : ↥d.G) : ↥d.G ≃ₜ* ↥d.G where
  toMulEquiv := MulAut.conj m
  continuous_toFun := by
    show Continuous fun g : ↥d.G => m * g * m⁻¹
    fun_prop
  continuous_invFun := by
    show Continuous fun g : ↥d.G => m⁻¹ * g * m
    fun_prop

@[simp] theorem conjG_apply (m g : ↥d.G) : d.conjG m g = m * g * m⁻¹ := rfl

/-- The Haar measure of `G(F)` is invariant under conjugation (`G(F)` is unimodular,
`isMulRightInvariant_haar_G`). -/
theorem map_conjG_haar (m : ↥d.G) :
    (Measure.haar : Measure ↥d.G).map (d.conjG m) = Measure.haar := by
  have e : (d.conjG m : ↥d.G → ↥d.G) = (· * m⁻¹) ∘ (m * ·) := by
    funext g; rfl
  rw [e, ← Measure.map_map (by fun_prop) (by fun_prop), map_mul_left_eq_self,
    map_mul_right_eq_self]

/-- Conjugation by `m` maps `G_x(F)` onto `G_{m x m⁻¹}(F)`. -/
def centConj (x m : ↥d.G) : ↥(d.centG x) ≃ₜ* ↥(d.centG (m * x * m⁻¹)) where
  toFun c := ⟨m * c * m⁻¹, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := (Subgroup.mem_centralizer_singleton_iff.1 c.2).eq
    show m * c * m⁻¹ * (m * x * m⁻¹) = m * x * m⁻¹ * (m * c * m⁻¹)
    calc m * c * m⁻¹ * (m * x * m⁻¹) = m * (c * x) * m⁻¹ := by group
      _ = m * (x * c) * m⁻¹ := by rw [hc]
      _ = _ := by group⟩
  invFun c := ⟨m⁻¹ * c * m, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := (Subgroup.mem_centralizer_singleton_iff.1 c.2).eq
    show m⁻¹ * c * m * x = x * (m⁻¹ * c * m)
    calc m⁻¹ * c * m * x = m⁻¹ * (c * (m * x * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * x * m⁻¹) * c) * m := by rw [hc]
      _ = _ := by group⟩
  left_inv c := Subtype.ext (by simp [mul_assoc])
  right_inv c := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem coe_centConj (x m : ↥d.G) (c : ↥(d.centG x)) :
    ((d.centConj x m c : ↥(d.centG (m * x * m⁻¹))) : ↥d.G) = m * c * m⁻¹ := rfl

variable {d} {L : d.ReducedLeviDatum} {K : d.IwasawaK L.toFlagLeviDatum} {x : ↥d.G}

/-- `D^G(m x m⁻¹) = D^G(x)` for `m ∈ G(F)`. -/
theorem weylDisc_conj (m : ↥d.G) :
    weylDisc d.lie ((m * x * m⁻¹ : ↥d.G) : d.ambientˣ) = weylDisc d.lie (x : d.ambientˣ) := by
  have e : ((m * x * m⁻¹ : ↥d.G) : d.ambientˣ) =
      (m : d.ambientˣ) * (x : d.ambientˣ) * (m : d.ambientˣ)⁻¹ := by simp
  rw [e]
  refine weylDisc_units_conj d.lie _ (le_antisymm ?_ fun X hX => ?_) _
  · rintro _ ⟨X, hX, rfl⟩
    exact lie_conj_stable d m X hX
  · have h := lie_conj_stable d m⁻¹ X hX
    refine ⟨_, h, ?_⟩
    simp [mul_assoc]

/-- **`J_M(x, f)` is invariant under conjugation of `x` by `M(F)`** (Beuzart-Plessis §1.10;
Waldspurger 2010, §2.3, Lemme (i)): `J_M(m x m⁻¹, f) = J_M(x, f)` for `m ∈ M(F)`, when
`G_x(F) ⊆ M(F)` and the Haar measure on `G_{m x m⁻¹}(F) = m G_x(F) m⁻¹` is the transport of the one
on `G_x(F)` (the sources' measures, defined through the exponential, are so related).  Proof: the
change of variables `G_x g ↦ G_{m x m⁻¹} m g` carries `dg/μ` to `dg/μ'` (uniqueness of the Weil
measure), and `v_M(m g) = v_M(g)`. -/
theorem weightedOrbitalIntegral_conj (hM : d.centG x ≤ L.M) {m : ↥d.G} (hm : m ∈ L.M)
    (μ : Measure ↥(d.centG x)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (μ' : Measure ↥(d.centG (m * x * m⁻¹))) [μ'.IsHaarMeasure] [μ'.IsMulRightInvariant]
    (hμ : μ.map (d.centConj x m) = μ') (f : ↥d.G → ℂ) :
    d.weightedOrbitalIntegral L K (m * x * m⁻¹) μ' f = d.weightedOrbitalIntegral L K x μ f := by
  set ι := (d.centG x).subtype
  set ι' := (d.centG (m * x * m⁻¹)).subtype
  have hι : ∀ c, ι' (d.centConj x m c) = d.conjG m (ι c) := fun _ => rfl
  set ē := CosetSpace.mapHomeomorph ι ι' (d.centConj x m).toMulEquiv (d.conjG m) hι
  -- the Weil measure for `x'`
  have hW0 := (d.orbQuotMeasure_spec μ).map (d.centConj x m) (d.conjG m) hι
  rw [d.map_conjG_haar, hμ] at hW0
  have hW := hW0.map_mulRight m
  have hq := d.orbQuotMeasure_eq μ' hW
  -- `G_{x'} ⊆ M`
  have hM' : d.centG (m * x * m⁻¹) ≤ L.M := by
    intro c hc
    have : m⁻¹ * c * m ∈ d.centG x := ((d.centConj x m).symm ⟨c, hc⟩).2
    have h2 := L.M.mul_mem (L.M.mul_mem hm (hM this)) (L.M.inv_mem hm)
    simpa [mul_assoc] using h2
  have hpt : ∀ g, d.weightedIntegrand L K (m * x * m⁻¹) f (m * g) =
      d.weightedIntegrand L K x f g := by
    intro g
    unfold weightedIntegrand
    rw [show m * g = ((⟨m, hm⟩ : ↥L.M) : ↥d.G) * g from rfl, L.vM_mul_left]
    congr 2
    group
  unfold weightedOrbitalIntegral
  rw [weylDisc_conj, hq]
  congr 1
  rw [(CosetSpace.mulRight ι' m).measurableEmbedding.integral_map,
    ē.measurableEmbedding.integral_map]
  congr 1
  funext q
  have e : CosetSpace.mulRight ι' m (ē q) = CosetSpace.mk ι' (m * CosetSpace.out ι q) := by
    have h1 : ē q = CosetSpace.mk ι' (d.conjG m (CosetSpace.out ι q)) := by
      conv_lhs => rw [← CosetSpace.mk_out ι q]
      rfl
    rw [h1, CosetSpace.mulRight_mk, conjG_apply, inv_mul_cancel_right]
  rw [e, weightedIntegrand_out_mk hM', hpt]

end Conj

end GGPData

end GSpinGGP
