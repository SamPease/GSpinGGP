/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.BPGeomExpansion
import GSpinGGP.TraceFormula.WeylIntegrationL1

/-!
# `θ_f` on all of `G_reg(F)`: Beuzart-Plessis' formula

For `f ∈ C_c^∞(G(F))` strongly cuspidal, Beuzart-Plessis (Astérisque 418, §5.2, p. 109) and
Waldspurger (Compositio Math. 146 (2010), §5.3) define, for `x ∈ G_reg(F)`,
`θ_f(x) = (−1)^{a_G − a_{M(x)}} ν(G_x)⁻¹ D^G(x)^{−1/2} J_{M(x)}(x, f)`, the weighted orbital
integral being taken with a special maximal compact subgroup `K` in good position relative to
`M(x)`.  `ReducedLeviDatum.thetaFBP L K f x` is that formula for one presentation `(L, K)`.

`thetaF d f` evaluates the formula at every regular `x`, for a presentation chosen once for each
torus `G_x(F)` (`thetaPres`): a reduced Levi datum `L` with `L.M = M(x)` (`IsMx`) and a `GoodK`
for `L` that is special (`GoodK.IsSpecial`).  The choice depends on `G_x(F)` only, so `x` and
`a x` (`a ∈ A_G(F)`, which have the same centralizer) use the same presentation.  Off `G_reg(F)`,
and at a regular `x` without such a presentation, `thetaF d f x = 0`; neither case is read by any
statement about `θ_f` (they only see `G_reg(F)`, and every regular `x` has a presentation by
`exists_isMx` and `exists_specialK`).

The definition is the formula for every `f`, with no hypothesis.  For `f` strongly cuspidal in
`C_c^∞(G(F))`, the literature axioms (`Literature/BPThetaF.lean`) say that every special
presentation gives the same value (this includes presentations `L ≠ L'` of the same `M(x)`:
`waldspurger2010_lemme_5_3`, conjunct 1, is the only source of that independence here), so
`thetaF d f` is Beuzart-Plessis' `θ_f` (`isBPThetaF_thetaF`)
for `dg = Measure.haar`; and then `thetaF d f` represents the orbital pairing (`IsThetaF`,
`isThetaF_thetaF_of_cusp`): BP Thm 5.5.1(iv) gives `J^A(f, f') = ∫_{Γ(G)} D^{1/2} θ_f J_G(·, f')`,
and the Weyl integration formula (for `θ_f f' ∈ L¹`, `integral_mul_invariant`) turns the right
side into `∫_G θ_f f'`.

For `χ`-equivariant `f` (`ScuspTestFn`), which are not compactly supported, the axioms do not
apply; `TraceFormula/ThetaF.lean` reduces that case to the compactly supported one with two
pointwise identities, which hold for every `f` and need no axiom (the one-presentation versions
`thetaFBP_mul_AG`, `thetaFBP_mul_invariant` are in `TraceFormula/ThetaFBP.lean`):
`thetaF_mul_AG_of_isChiEquivariant` (`θ_f(a x) = χ(a)⁻¹ θ_f(x)`) and `thetaF_mul_invariant`
(`θ_{κ f} = κ θ_f` for conjugation-invariant `κ`).

## Main definitions

* `GGPData.thetaPres T`: a special presentation `(L, K)` of `M(x)` for the tori `T = G_x(F)`.
* `thetaF d f`: Beuzart-Plessis' `θ_f` by its formula, `0` off `G_reg(F)`.

## Main results

* `thetaF_eq_thetaFBP`: for `f ∈ C_c^∞` strongly cuspidal, `θ_f(x) = thetaFBP L K f x` for every
  special presentation `(L, K)` of `M(x)`.
* `isBPThetaF_thetaF`, `thetaF_conj_of_cusp`.
* `isThetaF_thetaF_of_cusp`: `thetaF d f` represents the orbital pairing and is a
  quasi-character.
* `thetaF_mul_AG_of_isChiEquivariant`, `thetaF_mul_invariant`, `thetaF_zero_fun`.
-/

noncomputable section

open MeasureTheory

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable {d : GGPData F}

/-! ## The chosen presentation -/

variable (d)

/-- A special presentation of `M(x)` exists for some regular `x` with `G_x(F) = T`. -/
def HasThetaPres (T : Subgroup ↥d.G) : Prop :=
  ∃ x ∈ regularSet d.G d.lie, d.centG x = T ∧
    ∃ (L : d.ReducedLeviDatum) (K : d.GoodK L.toFlagLeviDatum), L.IsMx x ∧ K.IsSpecial

open scoped Classical in
/-- **The presentation used by `thetaF`**, chosen once for each torus `T = G_x(F)`: a reduced
Levi datum `L` with `L.M = M(x)` (`IsMx`) and a `GoodK` for `L` that is special (special maximal
compact in good position relative to `L.M`, `GoodK.IsSpecial`), if there is one. -/
def thetaPres (T : Subgroup ↥d.G) : Option (Σ L : d.ReducedLeviDatum, d.GoodK L.toFlagLeviDatum) :=
  if h : d.HasThetaPres T then
    some ⟨h.choose_spec.2.2.choose, h.choose_spec.2.2.choose_spec.choose⟩
  else none

variable {d}

/-- What `thetaPres` chooses: a special presentation of `M(x)` for every regular `x` with
`G_x(F) = T`. -/
theorem thetaPres_spec {T : Subgroup ↥d.G} {p : Σ L : d.ReducedLeviDatum, d.GoodK L.toFlagLeviDatum}
    (hp : d.thetaPres T = some p) :
    p.2.IsSpecial ∧ ∀ x ∈ regularSet d.G d.lie, d.centG x = T → p.1.IsMx x := by
  classical
  unfold thetaPres at hp
  split_ifs at hp with h
  · cases hp
    obtain ⟨hMx, hK⟩ := h.choose_spec.2.2.choose_spec.choose_spec
    refine ⟨hK, fun x hx hxT' => hMx.of_centG_eq hx (hxT'.trans h.choose_spec.2.1.symm)⟩

theorem thetaPres_isSome {T : Subgroup ↥d.G} (h : d.HasThetaPres T) : (d.thetaPres T).isSome := by
  classical
  unfold thetaPres
  rw [dite_eq_left h]
  rfl

/-- Every regular `x` has a special presentation of `M(x)` (from the `sorry`s `exists_isMx` and
`exists_specialK`). -/
theorem hasThetaPres_centG {x : ↥d.G} (hx : x ∈ regularSet d.G d.lie) :
    d.HasThetaPres (d.centG x) := by
  obtain ⟨L, hL⟩ := ReducedLeviDatum.exists_isMx hx
  obtain ⟨K, hK⟩ := d.exists_specialK L
  exact ⟨x, hx, rfl, L, K, hL, hK⟩

end GGPData

/-! ## `θ_f` -/

variable (d : GGPData F)

open scoped Classical in
/-- **Beuzart-Plessis' `θ_f`** (Astérisque 418, §5.2, p. 109; Waldspurger 2010, §5.3), in
Beuzart-Plessis' normalization (not the introductory formula `(−1)^{a_{M(x)}} J_{M(x)}(x, f)` of
Thesis Ch. 1): at `x ∈ G_reg(F)`,
`θ_f(x) = (−1)^{a_G − a_{M(x)}} ν(G_x)⁻¹ D^G(x)^{−1/2} J_{M(x)}(x, f) = L.thetaFBP K f x`
for the special presentation `(L, K)` of `M(x)` chosen for the torus `G_x(F)` (`thetaPres`), with
`dg = Measure.haar` on `G(F)`; `0` off `G_reg(F)` (and at a regular `x` without special
presentation, which does not occur by `exists_isMx` and `exists_specialK`).

The formula is evaluated for every `f`.  For `f ∈ C_c^∞(G(F))` strongly cuspidal every special
presentation gives the same value (`thetaF_eq_thetaFBP`, from `waldspurger2010_lemme_5_3`) and
`thetaF d f` represents the orbital pairing (`isThetaF_thetaF_of_cusp`).  For
`f ∈ 𝒞_scusp(G, χ⁻¹)` it represents the orbital pairing (`thetaF_spec`,
`TraceFormula/ThetaF.lean`); independence of the presentation is not stated for such `f`.
Convention: `θ_f(ag) = χ(a)⁻¹ θ_f(g)` for `χ`-equivariant `f`, so
`θ_f` is matched with characters of representations with central character `χ⁻¹`. -/
def thetaF (f : ↥d.G → ℂ) (x : ↥d.G) : ℂ :=
  if x ∈ regularSet d.G d.lie then
    (d.thetaPres (d.centG x)).elim 0 fun p => p.1.thetaFBP p.2 f x
  else 0

variable {d}

theorem thetaF_of_not_mem {f : ↥d.G → ℂ} {x : ↥d.G} (hx : x ∉ regularSet d.G d.lie) :
    thetaF d f x = 0 := by
  rw [thetaF, ite_eq_right hx]

theorem thetaF_of_thetaPres {f : ↥d.G → ℂ} {x : ↥d.G} (hx : x ∈ regularSet d.G d.lie)
    {p : Σ L : d.ReducedLeviDatum, d.GoodK L.toFlagLeviDatum}
    (hp : d.thetaPres (d.centG x) = some p) : thetaF d f x = p.1.thetaFBP p.2 f x := by
  rw [thetaF, ite_eq_left hx, hp]
  rfl

theorem thetaF_of_thetaPres_none {f : ↥d.G → ℂ} {x : ↥d.G}
    (hp : d.thetaPres (d.centG x) = none) : thetaF d f x = 0 := by
  unfold thetaF
  split_ifs
  · rw [hp]; rfl
  · rfl

/-- `θ_0 = 0` (no hypothesis). -/
theorem thetaF_zero_fun : thetaF d 0 = 0 := by
  funext x
  unfold thetaF
  split_ifs
  · cases h : d.thetaPres (d.centG x) with
    | none => rfl
    | some p => exact GGPData.ReducedLeviDatum.thetaFBP_zero_fun p.2 x
  · rfl

/-- **`θ_{κ f} = κ θ_f`** for `κ` invariant under conjugation (no hypothesis on `f`). -/
theorem thetaF_mul_invariant {κ : ↥d.G → ℂ} (hκ : ∀ g y : ↥d.G, κ (g⁻¹ * y * g) = κ y)
    (f : ↥d.G → ℂ) (x : ↥d.G) : thetaF d (κ * f) x = κ x * thetaF d f x := by
  unfold thetaF
  split_ifs
  · cases d.thetaPres (d.centG x) with
    | none => simp
    | some p => exact GGPData.ReducedLeviDatum.thetaFBP_mul_invariant p.2 hκ f x
  · simp

/-- **`θ_f(a x) = χ(a)⁻¹ θ_f(x)`** for `χ`-equivariant `f` and `a ∈ A_G(F)`, at every `x`
(no strong cuspidality or support condition): `a x` and `x` have the same centralizer, hence the
same chosen presentation, and `a x` is regular iff `x` is. -/
theorem thetaF_mul_AG_of_isChiEquivariant (χ : CentralCharOn d) {f : ↥d.G → ℂ}
    (hf : IsChiEquivariant d χ f) (a : ↥d.AG) (x : ↥d.G) :
    thetaF d f ((a : ↥d.G) * x) = (((χ.toHom a)⁻¹ : Circle) : ℂ) * thetaF d f x := by
  have hreg : (a : ↥d.G) * x ∈ regularSet d.G d.lie ↔ x ∈ regularSet d.G d.lie := by
    refine ⟨fun h => ?_, fun h => mul_mem_regularSet_of_mem_AG d a h⟩
    have := mul_mem_regularSet_of_mem_AG d a⁻¹ h
    rwa [InvMemClass.coe_inv, inv_mul_cancel_left] at this
  unfold thetaF
  rw [d.centG_mul_AG x a.2]
  by_cases hx : x ∈ regularSet d.G d.lie
  · rw [ite_eq_left (hreg.2 hx), ite_eq_left hx]
    cases d.thetaPres (d.centG x) with
    | none => simp
    | some p => exact GGPData.ReducedLeviDatum.thetaFBP_mul_AG p.2 χ hf a x
  · rw [ite_eq_right (mt hreg.1 hx), ite_eq_right hx, mul_zero]

variable (d) in
/-- A locally integrable function times a test function is integrable. -/
theorem integrable_mul_testFunction {θ f' : ↥d.G → ℂ}
    (hθ : LocallyIntegrable θ (Measure.haar : Measure ↥d.G)) (hf' : f' ∈ testFunctions ↥d.G) :
    Integrable (fun g => θ g * f' g) (Measure.haar : Measure ↥d.G) := by
  simpa [mul_comm] using hθ.integrable_smul_left_of_hasCompactSupport hf'.1.continuous hf'.2

section Cusp

variable {f : ↥d.G → ℂ} (hf : f ∈ testFunctions ↥d.G) (hcusp : IsStronglyCuspidalInline d f)
include hf hcusp

/-- **`θ_f` is given by every special presentation**, for `f ∈ C_c^∞(G(F))` strongly cuspidal:
`θ_f(x) = thetaFBP L K f x` for `x ∈ G_reg(F)`, `IsMx L x` and `K` special (Waldspurger 2010,
§5.2 Lemme (i) and §5.3 Lemme: `waldspurger2010_lemme_5_3`, with `y = 1`). -/
theorem thetaF_eq_thetaFBP {x : ↥d.G} (hx : x ∈ regularSet d.G d.lie)
    {L : d.ReducedLeviDatum} {K : d.GoodK L.toFlagLeviDatum} (hL : L.IsMx x) (hK : K.IsSpecial) :
    thetaF d f x = L.thetaFBP K f x := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (GGPData.thetaPres_isSome
    ⟨x, hx, rfl, L, K, hL, hK⟩)
  obtain ⟨hpK, hpL⟩ := GGPData.thetaPres_spec hp
  rw [thetaF_of_thetaPres hx hp]
  have := (waldspurger2010_lemme_5_3 d hf hcusp).1 x 1 p.1 L p.2 K (hpL x hx rfl)
    (by simpa using hL) hpK hK
  simpa using this.symm

/-- **`thetaF d f` is Beuzart-Plessis' `θ_f`** (`IsBPThetaF`), for `f ∈ C_c^∞(G(F))` strongly
cuspidal: special presentations exist at every regular `x` (`exists_isMx`, `exists_specialK`) and
all give `thetaF d f x` (`thetaF_eq_thetaFBP`). -/
theorem isBPThetaF_thetaF : d.IsBPThetaF f (thetaF d f) := fun x hx => by
  obtain ⟨y, -, hy, L, K, hL, hK⟩ := GGPData.hasThetaPres_centG hx
  refine ⟨⟨L, K, hL.of_centG_eq hx hy.symm, hK⟩, fun L K hL hK => ?_⟩
  exact thetaF_eq_thetaFBP hf hcusp hx hL hK

/-- **`θ_f` is invariant by conjugation** on `G_reg(F)`, for `f ∈ C_c^∞(G(F))` strongly cuspidal
(Waldspurger 2010, §5.3 Lemme, `waldspurger2010_lemme_5_3`). -/
theorem thetaF_conj_of_cusp (g x : ↥d.G) (hx : x ∈ regularSet d.G d.lie) :
    thetaF d f (g * x * g⁻¹) = thetaF d f x := by
  have hx' := conj_mem_regularSet d g x hx
  obtain ⟨y, -, hy, L, K, hL, hK⟩ := GGPData.hasThetaPres_centG hx
  obtain ⟨y', -, hy', L', K', hL', hK'⟩ := GGPData.hasThetaPres_centG hx'
  rw [thetaF_eq_thetaFBP hf hcusp hx (hL.of_centG_eq hx hy.symm) hK,
    thetaF_eq_thetaFBP hf hcusp hx' (hL'.of_centG_eq hx' hy'.symm) hK']
  exact (waldspurger2010_lemme_5_3 d hf hcusp).1 x g L L' K K' (hL.of_centG_eq hx hy.symm)
    (hL'.of_centG_eq hx' hy'.symm) hK hK'

/-- `θ_f` is locally integrable and continuous on `G_reg(F)` (`waldspurger2010_lemme_5_3`). -/
theorem locallyIntegrable_thetaF_of_cusp :
    LocallyIntegrable (thetaF d f) (Measure.haar : Measure ↥d.G) ∧
      ContinuousOn (thetaF d f) (regularSet d.G d.lie) :=
  (waldspurger2010_lemme_5_3 d hf hcusp).2 _ (isBPThetaF_thetaF hf hcusp)

/-- **`θ_f` represents the orbital pairing** and is a quasi-character, for `f ∈ C_c^∞(G(F))`
strongly cuspidal (BP Thm 5.5.1(iv) and the Weyl integration formula; BP Prop 5.6.1(ii),
Waldspurger 2010, §5.9 Corollaire; Thesis Thm 4.7.1, Prop 4.8.1).

Proof: `θ_f` is locally integrable and continuous on `G_reg(F)` (W1 §5.3).  For
`f' ∈ C_c^∞(G(F))`,
`⟨f, f'⟩ = J^A(f, f') = Σ_T |W(G,T)|⁻¹ ∫_{T(F)} θ_f(t) D^G(t)^{1/2} J_G(t, f') dt`
(BP Thm 5.5.1(iv), `jA_eq_gammaIntegral`), and since `θ_f` is conjugation invariant on `G_reg(F)`
and `θ_f f'` is integrable, the Weyl integration formula (`integral_mul_invariant`) identifies the
right side with `∫_G θ_f f' dg`.  The quasi-character property is W1 Cor 5.9. -/
theorem isThetaF_thetaF_of_cusp :
    IsThetaF d f (thetaF d f) ∧
      ∀ ψ : NontrivialAddChar F, IsQuasiCharacter d.G d.lie d.bilin ψ (thetaF d f) := by
  obtain ⟨hli, hc⟩ := locallyIntegrable_thetaF_of_cusp hf hcusp
  refine ⟨⟨hli, hc, fun f' hf' => ?_⟩,
    waldspurger2010_cor_5_9 d hf hcusp _ (isBPThetaF_thetaF hf hcusp)⟩
  obtain ⟨μ, hμ, -⟩ := bp_thm_5_5_1_iv d
  have hinv : ∀ t ∈ regularSet d.G d.lie, ∀ g : ↥d.G, thetaF d f (g⁻¹ * t * g) = thetaF d f t :=
    fun t ht g => by simpa using thetaF_conj_of_cusp hf hcusp g⁻¹ t ht
  rw [d.integral_mul_invariant μ hμ hinv (integrable_mul_testFunction d hli hf'),
    ← d.jA_eq_orbitalPairing,
    (d.jA_eq_gammaIntegral μ hμ hf hcusp (isBPThetaF_thetaF hf hcusp) hf').2.2]
  rfl

end Cusp

end GSpinGGP
