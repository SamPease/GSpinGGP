/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Interface
import GSpinGGP.Literature.GeomMult

/-!
# `m_geom` on quasi-characters: Thesis Prop 12.1.1

The statements in §1 are the interface consumed by
`Spine.lean` and `Main.lean`; all five are proved here from §0.  §2 is proved from §1.

* `tendsto_mGeomS`, `mGeomS_add`, `mGeomS_smul` (Thesis Prop 12.1.1(i)):
  for `θ` in the span `QCfin d` of the `QC(G, χ)`, the integrals `m_{geom,s}(θ)` converge
  absolutely for `s > 0` (hence are linear in `θ`), and the limit `s → 0⁺` exists.  §0b proves
  these from the precisely stated inputs `finite_gammaClass`, `germ_bound_of_mem_QC` (BP Prop
  4.5.1), `aestronglyMeasurable_torusFn_of_mem_QC`, `integrable_delta_rpow` (BP Lemma B.1.2(i)
  plus the eigenvalues of `t` on `W''`) and `tendsto_mGeomS_of_mem_QC` (the thesis's induction for
  one `χ`).  `integrable_delta_rpow` is proved from the literature axiom
  `bp_integrable_deltaGGP_rpow` (the GSpin consequence of B.1.2(i); B.1.2(i) itself is about
  algebraic characters of a torus, which are not available here); the others are SORRY.
  `mGeomS_smul` needs no input.
* `mGeom_congr_regularSet`: `m_geom(θ)` depends only on `θ|_{G_reg}` (germs only see the regular
  set, by `exists_nhds_mul_expA_mem_regularSet`).
* `charG_mem_QC`: `θ_π ∈ QC(G, η⁻¹)`-in-Lean-convention, i.e. `charG d π ∈ QC d η.inv`, for `π`
  tempered with central character `η` on `A_G(F)` (generalize `Main.charG_diag_scalar_mul`).
* Proved here: `tendsto_mGeomS_mGeom`, `mGeom_add`, `mGeom_smul`, `mGeom_finset_sum_of_mem`,
  `vChar_mem_QC`.
-/

noncomputable section

open MeasureTheory Topology Filter

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
variable (ψ : NontrivialAddChar F) (d : GGPData F)

/-! ## 0. Helpers

### 0a. Algebra of the integrand `gammaIntegrand` -/

section IntegrandAlgebra

/-- Elements of `QCfin d` are quasi-characters (for every `ψ`): the quasi-characters form a
submodule containing every `QC d χ`. -/
theorem isQuasiCharacter_of_mem_QCfin {θ : ↥d.G → ℂ} (hθ : θ ∈ QCfin d) (ψ' : NontrivialAddChar F) :
    IsQuasiCharacter d.G d.lie d.bilin ψ' θ := by
  let S : Submodule ℂ (↥d.G → ℂ) :=
    { carrier := {θ | ∀ ψ' : NontrivialAddChar F, IsQuasiCharacter d.G d.lie d.bilin ψ' θ}
      add_mem' := fun h₁ h₂ ψ' => isQuasiCharacter_add d ψ' (h₁ ψ') (h₂ ψ')
      zero_mem' := fun ψ' => isQuasiCharacter_zero d ψ'
      smul_mem' := fun c _ h ψ' => isQuasiCharacter_smul d ψ' c (h ψ') }
  have hle : QCfin d ≤ S := iSup_le fun χ _ h => h.1
  exact hle hθ ψ'

/-- **`x ∈ GSpin(W)(F)` semisimple ⇒ `diag x = (x, x)` semisimple in `C(W) × C(V)`**: the
squarefree minimal polynomial `p` of `x` kills `x` in `C(W)`, hence its image under the algebra
map `C(W) → C(V)`, hence the pair. -/
theorem isSS_diag_of_isSS {t : ↥(GSpin d.QW)}
    (ht : IsSS F (((t : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW)) :
    IsSS F (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient) := by
  set a : CliffordAlgebra d.QW := ((t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)
  set p := minpoly F (LinearMap.mulLeft F a)
  have hsq : Squarefree p := Module.End.IsSemisimple.minpoly_squarefree ht
  have h0 : Polynomial.aeval (Algebra.lmul F (CliffordAlgebra d.QW) a) p = 0 := minpoly.aeval F _
  rw [Polynomial.aeval_algHom_apply] at h0
  have h1 : Polynomial.aeval a p = 0 :=
    Algebra.lmul_injective (R := F) (h0.trans (map_zero _).symm)
  set φ := CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
  have hcoe : (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient) = (a, φ a) := rfl
  have h2 : Polynomial.aeval (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient) p = 0 := by
    rw [hcoe]
    refine Prod.ext ?_ ?_
    · have := Polynomial.aeval_algHom_apply (AlgHom.fst F (CliffordAlgebra d.QW)
        (CliffordAlgebra d.QV)) (a, φ a) p
      simp only [AlgHom.fst_apply] at this
      rw [Prod.fst_zero, ← this, h1]
    · have := Polynomial.aeval_algHom_apply (AlgHom.snd F (CliffordAlgebra d.QW)
        (CliffordAlgebra d.QV)) (a, φ a) p
      simp only [AlgHom.snd_apply] at this
      rw [Prod.snd_zero, ← this, Polynomial.aeval_algHom_apply, h1, map_zero]
  have h3 : Polynomial.aeval (Algebra.lmul F d.ambient
      (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient)) p = 0 := by
    rw [Polynomial.aeval_algHom_apply, h2, map_zero]
  exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq h3

/-- Points of `Γ(G,H)` are semisimple in `G`. -/
theorem isSS_diag_of_isGammaElt {t : ↥(GSpin d.QW)} (ht : d.IsGammaElt t) :
    IsSS F (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient) :=
  isSS_diag_of_isSS d ht.1

/-- A local expansion of `θ` at a semisimple `x` is one of every `θ'` agreeing with `θ` on
`G_reg(F)`: the expansion is only evaluated at `x e^X` with `X ∈ 𝔤_x` small and regular, which is
regular in `G` (`exists_nhds_mul_expA_mem_regularSet`). -/
theorem hasGermExpansion_congr_regularSet {θ θ' : ↥d.G → ℂ}
    (heq : Set.EqOn θ θ' (regularSet d.G d.lie)) {x : ↥d.G}
    (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    {c : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) → ℂ}
    (h : HasGermExpansion d.G d.lie d.bilin ψ θ x c) :
    HasGermExpansion d.G d.lie d.bilin ψ θ' x c := by
  obtain ⟨hfin, ω, hω, hexp⟩ := h
  obtain ⟨ω', hω', hreg⟩ := exists_nhds_mul_expA_mem_regularSet d x hx
  refine ⟨hfin, ω ∩ ω', inter_mem hω hω', fun X hX hXc hXr y hy => ?_⟩
  rw [← heq (hreg X hX.2 hXc hXr y hy)]
  exact hexp X hX.1 hXc hXr y hy

/-- **Germs only see `G_reg(F)`** (Thesis §4.1.1, §4.2): at a semisimple `x`, `c_{θ,O}(x)` depends
only on `θ|_{G_reg(F)}`.  On `Nil_reg(𝔤_x)` both germs are the coefficient of a common local
expansion (uniqueness, `germ_eq_of_hasGermExpansion`); off it both vanish. -/
theorem germ_congr_regularSet {θ θ' : ↥d.G → ℂ} (heq : Set.EqOn θ θ' (regularSet d.G d.lie))
    {x : ↥d.G} (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    (O : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))) :
    germ d.G d.lie d.bilin ψ θ x O = germ d.G d.lie d.bilin ψ θ' x O := by
  by_cases hO : O ∈ NilReg (grpCentralizer d.G x)
      (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))
  · by_cases h : ∃ c, HasGermExpansion d.G d.lie d.bilin ψ θ x c
    · obtain ⟨c, hc⟩ := h
      rw [germ_eq_of_hasGermExpansion d ψ hx hc hO,
        germ_eq_of_hasGermExpansion d ψ hx (hasGermExpansion_congr_regularSet ψ d heq hx hc) hO]
    · have h' : ¬ ∃ c, HasGermExpansion d.G d.lie d.bilin ψ θ' x c := fun ⟨c, hc⟩ =>
        h ⟨c, hasGermExpansion_congr_regularSet ψ d heq.symm hx hc⟩
      simp only [germ, hO, h, h', ↓reduceIte, ↓reduceDIte]
  · rw [germ_of_not_mem hO, germ_of_not_mem hO]

/-- The integrand of `m_{geom,s}` only sees `θ|_{G_reg(F)}`. -/
theorem gammaIntegrand_congr_regularSet {θ θ' : ↥d.G → ℂ}
    (heq : Set.EqOn θ θ' (regularSet d.G d.lie)) (T : Subgroup ↥(GSpin d.QW)) (s : ℝ)
    (t : ↥(GSpin d.QW)) : gammaIntegrand ψ d θ T s t = gammaIntegrand ψ d θ' T s t := by
  unfold gammaIntegrand
  split_ifs with h
  · rw [germ_congr_regularSet ψ d heq (isSS_diag_of_isGammaElt d h.1)]
  · rfl

/-- The integrand of `m_{geom,s}` is additive on quasi-characters (`germ_add`). -/
theorem gammaIntegrand_add {θ₁ θ₂ : ↥d.G → ℂ} (h₁ : IsQuasiCharacter d.G d.lie d.bilin ψ θ₁)
    (h₂ : IsQuasiCharacter d.G d.lie d.bilin ψ θ₂) (T : Subgroup ↥(GSpin d.QW)) (s : ℝ)
    (t : ↥(GSpin d.QW)) :
    gammaIntegrand ψ d (θ₁ + θ₂) T s t =
      gammaIntegrand ψ d θ₁ T s t + gammaIntegrand ψ d θ₂ T s t := by
  unfold gammaIntegrand
  split_ifs with h
  · have hx := isSS_diag_of_isGammaElt d h.1
    by_cases hO : orbitChoice d t ∈ NilReg (grpCentralizer d.G (d.diag t : d.ambientˣ))
        (lieCentralizer d.lie (((d.diag t : d.ambientˣ)) : d.ambient))
    · rw [germ_add d ψ hx (h₁.2 _ hx) (h₂.2 _ hx) hO]; ring
    · rw [germ_of_not_mem hO, germ_of_not_mem hO, germ_of_not_mem hO]; ring
  · simp

/-- The integrand of `m_{geom,s}` is homogeneous on quasi-characters (`germ_smul`). -/
theorem gammaIntegrand_smul (c : ℂ) {θ : ↥d.G → ℂ} (hθ : IsQuasiCharacter d.G d.lie d.bilin ψ θ)
    (T : Subgroup ↥(GSpin d.QW)) (s : ℝ) (t : ↥(GSpin d.QW)) :
    gammaIntegrand ψ d (c • θ) T s t = c * gammaIntegrand ψ d θ T s t := by
  unfold gammaIntegrand
  split_ifs with h
  · have hx := isSS_diag_of_isGammaElt d h.1
    by_cases hO : orbitChoice d t ∈ NilReg (grpCentralizer d.G (d.diag t : d.ambientˣ))
        (lieCentralizer d.lie (((d.diag t : d.ambientˣ)) : d.ambient))
    · rw [germ_smul d ψ hx c (hθ.2 _ hx) hO]; ring
    · rw [germ_of_not_mem hO, germ_of_not_mem hO]; ring
  · simp

/-- The integrand of `m_{geom,s}` vanishes for `θ = 0` (`germ_zero`). -/
theorem gammaIntegrand_zero (T : Subgroup ↥(GSpin d.QW)) (s : ℝ) (t : ↥(GSpin d.QW)) :
    gammaIntegrand ψ d 0 T s t = 0 := by
  unfold gammaIntegrand
  split_ifs with h
  · have hx := isSS_diag_of_isGammaElt d h.1
    by_cases hO : orbitChoice d t ∈ NilReg (grpCentralizer d.G (d.diag t : d.ambientˣ))
        (lieCentralizer d.lie (((d.diag t : d.ambientˣ)) : d.ambient))
    · rw [germ_zero d ψ hx hO]; ring
    · rw [germ_of_not_mem hO]; ring
  · rfl

/-- `m_{geom,s}` is homogeneous on quasi-characters, for every `s` (no convergence needed:
`∫ c f = c ∫ f` and `∑' c a = c ∑' a` hold unconditionally in `ℂ`). -/
theorem mGeomS_smul_of_isQuasiCharacter (c : ℂ) {θ : ↥d.G → ℂ}
    (hθ : IsQuasiCharacter d.G d.lie d.bilin ψ θ) (s : ℝ) :
    mGeomS ψ d (c • θ) s = c * mGeomS ψ d θ s := by
  unfold mGeomS torusIntegral
  rw [← tsum_mul_left]
  refine tsum_congr fun c' => ?_
  simp only [gammaIntegrand_smul ψ d c hθ, integral_const_mul]
  ring

/-- `m_{geom,s}(0) = 0`. -/
theorem mGeomS_zero (s : ℝ) : mGeomS ψ d 0 s = 0 := by
  simpa using mGeomS_smul_of_isQuasiCharacter ψ d 0 (isQuasiCharacter_zero d ψ) s

/-- `m_{geom,s}(θ) = m_{geom,s}(θ')` whenever `θ = θ'` on `G_reg(F)`. -/
theorem mGeomS_congr_regularSet {θ θ' : ↥d.G → ℂ} (h : Set.EqOn θ θ' (regularSet d.G d.lie)) :
    mGeomS ψ d θ = mGeomS ψ d θ' := by
  funext s
  unfold mGeomS torusIntegral
  simp only [gammaIntegrand_congr_regularSet ψ d h]

end IntegrandAlgebra

/-! ### 0b. Absolute convergence of `m_{geom,s}` (Thesis (12.1.2)) and the limit

The thesis proves (12.1.2) for one `θ ∈ QC(G(F), χ)` as follows (Thesis Prop 12.1.1(i), following
BP Astérisque 418, proof of Prop 11.2.1, (11.2.6)): `Γ(G,H)` is compact modulo conjugation, the
function `(D^G)^{1/2} c_{θ,O}` is locally bounded (BP Prop 4.5.1), so it suffices that
`∫_{Γ(G,H)} Δ(x)^{s - 1/2} dx` converges for `Re s > 0`, which is BP Lemma B.1.2(i).

Here that argument is split torus by torus into three precisely stated inputs (the first two
SORRY, the third proved from the axiom `bp_integrable_deltaGGP_rpow`), whose combination is proved
(`isTorusIntegrable_of_mem_QC`):
* `germ_bound_of_mem_QC`: `‖D^G(t)^{1/2} c_{θ,O_t}(t)‖ ≤ C` on `T_♮`;
* `aestronglyMeasurable_torusFn_of_mem_QC`: measurability of the integrand on `T(F)/A_{G,H}(F)`;
* `integrable_delta_rpow`: `∫_{T(F)/A_{G,H}(F)} 1_{T_♮} Δ^{s - 1/2} < ∞` for `s > 0`
  (BP Lemma B.1.2(i), applied to the eigencharacters of `t` on `W''`).
Together with `finite_gammaClass` (`Γ(G,H)` meets finitely many tori up to conjugacy) this gives
additivity of `m_{geom,s}` on `QCfin d`.  The existence of the limit for one `χ`
(`tendsto_mGeomS_of_mem_QC`, Thesis (12.1.4)) is the thesis's inductive argument and stays a
SORRY; the `QCfin` forms are then proved by linearity (submodules `qcGood`, `qcLim`). -/

section Convergence

/-- **`Γ(G,H)` meets finitely many conjugacy classes of tori** (Thesis §6.5:
"finite for `p`-adic `F`").  Why: `T_x = P^{-1}(Z_{SO(W''_x)}(x̄))` is determined by the
nondegenerate subspace `W''_x` (finitely many up to `SO(W)`, Witt) and the maximal torus
`Z_{SO(W''_x)}(x̄)^0` of `SO(W''_x)` (finitely many `SO(W''_x)(F)`-conjugacy classes of maximal tori
over a `p`-adic field: they are classified by étale algebras of bounded degree with finitely many
`H¹`-twists).  Status: SORRY (own work, GSpin input; consistent with
`toyD_subsingleton_gammaClass`). -/
theorem finite_gammaClass : Finite (GammaClass d) := by
  sorry

/-- **Local boundedness of `(D^G)^{1/2} c_{θ,O}` on `T_♮`** (BP Astérisque 418, Prop 4.5.1: for
`θ ∈ QC(G(F))`, `(D^G)^{1/2} c_θ` is locally bounded on `G(F)`; same proof for the individual
`c_{θ,O}`, `O ∈ Nil_reg(𝔤_x)`; Thesis Prop 12.1.1(i), proof of (12.1.2)).  The bound is global
on `T_♮ = {t | t ∈ Γ(G,H), T_t = T}` because `T(F) = A_{G,H}(F)·K` for a compact `K`
(`T(F)/A_{G,H}(F)` is compact, part of `IsGammaElt`) and the integrand is `A_{G,H}(F)`-invariant
(`χ` is trivial on `A_{G,H}(F)`, so `θ(ag) = θ(g)` on `G_reg(F)` and germs at `x` and `ax` agree).
BP Prop 4.5.1 is stated for the averaged `c_θ`; the bound for each individual `c_{θ,O}` is the
thesis's own reading of it, so this is an assumption of the thesis, not a citation of BP.
Status: SORRY (own work from BP Prop 4.5.1, GSpin input). -/
theorem germ_bound_of_mem_QC {χ : CentralCharOn d} {θ : ↥d.G → ℂ} (hθ : θ ∈ QC d χ)
    (T : Subgroup ↥(GSpin d.QW)) :
    ∃ C : ℝ, ∀ t : ↥(GSpin d.QW), d.IsGammaElt t → d.torusOf t = T →
      ‖(Real.sqrt (weylDisc d.lie (d.diag t : d.ambientˣ)) : ℂ) *
        germ d.G d.lie d.bilin ψ θ (d.diag t) (orbitChoice d t)‖ ≤ C := by
  sorry

/-- **Measurability of the integrand of `m_{geom,s}` on `T(F)/A_{G,H}(F)`** (Thesis §6.5, the
measure on `Γ(G,H)`).  Why: for `θ ∈ QC d χ` the integrand
`t ↦ D^G(t)^{1/2} c_{θ,O_t}(t) Δ(t)^{s-1/2}` is `A_{G,H}(F)`-invariant (see
`germ_bound_of_mem_QC`), so evaluating it on the representatives `Quotient.out q` gives the
descended function; `T_♮` is open in `T(F)` (no new eigenvalue `1` on `W''` and `Z(t) = T` are
open conditions on `T(F)`), the germs `c_{θ,O_t}(t)` are locally constant on `T_♮` (for `t' = t e^Y`, `Y ∈ Lie T` central in `𝔤_t`, the expansions at `t` and `t'`
coincide), and `D^G`, `Δ` are continuous; so the descended function is continuous on the open
image of `T_♮` and `0` off it.  Status: SORRY (own work, GSpin input). -/
theorem aestronglyMeasurable_torusFn_of_mem_QC {χ : CentralCharOn d} {θ : ↥d.G → ℂ}
    (hθ : θ ∈ QC d χ) (T : Subgroup ↥(GSpin d.QW)) (s : ℝ) :
    letI : MeasurableSpace (d.TorusQuot T) := borel _
    haveI : BorelSpace (d.TorusQuot T) := ⟨rfl⟩
    AEStronglyMeasurable (fun q : d.TorusQuot T =>
      gammaIntegrand ψ d θ T s ((Quotient.out q : ↥T) : ↥(GSpin d.QW)))
      (probHaar (d.TorusQuot T)) := by
  sorry

/-- **`∫_{T(F)/A_{G,H}(F)} 1_{T_♮}(t) Δ(t)^{s-1/2} dt < ∞` for `s > 0`** (Thesis Prop 12.1.1(i),
proof of (12.1.2): "a straightforward application of BP Lemma B.1.2(i)").

BP Astérisque 418, Lemma B.1.2(i): for a torus `T` over `F` and linearly independent
`χ_1, …, χ_n ∈ X^*(T)`, the function `t ↦ ∏ |χ_i(t) − 1|^{s−1}` is locally integrable on `T(F)`
for `Re s > 0`.  The GSpin reduction: on `T_♮`, `P(t)|_{W''}` has eigenvalues `λ_i^{±1}`
(`1 ≤ i ≤ n = dim W''/2`, all of absolute value `1` as `T(F)/A_{G,H}(F)` is compact), `λ_1, …, λ_n`
are linearly independent characters of `T`, and `Δ(t) = ∏ |λ_i(t) − 1|·|λ_i(t)^{-1} − 1| =
∏ |λ_i(t) − 1|²`, so `Δ^{s−1/2} = ∏ |λ_i − 1|^{2s − 1}` (B.1.2(i) with `2s`); local integrability on
`T(F)` descends to integrability on the compact `T(F)/A_{G,H}(F)` (`Δ` is `A_{G,H}(F)`-invariant).

B.1.2(i) itself is not an axiom: it quantifies over *algebraic* characters of an `F`-torus, which
this development cannot express, and the naive version for continuous characters is false.
Its GSpin consequence for the `Γ`-tori `T = T_x` is the literature
axiom `bp_integrable_deltaGGP_rpow`; for any other subgroup `T` the integrand is `0`.
Status: proved from `bp_integrable_deltaGGP_rpow`. -/
theorem integrable_delta_rpow (T : Subgroup ↥(GSpin d.QW)) {s : ℝ} (hs : 0 < s) :
    letI : MeasurableSpace (d.TorusQuot T) := borel _
    haveI : BorelSpace (d.TorusQuot T) := ⟨rfl⟩
    Integrable (fun q : d.TorusQuot T =>
      Set.indicator {t : ↥(GSpin d.QW) | d.IsGammaElt t ∧ d.torusOf t = T}
        (fun t => deltaGGP d t ^ (s - 1 / 2)) ((Quotient.out q : ↥T) : ↥(GSpin d.QW)))
      (probHaar (d.TorusQuot T)) := by
  by_cases h : ∃ x, d.IsGammaElt x ∧ d.torusOf x = T
  · obtain ⟨x, hx, rfl⟩ := h
    exact bp_integrable_deltaGGP_rpow d hx hs
  · let _ : MeasurableSpace (d.TorusQuot T) := borel _
    have : BorelSpace (d.TorusQuot T) := ⟨rfl⟩
    have h0 : (fun q : d.TorusQuot T =>
        Set.indicator {t : ↥(GSpin d.QW) | d.IsGammaElt t ∧ d.torusOf t = T}
          (fun t => deltaGGP d t ^ (s - 1 / 2)) ((Quotient.out q : ↥T) : ↥(GSpin d.QW))) =
        fun _ => 0 :=
      funext fun q => Set.indicator_of_notMem
        (s := {t : ↥(GSpin d.QW) | d.IsGammaElt t ∧ d.torusOf t = T}) (fun ht => h ⟨_, ht⟩) _
    rw [h0]
    exact integrable_zero _ _ _

/-- `T_1(F)/A_{G,H}(F)` is a point: `T_1 = {g | P(g) = 1} = F^×` (`ker_specP`). -/
theorem subsingleton_torusQuot_torusOf_one : Subsingleton (d.TorusQuot (d.torusOf 1)) := by
  have hker : ∀ g ∈ d.torusOf 1, g ∈ (scalarGSpin d.QW).range := by
    intro g hg
    rw [← ker_specP d.nondeg, MonoidHom.mem_ker]
    refine LinearEquiv.ext fun w => ?_
    refine (Subgroup.mem_inf.mp hg).2 w ?_
    rw [fixedSub, map_one, LinearMap.mem_ker]
    simp
  refine ⟨fun x y => ?_⟩
  induction x using QuotientGroup.induction_on with | H a => ?_
  induction y using QuotientGroup.induction_on with | H b => ?_
  rw [QuotientGroup.eq]
  obtain ⟨c, hc⟩ := hker _ (a⁻¹ * b).2
  exact Subgroup.mem_subgroupOf.mpr ⟨c, hc⟩

/-- **Consistency check of `bp_integrable_deltaGGP_rpow` at `x = 1`** (a point of `Γ(G,H)` for
every `d`): its conclusion holds outright, for every `s`, since `T_1(F)/A_{G,H}(F)` is a point and
the probability Haar measure is finite.  (For `toyData`, and for `dim W ≤ 2` with `W` split, every
torus of `Γ(G,H)` is `T_1`; the content of the axiom is `dim W''_x ≥ 2` anisotropic modulo the
centre.) -/
theorem integrable_delta_rpow_torusOf_one (s : ℝ) :
    letI : MeasurableSpace (d.TorusQuot (d.torusOf 1)) := borel _
    haveI : BorelSpace (d.TorusQuot (d.torusOf 1)) := ⟨rfl⟩
    Integrable (fun q : d.TorusQuot (d.torusOf 1) =>
      Set.indicator {t : ↥(GSpin d.QW) | d.IsGammaElt t ∧ d.torusOf t = d.torusOf 1}
        (fun t => deltaGGP d t ^ (s - 1 / 2))
        ((Quotient.out q : ↥(d.torusOf 1)) : ↥(GSpin d.QW)))
      (probHaar (d.TorusQuot (d.torusOf 1))) := by
  let _ : MeasurableSpace (d.TorusQuot (d.torusOf 1)) := borel _
  have : BorelSpace (d.TorusQuot (d.torusOf 1)) := ⟨rfl⟩
  have := subsingleton_torusQuot_torusOf_one d
  have : CompactSpace (d.TorusQuot (d.torusOf 1)) := Finite.compactSpace
  have : IsFiniteMeasure (probHaar (d.TorusQuot (d.torusOf 1))) := by
    unfold probHaar
    rw [dite_eq_left_of_eq_true (eq_true ‹_›)]
    infer_instance
  set f := fun q : d.TorusQuot (d.torusOf 1) =>
    Set.indicator {t : ↥(GSpin d.QW) | d.IsGammaElt t ∧ d.torusOf t = d.torusOf 1}
      (fun t => deltaGGP d t ^ (s - 1 / 2)) ((Quotient.out q : ↥(d.torusOf 1)) : ↥(GSpin d.QW))
  have hf : f = fun _ => f 1 := funext fun q => congrArg f (Subsingleton.elim _ _)
  rw [hf]
  exact integrable_const _

/-- **Thesis Prop 12.1.1(i), (12.1.4): the limit `lim_{s → 0⁺} m_{geom,s}(θ)` exists for
`θ ∈ QC(G(F), χ)`** (BP Astérisque 418, Prop 11.2.1(i)).  The thesis's proof
is an induction on `dim G`: away from `1` by semisimple descent to `G_x = G'_x × G''_x`
((12.1.6)–(12.1.8), BP Lemma 11.1.1, BP Prop 4.4.1(v), the uniform boundedness principle,
BP Appendix A), near `1` by descent to the Lie algebra and homogeneity ((12.1.9)–(12.1.15), BP
Lemma 11.1.2 and Lemma B.1.2(ii)).  Status: SORRY (own work, the thesis's induction). -/
theorem tendsto_mGeomS_of_mem_QC {χ : CentralCharOn d} {θ : ↥d.G → ℂ} (hθ : θ ∈ QC d χ) :
    ∃ L : ℂ, Tendsto (mGeomS ψ d θ) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  sorry

/-- The integrand of `m_{geom,s}` is integrable on `T(F)/A_{G,H}(F)` (for the measure used by
`torusIntegral`). -/
def IsTorusIntegrable (θ : ↥d.G → ℂ) (T : Subgroup ↥(GSpin d.QW)) (s : ℝ) : Prop :=
  letI : MeasurableSpace (d.TorusQuot T) := borel _
  haveI : BorelSpace (d.TorusQuot T) := ⟨rfl⟩
  Integrable (fun q : d.TorusQuot T =>
    gammaIntegrand ψ d θ T s ((Quotient.out q : ↥T) : ↥(GSpin d.QW))) (probHaar (d.TorusQuot T))

/-- **Thesis (12.1.2), torus by torus**: for `θ ∈ QC d χ` and `s > 0` the integrand of
`m_{geom,s}(θ)` is integrable on each `T(F)/A_{G,H}(F)`, bounded by `C · 1_{T_♮} Δ^{s-1/2}`. -/
theorem isTorusIntegrable_of_mem_QC {χ : CentralCharOn d} {θ : ↥d.G → ℂ} (hθ : θ ∈ QC d χ)
    (T : Subgroup ↥(GSpin d.QW)) {s : ℝ} (hs : 0 < s) : IsTorusIntegrable ψ d θ T s := by
  obtain ⟨C, hC⟩ := germ_bound_of_mem_QC ψ d hθ T
  let _ : MeasurableSpace (d.TorusQuot T) := borel _
  have : BorelSpace (d.TorusQuot T) := ⟨rfl⟩
  refine Integrable.mono' ((integrable_delta_rpow d T hs).const_mul C)
    (aestronglyMeasurable_torusFn_of_mem_QC ψ d hθ T s) (Eventually.of_forall fun q => ?_)
  set t : ↥(GSpin d.QW) := ((Quotient.out q : ↥T) : ↥(GSpin d.QW))
  by_cases h : d.IsGammaElt t ∧ d.torusOf t = T
  · have hΔ : 0 ≤ deltaGGP d t ^ (s - 1 / 2) := Real.rpow_nonneg (absF_nonneg _) _
    have hind : Set.indicator {t : ↥(GSpin d.QW) | d.IsGammaElt t ∧ d.torusOf t = T}
        (fun t => deltaGGP d t ^ (s - 1 / 2)) t = deltaGGP d t ^ (s - 1 / 2) :=
      Set.indicator_of_mem (s := {t : ↥(GSpin d.QW) | d.IsGammaElt t ∧ d.torusOf t = T}) h _
    have hCt := hC t h.1 h.2
    simp only [gammaIntegrand, h, and_self, ↓reduceIte, hind, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hΔ] at hCt ⊢
    exact mul_le_mul_of_nonneg_right hCt hΔ
  · have hind : Set.indicator {t : ↥(GSpin d.QW) | d.IsGammaElt t ∧ d.torusOf t = T}
        (fun t => deltaGGP d t ^ (s - 1 / 2)) t = 0 :=
      Set.indicator_of_notMem (s := {t : ↥(GSpin d.QW) | d.IsGammaElt t ∧ d.torusOf t = T}) h _
    simp only [gammaIntegrand, h, ↓reduceIte, hind, norm_zero, mul_zero, le_refl]

theorem isTorusIntegrable_add {θ₁ θ₂ : ↥d.G → ℂ} (h₁ : IsQuasiCharacter d.G d.lie d.bilin ψ θ₁)
    (h₂ : IsQuasiCharacter d.G d.lie d.bilin ψ θ₂) {T : Subgroup ↥(GSpin d.QW)} {s : ℝ}
    (hi₁ : IsTorusIntegrable ψ d θ₁ T s) (hi₂ : IsTorusIntegrable ψ d θ₂ T s) :
    IsTorusIntegrable ψ d (θ₁ + θ₂) T s := by
  unfold IsTorusIntegrable at *
  simp only [gammaIntegrand_add ψ d h₁ h₂]
  exact hi₁.add hi₂

theorem isTorusIntegrable_smul (c : ℂ) {θ : ↥d.G → ℂ}
    (hθ : IsQuasiCharacter d.G d.lie d.bilin ψ θ) {T : Subgroup ↥(GSpin d.QW)} {s : ℝ}
    (hi : IsTorusIntegrable ψ d θ T s) : IsTorusIntegrable ψ d (c • θ) T s := by
  unfold IsTorusIntegrable at *
  simp only [gammaIntegrand_smul ψ d c hθ]
  exact hi.const_mul c

theorem isTorusIntegrable_zero (T : Subgroup ↥(GSpin d.QW)) (s : ℝ) :
    IsTorusIntegrable ψ d 0 T s := by
  unfold IsTorusIntegrable
  simp only [gammaIntegrand_zero ψ d]
  exact integrable_zero _ _ _

/-- `torusIntegral` is additive on quasi-characters with integrable integrands. -/
theorem torusIntegral_add {θ₁ θ₂ : ↥d.G → ℂ} (h₁ : IsQuasiCharacter d.G d.lie d.bilin ψ θ₁)
    (h₂ : IsQuasiCharacter d.G d.lie d.bilin ψ θ₂) {T : Subgroup ↥(GSpin d.QW)} {s : ℝ}
    (hi₁ : IsTorusIntegrable ψ d θ₁ T s) (hi₂ : IsTorusIntegrable ψ d θ₂ T s) :
    torusIntegral ψ d (θ₁ + θ₂) T s = torusIntegral ψ d θ₁ T s + torusIntegral ψ d θ₂ T s := by
  unfold torusIntegral
  unfold IsTorusIntegrable at hi₁ hi₂
  simp only [gammaIntegrand_add ψ d h₁ h₂]
  exact integral_add hi₁ hi₂

/-- The quasi-characters (for `ψ`) whose `m_{geom,s}` integrands are integrable on every torus
for every `s > 0`: a submodule containing every `QC d χ`, hence `QCfin d`. -/
def qcGood : Submodule ℂ (↥d.G → ℂ) where
  carrier := {θ | IsQuasiCharacter d.G d.lie d.bilin ψ θ ∧
    ∀ (T : Subgroup ↥(GSpin d.QW)) (s : ℝ), 0 < s → IsTorusIntegrable ψ d θ T s}
  add_mem' := fun h₁ h₂ => ⟨isQuasiCharacter_add d ψ h₁.1 h₂.1, fun _ _ hs =>
    isTorusIntegrable_add ψ d h₁.1 h₂.1 (h₁.2 _ _ hs) (h₂.2 _ _ hs)⟩
  zero_mem' := ⟨isQuasiCharacter_zero d ψ, fun T s _ => isTorusIntegrable_zero ψ d T s⟩
  smul_mem' := fun c _ h => ⟨isQuasiCharacter_smul d ψ c h.1, fun _ _ hs =>
    isTorusIntegrable_smul ψ d c h.1 (h.2 _ _ hs)⟩

theorem QCfin_le_qcGood : QCfin d ≤ qcGood ψ d :=
  iSup_le fun _ _ hθ => ⟨hθ.1 ψ, fun T _ hs => isTorusIntegrable_of_mem_QC ψ d hθ T hs⟩

/-- **(12.1.2) ⇒ additivity of `m_{geom,s}` for `s > 0`** on `qcGood` (finitely many tori). -/
theorem mGeomS_add_of_mem_qcGood {θ₁ θ₂ : ↥d.G → ℂ} (h₁ : θ₁ ∈ qcGood ψ d)
    (h₂ : θ₂ ∈ qcGood ψ d) {s : ℝ} (hs : 0 < s) :
    mGeomS ψ d (θ₁ + θ₂) s = mGeomS ψ d θ₁ s + mGeomS ψ d θ₂ s := by
  have := finite_gammaClass d
  unfold mGeomS
  rw [← Summable.tsum_add Summable.of_finite Summable.of_finite]
  refine tsum_congr fun c => ?_
  rw [torusIntegral_add ψ d h₁.1 h₂.1 (h₁.2 _ s hs) (h₂.2 _ s hs), mul_add]

/-- The elements of `QCfin d` for which `lim_{s → 0⁺} m_{geom,s}` exists: a submodule (by
`mGeomS_add_of_mem_qcGood`, `mGeomS_smul_of_isQuasiCharacter`) containing every `QC d χ`
(`tendsto_mGeomS_of_mem_QC`), hence equal to `QCfin d`. -/
def qcLim : Submodule ℂ (↥d.G → ℂ) where
  carrier := {θ | θ ∈ QCfin d ∧ ∃ L : ℂ, Tendsto (mGeomS ψ d θ) (𝓝[>] (0 : ℝ)) (𝓝 L)}
  add_mem' := fun {θ₁ θ₂} h₁ h₂ => by
    obtain ⟨h₁, L₁, hL₁⟩ := h₁
    obtain ⟨h₂, L₂, hL₂⟩ := h₂
    refine ⟨add_mem h₁ h₂, L₁ + L₂, (hL₁.add hL₂).congr' ?_⟩
    exact eventually_nhdsWithin_of_forall fun s hs => (mGeomS_add_of_mem_qcGood ψ d
      (QCfin_le_qcGood ψ d h₁) (QCfin_le_qcGood ψ d h₂) hs).symm
  zero_mem' := ⟨zero_mem _, 0, tendsto_const_nhds.congr' (Eventually.of_forall fun s =>
    (mGeomS_zero ψ d s).symm)⟩
  smul_mem' := fun c θ h => by
    obtain ⟨h, L, hL⟩ := h
    refine ⟨Submodule.smul_mem _ c h, c * L, (hL.const_mul c).congr' ?_⟩
    exact Eventually.of_forall fun s => (mGeomS_smul_of_isQuasiCharacter ψ d c
      (isQuasiCharacter_of_mem_QCfin d h ψ) s).symm

theorem QCfin_le_qcLim : QCfin d ≤ qcLim ψ d :=
  iSup_le fun _ _ hθ => ⟨mem_QCfin_of_mem_QC d hθ, tendsto_mGeomS_of_mem_QC ψ d hθ⟩

end Convergence

/-! ### 0c. Central translation of characters (generalizing `Main.charG_diag_scalar_mul`)

`Main.lean` cannot be imported here, so the helper chain of `Main` (section `CentralTranslate`) is
redone for a central `z` acting by a scalar `π(z) = c · 1` (rather than `π(z) = 1`). -/

section CentralTranslateScalar

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- Left translates of test functions are test functions. -/
theorem testFunctions_comp_mul_left {f : G → ℂ} (hf : f ∈ testFunctions G) (z : G) :
    (fun g => f (z * g)) ∈ testFunctions G :=
  ⟨hf.1.comp_continuous (continuous_const.mul continuous_id),
    hf.2.comp_homeomorph (Homeomorph.mulLeft z)⟩

omit [T2Space G] in
/-- `π(f(z⁻¹ ·)) = π(z) π(f) = c π(f)` when `π(z) = c · 1`. -/
theorem opOf_comp_mul_left_of_scalar (π : UnitaryRep G) {f : G → ℂ} (hf : f ∈ testFunctions G)
    {z : G} {c : ℂ} (hπz : π.ρ z = c • (1 : π.H →L[ℂ] π.H)) :
    opOf π (fun g => f (z⁻¹ * g)) = c • opOf π f := by
  have hf' := testFunctions_comp_mul_left hf z⁻¹
  ext v
  rw [smul_apply, opOf_apply π (opIntegrable_of_mem_testFunctions π hf'),
    opOf_apply π (opIntegrable_of_mem_testFunctions π hf),
    ← integral_mul_left_eq_self (fun g => f (z⁻¹ * g) • π.ρ g v) z, ← integral_smul]
  congr 1
  funext g
  simp only [inv_mul_cancel_left, map_mul, hπz, mul_apply_eq_comp, smul_apply,
    one_apply_eq_self]
  exact smul_comm _ _ _

omit [T2Space G] in
theorem traceDatum_comp_mul_left_of_scalar (π : UnitaryRep G) {f : G → ℂ}
    (hf : f ∈ testFunctions G) {z : G} (hz : ∀ g, z * g = g * z) {c : ℂ}
    (hπz : π.ρ z = c • (1 : π.H →L[ℂ] π.H))
    {K : Subgroup G} (hK : TraceDatum π f K) : TraceDatum π (fun g => f (z⁻¹ * g)) K := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hK
  refine ⟨h1, h2, fun k hk g => ⟨?_, ?_⟩, h4, ?_⟩
  · have hz' : z⁻¹ * k = k * z⁻¹ := by
      have := hz k⁻¹
      have h := congrArg (fun u => u⁻¹) this
      simpa [mul_inv_rev] using h.symm
    simp only
    rw [← mul_assoc, hz', mul_assoc]
    exact (h3 k hk _).1
  · simp only
    rw [← mul_assoc]
    exact (h3 k hk _).2
  · intro v hv
    rw [opOf_comp_mul_left_of_scalar π hf hπz, smul_apply]
    exact Submodule.smul_mem _ c (h5 v hv)

omit [T2Space G] in
/-- `π(z⁻¹) = c⁻¹ · 1` when `π(z) = c · 1`. -/
theorem rho_inv_of_scalar (π : UnitaryRep G) {z : G} {c : ℂ}
    (hπz : π.ρ z = c • (1 : π.H →L[ℂ] π.H)) :
    π.ρ z⁻¹ = c⁻¹ • (1 : π.H →L[ℂ] π.H) := by
  by_cases hc : c = 0
  · -- then `1 = π(z⁻¹) π(z) = 0`, so all operators vanish
    have h1 : (1 : π.H →L[ℂ] π.H) = 0 := by
      have h := map_mul π.ρ z⁻¹ z
      rw [inv_mul_cancel, map_one, hπz, hc, zero_smul, mul_zero] at h
      exact h
    have h0 : ∀ T : π.H →L[ℂ] π.H, T = 0 := fun T => by rw [← mul_one T, h1, mul_zero]
    rw [h0 (π.ρ z⁻¹), h0 (c⁻¹ • 1)]
  · have h := map_mul π.ρ z⁻¹ z
    rw [inv_mul_cancel, map_one, hπz, mul_smul_comm, mul_one] at h
    -- `h : 1 = c • π(z⁻¹)`
    rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]

open Classical in
omit [T2Space G] in
/-- `tr π(f(z⁻¹ ·)) = c · tr π(f)` for `z` central with `π(z) = c · 1`. -/
theorem traceOf_comp_mul_left_of_scalar (π : UnitaryRep G) {f : G → ℂ}
    (hf : f ∈ testFunctions G) {z : G} (hz : ∀ g, z * g = g * z) {c : ℂ}
    (hπz : π.ρ z = c • (1 : π.H →L[ℂ] π.H)) :
    traceOf π (fun g => f (z⁻¹ * g)) = c * traceOf π f := by
  have hf' := testFunctions_comp_mul_left hf z⁻¹
  have hzi : ∀ g, z⁻¹ * g = g * z⁻¹ := fun g => by
    have h := congrArg (fun u => u⁻¹) (hz g⁻¹)
    simpa [mul_inv_rev] using h.symm
  have hπzi := rho_inv_of_scalar π hπz
  by_cases h : ∃ K, TraceDatum π f K
  · obtain ⟨K, hK⟩ := h
    have hK' := traceDatum_comp_mul_left_of_scalar π hf hz hπz hK
    rw [traceOf_eq π _ K hK', traceOf_eq π f K hK]
    have key : ∀ (T T' : π.H →L[ℂ] π.H), T = c • T' →
        ∀ (h₁ : ∀ v ∈ fixedSpace π K, T v ∈ fixedSpace π K)
        (h₂ : ∀ v ∈ fixedSpace π K, T' v ∈ fixedSpace π K),
        LinearMap.trace ℂ ↥(fixedSpace π K) (T.toLinearMap.restrict h₁) =
          c * LinearMap.trace ℂ ↥(fixedSpace π K) (T'.toLinearMap.restrict h₂) := by
      rintro T T' rfl h₁ h₂
      have : (c • T').toLinearMap.restrict h₁ = c • T'.toLinearMap.restrict h₂ :=
        LinearMap.ext fun v => rfl
      rw [this, map_smul, smul_eq_mul]
    exact key _ _ (opOf_comp_mul_left_of_scalar π hf hπz) _ _
  · have h' : ¬ ∃ K, TraceDatum π (fun g => f (z⁻¹ * g)) K := by
      rintro ⟨K, hK⟩
      apply h
      refine ⟨K, ?_⟩
      have := traceDatum_comp_mul_left_of_scalar π hf' hzi hπzi hK
      simpa using this
    unfold traceOf
    rw [dite_eq_right_iff.mpr fun h'' => absurd h'' h,
      dite_eq_right_iff.mpr fun h'' => absurd h'' h',
      mul_zero]

omit [T2Space G] in
/-- **Central translation of a character** (Thesis Ch. 1): if `θ` is a character of `π`,
`z` is central and `π(z) = c · 1` with `c ≠ 0`, then `g ↦ c⁻¹ θ(z g)` is again a character of `π`
(`∫ θ(zg) f(g) dg = tr π(f(z⁻¹·)) = c tr π(f)`). -/
theorem IsCharacterOf.comp_mul_left_of_scalar {π : UnitaryRep G} {θ : G → ℂ}
    (hθ : IsCharacterOf π θ) {z : G} (hz : ∀ g, z * g = g * z) {c : ℂ} (hc : c ≠ 0)
    (hπz : π.ρ z = c • (1 : π.H →L[ℂ] π.H)) :
    IsCharacterOf π (fun g => c⁻¹ * θ (z * g)) := by
  refine ⟨?_, fun f hf => ?_⟩
  · have := (locallyIntegrable_map_homeomorph (Homeomorph.mulLeft z) (f := θ)
      (μ := (Measure.haar : Measure G))).1
    rw [show Measure.map (Homeomorph.mulLeft z) (Measure.haar : Measure G) = Measure.haar from
      map_mul_left_eq_self _ z] at this
    exact (this hθ.1).smul c⁻¹
  · have h1 : ∫ g, θ (z * g) * f g ∂(Measure.haar : Measure G) = c * traceOf π f := by
      rw [← traceOf_comp_mul_left_of_scalar π hf hz hπz,
        ← hθ.2 _ (testFunctions_comp_mul_left hf z⁻¹),
        ← integral_mul_left_eq_self (fun g => θ g * f (z⁻¹ * g)) z]
      simp only [inv_mul_cancel_left]
    simp only [mul_assoc]
    rw [integral_const_mul, h1, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end CentralTranslateScalar

/-- **`θ_π(a g) = η(a) θ_π(g)` on `G_reg(F)`** for `π` tempered with central character `η` on
`A_G(F)` (generalizes `Main.charG_diag_scalar_mul` from `A_{G,H}(F)` and trivial character).
`g ↦ η(a)⁻¹ θ_π(a g)` is a character of `π` (`IsCharacterOf.comp_mul_left_of_scalar`) and is
continuous on `G_reg(F)`, which is stable under `A_G(F)` (`mul_mem_regularSet_of_mem_AG`); two
such characters agree on `G_reg(F)` (`hc_regularSet_open_conull`). -/
theorem charG_mul_AG {η : CentralCharOn d} {π : UnitaryRep ↥d.G} (hπ : IsTempCC d η π)
    (a : ↥d.AG) {g : ↥d.G} (hg : g ∈ regularSet d.G d.lie) :
    charG d π ((a : ↥d.G) * g) = ((η.toHom a : Circle) : ℂ) * charG d π g := by
  set z : ↥d.G := (a : ↥d.G)
  set c : ℂ := ((η.toHom a : Circle) : ℂ)
  have hc : c ≠ 0 := Circle.coe_ne_zero _
  have hzc : ∀ g' : ↥d.G, z * g' = g' * z := fun g' =>
    (Subgroup.mem_center_iff.mp (d.AG_le_center a.2) g').symm
  have hπz : π.ρ z = c • (1 : π.H →L[ℂ] π.H) := hπ.2 a
  obtain ⟨hchar, hcont⟩ := hc_character d π hπ.1
  have hchar' := IsCharacterOf.comp_mul_left_of_scalar hchar hzc hc hπz
  have hcont' : ContinuousOn (fun g' => c⁻¹ * charG d π (z * g')) (regularSet d.G d.lie) :=
    continuousOn_const.mul (hcont.comp (continuous_const.mul continuous_id).continuousOn
      fun g' hg' => mul_mem_regularSet_of_mem_AG d a hg')
  have : TotallyDisconnectedSpace ↥d.G := totallyDisconnectedSpace_subgroup F d.ambient d.G
  have hae := hchar'.ae_eq hchar
  have heq := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hae) (hc_regularSet_open_conull d).1
    hcont' hcont hg
  change c⁻¹ * charG d π (z * g) = charG d π g at heq
  rw [← heq, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-! ## 1. Interface statements -/

/-- **Thesis Prop 12.1.1(i), existence of the limit** (BP Prop 11.2.1,
Lemma B.1.2): for `θ ∈ QCfin d` the limit `m_geom(θ) = lim_{s → 0⁺} m_{geom,s}(θ)` exists.
(The thesis states it for `θ ∈ QC(G(F), χ)`; for finite sums over central characters it follows
from `mGeomS_add`.)  Status: proved from the single-`χ` limit `tendsto_mGeomS_of_mem_QC`
and the additivity below, via the submodule `qcLim`. -/
theorem tendsto_mGeomS {θ : ↥d.G → ℂ} (hθ : θ ∈ QCfin d) :
    ∃ L : ℂ, Tendsto (mGeomS ψ d θ) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  exact (QCfin_le_qcLim ψ d hθ).2

/-- **`m_{geom,s}` is additive for `s > 0`** (Thesis Prop 12.1.1(i): the integrals converge
absolutely, and germs are additive, `germ_add`).  Status: proved from the four §0b inputs
`finite_gammaClass`, `germ_bound_of_mem_QC`, `aestronglyMeasurable_torusFn_of_mem_QC`,
`integrable_delta_rpow`, via the submodule `qcGood`. -/
theorem mGeomS_add {θ₁ θ₂ : ↥d.G → ℂ} (h₁ : θ₁ ∈ QCfin d) (h₂ : θ₂ ∈ QCfin d) {s : ℝ}
    (hs : 0 < s) : mGeomS ψ d (θ₁ + θ₂) s = mGeomS ψ d θ₁ s + mGeomS ψ d θ₂ s := by
  exact mGeomS_add_of_mem_qcGood ψ d (QCfin_le_qcGood ψ d h₁) (QCfin_le_qcGood ψ d h₂) hs

/-- **`m_{geom,s}` is homogeneous for `s > 0`** (germs are homogeneous, `germ_smul`).
Status: proved, for every `s`; uses only `germ_unique`. -/
theorem mGeomS_smul (c : ℂ) {θ : ↥d.G → ℂ} (hθ : θ ∈ QCfin d) {s : ℝ} (hs : 0 < s) :
    mGeomS ψ d (c • θ) s = c * mGeomS ψ d θ s := by
  -- true for every `s` (`mGeomS_smul_of_isQuasiCharacter`); `hs` is not needed
  have _hs := hs
  exact mGeomS_smul_of_isQuasiCharacter ψ d c (isQuasiCharacter_of_mem_QCfin d hθ ψ) s

/-- **`m_geom` depends only on the values on `G_reg(F)`** (Thesis §6.5: `c_{θ,O}(x)` is defined
by the local expansion of `θ` on regular elements near `x`; `exists_nhds_mul_expA_mem_regularSet`
makes the two germ predicates for `θ` and `θ'` coincide at every semisimple `x`).
Status: proved; uses only `germ_unique`. -/
theorem mGeom_congr_regularSet {θ θ' : ↥d.G → ℂ} (h : Set.EqOn θ θ' (regularSet d.G d.lie)) :
    mGeom ψ d θ = mGeom ψ d θ' := by
  rw [mGeom, mGeom, mGeomS_congr_regularSet ψ d h]

/-- **The character of a tempered representation with central character `η` lies in
`QC(G(F), η)`** (Harish-Chandra; Thesis Ch. 1, §4.4), i.e. in `QC d η.inv` in the convention of
`QC`: `θ_π` is a quasi-character (`hc_character_isQuasiCharacter`) and `θ_π(ag) = η(a) θ_π(g)` on
`G_reg(F)` (central translation of the character, as in `Main.charG_diag_scalar_mul`).
Status: proved, via `charG_mul_AG`. -/
theorem charG_mem_QC {η : CentralCharOn d} {π : UnitaryRep ↥d.G} (hπ : IsTempCC d η π) :
    charG d π ∈ QC d η.inv := by
  refine ⟨fun ψ' => hc_character_isQuasiCharacter d ψ' π hπ.1, fun a g hg => ?_⟩
  rw [CentralCharOn.inv_apply, inv_inv]
  exact charG_mul_AG d hπ a hg

/-! ## 2. Consequences (proved) -/

/-- `m_{geom,s}(θ) → m_geom(θ)` as `s → 0⁺`, for `θ ∈ QCfin d`. -/
theorem tendsto_mGeomS_mGeom {θ : ↥d.G → ℂ} (hθ : θ ∈ QCfin d) :
    Tendsto (mGeomS ψ d θ) (𝓝[>] (0 : ℝ)) (𝓝 (mGeom ψ d θ)) := by
  obtain ⟨L, hL⟩ := tendsto_mGeomS ψ d hθ
  rwa [mGeom, hL.limUnder_eq]

/-- **`m_geom` is additive on `QCfin d`** (Thesis Prop 12.1.1(i), "`m_geom` is a linear form"). -/
theorem mGeom_add {θ₁ θ₂ : ↥d.G → ℂ} (h₁ : θ₁ ∈ QCfin d) (h₂ : θ₂ ∈ QCfin d) :
    mGeom ψ d (θ₁ + θ₂) = mGeom ψ d θ₁ + mGeom ψ d θ₂ := by
  have hsum := (tendsto_mGeomS_mGeom ψ d h₁).add (tendsto_mGeomS_mGeom ψ d h₂)
  have heq : (fun s => mGeomS ψ d θ₁ s + mGeomS ψ d θ₂ s) =ᶠ[𝓝[>] (0 : ℝ)]
      mGeomS ψ d (θ₁ + θ₂) :=
    eventually_nhdsWithin_of_forall fun s hs => (mGeomS_add ψ d h₁ h₂ hs).symm
  exact tendsto_nhds_unique (tendsto_mGeomS_mGeom ψ d (add_mem h₁ h₂)) (hsum.congr' heq)

/-- **`m_geom` is homogeneous on `QCfin d`.** -/
theorem mGeom_smul (c : ℂ) {θ : ↥d.G → ℂ} (hθ : θ ∈ QCfin d) :
    mGeom ψ d (c • θ) = c * mGeom ψ d θ := by
  have hlim := (tendsto_mGeomS_mGeom ψ d hθ).const_mul c
  have heq : (fun s => c * mGeomS ψ d θ s) =ᶠ[𝓝[>] (0 : ℝ)] mGeomS ψ d (c • θ) :=
    eventually_nhdsWithin_of_forall fun s hs => (mGeomS_smul ψ d c hθ hs).symm
  exact tendsto_nhds_unique (tendsto_mGeomS_mGeom ψ d (Submodule.smul_mem _ c hθ))
    (hlim.congr' heq)

/-- **`m_geom` of a finite sum** of elements of `QCfin d`. -/
theorem mGeom_finset_sum_of_mem {ι : Type*} (s : Finset ι) (θ : ι → ↥d.G → ℂ)
    (h : ∀ i ∈ s, θ i ∈ QCfin d) :
    mGeom ψ d (∑ i ∈ s, θ i) = ∑ i ∈ s, mGeom ψ d (θ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    simpa using mGeom_smul ψ d 0 (Submodule.zero_mem (QCfin d))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      mGeom_add ψ d (h i (Finset.mem_insert_self i s))
        (Submodule.sum_mem _ fun j hj => h j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => h j (Finset.mem_insert_of_mem hj)]

/-- **The character of a virtual tempered representation with central character `η` lies in
`QC d η.inv`** (from `charG_mem_QC` by linearity). -/
theorem vChar_mem_QC {η : CentralCharOn d} (P : VirtualTemp d η) : vChar d P ∈ QC d η.inv := by
  induction P using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
  | single c a =>
    rw [vChar_single]
    exact Submodule.smul_mem _ a (charG_mem_QC d c.isTempCC_rep)

end GSpinGGP
