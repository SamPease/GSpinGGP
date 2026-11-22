/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.GermBound
import GSpinGGP.TraceFormula.GermHomogeneous
import GSpinGGP.TraceFormula.TorusDescent
import GSpinGGP.Literature.BPQuasiCharacter
import GSpinGGP.Foundations.CharpolyLimit
import GSpinGGP.Foundations.ExpHaar

/-!
# The bound on `(D^G)^{1/2} c_{θ,O_t}(t)` on `T_♮`

Proof of the local bound used in Thesis Prop 12.1.1(i), (12.1.2): for `θ ∈ QC(G(F), χ)` and a
torus `T = T_x` of `Γ(G,H)`, `D^G(t)^{1/2} |c_{θ,O_t}(t)|` is bounded on
`T_♮ = {t ∈ Γ(G,H) | T_t = T}` (`germ_bound_of_mem_QC_aux`, used by `germ_bound_of_mem_QC` in
`TraceFormula/MGeom.lean`).

The thesis cites BP Astérisque 418, Prop 4.5.1, which bounds the *average* `c_θ` of the regular
germs. The argument here bounds each regular germ, following BP's proof of Prop 4.5.1 (local
boundedness of `(D^G)^{1/2} θ`, BP Prop 4.1.1(ii), `bp_sqrt_weylDisc_mul_locallyBounded`) but
evaluating the local expansion at finitely many points instead of along one torus:

* `sqrt_weylDisc_mul_norm_sum_le` (one point `x`, one direction `X`): along the ray
  `x e^{ϖ^{2k} X}`, `X ∈ 𝔤_x` regular semisimple, the local expansion, the homogeneity
  `ĵ(O, t² X) = |t|^{-dim O} ĵ(O, X)` (BP (1.8.5), `jHat_sq_smul_lieCentralizer`) and
  `D^G(x e^{λX}) = D^G(x) |λ|^{δ} D^{G_x}(X)` (`eventually_weylDisc_mul_expA_smul`) give
  `D^G(x)^{1/2} D^{G_x}(X)^{1/2} |∑_{O ∈ Nil_reg(𝔤_x)} c_{θ,O}(x) ĵ(O, X)| ≤ B` whenever
  `(D^G)^{1/2} |θ| ≤ B` on the regular points of a neighbourhood of `x`. Only `δ ≤ dim O_reg`
  (`dim 𝔤_{x,X} ≥ rank 𝔤_x`) and `dim O < dim O_reg` for non-regular `O` are used, so the
  non-regular terms die in the limit `k → ∞`.
* `sqrt_weylDisc_mul_norm_coeff_le`: with finitely many directions separating the regular
  `ĵ(O, ·)` (`exists_finset_bound_nilReg_coeff`), each regular germ is bounded.
* `exists_uniform_germ_bound`: on `T_♮` the centralizers `G_t`, `𝔤_t` and the orbit `O_t` do
  not depend on `t` (`grpCentralizer_diag_eq_of_torusOf_eq`, …), so one choice of directions
  serves every `t ∈ T_♮`.
* `germ_bound_of_mem_QC_aux`: the neighbourhoods from BP Prop 4.1.1(ii) at the points of `T(F)`
  (including those outside `T_♮`), the `A_{G,H}(F)`-invariance of the integrand and the
  compactness of `T(F)/A_{G,H}(F)` give a global bound (`exists_bound_of_locallyBounded`).
-/

noncomputable section

open Topology Filter

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

/-! ## 1. A locally bounded invariant function on a group with compact quotient is bounded -/

section Compact

/-- **Boundedness from local boundedness on a compact quotient.** Let `f : G → ℝ` be invariant
under right multiplication by `N`, with `G/N` compact, and bounded above near every point.
Then `f` is bounded above. -/
theorem exists_bound_of_locallyBounded {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (N : Subgroup G) [CompactSpace (G ⧸ N)] (f : G → ℝ)
    (hinv : ∀ g, ∀ n ∈ N, f (g * n) = f g)
    (hloc : ∀ g, ∃ U ∈ 𝓝 g, ∃ C : ℝ, ∀ g' ∈ U, f g' ≤ C) :
    ∃ C : ℝ, ∀ g, f g ≤ C := by
  classical
  choose U hU C hC using hloc
  let V : G → Set (G ⧸ N) := fun g => (QuotientGroup.mk : G → G ⧸ N) '' interior (U g)
  have hVo : ∀ g, IsOpen (V g) := fun g => QuotientGroup.isOpenMap_coe _ isOpen_interior
  have hcov : (Set.univ : Set (G ⧸ N)) ⊆ ⋃ g, V g := by
    intro q _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact Set.mem_iUnion.mpr ⟨g, g, mem_interior_iff_mem_nhds.mpr (hU g), rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hVo hcov
  refine ⟨∑ i ∈ t, |C i|, fun g => ?_⟩
  obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (QuotientGroup.mk g : G ⧸ N)))
  obtain ⟨u, hu, hug⟩ := hgi
  obtain ⟨n, hn, rfl⟩ : ∃ n ∈ N, u * n = g := by
    refine ⟨u⁻¹ * g, QuotientGroup.eq.mp hug, ?_⟩
    rw [mul_inv_cancel_left]
  rw [hinv u n hn]
  calc f u ≤ C i := hC i u (interior_subset hu)
    _ ≤ |C i| := le_abs_self _
    _ ≤ ∑ j ∈ t, |C j| :=
      Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _) hi

end Compact

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
variable (ψ : NontrivialAddChar F) (d : GGPData F)

/-! ## 2. Elementary facts -/

section Basic

/-- `D^{𝔤'}(X) > 0` for `X` in a Lie subalgebra `𝔤'`. -/
theorem weylDiscLie_pos (𝔤' : LieSubalgebra F d.ambient) {X : d.ambient} (hX : X ∈ 𝔤') :
    0 < weylDiscLie 𝔤' X := by
  have h : ∀ Y ∈ 𝔤'.toSubmodule,
      (LinearMap.mulLeft F X - LinearMap.mulRight F X) Y ∈ 𝔤'.toSubmodule := fun Y hY => by
    have := 𝔤'.lie_mem hX hY
    simpa [Ring.lie_def] using this
  rw [weylDiscLie, dite_eq_left_of_eq_true (eq_true h)]
  exact absF_pos (mt Polynomial.trailingCoeff_eq_zero.mp (LinearMap.charpoly_monic _).ne_zero)

/-- `rank 𝔤 ≤ dim 𝔤_X` for `X ∈ 𝔤` (the rank is the minimum). -/
theorem lieRank_le_finrank_lieCentralizer (𝔤' : LieSubalgebra F d.ambient) {X : d.ambient}
    (hX : X ∈ 𝔤') : lieRank 𝔤' ≤ Module.finrank F ↥(lieCentralizer 𝔤' X) :=
  ciInf_le (OrderBot.bddBelow _) (⟨X, hX⟩ : ↥𝔤')

/-- `dim 𝔤_X ≤ dim 𝔤`. -/
theorem finrank_lieCentralizer_le (𝔤' : LieSubalgebra F d.ambient) (X : d.ambient) :
    Module.finrank F ↥(lieCentralizer 𝔤' X) ≤ Module.finrank F ↥𝔤' :=
  Submodule.finrank_mono (show (lieCentralizer 𝔤' X).toSubmodule ≤ 𝔤'.toSubmodule from
    fun _ h => h.1)

/-- The chosen representative of a nilpotent orbit lies in it. -/
theorem out_mem_nilOrbitSet {G' : Subgroup d.ambientˣ} {𝔤' : LieSubalgebra F d.ambient}
    (O : NilOrbit G' 𝔤') :
    (⟨(Quotient.out O).val, (Quotient.out O).property.1⟩ : ↥𝔤') ∈ nilOrbitSet O :=
  ⟨(Quotient.out O).property.2, Quotient.out_eq O⟩

/-- Membership in `Nil_reg` transported along equal centralizers. -/
theorem mem_nilReg_congr {G₁ G₂ : Subgroup d.ambientˣ} {𝔤₁ 𝔤₂ : LieSubalgebra F d.ambient}
    (hG : G₁ = G₂) (h𝔤 : 𝔤₁ = 𝔤₂) {O₁ : NilOrbit G₁ 𝔤₁} {O₂ : NilOrbit G₂ 𝔤₂}
    (h : HEq O₁ O₂) : O₁ ∈ NilReg G₁ 𝔤₁ ↔ O₂ ∈ NilReg G₂ 𝔤₂ := by
  subst hG h𝔤
  cases h
  rfl

/-- **Points `x e^Y`, `Y → 0`, eventually lie in a given neighbourhood of `x` in `G(F)`**
(`eventually_mul_expA_mem` for `G(F) ≤ (C(W) × C(V))ˣ`). -/
theorem eventually_mem_of_mul_expA (x : ↥d.G) {U : Set ↥d.G} (hU : U ∈ 𝓝 x) :
    ∀ᶠ Y in 𝓝 (0 : d.ambient), ∀ y : ↥d.G,
      ((y : d.ambientˣ) : d.ambient) = ((x : d.ambientˣ) : d.ambient) * expA F Y → y ∈ U :=
  eventually_mul_expA_mem F hU

end Basic

/-! ## 3. The Weyl discriminant along a ray -/

section Disc

/-- **The derivative of `c ↦ e^{cX}` at `0` is `X`**: `c⁻¹ (e^{cX} − 1) → X` as `c → 0`, `c ≠ 0`
(from `e^Y − 1 = Y u(Y)` with `u` continuous at `0`, `u(0) = 1`, `exists_expA_sub_one_eq_mul`). -/
theorem tendsto_inv_smul_expA_sub_one {A : Type*} [Ring A] [Algebra F A]
    [Module.Finite F A] [TopologicalSpace A] [IsModuleTopology F A] (X : A) :
    Tendsto (fun c : F => c⁻¹ • (expA F (c • X) - 1)) (𝓝[≠] 0) (𝓝 X) := by
  have := isTopologicalRing_of_moduleTopology F A
  have := IsModuleTopology.toContinuousSMul F A
  obtain ⟨u, hu, hu0, hev⟩ := exists_expA_sub_one_eq_mul (F := F) (A := A)
  have hcX : Tendsto (fun c : F => c • X) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun c : F => c • X) (𝓝 0) (𝓝 ((0 : F) • X)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rw [zero_smul] at this; exact this.mono_left nhdsWithin_le_nhds
  have hu' : Tendsto (fun c : F => X * u (c • X)) (𝓝[≠] 0) (𝓝 X) := by
    simpa [hu0] using tendsto_const_nhds.mul ((hu.tendsto).comp hcX)
  refine hu'.congr' ?_
  filter_upwards [hcX.eventually hev, self_mem_nhdsWithin] with c hh hc
  rw [hh.1, smul_mul_assoc, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- `ad X` on `𝔤`, for `X ∈ 𝔤`. -/
def adLie {X : d.ambient} (hX : X ∈ d.lie) : Module.End F d.lie.toSubmodule :=
  (LinearMap.mulLeft F X - LinearMap.mulRight F X).restrict fun Y hY => by
    simpa [Ring.lie_def] using d.lie.lie_mem hX hY

theorem coe_adLie {X : d.ambient} (hX : X ∈ d.lie) (v : d.lie.toSubmodule) :
    ((adLie d hX v : d.lie.toSubmodule) : d.ambient) = X * v - v * X := rfl

/-- `1 − Ad g` commutes with `ad X` when `g` commutes with `X`. -/
theorem commute_oneSubAd_adLie {g : ↥d.G} {X : d.ambient} (hX : X ∈ d.lie)
    (hgX : ((g : d.ambientˣ) : d.ambient) * X = X * ((g : d.ambientˣ) : d.ambient)) :
    Commute (oneSubAd d g) (adLie d hX) := by
  have hgX' : (((g : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) * X =
      X * (((g : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) :=
    (Commute.units_inv_left (u := (g : d.ambientˣ)) hgX).eq
  have hR : Commute (adRestrict d g) (adLie d hX) := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp only [mul_apply_eq_comp, coe_adRestrict, coe_adLie]
    set gv := ((g : d.ambientˣ) : d.ambient)
    set gi := (((g : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient)
    have h1 : gv * (X * v) * gi = X * (gv * v * gi) := by
      rw [← mul_assoc gv X, hgX]; simp only [mul_assoc]
    have h2 : gv * ((v : d.ambient) * X) * gi = gv * v * gi * X := by
      calc gv * ((v : d.ambient) * X) * gi = gv * v * (X * gi) := by simp only [mul_assoc]
        _ = gv * v * (gi * X) := by rw [hgX']
        _ = _ := by simp only [mul_assoc]
    rw [mul_sub, sub_mul, h1, h2]
  rw [oneSubAd_eq_one_sub_adRestrict]
  exact (Commute.one_left _).sub_left hR

/-- **`D^G(x e^{λX}) = D^G(x) |λ|^{δ} D^{G_x}(X)` for small `λ ≠ 0`** (BP Astérisque 418, §3.3 and
(3.3.1); Harish-Chandra), for `x ∈ G(F)` semisimple and `X ∈ 𝔤_x` semisimple, with
`δ = dim 𝔤_x − dim 𝔤_{x,X}` and `D^{G_x}(X) = |det(ad X)|_{𝔤_x/𝔤_{x,X}}|`.
Proof (`eventually_absF_trailingCoeff_charpoly` with `S = 1 − Ad x`, `D = ad X` on `𝔤` and
`N_c = 1 − Ad(x e^{cX})`). `𝔤 = 𝔤_x ⊕ 𝔮`, `𝔮 = Im(1 − Ad x)`, both stable under
`Ad(x e^{λX})`. On `𝔮`,
`det(1 − Ad(x e^{λX}))` is continuous in `λ` and nonzero at `0`, so its absolute value is
`|det(1 − Ad x)|_𝔮| = D^G(x)` for `λ` small. On `𝔤_x = 𝔤_{x,X} ⊕ C`, `C = Im(ad X)`,
`Ad(e^{λX}) = e^{λ ad X}` is `1` on `𝔤_{x,X}`, and `λ⁻¹(1 − e^{λ ad X})|_C → −ad X|_C`, which is
invertible; so `|det(1 − e^{λ ad X})|_C| = |λ|^{dim C} |det(ad X)|_C|` for `λ` small. -/
theorem eventually_weylDisc_mul_expA_smul (x : ↥d.G) (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    {X : d.ambient} (hX : X ∈ lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))
    (hXs : IsSS F X) :
    ∀ᶠ c in 𝓝[≠] (0 : F), ∀ y : ↥d.G,
      ((y : d.ambientˣ) : d.ambient) = ((x : d.ambientˣ) : d.ambient) * expA F (c • X) →
      weylDisc d.lie (y : d.ambientˣ) = weylDisc d.lie (x : d.ambientˣ) *
        absF c ^ (Module.finrank F ↥(lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) -
          Module.finrank F ↥(lieCentralizer
            (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) X)) *
        weylDiscLie (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) X := by
  classical
  have := isTopologicalRing_of_moduleTopology F d.ambient
  have := IsModuleTopology.toContinuousSMul F d.ambient
  set a : d.ambient := ((x : d.ambientˣ) : d.ambient) with ha
  set ai : d.ambient := (((x : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) with hai
  have haai : a * ai = 1 := Units.mul_inv _
  have haia : ai * a = 1 := Units.inv_mul _
  obtain ⟨hXl, hXa⟩ := mem_lieCentralizer.mp hX
  have hXa' : Commute a X := hXa
  set V := d.lie.toSubmodule with hV
  set S := oneSubAd d x with hSdef
  set D := adLie d hXl with hDdef
  have hSv : ∀ v : V, ((S v : V) : d.ambient) = v - a * v * ai := fun v => rfl
  have hS0 : ∀ v : V, S v = 0 ↔ a * v = v * a := by
    intro v
    rw [← Subtype.coe_inj, hSv, Submodule.coe_zero, sub_eq_zero]
    constructor
    · intro h
      calc a * v = a * v * ai * a := by rw [mul_assoc (a * v), haia, mul_one]
        _ = v * a := by rw [← h]
    · intro h
      rw [h, mul_assoc, haai, mul_one]
  -- semisimplicity
  have hS : Module.End.IsSemisimple S := isSemisimple_oneSubAd d x hx
  have hD : Module.End.IsSemisimple D := by
    set p := minpoly F (LinearMap.mulLeft F X)
    have hsq : Squarefree p := Module.End.IsSemisimple.minpoly_squarefree hXs
    have h0 : Polynomial.aeval (Algebra.lmul F d.ambient X) p = 0 := minpoly.aeval F _
    rw [Polynomial.aeval_algHom_apply] at h0
    have h1 : Polynomial.aeval X p = 0 :=
      Algebra.lmul_injective (R := F) (h0.trans (map_zero _).symm)
    have hR : Module.End.IsSemisimple (LinearMap.mulRight F X) :=
      Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq (by
        rw [aeval_mulRight, h1]; exact LinearMap.ext fun Y => by simp)
    have hAd : Module.End.IsSemisimple (LinearMap.mulLeft F X - LinearMap.mulRight F X) :=
      Module.End.IsSemisimple.sub_of_commute (LinearMap.commute_mulLeft_right X X) hXs hR
    exact hAd.restrict ((Module.End.mem_invtSubmodule _).mpr fun Y hY => by
      simpa [Ring.lie_def] using d.lie.lie_mem hXl hY)
  have hDK : ∀ v ∈ LinearMap.ker S, D v ∈ LinearMap.ker S := fun v hv => by
    rw [LinearMap.mem_ker, hS0] at hv ⊢
    have e1 : a * (X * v) = X * (v * a) := by rw [← mul_assoc, hXa, mul_assoc, hv]
    have e2 : a * (v * X) = v * (X * a) := by rw [← mul_assoc, hv, mul_assoc, hXa]
    rw [coe_adLie, mul_sub, sub_mul, e1, e2]
    simp only [mul_assoc]
  -- the family `N_c = 1 − Ad(x e^{cX})`
  let N : F → Module.End F V := fun c =>
    if h : ∃ y : ↥d.G, ((y : d.ambientˣ) : d.ambient) = a * expA F (c • X) then
      oneSubAd d h.choose else 0
  have hN : ∀ c (y : ↥d.G), ((y : d.ambientˣ) : d.ambient) = a * expA F (c • X) →
      N c = oneSubAd d y := fun c y hy => by
    have h : ∃ y : ↥d.G, ((y : d.ambientˣ) : d.ambient) = a * expA F (c • X) := ⟨y, hy⟩
    have hy' : h.choose = y := Subtype.ext (Units.ext (h.choose_spec.trans hy.symm))
    simp only [N, h, ↓reduceDIte, hy']
  obtain ⟨Ue, hUe, hee⟩ := expA_mul_expA_neg F (A := d.ambient)
  have hcX : Tendsto (fun c : F => c • X) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun c : F => c • X) (𝓝 0) (𝓝 ((0 : F) • X)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hgood : ∀ᶠ c in 𝓝[≠] (0 : F), c • X ∈ Ue ∧
      (c • X ∈ d.lie → ∃ g : ↥d.G, ((g : d.ambientˣ) : d.ambient) = expA F (c • X)) :=
    (hcX.eventually hUe).and (hcX.eventually (eventually_expA_mem_G d))
  -- the data at a good `c`
  have key : ∀ c : F, c • X ∈ Ue →
      (c • X ∈ d.lie → ∃ g : ↥d.G, ((g : d.ambientˣ) : d.ambient) = expA F (c • X)) →
      ∃ y : ↥d.G, ((y : d.ambientˣ) : d.ambient) = a * expA F (c • X) ∧
        (((y : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) = expA F (-(c • X)) * ai ∧
        N c = oneSubAd d y := by
    intro c hU hG
    obtain ⟨g, hg⟩ := hG (d.lie.smul_mem c hXl)
    have hy : (((x * g : ↥d.G) : d.ambientˣ) : d.ambient) = a * expA F (c • X) := by
      rw [Subgroup.coe_mul, Units.val_mul, hg]
    refine ⟨x * g, hy, ?_, hN c _ hy⟩
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hy, mul_assoc, ← mul_assoc (expA F (c • X)), hee _ hU, one_mul, haai]
  have hcomm : ∀ c : F, Commute a (expA F (c • X)) ∧ Commute a (expA F (-(c • X))) ∧
      Commute X (expA F (c • X)) := fun c =>
    ⟨commute_expA_of_commute (F := F) (hXa'.smul_right c),
      commute_expA_of_commute (F := F) (hXa'.smul_right c).neg_right,
      commute_expA_of_commute (F := F) ((Commute.refl X).smul_right c)⟩
  have hNS : ∀ᶠ c in 𝓝[≠] (0 : F), Commute (N c) S := by
    filter_upwards [hgood] with c ⟨hU, hG⟩
    obtain ⟨y, hy, -, hNc⟩ := key c hU hG
    rw [hNc]
    refine commute_oneSubAd d (Subtype.ext (Units.ext ?_))
    simp only [Subgroup.coe_mul, Units.val_mul, hy]
    rw [mul_assoc, (hcomm c).1.eq.symm, ← mul_assoc]
  have hND : ∀ᶠ c in 𝓝[≠] (0 : F), Commute (N c) D := by
    filter_upwards [hgood] with c ⟨hU, hG⟩
    obtain ⟨y, hy, -, hNc⟩ := key c hU hG
    rw [hNc]
    refine commute_oneSubAd_adLie d hXl ?_
    rw [hy, mul_assoc, (hcomm c).2.2.eq.symm, ← mul_assoc, hXa, mul_assoc]
  have hconj : ∀ c : F, c • X ∈ Ue → ∀ (y : ↥d.G),
      ((y : d.ambientˣ) : d.ambient) = a * expA F (c • X) →
      (((y : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) = expA F (-(c • X)) * ai →
      ∀ v : V, ((oneSubAd d y v : V) : d.ambient) =
        v - a * expA F (c • X) * v * (expA F (-(c • X)) * ai) := by
    intro c _ y hy hyi v
    change (v : d.ambient) - ((y : d.ambientˣ) : d.ambient) * v *
      (((y : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) = _
    rw [hy, hyi]
  have hK : ∀ᶠ c in 𝓝[≠] (0 : F), ∀ v, S v = 0 → D v = 0 → N c v = 0 := by
    filter_upwards [hgood] with c ⟨hU, hG⟩ v hSv0 hDv0
    obtain ⟨y, hy, hyi, hNc⟩ := key c hU hG
    rw [hNc]
    refine Subtype.ext ?_
    rw [hconj c hU y hy hyi v, Submodule.coe_zero]
    have hva : Commute a (v : d.ambient) := (hS0 v).mp hSv0
    have hvX : Commute X (v : d.ambient) := by
      have := congrArg Subtype.val hDv0
      rw [coe_adLie, Submodule.coe_zero, sub_eq_zero] at this
      exact this
    have hve : Commute (v : d.ambient) (expA F (c • X)) :=
      commute_expA_of_commute (F := F) (hvX.symm.smul_right c)
    have hve' : Commute (v : d.ambient) (expA F (-(c • X))) :=
      commute_expA_of_commute (F := F) (hvX.symm.smul_right c).neg_right
    have hfix : a * expA F (c • X) * v * (expA F (-(c • X)) * ai) = v := by
      calc a * expA F (c • X) * v * (expA F (-(c • X)) * ai) =
          v * (a * (expA F (c • X) * expA F (-(c • X))) * ai) := by
            rw [mul_assoc a, ← hve.eq, ← mul_assoc a, hva.eq]; simp only [mul_assoc]
        _ = v := by rw [hee _ hU, mul_one, haai, mul_one]
    rw [hfix, sub_self]
  -- limits
  have he : Tendsto (fun c : F => expA F (c • X)) (𝓝[≠] 0) (𝓝 1) := by
    have := (continuousAt_expA_at_zero F (A := d.ambient)).tendsto.comp hcX
    rwa [expA_zero_eq_one] at this
  have he' : Tendsto (fun c : F => expA F (-(c • X))) (𝓝[≠] 0) (𝓝 1) := by
    have := (continuousAt_expA_at_zero F (A := d.ambient)).tendsto.comp
      (by simpa using hcX.neg : Tendsto (fun c : F => -(c • X)) (𝓝[≠] 0) (𝓝 0))
    rwa [expA_zero_eq_one] at this
  have hlim : ∀ v, Tendsto (fun c => V.subtype (N c v)) (𝓝[≠] 0) (𝓝 (V.subtype (S v))) := by
    intro v
    have hT : Tendsto (fun c : F => (v : d.ambient) - a * expA F (c • X) * v *
        (expA F (-(c • X)) * ai)) (𝓝[≠] 0) (𝓝 ((v : d.ambient) - a * 1 * v * (1 * ai))) :=
      tendsto_const_nhds.sub (((tendsto_const_nhds.mul he).mul tendsto_const_nhds).mul
        (he'.mul tendsto_const_nhds))
    simp only [mul_one, one_mul] at hT
    refine hT.congr' ?_
    filter_upwards [hgood] with c ⟨hU, hG⟩
    obtain ⟨y, hy, hyi, hNc⟩ := key c hU hG
    rw [Submodule.subtype_apply, hNc, hconj c hU y hy hyi v]
  have hder : ∀ v, S v = 0 →
      Tendsto (fun c => V.subtype (c⁻¹ • N c v)) (𝓝[≠] 0) (𝓝 (V.subtype (-D v))) := by
    intro v hv
    have hva : Commute a (v : d.ambient) := (hS0 v).mp hv
    have h1 := tendsto_inv_smul_expA_sub_one (F := F) X
    have h2 := tendsto_inv_smul_expA_sub_one (F := F) (-X)
    simp only [smul_neg] at h2
    have hT : Tendsto (fun c : F => -((c⁻¹ • (expA F (c • X) - 1)) * v * expA F (-(c • X)) +
        (v : d.ambient) * (c⁻¹ • (expA F (-(c • X)) - 1)))) (𝓝[≠] 0)
        (𝓝 (-(X * v * 1 + (v : d.ambient) * -X))) :=
      (((h1.mul tendsto_const_nhds).mul he').add (tendsto_const_nhds.mul h2)).neg
    have hlimv : -(X * v * 1 + (v : d.ambient) * -X) = V.subtype (-D v) := by
      rw [map_neg, Submodule.subtype_apply, coe_adLie]; noncomm_ring
    rw [hlimv] at hT
    refine hT.congr' ?_
    filter_upwards [hgood] with c ⟨hU, hG⟩
    obtain ⟨y, hy, hyi, hNc⟩ := key c hU hG
    rw [map_smul, Submodule.subtype_apply, hNc, hconj c hU y hy hyi v]
    have hconj' : a * expA F (c • X) * v * (expA F (-(c • X)) * ai) =
        expA F (c • X) * v * expA F (-(c • X)) := by
      calc _ = expA F (c • X) * (a * v) * (expA F (-(c • X)) * ai) := by
            rw [(hcomm c).1.eq]; simp only [mul_assoc]
        _ = expA F (c • X) * v * (a * expA F (-(c • X))) * ai := by
            rw [hva.eq]; simp only [mul_assoc]
        _ = expA F (c • X) * v * expA F (-(c • X)) * (a * ai) := by
            rw [(hcomm c).2.1.eq]; simp only [mul_assoc]
        _ = _ := by rw [haai, mul_one]
    rw [hconj']
    simp only [smul_sub, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    abel
  -- the abstract statement
  have hmain := eventually_absF_trailingCoeff_charpoly V.subtype V.injective_subtype hS hD N hNS
    hND hK hlim hder hDK
  -- identifications
  have hmapK : (LinearMap.ker S).map V.subtype = (lieCentralizer d.lie a).toSubmodule := by
    ext Z
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact mem_lieCentralizer.mpr ⟨v.property, (hS0 v).mp hv⟩
    · intro hZ
      obtain ⟨hZl, hZa⟩ := mem_lieCentralizer.mp hZ
      exact ⟨⟨Z, hZl⟩, (hS0 _).mpr hZa, rfl⟩
  have hmapK2 : ((LinearMap.ker (D.restrict hDK)).map (LinearMap.ker S).subtype).map V.subtype =
      (lieCentralizer (lieCentralizer d.lie a) X).toSubmodule := by
    ext Z
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      have hw0 : D.restrict hDK w = 0 := hw
      have hw' := congrArg (fun u : LinearMap.ker S => ((u : V) : d.ambient)) hw0
      change X * ((w : V) : d.ambient) - ((w : V) : d.ambient) * X = 0 at hw'
      rw [sub_eq_zero] at hw'
      exact mem_lieCentralizer.mpr
        ⟨mem_lieCentralizer.mpr ⟨(w : V).property, (hS0 _).mp w.property⟩, hw'⟩
    · intro hZ
      obtain ⟨hZc, hZX⟩ := mem_lieCentralizer.mp hZ
      obtain ⟨hZl, hZa⟩ := mem_lieCentralizer.mp hZc
      let v : V := ⟨Z, hZl⟩
      let w : LinearMap.ker S := ⟨v, (hS0 v).mpr hZa⟩
      refine ⟨(w : V), ⟨w, ?_, rfl⟩, rfl⟩
      change D.restrict hDK w = 0
      refine Subtype.ext (Subtype.ext ?_)
      change X * Z - Z * X = 0
      rw [hZX, sub_self]
  have hdim1 : Module.finrank F ↥(LinearMap.ker S) =
      Module.finrank F ↥(lieCentralizer d.lie a) :=
    ((Submodule.equivMapOfInjective _ V.injective_subtype _).trans
      (LinearEquiv.ofEq _ _ hmapK)).finrank_eq
  have hdim2 : Module.finrank F ↥(LinearMap.ker (D.restrict hDK)) =
      Module.finrank F ↥(lieCentralizer (lieCentralizer d.lie a) X) :=
    (((Submodule.equivMapOfInjective _ (LinearMap.ker S).injective_subtype _).trans
      (Submodule.equivMapOfInjective _ V.injective_subtype _)).trans
      (LinearEquiv.ofEq _ _ hmapK2)).finrank_eq
  set e : ↥(LinearMap.ker S) ≃ₗ[F] ↥(lieCentralizer d.lie a).toSubmodule :=
    (Submodule.equivMapOfInjective _ V.injective_subtype _).trans (LinearEquiv.ofEq _ _ hmapK)
    with he_def
  have he_coe : ∀ w, ((e w : ↥(lieCentralizer d.lie a).toSubmodule) : d.ambient) =
      ((w : V) : d.ambient) := fun w => rfl
  have hadX : ∀ Y ∈ (lieCentralizer d.lie a).toSubmodule,
      (LinearMap.mulLeft F X - LinearMap.mulRight F X) Y ∈
        (lieCentralizer d.lie a).toSubmodule := fun Y hY => by
    simpa [Ring.lie_def] using (lieCentralizer d.lie a).lie_mem hX hY
  have hconjD : e.conj (D.restrict hDK) =
      (LinearMap.mulLeft F X - LinearMap.mulRight F X).restrict hadX := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    obtain ⟨u, rfl⟩ := e.surjective w
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, he_coe]
    simp only [LinearMap.coe_restrict_apply, LinearMap.sub_apply,
      LinearMap.mulLeft_apply, LinearMap.mulRight_apply, he_coe]
    exact coe_adLie d hXl _
  have hwl : weylDiscLie (lieCentralizer d.lie a) X =
      absF (D.restrict hDK).charpoly.trailingCoeff := by
    rw [weylDiscLie, dite_eq_left_of_eq_true (eq_true hadX), ← hconjD,
      LinearEquiv.charpoly_conj]
  filter_upwards [hmain, hgood] with c hc ⟨hU, hG⟩ y hy
  rw [weylDisc_eq_oneSubAd, weylDisc_eq_oneSubAd, ← hN c y hy, hc, hdim1, hdim2, hwl]

end Disc

/-! ## 4. The bound at one point -/

section Point

variable {θ : ↥d.G → ℂ}

set_option hygiene false in
/-- `G_x`, for the bound variable `x`. -/
local notation "G'" => grpCentralizer d.G (x : d.ambientˣ)

set_option hygiene false in
/-- `𝔤_x`, for the bound variable `x`. -/
local notation "𝔤'" => lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)

/-- **The regular part of the expansion along one direction** (BP Astérisque 418, proof of
Prop 4.5.1, evaluated along a ray): let `x ∈ G(F)` be semisimple, `c` a local expansion of `θ` at
`x`, `s = Nil_reg(𝔤_x)`, `X ∈ 𝔤_x` regular semisimple, and `(D^G)^{1/2}|θ| ≤ B` on the regular
points of a neighbourhood `U` of `x`. Then
`D^G(x)^{1/2} D^{G_x}(X)^{1/2} |∑_{O ∈ s} c_O ĵ(O, X)| ≤ B`.
Along `y_k = x e^{ϖ^{2k} X}`: `θ(y_k) = ∑_O c_O |ϖ|^{-k dim O} ĵ(O, X)`
(`jHat_sq_smul_lieCentralizer`) and `D^G(y_k)^{1/2} = D^G(x)^{1/2} |ϖ|^{kδ} D^{G_x}(X)^{1/2}`
(`eventually_weylDisc_mul_expA_smul`), `δ = dim 𝔤_x − dim 𝔤_{x,X}`. With `e = dim 𝔤_x − rank 𝔤_x`
(the dimension of the regular orbits), `δ ≤ e` and `dim O < e` for `O` non-regular, so
`D^G(x)^{1/2} D^{G_x}(X)^{1/2} |f_k| ≤ (D^G)^{1/2}(y_k) |θ(y_k)| ≤ B` with
`f_k = ∑_O c_O |ϖ|^{k(e − dim O)} ĵ(O, X) → ∑_{O ∈ s} c_O ĵ(O, X)`. -/
theorem sqrt_weylDisc_mul_norm_sum_le (x : ↥d.G) (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    {c : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) → ℂ}
    (hc : HasGermExpansion d.G d.lie d.bilin ψ θ x c)
    (s : Finset (NilOrbit (grpCentralizer d.G x)
      (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))))
    (hs : ∀ O, O ∈ s ↔
      O ∈ NilReg (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)))
    {X : d.ambient} (hX : X ∈ lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))
    (hXr : IsRegularSS (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) X)
    {U : Set ↥d.G} (hU : U ∈ 𝓝 x) {B : ℝ}
    (hB : ∀ z ∈ U, z ∈ regularSet d.G d.lie →
      Real.sqrt (weylDisc d.lie (z : d.ambientˣ)) * ‖θ z‖ ≤ B) :
    Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) *
        Real.sqrt (weylDiscLie (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) X) *
      ‖∑ O ∈ s, c O * jHat (grpCentralizer d.G x)
        (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) d.bilin ψ O X‖ ≤ B := by
  classical
  obtain ⟨hfin, ω, hω, hexp⟩ := hc
  -- dimensions
  set rep : NilOrbit G' 𝔤' → ↥𝔤' := fun O => ⟨(Quotient.out O).val, (Quotient.out O).property.1⟩
  set e : NilOrbit G' 𝔤' → ℕ := fun O =>
    Module.finrank F ↥𝔤' - Module.finrank F ↥(lieCentralizer 𝔤' ((rep O : ↥𝔤') : d.ambient))
  set er : ℕ := Module.finrank F ↥𝔤' - lieRank 𝔤'
  set δ : ℕ := Module.finrank F ↥𝔤' - Module.finrank F ↥(lieCentralizer 𝔤' X)
  have hδ : δ ≤ er := by
    simp only [δ, er]
    have := lieRank_le_finrank_lieCentralizer d 𝔤' hX
    have := finrank_lieCentralizer_le d 𝔤' X
    omega
  have hrk : ∀ O, lieRank 𝔤' ≤ Module.finrank F ↥(lieCentralizer 𝔤' ((rep O : ↥𝔤') : d.ambient)) ∧
      Module.finrank F ↥(lieCentralizer 𝔤' ((rep O : ↥𝔤') : d.ambient)) ≤ Module.finrank F ↥𝔤' :=
    fun O => ⟨lieRank_le_finrank_lieCentralizer d 𝔤' (rep O).property,
      finrank_lieCentralizer_le d 𝔤' _⟩
  have hreg : ∀ O, O ∈ NilReg G' 𝔤' ↔
      Module.finrank F ↥(lieCentralizer 𝔤' ((rep O : ↥𝔤') : d.ambient)) = lieRank 𝔤' := fun O =>
    ⟨fun h => h.2.2, fun h => ⟨(Quotient.out O).property.1, (Quotient.out O).property.2, h⟩⟩
  have he_reg : ∀ O, O ∈ NilReg G' 𝔤' → er - e O = 0 := fun O hO => by
    have := (hreg O).mp hO; have := hrk O; simp only [e, er]; omega
  have he_nreg : ∀ O, O ∉ NilReg G' 𝔤' → 0 < er - e O := fun O hO => by
    have h1 := (hreg O).not.mp hO; have := hrk O; simp only [e, er]; omega
  have he_le : ∀ O, e O ≤ er := fun O => by have := hrk O; simp only [e, er]; omega
  -- the finite set of orbits
  set S : Finset (NilOrbit G' 𝔤') := hfin.toFinset ∪ s
  have hsS : s ⊆ S := Finset.subset_union_right
  -- a uniformizer-like element
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one F
  have hϖne : ϖ ≠ 0 := norm_pos_iff.mp hϖ0
  set a : ℝ := absF ϖ
  have ha0 : 0 < a := absF_pos hϖne
  have ha1 : a < 1 := absF_lt_one_of_norm_lt_one hϖ1
  have hpow : Tendsto (fun k : ℕ => ϖ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hϖ1
  have hlam : Tendsto (fun k : ℕ => (ϖ ^ k) ^ 2) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using hpow.pow 2
    · exact Eventually.of_forall fun k => pow_ne_zero _ (pow_ne_zero _ hϖne)
  have := IsModuleTopology.toContinuousSMul F d.ambient
  have hY : Tendsto (fun k : ℕ => ((ϖ ^ k) ^ 2) • X) atTop (𝓝 0) := by
    simpa using (hpow.pow 2).smul_const X
  -- the events
  obtain ⟨ωr, hωr, hregG⟩ := exists_nhds_mul_expA_mem_regularSet d x hx
  have hev : ∀ᶠ k in atTop,
      ((ϖ ^ k) ^ 2) • X ∈ ω ∧ ((ϖ ^ k) ^ 2) • X ∈ ωr ∧
      (((ϖ ^ k) ^ 2) • X ∈ d.lie → ∃ g : ↥d.G, ((g : d.ambientˣ) : d.ambient) =
        expA F (((ϖ ^ k) ^ 2) • X)) ∧
      (∀ y : ↥d.G, ((y : d.ambientˣ) : d.ambient) =
        ((x : d.ambientˣ) : d.ambient) * expA F (((ϖ ^ k) ^ 2) • X) → y ∈ U) ∧
      (∀ y : ↥d.G, ((y : d.ambientˣ) : d.ambient) =
        ((x : d.ambientˣ) : d.ambient) * expA F (((ϖ ^ k) ^ 2) • X) →
        weylDisc d.lie (y : d.ambientˣ) = weylDisc d.lie (x : d.ambientˣ) *
          absF ((ϖ ^ k) ^ 2) ^ δ * weylDiscLie 𝔤' X) :=
    (hY.eventually hω).and ((hY.eventually hωr).and ((hY.eventually (eventually_expA_mem_G d)).and
      ((hY.eventually (eventually_mem_of_mul_expA d x hU)).and
        (hlam.eventually (eventually_weylDisc_mul_expA_smul d x hx hX hXr.1)))))
  -- the bracket `f_k`
  set f : ℕ → ℂ := fun k => ∑ O ∈ S, c O * (((a ^ k) ^ (er - e O) : ℝ) : ℂ) *
    jHat G' 𝔤' d.bilin ψ O X
  have hf : Tendsto f atTop (𝓝 (∑ O ∈ s, c O * jHat G' 𝔤' d.bilin ψ O X)) := by
    have hlim : (∑ O ∈ s, c O * jHat G' 𝔤' d.bilin ψ O X) =
        ∑ O ∈ S, (if O ∈ s then c O * jHat G' 𝔤' d.bilin ψ O X else 0) := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsS]
    rw [hlim]
    refine tendsto_finsetSum _ fun O _ => ?_
    by_cases hO : O ∈ s
    · simp only [hO, ↓reduceIte, he_reg O ((hs O).mp hO), pow_zero, Complex.ofReal_one, mul_one]
      exact tendsto_const_nhds
    · simp only [hO, ↓reduceIte]
      have hpos := he_nreg O (fun h => hO ((hs O).mpr h))
      have h0 : Tendsto (fun k : ℕ => (a ^ k) ^ (er - e O)) atTop (𝓝 0) := by
        simpa [zero_pow hpos.ne'] using
          (tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).pow (er - e O)
      have h0' := ((Complex.continuous_ofReal.tendsto 0).comp h0).const_mul (c O) |>.mul_const
        (jHat G' 𝔤' d.bilin ψ O X)
      simpa using h0'
  -- the bound for large `k`
  have hbound : ∀ᶠ k in atTop, Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) *
      Real.sqrt (weylDiscLie 𝔤' X) * ‖f k‖ ≤ B := by
    filter_upwards [hev] with k ⟨hkω, hkωr, hkG, hkU, hkD⟩
    set t : F := ϖ ^ k
    have ht : t ≠ 0 := pow_ne_zero _ hϖne
    have hat : absF t = a ^ k := absF_pow ϖ k
    set Y : d.ambient := (t ^ 2) • X
    have hYc : Y ∈ 𝔤' := LieSubalgebra.smul_mem _ _ hX
    have hYr : IsRegularSS 𝔤' Y := (isRegularSS_smul_iff (pow_ne_zero 2 ht) X).mpr hXr
    obtain ⟨g, hg⟩ := hkG (mem_lieCentralizer.mp hYc).1
    set y : ↥d.G := x * g
    have hy : ((y : d.ambientˣ) : d.ambient) = ((x : d.ambientˣ) : d.ambient) * expA F Y := by
      rw [← hg]; rfl
    have hyU := hkU y hy
    have hyr := hregG Y hkωr hYc hYr y hy
    have hθy := hexp Y hkω hYc hYr y hy
    have hBy := hB y hyU hyr
    -- `θ(y) = (|t|^{e})⁻¹ f_k`
    set b : ℝ := a ^ k
    have hb0 : 0 < b := pow_pos ha0 k
    have hb1 : b ≤ 1 := pow_le_one₀ ha0.le ha1.le
    have hθf : θ y = (((b ^ er)⁻¹ : ℝ) : ℂ) * f k := by
      rw [hθy, finsum_eq_sum_of_support_subset (s := S) _ (fun O hO => by
        have : O ∈ Function.support c := Function.support_mul_subset_left _ _ hO
        exact Finset.mem_union_left _ (hfin.mem_toFinset.mpr this)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun O _ => ?_
      rw [jHat_sq_smul_lieCentralizer d ψ x hx O (out_mem_nilOrbitSet d O) ht X hX hXr, hat]
      have hsplit : b ^ er = b ^ (er - e O) * b ^ e O := by
        rw [← pow_add, Nat.sub_add_cancel (he_le O)]
      have hbe : b ^ e O ≠ 0 := (pow_pos hb0 _).ne'
      have hbr : b ^ er ≠ 0 := (pow_pos hb0 _).ne'
      have key : ((b ^ e O)⁻¹ : ℝ) = (b ^ er)⁻¹ * b ^ (er - e O) := by
        rw [hsplit]; field_simp
      have heO : Module.finrank F ↥𝔤' - Module.finrank F ↥(lieCentralizer 𝔤'
          ((⟨(Quotient.out O).val, (Quotient.out O).property.1⟩ : ↥𝔤') : d.ambient)) = e O := rfl
      have hab : a ^ k = b := rfl
      rw [heO, hab, key]
      push_cast
      ring
    -- `D^G(y)^{1/2} = D^G(x)^{1/2} b^δ D'(X)^{1/2}`
    have hDy : Real.sqrt (weylDisc d.lie (y : d.ambientˣ)) =
        Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) * b ^ δ * Real.sqrt (weylDiscLie 𝔤' X) := by
      rw [hkD y hy, absF_pow, hat, ← pow_mul, mul_comm 2 δ, pow_mul,
        Real.sqrt_mul (by positivity [(weylDisc_pos d x).le]),
        Real.sqrt_mul (weylDisc_pos d x).le, Real.sqrt_sq (by positivity)]
    rw [hDy, hθf, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr
      (pow_nonneg hb0.le _))] at hBy
    have hbδ : b ^ er ≤ b ^ δ := pow_le_pow_of_le_one hb0.le hb1 hδ
    have hratio : 1 ≤ b ^ δ * (b ^ er)⁻¹ := by
      rw [le_mul_inv_iff₀ (pow_pos hb0 _), one_mul]; exact hbδ
    have hnn : 0 ≤ Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) * Real.sqrt (weylDiscLie 𝔤' X) *
        ‖f k‖ := by positivity
    calc Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) * Real.sqrt (weylDiscLie 𝔤' X) * ‖f k‖
        ≤ Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) * Real.sqrt (weylDiscLie 𝔤' X) * ‖f k‖ *
          (b ^ δ * (b ^ er)⁻¹) := le_mul_of_one_le_right hnn hratio
      _ = Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) * b ^ δ * Real.sqrt (weylDiscLie 𝔤' X) *
          ((b ^ er)⁻¹ * ‖f k‖) := by ring
      _ ≤ B := hBy
  exact le_of_tendsto ((tendsto_const_nhds.mul hf.norm)) hbound

/-- **Each regular germ is bounded by finitely many directions**: with `X_1, …, X_n ∈ 𝔤_x` regular
semisimple separating the regular `ĵ(O, ·)` (constant `C`, as given by
`exists_finset_bound_nilReg_coeff`) and `m ≤ D^{G_x}(X_j)^{1/2}`, `m > 0`,
`D^G(x)^{1/2} |c_{O₀}| ≤ C B / m` (`sqrt_weylDisc_mul_norm_sum_le` at each `X_j`). -/
theorem sqrt_weylDisc_mul_norm_coeff_le (x : ↥d.G) (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    {c : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) → ℂ}
    (hc : HasGermExpansion d.G d.lie d.bilin ψ θ x c)
    (s : Finset (NilOrbit (grpCentralizer d.G x)
      (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))))
    (hs : ∀ O, O ∈ s ↔
      O ∈ NilReg (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)))
    (O₀ : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)))
    {σ : Finset d.ambient} {C : ℝ}
    (hσ : ∀ X ∈ σ, X ∈ lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient) ∧
      IsRegularSS (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) X)
    (hlin : ∀ (a : NilOrbit (grpCentralizer d.G x)
        (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) → ℂ) (M : ℝ),
      (∀ X ∈ σ, ‖∑ O ∈ s, a O * jHat (grpCentralizer d.G x)
        (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) d.bilin ψ O X‖ ≤ M) →
      ‖a O₀‖ ≤ C * M)
    {m : ℝ} (hm : 0 < m)
    (hmX : ∀ X ∈ σ,
      m ≤ Real.sqrt (weylDiscLie (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) X))
    {U : Set ↥d.G} (hU : U ∈ 𝓝 x) {B : ℝ}
    (hB : ∀ z ∈ U, z ∈ regularSet d.G d.lie →
      Real.sqrt (weylDisc d.lie (z : d.ambientˣ)) * ‖θ z‖ ≤ B) :
    Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) * ‖c O₀‖ ≤ C * (B / m) := by
  have hD : 0 < Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) := Real.sqrt_pos.mpr (weylDisc_pos d x)
  have hM := hlin c (B / (Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) * m)) fun X hX => by
    have h := sqrt_weylDisc_mul_norm_sum_le ψ d x hx hc s hs (hσ X hX).1 (hσ X hX).2 hU hB
    have hmX' := hmX X hX
    have hDX : 0 < Real.sqrt
        (weylDiscLie (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) X) :=
      hm.trans_le hmX'
    have hB0 : 0 ≤ B := le_trans (by positivity) h
    rw [le_div_iff₀ (by positivity)]
    calc ‖_‖ * (Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) * m)
        ≤ ‖_‖ * (Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) *
          Real.sqrt (weylDiscLie (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) X)) := by
          gcongr
      _ ≤ B := by linarith
  calc Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) * ‖c O₀‖
      ≤ Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) *
        (C * (B / (Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) * m))) := by gcongr
    _ = C * (B / m) := by field_simp

end Point

/-! ## 5. Uniformity on `T_♮` -/

section Uniform

variable {θ : ↥d.G → ℂ}

/-- The bound of `sqrt_weylDisc_mul_norm_coeff_le` stated for data indexed by abstract `G'`, `𝔤'`
equal to the centralizers of `x` (so that one choice of data serves several `x`). -/
theorem norm_sqrt_weylDisc_mul_germ_le_of_eq (hθ : IsQuasiCharacter d.G d.lie d.bilin ψ θ)
    (x : ↥d.G) (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    {G' : Subgroup d.ambientˣ} {𝔤' : LieSubalgebra F d.ambient}
    (hG : grpCentralizer d.G x = G') (h𝔤 : lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient) = 𝔤')
    (s : Finset (NilOrbit G' 𝔤')) (hs : ∀ O, O ∈ s ↔ O ∈ NilReg G' 𝔤')
    {O₀ : NilOrbit G' 𝔤'} (hO₀ : O₀ ∈ NilReg G' 𝔤')
    {σ : Finset d.ambient} {C : ℝ} (hσ : ∀ X ∈ σ, X ∈ 𝔤' ∧ IsRegularSS 𝔤' X)
    (hlin : ∀ (a : NilOrbit G' 𝔤' → ℂ) (M : ℝ),
      (∀ X ∈ σ, ‖∑ O ∈ s, a O * jHat G' 𝔤' d.bilin ψ O X‖ ≤ M) → ‖a O₀‖ ≤ C * M)
    {m : ℝ} (hm : 0 < m) (hmX : ∀ X ∈ σ, m ≤ Real.sqrt (weylDiscLie 𝔤' X))
    {U : Set ↥d.G} (hU : U ∈ 𝓝 x) {B : ℝ}
    (hB : ∀ z ∈ U, z ∈ regularSet d.G d.lie →
      Real.sqrt (weylDisc d.lie (z : d.ambientˣ)) * ‖θ z‖ ≤ B)
    (O : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)))
    (hO : HEq O O₀) :
    ‖(Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) : ℂ) * germ d.G d.lie d.bilin ψ θ x O‖ ≤
      C * (B / m) := by
  subst hG h𝔤
  cases hO
  obtain ⟨c, hc⟩ := hθ.2 x hx
  rw [germ_eq_of_hasGermExpansion d ψ hx hc hO₀, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact sqrt_weylDisc_mul_norm_coeff_le ψ d x hx hc s hs O hσ hlin hm hmX hU hB

/-- **A bound on `T_♮` uniform in the point**: for `x ∈ Γ(G,H)` there is `K ≥ 0` such that for
every `t ∈ Γ(G,H)` with `T_t = T_x`, every neighbourhood `U` of `t` and every `B ≥ 0` bounding
`(D^G)^{1/2}|θ|` on the regular points of `U`, `D^G(t)^{1/2} |c_{θ,O_t}(t)| ≤ K B`. The
centralizers and `O_t` do not depend on `t ∈ T_♮`, so the directions and constants of
`exists_finset_bound_nilReg_coeff` at `x` serve every `t`. Status: proved from `finite_nilReg`
(SORRY). -/
theorem exists_uniform_germ_bound (hθ : IsQuasiCharacter d.G d.lie d.bilin ψ θ)
    {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ↥(GSpin d.QW), d.IsGammaElt t → d.torusOf t = d.torusOf x →
      ∀ U ∈ 𝓝 (d.diag t), ∀ B : ℝ, 0 ≤ B →
      (∀ z ∈ U, z ∈ regularSet d.G d.lie →
        Real.sqrt (weylDisc d.lie (z : d.ambientˣ)) * ‖θ z‖ ≤ B) →
      ‖(Real.sqrt (weylDisc d.lie (d.diag t : d.ambientˣ)) : ℂ) *
        germ d.G d.lie d.bilin ψ θ (d.diag t) (orbitChoice d t)‖ ≤ K * B := by
  classical
  have hx₀ : IsSS F (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient) := isSS_diag_of_isSS d hx.1
  have hdata : ∀ t : ↥(GSpin d.QW), d.IsGammaElt t → d.torusOf t = d.torusOf x →
      grpCentralizer d.G (d.diag t : d.ambientˣ) = grpCentralizer d.G (d.diag x : d.ambientˣ) ∧
      lieCentralizer d.lie ((d.diag t : d.ambientˣ) : d.ambient) =
        lieCentralizer d.lie ((d.diag x : d.ambientˣ) : d.ambient) ∧
      HEq (orbitChoice d t) (orbitChoice d x) := fun t ht hT =>
    have htx : t ∈ d.torusOf x := hT ▸ d.self_mem_torusOf t
    ⟨grpCentralizer_diag_eq_of_torusOf_eq d hx ht htx hT,
      lieCentralizer_diag_eq_of_torusOf_eq d hx ht htx hT,
      orbitChoice_heq_of_torusOf_eq d hx ht htx hT⟩
  by_cases hO₀ : orbitChoice d x ∈ NilReg (grpCentralizer d.G (d.diag x : d.ambientˣ))
      (lieCentralizer d.lie ((d.diag x : d.ambientˣ) : d.ambient))
  · set s := (finite_nilReg d (d.diag x) hx₀).toFinset
    have hs : ∀ O, O ∈ s ↔ O ∈ NilReg (grpCentralizer d.G (d.diag x : d.ambientˣ))
        (lieCentralizer d.lie ((d.diag x : d.ambientˣ) : d.ambient)) := fun O =>
      Set.Finite.mem_toFinset _
    obtain ⟨σ, C, hC, hσ, hlin⟩ := exists_finset_bound_nilReg_coeff d ψ (d.diag x) hx₀ s
      Filter.univ_mem hO₀ ((hs _).mpr hO₀)
    -- a positive lower bound for `D^{G_x}(X)^{1/2}` on `σ`
    obtain ⟨m, hm, hmX⟩ : ∃ m : ℝ, 0 < m ∧ ∀ X ∈ σ, m ≤ Real.sqrt (weylDiscLie
        (lieCentralizer d.lie ((d.diag x : d.ambientˣ) : d.ambient)) X) := by
      by_cases hσe : σ.Nonempty
      · refine ⟨σ.inf' hσe fun X => Real.sqrt (weylDiscLie
          (lieCentralizer d.lie ((d.diag x : d.ambientˣ) : d.ambient)) X), ?_,
          fun X hX => Finset.inf'_le _ hX⟩
        rw [Finset.lt_inf'_iff]
        exact fun X hX => Real.sqrt_pos.mpr (weylDiscLie_pos d _ (hσ X hX).2.1)
      · exact ⟨1, one_pos, fun X hX => (hσe ⟨X, hX⟩).elim⟩
    refine ⟨C / m, div_nonneg hC hm.le, fun t ht hT U hU B _ hB => ?_⟩
    obtain ⟨hG, h𝔤, hO⟩ := hdata t ht hT
    have := norm_sqrt_weylDisc_mul_germ_le_of_eq ψ d hθ (d.diag t) (isSS_diag_of_isSS d ht.1)
      hG h𝔤 s hs hO₀ (fun X hX => ⟨(hσ X hX).2.1, (hσ X hX).2.2⟩) hlin hm hmX hU hB _ hO
    calc _ ≤ C * (B / m) := this
      _ = C / m * B := by ring
  · refine ⟨0, le_rfl, fun t ht hT U _ B _ _ => ?_⟩
    obtain ⟨hG, h𝔤, hO⟩ := hdata t ht hT
    rw [germ_of_not_mem (fun h => hO₀ ((mem_nilReg_congr d hG h𝔤 hO).mp h))]
    simp

end Uniform

/-! ## 6. The global bound on `T_♮` -/

/-- **`D^G(t)^{1/2} |c_{θ,O_t}(t)|` is bounded on `T_♮`** for `θ ∈ QC(G(F), χ)` (Thesis
Prop 12.1.1(i), proof of (12.1.2)). The function `t ↦ D^G(t)^{1/2} |c_{θ,O_t}(t)|` (`0` off `T_♮`)
on `T(F)` is `A_{G,H}(F)`-invariant and bounded near every point of `T(F)`: at `t₁ ∈ T(F)`, BP
Prop 4.1.1(ii) (`bp_sqrt_weylDisc_mul_locallyBounded`) bounds `(D^G)^{1/2}|θ|` on the regular points
of a neighbourhood `U` of `t₁`, and `exists_uniform_germ_bound` converts this into a bound at every
`t ∈ T_♮` near `t₁`. As `T(F)/A_{G,H}(F)` is compact, the function is bounded
(`exists_bound_of_locallyBounded`). Status: proved from `finite_nilReg` (SORRY). -/
theorem germ_bound_of_mem_QC_aux {χ : CentralCharOn d} {θ : ↥d.G → ℂ} (hθ : θ ∈ QC d χ)
    (T : Subgroup ↥(GSpin d.QW)) :
    ∃ C : ℝ, ∀ t : ↥(GSpin d.QW), d.IsGammaElt t → d.torusOf t = T →
      ‖(Real.sqrt (weylDisc d.lie (d.diag t : d.ambientˣ)) : ℂ) *
        germ d.G d.lie d.bilin ψ θ (d.diag t) (orbitChoice d t)‖ ≤ C := by
  classical
  by_cases hT : ∃ x, d.IsGammaElt x ∧ d.torusOf x = T
  swap
  · exact ⟨0, fun t ht hTt => (hT ⟨t, ht, hTt⟩).elim⟩
  obtain ⟨x, hx, rfl⟩ := hT
  obtain ⟨K, hK0, hK⟩ := exists_uniform_germ_bound ψ d (hθ.1 ψ) hx
  have : CompactSpace (d.TorusQuot (d.torusOf x)) := hx.2.2
  let g : ↥(GSpin d.QW) → ℝ := fun t => if d.IsGammaElt t ∧ d.torusOf t = d.torusOf x then
    ‖(Real.sqrt (weylDisc d.lie (d.diag t : d.ambientˣ)) : ℂ) *
      germ d.G d.lie d.bilin ψ θ (d.diag t) (orbitChoice d t)‖ else 0
  have hinv : ∀ t : ↥(d.torusOf x), ∀ n ∈ d.scalarsIn (d.torusOf x),
      g ((t * n : ↥(d.torusOf x)) : ↥(GSpin d.QW)) = g t := by
    intro t n hn
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hn
    have htn : ((t * n : ↥(d.torusOf x)) : ↥(GSpin d.QW)) = scalarGSpin d.QW c * t := by
      rw [Subgroup.coe_mul, ← hc, (scalarGSpin_commute d.QW c t).eq]
    rw [htn]
    simp only [g, isGammaElt_scalar_mul_iff d c t, torusOf_scalar_mul d c t]
    split_ifs with h
    · rw [weylDisc_diag_scalar_mul d c t, germ_scalar_mul_of_mem_QC ψ d hθ c t h.1.1]
    · rfl
  have hloc : ∀ t : ↥(d.torusOf x), ∃ V ∈ 𝓝 t, ∃ C : ℝ, ∀ t' ∈ V,
      g (t' : ↥(GSpin d.QW)) ≤ C := by
    intro t
    obtain ⟨U, hU, B, hB⟩ := bp_sqrt_weylDisc_mul_locallyBounded d ψ (hθ.1 ψ)
      (d.diag (t : ↥(GSpin d.QW)))
    have hcont : Continuous fun t' : ↥(d.torusOf x) => d.diag (t' : ↥(GSpin d.QW)) :=
      (continuous_diag d).comp continuous_subtypeVal
    refine ⟨(fun t' : ↥(d.torusOf x) => d.diag (t' : ↥(GSpin d.QW))) ⁻¹' interior U,
      hcont.continuousAt.preimage_mem_nhds (interior_mem_nhds.mpr hU), K * max B 0,
      fun t' ht' => ?_⟩
    simp only [g]
    split_ifs with h
    · refine hK _ h.1 h.2 U (mem_interior_iff_mem_nhds.mp ht') (max B 0) (le_max_right _ _)
        fun z hz hzr => (hB z hz hzr).trans (le_max_left _ _)
    · exact mul_nonneg hK0 (le_max_right _ _)
  obtain ⟨C, hC⟩ := exists_bound_of_locallyBounded (d.scalarsIn (d.torusOf x))
    (fun t : ↥(d.torusOf x) => g t) hinv hloc
  refine ⟨C, fun t ht hTt => ?_⟩
  have := hC ⟨t, hTt ▸ d.self_mem_torusOf t⟩
  simpa [g, ht, hTt] using this

end GSpinGGP
