/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Interface
import GSpinGGP.TraceFormula.GermTranslate

/-!
# Measurability of the integrand of `m_{geom,s}` on `T(F)/A_{G,H}(F)`

The integral `torusIntegral` evaluates `t ↦ D^G(t)^{1/2} c_{θ,O_t}(t) Δ(t)^{s-1/2}` (set to `0`
off `T_♮`) on chosen coset representatives `Quotient.out q`.  This file reduces measurability of
that function of `q ∈ T(F)/A_{G,H}(F)` (used in Thesis Prop 12.1.1(i), proof of (12.1.2)) to
three precisely stated inputs on `T(F)` itself:

* `gammaIntegrand_scalar_mul_of_mem_QC`: the integrand is `A_{G,H}(F)`-invariant;
* `isOpen_torusNat`: `T_♮ = {t ∈ T | t ∈ Γ(G,H), T_t = T}` is open in `T(F)`;
* `continuousOn_gammaIntegrand_of_mem_QC`: the integrand is continuous on `T_♮`.

The reduction is the general descent lemma `aestronglyMeasurable_comp_out`: a function on a
topological group that is invariant under a normal subgroup `N`, continuous on an open set and `0`
off it, evaluated on coset representatives, is a.e.-strongly measurable on `G/N` for every
measure. -/

noncomputable section

open MeasureTheory Topology Filter

set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

/-! ## 1. The descent lemma -/

section Descent

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Evaluating an `N`-invariant function on coset representatives gives its descent:
`f (out (mk g)) = f g`. -/
theorem comp_out_mk_of_invariant (N : Subgroup G) {f : G → ℂ}
    (hinv : ∀ g, ∀ n ∈ N, f (g * n) = f g) (g : G) :
    f (Quotient.out (QuotientGroup.mk g : G ⧸ N)) = f g := by
  obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N g
  rw [hn]
  exact hinv g n n.2

/-- **Descent of measurability to `G/N`.**  Let `f : G → ℂ` be invariant under right
multiplication by `N`, continuous on an open set `U` and `0` off `U`.  Then
`q ↦ f (Quotient.out q)` is a.e.-strongly measurable on `G/N` (Borel σ-algebra) for every
measure: it is the descent of `f`, continuous on the open set `mk(U)` (the quotient map is open)
and `0` off it. -/
theorem aestronglyMeasurable_comp_out (N : Subgroup G) [MeasurableSpace (G ⧸ N)]
    [BorelSpace (G ⧸ N)] (μ : Measure (G ⧸ N)) {f : G → ℂ}
    (hinv : ∀ g, ∀ n ∈ N, f (g * n) = f g) {U : Set G} (hU : IsOpen U)
    (hf0 : ∀ g ∉ U, f g = 0) (hfc : ContinuousOn f U) :
    AEStronglyMeasurable (fun q : G ⧸ N => f (Quotient.out q)) μ := by
  set F' : G ⧸ N → ℂ := fun q => f (Quotient.out q)
  have hmk : ∀ g, F' (QuotientGroup.mk g) = f g := comp_out_mk_of_invariant N hinv
  set V : Set (G ⧸ N) := (QuotientGroup.mk : G → G ⧸ N) '' U
  have hV : IsOpen V := QuotientGroup.isOpenMap_coe U hU
  have hF0 : ∀ q ∉ V, F' q = 0 := fun q hq => by
    refine hf0 _ fun hu => hq ⟨_, hu, ?_⟩
    exact QuotientGroup.out_eq' q
  have hFc : ContinuousOn F' V := by
    rintro _ ⟨u, hu, rfl⟩
    refine ContinuousAt.continuousWithinAt ?_
    have hfu : ContinuousAt f u := hfc.continuousAt (hU.mem_nhds hu)
    intro W hW
    rw [hmk] at hW
    have h1 : f ⁻¹' W ∈ 𝓝 u := hfu hW
    have h2 := (QuotientGroup.isOpenMap_coe (N := N)).image_mem_nhds h1
    refine Filter.mem_map.mpr (Filter.mem_of_superset h2 ?_)
    rintro _ ⟨x, hx, rfl⟩
    change F' (QuotientGroup.mk x) ∈ W
    rw [hmk]
    exact hx
  have hind : F' = V.indicator F' := by
    funext q
    by_cases hq : q ∈ V
    · rw [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_notMem hq, hF0 q hq]
  rw [hind, aestronglyMeasurable_indicator_iff hV.measurableSet]
  exact hFc.aestronglyMeasurable hV.measurableSet

end Descent

/-! ## 2. The three inputs on `T(F)` -/

section Inputs

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
variable (ψ : NontrivialAddChar F) (d : GGPData F)

/-- `W'_{ct} = W'_t` for central scalars `c` (`P(ct) = P(t)`). -/
theorem fixedSub_scalar_mul (c : Fˣ) (t : ↥(GSpin d.QW)) :
    fixedSub (scalarGSpin d.QW c * t) = fixedSub t := by
  rw [fixedSub, fixedSub, map_mul, specP_scalarGSpin, one_mul]

/-- `T_{ct} = T_t` for central scalars `c`. -/
theorem torusOf_scalar_mul (c : Fˣ) (t : ↥(GSpin d.QW)) :
    d.torusOf (scalarGSpin d.QW c * t) = d.torusOf t := by
  unfold GGPData.torusOf
  rw [fixedSub_scalar_mul d c t]
  congr 1
  ext g
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  rw [← mul_assoc g, ← (scalarGSpin_commute d.QW c g).eq]
  simp only [mul_assoc]
  exact mul_right_inj (scalarGSpin d.QW c)

/-- `ct` is semisimple iff `t` is, for `c ∈ F^×`. -/
theorem isSS_scalar_mul_iff (c : Fˣ) (t : ↥(GSpin d.QW)) :
    IsSS F (((scalarGSpin d.QW c * t : ↥(GSpin d.QW)) : (CliffordAlgebra d.QW)ˣ) :
      CliffordAlgebra d.QW) ↔
      IsSS F (((t : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW) := by
  have hcoe : (((scalarGSpin d.QW c * t : ↥(GSpin d.QW)) : (CliffordAlgebra d.QW)ˣ) :
      CliffordAlgebra d.QW) = (c : F) • (((t : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW) := by
    rw [Algebra.smul_def]; rfl
  have hL : ∀ (a : F) (y : CliffordAlgebra d.QW),
      LinearMap.mulLeft F (a • y) = a • LinearMap.mulLeft F y := fun a y => by
    ext w; simp
  rw [hcoe]
  unfold IsSS
  constructor
  · intro h
    have h' := Module.End.IsSemisimple_smul ((c : F)⁻¹) h
    rwa [← hL, smul_smul, inv_mul_cancel₀ c.ne_zero, one_smul] at h'
  · intro h
    rw [hL]
    exact Module.End.IsSemisimple_smul _ h

/-- `ct ∈ Γ(G,H)` iff `t ∈ Γ(G,H)`, for `c ∈ F^×`. -/
theorem isGammaElt_scalar_mul_iff (c : Fˣ) (t : ↥(GSpin d.QW)) :
    d.IsGammaElt (scalarGSpin d.QW c * t) ↔ d.IsGammaElt t := by
  unfold GGPData.IsGammaElt
  rw [torusOf_scalar_mul d c t, isSS_scalar_mul_iff d c t]

/-- `diag(ct) = c · diag(t)` in the ambient algebra. -/
theorem coe_diag_scalar_mul (c : Fˣ) (t : ↥(GSpin d.QW)) :
    (((d.diag (scalarGSpin d.QW c * t) : ↥d.G) : d.ambientˣ) : d.ambient) =
      algebraMap F d.ambient (c : F) * (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient) := by
  rw [map_mul, Subgroup.coe_mul, Units.val_mul, coe_diag_scalarGSpin]

/-- For a nonzero scalar `c`: `y (c a) = (c a) y ↔ y a = a y`. -/
theorem algebraMap_mul_commute_iff {A : Type*} [Ring A] [Algebra F A] {c : F} (hc : c ≠ 0)
    (a y : A) : y * (algebraMap F A c * a) = (algebraMap F A c * a) * y ↔ y * a = a * y := by
  rw [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
  exact smul_right_inj hc

/-- `(c⁻¹)` is the inverse of a unit acting as the scalar `c`. -/
theorem val_inv_of_val_eq_algebraMap {A : Type*} [Ring A] [Algebra F A] {c : F} (hc : c ≠ 0)
    (u : Aˣ) (hu : (u : A) = algebraMap F A c) : ((u⁻¹ : Aˣ) : A) = algebraMap F A c⁻¹ :=
  Units.inv_eq_of_mul_eq_one_right (by rw [hu, ← map_mul, mul_inv_cancel₀ hc, map_one])

/-- `Ad(u x) = Ad(x)` for a central unit `u`. -/
theorem conjAd_central_mul {A : Type*} [Ring A] [Algebra F A] (u x : Aˣ)
    (hu : ∀ a : A, (u : A) * a = a * u) : conjAd F (u * x) = conjAd F x := by
  refine AlgEquiv.ext fun X => ?_
  show ((u * x : Aˣ) : A) * X * (((u * x)⁻¹ : Aˣ) : A) = (x : A) * X * ((x⁻¹ : Aˣ) : A)
  rw [mul_inv_rev, Units.val_mul, Units.val_mul]
  calc (u : A) * x * X * (↑x⁻¹ * ↑u⁻¹) = (u : A) * (x * X * ↑x⁻¹) * ↑u⁻¹ := by
        simp only [mul_assoc]
    _ = (x * X * ↑x⁻¹) * u * ↑u⁻¹ := by rw [hu]
    _ = (x : A) * X * ↑x⁻¹ := by rw [mul_assoc _ (u : A), Units.mul_inv, mul_one]

/-- `D^G(ct) = D^G(t)` (`Ad(ct) = Ad(t)`). -/
theorem weylDisc_diag_scalar_mul (c : Fˣ) (t : ↥(GSpin d.QW)) :
    weylDisc d.lie (d.diag (scalarGSpin d.QW c * t) : d.ambientˣ) =
      weylDisc d.lie (d.diag t : d.ambientˣ) := by
  have h : conjAd F (d.diag (scalarGSpin d.QW c * t) : d.ambientˣ) =
      conjAd F (d.diag t : d.ambientˣ) := by
    rw [map_mul, Subgroup.coe_mul]
    refine conjAd_central_mul _ _ fun a => ?_
    rw [coe_diag_scalarGSpin]
    exact Algebra.commutes _ _
  unfold weylDisc
  rw [h]

/-- `OrbitSpec d (ct) = OrbitSpec d t` (it only depends on `W'_t`). -/
theorem orbitSpec_scalar_mul (c : Fˣ) (t : ↥(GSpin d.QW)) :
    OrbitSpec d (scalarGSpin d.QW c * t) = OrbitSpec d t := by
  funext X
  unfold OrbitSpec
  rw [fixedSub_scalar_mul d c t]

/-- `O_x` and `O_{x'}` correspond when `x, x'` have the same centralizers and the same `OrbitSpec`. -/
theorem orbitChoice_heq_of_eq {x x' : ↥(GSpin d.QW)}
    (hH : grpCentralizer d.G (d.diag x : d.ambientˣ) = grpCentralizer d.G (d.diag x' : d.ambientˣ))
    (h𝔥 : lieCentralizer d.lie ((d.diag x : d.ambientˣ) : d.ambient) =
      lieCentralizer d.lie ((d.diag x' : d.ambientˣ) : d.ambient))
    (hP : OrbitSpec d x = OrbitSpec d x') :
    HEq (orbitChoice d x) (orbitChoice d x') := by
  rw [orbitChoice_eq_pickNilOrbit, orbitChoice_eq_pickNilOrbit]
  exact heq_pickNilOrbit _ _ _ _ hH h𝔥 _ _ hP

/-- `G_{ct} = G_t` for central scalars `c`. -/
theorem grpCentralizer_diag_scalar_mul (c : Fˣ) (t : ↥(GSpin d.QW)) :
    grpCentralizer d.G (d.diag (scalarGSpin d.QW c * t) : d.ambientˣ) =
      grpCentralizer d.G (d.diag t : d.ambientˣ) := by
  have hx := coe_diag_scalar_mul d c t
  ext g
  simp only [grpCentralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq]
  refine and_congr_right fun _ => ?_
  rw [Units.ext_iff, Units.ext_iff, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul,
    hx, eq_comm, algebraMap_mul_commute_iff c.ne_zero, eq_comm]

/-- `𝔤_{ct} = 𝔤_t` for central scalars `c`. -/
theorem lieCentralizer_diag_scalar_mul (c : Fˣ) (t : ↥(GSpin d.QW)) :
    lieCentralizer d.lie ((d.diag (scalarGSpin d.QW c * t) : d.ambientˣ) : d.ambient) =
      lieCentralizer d.lie ((d.diag t : d.ambientˣ) : d.ambient) := by
  have hx := coe_diag_scalar_mul d c t
  refine LieSubalgebra.ext _ _ fun X => ?_
  rw [mem_lieCentralizer, mem_lieCentralizer, hx]
  refine and_congr_right fun _ => ?_
  rw [eq_comm, algebraMap_mul_commute_iff c.ne_zero, eq_comm]

/-- `O_{ct}` and `O_t` correspond. -/
theorem orbitChoice_scalar_mul_heq (c : Fˣ) (t : ↥(GSpin d.QW)) :
    HEq (orbitChoice d (scalarGSpin d.QW c * t)) (orbitChoice d t) :=
  orbitChoice_heq_of_eq d (grpCentralizer_diag_scalar_mul d c t)
    (lieCentralizer_diag_scalar_mul d c t) (orbitSpec_scalar_mul d c t)

/-- **Germs are `A_{G,H}(F)`-invariant**: for `θ ∈ QC(G(F), χ)` (`χ` trivial on `A_{G,H}(F)`),
`c ∈ F^×` and `t` semisimple, `c_{θ,O_{ct}}(ct) = c_{θ,O_t}(t)`.  `θ(c y) = θ(y)` on `G_reg(F)`,
`x e^X` is regular for `X ∈ 𝔤_x` small and regular (`exists_nhds_mul_expA_mem_regularSet`), and
`ct`, `t` have the same centralizers, so a local expansion at `t` is one at `ct`
(`germ_eq_germ_of_translate`); `O_{ct}` and `O_t` correspond (`heq_pickNilOrbit`). -/
theorem germ_scalar_mul_of_mem_QC {χ : CentralCharOn d} {θ : ↥d.G → ℂ}
    (hθ : θ ∈ QC d χ) (c : Fˣ) (t : ↥(GSpin d.QW))
    (ht : IsSS F (((t : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW)) :
    germ d.G d.lie d.bilin ψ θ (d.diag (scalarGSpin d.QW c * t))
        (orbitChoice d (scalarGSpin d.QW c * t)) =
      germ d.G d.lie d.bilin ψ θ (d.diag t) (orbitChoice d t) := by
  set z := d.diag (scalarGSpin d.QW c) with hzdef
  have hz : (((z : d.G) : d.ambientˣ) : d.ambient) = algebraMap F d.ambient (c : F) :=
    coe_diag_scalarGSpin c
  have hx : ((d.diag (scalarGSpin d.QW c * t) : d.ambientˣ) : d.ambient) =
      algebraMap F d.ambient (c : F) * ((d.diag t : d.ambientˣ) : d.ambient) :=
    coe_diag_scalar_mul d c t
  have hss' : IsSS F (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient) := isSS_diag_of_isSS d ht
  have hss : IsSS F (((d.diag (scalarGSpin d.QW c * t) : ↥d.G) : d.ambientˣ) : d.ambient) :=
    isSS_diag_of_isSS d ((isSS_scalar_mul_iff d c t).mpr ht)
  have hH := grpCentralizer_diag_scalar_mul d c t
  have h𝔥 := lieCentralizer_diag_scalar_mul d c t
  refine germ_eq_germ_of_translate ψ θ _ _ hss hss' hH h𝔥 ?_ ((hθ.1 ψ).2 _ hss') _ _ ?_
  · obtain ⟨ω, hω, hreg⟩ := exists_nhds_mul_expA_mem_regularSet d _ hss
    refine ⟨ω, hω, fun X hX hXc hXr y hy => ⟨z⁻¹ * y, ?_, ?_⟩⟩
    · rw [Subgroup.coe_mul, Units.val_mul, InvMemClass.coe_inv, hy, map_mul, Subgroup.coe_mul,
        Units.val_mul, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul]
    · have hyr : y ∈ regularSet d.G d.lie := hreg X hX hXc hXr y hy
      have hy'r : z⁻¹ * y ∈ regularSet d.G d.lie := by
        show IsRegularSS d.lie (((z⁻¹ * y : d.G) : d.ambientˣ) : d.ambient)
        have : (((z⁻¹ * y : d.G) : d.ambientˣ) : d.ambient) =
            algebraMap F d.ambient ((c : F)⁻¹) * ((y : d.ambientˣ) : d.ambient) := by
          rw [Subgroup.coe_mul, Units.val_mul, InvMemClass.coe_inv,
            val_inv_of_val_eq_algebraMap c.ne_zero _ hz]
        rw [this]
        exact isRegularSS_algebraMap_mul d.lie (inv_ne_zero c.ne_zero) hyr
      have hzAGH : z ∈ d.AGH := ⟨c, rfl⟩
      have hzAG : z ∈ d.AG := d.AGH_le_AG hzAGH
      have h1 : θ (((⟨z, hzAG⟩ : ↥d.AG) : ↥d.G) * (z⁻¹ * y)) =
          (((χ.toHom ⟨z, hzAG⟩)⁻¹ : Circle) : ℂ) * θ (z⁻¹ * y) := hθ.2 ⟨z, hzAG⟩ (z⁻¹ * y) hy'r
      have h2 : ((⟨z, hzAG⟩ : ↥d.AG) : ↥d.G) * (z⁻¹ * y) = y := mul_inv_cancel_left z y
      have h3 : χ.toHom ⟨z, hzAG⟩ = 1 := χ.trivial_AGH z hzAGH
      have key : ∀ u : Circle, u = 1 → ∀ a b : ℂ, a = ((u⁻¹ : Circle) : ℂ) * b → a = b := by
        rintro u rfl a b h
        simpa using h
      have h4 := key _ h3 _ _ h1
      calc θ y = θ (((⟨z, hzAG⟩ : ↥d.AG) : ↥d.G) * (z⁻¹ * y)) := by rw [h2]
        _ = θ (z⁻¹ * y) := h4
  · exact orbitChoice_scalar_mul_heq d c t

/-- **The integrand of `m_{geom,s}` is `A_{G,H}(F)`-invariant** (Thesis §6.5: the integral is over
`A_{G,H}(F)\T(F)`).  For `c ∈ F^×` and `θ ∈ QC(G(F), χ)`:
`c·t ∈ T_♮ ⇔ t ∈ T_♮` (`P(ct) = P(t)`, and `ct`, `t` have the same centralizer), `D^G(ct) = D^G(t)`
(`Ad(ct) = Ad(t)`), `Δ(ct) = Δ(t)` (`deltaGGP_scalar_mul`), and `c_{θ,O_{ct}}(ct) = c_{θ,O_t}(t)`
(`germ_scalar_mul_of_mem_QC`). -/
theorem gammaIntegrand_scalar_mul_of_mem_QC {χ : CentralCharOn d} {θ : ↥d.G → ℂ}
    (hθ : θ ∈ QC d χ) (T : Subgroup ↥(GSpin d.QW)) (s : ℝ) (c : Fˣ) (t : ↥(GSpin d.QW)) :
    gammaIntegrand ψ d θ T s (scalarGSpin d.QW c * t) = gammaIntegrand ψ d θ T s t := by
  unfold gammaIntegrand
  rw [isGammaElt_scalar_mul_iff d c t, torusOf_scalar_mul d c t]
  split_ifs with h
  · rw [weylDisc_diag_scalar_mul d c t, deltaGGP_scalar_mul,
      germ_scalar_mul_of_mem_QC ψ d hθ c t h.1.1]
  · rfl

/-- **`T_♮` is open in `T(F)`** (Thesis §6.5: `T_♮` is Zariski open in `T`).  Why: for
`t₀ ∈ T_♮` and `t ∈ T` near `t₀`, `t` fixes `W'_{t₀}` (`t ∈ T`) and `rk(P(t) − 1) ≥ rk(P(t₀) − 1)`
(lower semicontinuity of the rank), so `W'_t = W'_{t₀}`; `P(t)|_{W''}` stays regular in
`SO(W'')`, so `T_t = T`; and the clauses of `IsGammaElt t` follow from `T_t = T`
(elements of the torus `T` are semisimple; `T` is commutative; `T(F)/A_{G,H}(F)` is compact).
Status: SORRY (own work). -/
theorem isOpen_torusNat (T : Subgroup ↥(GSpin d.QW)) :
    IsOpen {t : ↥T | d.IsGammaElt (t : ↥(GSpin d.QW)) ∧ d.torusOf (t : ↥(GSpin d.QW)) = T} := by
  sorry

/-- **The integrand of `m_{geom,s}` is continuous on `T_♮`** (Thesis Prop 12.1.1(i)).  Why: on
`T_♮` the subspaces `W'_t = W'_T`, `W''_t = W''_T` and the centralizers `G_t`, `𝔤_t` are constant,
so `D^G(t) = |det(1 − Ad t)|_{𝔤/𝔤_T}|` and `Δ(t) = |det(P(t) − 1)|_{W''_T}|` are continuous; and
`t ↦ c_{θ,O_t}(t)` is locally constant: for `t' = t e^Y` with `Y ∈ Lie T` small (central in
`𝔤_t`), `θ(t' e^X) = θ(t e^{X+Y})`, and `ĵ(O, X + Y) = ĵ(O, X)` on `𝔤_{t,reg}` (`b(Y, N) = 0`
for `N` nilpotent commuting with `Y`), so the expansion at `t` is one at `t'` with the same
coefficients, while `O_{t'} = O_t` (`OrbitSpec d t' = OrbitSpec d t`).
Status: SORRY (own work, GSpin input). -/
theorem continuousOn_gammaIntegrand_of_mem_QC {χ : CentralCharOn d} {θ : ↥d.G → ℂ}
    (hθ : θ ∈ QC d χ) (T : Subgroup ↥(GSpin d.QW)) (s : ℝ) :
    ContinuousOn (fun t : ↥T => gammaIntegrand ψ d θ T s (t : ↥(GSpin d.QW)))
      {t : ↥T | d.IsGammaElt (t : ↥(GSpin d.QW)) ∧ d.torusOf (t : ↥(GSpin d.QW)) = T} := by
  sorry

end Inputs

/-! ## 3. Assembly -/

section Assembly

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
variable (ψ : NontrivialAddChar F) (d : GGPData F)

/-- **Measurability of the integrand of `m_{geom,s}` on `T(F)/A_{G,H}(F)`**, from the three
inputs of §2 by `aestronglyMeasurable_comp_out` (for any measure on the quotient). -/
theorem aestronglyMeasurable_torusFn_of_inputs {χ : CentralCharOn d} {θ : ↥d.G → ℂ}
    (hθ : θ ∈ QC d χ) (T : Subgroup ↥(GSpin d.QW)) (s : ℝ)
    [MeasurableSpace (d.TorusQuot T)] [BorelSpace (d.TorusQuot T)]
    (μ : Measure (d.TorusQuot T)) :
    AEStronglyMeasurable (fun q : d.TorusQuot T =>
      gammaIntegrand ψ d θ T s ((Quotient.out q : ↥T) : ↥(GSpin d.QW))) μ := by
  refine aestronglyMeasurable_comp_out (d.scalarsIn T) μ
    (f := fun t : ↥T => gammaIntegrand ψ d θ T s (t : ↥(GSpin d.QW))) ?_ (isOpen_torusNat d T)
    ?_ (continuousOn_gammaIntegrand_of_mem_QC ψ d hθ T s)
  · intro g n hn
    obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf).mp hn
    change gammaIntegrand ψ d θ T s ((g : ↥(GSpin d.QW)) * (n : ↥(GSpin d.QW))) = _
    rw [← hc, ← (scalarGSpin_commute d.QW c g).eq]
    exact gammaIntegrand_scalar_mul_of_mem_QC ψ d hθ T s c g
  · intro g hg
    have hg' : ¬ (d.IsGammaElt (g : ↥(GSpin d.QW)) ∧ d.torusOf (g : ↥(GSpin d.QW)) = T) := hg
    simp only [gammaIntegrand, hg', ↓reduceIte]

end Assembly

end GSpinGGP
