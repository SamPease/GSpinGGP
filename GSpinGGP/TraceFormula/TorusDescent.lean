/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Interface
import GSpinGGP.TraceFormula.GermTranslate
import GSpinGGP.GGP.MovedCentralizer
import GSpinGGP.Foundations.RankSemicontinuity
import GSpinGGP.Foundations.Determinant
import GSpinGGP.GGP.IsometrySemisimple
import GSpinGGP.GGP.GSpinSemisimple
import GSpinGGP.TraceFormula.ThetaF
import GSpinGGP.TraceFormula.JHatSelfDual

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

/-! ### `T_♮` is open in `T(F)` -/

open scoped TensorProduct

omit [NontriviallyNormedField F] [PAdicField F] in
/-- `W'_x = ker(P(x) − 1)` is the set of `v` with `ι(v)` commuting with `x`. -/
theorem mem_fixedSub_iff_commute_ι {K V : Type*} [Field K] [Invertible (2 : K)] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (x : GSpin Q) (v : V) :
    v ∈ fixedSub x ↔ ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * CliffordAlgebra.ι Q v =
      CliffordAlgebra.ι Q v * ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  have hP : v ∈ fixedSub x ↔ specP Q x v = v := by simp [fixedSub, sub_eq_zero]
  rw [hP]
  constructor
  · intro h
    have h' := congrArg (CliffordAlgebra.ι Q) h
    rw [ι_specP] at h'
    conv_rhs => rw [← h']
    simp [mul_assoc]
  · intro h
    apply CliffordAlgebra.ι_injective Q
    rw [ι_specP, h, mul_assoc, Units.mul_inv, mul_one]

/-- The space `{Z ∈ gspin(W) : [Z, ι(U)] = 0}`; for `U = W'_x`, the moved part of `𝔤_x` is the
kernel of `ad x` on it. -/
def movedLieSub (U : Submodule F (Fin d.m → F)) : Submodule F (CliffordAlgebra d.QW) :=
  (gspin d.QW).toSubmodule ⊓ ⨅ u : U, LinearMap.ker
    (LinearMap.mulLeft F (CliffordAlgebra.ι d.QW (u : Fin d.m → F)) -
      LinearMap.mulRight F (CliffordAlgebra.ι d.QW (u : Fin d.m → F)))

theorem mem_movedLieSub {U : Submodule F (Fin d.m → F)} {Z : CliffordAlgebra d.QW} :
    Z ∈ movedLieSub d U ↔ Z ∈ gspin d.QW ∧ ∀ u ∈ U,
      CliffordAlgebra.ι d.QW u * Z = Z * CliffordAlgebra.ι d.QW u := by
  simp [movedLieSub, Submodule.mem_iInf, sub_eq_zero]

/-- **Elements of the moved part of `𝔤_x` commute with `T_x(F)`**: if `T_x(F)` is commutative,
`Z ∈ gspin(W)` commutes with `x` and with `ι(W'_x)`, and `t ∈ T_x`, then `Z` commutes with `t`.
`Z` has the commutant of some `g ∈ GSpin(W)(F)` (`exists_gspin_commute_iff`), which lies in
`T_x(F)` (`mem_torusOf_of_commute`) and so commutes with `t`. -/
theorem commute_of_mem_torusOf_of_movedPart {x t : ↥(GSpin d.QW)}
    (hcomm : ∀ a ∈ d.torusOf x, ∀ b ∈ d.torusOf x, Commute a b) (ht : t ∈ d.torusOf x)
    {Z : CliffordAlgebra d.QW} (hZ : Z ∈ gspin d.QW)
    (hZx : ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * Z =
      Z * ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
    (hZf : ∀ v ∈ fixedSub x, CliffordAlgebra.ι d.QW v * Z = Z * CliffordAlgebra.ι d.QW v) :
    ((t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * Z =
      Z * ((t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) := by
  obtain ⟨g, hg⟩ := exists_gspin_commute_iff d.QW hZ
  have hgT : g ∈ d.torusOf x :=
    mem_torusOf_of_commute d ((hg _).mpr hZx) fun w hw => (hg _).mpr (hZf w hw)
  exact (hg _).mp (congrArg (fun k : ↥(GSpin d.QW) =>
    ((k : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) (hcomm t ht g hgT).eq)

/-- **Elements of `T_x` are semisimple** for `x ∈ Γ(G,H)` (Thesis §6.5: `T_x` is a torus).
Over `F̄`, `X = P(x)` is semisimple and the moved part of its Lie centralizer is abelian
(`lieAbelian_specP_baseChange`); `P(t)` is an isometry commuting with `X` and fixing
`ker (X − 1) = W'_x ⊗ F̄`, hence semisimple (`IsomCent.isSemisimple_of_commute_of_lieAbelian`:
`P(t)` is scalar on the eigenlines of `X` and an isometry of the nondegenerate plane `E₋₁`).
Then `t` is semisimple by `isSS_of_isSemisimple_specP_baseChange`. -/
theorem isSS_of_mem_torusOf {x t : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) (ht : t ∈ d.torusOf x) :
    IsSS F (((t : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW) := by
  refine isSS_of_isSemisimple_specP_baseChange d.nondeg t ?_
  have hQ := isNondeg_baseChange _ d.nondeg
  have hB : (bform (d.QW.baseChange (AlgebraicClosure F))).IsSymm := ⟨fun u v => bform_comm _ u v⟩
  rw [← specP_bcGSpin]
  have hxss : Module.End.IsSemisimple (specP _ (bcGSpin d.QW x) :
      AlgebraicClosure F ⊗[F] (Fin d.m → F) →ₗ[AlgebraicClosure F] _) := by
    rw [specP_bcGSpin]
    exact isSemisimple_baseChange (isSemisimple_specP_of_isSS d.QW x hx.1)
  have hL : IsomCent.LieAbelian (bform (d.QW.baseChange (AlgebraicClosure F)))
      (specP _ (bcGSpin d.QW x) :
        AlgebraicClosure F ⊗[F] (Fin d.m → F) →ₗ[AlgebraicClosure F] _) := by
    rw [specP_bcGSpin]
    exact lieAbelian_specP_baseChange x hx
  have htx : Commute t x := Subgroup.mem_centralizer_singleton_iff.mp ht.1
  have hc : Commute (specP _ (bcGSpin d.QW x)) (specP _ (bcGSpin d.QW t)) :=
    ((htx.symm.map (bcGSpin d.QW)).map (specP _))
  refine IsomCent.isSemisimple_of_commute_of_lieAbelian hB hQ (Steinberg.isIsom_specP _) hxss hL
    (Steinberg.isIsom_specP _) (Steinberg.commute_toLinearMap hc.symm) fun z hz => ?_
  have hle : fixedSub x ≤ fixedSub t := fun v hv => by
    have := ht.2 v hv
    simpa [fixedSub, sub_eq_zero] using this
  rw [GGPData.eigenspace_bc_one] at hz
  have hz' := Submodule.baseChange_mono (AlgebraicClosure F) hle hz
  rw [← GGPData.eigenspace_bc_one, Module.End.mem_eigenspace_iff, one_smul] at hz'
  exact hz'

/-- **`T_♮` is open in `T(F)`** (Thesis §6.5: `T_♮` is Zariski open in `T`).  For `x = t₀ ∈ T_♮`
(so `T = T_x`) and `t ∈ T` near `x`:
* `W'_x ⊆ W'_t` (`t ∈ T_x`), and `dim W'_t ≤ dim W'_x` by upper semicontinuity of kernel dimension
  (`W'_t = ker(v ↦ t ι(v) − ι(v) t)`), so `W'_t = W'_x`;
* likewise the moved part `𝔩_t` of `𝔤_t` contains `𝔩_x` (`commute_of_mem_torusOf_of_movedPart`)
  and has dimension `≤ dim 𝔩_x`, so `𝔩_t = 𝔩_x` is abelian; hence so is the Lie algebra of `S_t`
  over `F̄` (`lieAbelian_specP_baseChange_of_movedPartAbelian`);
* `t` is semisimple (`isSS_of_mem_torusOf`), so by Steinberg's description of centralizers
  (`Steinberg.commute_of_commute_of_lieAbelian`) everything commuting with `t` and fixing
  `W'_t = W'_x` commutes with `x`: `T_t ⊆ T_x`; and `T_x ⊆ T_t` as `T_x` is commutative.
So `T_t = T`, and the commutativity and compactness clauses of `t ∈ Γ(G,H)` are those of `x`. -/
theorem isOpen_torusNat (T : Subgroup ↥(GSpin d.QW)) :
    IsOpen {t : ↥T | d.IsGammaElt (t : ↥(GSpin d.QW)) ∧ d.torusOf (t : ↥(GSpin d.QW)) = T} := by
  rw [isOpen_iff_mem_nhds]
  rintro t₀ ⟨hx, hT⟩
  set x : ↥(GSpin d.QW) := (t₀ : ↥(GSpin d.QW)) with hxdef
  set val : ↥T → CliffordAlgebra d.QW :=
    fun t => (((t : ↥(GSpin d.QW)) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) with hvaldef
  have hval : Continuous val :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_subtype_val
  have hmemT : ∀ t : ↥T, (t : ↥(GSpin d.QW)) ∈ d.torusOf x := fun t => hT.symm ▸ t.2
  -- `W'_t = W'_x` near `x`
  let f : ↥T → (Fin d.m → F) →ₗ[F] CliffordAlgebra d.QW := fun t =>
    (LinearMap.mulLeft F (val t) - LinearMap.mulRight F (val t)) ∘ₗ CliffordAlgebra.ι d.QW
  have hfker : ∀ t : ↥T, LinearMap.ker (f t) = fixedSub (t : ↥(GSpin d.QW)) := fun t => by
    ext v
    simp [f, val, mem_fixedSub_iff_commute_ι, sub_eq_zero]
  have hfc : ∀ v, Continuous fun t => f t v := fun v =>
    (hval.mul continuous_const).sub (continuous_const.mul hval)
  have hE1 := eventually_ker_eq_of_le f hfc t₀ (Eventually.of_forall fun t => by
    rw [hfker, hfker]
    intro v hv
    have := (hmemT t).2 v hv
    simpa [fixedSub, sub_eq_zero] using this)
  -- `𝔩_t = 𝔩_x` near `x`
  let M := movedLieSub d (fixedSub x)
  let g : ↥T → ↥M →ₗ[F] CliffordAlgebra d.QW := fun t =>
    (LinearMap.mulLeft F (val t) - LinearMap.mulRight F (val t)) ∘ₗ M.subtype
  have hgker : ∀ t : ↥T, ∀ Z : ↥M, Z ∈ LinearMap.ker (g t) ↔
      val t * (Z : CliffordAlgebra d.QW) = Z * val t := fun t Z => by
    simp [g, sub_eq_zero]
  have hgc : ∀ Z, Continuous fun t => g t Z := fun Z =>
    (hval.mul continuous_const).sub (continuous_const.mul hval)
  have hE2 := eventually_ker_eq_of_le g hgc t₀ (Eventually.of_forall fun t Z hZ => by
    rw [hgker] at hZ ⊢
    obtain ⟨hZg, hZf⟩ := mem_movedLieSub d |>.mp Z.2
    exact commute_of_mem_torusOf_of_movedPart d hx.2.1 (hmemT t) hZg hZ hZf)
  filter_upwards [hE1, hE2] with t h1 h2
  rw [hfker, hfker] at h1
  set tt : ↥(GSpin d.QW) := (t : ↥(GSpin d.QW)) with httdef
  have htT : tt ∈ d.torusOf x := hmemT t
  -- the moved part of `𝔤_t` is abelian
  have hMPA : MovedPartAbelian d.QW tt := by
    have hin : ∀ X ∈ lieCentralizer (gspin d.QW) ((tt : (CliffordAlgebra d.QW)ˣ) :
        CliffordAlgebra d.QW), (∀ v ∈ fixedSub tt, ⁅X, CliffordAlgebra.ι d.QW v⁆ = 0) →
        X ∈ lieCentralizer (gspin d.QW) ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) := by
      intro X hX hXf
      rw [mem_lieCentralizer] at hX ⊢
      have hXM : X ∈ M := (mem_movedLieSub d).mpr ⟨hX.1, fun u hu => by
        have := hXf u (h1 ▸ hu)
        rw [Ring.lie_def, sub_eq_zero] at this
        exact this.symm⟩
      have hk : (⟨X, hXM⟩ : ↥M) ∈ LinearMap.ker (g t) := (hgker t _).mpr hX.2
      rw [h2] at hk
      exact ⟨hX.1, (hgker t₀ _).mp hk⟩
    intro X hX Y hY hXf hYf
    exact movedPartAbelian_of_isGammaElt d x hx X (hin X hX hXf) Y (hin Y hY hYf)
      (fun v hv => hXf v (h1 ▸ hv)) (fun v hv => hYf v (h1 ▸ hv))
  have hss := isSS_of_mem_torusOf d hx htT
  have hxt : Commute x tt := (Subgroup.mem_centralizer_singleton_iff.mp htT.1).symm
  -- `T_t = T_x`
  have hTT : d.torusOf tt = d.torusOf x := by
    apply le_antisymm
    · intro z hz
      have hQ := isNondeg_baseChange _ d.nondeg
      have hxss : Module.End.IsSemisimple (specP _ (bcGSpin d.QW x) :
          AlgebraicClosure F ⊗[F] (Fin d.m → F) →ₗ[AlgebraicClosure F] _) := by
        rw [specP_bcGSpin]
        exact isSemisimple_baseChange (isSemisimple_specP_of_isSS d.QW x hx.1)
      have htss : Module.End.IsSemisimple (specP _ (bcGSpin d.QW tt) :
          AlgebraicClosure F ⊗[F] (Fin d.m → F) →ₗ[AlgebraicClosure F] _) := by
        rw [specP_bcGSpin]
        exact isSemisimple_baseChange (isSemisimple_specP_of_isSS d.QW tt hss)
      have hL : IsomCent.LieAbelian (bform (d.QW.baseChange (AlgebraicClosure F)))
          (specP _ (bcGSpin d.QW tt) :
            AlgebraicClosure F ⊗[F] (Fin d.m → F) →ₗ[AlgebraicClosure F] _) := by
        rw [specP_bcGSpin]
        exact lieAbelian_specP_baseChange_of_movedPartAbelian tt hMPA
      have hE : Module.End.eigenspace (specP _ (bcGSpin d.QW x) :
            AlgebraicClosure F ⊗[F] (Fin d.m → F) →ₗ[AlgebraicClosure F] _) 1 =
          Module.End.eigenspace (specP _ (bcGSpin d.QW tt) :
            AlgebraicClosure F ⊗[F] (Fin d.m → F) →ₗ[AlgebraicClosure F] _) 1 := by
        rw [GGPData.eigenspace_bc_one, GGPData.eigenspace_bc_one, h1]
      have hzt : Commute z tt := Subgroup.mem_centralizer_singleton_iff.mp hz.1
      have key := Steinberg.commute_of_commute_of_lieAbelian hQ hxss htss hL (hxt.map _) hE
        (hzt.map (bcGSpin d.QW))
      have hzx : Commute z x := by
        refine bcGSpin_injective d.QW ?_
        rw [map_mul, map_mul]
        exact key.eq
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr hzx.eq, fun v hv => hz.2 v ?_⟩
      rw [h1]
      exact hv
    · intro a ha
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hx.2.1 a ha tt htT).eq,
        fun v hv => ha.2 v ?_⟩
      rw [← h1]
      exact hv
  refine ⟨⟨hss, ?_, ?_⟩, hTT.trans hT⟩
  · rw [hTT]; exact hx.2.1
  · rw [hTT]; exact hx.2.2

/-! ### Continuity of the integrand on `T_♮` -/

/-- **`Δ(t)^{s−1/2}` is continuous on `T_♮`** (used in the proof of Thesis Prop 12.1.1(i)).
For `x ∈ T_♮`
(so `T = T_x`) and `t ∈ T_♮`: `W'_t = W'_x`, and `W''_t ⊆ W''_x` (`P(t)` is `1` on `W'_x` and
preserves `W''_x`; `W = W'_x ⊕ W''_x` as `P(x)` is semisimple), so `W''_t = W''_x` by
dimension.  Hence `Δ(t) = |det (P(t) − 1)|_{W''_x}|_F`, a continuous function of `t`, nonzero at
`x` (`W'_x ∩ W''_x = 0`), and `|·|_F` is locally constant on `F^×`. -/
theorem continuousOn_deltaGGP_rpow (T : Subgroup ↥(GSpin d.QW)) (s : ℝ) :
    ContinuousOn (fun t : ↥T => ((deltaGGP d (t : ↥(GSpin d.QW)) ^ (s - 1 / 2) : ℝ) : ℂ))
      {t : ↥T | d.IsGammaElt (t : ↥(GSpin d.QW)) ∧ d.torusOf (t : ↥(GSpin d.QW)) = T} := by
  rw [(isOpen_torusNat d T).continuousOn_iff]
  rintro t₀ ⟨hx, hT⟩
  set x : ↥(GSpin d.QW) := (t₀ : ↥(GSpin d.QW)) with hxdef
  have hmemT : ∀ t : ↥T, (t : ↥(GSpin d.QW)) ∈ d.torusOf x := fun t => hT.symm ▸ t.2
  set U := movedSub x with hUdef
  set P : ↥T → Module.End F (Fin d.m → F) :=
    fun t => (specP d.QW (t : ↥(GSpin d.QW)) : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) with hPdef
  have hPx : P t₀ = (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) := rfl
  -- `P(t)` commutes with `P(x)`, so preserves `U = W''_x`
  have hcomm : ∀ t : ↥T, Commute (P t₀ - 1) (P t - 1) := fun t => by
    have hc : Commute x (t : ↥(GSpin d.QW)) :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hmemT t).1).symm
    have hc' : Commute (P t₀) (P t) :=
      Steinberg.commute_toLinearMap ((hc.map (specP d.QW)).symm)
    exact (hc'.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)
  have hmaps : ∀ t : ↥T, ∀ u ∈ U, (P t - 1) u ∈ U := by
    rintro t _ ⟨w, rfl⟩
    exact ⟨(P t - 1) w, LinearMap.congr_fun (hcomm t).eq w⟩
  set g : ↥T → U →ₗ[F] U := fun t => (P t - 1).restrict (hmaps t) with hgdef
  -- `W = W'_x ⊕ W''_x`
  have hss : Module.End.IsSemisimple (P t₀ - 1) :=
    Module.End.IsSemisimple.sub_of_commute (Commute.one_right _)
      (isSemisimple_specP_of_isSS d.QW x hx.1) Module.End.isSemisimple_id
  have hdisj : Disjoint (fixedSub x) U := disjoint_ker_range_of_isSemisimple hss
  have hrn := LinearMap.finrank_range_add_finrank_ker (P t₀ - 1)
  have hcompl : IsCompl (fixedSub x) U := by
    refine (Submodule.isCompl_iff_disjoint _ _ ?_).2 hdisj
    have e1 : Module.finrank F (fixedSub x) = Module.finrank F (LinearMap.ker (P t₀ - 1)) := rfl
    have e2 : Module.finrank F U = Module.finrank F (LinearMap.range (P t₀ - 1)) := rfl
    omega
  -- on `T_♮`, `W''_t = W''_x` and `Δ(t) = |det g(t)|`
  have hΔ : ∀ t : ↥T, d.IsGammaElt (t : ↥(GSpin d.QW)) ∧ d.torusOf (t : ↥(GSpin d.QW)) = T →
      deltaGGP d (t : ↥(GSpin d.QW)) = absF (LinearMap.det (g t)) := by
    rintro t ⟨-, hTt⟩
    have hfix : fixedSub (t : ↥(GSpin d.QW)) = fixedSub x := by
      apply le_antisymm
      · intro v hv
        have hxt : x ∈ d.torusOf (t : ↥(GSpin d.QW)) := hTt.symm ▸ t₀.2
        have := hxt.2 v hv
        simpa [fixedSub, sub_eq_zero] using this
      · intro v hv
        have := (hmemT t).2 v hv
        simpa [fixedSub, sub_eq_zero] using this
    have hle : movedSub (t : ↥(GSpin d.QW)) ≤ U := by
      rintro _ ⟨v, rfl⟩
      have hv : v ∈ fixedSub x ⊔ U := hcompl.sup_eq_top ▸ Submodule.mem_top
      obtain ⟨a, ha, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
      have ha' : (P t - 1) a = 0 := by
        have := (hmemT t).2 a ha
        simp only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
        exact this
      show (P t - 1) (a + u) ∈ U
      rw [map_add, ha', zero_add]
      exact hmaps t u hu
    have hrnt := LinearMap.finrank_range_add_finrank_ker (P t - 1)
    have heq : movedSub (t : ↥(GSpin d.QW)) = U := by
      refine Submodule.eq_of_le_of_finrank_eq hle ?_
      change Module.finrank F (LinearMap.range (P t - 1)) = Module.finrank F (LinearMap.range (P t₀ - 1))
      have h1 : Module.finrank F (LinearMap.ker (P t - 1)) =
          Module.finrank F (LinearMap.ker (P t₀ - 1)) := by
        change Module.finrank F (fixedSub (t : ↥(GSpin d.QW))) = Module.finrank F (fixedSub x)
        rw [hfix]
      have := hrnt.trans hrn.symm
      rw [h1] at this
      exact Nat.add_right_cancel this
    unfold deltaGGP
    congr 1
    exact Steinberg.det_restrict_eq rfl heq _ _
  -- continuity of `t ↦ det g(t)`
  have hPc : ∀ v, Continuous fun t : ↥T => P t v := fun v => by
    have hn : Continuous fun t : ↥T => ((t : ↥(GSpin d.QW)) : (CliffordAlgebra d.QW)ˣ) :=
      continuous_subtype_val.comp continuous_subtype_val
    show Continuous fun t : ↥T => specP d.QW (t : ↥(GSpin d.QW)) v
    simp only [specP_apply_eq]
    exact (IsModuleTopology.continuous_of_linearMap (CliffordAlgebra.ιInv d.QW)).comp
      ((Units.continuous_val.comp hn).mul (continuous_const.mul (Units.continuous_coe_inv.comp hn)))
  have hdet : Continuous fun t => LinearMap.det (g t) := by
    refine ContinuousLinearMap.continuous_det.comp
      (f := fun t => LinearMap.toContinuousLinearMap (g t)) (continuous_clm_apply.2 fun u => ?_)
    show Continuous fun t => g t u
    refine Continuous.subtype_mk ?_ _
    show Continuous fun t => (P t - 1) (u : Fin d.m → F)
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    exact (hPc u).sub continuous_const
  -- `det g(x) ≠ 0`
  have hdet0 : LinearMap.det (g t₀) ≠ 0 := by
    rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    have hu' : (P t₀ - 1) (u : Fin d.m → F) = 0 := congrArg Subtype.val hu
    have : (u : Fin d.m → F) ∈ fixedSub x ⊓ U := ⟨LinearMap.mem_ker.mpr hu', u.2⟩
    rw [hdisj.eq_bot, Submodule.mem_bot] at this
    exact (Submodule.mem_bot F).mpr (Subtype.ext this)
  -- conclude
  have hpos : 0 < absF (LinearMap.det (g t₀)) := absF_pos hdet0
  have hcont : ContinuousAt (fun a : F => ((absF a ^ (s - 1 / 2) : ℝ) : ℂ))
      (LinearMap.det (g t₀)) :=
    Complex.continuous_ofReal.continuousAt.comp
      ((Real.continuousAt_rpow_const _ _ (Or.inl hpos.ne')).comp (continuousAt_absF hdet0))
  refine (ContinuousAt.comp (f := fun t => LinearMap.det (g t)) hcont hdet.continuousAt).congr ?_
  filter_upwards [(isOpen_torusNat d T).mem_nhds ⟨hx, hT⟩] with t ht
  simp only [Function.comp_apply, hΔ t ht]

/-- `𝔤 = gspin(W) × gspin(V)` is `Ad(G)`-stable. -/
theorem lie_conj_stable (d : GGPData F) (t : ↥d.G) :
    ∀ X ∈ d.lie.toSubmodule, conjAd F (t : d.ambientˣ) X ∈ d.lie.toSubmodule := fun _ hX =>
  ⟨conj_mem_gspin d.QW (d.fst t) hX.1, conj_mem_gspin d.QV (d.snd t) hX.2⟩

/-- `1 − Ad(t)` on `𝔤`. -/
abbrev oneSubAd (d : GGPData F) (t : ↥d.G) : d.lie.toSubmodule →ₗ[F] d.lie.toSubmodule :=
  1 - (conjAd F (t : d.ambientˣ)).toLinearEquiv.toLinearMap.restrict (lie_conj_stable d t)

theorem weylDisc_eq_oneSubAd (d : GGPData F) (t : ↥d.G) :
    weylDisc d.lie (t : d.ambientˣ) = absF (LinearMap.charpoly (oneSubAd d t)).trailingCoeff := by
  rw [weylDisc, dite_eq_left (lie_conj_stable d t)]

/-- `1 − Ad g` is semisimple on `𝔤` for semisimple `g ∈ G(F)`. -/
theorem isSemisimple_oneSubAd (g : ↥d.G) (hg : IsSS F ((g : d.ambientˣ) : d.ambient)) :
    Module.End.IsSemisimple (oneSubAd d g) := by
  set a : d.ambient := ((g : d.ambientˣ) : d.ambient)
  set ai : d.ambient := (((g : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient)
  have hinv : Module.End.IsSemisimple (LinearMap.mulLeft F ai) := isSS_coe_inv hg
  have hAd : Module.End.IsSemisimple (LinearMap.mulLeft F a * LinearMap.mulRight F ai) :=
    Module.End.IsSemisimple.mul_of_commute (LinearMap.commute_mulLeft_right _ _) hg
      (isSemisimple_mulRight_of_mulLeft hinv)
  have hp' : ∀ X ∈ d.lie.toSubmodule,
      (LinearMap.mulLeft F a * LinearMap.mulRight F ai) X ∈ d.lie.toSubmodule := fun X hX => by
    have := lie_conj_stable d g X hX
    simpa [mul_assoc] using this
  have hp : d.lie.toSubmodule ∈ Module.End.invtSubmodule
      (LinearMap.mulLeft F a * LinearMap.mulRight F ai) :=
    (Module.End.mem_invtSubmodule _).mpr hp'
  have hres := hAd.restrict hp
  have heq : (conjAd F (g : d.ambientˣ)).toLinearEquiv.toLinearMap.restrict (lie_conj_stable d g) =
      (LinearMap.mulLeft F a * LinearMap.mulRight F ai).restrict hp' :=
    LinearMap.ext fun X => Subtype.ext (mul_assoc _ _ _)
  rw [oneSubAd, heq]
  exact Module.End.IsSemisimple.sub_of_commute (Commute.one_left _) Module.End.isSemisimple_id hres


omit [PAdicField F] in
/-- **Equal centralizers in `GSpin` give equal centralizers in `gspin`**: if `a, b ∈ GSpin(V)` have
the same centralizer in `GSpin(V)(F)`, then `X ∈ gspin(V)` commutes with `a` iff with `b`
(`X` has the commutant of some `g ∈ GSpin(V)(F)`, `exists_gspin_commute_iff`). -/
theorem commute_gspin_of_commute_iff [PAdicField F] {V : Type*} [AddCommGroup V] [Module F V]
    [Module.Finite F V] {Q : QuadraticForm F V} {a b : GSpin Q}
    (h : ∀ g : GSpin Q, Commute g a → Commute g b) {X : CliffordAlgebra Q} (hX : X ∈ gspin Q)
    (hXa : ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * X =
      X * ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) :
    ((b : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * X =
      X * ((b : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  obtain ⟨g, hg⟩ := exists_gspin_commute_iff Q hX
  have hgb := h g (Subtype.ext (Units.ext ((hg _).mpr hXa).eq.symm))
  exact (hg _).mp (congrArg (fun k : GSpin Q => ((k : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
    hgb.eq).symm

/-- Commutation in `GSpin(V)(F)` can be tested over `F̄`. -/
theorem commute_iff_commute_bcGSpin {V : Type*} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (g a : GSpin Q) :
    Commute g a ↔ Commute (bcGSpin Q g) (bcGSpin Q a) :=
  ⟨fun h => h.map _, fun h => bcGSpin_injective Q (by rw [map_mul, map_mul]; exact h.eq)⟩

/-- On `T_♮`, an element of `GSpin(W)(F)` (resp. `GSpin(V)(F)`) commutes with `t` iff with `x`
(`GGPData.commute_bc_iff_of_torusOf_eq` over `F̄`, and injectivity of `GSpin(F) → GSpin(F̄)`). -/
theorem commute_iff_of_torusOf_eq {x t : GSpin d.QW} (hx : d.IsGammaElt x) (ht : d.IsGammaElt t)
    (htx : t ∈ d.torusOf x) (hT : d.torusOf t = d.torusOf x) :
    (∀ g : GSpin d.QW, Commute g t ↔ Commute g x) ∧
      ∀ g : GSpin d.QV, Commute g (d.incl t) ↔ Commute g (d.incl x) := by
  refine ⟨fun g => ?_, fun g => ?_⟩
  · rw [commute_iff_commute_bcGSpin, commute_iff_commute_bcGSpin]
    exact d.commute_bc_iff_of_torusOf_eq hx ht htx hT _
  · rw [commute_iff_commute_bcGSpin, commute_iff_commute_bcGSpin]
    exact d.commute_bc_incl_iff_of_torusOf_eq hx ht htx hT _

/-- `diag(t)` as an element of `C(W) × C(V)`. -/
theorem coe_diag_eq (t : GSpin d.QW) :
    (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient) =
      (((t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW),
        (((d.incl t : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) := rfl

/-- **On `T_♮` the Lie centralizers agree**: `𝔤_t = 𝔤_x` for `t ∈ T_x` with `t ∈ Γ(G,H)` and
`T_t = T_x`. -/
theorem commute_lie_iff_of_torusOf_eq {x t : GSpin d.QW} (hx : d.IsGammaElt x)
    (ht : d.IsGammaElt t) (htx : t ∈ d.torusOf x) (hT : d.torusOf t = d.torusOf x)
    {X : d.ambient} (hX : X ∈ d.lie) :
    (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient) * X =
        X * (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient) ↔
      (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient) * X =
        X * (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient) := by
  obtain ⟨hW, hV⟩ := commute_iff_of_torusOf_eq d hx ht htx hT
  rw [coe_diag_eq, coe_diag_eq, Prod.ext_iff, Prod.ext_iff]
  simp only [Prod.fst_mul, Prod.snd_mul]
  exact ⟨fun h => ⟨commute_gspin_of_commute_iff (fun g => (hW g).mp) hX.1 h.1,
      commute_gspin_of_commute_iff (fun g => (hV g).mp) hX.2 h.2⟩,
    fun h => ⟨commute_gspin_of_commute_iff (fun g => (hW g).mpr) hX.1 h.1,
      commute_gspin_of_commute_iff (fun g => (hV g).mpr) hX.2 h.2⟩⟩

/-- `t ↦ v − diag(t) v diag(t)⁻¹` is continuous on `GSpin(W)(F)`, in `C(W) × C(V)`. -/
theorem continuous_sub_conj_diag (v : d.ambient) :
    Continuous fun t : ↥(GSpin d.QW) => v - (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient) * v *
      ((((d.diag t : ↥d.G) : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) := by
  have hval : Continuous fun t : ↥(GSpin d.QW) =>
      ((t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) :=
    Units.continuous_val.comp continuous_subtype_val
  have hvali : Continuous fun t : ↥(GSpin d.QW) =>
      (((t : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  have hmap : Continuous (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)) :=
    IsModuleTopology.continuous_of_linearMap
      (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)).toLinearMap
  refine continuous_const.sub (Continuous.mul (Continuous.mul ?_ continuous_const) ?_)
  · exact hval.prodMk (hmap.comp hval)
  · exact hvali.prodMk (hmap.comp hvali)

/-- **`D^G` is continuous on `T_♮`** (used in the proof of Thesis Prop 12.1.1(i)).
Fix `x ∈ T_♮` (so
`T = T_x`), `N_t = 1 − Ad(t)` on `𝔤`, `L = ker N_x = 𝔤_x` and `C = im N_x`.  As `N_x` is
semisimple, `𝔤 = L ⊕ C`, and both are `N_t`-stable for `t ∈ T` (`N_t` commutes with `N_x`).  For
`t ∈ T_♮`, `ker N_t = 𝔤_t = 𝔤_x = L` (`commute_lie_iff_of_torusOf_eq`), so
`charpoly N_t = X^{dim L} · charpoly (N_t|_C)` with `N_t|_C` invertible, and
`D^G(t) = |det (N_t|_C)|_F`: a continuous function of `t`, nonzero at `x`. -/
theorem continuousOn_weylDisc_torusNat (T : Subgroup ↥(GSpin d.QW)) :
    ContinuousOn (fun t : ↥T => weylDisc d.lie (d.diag (t : ↥(GSpin d.QW)) : d.ambientˣ))
      {t : ↥T | d.IsGammaElt (t : ↥(GSpin d.QW)) ∧ d.torusOf (t : ↥(GSpin d.QW)) = T} := by
  rw [(isOpen_torusNat d T).continuousOn_iff]
  rintro t₀ ⟨hx, hT⟩
  set x : ↥(GSpin d.QW) := (t₀ : ↥(GSpin d.QW)) with hxdef
  have hmemT : ∀ t : ↥T, (t : ↥(GSpin d.QW)) ∈ d.torusOf x := fun t => hT.symm ▸ t.2
  obtain ⟨N, hNdef⟩ : ∃ N : ↥T → Module.End F d.lie.toSubmodule,
      N = fun t : ↥T => oneSubAd d (d.diag (t : ↥(GSpin d.QW))) := ⟨_, rfl⟩
  set u : ↥T → d.ambient := fun t => (((d.diag (t : ↥(GSpin d.QW)) : ↥d.G) : d.ambientˣ) : d.ambient)
  set ui : ↥T → d.ambient := fun t =>
    ((((d.diag (t : ↥(GSpin d.QW)) : ↥d.G) : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient)
  have hN : ∀ t (X : d.lie.toSubmodule), ((N t X : d.lie.toSubmodule) : d.ambient) =
      (X : d.ambient) - u t * X * ui t := by
    subst hNdef
    intro t X
    rfl
  -- `N_t` commutes with `N_x`
  have hcomm : ∀ t : ↥T, Commute (N t) (N t₀) := fun t => by
    have hc : Commute (d.diag (t : ↥(GSpin d.QW))) (d.diag x) :=
      (show Commute (t : ↥(GSpin d.QW)) x from
        Subgroup.mem_centralizer_singleton_iff.mp (hmemT t).1).map d.diag
    have h1 : u t * u t₀ = u t₀ * u t := congrArg (fun k : ↥d.G => ((k : d.ambientˣ) : d.ambient)) hc.eq
    have h2 : ui t₀ * ui t = ui t * ui t₀ := by
      have := congrArg (fun k : ↥d.G => (((k⁻¹ : ↥d.G) : d.ambientˣ) : d.ambient)) hc.eq
      simpa [mul_inv_rev] using this
    refine LinearMap.ext fun X => Subtype.ext ?_
    simp only [Module.End.mul_apply, hN]
    have e1 : u t * (u t₀ * X * ui t₀) * ui t = u t₀ * (u t * X * ui t) * ui t₀ := by
      simp only [← mul_assoc]
      rw [h1, mul_assoc _ (ui t₀), h2, ← mul_assoc]
    rw [mul_sub, sub_mul, mul_sub, sub_mul, e1]
    abel
  -- `N_x` is semisimple
  have hss : Module.End.IsSemisimple (N t₀) := by
    rw [hNdef]
    exact isSemisimple_oneSubAd d (d.diag x) (isSS_diag_of_isSS d hx.1)
  -- `𝔤 = L ⊕ C`, both `N_t`-stable
  obtain ⟨L, hLdef⟩ : ∃ L, L = LinearMap.ker (N t₀) := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C, C = LinearMap.range (N t₀) := ⟨_, rfl⟩
  have hdisj : Disjoint L C := by
    rw [hLdef, hCdef]; exact disjoint_ker_range_of_isSemisimple hss
  have hcompl : IsCompl L C := by
    refine (Submodule.isCompl_iff_disjoint _ _ ?_).2 hdisj
    have := LinearMap.finrank_range_add_finrank_ker (N t₀)
    rw [hLdef, hCdef]
    omega
  have hL : ∀ t, ∀ X ∈ L, N t X ∈ L := fun t X hX => by
    rw [hLdef, LinearMap.mem_ker] at hX ⊢
    rw [← Module.End.mul_apply, ← (hcomm t).eq, Module.End.mul_apply, hX, map_zero]
  have hC : ∀ t, ∀ X ∈ C, N t X ∈ C := by
    rw [hCdef]
    rintro t _ ⟨Y, rfl⟩
    exact ⟨N t Y, (LinearMap.congr_fun (hcomm t).eq Y).symm⟩
  -- on `T_♮`, `ker N_t = L`
  have hzero : ∀ t (X : d.lie.toSubmodule), N t X = 0 ↔ u t * X = X * u t := fun t X => by
    have hiu : ui t * u t = 1 := Units.inv_mul _
    have hui : u t * ui t = 1 := Units.mul_inv _
    rw [← Submodule.coe_eq_zero, hN, sub_eq_zero]
    constructor
    · intro h
      calc u t * X = u t * X * (ui t * u t) := by rw [hiu, mul_one]
        _ = X * u t := by rw [← mul_assoc, ← h]
    · intro h
      rw [h, mul_assoc, hui, mul_one]
  have hker : ∀ t : ↥T, d.IsGammaElt (t : ↥(GSpin d.QW)) ∧ d.torusOf (t : ↥(GSpin d.QW)) = T →
      LinearMap.ker (N t) = L := by
    rintro t ⟨ht, hTt⟩
    ext X
    rw [hLdef, LinearMap.mem_ker, LinearMap.mem_ker]
    exact (hzero t X).trans ((commute_lie_iff_of_torusOf_eq d hx ht (hmemT t)
      (hTt.trans hT.symm) X.2).trans (hzero t₀ X).symm)
  -- `D^G(t) = |det (N_t|_C)|` on `T_♮`
  obtain ⟨g, hgdef, hg⟩ : ∃ g : ↥T → C →ₗ[F] C, g = (fun t => (N t).restrict (hC t)) ∧
      ∀ t c, ((g t c : C) : d.lie.toSubmodule) = N t c :=
    ⟨_, rfl, fun t c => LinearMap.coe_restrict_apply (hC t) c⟩
  have hkey : ∀ t : ↥T, d.IsGammaElt (t : ↥(GSpin d.QW)) ∧ d.torusOf (t : ↥(GSpin d.QW)) = T →
      LinearMap.det (g t) ≠ 0 ∧ (LinearMap.charpoly (N t)).trailingCoeff =
        (-1) ^ Module.finrank F C * LinearMap.det (g t) := fun t htS => by
    rw [hgdef]
    exact trailingCoeff_charpoly_of_isCompl hcompl (hker t htS) (hC t)
  have hdet0 := fun t htS => (hkey t htS).1
  have hW : ∀ t : ↥T, d.IsGammaElt (t : ↥(GSpin d.QW)) ∧ d.torusOf (t : ↥(GSpin d.QW)) = T →
      weylDisc d.lie (d.diag (t : ↥(GSpin d.QW)) : d.ambientˣ) = absF (LinearMap.det (g t)) := by
    intro t htS
    have h1 : weylDisc d.lie (d.diag (t : ↥(GSpin d.QW)) : d.ambientˣ) =
        absF (LinearMap.charpoly (N t)).trailingCoeff := by
      rw [hNdef]
      beta_reduce
      exact weylDisc_eq_oneSubAd d (d.diag (t : ↥(GSpin d.QW)))
    refine h1.trans ((congrArg absF (hkey t htS).2).trans ?_)
    exact absF_eq_of_norm_eq (hdet0 t htS) (by simp [norm_mul, norm_pow])
  -- continuity of `t ↦ det (N_t|_C)`
  have hdet : Continuous fun t => LinearMap.det (g t) := by
    rw [hgdef]
    refine continuous_det_restrict_of_continuous d.lie.toSubmodule.subtype
      d.lie.toSubmodule.injective_subtype N (fun v => ?_) C hC
    simp only [Submodule.subtype_apply, hN]
    exact (continuous_sub_conj_diag d (v : d.ambient)).comp continuous_subtype_val
  -- conclude
  refine continuousAt_of_eventually_eq_absF hdet.continuousAt (hkey t₀ ⟨hx, hT⟩).1 ?_
  filter_upwards [(isOpen_torusNat d T).mem_nhds ⟨hx, hT⟩] with t ht
  exact (hW t ht).symm

/-- `G_{diag t} = G_{diag x}` for `t ∈ T_{x,♮}` (`commute_iff_of_torusOf_eq`, componentwise). -/
theorem grpCentralizer_diag_eq_of_torusOf_eq {x t : GSpin d.QW} (hx : d.IsGammaElt x)
    (ht : d.IsGammaElt t) (htx : t ∈ d.torusOf x) (hT : d.torusOf t = d.torusOf x) :
    grpCentralizer d.G (d.diag t : d.ambientˣ) = grpCentralizer d.G (d.diag x : d.ambientˣ) := by
  obtain ⟨hW, hV⟩ := commute_iff_of_torusOf_eq d hx ht htx hT
  have key : ∀ (g : ↥d.G) (a : GSpin d.QW), Commute (g : d.ambientˣ) (d.diag a : d.ambientˣ) ↔
      Commute (d.fst g) a ∧ Commute (d.snd g) (d.incl a) := by
    intro g a
    have e1 : ∀ (u v : GSpin d.QW), Commute u v ↔
        Commute ((u : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) (v : (CliffordAlgebra d.QW)ˣ) :=
      fun u v => ⟨fun h => congrArg (fun k : GSpin d.QW => ((k : (CliffordAlgebra d.QW)ˣ) :
        CliffordAlgebra d.QW)) h.eq, fun h => Subtype.ext (Units.ext h.eq)⟩
    have e2 : ∀ (u v : GSpin d.QV), Commute u v ↔
        Commute ((u : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) (v : (CliffordAlgebra d.QV)ˣ) :=
      fun u v => ⟨fun h => congrArg (fun k : GSpin d.QV => ((k : (CliffordAlgebra d.QV)ˣ) :
        CliffordAlgebra d.QV)) h.eq, fun h => Subtype.ext (Units.ext h.eq)⟩
    rw [e1, e2]
    have hg : (((g : d.ambientˣ)) : d.ambient) =
        ((((d.fst g : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW),
          (((d.snd g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) := rfl
    constructor
    · intro h
      have h' := congrArg (fun k : d.ambientˣ => (k : d.ambient)) h.eq
      simp only [Units.val_mul, hg, coe_diag_eq, Prod.mk_mul_mk, Prod.mk.injEq] at h'
      exact ⟨h'.1, h'.2⟩
    · rintro ⟨h1, h2⟩
      refine Units.ext ?_
      simp only [Units.val_mul, hg, coe_diag_eq, Prod.mk_mul_mk, h1.eq, h2.eq]
  ext g
  simp only [grpCentralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq]
  refine ⟨fun ⟨hg, h⟩ => ⟨hg, ?_⟩, fun ⟨hg, h⟩ => ⟨hg, ?_⟩⟩
  · have := (key ⟨g, hg⟩ t).mp h.symm
    exact ((key ⟨g, hg⟩ x).mpr ⟨(hW _).mp this.1, (hV _).mp this.2⟩).symm
  · have := (key ⟨g, hg⟩ x).mp h.symm
    exact ((key ⟨g, hg⟩ t).mpr ⟨(hW _).mpr this.1, (hV _).mpr this.2⟩).symm

/-- `𝔤_{diag t} = 𝔤_{diag x}` for `t ∈ T_{x,♮}`. -/
theorem lieCentralizer_diag_eq_of_torusOf_eq {x t : GSpin d.QW} (hx : d.IsGammaElt x)
    (ht : d.IsGammaElt t) (htx : t ∈ d.torusOf x) (hT : d.torusOf t = d.torusOf x) :
    lieCentralizer d.lie ((d.diag t : d.ambientˣ) : d.ambient) =
      lieCentralizer d.lie ((d.diag x : d.ambientˣ) : d.ambient) := by
  refine LieSubalgebra.ext _ _ fun X => ?_
  rw [mem_lieCentralizer, mem_lieCentralizer]
  exact ⟨fun h => ⟨h.1, (commute_lie_iff_of_torusOf_eq d hx ht htx hT h.1).mp h.2⟩,
    fun h => ⟨h.1, (commute_lie_iff_of_torusOf_eq d hx ht htx hT h.1).mpr h.2⟩⟩

/-- **The chosen orbits agree on `T_♮`**: `O_t` and `O_x` correspond for `t ∈ T_{x,♮}` (equal
centralizers, and `OrbitSpec` only depends on `W'_t = W'_x`). -/
theorem orbitChoice_heq_of_torusOf_eq {x t : GSpin d.QW} (hx : d.IsGammaElt x)
    (ht : d.IsGammaElt t) (htx : t ∈ d.torusOf x) (hT : d.torusOf t = d.torusOf x) :
    HEq (orbitChoice d t) (orbitChoice d x) := by
  refine orbitChoice_heq_of_eq d (grpCentralizer_diag_eq_of_torusOf_eq d hx ht htx hT)
    (lieCentralizer_diag_eq_of_torusOf_eq d hx ht htx hT) ?_
  funext X
  unfold OrbitSpec
  rw [d.fixedSub_eq_of_torusOf_eq htx hT]

/-- **`b(Y, N) = 0`** for the trace form `b` of `C(W) × C(V)`, `N` nilpotent commuting with `Y`
(`YN` is nilpotent, so left multiplication by it has trace `0`). -/
theorem bilin_eq_zero_of_commute_of_isNilpotent {Y N : d.ambient} (hc : Commute Y N)
    (hN : IsNilpotent N) : d.bilin Y N = 0 := by
  rw [GGPData.bilin_apply]
  have hYN : IsNilpotent (Y * N) := hc.isNilpotent_mul_left hN
  exact LinearMap.isNilpotent_trace_of_isNilpotent (hYN.map (Algebra.lmul F d.ambient)) |>.eq_zero

/-! ### The germ term on `T_♮` -/

/-- **`b` is nondegenerate on `𝔤_g`** for semisimple `g ∈ G(F)`: `𝔤 = 𝔤_g ⊕ im(1 − Ad g)`
(`1 − Ad g` is semisimple), and `b(Z, W − g W g⁻¹) = b(Z, W) − b(g Z g⁻¹, g W g⁻¹) = 0` for
`Z ∈ 𝔤_g`, as `b` is `Ad`-invariant; so `b(Z, ·) = 0` on `𝔤_g` forces `b(Z, ·) = 0` on `𝔤`. -/
theorem restrictForm_lieCentralizer_nondegenerate (g : ↥d.G)
    (hg : IsSS F ((g : d.ambientˣ) : d.ambient)) :
    (restrictForm (lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) d.bilin).Nondegenerate := by
  set a : d.ambient := ((g : d.ambientˣ) : d.ambient)
  set ai : d.ambient := (((g : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient)
  have hia : ai * a = 1 := Units.inv_mul _
  have hai : a * ai = 1 := Units.mul_inv _
  set N := oneSubAd d g
  have hss := isSemisimple_oneSubAd d g hg
  have hcompl : IsCompl (LinearMap.ker N) (LinearMap.range N) := by
    refine (Submodule.isCompl_iff_disjoint _ _ ?_).2 (disjoint_ker_range_of_isSemisimple hss)
    have := LinearMap.finrank_range_add_finrank_ker N
    omega
  have hN : ∀ X : d.lie.toSubmodule, ((N X : d.lie.toSubmodule) : d.ambient) =
      (X : d.ambient) - a * X * ai := fun X => rfl
  have hL : ∀ Z : ↥(lieCentralizer d.lie a),
      (∀ W, restrictForm (lieCentralizer d.lie a) d.bilin Z W = 0) → Z = 0 := by
    intro Z hZ
    obtain ⟨hZl, hZc⟩ := mem_lieCentralizer.mp Z.2
    refine Subtype.ext (d.bilin_nondegenerate_lie Z hZl fun Y hY => ?_)
    obtain ⟨l, hl, c, hc, hlc⟩ := Submodule.mem_sup.mp
      (hcompl.sup_eq_top ▸ Submodule.mem_top (x := (⟨Y, hY⟩ : d.lie.toSubmodule)))
    have hYeq : Y = (l : d.ambient) + (c : d.ambient) := by
      have := congrArg Subtype.val hlc
      simpa using this.symm
    rw [hYeq, map_add]
    have h1 : d.bilin Z l = 0 := by
      have hl0 := congrArg Subtype.val (LinearMap.mem_ker.mp hl)
      rw [hN, ZeroMemClass.coe_zero, sub_eq_zero] at hl0
      have hl' : (l : d.ambient) ∈ lieCentralizer d.lie a := by
        rw [mem_lieCentralizer]
        refine ⟨l.2, ?_⟩
        calc a * l = a * l * ai * a := by rw [mul_assoc _ ai, hia, mul_one]
          _ = l * a := by rw [← hl0]
      have := hZ ⟨l, hl'⟩
      simpa [restrictForm] using this
    have h2 : d.bilin Z c = 0 := by
      obtain ⟨w, rfl⟩ := hc
      have hconj : a * (Z : d.ambient) * ai = Z := by
        rw [hZc, mul_assoc, hai, mul_one]
      rw [hN, map_sub, ← d.bilin_conj g (Z : d.ambient) (w : d.ambient)]
      change d.bilin (a * Z * ai) (a * w * ai) - d.bilin (Z : d.ambient) (a * w * ai) = 0
      rw [hconj, sub_self]
    rw [h1, h2, add_zero]
  refine ⟨hL, fun Y hY => hL Y fun X => ?_⟩
  have := hY X
  simp only [restrictForm, LinearMap.compl₁₂_apply] at this ⊢
  rw [GGPData.bilin_apply, LinearMap.mulLeft_mul, ← Module.End.mul_eq_comp,
    LinearMap.trace_mul_comm, Module.End.mul_eq_comp, ← LinearMap.mulLeft_mul, ← GGPData.bilin_apply]
  exact this

/-- **The regular semisimple set of `𝔤_g` is open** for semisimple `g ∈ G(F)`.
Sketch: `𝔤_g` is reductive (centralizer of a semisimple element, characteristic `0`), and in a
reductive Lie algebra of rank `r` the regular semisimple elements are those where the coefficient
of `T^r` in `det(T − ad Z)` does not vanish, a polynomial condition (Harish-Chandra's regular set
`𝔤'`); `IsRegularSS` (semisimple in `C(W) × C(V)` with abelian centralizer in `𝔤_g`) is that
condition, as `𝔤_g = Lie(G_g)` is the Lie algebra of a reductive group acting algebraically on
`C(W) × C(V)`, so its centre acts semisimply and semisimplicity in `𝔤_g` (Jordan decomposition)
agrees with semisimplicity in `C(W) × C(V)`.  This is the Lie algebra
analogue of `hc_regularSet_open_conull`; the identification is not formalized.
Status: SORRY (structure of reductive Lie algebras). -/
theorem isOpen_regularSS_lieCentralizer (g : ↥d.G)
    (hg : IsSS F ((g : d.ambientˣ) : d.ambient)) :
    IsOpen {Z : ↥(lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) |
      IsRegularSS (lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) (Z : d.ambient)} := by
  sorry

/-- `expA` on `C(W) × C(V)` is computed componentwise near `0`. -/
theorem eventually_expA_ambient :
    ∀ᶠ X in 𝓝 (0 : d.ambient), (expA F X).1 = expA F X.1 ∧ (expA F X).2 = expA F X.2 := by
  have h1 := eventually_map_expA (F := F) (A := d.ambient)
    (LinearMap.fst F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) (fun X n => Prod.pow_fst X n)
  have h2 := eventually_map_expA (F := F) (A := d.ambient)
    (LinearMap.snd F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) (fun X n => Prod.pow_snd X n)
  filter_upwards [h1, h2] with X hX1 hX2
  exact ⟨hX1, hX2⟩

/-- **`e^X ∈ G(F)` for `X ∈ 𝔤` near `0`** (componentwise `MovedPart.exists_nhds_expA_mem_GSpin`). -/
theorem eventually_expA_mem_G :
    ∀ᶠ X in 𝓝 (0 : d.ambient), X ∈ d.lie → ∃ g : ↥d.G, ((g : d.ambientˣ) : d.ambient) = expA F X := by
  obtain ⟨U₁, hU₁, h₁⟩ := MovedPart.exists_nhds_expA_mem_GSpin (F := F) d.QW
  obtain ⟨U₂, hU₂, h₂⟩ := MovedPart.exists_nhds_expA_mem_GSpin (F := F) d.QV
  have hf : (fun X : d.ambient => X.1) ⁻¹' U₁ ∈ 𝓝 (0 : d.ambient) :=
    continuous_fst.continuousAt.preimage_mem_nhds hU₁
  have hs : (fun X : d.ambient => X.2) ⁻¹' U₂ ∈ 𝓝 (0 : d.ambient) :=
    continuous_snd.continuousAt.preimage_mem_nhds hU₂
  filter_upwards [hf, hs, eventually_expA_ambient d] with X hX1 hX2 hX hXl
  obtain ⟨g₁, hg₁⟩ := h₁ X.1 hX1 hXl.1
  obtain ⟨g₂, hg₂⟩ := h₂ X.2 hX2 hXl.2
  refine ⟨d.pair (g₁, g₂), Prod.ext ?_ ?_⟩
  · rw [hX.1]; exact hg₁
  · rw [hX.2]; exact hg₂

/-- **The logarithm of `G(F)` near `1` lies in `𝔤`**: for `Y` near `0`, `e^Y ∈ G(F)` implies
`Y ∈ 𝔤 = gspin(W) × gspin(V)` (componentwise `eventually_mem_gspin_of_expA_mem`). -/
theorem eventually_mem_lie_of_expA_mem :
    ∀ᶠ Y in 𝓝 (0 : d.ambient), ∀ g : ↥d.G, ((g : d.ambientˣ) : d.ambient) = expA F Y →
      Y ∈ d.lie := by
  have h₁ := (continuous_fst.tendsto (0 : d.ambient)).eventually
    (eventually_mem_gspin_of_expA_mem (F := F) d.QW)
  have h₂ := (continuous_snd.tendsto (0 : d.ambient)).eventually
    (eventually_mem_gspin_of_expA_mem (F := F) d.QV)
  filter_upwards [h₁, h₂, eventually_expA_ambient d] with Y hY1 hY2 hY g hg
  refine ⟨hY1 (d.fst g) ?_, hY2 (d.snd g) ?_⟩
  · rw [← hY.1, ← hg]; rfl
  · rw [← hY.2, ← hg]; rfl

/-- `t ↦ diag t` is continuous from `GSpin(W)(F)` to `C(W) × C(V)`. -/
theorem continuous_coe_diag :
    Continuous fun t : ↥(GSpin d.QW) => (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient) := by
  have hval : Continuous fun t : ↥(GSpin d.QW) =>
      ((t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) :=
    Units.continuous_val.comp continuous_subtype_val
  have hmap : Continuous (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)) :=
    IsModuleTopology.continuous_of_linearMap
      (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)).toLinearMap
  exact hval.prodMk (hmap.comp hval)

/-- **Translation by a small central semisimple `e^Y` preserves the germ** (an ingredient, not
written out in the Thesis, of the proof of Thesis Prop 12.1.1(i)): if `diag t = diag x · e^Y`
with `t ∈ T_{x,♮}` and `Y ∈ 𝔤_x` small, central in
`𝔤_x` and semisimple, then for `X ∈ 𝔤_t = 𝔤_x` small and regular
`θ(t e^X) = θ(x e^{X+Y}) = ∑ c_O ĵ(O, X + Y) = ∑ c_O ĵ(O, X) = θ(x e^X)`
(`jHat_add_eq_of_nondegenerate`, with `b` nondegenerate on `𝔤_x`), so the germs at `t` and `x`
agree (`germ_eq_germ_of_translate`; `O_t = O_x`). -/
theorem exists_nhds_germ_eq_of_central {χ : CentralCharOn d} {θ : ↥d.G → ℂ} (hθ : θ ∈ QC d χ)
    {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) :
    ∃ N ∈ 𝓝 (0 : d.ambient), ∀ t : ↥(GSpin d.QW), d.IsGammaElt t → t ∈ d.torusOf x →
      d.torusOf t = d.torusOf x → ∀ Y ∈ N,
      Y ∈ lieCentralizer d.lie (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient) →
      (∀ W ∈ lieCentralizer d.lie (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient), Commute W Y) →
      IsSS F Y →
      (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient) =
        (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient) * expA F Y →
      germ d.G d.lie d.bilin ψ θ (d.diag t) (orbitChoice d t) =
        germ d.G d.lie d.bilin ψ θ (d.diag x) (orbitChoice d x) := by
  set X₀ : d.ambient := (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient) with hX₀
  have hssx : IsSS F X₀ := isSS_diag_of_isSS d hx.1
  obtain ⟨c', hc'⟩ := (hθ.1 ψ).2 (d.diag x) hssx
  obtain ⟨-, ω, hω, hexp⟩ := id hc'
  obtain ⟨ω₁, hω₁, hhalf⟩ := exists_nhds_zero_half hω
  obtain ⟨Ua, hUa, hadd⟩ := expA_add_of_commute F (A := d.ambient)
  obtain ⟨UG, hUG, hG⟩ := (eventually_expA_mem_G d).exists_mem
  have hnd := restrictForm_lieCentralizer_nondegenerate d (d.diag x) hssx
  have hopen := isOpen_regularSS_lieCentralizer d (d.diag x) hssx
  refine ⟨ω₁ ∩ Ua, inter_mem hω₁ hUa, fun t ht htx hT Y hYN hY hYc hYss hYt => ?_⟩
  have hsst : IsSS F (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient) := isSS_diag_of_isSS d ht.1
  have hH := grpCentralizer_diag_eq_of_torusOf_eq d hx ht htx hT
  have hL := lieCentralizer_diag_eq_of_torusOf_eq d hx ht htx hT
  refine germ_eq_germ_of_translate ψ θ (d.diag t) (d.diag x) hsst hssx hH hL ?_ ⟨c', hc'⟩ _ _
    (orbitChoice_heq_of_torusOf_eq d hx ht htx hT)
  refine ⟨ω₁ ∩ Ua ∩ UG, inter_mem (inter_mem hω₁ hUa) hUG, fun X hX hXc hXr y hy => ?_⟩
  rw [hL] at hXc hXr
  obtain ⟨g, hg⟩ := hG X hX.2 (mem_lieCentralizer.mp hXc).1
  have hy'' : (((d.diag x * g : ↥d.G) : d.ambientˣ) : d.ambient) = X₀ * expA F X := by
    rw [Subgroup.coe_mul, Units.val_mul, hg]
  refine ⟨d.diag x * g, hy'', ?_⟩
  have hXY : Commute X Y := hYc X hXc
  have hy' : ((y : d.ambientˣ) : d.ambient) = X₀ * expA F (X + Y) := by
    rw [hy, hYt, mul_assoc, add_comm X Y, hadd Y hYN.2 X hX.1.2 hXY.symm]
  have hXYc : X + Y ∈ lieCentralizer d.lie X₀ := (lieCentralizer d.lie X₀).add_mem hXc hY
  have hXYr : IsRegularSS (lieCentralizer d.lie X₀) (X + Y) :=
    (isRegularSS_add_iff_of_central hYss hYc hXc).mpr hXr
  have hω0 : X ∈ ω := by simpa using hhalf X hX.1.1 0 (mem_of_mem_nhds hω₁)
  rw [hexp (X + Y) (hhalf X hX.1.1 Y hYN.1) hXYc hXYr y hy', hexp X hω0 hXc hXr _ hy'']
  refine finsum_congr fun O => ?_
  congr 1
  exact jHat_add_eq_of_nondegenerate (X := ⟨X, hXc⟩) O hnd ⟨Y, hY⟩
    (fun N hN => bilin_eq_zero_of_commute_of_isNilpotent d (hYc N N.2).symm hN)
    (fun Z => isRegularSS_add_iff_of_central hYss hYc Z.2) hopen subset_rfl hXr

/-- **The germ is constant near `x` on `T_{x,♮}`**, in terms of a logarithm: for `t ∈ T_{x,♮}`
and `Y` near `0` with `e^Y = diag(x)⁻¹ diag(t)`, the germs at `t` and `x` agree.  `Y` lies in `𝔤`
(`eventually_mem_lie_of_expA_mem`), commutes with `diag x` and with `𝔤_x = 𝔤_t`
(`exists_nhds_commute_of_commute_expA`), and lies in `F[e^Y]` (`exists_nhds_mem_of_expA_mem`),
hence is semisimple; then `exists_nhds_germ_eq_of_central` applies. -/
theorem exists_nhds_germ_eq_of_expA {χ : CentralCharOn d} {θ : ↥d.G → ℂ} (hθ : θ ∈ QC d χ)
    {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) :
    ∃ N ∈ 𝓝 (0 : d.ambient), ∀ t : ↥(GSpin d.QW), d.IsGammaElt t → t ∈ d.torusOf x →
      d.torusOf t = d.torusOf x → ∀ Y ∈ N,
      expA F Y = ((((d.diag x : ↥d.G) : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) *
        (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient) →
      germ d.G d.lie d.bilin ψ θ (d.diag t) (orbitChoice d t) =
        germ d.G d.lie d.bilin ψ θ (d.diag x) (orbitChoice d x) := by
  obtain ⟨N₁, hN₁, hgerm⟩ := exists_nhds_germ_eq_of_central ψ d hθ hx
  obtain ⟨Ul, hUl, hlie⟩ := (eventually_mem_lie_of_expA_mem d).exists_mem
  obtain ⟨Uc, hUc, hcomm⟩ := exists_nhds_commute_of_commute_expA F (A := d.ambient)
  obtain ⟨Us, hUs, hsub⟩ := exists_nhds_mem_of_expA_mem F (A := d.ambient)
  refine ⟨N₁ ∩ Ul ∩ Uc ∩ Us, inter_mem (inter_mem (inter_mem hN₁ hUl) hUc) hUs,
    fun t ht htx hT Y hY he => ?_⟩
  obtain ⟨⟨⟨hYN, hYl⟩, hYc⟩, hYs⟩ := hY
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : d.ambient, X₀ = (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient) :=
    ⟨_, rfl⟩
  obtain ⟨Dt, hDt⟩ : ∃ Dt : d.ambient, Dt = (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient) :=
    ⟨_, rfl⟩
  have hssx : IsSS F X₀ := hX₀ ▸ isSS_diag_of_isSS d hx.1
  have hsst : IsSS F Dt := hDt ▸ isSS_diag_of_isSS d ht.1
  have hDX : Commute Dt X₀ := by
    have hc : Commute t x := Subgroup.mem_centralizer_singleton_iff.mp htx.1
    rw [hDt, hX₀]
    exact congrArg (fun k : ↥d.G => ((k : d.ambientˣ) : d.ambient)) (hc.map d.diag).eq
  have hDteq : (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient) =
      (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient) * expA F Y := by
    rw [he, ← mul_assoc, Units.mul_inv, one_mul]
  have hYlie : Y ∈ d.lie := hlie Y hYl ((d.diag x)⁻¹ * d.diag t) (by rw [he]; rfl)
  have hcommY : ∀ W : d.ambient, Commute W X₀ → Commute W Dt → Commute W Y := fun W h1 h2 => by
    refine hcomm Y hYc W ?_
    rw [he]
    rw [hX₀] at h1
    rw [hDt] at h2
    exact h1.units_inv_right.mul_right h2
  have hL := lieCentralizer_diag_eq_of_torusOf_eq d hx ht htx hT
  rw [← hX₀, ← hDt] at hL
  have hYcent : Y ∈ lieCentralizer d.lie X₀ :=
    mem_lieCentralizer.mpr ⟨hYlie, (hcommY X₀ (Commute.refl _) hDX.symm).eq⟩
  have hYc' : ∀ W ∈ lieCentralizer d.lie X₀, Commute W Y := by
    intro W hW
    have h1 := (mem_lieCentralizer.mp hW).2
    have h2 := (mem_lieCentralizer.mp (hL.symm ▸ hW : W ∈ lieCentralizer d.lie Dt)).2
    exact hcommY W h1.symm h2.symm
  have huss : IsSS F (expA F Y) := by
    rw [he]
    refine isSS_mul_of_commute ?_ (isSS_coe_inv (hX₀ ▸ hssx)) (hDt ▸ hsst)
    have := hDX.symm
    rw [hDt, hX₀] at this
    exact this.units_inv_left
  have hYss : IsSS F Y := isSS_of_mem_adjoin huss
    (hsub Y hYs (Algebra.adjoin F {expA F Y}) (Algebra.self_mem_adjoin_singleton F _))
  exact hgerm t ht htx hT Y hYN (hX₀ ▸ hYcent) (hX₀ ▸ hYc') hYss hDteq

/-- **The germ term is continuous on `T_♮`** (an ingredient, not written out in the Thesis, of
the proof of Thesis Prop 12.1.1(i)): for `θ ∈ QC(G(F), χ)`,
`t ↦ c_{θ,O_t}(t)` is locally constant on `T_♮`.  Near `t₀ ∈ T_♮`, write
`diag t = diag t₀ · e^Y` with `Y = log(diag(t₀)⁻¹ diag t)` (`exists_logA`), small; then the germs at
`t` and `t₀` agree (`exists_nhds_germ_eq_of_expA`): `Y` is central in `𝔤_{t₀}` and semisimple, and
`ĵ(O, X + Y) = ĵ(O, X)` on the regular set of `𝔤_{t₀}`.
Literature: Waldspurger 2010 (Compositio 146; arXiv:0902.1875, §7.3, Proposition (i), proof in
§7.6–7.7) proves this local constancy for quasi-characters of `SO(W)` and of `SO(V)` separately; here
the group is `GSpin(W) × GSpin(V)` and the argument is carried out directly.  The openness of the
regular set of `𝔤_{t₀}` is `isOpen_regularSS_lieCentralizer` (not yet formalized). -/
theorem continuousOn_germ_of_mem_QC {χ : CentralCharOn d} {θ : ↥d.G → ℂ}
    (hθ : θ ∈ QC d χ) (T : Subgroup ↥(GSpin d.QW)) :
    ContinuousOn (fun t : ↥T => germ d.G d.lie d.bilin ψ θ (d.diag (t : ↥(GSpin d.QW)))
        (orbitChoice d (t : ↥(GSpin d.QW))))
      {t : ↥T | d.IsGammaElt (t : ↥(GSpin d.QW)) ∧ d.torusOf (t : ↥(GSpin d.QW)) = T} := by
  rw [(isOpen_torusNat d T).continuousOn_iff]
  rintro t₀ ⟨hx, hT⟩
  obtain ⟨N, hN, hgerm⟩ := exists_nhds_germ_eq_of_expA ψ d hθ hx
  obtain ⟨log, hlc, hl1, hle⟩ := exists_logA F (A := d.ambient)
  -- `u(t) = diag(t₀)⁻¹ diag(t) → 1`, so `log u(t) → 0`
  obtain ⟨u, hudef⟩ : ∃ u : ↥T → d.ambient, u = fun t : ↥T =>
      ((((d.diag (t₀ : ↥(GSpin d.QW)) : ↥d.G) : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) *
        (((d.diag (t : ↥(GSpin d.QW)) : ↥d.G) : d.ambientˣ) : d.ambient) := ⟨_, rfl⟩
  have hu : Continuous u := by
    rw [hudef]
    exact continuous_const.mul ((continuous_coe_diag d).comp continuous_subtype_val)
  have hut : Tendsto u (𝓝 t₀) (𝓝 1) := by
    have h1 : u t₀ = 1 := by rw [hudef]; exact Units.inv_mul _
    simpa [h1] using hu.tendsto t₀
  have hY : Tendsto (fun t => log (u t)) (𝓝 t₀) (𝓝 0) := by
    have := hlc.tendsto.comp hut
    rwa [hl1] at this
  have h0 : ∀ᶠ t in 𝓝 t₀, t ∈ {t : ↥T | d.IsGammaElt (t : ↥(GSpin d.QW)) ∧
      d.torusOf (t : ↥(GSpin d.QW)) = T} := (isOpen_torusNat d T).mem_nhds ⟨hx, hT⟩
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [h0, hut.eventually hle, hY.eventually hN] with t ⟨ht, hT'⟩ he hYN
  have htx : (t : ↥(GSpin d.QW)) ∈ d.torusOf (t₀ : ↥(GSpin d.QW)) := hT.symm ▸ t.2
  exact hgerm t ht htx (hT'.trans hT.symm) _ hYN (he.trans (by rw [hudef]))

/-- **`D^G(t)^{1/2} c_{θ,O_t}(t)` is continuous on `T_♮`** (used in the proof of Thesis
Prop 12.1.1(i)): from
`continuousOn_weylDisc_torusNat` and `continuousOn_germ_of_mem_QC`. -/
theorem continuousOn_weylDisc_germ_of_mem_QC {χ : CentralCharOn d} {θ : ↥d.G → ℂ}
    (hθ : θ ∈ QC d χ) (T : Subgroup ↥(GSpin d.QW)) :
    ContinuousOn (fun t : ↥T => (Real.sqrt (weylDisc d.lie (d.diag (t : ↥(GSpin d.QW)) :
        d.ambientˣ)) : ℂ) * germ d.G d.lie d.bilin ψ θ (d.diag (t : ↥(GSpin d.QW)))
          (orbitChoice d (t : ↥(GSpin d.QW))))
      {t : ↥T | d.IsGammaElt (t : ↥(GSpin d.QW)) ∧ d.torusOf (t : ↥(GSpin d.QW)) = T} :=
  (Complex.continuous_ofReal.comp_continuousOn
    (Real.continuous_sqrt.comp_continuousOn (continuousOn_weylDisc_torusNat d T))).mul
    (continuousOn_germ_of_mem_QC ψ d hθ T)

/-- **The integrand of `m_{geom,s}` is continuous on `T_♮`** (used in the proof of Thesis
Prop 12.1.1(i)): it is the
product of `D^G(t)^{1/2} c_{θ,O_t}(t)` (`continuousOn_weylDisc_germ_of_mem_QC`) and `Δ(t)^{s−1/2}`
(`continuousOn_deltaGGP_rpow`) there. -/
theorem continuousOn_gammaIntegrand_of_mem_QC {χ : CentralCharOn d} {θ : ↥d.G → ℂ}
    (hθ : θ ∈ QC d χ) (T : Subgroup ↥(GSpin d.QW)) (s : ℝ) :
    ContinuousOn (fun t : ↥T => gammaIntegrand ψ d θ T s (t : ↥(GSpin d.QW)))
      {t : ↥T | d.IsGammaElt (t : ↥(GSpin d.QW)) ∧ d.torusOf (t : ↥(GSpin d.QW)) = T} := by
  refine ((continuousOn_weylDisc_germ_of_mem_QC ψ d hθ T).mul
    (continuousOn_deltaGGP_rpow d T s)).congr fun t ht => ?_
  have ht' : d.IsGammaElt (t : ↥(GSpin d.QW)) ∧ d.torusOf (t : ↥(GSpin d.QW)) = T := ht
  simp only [gammaIntegrand, ht', and_self, ↓reduceIte, Pi.mul_apply]

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
