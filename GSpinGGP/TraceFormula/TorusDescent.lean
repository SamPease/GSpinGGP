/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Interface
import GSpinGGP.TraceFormula.GermTranslate
import GSpinGGP.GGP.MovedCentralizer
import GSpinGGP.Foundations.RankSemicontinuity
import GSpinGGP.GGP.IsometrySemisimple
import GSpinGGP.GGP.GSpinSemisimple

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
For `c ≠ 0` small, `e^{cZ} ∈ T_x(F)` (`MovedPart.exists_nhds_expA_mem_GSpin`), so it commutes
with `t`, and near `0` the centralizer of `e^{cZ}` is that of `cZ`
(`exists_nhds_commute_of_commute_expA`). -/
theorem commute_of_mem_torusOf_of_movedPart {x t : ↥(GSpin d.QW)}
    (hcomm : ∀ a ∈ d.torusOf x, ∀ b ∈ d.torusOf x, Commute a b) (ht : t ∈ d.torusOf x)
    {Z : CliffordAlgebra d.QW} (hZ : Z ∈ gspin d.QW)
    (hZx : ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * Z =
      Z * ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
    (hZf : ∀ v ∈ fixedSub x, CliffordAlgebra.ι d.QW v * Z = Z * CliffordAlgebra.ι d.QW v) :
    ((t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * Z =
      Z * ((t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) := by
  obtain ⟨U, hU, hG⟩ := MovedPart.exists_nhds_expA_mem_GSpin (F := F) d.QW
  obtain ⟨U', hU', hc⟩ := exists_nhds_commute_of_commute_expA F (A := CliffordAlgebra d.QW)
  have hlim : Tendsto (fun c : F => c • Z) (𝓝[≠] 0) (𝓝 0) := by
    have : Continuous (fun c : F => c • Z) := continuous_id.smul continuous_const
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨c, hcU, hc0⟩ := ((hlim.eventually (inter_mem hU hU')).and self_mem_nhdsWithin).exists
  obtain ⟨g, hg⟩ := hG _ hcU.1 ((gspin d.QW).smul_mem c hZ)
  have hgT : g ∈ d.torusOf x := by
    refine ⟨?_, fun w hw => ?_⟩
    · show g ∈ Subgroup.centralizer {x}
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxc : Commute ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) (c • Z) :=
        Commute.smul_right hZx c
      have := commute_expA_of_commute (F := F) hxc
      rw [← hg] at this
      exact Subtype.ext (Units.ext this.eq.symm)
    · apply CliffordAlgebra.ι_injective d.QW
      rw [ι_specP]
      have hwc : Commute (CliffordAlgebra.ι d.QW w) (c • Z) := Commute.smul_right (hZf w hw) c
      have := (commute_expA_of_commute (F := F) hwc).eq
      rw [← hg] at this
      rw [← this, mul_assoc, Units.mul_inv, mul_one]
  have h1 : Commute ((t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) (expA F (c • Z)) := by
    have := congrArg (fun k : ↥(GSpin d.QW) =>
      (((k : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW)) (hcomm g hgT t ht).eq
    simp only [Subgroup.coe_mul, Units.val_mul] at this
    rw [hg] at this
    exact this.symm
  have h2 := (hc _ hcU.2 _ h1).eq
  rw [mul_smul_comm, smul_mul_assoc] at h2
  exact smul_right_injective _ hc0 h2

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

open scoped Pointwise in
omit [PAdicField F] in
/-- `|u|_F = 1` for `‖u‖ = 1`: multiplication by `u` preserves the closed unit ball. -/
theorem absF_eq_one_of_norm_eq_one [LocallyCompactSpace F] {u : F} (hu : ‖u‖ = 1) :
    absF u = 1 := by
  let _ : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  set μ : Measure F := Measure.addHaar
  have hs : u • Metric.closedBall (0 : F) 1 = Metric.closedBall 0 1 := by
    rw [smul_closedBall u (0 : F) zero_le_one, smul_zero, hu, mul_one]
  have h := absF_haar μ hu0 (Metric.closedBall 0 1)
  rw [hs] at h
  have hpos := Metric.measure_closedBall_pos μ (0 : F) zero_lt_one
  have hfin := (isCompact_closedBall (0 : F) 1).measure_lt_top (μ := μ)
  have h1 : ENNReal.ofReal (absF u) = 1 := (ENNReal.mul_eq_right hpos.ne' hfin.ne).mp h.symm
  rwa [ENNReal.ofReal_eq_one] at h1

omit [PAdicField F] in
/-- `|a|_F` only depends on `‖a‖`. -/
theorem absF_eq_of_norm_eq [LocallyCompactSpace F] {a b : F} (ha : a ≠ 0) (h : ‖b‖ = ‖a‖) :
    absF b = absF a := by
  have hb : b = a * (b / a) := by field_simp
  rw [hb, absF_mul, absF_eq_one_of_norm_eq_one (u := b / a) ?_, mul_one]
  rw [norm_div, h, div_self (norm_ne_zero_iff.mpr ha)]

omit [PAdicField F] in
/-- Over an ultrametric local field, `|·|_F` is locally constant on `F^×`. -/
theorem continuousAt_absF [LocallyCompactSpace F] [IsUltrametricDist F] {a : F} (ha : a ≠ 0) :
    ContinuousAt absF a := by
  have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  refine (continuousAt_const (y := absF a)).congr ?_
  filter_upwards [Metric.ball_mem_nhds a hpos] with b hb
  rw [Metric.mem_ball, dist_eq_norm] at hb
  refine (absF_eq_of_norm_eq ha ?_).symm
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hb)
  rwa [add_sub_cancel, max_eq_left hb.le] at this

omit [PAdicField F] in
/-- The determinant of a pointwise continuous family of endomorphisms of a finite-dimensional
normed space is continuous. -/
theorem continuous_det_of_continuous_apply [CompleteSpace F] {X : Type*} [TopologicalSpace X]
    {U : Type*} [NormedAddCommGroup U] [NormedSpace F U] [FiniteDimensional F U]
    (f : X → U →ₗ[F] U) (hf : ∀ v, Continuous fun x => f x v) :
    Continuous fun x => LinearMap.det (f x) := by
  classical
  let b := Module.finBasis F U
  simp_rw [← LinearMap.det_toMatrix b]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  simp only [LinearMap.toMatrix_apply]
  exact (LinearMap.continuous_of_finiteDimensional (b.coord i)).comp (hf (b j))

/-- **`Δ(t)^{s−1/2}` is continuous on `T_♮`** (part of Thesis Prop 12.1.1(i)).  For `x ∈ T_♮`
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
    refine continuous_det_of_continuous_apply g fun u => ?_
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

/-- **`D^G(t)^{1/2} c_{θ,O_t}(t)` is continuous on `T_♮`** (Thesis Prop 12.1.1(i)).  Proof sketch:
on `T_♮` the centralizers `G_t`, `𝔤_t` are those of `x ∈ T_♮` (`T = T_x`): over `F̄`,
`Z(t̄) = Z(x̄)` (`GGPData.commute_bc_iff_of_torusOf_eq` and its `V`-version), and `𝔤_t = 𝔤_x`
follows by exponentiating (`MovedPart.exists_nhds_expA_mem_GSpin`,
`exists_nhds_commute_of_commute_expA`).  So `1 − Ad t` is semisimple with kernel `𝔤_x` of constant
dimension `r`, and `D^G(t) = |c_r(t)|_F` with `c_r(t)` the coefficient of `X^r` in the
characteristic polynomial of `1 − Ad t` on `𝔤`, continuous and nonzero; hence `D^G` is
continuous on `T_♮`.  And `t ↦ c_{θ,O_t}(t)` is locally constant: for `t' = t e^Y` with
`Y ∈ Lie T` small (central in `𝔤_t`), `θ(t' e^X) = θ(t e^{X+Y})`, and `ĵ(O, X + Y) = ĵ(O, X)` on
`𝔤_{t,reg}` (`b(Y, N) = 0` for `N` nilpotent commuting with `Y`), so the expansion at `t` is one
at `t'` with the same coefficients, while `O_{t'} = O_t` (`OrbitSpec d t' = OrbitSpec d t`).
Status: SORRY (own work, GSpin input). -/
theorem continuousOn_weylDisc_germ_of_mem_QC {χ : CentralCharOn d} {θ : ↥d.G → ℂ}
    (hθ : θ ∈ QC d χ) (T : Subgroup ↥(GSpin d.QW)) :
    ContinuousOn (fun t : ↥T => (Real.sqrt (weylDisc d.lie (d.diag (t : ↥(GSpin d.QW)) :
        d.ambientˣ)) : ℂ) * germ d.G d.lie d.bilin ψ θ (d.diag (t : ↥(GSpin d.QW)))
          (orbitChoice d (t : ↥(GSpin d.QW))))
      {t : ↥T | d.IsGammaElt (t : ↥(GSpin d.QW)) ∧ d.torusOf (t : ↥(GSpin d.QW)) = T} := by
  sorry

/-- **The integrand of `m_{geom,s}` is continuous on `T_♮`** (Thesis Prop 12.1.1(i)): it is the
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
