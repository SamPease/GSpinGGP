/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LieAlgebra
import GSpinGGP.TraceFormula.LuoExpansion

/-!
# From the special orthogonal triple to `𝔤⁰`: `J^Lie = m^Lie_geom(θ_f)`

The statement `luo_lie_geomExpansion_SO` (`TraceFormula/LuoExpansion.lean`) is about the special orthogonal triple
`(Ḡ, H̄, ξ)` of an admissible pair, with objects defined on the quadratic spaces
(`TraceFormula/SOLie.lean`).  This file identifies them with the objects on
`𝔤⁰ = so(W) ⊕ so(V) ⊆ C(W) × C(V)` of the general spin triple (`TraceFormula/LieAlgebra.lean`)
when neither `W` nor `V` is a hyperbolic plane, and deduces
`distribJLie_eq_mGeomLie_of_luo`: `J^Lie(f) = m^Lie_geom(θ_f)` for `f ∈ S_scusp(𝔤⁰(F))` (Thesis
Thm 12.2.2 on `𝔤⁰`).

The identification is own work, stated step by step (most steps are `sorry` here):
* (L1) `toSO`: `X ↦ (ad_W X_W, ad_V X_V)` maps `𝔤⁰` onto `so(W) ⊕ so(V)` (`toSO_mem` is proved;
  `toSO_bijective` and the transfer of strong cuspidality `isScusp_toSO` are `sorry`);
* (L2) `luoOf`: the admissible pair of `d` with Luo's basis `z^L_i = ν^{-i} z_i`,
  `z^L_{-i} = ν^{i-1} z_{-i}` (`i ≥ 1`), `z^L_0 = z_0` (`luoOf_gram` proved), and `λ` agrees
  (`lam_toSO`);
* (L3) `muG`: the push-forward of `Measure.haar` on `G(F)/A_G(F)` to `Ḡ(F)`, a Haar measure
  (`muG_isHaarMeasure`);
* (L4) `exists_JLie_transfer`: `J^Lie` of `d` is Luo's `J^Lie` for compatible measures;
* (L5) `isThetaFLie_of_SO`: a `θ` representing the orbital pairing on `so(W) ⊕ so(V)` gives one on
  `𝔤⁰`;
* `isThetaFLie_eqOn_regular`: `θ_f` is unique on `𝔤⁰_reg`;
* (L6, L7) `cTheta_toSO`: the germs `c_{θ,O_X}(X)` agree (trace form vs `bilin`, `Z_G(X)` vs
  `Ḡ_X`, the orbit choice `orbitChoiceLie` vs Luo's and Waldspurger's `O_{±ν₀}`);
* (L8) `gammaClass_equiv`, `torusIntegralLie_toSO`: `Γ^Lie` (tori, `|W(H,T)|`, `ν(T) dX`,
  `D^G`, `Δ`, `𝔱_♮`) agree; `mGeomLieS_toSO` is proved from them;
* (L9) `mGeomLie_congr_regularSet`: `m^Lie_geom(θ)` depends only on `θ|_{𝔤⁰_reg}`.
-/

noncomputable section

open MeasureTheory Topology Filter

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

/-! ## (L2) The admissible pair with Luo's basis -/

/-- The rescaling of `z_i` to Luo's basis: `ν^{-i}` for `i ≥ 0`, `ν^{-i-1}` for `i < 0`. -/
def luoScale (i : ℤ) : F := if 0 ≤ i then (d.ν : F) ^ (-i) else (d.ν : F) ^ (-i - 1)

/-- Luo's basis `z^L_i = ν^{-i} z_i`, `z^L_{-i} = ν^{i-1} z_{-i}` (`i ≥ 1`), `z^L_0 = z_0`. -/
def luoZ (i : ℤ) : d.Z := d.luoScale i • zvec d.r i

theorem luoScale_mul_neg {i : ℤ} (hi : i ≠ 0) : d.luoScale i * d.luoScale (-i) * (d.ν : F) = 1 := by
  have hν : (d.ν : F) ≠ 0 := d.ν.ne_zero
  unfold luoScale
  rcases lt_or_gt_of_ne hi with h | h
  · have h1 : ¬ (0 ≤ i) := by omega
    have h2 : 0 ≤ -i := by omega
    simp only [h1, h2, ↓reduceIte]
    rw [← zpow_add₀ hν, ← zpow_add_one₀ hν]
    convert zpow_zero (d.ν : F) using 2; ring
  · have h1 : 0 ≤ i := by omega
    have h2 : ¬ (0 ≤ -i) := by omega
    simp only [h1, h2, ↓reduceIte]
    rw [← zpow_add₀ hν, ← zpow_add_one₀ hν]
    convert zpow_zero (d.ν : F) using 2; ring

/-- **Luo's normalization holds for `luoZ`** (Luo §2.1): `q(z^L_i, z^L_j) = δ_{i,-j}` for
`i, j ≠ 0`, `q(z^L_0, z^L_0) = ν`. -/
theorem luoZ_gram (i j : ℤ) (hi : |i| ≤ d.r) (hj : |j| ≤ d.r) :
    bform d.QZ (d.luoZ i) (d.luoZ j) =
      if i + j = 0 then (if i = 0 then d.QZ (d.luoZ 0) else 1) else 0 := by
  have h := bform_splitOddForm_zvec (K := F) d.r (d.ν : F) hi hj
  simp only [luoZ, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [h]
  split_ifs with h1 h2
  · subst h2
    have h00 := bform_splitOddForm_zvec (K := F) d.r (d.ν : F) (le_of_eq abs_zero |>.trans
      (Nat.cast_nonneg _)) (le_of_eq abs_zero |>.trans (Nat.cast_nonneg _))
    rw [← QuadraticMap.associated_eq_self_apply F d.QZ (d.luoScale 0 • zvec d.r 0)]
    simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [show j = 0 by omega]
    rw [h00]; simp
  · rw [show j = -i by omega, ← mul_assoc, d.luoScale_mul_neg h2]
  · simp

theorem QZ_luoZ_zero_ne : d.QZ (d.luoZ 0) ≠ 0 := by
  have h00 := bform_splitOddForm_zvec (K := F) d.r (d.ν : F) (le_of_eq abs_zero |>.trans
    (Nat.cast_nonneg _)) (le_of_eq abs_zero |>.trans (Nat.cast_nonneg _))
  rw [← QuadraticMap.associated_eq_self_apply F d.QZ (d.luoZ 0)]
  simp only [luoZ, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [h00]
  simp [luoScale, d.ν.ne_zero]

/-- **The admissible pair of `d` with Luo's basis** (`luoZ`): `W`, `QW`, `r` and
`D ⊕ Z = K^{2r+1}` with `QZ` are those of `d`, so `V` and `QV` are those of `d`. -/
def luoOf : LuoDatum F where
  m := d.m
  QW := d.QW
  nondeg := d.nondeg
  r := d.r
  QZ := d.QZ
  z := d.luoZ
  gram := d.luoZ_gram
  aniso := d.QZ_luoZ_zero_ne

/-! ## (L1) `𝔤⁰ ≅ so(W) ⊕ so(V)` -/

/-- `X = (X_W, X_V) ↦ (ad_W X_W, ad_V X_V)`, the action on `W` and on `V`. -/
def toSOLin : d.ambient →ₗ[F] d.luoOf.Amb :=
  LinearMap.prod ((adV d.QW).comp (LinearMap.fst F _ _)) ((adV d.QV).comp (LinearMap.snd F _ _))

theorem fstA_toSOLin (X : d.ambient) : d.luoOf.fstA (d.toSOLin X) = adV d.QW X.1 := rfl

theorem sndA_toSOLin (X : d.ambient) : d.luoOf.sndA (d.toSOLin X) = adV d.QV X.2 := rfl

/-- `adV X` is skew for `X ∈ gspin` (`bform_adV`). -/
theorem adV_mem_skewAdjoint {V : Type*} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
    {X : CliffordAlgebra Q} (hX : X ∈ gspin Q) :
    adV Q X ∈ skewAdjointLieSubalgebra (bform Q) := by
  show adV Q X ∈ (bform Q).skewAdjointSubmodule
  rw [LinearMap.mem_skewAdjointSubmodule]
  intro u w
  rw [bform_adV hX, Pi.neg_apply, map_neg]

/-- (L1) `ad` maps `𝔤⁰` into `so(W) ⊕ so(V)`. -/
theorem toSO_mem (X : ↥d.lieZero) : d.toSOLin (X : d.ambient) ∈ d.luoOf.lie :=
  ⟨adV_mem_skewAdjoint X.2.1.1, adV_mem_skewAdjoint X.2.2.1⟩

/-- `𝔤⁰ → so(W) ⊕ so(V)`. -/
def toSOFun (X : ↥d.lieZero) : ↥d.luoOf.lie := ⟨d.toSOLin X, d.toSO_mem X⟩

/-- **(L1) `ad : 𝔤⁰ → so(W) ⊕ so(V)` is bijective** (Thesis Prop 5.1.3.1: `so_Cliff(V) ≅ ∧²V ≅
so(V)`; injective on the traceless part, onto by `exists_mem_soSub_adV_eq`-type surjectivity).
Not proved here. -/
theorem toSO_bijective : Function.Bijective d.toSOFun := by
  sorry

/-- `𝔤⁰ ≃ so(W) ⊕ so(V)`. -/
def toSO : ↥d.lieZero ≃ ↥d.luoOf.lie := Equiv.ofBijective d.toSOFun d.toSO_bijective

/-- **(L1) Strong cuspidality is transported** (`IsLieScusp` on `𝔤⁰` to `IsScusp` on
`so(W) ⊕ so(V)`): `ad` carries the flag parabolics `𝔭⁰ = liePar`, their radicals `lieUnip` and the
properness condition (`whittB FW FV ≠ ⊤` vs a non-stabilizing element of `Ḡ`, through the surjection
`G(F) → Ḡ(F)`) to those of `Ḡ`, and Haar measures on `𝔲(F)` to Haar measures.  Not proved here. -/
theorem isScusp_toSO {f : ↥d.lieZero → ℂ} (hf : d.IsLieScusp f) :
    d.luoOf.IsScusp (f ∘ d.toSO.symm) := by
  sorry

theorem luoOf_zV (i : ℤ) : d.luoOf.zV i = d.luoScale i • d.zV i := by
  unfold LuoDatum.zV GGPData.zV
  rw [Prod.smul_mk, smul_zero]
  rfl

theorem luoScale_neg_succ_mul (i : ℕ) : d.luoScale (-(i : ℤ) - 1) * d.luoScale (i : ℕ) = 1 := by
  have hν : (d.ν : F) ≠ 0 := d.ν.ne_zero
  have h1 : ¬ (0 ≤ -(i : ℤ) - 1) := by omega
  have h2 : (0 : ℤ) ≤ (i : ℕ) := by omega
  simp only [luoScale, h1, h2, ↓reduceIte]
  rw [← zpow_add₀ hν]
  convert zpow_zero (d.ν : F) using 2; ring

/-- **(L2) `λ` agrees with Luo's `λ`**: `Σ_{i<r} b(z_{-i-1}, X z_i) = Σ_{i<r}
q(z^L_{-i-1}, X z^L_i)`, since `z^L_{-i-1} = ν^{i} z_{-i-1}` and `z^L_i = ν^{-i} z_i`. -/
theorem lam_toSO (X : d.ambient) : d.lamLie X = d.luoOf.lam (d.toSOLin X) := by
  have key : ∀ k : ℕ, bform d.QV (d.zV (-(k : ℤ) - 1)) (adV d.QV X.2 (d.zV k)) =
      bform d.QV (d.luoOf.zV (-(k : ℤ) - 1)) (adV d.QV X.2 (d.luoOf.zV k)) := by
    intro k
    rw [d.luoOf_zV, d.luoOf_zV, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul,
      map_smul, smul_eq_mul, ← mul_assoc, d.luoScale_neg_succ_mul, one_mul]
  exact Finset.sum_congr rfl fun i _ => key i

/-! ## (L3) The Haar measure on `Ḡ(F)` -/

/-- `G(F) → Ḡ(F) ⊆ (End W × End V)ˣ`, `(a, b) ↦ (P(a), P(b))` (`Pbar`). -/
def toGbarU : ↥d.G →* d.luoOf.Ambˣ :=
  ((MulEquiv.prodUnits.symm.toMonoidHom :
      (Module.End F d.luoOf.W)ˣ × (Module.End F d.luoOf.V)ˣ →*
        (Module.End F d.luoOf.W × Module.End F d.luoOf.V)ˣ)).comp
    ((((LinearMap.GeneralLinearGroup.generalLinearEquiv F d.luoOf.W).symm.toMonoidHom.comp
        (SOGrp d.QW).subtype).prodMap
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv F d.luoOf.V).symm.toMonoidHom.comp
        (SOGrp d.QV).subtype)).comp d.Pbar)

theorem toGbarU_mem (g : ↥d.G) : d.toGbarU g ∈ d.luoOf.Gbar := by
  refine ⟨?_, ?_⟩
  · show (LinearMap.GeneralLinearGroup.generalLinearEquiv F d.luoOf.W)
      (d.luoOf.unitFst (d.toGbarU g)) ∈ SOGrp d.QW
    have h : (LinearMap.GeneralLinearGroup.generalLinearEquiv F d.luoOf.W)
        (d.luoOf.unitFst (d.toGbarU g)) = (((d.Pbar g).1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))) :=
      LinearEquiv.ext fun _ => rfl
    rw [h]; exact (d.Pbar g).1.2
  · show (LinearMap.GeneralLinearGroup.generalLinearEquiv F d.luoOf.V)
      (d.luoOf.unitSnd (d.toGbarU g)) ∈ SOGrp d.QV
    have h : (LinearMap.GeneralLinearGroup.generalLinearEquiv F d.luoOf.V)
        (d.luoOf.unitSnd (d.toGbarU g)) = (((d.Pbar g).2 : d.V ≃ₗ[F] d.V)) :=
      LinearEquiv.ext fun _ => rfl
    rw [h]; exact (d.Pbar g).2.2

/-- `G(F) → Ḡ(F)`. -/
def toGbar : ↥d.G →* ↥d.luoOf.Gbar := d.toGbarU.codRestrict _ d.toGbarU_mem

/-- **The Haar measure on `Ḡ(F)`**: the push-forward of `Measure.haar` on `G(F)/A_G(F)` along
`G(F)/A_G(F) → Ḡ(F)` (an isomorphism of topological groups when neither `W` nor `V` is a hyperbolic
plane: `AGbar_eq_bot` and Hilbert 90, `Pbar_surjective`). -/
def muG : Measure ↥d.luoOf.Gbar :=
  Measure.map (fun x : d.GmodAG => d.toGbar (Quotient.out x)) Measure.haar

/-- **(L3) `muG` is a Haar measure on `Ḡ(F)`**: `G(F)/A_G(F) → Ḡ(F)` is a bijective continuous
homomorphism of locally compact, σ-compact groups (`AGbar_eq_bot`, `Pbar_surjective`), hence a
homeomorphism (open mapping theorem), and the push-forward of a Haar measure by an isomorphism of
topological groups is a Haar measure.  Not proved here. -/
theorem muG_isHaarMeasure (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) :
    d.muG.IsHaarMeasure := by
  sorry

/-! ## (L4) `J^Lie` -/

variable (ψ : NontrivialAddChar F)

/-- **(L4) `J^Lie` of `d` is Luo's `J^Lie`** for `muG`, a Haar measure `μH` on `H̄(F)`, the
`exp`-compatible `μ_𝔥` and the quotient measure: `H(F)/A_{G,H}(F) ≃ H̄(F)` (Hilbert 90 and
`ker P ∩ H = A_{G,H}`, through `quotHG_equiv_SO`), `ad : 𝔥⁰ ≃ 𝔥 = so(W) ⊕ 𝔫`, `λ` (`lam_toSO`), `measH0` and `weilMeasureHG` push forward to an `exp`-compatible pair and its Weil
measure (independence of the `exp`-compatible pair), and change of variables.  Not proved here. -/
theorem exists_JLie_transfer (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) :
    ∃ (μH : Measure ↥d.luoOf.Hbar) (μ𝔥 : Measure ↥d.luoOf.lieH)
      (m : Measure (CosetSpace d.luoOf.Hbar.subtype)),
      μH.IsHaarMeasure ∧ d.luoOf.IsExpCompatH μH μ𝔥 ∧
      IsWeilMeasure d.luoOf.Hbar.subtype d.muG μH m ∧
      ∀ f : ↥d.lieZero → ℂ, d.IsLieScusp f →
        d.distribJLie ψ f = d.luoOf.distribJLie ψ μ𝔥 m (f ∘ d.toSO.symm) := by
  sorry

/-! ## (L5) `θ_f` -/

/-- **(L5) `θ_f` transfers**: if `θ` on `so(W) ⊕ so(V)` is locally integrable, continuous on the
regular set and represents the orbital pairing of `f ∘ ad⁻¹` for `muG`, then `θ ∘ ad` represents
the orbital pairing of `f` on `𝔤⁰` (`IsThetaFLie`).  Ingredients: `ad` carries `measLie0` (self-dual
for `bilin`) to a positive multiple `c` of the self-dual measure for the trace form (both are Haar
measures), which multiplies both sides of the identity; `ad(gXg⁻¹) = P(g) ad(X) P(g)⁻¹`; the
regular sets correspond; change of variables along `G(F)/A_G(F) ≃ Ḡ(F)`.  Not proved here. -/
theorem isThetaFLie_of_SO (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    {f : ↥d.lieZero → ℂ} (hf : d.IsLieScusp f) {θ : ↥d.luoOf.lie → ℂ}
    (h1 : LocallyIntegrable θ (d.luoOf.measLie ψ))
    (h2 : ContinuousOn θ {X : ↥d.luoOf.lie | IsRegularSS d.luoOf.lie (X : d.luoOf.Amb)})
    (h3 : ∀ f' : ↥d.luoOf.lie → ℂ, IsTestFn f' →
      ∫ X, θ X * f' X ∂d.luoOf.measLie ψ = d.luoOf.orbitalPairing ψ d.muG (f ∘ d.toSO.symm) f') :
    d.IsThetaFLie ψ f (θ ∘ d.toSO) := by
  sorry

/-- **`θ_f` is unique on `𝔤⁰_reg`**: two locally integrable functions, continuous on `𝔤⁰_reg(F)`,
representing the same distribution agree on `𝔤⁰_reg(F)` (they agree almost everywhere, `𝔤⁰_reg` is
open and `measLie0` charges every nonempty open set).  This uses that `measLie0` is a Haar measure
and not the junk value `0`, i.e. that `bilin` is nondegenerate on `𝔤⁰`, so that a self-dual measure
exists; that nondegeneracy is part of what remains to be proved.  Not proved here. -/
theorem isThetaFLie_eqOn_regular {f θ θ' : ↥d.lieZero → ℂ} (hθ : d.IsThetaFLie ψ f θ)
    (hθ' : d.IsThetaFLie ψ f θ') :
    ∀ X : ↥d.lieZero, IsRegularSS d.lieZero (X : d.ambient) → θ X = θ' X := by
  sorry

/-! ## (L6)–(L9) `m^Lie_geom` -/

/-- **(L6, L7) The germs `c_θ(X)` agree.**  For a quasi-character `θ` on `so(W) ⊕ so(V)` and
`X ∈ 𝔱⁰_♮` of a torus of `Γ^Lie(G,H)`, the germ of `θ ∘ ad` at `X` for the orbit `orbitChoiceLie X`
(`germLie` for `(G, 𝔤⁰, bilin)`) is Luo's `c_θ(ad X)` (`germLie` for `(Ḡ, 𝔤, B)` and the orbit
`orbitChoice`).  Ingredients: (L6) on `so(W) ⊕ so(V)`, `bilin = (k_W tr_W, k_V tr_V)` with
`k_W, k_V ∈ F^×` (one constant for each factor, so the scaling argument is applied to `so(W)` and
`so(V)` separately), and `ĵ_{aB}(O, ·) = ĵ_B(aO, ·)` with `aO = O` for regular nilpotent orbits, so
the germs do not depend on the choice of invariant form; `Z_G(X)(F) → Ḡ_X(F)` is onto, so the nilpotent
orbits of `𝔤⁰_X` are the same; (L7) `OrbitSpecAt` is Luo's and Waldspurger's recipe (`O_{ν₀}` on
`V'_X`, `O_{−ν₀}` on `W'_X`), with `ν₀ = q(z₀) = ν`.  Not proved here. -/
theorem cTheta_toSO (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) {θ : ↥d.luoOf.lie → ℂ}
    (hθ : IsLieQuasiCharacter d.luoOf.Gbar d.luoOf.lie d.luoOf.traceForm ψ θ)
    (T : d.GammaTorus) (X : CliffordAlgebra d.QW) (hX : d.IsGammaEltLie T.1 X) :
    d.germLie0 ψ (θ ∘ d.toSO) (d.diagLie X) (d.orbitChoiceLie X) =
      d.luoOf.cTheta ψ θ (d.toSOLin (d.diagLie X)) := by
  sorry

/-- The torus `T'` of Luo's `𝒯` is `H̄(F)`-conjugate to the image of `T ⊆ GSpin(W)(F)` under
`t ↦ (P(t), P(t) ⊕ 1)` (the natural correspondence of tori). -/
def IsNaturalTorusCorr (T : Subgroup ↥(GSpin d.QW)) (T' : Subgroup d.luoOf.Ambˣ) : Prop :=
  ∃ h ∈ d.luoOf.HbarU, T' = (T.map (d.toGbarU.comp d.diag)).map (MulAut.conj h).toMonoidHom

/-- **(L8) The index sets of `Γ^Lie` agree**: `P` maps the tori `T_x` of `GammaClass d` onto the
tori `H''_X` of Luo's `𝒯` (`T_x(F)/A_{G,H}(F) ≅ H''_X(F)`), compatibly with conjugacy (by
`GSpin(W)(F)`, resp. `H̄(F)`; `N ⊆ H̄` does not normalize a torus of `SO(W)` nontrivially), and
`|N_{GSpin(W)}(T)/Z_{GSpin(W)}(T)| = |N_{H̄}(T)/Z_{H̄}(T)|`: there is a bijection of classes
matching each torus with the conjugacy class of its image (`IsNaturalTorusCorr`).  Not proved here. -/
theorem gammaClass_equiv (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) :
    ∃ e : GammaClass d ≃ d.luoOf.GammaClass,
      (∀ c, d.IsNaturalTorusCorr (Quot.out c).1 (Quot.out (e c)).1) ∧
      ∀ c, weylCard d c = d.luoOf.weylCardOf (Quot.out (e c)).1 := by
  sorry

/-- **(L8) The torus integrals agree**, for a bijection of classes matching each torus with its
image (`IsNaturalTorusCorr`, as given by `gammaClass_equiv`) and the measures
`ν(T) dX`: on each torus, `ad` maps `𝔱⁰ = lieTorus T` onto Luo's `𝔱` (embedded diagonally), carries
`measLieTorus` (`exp`-compatible with the probability measure on `T(F)/A_{G,H}(F)`) to the
`exp`-compatible measure for the probability measure on `H''(F)`, `𝔱⁰_♮` (`IsGammaEltLie`) to `𝔱_♮`
(`IsNat`), `D^G` (`weylDiscLie` on `𝔤⁰` vs on `so(W) ⊕ so(V)`) and `Δ` to the same values, and (by
the hypothesis `hc`, i.e. `cTheta_toSO`) `c_θ` to `c_θ`; the representatives of the classes differ
by conjugation, which preserves the integrands and measures.  Not proved here. -/
theorem torusIntegralLie_toSO (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    (e : GammaClass d ≃ d.luoOf.GammaClass)
    (hen : ∀ c, d.IsNaturalTorusCorr (Quot.out c).1 (Quot.out (e c)).1) :
    ∃ μT : ∀ T : d.luoOf.GammaTorus, Measure ↥(d.luoOf.lieTorus T.1),
      (∀ T, d.luoOf.IsExpCompatT T.1 (μT T)) ∧
      ∀ θ : ↥d.luoOf.lie → ℂ,
        IsLieQuasiCharacter d.luoOf.Gbar d.luoOf.lie d.luoOf.traceForm ψ θ →
        (∀ (T : d.GammaTorus) (X : CliffordAlgebra d.QW), d.IsGammaEltLie T.1 X →
          d.germLie0 ψ (θ ∘ d.toSO) (d.diagLie X) (d.orbitChoiceLie X) =
            d.luoOf.cTheta ψ θ (d.toSOLin (d.diagLie X))) →
        ∀ (c : GammaClass d) (s : ℝ), 0 < s →
          d.torusIntegralLie ψ (θ ∘ d.toSO) (Quot.out c).1 s =
            ∫ X : ↥(d.luoOf.lieTorus (Quot.out (e c)).1),
              d.luoOf.gammaIntegrand ψ θ (Quot.out (e c)).1 s X ∂μT (Quot.out (e c)) := by
  sorry

/-- **(L9) `m^Lie_geom(θ)` depends only on `θ|_{𝔤⁰_reg}`** (the Lie-algebra form of
`mGeomS_congr_regularSet`): the germs `c_{θ,O}(X)` only see `θ` at `X + Y` with `Y ∈ 𝔤⁰_X` small
and regular in `𝔤⁰_X`, and such `X + Y` are regular in `𝔤⁰`.  Not proved here. -/
theorem mGeomLie_congr_regularSet {θ θ' : ↥d.lieZero → ℂ}
    (he : ∀ X : ↥d.lieZero, IsRegularSS d.lieZero (X : d.ambient) → θ X = θ' X) :
    d.mGeomLie ψ θ = d.mGeomLie ψ θ' := by
  sorry

/-- `m^Lie_{geom,s}` agrees with Luo's, for `s > 0`, from `gammaClass_equiv` and
`torusIntegralLie_toSO`. -/
theorem mGeomLieS_toSO (e : GammaClass d ≃ d.luoOf.GammaClass)
    (he : ∀ c, weylCard d c = d.luoOf.weylCardOf (Quot.out (e c)).1)
    (μT : ∀ T : d.luoOf.GammaTorus, Measure ↥(d.luoOf.lieTorus T.1)) {θ : ↥d.luoOf.lie → ℂ}
    (hT : ∀ (c : GammaClass d) (s : ℝ), 0 < s →
      d.torusIntegralLie ψ (θ ∘ d.toSO) (Quot.out c).1 s =
        ∫ X : ↥(d.luoOf.lieTorus (Quot.out (e c)).1),
          d.luoOf.gammaIntegrand ψ θ (Quot.out (e c)).1 s X ∂μT (Quot.out (e c)))
    {s : ℝ} (hs : 0 < s) :
    d.mGeomLieS ψ (θ ∘ d.toSO) s = d.luoOf.mGeomLieS ψ μT θ s := by
  unfold mGeomLieS LuoDatum.mGeomLieS
  rw [← e.tsum_eq]
  refine tsum_congr fun c => ?_
  rw [he c, hT c s hs]

/-! ## `J^Lie = m^Lie_geom(θ_f)` on `𝔤⁰` -/

/-- **Thesis Thm 12.2.2 on `𝔤⁰`: `J^Lie(f) = m^Lie_geom(θ_f)`** for `f ∈ S_scusp(𝔤⁰(F))`, when
neither `W` nor `V` is a hyperbolic plane: Luo Thm 7.3.3 for the special orthogonal triple
(`luo_lie_geomExpansion_SO`), transported by (L1)–(L9). -/
theorem distribJLie_eq_mGeomLie_of_luo (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    {f : ↥d.lieZero → ℂ} (hf : d.IsLieScusp f) :
    d.distribJLie ψ f = d.mGeomLie ψ (d.thetaFLie ψ f) := by
  have := d.muG_isHaarMeasure hW hV
  obtain ⟨μH, μ𝔥, m, hμH, h𝔥, hm, hJ⟩ :=
    d.exists_JLie_transfer ψ hW hV
  obtain ⟨e, hen, he⟩ := d.gammaClass_equiv hW hV
  obtain ⟨μT, hμT, hT⟩ := d.torusIntegralLie_toSO ψ hW hV e hen
  obtain ⟨θ, ⟨h1, h2, h3⟩, hqc, hlim⟩ :=
    luo_lie_geomExpansion_SO d.luoOf hW hV ψ d.muG μH μ𝔥 h𝔥 m hm μT hμT
      (f ∘ d.toSO.symm) (d.isScusp_toSO hf)
  have hθ : d.IsThetaFLie ψ f (θ ∘ d.toSO) := d.isThetaFLie_of_SO ψ hW hV hf h1 h2 h3
  have hreg := d.isThetaFLie_eqOn_regular ψ
    (d.isThetaFLie_thetaFLie_of_exists ψ ⟨_, hθ⟩) hθ
  rw [d.mGeomLie_congr_regularSet ψ hreg, hJ f hf]
  have hc := fun T X hX => d.cTheta_toSO ψ hW hV hqc T X hX
  have hev : d.luoOf.mGeomLieS ψ μT θ =ᶠ[𝓝[>] (0 : ℝ)] d.mGeomLieS ψ (θ ∘ d.toSO) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (d.mGeomLieS_toSO ψ e he μT (hT θ hqc hc) hs).symm
  exact ((hlim.congr' hev).limUnder_eq).symm

end GGPData

end GSpinGGP
