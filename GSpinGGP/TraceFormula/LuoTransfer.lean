/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LieAlgebra
import GSpinGGP.GGP.MovedCentralizer
import GSpinGGP.Literature.Luo
import GSpinGGP.Literature.Fourier
import GSpinGGP.TraceFormula.SelfDual

/-!
# From the special orthogonal triple to `𝔤⁰`: `J^Lie = m^Lie_geom(θ_f)`

The literature axiom `luo_lie_geomExpansion_SO` is about the special orthogonal triple
`(Ḡ, H̄, ξ)` of an admissible pair, with objects defined on the quadratic spaces
(`TraceFormula/SOLie.lean`).  This file identifies them with the objects on
`𝔤⁰ = so(W) ⊕ so(V) ⊆ C(W) × C(V)` of the general spin triple (`TraceFormula/LieAlgebra.lean`)
when neither `W` nor `V` is a hyperbolic plane, and deduces
`distribJLie_eq_mGeomLie_of_luo`: `J^Lie(f) = m^Lie_geom(θ_f)` for `f ∈ S_scusp(𝔤⁰(F))` (Thesis
Thm 12.2.2 on `𝔤⁰`).

The identification is own work, stated step by step (most steps are `sorry` here):
* (L1) `toSO`: `X ↦ (ad_W X_W, ad_V X_V)` maps `𝔤⁰` onto `so(W) ⊕ so(V)` (`toSO_mem` is proved;
  `toSO_bijective` and the transfer of strong cuspidality `isScusp_toSO` are proved);
* (L2) `luoOf`: the admissible pair of `d` with Luo's basis `z^L_i = ν^{-i} z_i`,
  `z^L_{-i} = ν^{i-1} z_{-i}` (`i ≥ 1`), `z^L_0 = z_0` (`luoOf_gram` proved), and `λ` agrees
  (`lam_toSO`);
* (L3) `muG`: the push-forward of `Measure.haar` on `G(F)/A_G(F)` to `Ḡ(F)`, a Haar measure
  (`muG_isHaarMeasure`, proved);
* (L4) `exists_JLie_transfer`: `J^Lie` of `d` is Luo's `J^Lie` for compatible measures;
* (L5) `isThetaFLie_of_SO`: a `θ` representing the orbital pairing on `so(W) ⊕ so(V)` gives one on
  `𝔤⁰`;
* `isThetaFLie_eqOn_regular`: `θ_f` is unique on `𝔤⁰_reg`;
* (L6, L7) `cTheta_toSO`: the germs `c_{θ,O_X}(X)` agree (trace form vs `bilin`, `Z_G(X)` vs
  `Ḡ_X`, the orbit choice `orbitChoiceLie` vs Luo's and Waldspurger's `O_{±ν₀}`);
* (L8) `gammaClass_equiv`, `torusIntegralLie_toSO`: `Γ^Lie` (tori, `|W(H,T)|`, `ν(T) dX`,
  `D^G`, `Δ`, `𝔱_♮`) agree; `mGeomLieS_toSO` is proved from them;
* (L9) `mGeomLie_congr_regularSet` (proved): `m^Lie_geom(θ)` depends only on `θ|_{𝔤⁰_reg}`.
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
so(V)`): `adV` is injective on the traceless part (its kernel on `gspin` is the scalars) and maps
it onto `so` (`exists_mem_gspin_adV_eq`, after subtracting the trace part). -/
theorem toSO_bijective : Function.Bijective d.toSOFun := by
  -- `adV` is injective on the traceless part: its kernel on `gspin` is the scalars, and a traceless
  -- scalar is `0`.
  have hinj : ∀ {U : Type} [AddCommGroup U] [Module F U] [Module.Finite F U]
      {Q : QuadraticForm F U}, IsNondeg Q → ∀ {X : CliffordAlgebra Q}, X ∈ soSub Q →
      adV Q X = 0 → X = 0 := by
    intro U _ _ _ Q hQ X hX h0
    obtain ⟨r, rfl⟩ := eq_algebraMap_of_adV_eq_zero hQ hX.1 h0
    have h2 := (mem_soSub.mp hX).2
    rw [Algebra.algebraMap_eq_smul_one, cliffTrace_smul, cliffTrace_one] at h2
    have hr : r = 0 :=
      (mul_eq_zero.mp h2).resolve_right (cast_finrank_cliffordAlgebra_ne_zero Q)
    rw [hr, map_zero]
  -- `adV` maps the traceless part onto `so`: lift to `gspin` and subtract the trace part.
  have hsurj : ∀ {U : Type} [AddCommGroup U] [Module F U] [Module.Finite F U]
      {Q : QuadraticForm F U}, IsNondeg Q → ∀ M : Module.End F U,
      M ∈ skewAdjointLieSubalgebra (bform Q) → ∃ Y ∈ soSub Q, adV Q Y = M := by
    intro U _ _ _ Q hQ M hM
    have hMs : ∀ u w, bform Q (M u) w = -bform Q u (M w) := by
      have h := (LinearMap.mem_skewAdjointSubmodule (B := bform Q) (f := M)).mp hM
      intro u w
      have := h u w
      simpa using this
    obtain ⟨Y, hYg, hY⟩ := exists_mem_gspin_adV_eq hQ M hMs
    set n : F := (Module.finrank F (CliffordAlgebra Q) : F)
    have hn : n ≠ 0 := cast_finrank_cliffordAlgebra_ne_zero Q
    set c : F := cliffTrace Q Y / n
    refine ⟨Y - c • 1, ⟨sub_mem hYg ((gspin Q).smul_mem c (one_mem_gspin Q)), ?_⟩, ?_⟩
    · rw [sub_eq_add_neg, cliffTrace_add, ← neg_smul, cliffTrace_smul, cliffTrace_one]
      change cliffTrace Q Y + -(cliffTrace Q Y / n) * n = 0
      field_simp
      ring
    · rw [map_sub, hY, ← Algebra.algebraMap_eq_smul_one, adV_algebraMap, sub_zero]
  constructor
  · intro X Y hXY
    have h := congrArg Subtype.val hXY
    change d.toSOLin (X : d.ambient) = d.toSOLin (Y : d.ambient) at h
    have hZ : ((X : d.ambient) - (Y : d.ambient)) ∈ d.lieZero := sub_mem X.2 Y.2
    have h0 : d.toSOLin ((X : d.ambient) - (Y : d.ambient)) = 0 := by rw [map_sub, h, sub_self]
    have h1 : adV d.QW ((X : d.ambient) - (Y : d.ambient)).1 = 0 := congrArg Prod.fst h0
    have h2 : adV d.QV ((X : d.ambient) - (Y : d.ambient)).2 = 0 := congrArg Prod.snd h0
    have e1 := hinj d.nondeg hZ.1 h1
    have e2 := hinj d.nondeg_QV hZ.2 h2
    exact Subtype.ext (sub_eq_zero.mp (Prod.ext e1 e2))
  · intro M
    obtain ⟨Y₁, hY₁, e₁⟩ := hsurj d.nondeg (d.luoOf.fstA (M : d.luoOf.Amb)) M.2.1
    obtain ⟨Y₂, hY₂, e₂⟩ := hsurj d.nondeg_QV (d.luoOf.sndA (M : d.luoOf.Amb)) M.2.2
    exact ⟨⟨(Y₁, Y₂), hY₁, hY₂⟩, Subtype.ext (Prod.ext e₁ e₂)⟩

/-- `ad : 𝔤⁰ → so(W) ⊕ so(V)` as a linear map. -/
def toSOLinRestr : ↥d.lieZero →ₗ[F] ↥d.luoOf.lie :=
  LinearMap.codRestrict d.luoOf.lie.toSubmodule (d.toSOLin ∘ₗ d.lieZero.toSubmodule.subtype)
    d.toSO_mem

/-- `ad : 𝔤⁰ ≃ so(W) ⊕ so(V)` as a linear equivalence (`toSO_bijective`). -/
def toSOLinEquiv : ↥d.lieZero ≃ₗ[F] ↥d.luoOf.lie :=
  LinearEquiv.ofBijective d.toSOLinRestr d.toSO_bijective

/-- `𝔤⁰ ≃ so(W) ⊕ so(V)`. -/
def toSO : ↥d.lieZero ≃ ↥d.luoOf.lie := d.toSOLinEquiv.toEquiv

/-- `(toSO X : End W × End V) = toSOLin X`. -/
@[simp] theorem coe_toSO (X : ↥d.lieZero) : (d.toSO X : d.luoOf.Amb) = d.toSOLin X := rfl

theorem toSOLin_toSO_symm (Y : ↥d.luoOf.lie) : d.toSOLin (d.toSO.symm Y : d.ambient) = Y :=
  congrArg Subtype.val (d.toSO.apply_symm_apply Y)

/-- `ad : 𝔤⁰ ≃ so(W) ⊕ so(V)` is a homeomorphism (finite dimension). -/
def toSOCLE : ↥d.lieZero ≃L[F] ↥d.luoOf.lie :=
  haveI := t2Space_of_moduleTopology F d.ambient
  haveI := isTopologicalRing_of_moduleTopology F d.ambient
  haveI := IsModuleTopology.toContinuousSMul F d.ambient
  haveI := t2Space_of_moduleTopology F d.luoOf.Amb
  haveI := isTopologicalRing_of_moduleTopology F d.luoOf.Amb
  haveI := IsModuleTopology.toContinuousSMul F d.luoOf.Amb
  haveI : ContinuousSMul F ↥d.lieZero := inferInstanceAs (ContinuousSMul F ↥d.lieZero.toSubmodule)
  haveI : IsTopologicalAddGroup ↥d.lieZero :=
    inferInstanceAs (IsTopologicalAddGroup ↥d.lieZero.toSubmodule)
  haveI : ContinuousSMul F ↥d.luoOf.lie :=
    inferInstanceAs (ContinuousSMul F ↥d.luoOf.lie.toSubmodule)
  haveI : IsTopologicalAddGroup ↥d.luoOf.lie :=
    inferInstanceAs (IsTopologicalAddGroup ↥d.luoOf.lie.toSubmodule)
  d.toSOLinEquiv.toContinuousLinearEquiv

theorem coe_toSOCLE_symm : ⇑d.toSOCLE.symm = ⇑d.toSO.symm := rfl

/-- `ad` carries `𝔭⁰` onto `𝔭`: the conditions on `X_W`, `X_V` are conditions on `ad X_W`,
`ad X_V`. -/
theorem mem_liePar_iff (X : ↥d.lieZero) {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV} :
    (X : d.ambient) ∈ d.liePar FW FV ↔ d.toSOLin X ∈ d.luoOf.liePar FW FV :=
  ⟨fun h => ⟨d.toSO_mem X, h.2.1.2, h.2.2.2⟩, fun h => ⟨X.2, ⟨X.2.1, h.2.1⟩, ⟨X.2.2, h.2.2⟩⟩⟩

/-- `ad` carries `𝔲 = Lie(U_P)` of `𝔤⁰` onto that of `so(W) ⊕ so(V)`. -/
theorem mem_lieUnip_iff (X : ↥d.lieZero) {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV} :
    (X : d.ambient) ∈ d.lieUnip FW FV ↔ d.toSOLin X ∈ d.luoOf.lieUnip FW FV :=
  ⟨fun h => ⟨d.toSO_mem X, h.2.1.2, h.2.2.2⟩, fun h => ⟨X.2, ⟨X.2.1, h.2.1⟩, ⟨X.2.2, h.2.2⟩⟩⟩

/-- `ad : 𝔲 ≃ 𝔲` between the nilpotent radicals of `𝔭⁰` and `𝔭`. -/
def toSOUnip (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) :
    ↥(d.lieUnip FW FV) ≃ₗ[F] ↥(d.luoOf.lieUnip FW FV) where
  toFun N := ⟨d.toSOLin (N : d.ambient),
    (d.mem_lieUnip_iff ⟨N, d.lieUnip_le_lie0 FW FV N.2⟩).mp N.2⟩
  invFun N := ⟨(d.toSO.symm ⟨N, d.luoOf.lieUnip_le_lie FW FV N.2⟩ : d.ambient),
    (d.mem_lieUnip_iff _).mpr (by rw [d.toSOLin_toSO_symm]; exact N.2)⟩
  map_add' N N' := Subtype.ext (map_add d.toSOLin (N : d.ambient) N')
  map_smul' c N := Subtype.ext (map_smul d.toSOLin c (N : d.ambient))
  left_inv N := Subtype.ext (by
    exact congrArg (fun Y : ↥d.lieZero => (Y : d.ambient))
      (d.toSO.symm_apply_apply ⟨(N : d.ambient), d.lieUnip_le_lie0 FW FV N.2⟩))
  right_inv N := Subtype.ext (d.toSOLin_toSO_symm _)

/-- `toSOUnip` is a homeomorphism (finite dimension). -/
def toSOUnipCLE (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) :
    ↥(d.lieUnip FW FV) ≃L[F] ↥(d.luoOf.lieUnip FW FV) :=
  haveI := t2Space_of_moduleTopology F d.ambient
  haveI := isTopologicalRing_of_moduleTopology F d.ambient
  haveI := IsModuleTopology.toContinuousSMul F d.ambient
  haveI := t2Space_of_moduleTopology F d.luoOf.Amb
  haveI := isTopologicalRing_of_moduleTopology F d.luoOf.Amb
  haveI := IsModuleTopology.toContinuousSMul F d.luoOf.Amb
  (d.toSOUnip FW FV).toContinuousLinearEquiv

/-- A proper parabolic of `Ḡ` (some element of `Ḡ(F)` moves the flag pair) gives a proper
parabolic of `G` (lift that element through `G(F) → Ḡ(F)`, `Pbar_surjective`). -/
theorem isProperFlagPair_of_luoOf {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV}
    (h : d.luoOf.IsProperFlagPair FW FV) : d.IsProperFlagPair FW FV := by
  obtain ⟨g, hg, hn⟩ := h
  intro htop
  obtain ⟨x, hx⟩ := d.Pbar_surjective (⟨_, hg.1⟩, ⟨_, hg.2⟩)
  have hxB : x ∈ d.whittB FW FV := htop ▸ Subgroup.mem_top x
  have e1 : ((specP d.QW (d.fst x) : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) :
      (Fin d.m → F) →ₗ[F] (Fin d.m → F)) =
      d.luoOf.fstA (g : d.luoOf.Amb) := by
    rw [← d.Pbar_fst, hx]; rfl
  have e2 : ((specP d.QV (d.snd x) : d.V ≃ₗ[F] d.V) : d.V →ₗ[F] d.V) =
      d.luoOf.sndA (g : d.luoOf.Amb) := by
    rw [← d.Pbar_snd, hx]; rfl
  refine hn ⟨fun i => ?_, fun i => ?_⟩
  · rw [← e1]; exact (hxB.1 i).le
  · rw [← e2]; exact (hxB.2 i).le

/-- **(L1) Strong cuspidality is transported** (`IsLieScusp` on `𝔤⁰` to `IsScusp` on
`so(W) ⊕ so(V)`): `ad` is a homeomorphism (`toSOCLE`) carrying the flag parabolics `𝔭⁰ = liePar`
and their radicals `lieUnip` to those of `Ḡ` (`mem_liePar_iff`, `mem_lieUnip_iff`), properness of a
flag pair for `Ḡ` gives properness for `G` (through the surjection `G(F) → Ḡ(F)`,
`isProperFlagPair_of_luoOf`), and a Haar measure on `𝔲(F)` of `Ḡ` pulls back along `ad` to a Haar
measure on `𝔲(F)` of `G`. -/
theorem isScusp_toSO {f : ↥d.lieZero → ℂ} (hf : d.IsLieScusp f) :
    d.luoOf.IsScusp (f ∘ d.toSO.symm) := by
  have := t2Space_of_moduleTopology F d.ambient
  have := isTopologicalRing_of_moduleTopology F d.ambient
  have := isTopologicalRing_of_moduleTopology F d.luoOf.Amb
  refine ⟨?_, ?_⟩
  · rw [← coe_toSOCLE_symm]
    exact ⟨hf.1.1.comp_continuous d.toSOCLE.symm.continuous,
      hf.1.2.comp_homeomorph d.toSOCLE.symm.toHomeomorph⟩
  intro (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) hP X hX μ hμ
  let : MeasurableSpace ↥(d.luoOf.lieUnip FW FV) := d.luoOf.instMeasurableSpaceLieUnip FW FV
  have : BorelSpace ↥(d.lieUnip FW FV) := ⟨rfl⟩
  have : BorelSpace ↥(d.luoOf.lieUnip FW FV) := ⟨rfl⟩
  set X' : ↥d.lieZero := d.toSO.symm X with hX'def
  have hX' : (X' : d.ambient) ∈ d.liePar FW FV :=
    (d.mem_liePar_iff X').mpr (by rw [hX'def, d.toSOLin_toSO_symm]; exact hX)
  set e := d.toSOUnipCLE FW FV
  set em : ↥(d.luoOf.lieUnip FW FV) ≃ᵐ ↥(d.lieUnip FW FV) := e.symm.toHomeomorph.toMeasurableEquiv
  have : (μ.map em).IsAddHaarMeasure := e.symm.isAddHaarMeasure_map μ
  obtain ⟨hint, h0⟩ := hf.2 FW FV (d.isProperFlagPair_of_luoOf hP) X' hX' (μ.map em) inferInstance
  have key : (fun N : ↥(d.luoOf.lieUnip FW FV) =>
      (f ∘ d.toSO.symm) ⟨(X : d.luoOf.Amb) + N, d.luoOf.lie.add_mem X.2
        (d.luoOf.lieUnip_le_lie FW FV N.2)⟩) =
      (fun N' : ↥(d.lieUnip FW FV) =>
        f ⟨(X' : d.ambient) + N', d.lie0.add_mem X'.2 (d.lieUnip_le_lie0 FW FV N'.2)⟩) ∘ em := by
    funext N
    simp only [Function.comp_apply]
    congr 1
    have hN : d.toSOLin ((em N : ↥(d.lieUnip FW FV)) : d.ambient) = N :=
      d.toSOLin_toSO_symm ⟨N, d.luoOf.lieUnip_le_lie FW FV N.2⟩
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    change (X : d.luoOf.Amb) + N = d.toSOLin ((X' : d.ambient) + (em N : d.ambient))
    rw [map_add, hN, hX'def, d.toSOLin_toSO_symm]
  refine ⟨?_, ?_⟩
  · rw [key]; exact (integrable_map_equiv em _).mp hint
  · rw [key]; exact (integral_map_equiv em _).symm.trans h0

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

/-- The underlying pair of endomorphisms of `toGbarU g`. -/
theorem toGbarU_val (g : ↥d.G) : ((d.toGbarU g : d.luoOf.Ambˣ) : d.luoOf.Amb) =
    d.luoOf.pair (specP d.QW (d.fst g)).toLinearMap (specP d.QV (d.snd g)).toLinearMap := rfl

theorem continuous_toGbarU_val :
    Continuous fun g : ↥d.G => ((d.toGbarU g : d.luoOf.Ambˣ) : d.luoOf.Amb) := by
  let ℓ : (Module.End F d.luoOf.W × Module.End F d.luoOf.V) →ₗ[F] d.luoOf.Amb := LinearMap.id
  have hl : Continuous ℓ := IsModuleTopology.continuous_of_linearMap ℓ
  exact hl.comp ((continuous_specP_toEnd d.continuous_fst).prodMk
    (continuous_specP_toEnd d.continuous_snd))

/-- `G(F) → Ḡ(F)` is continuous. -/
theorem continuous_toGbar : Continuous d.toGbar := by
  apply continuous_induced_rng.2
  show Continuous fun g => d.toGbarU g
  rw [Units.continuous_iff]
  refine ⟨d.continuous_toGbarU_val, ?_⟩
  have : (fun g : ↥d.G => (((d.toGbarU g)⁻¹ : d.luoOf.Ambˣ) : d.luoOf.Amb)) =
      (fun g : ↥d.G => ((d.toGbarU g : d.luoOf.Ambˣ) : d.luoOf.Amb)) ∘ (fun g => g⁻¹) := by
    funext g; simp [map_inv]
  rw [this]
  exact d.continuous_toGbarU_val.comp continuous_inv

/-- **The Haar measure on `Ḡ(F)`**: the push-forward of `Measure.haar` on `G(F)/A_G(F)` along
`G(F)/A_G(F) → Ḡ(F)` (an isomorphism of topological groups when neither `W` nor `V` is a hyperbolic
plane: `AGbar_eq_bot` and Hilbert 90, `Pbar_surjective`). -/
def muG : Measure ↥d.luoOf.Gbar :=
  Measure.map (fun x : d.GmodAG => d.toGbar (Quotient.out x)) Measure.haar

/-- **`G(F)/A_G(F) ≃ Ḡ(F)` as topological groups**, by `x ↦ toGbar (out x)`, when neither `W` nor
`V` is a hyperbolic plane: `toGbar` descends to a continuous bijective homomorphism (its kernel is
`A_G`: `AGbar_eq_bot`, `exists_scalarPair_of_specP_eq`; onto by `Pbar_surjective`), open by the
open mapping theorem for locally compact σ-compact groups (`Ḡ(F)` is closed, `isClosed_Gbar`). -/
theorem exists_continuousMulEquiv_toGbar (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) :
    ∃ e : d.GmodAG ≃ₜ* ↥d.luoOf.Gbar, ⇑e = fun x : d.GmodAG => d.toGbar (Quotient.out x) := by
  have hPbar : ∀ g, d.Pbar g = 1 → d.toGbar g = 1 := by
    intro g hg
    apply Subtype.ext
    change d.toGbarU g = 1
    apply Units.ext
    have h1 : specP d.QW (d.fst g) = 1 :=
      congrArg (fun p : d.GbarGrp => (p.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))) hg
    have h2 : specP d.QV (d.snd g) = 1 := congrArg (fun p : d.GbarGrp => (p.2 : d.V ≃ₗ[F] d.V)) hg
    rw [toGbarU_val, h1, h2]
    rfl
  have hker : d.AG ≤ d.toGbar.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    apply hPbar
    have hm : d.Pbar g ∈ d.AGbar := ⟨g, hg, rfl⟩
    rw [d.AGbar_eq_bot hW hV] at hm
    exact hm
  let φ : d.GmodAG →* ↥d.luoOf.Gbar := QuotientGroup.lift d.AG d.toGbar hker
  have hφ : (fun x : d.GmodAG => d.toGbar (Quotient.out x)) = φ := by
    funext x
    conv_rhs => rw [← QuotientGroup.out_eq' x]
    rfl
  have hcont : Continuous φ :=
    (QuotientGroup.isQuotientMap_mk d.AG).continuous_iff.mpr d.continuous_toGbar
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    induction x using QuotientGroup.induction_on with | H g => ?_
    have h1 : d.toGbar g = 1 := hx
    have hv := congrArg (fun u : ↥d.luoOf.Gbar => ((u : d.luoOf.Ambˣ) : d.luoOf.Amb)) h1
    simp only [OneMemClass.coe_one, Units.val_one] at hv
    have e1 : specP d.QW (d.fst g) = specP d.QW (d.fst 1) := by
      rw [map_one, map_one]
      exact LinearEquiv.toLinearMap_injective (congrArg Prod.fst hv)
    have e2 : specP d.QV (d.snd g) = specP d.QV (d.snd 1) := by
      rw [map_one, map_one]
      exact LinearEquiv.toLinearMap_injective (congrArg Prod.snd hv)
    obtain ⟨c₁, c₂, hc⟩ := d.exists_scalarPair_of_specP_eq e1 e2
    rw [QuotientGroup.eq_one_iff, hc, one_mul]
    exact d.scalarPair_mem_AG c₁ c₂
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨g, hg⟩ := d.Pbar_surjective
      (⟨LinearMap.GeneralLinearGroup.generalLinearEquiv F _ (d.luoOf.unitFst (y : d.luoOf.Ambˣ)),
          y.2.1⟩,
       ⟨LinearMap.GeneralLinearGroup.generalLinearEquiv F _ (d.luoOf.unitSnd (y : d.luoOf.Ambˣ)),
          y.2.2⟩)
    refine ⟨QuotientGroup.mk g, ?_⟩
    apply Subtype.ext
    apply Units.ext
    show d.luoOf.pair _ _ = _
    rw [MonoidHom.comp_apply, hg]
    rfl
  have hopen : IsOpenMap φ := φ.isOpenMap_of_sigmaCompact hsurj hcont
  let e : d.GmodAG ≃* ↥d.luoOf.Gbar := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
  let h : d.GmodAG ≃ₜ ↥d.luoOf.Gbar := e.toEquiv.toHomeomorphOfContinuousOpen hcont hopen
  exact ⟨{ e with continuous_toFun := hcont, continuous_invFun := h.symm.continuous }, hφ.symm⟩

/-- **(L3) `muG` is a Haar measure on `Ḡ(F)`**: `G(F)/A_G(F) → Ḡ(F)` is a bijective continuous
homomorphism of locally compact, σ-compact groups (`AGbar_eq_bot`, `Pbar_surjective`), hence a
homeomorphism (open mapping theorem; `Ḡ(F)` is locally compact, `isClosed_Gbar`), and the
push-forward of a Haar measure by an isomorphism of topological groups is a Haar measure.
Injectivity: the kernel of `P` is the central `G_m × G_m ⊆ A_G`
(`exists_scalarPair_of_specP_eq`). -/
theorem muG_isHaarMeasure (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) :
    d.muG.IsHaarMeasure := by
  obtain ⟨e, he⟩ := d.exists_continuousMulEquiv_toGbar hW hV
  unfold muG
  rw [← he]
  exact e.toMulEquiv.isHaarMeasure_map Measure.haar e.continuous e.symm.continuous

/-! ## (L4) `J^Lie` -/

variable (ψ : NontrivialAddChar F)

/-- **(L4) `J^Lie` of `d` is Luo's `J^Lie`** for `muG`, a Haar measure `μH` on `H̄(F)`, the
`exp`-compatible `μ_𝔥` and the quotient measure: `H(F)/A_{G,H}(F) ≃ H̄(F)` (Hilbert 90 and
`ker P ∩ H = A_{G,H}`, through `quotHG_equiv_SO`), `ad : 𝔥⁰ ≃ 𝔥 = so(W) ⊕ 𝔫`, `λ` (`lam_toSO`),
`measH0` and `weilMeasureHG` push forward to an `exp`-compatible pair and its Weil
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

/-- `b(X, Z) = 0` for `X ∈ 𝔤⁰` and `Z` in the centre `𝔷 = F(1,0) ⊕ F(0,1)`:
`b(X, (1,0)) = tr(L_{X_W})` and `b(X, (0,1)) = tr(L_{X_V})`, which vanish on the traceless part. -/
theorem bilin_lie0_lieCenter {X Z : d.ambient} (hX : X ∈ d.lie0) (hZ : Z ∈ d.lieCenter) :
    d.bilin X Z = 0 := by
  rw [lieCenter, Submodule.mem_span_pair] at hZ
  obtain ⟨a, b, rfl⟩ := hZ
  have h1 : d.bilin X ((1 : CliffordAlgebra d.QW), (0 : CliffordAlgebra d.QV)) = 0 := by
    rw [bilin_apply, trace_mulLeft_prod]
    have e1 := (mem_soSub.mp hX.1).2
    unfold cliffTrace at e1
    simp [e1]
  have h2 : d.bilin X ((0 : CliffordAlgebra d.QW), (1 : CliffordAlgebra d.QV)) = 0 := by
    rw [bilin_apply, trace_mulLeft_prod]
    have e2 := (mem_soSub.mp hX.2).2
    unfold cliffTrace at e2
    simp [e2]
  rw [map_add, map_smul, map_smul, h1, h2, smul_zero, smul_zero, add_zero]

/-- **The trace form is nondegenerate on `𝔤⁰`** (Thesis §2.4): `𝔤 = 𝔷 ⊕ 𝔤⁰` with `𝔷 ⊥ 𝔤⁰`, and the
form is nondegenerate on `𝔤` (`bilin_nondegenerate_lie`). -/
theorem restrictForm_lieZero_nondegenerate :
    (restrictForm d.lieZero d.bilin).Nondegenerate := by
  have hL : ∀ X : ↥d.lieZero, (∀ Y : ↥d.lieZero, restrictForm d.lieZero d.bilin X Y = 0) →
      X = 0 := by
    intro X hX
    refine Subtype.ext (d.bilin_nondegenerate_lie X (d.lieZero_le_lie X.2) fun Y hY => ?_)
    have hY' : Y ∈ d.lieCenter ⊔ d.lie0 := by rw [← lie_eq_center_sup_lie0]; exact hY
    obtain ⟨Z, hZ, Y₀, hY₀, rfl⟩ := Submodule.mem_sup.mp hY'
    rw [map_add, d.bilin_lie0_lieCenter X.2 hZ, zero_add]
    exact hX ⟨Y₀, hY₀⟩
  refine ⟨hL, fun Y hY => hL Y fun X => ?_⟩
  have := hY X
  simp only [restrictForm, LinearMap.compl₁₂_apply] at this ⊢
  rw [ggp_bilin_symm]; exact this

/-- A self-dual measure exists on `𝔤⁰` (from the existence of self-dual Haar measures, for the
nondegenerate trace form). -/
theorem exists_isSelfDual_lieZero : ∃ μ, IsSelfDual μ (restrictForm d.lieZero d.bilin) ψ := by
  have := t2Space_of_moduleTopology F d.ambient
  exact exists_isSelfDual_of_isInducing d.lieZero.incl.toLinearMap IsInducing.subtypeVal
    Subtype.val_injective _ d.restrictForm_lieZero_nondegenerate ψ

/-- `measLie0` is a Haar measure on `𝔤⁰` (not the junk value `0`). -/
theorem isAddHaarMeasure_measLie0 : (d.measLie0 ψ).IsAddHaarMeasure :=
  selfDualMeasure_isAddHaar (d.exists_isSelfDual_lieZero ψ)

/-- The centre `𝔷 = F(1,0) ⊕ F(0,1)` commutes with everything in `C(W) × C(V)`. -/
theorem commute_of_mem_lieCenter {Z : d.ambient} (hZ : Z ∈ d.lieCenter) (Y : d.ambient) :
    Z * Y = Y * Z := by
  rw [lieCenter, Submodule.mem_span_pair] at hZ
  obtain ⟨a, b, rfl⟩ := hZ
  refine Prod.ext ?_ ?_ <;> simp [Algebra.smul_def, Algebra.commutes]

/-- `X` is regular semisimple for `𝔤⁰` iff it is for `𝔤 = 𝔷 ⊕ 𝔤⁰`: the centralizer of `X` in `𝔤`
is `𝔷` plus its centralizer in `𝔤⁰`, and `𝔷` is central. -/
theorem isRegularSS_lieZero_iff {X : d.ambient} :
    IsRegularSS d.lieZero X ↔ IsRegularSS d.lie X := by
  unfold IsRegularSS
  refine and_congr_right fun _ => ?_
  rw [isLieAbelian_iff_forall_commute, isLieAbelian_iff_forall_commute]
  constructor
  · intro h Y₁ h₁ Y₂ h₂
    rw [mem_lieCentralizer] at h₁ h₂
    have d₁ : Y₁ ∈ d.lieCenter ⊔ d.lie0 := by rw [← lie_eq_center_sup_lie0]; exact h₁.1
    have d₂ : Y₂ ∈ d.lieCenter ⊔ d.lie0 := by rw [← lie_eq_center_sup_lie0]; exact h₂.1
    obtain ⟨Z₁, hZ₁, A₁, hA₁, rfl⟩ := Submodule.mem_sup.mp d₁
    obtain ⟨Z₂, hZ₂, A₂, hA₂, rfl⟩ := Submodule.mem_sup.mp d₂
    have c₁ : X * A₁ = A₁ * X := by
      have := h₁.2
      rw [mul_add, add_mul, ← d.commute_of_mem_lieCenter hZ₁ X] at this
      exact add_left_cancel this
    have c₂ : X * A₂ = A₂ * X := by
      have := h₂.2
      rw [mul_add, add_mul, ← d.commute_of_mem_lieCenter hZ₂ X] at this
      exact add_left_cancel this
    have hA : A₁ * A₂ = A₂ * A₁ :=
      h A₁ (mem_lieCentralizer.mpr ⟨hA₁, c₁⟩) A₂ (mem_lieCentralizer.mpr ⟨hA₂, c₂⟩)
    rw [add_mul, mul_add, mul_add, add_mul, mul_add, mul_add, hA,
      d.commute_of_mem_lieCenter hZ₁ Z₂, d.commute_of_mem_lieCenter hZ₁ A₂,
      ← d.commute_of_mem_lieCenter hZ₂ A₁]
    abel
  · intro h Y₁ h₁ Y₂ h₂
    rw [mem_lieCentralizer] at h₁ h₂
    exact h Y₁ (mem_lieCentralizer.mpr ⟨d.lieZero_le_lie h₁.1, h₁.2⟩) Y₂
      (mem_lieCentralizer.mpr ⟨d.lieZero_le_lie h₂.1, h₂.2⟩)

/-- **The regular semisimple set of `𝔤⁰` is open**: it is the preimage, under the inclusion
`𝔤⁰ ⊆ 𝔤`, of the regular semisimple set of `𝔤 = 𝔤_1` (`isOpen_setOf_isRegularSS_lieCentralizer`
at `g = 1`). -/
theorem isOpen_setOf_isRegularSS_lieZero :
    IsOpen {X : ↥d.lieZero | IsRegularSS d.lieZero (X : d.ambient)} := by
  have hss : IsSS F (((1 : ↥d.G) : d.ambientˣ) : d.ambient) := by
    unfold IsSS
    simp only [OneMemClass.coe_one, Units.val_one, LinearMap.mulLeft_one]
    exact Module.End.isSemisimple_id
  have hL : lieCentralizer d.lie (((1 : ↥d.G) : d.ambientˣ) : d.ambient) = d.lie := by
    refine LieSubalgebra.ext _ _ fun X => ?_
    simp [mem_lieCentralizer]
  have h := isOpen_setOf_isRegularSS_lieCentralizer d 1 hss
  rw [hL] at h
  have hc : Continuous fun X : ↥d.lieZero => (⟨(X : d.ambient), d.lieZero_le_lie X.2⟩ : ↥d.lie) :=
    Continuous.subtype_mk continuous_subtype_val _
  have he : {X : ↥d.lieZero | IsRegularSS d.lieZero (X : d.ambient)} =
      (fun X : ↥d.lieZero => (⟨(X : d.ambient), d.lieZero_le_lie X.2⟩ : ↥d.lie)) ⁻¹'
        {Z : ↥d.lie | IsRegularSS d.lie (Z : d.ambient)} := by
    ext X
    exact d.isRegularSS_lieZero_iff
  rw [he]
  exact h.preimage hc

/-- **`θ_f` is unique on `𝔤⁰_reg`**: two locally integrable functions, continuous on `𝔤⁰_reg(F)`,
representing the same distribution agree on `𝔤⁰_reg(F)` (they agree almost everywhere, `𝔤⁰_reg` is
open and `measLie0` charges every nonempty open set).  This uses that `measLie0` is a Haar measure
and not the junk value `0`, i.e. that `bilin` is nondegenerate on `𝔤⁰`, so that a self-dual measure
exists (`isAddHaarMeasure_measLie0`), and that the regular set of `𝔤⁰` is open
(`isOpen_setOf_isRegularSS_lieZero`). -/
theorem isThetaFLie_eqOn_regular {f θ θ' : ↥d.lieZero → ℂ} (hθ : d.IsThetaFLie ψ f θ)
    (hθ' : d.IsThetaFLie ψ f θ') :
    ∀ X : ↥d.lieZero, IsRegularSS d.lieZero (X : d.ambient) → θ X = θ' X := by
  have := t2Space_of_moduleTopology F d.ambient
  have := isTopologicalRing_of_moduleTopology F d.ambient
  have hind : IsInducing (d.lieZero.incl.toLinearMap : ↥d.lieZero → d.ambient) :=
    IsInducing.subtypeVal
  have : IsTopologicalAddGroup ↥d.lieZero :=
    hind.isTopologicalAddGroup d.lieZero.incl.toLinearMap
  have : ContinuousSMul F ↥d.lieZero :=
    hind.continuousSMul continuous_id (fun {c x} => d.lieZero.incl.toLinearMap.map_smul c x)
  -- `𝔤⁰ ≅ F^n` as topological vector spaces
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let e : ↥d.lieZero ≃L[F] (Fin (Module.finrank F ↥d.lieZero) → F) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have : LocallyCompactSpace ↥d.lieZero := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have : TotallyDisconnectedSpace ↥d.lieZero := e.toHomeomorph.symm.totallyDisconnectedSpace
  have : SigmaCompactSpace ↥d.lieZero := e.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  have : SecondCountableTopology ↥d.lieZero :=
    e.toHomeomorph.isEmbedding.secondCountableTopology
  have := d.isAddHaarMeasure_measLie0 ψ
  obtain ⟨hli, hc, hrep⟩ := hθ
  obtain ⟨hli', hc', hrep'⟩ := hθ'
  have hint : ∀ {φ : ↥d.lieZero → ℂ}, LocallyIntegrable φ (d.measLie0 ψ) →
      ∀ f' : ↥d.lieZero → ℂ, IsTestFn f' → Integrable (fun X => φ X * f' X) (d.measLie0 ψ) := by
    intro φ hφ f' hf'
    simpa [mul_comm] using hφ.integrable_smul_left_of_hasCompactSupport hf'.1.continuous hf'.2
  -- the two functions agree almost everywhere
  have hae : (θ - θ') =ᵐ[d.measLie0 ψ] 0 :=
    ae_eq_zero_of_integral_isLocallyConstant (hli.sub hli') fun f' hf hcs => by
      simp only [Pi.sub_apply, sub_mul]
      rw [integral_sub (hint hli f' ⟨hf, hcs⟩) (hint hli' f' ⟨hf, hcs⟩), hrep f' ⟨hf, hcs⟩,
        hrep' f' ⟨hf, hcs⟩, sub_self]
  have hae' : θ =ᵐ[d.measLie0 ψ] θ' := by
    filter_upwards [hae] with X hX
    exact sub_eq_zero.mp hX
  -- hence everywhere on the open regular set, where both are continuous
  have hEq := MeasureTheory.Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hae')
    d.isOpen_setOf_isRegularSS_lieZero hc hc'
  exact fun X hX => hEq hX

/-! ## (L5) `θ_f`: the transfer -/

/-- **`ad` is equivariant**: `ad(g⁻¹ X g) = P(g)⁻¹ ad(X) P(g)` (`adV_conj` on each factor). -/
theorem toSOLin_adLie0_inv (g : ↥d.G) (X : ↥d.lieZero) :
    d.toSOLin (d.adLie0 g⁻¹ X : d.ambient) = d.luoOf.conjInv (d.toGbar g) (d.toSOLin X) := by
  have hinv : ((d.toGbar g)⁻¹ : ↥d.luoOf.Gbar) = d.toGbar g⁻¹ := (map_inv d.toGbar g).symm
  unfold LuoDatum.conjInv
  rw [hinv]
  refine Prod.ext (LinearMap.ext fun v => ?_) (LinearMap.ext fun v => ?_)
  · have h := adV_conj (d.fst g⁻¹) X.2.1.1 v
    rw [map_inv, inv_inv] at h
    exact h
  · have h := adV_conj (d.snd g⁻¹) X.2.2.1 v
    rw [map_inv, inv_inv] at h
    exact h

/-- `ad` preserves commutators on `𝔤⁰` (`adV_commutator` on each factor). -/
theorem toSOLin_commutator {X Y : d.ambient} (hX : X ∈ d.lieZero) (hY : Y ∈ d.lieZero) :
    d.toSOLin (X * Y - Y * X) = d.toSOLin X * d.toSOLin Y - d.toSOLin Y * d.toSOLin X :=
  Prod.ext (adV_commutator hX.1.1 hY.1.1) (adV_commutator hX.2.1 hY.2.1)

/-- **`ad` maps semisimple elements of `𝔤⁰` to semisimple ones**: the minimal polynomial `q` of
`ad X = L_X − R_X` on `C(W) × C(V)` is squarefree, and kills `adV X_W` and `adV X_V`
(`ι((adV X_W)^k v) = (ad X_W)^k ι(v)`), hence the pair `(adV X_W, adV X_V)`. -/
theorem isSS_toSOLin {X : d.ambient} (hX : X ∈ d.lieZero) (hs : IsSS F X) :
    IsSS F (d.toSOLin X) := by
  set D := LieAlgebra.ad F d.ambient X
  have hD : D.IsSemisimple := LieAlgebra.ad_isSemisimple_of_isSemisimple_mulLeft hs
  set q := minpoly F D
  have hq : Squarefree q := hD.minpoly_squarefree
  have h0 : Polynomial.aeval D q = 0 := minpoly.aeval F D
  have hfst : ∀ (i : ℕ) (y : d.ambient),
      ((D ^ i) y).1 = (LieAlgebra.ad F (CliffordAlgebra d.QW) X.1 ^ i) y.1 := by
    intro i
    induction i with
    | zero => intro y; rfl
    | succ i ih =>
      intro y
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
      simp only [D, LieAlgebra.ad_apply, Ring.lie_def, Prod.fst_sub, Prod.fst_mul]
  have hsnd : ∀ (i : ℕ) (y : d.ambient),
      ((D ^ i) y).2 = (LieAlgebra.ad F (CliffordAlgebra d.QV) X.2 ^ i) y.2 := by
    intro i
    induction i with
    | zero => intro y; rfl
    | succ i ih =>
      intro y
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
      simp only [D, LieAlgebra.ad_apply, Ring.lie_def, Prod.snd_sub, Prod.snd_mul]
  have hW : Polynomial.aeval (adV d.QW X.1) q = 0 := by
    refine LinearMap.ext fun v => ?_
    apply CliffordAlgebra.ι_injective d.QW
    have key : CliffordAlgebra.ι d.QW (Polynomial.aeval (adV d.QW X.1) q v) =
        (Polynomial.aeval D q (CliffordAlgebra.ι d.QW v, 0)).1 := by
      rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
        Prod.fst_sum, Prod.smul_fst, hfst, ι_adV_pow hX.1.1]
    rw [key, h0]
    simp
  have hV : Polynomial.aeval (adV d.QV X.2) q = 0 := by
    refine LinearMap.ext fun v => ?_
    apply CliffordAlgebra.ι_injective d.QV
    have key : CliffordAlgebra.ι d.QV (Polynomial.aeval (adV d.QV X.2) q v) =
        (Polynomial.aeval D q (0, CliffordAlgebra.ι d.QV v)).2 := by
      rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
        Prod.snd_sum, Prod.smul_snd, hsnd, ι_adV_pow hX.2.1]
    rw [key, h0]
    simp
  have hq0 : Polynomial.aeval (d.toSOLin X) q = 0 := by
    refine Prod.ext ?_ ?_
    · change d.luoOf.fstA (Polynomial.aeval (d.toSOLin X) q) = 0
      rw [← Polynomial.aeval_algHom_apply, fstA_toSOLin]
      exact hW
    · change d.luoOf.sndA (Polynomial.aeval (d.toSOLin X) q) = 0
      rw [← Polynomial.aeval_algHom_apply, sndA_toSOLin]
      exact hV
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hq ?_
  have h := Polynomial.aeval_algHom_apply (Algebra.lmul F d.luoOf.Amb) (d.toSOLin X) q
  rw [hq0, map_zero] at h
  exact h

/-- **`ad` maps regular semisimple elements of `𝔤⁰` to regular semisimple elements of
`so(W) ⊕ so(V)`**: semisimplicity by `isSS_toSOLin`; the centralizer of `ad X` pulls back along the
bijection `ad` (`toSO_bijective`) into the centralizer of `X`, as `ad` preserves commutators. -/
theorem isRegularSS_toSOLin {X : d.ambient} (hX : X ∈ d.lieZero)
    (h : IsRegularSS d.lieZero X) : IsRegularSS d.luoOf.lie (d.toSOLin X) := by
  refine ⟨d.isSS_toSOLin hX h.1, ?_⟩
  rw [isLieAbelian_iff_forall_commute]
  have hab := isLieAbelian_iff_forall_commute.mp h.2
  have pull : ∀ M ∈ lieCentralizer d.luoOf.lie (d.toSOLin X),
      ∃ Z ∈ lieCentralizer d.lieZero X, d.toSOLin Z = M := by
    intro M hM
    rw [mem_lieCentralizer] at hM
    set Z : ↥d.lieZero := d.toSO.symm ⟨M, hM.1⟩ with hZdef
    have hZM : d.toSOLin (Z : d.ambient) = M := d.toSOLin_toSO_symm ⟨M, hM.1⟩
    refine ⟨Z, mem_lieCentralizer.mpr ⟨Z.2, ?_⟩, hZM⟩
    have hc : X * Z - Z * X ∈ d.lieZero := by
      have := d.lieZero.lie_mem hX Z.2
      rwa [Ring.lie_def] at this
    have h0 : d.toSOFun ⟨_, hc⟩ = d.toSOFun 0 := by
      apply Subtype.ext
      change d.toSOLin (X * Z - Z * X) = d.toSOLin 0
      rw [d.toSOLin_commutator hX Z.2, hZM, hM.2, sub_self, map_zero]
    exact sub_eq_zero.mp (congrArg Subtype.val (d.toSO_bijective.1 h0))
  intro M₁ h₁ M₂ h₂
  obtain ⟨Z₁, hZ₁, rfl⟩ := pull M₁ h₁
  obtain ⟨Z₂, hZ₂, rfl⟩ := pull M₂ h₂
  rw [← sub_eq_zero, ← d.toSOLin_commutator (mem_lieCentralizer.mp hZ₁).1
    (mem_lieCentralizer.mp hZ₂).1, hab Z₁ hZ₁ Z₂ hZ₂, sub_self, map_zero]

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
  have := t2Space_of_moduleTopology F d.ambient
  have := isTopologicalRing_of_moduleTopology F d.ambient
  have := t2Space_of_moduleTopology F d.luoOf.Amb
  have : ContinuousSMul F d.luoOf.Amb := IsModuleTopology.toContinuousSMul F d.luoOf.Amb
  have : ContinuousSMul F ↥d.luoOf.lie :=
    inferInstanceAs (ContinuousSMul F ↥d.luoOf.lie.toSubmodule)
  have : IsTopologicalAddGroup ↥d.luoOf.lie :=
    inferInstanceAs (IsTopologicalAddGroup ↥d.luoOf.lie.toSubmodule)
  have : T2Space ↥d.luoOf.lie := inferInstance
  have : ContinuousSMul F ↥d.lieZero := inferInstanceAs (ContinuousSMul F ↥d.lieZero.toSubmodule)
  have : IsTopologicalAddGroup ↥d.lieZero :=
    inferInstanceAs (IsTopologicalAddGroup ↥d.lieZero.toSubmodule)
  -- `so(W) ⊕ so(V) ≅ F^n`: locally compact and second countable
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let eF : ↥d.luoOf.lie ≃L[F] (Fin (Module.finrank F ↥d.luoOf.lie) → F) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have : LocallyCompactSpace ↥d.luoOf.lie := eF.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology ↥d.luoOf.lie := eF.toHomeomorph.isEmbedding.secondCountableTopology
  have := d.isAddHaarMeasure_measLie0 ψ
  have := d.luoOf.isAddHaarMeasure_measLie d.nondeg_QV ψ
  set e := d.toSOCLE with he
  have hecoe : ⇑e = ⇑d.toSO := rfl
  -- `ad` carries `measLie0` to a multiple of `measLie`
  have : (Measure.map e (d.measLie0 ψ)).IsAddHaarMeasure := e.isAddHaarMeasure_map _
  set c := Measure.addHaarScalarFactor (Measure.map e (d.measLie0 ψ)) (d.luoOf.measLie ψ)
  have hc : Measure.map e (d.measLie0 ψ) = (c : ENNReal) • d.luoOf.measLie ψ :=
    Measure.isAddLeftInvariant_eq_smul _ _
  set em := e.toHomeomorph.toMeasurableEquiv
  have hint : ∀ k : ↥d.luoOf.lie → ℂ, ∫ X, k (d.toSO X) ∂d.measLie0 ψ =
      ((c : ENNReal).toReal : ℝ) • ∫ Y, k Y ∂d.luoOf.measLie ψ := by
    intro k
    rw [← integral_smul_measure, ← hc]
    exact (integral_map_equiv em k).symm
  refine ⟨?_, ?_, ?_⟩
  · -- local integrability
    have hl : LocallyIntegrable θ (Measure.map e.toHomeomorph (d.measLie0 ψ)) := by
      change LocallyIntegrable θ (Measure.map e (d.measLie0 ψ))
      rw [hc]
      intro x
      obtain ⟨s, hs, hi⟩ := h1 x
      exact ⟨s, hs, by
        rw [IntegrableOn, Measure.restrict_smul]
        exact hi.smul_measure ENNReal.coe_ne_top⟩
    exact (locallyIntegrable_map_homeomorph e.toHomeomorph).1 hl
  · -- continuity on the regular set
    exact h2.comp e.continuous.continuousOn fun X hX => d.isRegularSS_toSOLin X.2 hX
  · intro f' hf'
    have hf'' : IsTestFn (f' ∘ d.toSO.symm) := by
      rw [← coe_toSOCLE_symm]
      exact ⟨hf'.1.comp_continuous d.toSOCLE.symm.continuous,
        hf'.2.comp_homeomorph d.toSOCLE.symm.toHomeomorph⟩
    -- pointwise: `f(g⁻¹ X g)` in terms of `ad`
    have hpt : ∀ (g : ↥d.G) (Y : ↥d.luoOf.lie),
        f (d.adLie0 g⁻¹ (d.toSO.symm Y)) * f' (d.toSO.symm Y) =
          d.luoOf.extFn (f ∘ d.toSO.symm) (d.luoOf.conjInv (d.toGbar g) Y) *
            (f' ∘ d.toSO.symm) Y := by
      intro g Y
      have hcj : d.luoOf.conjInv (d.toGbar g) Y = d.toSOLin (d.adLie0 g⁻¹ (d.toSO.symm Y)) := by
        rw [d.toSOLin_adLie0_inv, d.toSOLin_toSO_symm]
      have hm : d.luoOf.conjInv (d.toGbar g) Y ∈ d.luoOf.lie := hcj ▸ d.toSO_mem _
      rw [LuoDatum.extFn, dite_eq_left_of_eq_true (eq_true hm)]
      simp only [Function.comp_apply]
      congr 2
      rw [eq_comm, Equiv.symm_apply_eq]
      exact Subtype.ext hcj
    obtain ⟨φ, hφ⟩ := d.exists_continuousMulEquiv_toGbar hW hV
    have hmu : d.muG = Measure.map φ Measure.haar := by rw [hφ]; rfl
    have hL := hint fun Y => θ Y * f' (d.toSO.symm Y)
    simp only [Equiv.symm_apply_apply] at hL
    simp only [Function.comp_apply]
    rw [hL]
    have h3' := h3 _ hf''
    simp only [Function.comp_apply] at h3'
    rw [h3', LuoDatum.orbitalPairing, orbitalPairingLie, hmu,
      show Measure.map (⇑φ) (Measure.haar : Measure d.GmodAG) =
        Measure.map (⇑φ.toHomeomorph) Measure.haar from rfl,
      φ.toHomeomorph.measurableEmbedding.integral_map, ← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hI := hint fun Y => f (d.adLie0 (Quotient.out x)⁻¹ (d.toSO.symm Y)) * f' (d.toSO.symm Y)
    simp only [Equiv.symm_apply_apply] at hI
    simp only
    rw [hI]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun Y => ?_)
    dsimp only
    rw [hpt, show φ.toHomeomorph x = d.toGbar (Quotient.out x) from congrFun hφ x]

/-! ## (L6)–(L9) `m^Lie_geom` -/

/-- **(L6, L7) The germs `c_θ(X)` agree.**  For a quasi-character `θ` on `so(W) ⊕ so(V)` and
`X ∈ 𝔱⁰_♮` of a torus of `Γ^Lie(G,H)`, the germ of `θ ∘ ad` at `X` for the orbit `orbitChoiceLie X`
(`germLie` for `(G, 𝔤⁰, bilin)`) is Luo's `c_θ(ad X)` (`germLie` for `(Ḡ, 𝔤, B)` and the orbit
`orbitChoice`).  Ingredients: (L6) on `so(W) ⊕ so(V)`, `bilin = (k_W tr_W, k_V tr_V)` with
`k_W, k_V ∈ F^×` (one constant for each factor, so the scaling argument is applied to `so(W)` and
`so(V)` separately), and `ĵ_{aB}(O, ·) = ĵ_B(aO, ·)` with `aO = O` for regular nilpotent orbits, so
the germs do not depend on the choice of invariant form; `Z_G(X)(F) → Ḡ_X(F)` is onto, so the
nilpotent
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
matching each torus with the conjugacy class of its image (`IsNaturalTorusCorr`).
Not proved here. -/
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

/-- A local expansion of `θ` at a semisimple `X` is one of every `θ'` agreeing with `θ` on
`𝔤⁰_reg(F)`: the expansion is only evaluated at `X + Y` with `Y ∈ 𝔤⁰_X` small and regular, which
is regular in `𝔤⁰` (`exists_nhds_isRegularSS_add`).  Lie-algebra form of
`hasGermExpansion_congr_regularSet`. -/
theorem hasGermExpansionLie_congr_regularSet {θ θ' : ↥d.lieZero → ℂ}
    (he : ∀ X : ↥d.lieZero, IsRegularSS d.lieZero (X : d.ambient) → θ X = θ' X)
    {X : d.ambient} (hX : IsSS F X)
    {c : NilOrbit (lieGrpCentralizer d.G X) (lieCentralizer d.lieZero X) → ℂ}
    (h : HasGermExpansionLie d.G d.lieZero d.bilin ψ θ X c) :
    HasGermExpansionLie d.G d.lieZero d.bilin ψ θ' X c := by
  obtain ⟨hfin, ω, hω, hexp⟩ := h
  obtain ⟨ω', hω', hreg⟩ := exists_nhds_isRegularSS_add F d.lieZero hX
  refine ⟨hfin, ω ∩ ω', Filter.inter_mem hω hω', fun Y hY hYc hYr Z hZ => ?_⟩
  rw [← he Z (by rw [hZ]; exact hreg Y hY.2 hYc hYr)]
  exact hexp Y hY.1 hYc hYr Z hZ

/-- **Germs only see `𝔤⁰_reg(F)`**: at a semisimple `X`, `c_{θ,O}(X)` depends only on
`θ|_{𝔤⁰_reg(F)}`.  The two functions have the same local expansions at `X`
(`hasGermExpansionLie_congr_regularSet`), so the same coefficient is chosen; no uniqueness of the
expansion is used. -/
theorem germLie0_congr_regularSet {θ θ' : ↥d.lieZero → ℂ}
    (he : ∀ X : ↥d.lieZero, IsRegularSS d.lieZero (X : d.ambient) → θ X = θ' X)
    {X : d.ambient} (hX : IsSS F X)
    (O : NilOrbit (lieGrpCentralizer d.G X) (lieCentralizer d.lieZero X)) :
    d.germLie0 ψ θ X O = d.germLie0 ψ θ' X O := by
  classical
  have hP : (fun c => HasGermExpansionLie d.G d.lieZero d.bilin ψ θ X c) =
      fun c => HasGermExpansionLie d.G d.lieZero d.bilin ψ θ' X c :=
    funext fun c => propext
      ⟨d.hasGermExpansionLie_congr_regularSet ψ he hX,
        d.hasGermExpansionLie_congr_regularSet ψ (fun Z hZ => (he Z hZ).symm) hX⟩
  have key : ∀ {P Q : (NilOrbit (lieGrpCentralizer d.G X) (lieCentralizer d.lieZero X) → ℂ) →
      Prop}, P = Q → (if h : ∃ c, P c then h.choose O else 0) =
        (if h : ∃ c, Q c then h.choose O else 0) := by
    intro P Q hPQ
    subst hPQ
    rfl
  unfold germLie0 germLie
  rw [key hP]

/-- The integrand of `m^Lie_{geom,s}` only sees `θ|_{𝔤⁰_reg(F)}`, at points of `𝔱⁰_♮` that are
semisimple. -/
theorem gammaIntegrandLie_congr_regularSet {θ θ' : ↥d.lieZero → ℂ}
    (he : ∀ X : ↥d.lieZero, IsRegularSS d.lieZero (X : d.ambient) → θ X = θ' X)
    (T : Subgroup ↥(GSpin d.QW)) (s : ℝ) (X : CliffordAlgebra d.QW)
    (hss : d.IsGammaEltLie T X → IsSS F (d.diagLie X)) :
    d.gammaIntegrandLie ψ θ T s X = d.gammaIntegrandLie ψ θ' T s X := by
  unfold gammaIntegrandLie
  split_ifs with h
  · rw [d.germLie0_congr_regularSet ψ he (hss h)]
  · rfl

/-- `m^Lie_geom(θ)` depends only on `θ|_{𝔤⁰_reg}`, given that the points of `𝔱⁰_♮` are semisimple
for the tori representing the classes of `Γ^Lie(G,H)`. -/
theorem mGeomLie_congr_regularSet_of_isSS {θ θ' : ↥d.lieZero → ℂ}
    (he : ∀ X : ↥d.lieZero, IsRegularSS d.lieZero (X : d.ambient) → θ X = θ' X)
    (hss : ∀ (c : GammaClass d) (X : CliffordAlgebra d.QW),
      d.IsGammaEltLie (Quot.out c).1 X → IsSS F (d.diagLie X)) :
    d.mGeomLie ψ θ = d.mGeomLie ψ θ' := by
  have hS : d.mGeomLieS ψ θ = d.mGeomLieS ψ θ' := by
    funext s
    unfold mGeomLieS torusIntegralLie
    refine tsum_congr fun c => ?_
    congr 2
    funext X
    exact d.gammaIntegrandLie_congr_regularSet ψ he _ s X (hss c X)
  unfold mGeomLie
  rw [hS]

/-- **(L9) `m^Lie_geom(θ)` depends only on `θ|_{𝔤⁰_reg}`** (the Lie-algebra form of
`mGeomS_congr_regularSet`): the germs `c_{θ,O}(X)` only see `θ` at `X + Y` with `Y ∈ 𝔤⁰_X` small
and regular in `𝔤⁰_X`, and such `X + Y` are regular in `𝔤⁰` (`mGeomLie_congr_regularSet_of_isSS`).
The points `X` of `𝔱⁰_♮` are semisimple for `T = T_x`, `x ∈ Γ(G,H)`: `X` commutes with `x` and
kills `W'_x` (`GGPData.isSS_of_commute_of_isGammaElt`), and so is `(X, X)`. -/
theorem mGeomLie_congr_regularSet {θ θ' : ↥d.lieZero → ℂ}
    (he : ∀ X : ↥d.lieZero, IsRegularSS d.lieZero (X : d.ambient) → θ X = θ' X) :
    d.mGeomLie ψ θ = d.mGeomLie ψ θ' := by
  refine d.mGeomLie_congr_regularSet_of_isSS ψ he fun c X hX => ?_
  obtain ⟨x, hx, hT⟩ := (Quot.out c).2
  obtain ⟨hXs, hXc, hXf⟩ := hX.1
  rw [← hT] at hXc hXf
  have hss : IsSS F X := d.isSS_of_commute_of_isGammaElt hx hXs.1
    (hXc x (d.self_mem_torusOf x)) fun v hv => hXf v <| Submodule.mem_iInf _ |>.mpr fun t => by
      have := t.2.2 v hv
      simpa [fixedSub, sub_eq_zero] using this
  exact isSS_algHom ((AlgHom.id F _).prod
    (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ))) hss

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
