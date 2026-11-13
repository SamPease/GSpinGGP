/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.ExpCompatT
import GSpinGGP.TraceFormula.LuoTorus
import GSpinGGP.GGP.TorusIntegral

/-!
# Conjugating a torus of `Γ(G,H)`

For `g ∈ GSpin(W)(F)` and a subgroup `T`, with `T₁ = g T g⁻¹`:

* `specP_mem_commonFixed_map_conj`, `specP_inv_mem_commonFixed`: `W'_{T₁} = P(g) W'_T`;
* `conj_mem_lieTorus`, `lieTorusConj`: `X ↦ g X g⁻¹` maps `𝔱⁰(T)` onto `𝔱⁰(T₁)`;
* `isGammaEltLie_conj`: it maps `𝔱⁰_♮(T)` into `𝔱⁰_♮(T₁)`;
* `deltaLie_conj`, `weylDiscLie_diagLie_conj`: `Δ` and `D^G` are conjugation invariant;
* `isExpCompatT_map_lieTorusConj`: conjugation carries `ν(T) dX` to `ν(gTg⁻¹) dX`;
* `isGammaElt_conj`: `Γ(G,H)` is stable under conjugation;
* `torusIntegralLie_conj_of`: the torus integrals over `T_x` and `g T_x g⁻¹` agree if the germs
  are conjugation invariant.
-/

noncomputable section

open MeasureTheory Topology Filter

set_option linter.style.haveILetI false

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

/-- `(gTg⁻¹)g⁻¹ = T`. -/
theorem map_conj_inv_map_conj (T : Subgroup ↥(GSpin d.QW)) (g : ↥(GSpin d.QW)) :
    (T.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = T := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id T
  ext t
  simp [mul_assoc]

/-- `P(g)` maps `W'_T` into `W'_{gTg⁻¹}`. -/
theorem specP_mem_commonFixed_map_conj {T : Subgroup ↥(GSpin d.QW)} (g : ↥(GSpin d.QW))
    {w : Fin d.m → F} (hw : w ∈ commonFixed T) :
    specP d.QW g w ∈ commonFixed (T.map (MulAut.conj g).toMonoidHom) := by
  refine (Submodule.mem_iInf _).mpr fun t₁ => ?_
  obtain ⟨_, t, ht, rfl⟩ := t₁
  have h := LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hw ⟨t, ht⟩)
  have h' : specP d.QW t w = w := by simpa [sub_eq_zero] using h
  have e : specP d.QW (g * t * g⁻¹) (specP d.QW g w) = specP d.QW g w := by
    rw [map_mul, LinearEquiv.mul_apply, show specP d.QW g⁻¹ (specP d.QW g w) = w by simp, map_mul,
      LinearEquiv.mul_apply, h']
  refine LinearMap.mem_ker.mpr ?_
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, LinearMap.sub_apply, LinearMap.id_coe,
    id_eq, LinearEquiv.coe_coe]
  rw [e, sub_self]

/-- `P(g)⁻¹` maps `W'_{gTg⁻¹}` into `W'_T`. -/
theorem specP_inv_mem_commonFixed {T : Subgroup ↥(GSpin d.QW)} (g : ↥(GSpin d.QW))
    {w : Fin d.m → F} (hw : w ∈ commonFixed (T.map (MulAut.conj g).toMonoidHom)) :
    specP d.QW g⁻¹ w ∈ commonFixed T := by
  have := d.specP_mem_commonFixed_map_conj g⁻¹ hw
  rwa [map_conj_inv_map_conj] at this

/-- The value of `g t g⁻¹` in `C(W)`. -/
theorem coe_conj_gspin (g t : ↥(GSpin d.QW)) :
    (((MulAut.conj g t : ↥(GSpin d.QW)) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) =
      ((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) *
        ((t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) *
        (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) := rfl

/-- **`X ↦ g X g⁻¹` maps `𝔱⁰(T)` into `𝔱⁰(gTg⁻¹)`**: it preserves `so_Cliff(W)`
(`conj_mem_soSub`), commutation with `T` becomes commutation with `gTg⁻¹`, and
`ad (g X g⁻¹) = P(g) ad X P(g)⁻¹` (`adV_conj`) kills `W'_{gTg⁻¹} = P(g) W'_T`. -/
theorem conj_mem_lieTorus {T : Subgroup ↥(GSpin d.QW)} (g : ↥(GSpin d.QW))
    {X : CliffordAlgebra d.QW} (hX : X ∈ d.lieTorus T) :
    ((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X *
        (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) ∈
      d.lieTorus (T.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hX0, hX1, hX2⟩ := hX
  refine ⟨conj_mem_soSub g hX0, ?_, fun w hw => ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, coe_conj_gspin]
    have h := hX1 t ht
    simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc (((t : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW), h,
      mul_assoc]
  · rw [adV_conj g hX0.1, hX2 _ (d.specP_inv_mem_commonFixed g hw), map_zero]

/-- `X ↦ g X g⁻¹` as a linear homeomorphism `𝔱⁰(T) ≃ 𝔱⁰(T')`, `T' = gTg⁻¹`. -/
def lieTorusConj {T T' : Subgroup ↥(GSpin d.QW)} (g : ↥(GSpin d.QW))
    (hT' : T' = T.map (MulAut.conj g).toMonoidHom) :
    ↥(d.lieTorus T) ≃L[F] ↥(d.lieTorus T') :=
  haveI := submodule_isModuleTopology (d.lieTorus T)
  haveI := submodule_isModuleTopology (d.lieTorus T')
  have hT : T = T'.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [hT', map_conj_inv_map_conj]
  let e : ↥(d.lieTorus T) ≃ₗ[F] ↥(d.lieTorus T') :=
    { toFun := fun X => ⟨_, hT' ▸ d.conj_mem_lieTorus g X.2⟩
      invFun := fun Y => ⟨((g⁻¹ : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) *
          (Y : CliffordAlgebra d.QW) *
          ((((g⁻¹ : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ))⁻¹ : (CliffordAlgebra d.QW)ˣ),
        hT ▸ d.conj_mem_lieTorus g⁻¹ Y.2⟩
      map_add' := fun X Y => Subtype.ext (by simp [mul_add, add_mul])
      map_smul' := fun r X => Subtype.ext (by simp)
      left_inv := fun X => Subtype.ext (by simp [mul_assoc])
      right_inv := fun Y => Subtype.ext (by simp [mul_assoc]) }
  { e with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

@[simp] theorem coe_lieTorusConj {T T' : Subgroup ↥(GSpin d.QW)} (g : ↥(GSpin d.QW))
    (hT' : T' = T.map (MulAut.conj g).toMonoidHom) (X : ↥(d.lieTorus T)) :
    ((d.lieTorusConj g hT' X : ↥(d.lieTorus T')) : CliffordAlgebra d.QW) =
      ((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X *
        (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) := rfl

/-- **`X ↦ g X g⁻¹` maps `𝔱⁰_♮(T)` into `𝔱⁰_♮(gTg⁻¹)`**: `ker ad(gXg⁻¹) = P(g) ker ad X`, and
an element of `so_Cliff(W)` commuting with `gXg⁻¹` and killing `W'_{gTg⁻¹}` is `g Y g⁻¹` with `Y`
commuting with `X` and killing `W'_T`. -/
theorem isGammaEltLie_conj {T : Subgroup ↥(GSpin d.QW)} (g : ↥(GSpin d.QW))
    {X : CliffordAlgebra d.QW} (hX : d.IsGammaEltLie T X) :
    d.IsGammaEltLie (T.map (MulAut.conj g).toMonoidHom)
      (((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X *
        (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) := by
  obtain ⟨hXT, hker, hreg⟩ := hX
  have hXg : X ∈ gspin d.QW := hXT.1.1
  refine ⟨d.conj_mem_lieTorus g hXT, ?_, fun Y hY hYX hYf => ?_⟩
  · ext v
    rw [LinearMap.mem_ker, adV_conj g hXg]
    constructor
    · intro hv
      have h0 : adV d.QW X (specP d.QW g⁻¹ v) = 0 := by
        simpa using congrArg (specP d.QW g⁻¹) hv
      have := d.specP_mem_commonFixed_map_conj g (hker ▸ (LinearMap.mem_ker.mpr h0))
      rwa [specP_inv_apply_apply] at this
    · intro hv
      have := d.specP_inv_mem_commonFixed g hv
      rw [← hker, LinearMap.mem_ker] at this
      rw [this, map_zero]
  · -- `Y' = g⁻¹ Y g`
    set a := ((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)
    set ai := (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)
    have hai : ai * a = 1 := Units.inv_mul _
    have hia : a * ai = 1 := Units.mul_inv _
    have hY' : ai * Y * a ∈ soSub d.QW := by
      have := conj_mem_soSub g⁻¹ hY
      simpa using this
    have hY'X : ai * Y * a * X = X * (ai * Y * a) := by
      calc ai * Y * a * X = ai * (Y * (a * X * ai)) * a := by
            simp only [mul_assoc, hai, mul_one]
        _ = ai * (a * X * ai * Y) * a := by rw [hYX]
        _ = X * (ai * Y * a) := by
            simp only [mul_assoc]; rw [← mul_assoc ai a, hai, one_mul]
    have hY'f : ∀ w ∈ commonFixed T, adV d.QW (ai * Y * a) w = 0 := by
      intro w hw
      have e := adV_conj g⁻¹ hY.1 w
      simp only [Subgroup.coe_inv, inv_inv] at e
      change adV d.QW (ai * Y * a) w = _ at e
      rw [e, hYf _ (d.specP_mem_commonFixed_map_conj g hw), map_zero]
    have hmem := d.conj_mem_lieTorus g (hreg _ hY' hY'X hY'f)
    have e : a * (ai * Y * a) * ai = Y := by
      simp only [← mul_assoc, hia, one_mul]; rw [mul_assoc, hia, mul_one]
    rwa [e] at hmem

/-- `ad (g X g⁻¹) = P(g) ad X P(g)⁻¹` as endomorphisms of `W`. -/
theorem adV_conj_eq_conj (g : ↥(GSpin d.QW)) {X : CliffordAlgebra d.QW} (hX : X ∈ gspin d.QW) :
    adV d.QW (((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X *
        (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) =
      (specP d.QW g).conj (adV d.QW X) := by
  refine LinearMap.ext fun v => ?_
  rw [adV_conj g hX, LinearEquiv.conj_apply_apply]
  congr 2

/-- **`Δ` is conjugation invariant**: `Δ(gXg⁻¹) = Δ(X)` for `X ∈ gspin(W)`. -/
theorem deltaLie_conj (g : ↥(GSpin d.QW)) {X : CliffordAlgebra d.QW} (hX : X ∈ gspin d.QW) :
    d.deltaLie (((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X *
        (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) =
      d.deltaLie X := by
  change absF (detIm (adV d.QW _)) = absF (detIm (adV d.QW X))
  rw [d.adV_conj_eq_conj g hX]
  exact congrArg absF (detIm_conj (adV d.QW X) (specP d.QW g))

/-- `(gXg⁻¹, gXg⁻¹) = (g, g) (X, X) (g, g)⁻¹` in `C(W) × C(V)`. -/
theorem diagLie_conj (g : ↥(GSpin d.QW)) (X : CliffordAlgebra d.QW) :
    d.diagLie (((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X *
        (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) =
      (((d.diag g : ↥d.G) : d.ambientˣ) : d.ambient) * d.diagLie X *
        ((((d.diag g : ↥d.G) : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) := by
  refine Prod.ext rfl ?_
  change CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ) (_ * X * _) = _
  rw [map_mul, map_mul]
  rfl

/-- **`D^G` is conjugation invariant** on the diagonal: `D^G((gXg⁻¹, gXg⁻¹)) = D^G((X, X))` for
`X ∈ so_Cliff(W)` (`weylDiscLie_units_conj` with `(g, g) ∈ G(F)`, which normalizes `𝔤⁰`). -/
theorem weylDiscLie_diagLie_conj (g : ↥(GSpin d.QW)) {X : CliffordAlgebra d.QW}
    (hX : X ∈ soSub d.QW) :
    weylDiscLie d.lieZero (d.diagLie (((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X *
        (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))) =
      weylDiscLie d.lieZero (d.diagLie X) := by
  rw [d.diagLie_conj]
  refine weylDiscLie_units_conj d.lieZero _ (le_antisymm ?_ fun Y hY => ?_)
    (d.diagLie_mem_lieZero hX)
  · rintro _ ⟨Y, hY, rfl⟩
    exact d.conj_mem_lie0 _ hY
  · have := d.conj_mem_lie0 (d.diag g)⁻¹ hY
    simp only [Subgroup.coe_inv, inv_inv] at this
    exact ⟨_, this, by simp [mul_assoc]⟩

/-- Conjugation by `g` as an isomorphism of topological groups `T ≃ gTg⁻¹`. -/
def torusConjHomeomorph (T : Subgroup ↥(GSpin d.QW)) (g : ↥(GSpin d.QW)) :
    ↥T ≃ₜ* ↥(T.map (MulAut.conj g).toMonoidHom) :=
  ContinuousMulEquiv.subgroupMap
    { MulAut.conj g with
      continuous_toFun := by
        change Continuous fun t : ↥(GSpin d.QW) => g * t * g⁻¹
        fun_prop
      continuous_invFun := by
        change Continuous fun t : ↥(GSpin d.QW) => g⁻¹ * t * g⁻¹⁻¹
        fun_prop } T

@[simp] theorem coe_torusConjHomeomorph (T : Subgroup ↥(GSpin d.QW)) (g : ↥(GSpin d.QW))
    (t : ↥T) : ((d.torusConjHomeomorph T g t : ↥(T.map (MulAut.conj g).toMonoidHom)) :
      ↥(GSpin d.QW)) = g * t * g⁻¹ := rfl

/-- Conjugation carries the scalars of `T` onto the scalars of `gTg⁻¹` (they are central). -/
theorem map_scalarsIn_torusConjHomeomorph (T : Subgroup ↥(GSpin d.QW)) (g : ↥(GSpin d.QW)) :
    (d.scalarsIn T).map (d.torusConjHomeomorph T g).toMulEquiv.toMonoidHom =
      d.scalarsIn (T.map (MulAut.conj g).toMonoidHom) := by
  have hc : ∀ c : Fˣ, g * scalarGSpin d.QW c * g⁻¹ = scalarGSpin d.QW c := fun c => by
    rw [(scalarGSpin_commute d.QW c g).eq.symm, mul_inv_cancel_right]
  have hmem : ∀ {T' : Subgroup ↥(GSpin d.QW)} (s : ↥T'),
      s ∈ d.scalarsIn T' ↔ ∃ c, scalarGSpin d.QW c = (s : ↥(GSpin d.QW)) := fun _ => Iff.rfl
  ext s'
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨c, hcs⟩ := (hmem s).mp hs
    refine (hmem _).mpr ⟨c, ?_⟩
    change _ = g * (s : ↥(GSpin d.QW)) * g⁻¹
    rw [← hcs, hc]
  · intro hs'
    obtain ⟨c, hcs⟩ : ∃ c, scalarGSpin d.QW c = (s' : ↥(GSpin d.QW)) := hs'
    obtain ⟨_, t, ht, rfl⟩ := s'
    have htc : t = scalarGSpin d.QW c := by
      have h : g * t * g⁻¹ = g * scalarGSpin d.QW c * g⁻¹ := by rw [hc]; exact hcs.symm
      exact mul_left_cancel (mul_right_cancel h)
    subst htc
    exact ⟨⟨_, ht⟩, (hmem _).mpr ⟨c, rfl⟩, Subtype.ext rfl⟩

/-- `T(F)/A_{G,H}(F) ≃ (gTg⁻¹)(F)/A_{G,H}(F)`, induced by conjugation. -/
def torusQuotConj (T : Subgroup ↥(GSpin d.QW)) (g : ↥(GSpin d.QW)) :
    d.TorusQuot T ≃ₜ* d.TorusQuot (T.map (MulAut.conj g).toMonoidHom) :=
  (d.torusConjHomeomorph T g).quotientCongr _ _ (d.map_scalarsIn_torusConjHomeomorph T g)

/-- **Conjugation carries `ν(T) dX` to `ν(gTg⁻¹) dX`**: `X ↦ g X g⁻¹` maps
`{e^X A_{G,H}(F) : X ∈ S}` onto `{e^Y A_{G,H}(F) : Y ∈ g S g⁻¹}` (`expA_units_conj`), and
`T(F)/A_{G,H}(F) ≃ (gTg⁻¹)(F)/A_{G,H}(F)` carries probability Haar measure to probability Haar
measure (`probHaar_preimage`). -/
theorem isExpCompatT_map_lieTorusConj {T : Subgroup ↥(GSpin d.QW)} [CompactSpace (d.TorusQuot T)]
    (g : ↥(GSpin d.QW)) {μ : Measure ↥(d.lieTorus T)} (hμ : d.IsExpCompatT T μ) :
    d.IsExpCompatT (T.map (MulAut.conj g).toMonoidHom) (μ.map (d.lieTorusConj g rfl)) := by
  set T₁ := T.map (MulAut.conj g).toMonoidHom with hT₁
  letI : MeasurableSpace (d.TorusQuot T) := borel _
  haveI : BorelSpace (d.TorusQuot T) := ⟨rfl⟩
  letI : MeasurableSpace (d.TorusQuot T₁) := borel _
  haveI : BorelSpace (d.TorusQuot T₁) := ⟨rfl⟩
  have := submodule_isTopologicalAddGroup (d.lieTorus T)
  have := submodule_isTopologicalAddGroup (d.lieTorus T₁)
  obtain ⟨hμH, U, hU, hUS⟩ := hμ
  let e := d.lieTorusConj g (T' := T₁) rfl
  refine ⟨e.toLinearEquiv.toAddEquiv.isAddHaarMeasure_map _ e.continuous e.symm.continuous,
    e.symm ⁻¹' U, e.symm.continuous.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hU),
    fun S' hS' hS'U => ?_⟩
  have hSm : MeasurableSet (e ⁻¹' S') := e.continuous.measurable hS'
  have hSU : e ⁻¹' S' ⊆ U := fun X hX => by
    have := hS'U hX
    rwa [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] at this
  refine (Measure.map_apply e.continuous.measurable hS').trans ((hUS _ hSm hSU).trans ?_)
  let E := d.torusQuotConj T g
  haveI : CompactSpace (d.TorusQuot T₁) := E.toHomeomorph.compactSpace
  refine Eq.trans ?_ (probHaar_preimage E _)
  congr 1
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨X, hX, t, ht, rfl⟩
    refine ⟨e X, hX, d.torusConjHomeomorph T g t, ?_, ?_⟩
    · change ((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) *
          (((t : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) *
          (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) =
        expA F (((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) *
          (X : CliffordAlgebra d.QW) *
          (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
      rw [ht, expA_units_conj]
    · exact (d.torusConjHomeomorph T g).quotientCongr_mk (d.scalarsIn T)
        (d.scalarsIn (T.map (MulAut.conj g).toMonoidHom))
        (d.map_scalarsIn_torusConjHomeomorph T g) t
  · rintro ⟨Y, hY, t₁, ht₁, hq⟩
    obtain ⟨X, rfl⟩ := e.surjective Y
    obtain ⟨t, rfl⟩ := (d.torusConjHomeomorph T g).surjective t₁
    refine ⟨X, hY, t, ?_, ?_⟩
    · have ht' : ((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) *
          (((t : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) *
          (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) =
          expA F (((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) *
            (X : CliffordAlgebra d.QW) *
            (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) :=
        ht₁
      rw [expA_units_conj] at ht'
      simpa [mul_assoc] using congrArg (fun z =>
        (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * z *
          ((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) ht'
    · exact E.injective ((show E q = _ from hq).trans
        ((d.torusConjHomeomorph T g).quotientCongr_mk (d.scalarsIn T)
          (d.scalarsIn (T.map (MulAut.conj g).toMonoidHom))
          (d.map_scalarsIn_torusConjHomeomorph T g) t).symm)

/-- `X ∈ 𝔱⁰_♮(T)` iff `g X g⁻¹ ∈ 𝔱⁰_♮(gTg⁻¹)`. -/
theorem isGammaEltLie_conj_iff {T : Subgroup ↥(GSpin d.QW)} (g : ↥(GSpin d.QW))
    {X : CliffordAlgebra d.QW} :
    d.IsGammaEltLie (T.map (MulAut.conj g).toMonoidHom)
        (((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X *
          (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) ↔
      d.IsGammaEltLie T X := by
  refine ⟨fun h => ?_, d.isGammaEltLie_conj g⟩
  have h' := d.isGammaEltLie_conj g⁻¹ h
  rw [map_conj_inv_map_conj] at h'
  convert h' using 1
  simp [mul_assoc]

/-- **`Γ(G,H)` is stable under conjugation**: `g x g⁻¹` is semisimple (`isSS_conj`), and
`T_{gxg⁻¹} = g T_x g⁻¹` (`torusOf_conj`) is commutative with compact
`T_{gxg⁻¹}(F)/A_{G,H}(F) ≃ T_x(F)/A_{G,H}(F)` (`torusQuotConj`). -/
theorem isGammaElt_conj {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) (g : ↥(GSpin d.QW)) :
    d.IsGammaElt (g * x * g⁻¹) := by
  haveI : CompactSpace (d.TorusQuot (d.torusOf x)) := hx.2.2
  refine ⟨(d.isSS_conj x g).mpr hx.1, ?_, ?_⟩
  · rw [d.torusOf_conj]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (hx.2.1 a ha b hb).map _
  · rw [d.torusOf_conj]
    exact (d.torusQuotConj (d.torusOf x) g).toHomeomorph.compactSpace

variable (ψ : NontrivialAddChar F)

/-- **The torus integral is invariant under conjugating the torus**, given that the germs are
(`hgerm`): for `x ∈ Γ(G,H)`, `X ↦ g X g⁻¹` carries `ν(T_x) dX` to `ν(g T_x g⁻¹) dX`
(`isExpCompatT_map_lieTorusConj`), `𝔱⁰_♮(T_x)` onto `𝔱⁰_♮(g T_x g⁻¹)`
(`isGammaEltLie_conj_iff`), and preserves `D^G` and `Δ` (`weylDiscLie_diagLie_conj`,
`deltaLie_conj`). -/
theorem torusIntegralLie_conj_of {θ' : ↥d.lieZero → ℂ} {x : ↥(GSpin d.QW)}
    (hx : d.IsGammaElt x) (g : ↥(GSpin d.QW))
    (hgerm : ∀ X : CliffordAlgebra d.QW, d.IsGammaEltLie (d.torusOf x) X →
      d.germLie0 ψ θ' (d.diagLie (((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X *
          (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)))
        (d.orbitChoiceLie (((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X *
          (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))) =
        d.germLie0 ψ θ' (d.diagLie X) (d.orbitChoiceLie X))
    (s : ℝ) :
    d.torusIntegralLie ψ θ' ((d.torusOf x).map (MulAut.conj g).toMonoidHom) s =
      d.torusIntegralLie ψ θ' (d.torusOf x) s := by
  haveI : CompactSpace (d.TorusQuot (d.torusOf x)) := hx.2.2
  obtain ⟨μ, hμ⟩ := d.exists_isExpCompatT ⟨_, x, hx, rfl⟩
  let c := d.lieTorusConj g (T := d.torusOf x) rfl
  let cM := c.toHomeomorph.toMeasurableEquiv
  have hmap : μ.map c = μ.map cM := rfl
  unfold torusIntegralLie
  rw [d.measLieTorus_eq (d.isExpCompatT_map_lieTorusConj g hμ), d.measLieTorus_eq hμ, hmap,
    integral_map_equiv]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  change d.gammaIntegrandLie ψ θ' _ s (((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) *
      (X : CliffordAlgebra d.QW) *
      (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) =
    d.gammaIntegrandLie ψ θ' (d.torusOf x) s X
  unfold gammaIntegrandLie
  by_cases h : d.IsGammaEltLie (d.torusOf x) X
  · rw [ite_eq_left ((d.isGammaEltLie_conj_iff g).mpr h), ite_eq_left h, hgerm _ h,
      d.weylDiscLie_diagLie_conj g X.2.1, d.deltaLie_conj g X.2.1.1]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((d.isGammaEltLie_conj_iff g).mp h'))]

end GGPData

end GSpinGGP
