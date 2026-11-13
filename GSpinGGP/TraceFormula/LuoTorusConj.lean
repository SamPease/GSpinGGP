/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LuoTorusIntegral

/-!
# Conjugating a torus of `Γ(G,H)`

For `g ∈ GSpin(W)(F)` and a subgroup `T`, with `T₁ = g T g⁻¹`:

* `specP_mem_commonFixed_map_conj`, `specP_inv_mem_commonFixed`: `W'_{T₁} = P(g) W'_T`;
* `conj_mem_lieTorus`, `lieTorusConj`: `X ↦ g X g⁻¹` maps `𝔱⁰(T)` onto `𝔱⁰(T₁)`;
* `isGammaEltLie_conj`: it maps `𝔱⁰_♮(T)` into `𝔱⁰_♮(T₁)`;
* `deltaLie_conj`, `weylDiscLie_conj`: `Δ` and `D^G` are conjugation invariant.
-/

noncomputable section

open MeasureTheory Topology Filter

set_option linter.style.haveILetI false

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

section WeylDisc

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] {A : Type*} [Ring A] [Algebra F A]
  [Module.Finite F A]

/-- **`D^G` is invariant under conjugation** by a unit `u` normalizing `𝔤`: `ad (u X u⁻¹)` on `𝔤`
is conjugate to `ad X` by `Ad u` (`LinearEquiv.charpoly_conj`). -/
theorem weylDiscLie_units_conj (𝔤 : LieSubalgebra F A) (u : Aˣ)
    (hu : ∀ Y ∈ 𝔤, (u : A) * Y * ((u⁻¹ : Aˣ) : A) ∈ 𝔤)
    (hu' : ∀ Y ∈ 𝔤, ((u⁻¹ : Aˣ) : A) * Y * (u : A) ∈ 𝔤) {X : A} (hX : X ∈ 𝔤) :
    weylDiscLie 𝔤 ((u : A) * X * ((u⁻¹ : Aˣ) : A)) = weylDiscLie 𝔤 X := by
  have hX' : (u : A) * X * ((u⁻¹ : Aˣ) : A) ∈ 𝔤 := hu X hX
  have h1 : ∀ Z ∈ 𝔤, ∀ Y ∈ 𝔤.toSubmodule,
      (LinearMap.mulLeft F Z - LinearMap.mulRight F Z) Y ∈ 𝔤.toSubmodule := by
    intro Z hZ Y hY
    have := 𝔤.lie_mem hZ hY
    rwa [Ring.lie_def] at this
  let c : ↥𝔤 ≃ₗ[F] ↥𝔤 :=
    { toFun := fun Y => ⟨(u : A) * Y * ((u⁻¹ : Aˣ) : A), hu _ Y.2⟩
      invFun := fun Y => ⟨((u⁻¹ : Aˣ) : A) * Y * (u : A), hu' _ Y.2⟩
      map_add' := fun Y Z => Subtype.ext (by simp [mul_add, add_mul])
      map_smul' := fun r Y => Subtype.ext (by simp)
      left_inv := fun Y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun Y => Subtype.ext (by simp [mul_assoc]) }
  unfold weylDiscLie
  rw [dite_eq_left (h1 _ hX'), dite_eq_left (h1 _ hX)]
  congr 2
  rw [← LinearEquiv.charpoly_conj c.symm]
  congr 1
  refine LinearMap.ext fun Y => Subtype.ext ?_
  change ((u⁻¹ : Aˣ) : A) * ((u : A) * X * ((u⁻¹ : Aˣ) : A) * ((u : A) * Y * ((u⁻¹ : Aˣ) : A)) -
      (u : A) * Y * ((u⁻¹ : Aˣ) : A) * ((u : A) * X * ((u⁻¹ : Aˣ) : A))) * (u : A) =
    X * Y - Y * X
  simp only [mul_sub, sub_mul, mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]

end WeylDisc


section DetRange

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The determinant of an endomorphism on its range is invariant under conjugation. -/
theorem LinearMap.det_restrict_range_conj (f : Module.End K V) (e : V ≃ₗ[K] V) :
    LinearMap.det ((e.conj f).restrict (p := LinearMap.range (e.conj f))
        (q := LinearMap.range (e.conj f)) (fun v _ => LinearMap.mem_range_self _ v)) =
      LinearMap.det (f.restrict (p := LinearMap.range f) (q := LinearMap.range f)
        (fun v _ => LinearMap.mem_range_self _ v)) := by
  let eR : ↥(LinearMap.range f) ≃ₗ[K] ↥(LinearMap.range (e.conj f)) :=
    { toFun := fun v => ⟨e v, by
        obtain ⟨u, hu⟩ := v.2
        exact ⟨e u, by rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, hu]⟩⟩
      invFun := fun w => ⟨e.symm w, by
        obtain ⟨u, hu⟩ := w.2
        exact ⟨e.symm u, by rw [← hu, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]⟩⟩
      map_add' := fun v w => Subtype.ext (map_add e _ _)
      map_smul' := fun c v => Subtype.ext (map_smul e c _)
      left_inv := fun v => Subtype.ext (e.symm_apply_apply _)
      right_inv := fun w => Subtype.ext (e.apply_symm_apply _) }
  rw [← LinearMap.det_conj _ eR]
  congr 1

end DetRange

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

local notation "uW" g => (((g : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)

/-- `P(g)` maps `W'_T` into `W'_{gTg⁻¹}`. -/
theorem specP_mem_commonFixed_map_conj {T : Subgroup ↥(GSpin d.QW)} (g : ↥(GSpin d.QW))
    {w : Fin d.m → F} (hw : w ∈ commonFixed T) :
    specP d.QW g w ∈ commonFixed (T.map (MulAut.conj g).toMonoidHom) := by
  refine (Submodule.mem_iInf _).mpr fun t₁ => ?_
  obtain ⟨_, t, ht, rfl⟩ := t₁
  have h := LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hw ⟨t, ht⟩)
  have h' : specP d.QW t w = w := by simpa [sub_eq_zero] using h
  have e : specP d.QW (g * t * g⁻¹) (specP d.QW g w) = specP d.QW g w := by
    have e1 : specP d.QW g⁻¹ (specP d.QW g w) = w := by
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    rw [map_mul, LinearEquiv.mul_apply, e1, map_mul, LinearEquiv.mul_apply, h']
  refine LinearMap.mem_ker.mpr ?_
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, LinearMap.sub_apply, LinearMap.id_coe,
    id_eq, LinearEquiv.coe_coe]
  rw [e, sub_self]

/-- `P(g)⁻¹` maps `W'_{gTg⁻¹}` into `W'_T`. -/
theorem specP_inv_mem_commonFixed {T : Subgroup ↥(GSpin d.QW)} (g : ↥(GSpin d.QW))
    {w : Fin d.m → F} (hw : w ∈ commonFixed (T.map (MulAut.conj g).toMonoidHom)) :
    specP d.QW g⁻¹ w ∈ commonFixed T := by
  have hT : (T.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = T := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id T
    ext t
    simp [mul_assoc]
  have := d.specP_mem_commonFixed_map_conj g⁻¹ hw
  rwa [hT] at this

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
    rw [hT', Subgroup.map_map]
    convert (Subgroup.map_id T).symm
    ext t
    simp [mul_assoc]
  let e : ↥(d.lieTorus T) ≃ₗ[F] ↥(d.lieTorus T') :=
    { toFun := fun X => ⟨_, hT' ▸ d.conj_mem_lieTorus g X.2⟩
      invFun := fun Y => ⟨((g⁻¹ : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) * (Y : CliffordAlgebra d.QW) *
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

theorem specP_inv_apply_specP (g : ↥(GSpin d.QW)) (w : Fin d.m → F) :
    specP d.QW g⁻¹ (specP d.QW g w) = w := by
  rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem specP_apply_specP_inv (g : ↥(GSpin d.QW)) (w : Fin d.m → F) :
    specP d.QW g (specP d.QW g⁻¹ w) = w := by
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl

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
        have := congrArg (specP d.QW g⁻¹) hv
        rwa [specP_inv_apply_specP, map_zero] at this
      have := d.specP_mem_commonFixed_map_conj g (hker ▸ (LinearMap.mem_ker.mpr h0))
      rwa [specP_apply_specP_inv] at this
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
  have key : ∀ f f' : Module.End F (Fin d.m → F), f' = (specP d.QW g).conj f →
      absF (LinearMap.det (f'.restrict (p := LinearMap.range f') (q := LinearMap.range f')
        (fun v _ => LinearMap.mem_range_self _ v))) =
      absF (LinearMap.det (f.restrict (p := LinearMap.range f) (q := LinearMap.range f)
        (fun v _ => LinearMap.mem_range_self _ v))) := by
    rintro f _ rfl
    rw [LinearMap.det_restrict_range_conj]
  exact key _ _ (d.adV_conj_eq_conj g hX)

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
  refine weylDiscLie_units_conj d.lieZero _ (fun Y hY => d.conj_mem_lie0 _ hY) (fun Y hY => ?_)
    (d.diagLie_mem_lieZero hX)
  have := d.conj_mem_lie0 (d.diag g)⁻¹ hY
  simp only [Subgroup.coe_inv, inv_inv] at this
  exact this

end GGPData

end GSpinGGP
