/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalGroups

/-!
# Isomorphisms of descent data at two semisimple elements

For semisimple `x ∈ G(F)` and `y ∈ G'(F)` (possibly in different groups), an `F`-isomorphism
`ι : G_x ≃ G'_y` (for instance `ι = ψ ∘ Ad(g)` for strongly stably conjugate `x`, `y`, Thesis §6.1)
induces a bijection `𝔤_x(F) ≃ 𝔤'_y(F)` and a bijection `G_x(F) ≃ G'_y(F)` compatible with all the
structure entering the local expansions of quasi-characters. `CentralizerIso` records exactly those
compatibilities, on the ambient algebras.

* `CentralizerIso.nilOrbitEquiv`: the induced bijection `Nil(𝔤_x) ≃ Nil(𝔤'_y)`;
* `CentralizerIso.nilOrbitEquiv_mem_nilReg_iff`: it maps `Nil_reg(𝔤_x)` onto `Nil_reg(𝔤'_y)`.

General lemmas: `conj_mem_lieCentralizer` (`G_x` preserves `𝔤_x`), `mk_mem_nilReg_iff` (the orbit of a
nilpotent `X` is regular iff `X` is).
-/

noncomputable section

open Topology

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
  {A : Type*} [Ring A] [Algebra F A] [TopologicalSpace A] [Module.Finite F A] [IsModuleTopology F A]
  {A' : Type*} [Ring A'] [Algebra F A'] [TopologicalSpace A'] [Module.Finite F A']
  [IsModuleTopology F A']

/-- Conjugation by `G_x(F)` preserves `𝔤_x` when conjugation by `G(F)` preserves `𝔤`. -/
theorem conj_mem_lieCentralizer {H : Subgroup Aˣ} {𝔥 : LieSubalgebra F A} {z : Aˣ}
    (hH : ∀ g ∈ H, ∀ Y ∈ 𝔥, (g : A) * Y * (↑g⁻¹ : A) ∈ 𝔥) {g : Aˣ} (hg : g ∈ grpCentralizer H z)
    {X : A} (hX : X ∈ lieCentralizer 𝔥 (z : A)) :
    (g : A) * X * (↑g⁻¹ : A) ∈ lieCentralizer 𝔥 (z : A) := by
  obtain ⟨hgH, hgz⟩ := hg
  have hc : (g : A) * (z : A) = (z : A) * g := by
    have := Subgroup.mem_centralizer_iff.mp hgz z rfl
    exact (congrArg Units.val this).symm
  have hc' : (↑g⁻¹ : A) * (z : A) = (z : A) * (↑g⁻¹ : A) := by
    have := Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hgz) z rfl
    exact (congrArg Units.val this).symm
  obtain ⟨hX𝔥, hXz⟩ := mem_lieCentralizer.mp hX
  refine mem_lieCentralizer.mpr ⟨hH g hgH X hX𝔥, ?_⟩
  calc (z : A) * ((g : A) * X * (↑g⁻¹ : A)) = (g : A) * ((z : A) * X) * (↑g⁻¹ : A) := by
        simp only [← mul_assoc, ← hc]
    _ = (g : A) * (X * (z : A)) * (↑g⁻¹ : A) := by rw [hXz]
    _ = (g : A) * X * (↑g⁻¹ : A) * (z : A) := by
        simp only [mul_assoc, ← hc']

/-- The orbit of a nilpotent `X` is regular iff `X` is regular nilpotent (when conjugation by `H`
preserves `𝔥`). -/
theorem mk_mem_nilReg_iff {H : Subgroup Aˣ} {𝔥 : LieSubalgebra F A}
    (hH : ∀ g ∈ H, ∀ Y ∈ 𝔥, (g : A) * Y * (↑g⁻¹ : A) ∈ 𝔥)
    (X : {X : A // X ∈ 𝔥 ∧ IsNilpotent X}) :
    Quotient.mk (nilSetoid H 𝔥) X ∈ NilReg H 𝔥 ↔ IsRegularNil 𝔥 X.1 := by
  refine ⟨fun h => ?_, mk_mem_nilReg_of_isRegularNil H 𝔥 hH X⟩
  obtain ⟨g, hgH, hgX⟩ := Quotient.exact (Quotient.out_eq (Quotient.mk (nilSetoid H 𝔥) X))
  refine ⟨X.2.1, X.2.2, ?_⟩
  have hg' : ∀ Y ∈ 𝔥, (↑g⁻¹ : A) * Y * (g : A) ∈ 𝔥 := fun Y hY => by
    simpa using hH g⁻¹ (H.inv_mem hgH) Y hY
  rw [← hgX, finrank_lieCentralizer_conj 𝔥 g (hH g hgH) hg']
  exact h.2.2

/-- **An isomorphism of the descent data at `x` and `y`**: an `F`-linear map of the ambient algebras
restricting to a bijection `𝔤_x(F) → 𝔤'_y(F)` that respects the commutator, the forms `b`, `b'`,
nilpotency, regular semisimplicity in `𝔤_x` and `𝔤'_y`, and the maps `Y ↦ e^Y X e^{-Y}`
(`orbitMap`), together with a bijection `G_x(F) → G'_y(F)` intertwining the adjoint actions.
This is what an isomorphism `G_x ≃ G'_y` defined over `F` (restriction of an isomorphism of the
ambient algebras over `F̄`) induces on `F`-points. -/
structure CentralizerIso (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A) (b : LinearMap.BilinForm F A)
    (G' : Subgroup A'ˣ) (𝔤' : LieSubalgebra F A') (b' : LinearMap.BilinForm F A')
    (x : Aˣ) (y : A'ˣ) where
  /-- The map on Lie algebras (only its values on `𝔤_x` matter). -/
  lin : A →ₗ[F] A'
  mapsTo : ∀ X ∈ lieCentralizer 𝔤 (x : A), lin X ∈ lieCentralizer 𝔤' (y : A')
  injOn : Set.InjOn lin (lieCentralizer 𝔤 (x : A))
  surjOn : ∀ X' ∈ lieCentralizer 𝔤' (y : A'), ∃ X ∈ lieCentralizer 𝔤 (x : A), lin X = X'
  map_commutator : ∀ X ∈ lieCentralizer 𝔤 (x : A), ∀ Y ∈ lieCentralizer 𝔤 (x : A),
    lin (X * Y - Y * X) = lin X * lin Y - lin Y * lin X
  map_bilin : ∀ X ∈ lieCentralizer 𝔤 (x : A), ∀ Y ∈ lieCentralizer 𝔤 (x : A),
    b' (lin X) (lin Y) = b X Y
  isNilpotent_iff : ∀ X ∈ lieCentralizer 𝔤 (x : A), IsNilpotent (lin X) ↔ IsNilpotent X
  isRegularSS_iff : ∀ X ∈ lieCentralizer 𝔤 (x : A),
    IsRegularSS (lieCentralizer 𝔤' (y : A')) (lin X) ↔ IsRegularSS (lieCentralizer 𝔤 (x : A)) X
  map_orbitMap : ∀ X ∈ lieCentralizer 𝔤 (x : A), ∀ Y ∈ lieCentralizer 𝔤 (x : A),
    lin (orbitMap F X Y) = orbitMap F (lin X) (lin Y)
  /-- The map on groups. -/
  grp : Aˣ → A'ˣ
  grp_mapsTo : ∀ g ∈ grpCentralizer G x, grp g ∈ grpCentralizer G' y
  grp_surjOn : ∀ g' ∈ grpCentralizer G' y, ∃ g ∈ grpCentralizer G x, grp g = g'
  map_conj : ∀ g ∈ grpCentralizer G x, ∀ X ∈ lieCentralizer 𝔤 (x : A),
    lin ((g : A) * X * (↑g⁻¹ : A)) = (grp g : A') * lin X * (↑(grp g)⁻¹ : A')

namespace CentralizerIso

variable {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A} {b : LinearMap.BilinForm F A}
  {G' : Subgroup A'ˣ} {𝔤' : LieSubalgebra F A'} {b' : LinearMap.BilinForm F A'}
  {x : Aˣ} {y : A'ˣ} (ι : CentralizerIso G 𝔤 b G' 𝔤' b' x y)

/-- The map on nilpotent elements of `𝔤_x`. -/
def nilMap (X : {X : A // X ∈ lieCentralizer 𝔤 (x : A) ∧ IsNilpotent X}) :
    {X' : A' // X' ∈ lieCentralizer 𝔤' (y : A') ∧ IsNilpotent X'} :=
  ⟨ι.lin X.1, ι.mapsTo _ X.2.1, (ι.isNilpotent_iff _ X.2.1).mpr X.2.2⟩

/-- The induced map `Nil(𝔤_x) → Nil(𝔤'_y)`. -/
def nilOrbitMap : NilOrbit (grpCentralizer G x) (lieCentralizer 𝔤 (x : A)) →
    NilOrbit (grpCentralizer G' y) (lieCentralizer 𝔤' (y : A')) :=
  Quotient.map ι.nilMap fun X Y ⟨g, hg, h⟩ =>
    ⟨ι.grp g, ι.grp_mapsTo g hg, by
      show (ι.grp g : A') * ι.lin X.1 * (↑(ι.grp g)⁻¹ : A') = ι.lin Y.1
      rw [← ι.map_conj g hg X.1 X.2.1, h]⟩

theorem nilOrbitMap_mk (X : {X : A // X ∈ lieCentralizer 𝔤 (x : A) ∧ IsNilpotent X}) :
    ι.nilOrbitMap (Quotient.mk _ X) = Quotient.mk _ (ι.nilMap X) := rfl

theorem nilOrbitMap_bijective (hG : ∀ g ∈ G, ∀ Y ∈ 𝔤, (g : A) * Y * (↑g⁻¹ : A) ∈ 𝔤) :
    Function.Bijective ι.nilOrbitMap := by
  constructor
  · intro O₁ O₂
    induction O₁ using Quotient.inductionOn with | h X => ?_
    induction O₂ using Quotient.inductionOn with | h Y => ?_
    intro h
    obtain ⟨g', hg', hgXY⟩ := Quotient.exact h
    obtain ⟨g, hg, rfl⟩ := ι.grp_surjOn g' hg'
    refine Quotient.sound ⟨g, hg, ι.injOn (conj_mem_lieCentralizer hG hg X.2.1) Y.2.1 ?_⟩
    rw [ι.map_conj g hg X.1 X.2.1]
    exact hgXY
  · intro O'
    induction O' using Quotient.inductionOn with | h X' => ?_
    obtain ⟨X, hX, hXX'⟩ := ι.surjOn X'.1 X'.2.1
    have hn : IsNilpotent X := (ι.isNilpotent_iff X hX).mp (hXX' ▸ X'.2.2)
    exact ⟨Quotient.mk _ ⟨X, hX, hn⟩, congrArg (Quotient.mk _) (Subtype.ext hXX')⟩

/-- The induced bijection `Nil(𝔤_x) ≃ Nil(𝔤'_y)`, when conjugation by `G(F)` preserves `𝔤`. -/
def nilOrbitEquiv (hG : ∀ g ∈ G, ∀ Y ∈ 𝔤, (g : A) * Y * (↑g⁻¹ : A) ∈ 𝔤) :
    NilOrbit (grpCentralizer G x) (lieCentralizer 𝔤 (x : A)) ≃
      NilOrbit (grpCentralizer G' y) (lieCentralizer 𝔤' (y : A')) :=
  Equiv.ofBijective _ (ι.nilOrbitMap_bijective hG)

/-- `ι` maps the centralizer of `X` in `𝔤_x` onto the centralizer of `ι X` in `𝔤'_y`. -/
theorem map_lieCentralizer {X : A} (hX : X ∈ lieCentralizer 𝔤 (x : A)) :
    (lieCentralizer (lieCentralizer 𝔤 (x : A)) X).toSubmodule.map ι.lin =
      (lieCentralizer (lieCentralizer 𝔤' (y : A')) (ι.lin X)).toSubmodule := by
  ext Z'
  simp only [Submodule.mem_map, LieSubalgebra.mem_toSubmodule]
  rw [mem_lieCentralizer]
  constructor
  · rintro ⟨Z, hZ', rfl⟩
    obtain ⟨hZ, hZX⟩ := mem_lieCentralizer.mp hZ'
    change Z ∈ lieCentralizer 𝔤 (x : A) at hZ
    refine ⟨ι.mapsTo Z hZ, ?_⟩
    have := ι.map_commutator X hX Z hZ
    rw [hZX, sub_self, map_zero] at this
    exact sub_eq_zero.mp this.symm
  · rintro ⟨hZ', hZX'⟩
    obtain ⟨Z, hZ, rfl⟩ := ι.surjOn Z' hZ'
    refine ⟨Z, mem_lieCentralizer.mpr ⟨hZ, ?_⟩, rfl⟩
    have hmem : X * Z - Z * X ∈ lieCentralizer 𝔤 (x : A) := by
      have := (lieCentralizer 𝔤 (x : A)).lie_mem hX hZ
      rwa [Ring.lie_def] at this
    have h0 := ι.injOn hmem (zero_mem _) (by
      rw [ι.map_commutator X hX Z hZ, hZX', sub_self, map_zero])
    exact sub_eq_zero.mp h0

/-- `dim 𝔤'_{y, ι X} = dim 𝔤_{x, X}`. -/
theorem finrank_lieCentralizer {X : A} (hX : X ∈ lieCentralizer 𝔤 (x : A)) :
    Module.finrank F ↥(lieCentralizer (lieCentralizer 𝔤' (y : A')) (ι.lin X)) =
      Module.finrank F ↥(lieCentralizer (lieCentralizer 𝔤 (x : A)) X) := by
  set S := (lieCentralizer (lieCentralizer 𝔤 (x : A)) X).toSubmodule
  have hinj : Function.Injective (ι.lin ∘ₗ S.subtype) := fun Z₁ Z₂ h => by
    have hS : ∀ Z : ↥S, (Z : A) ∈ lieCentralizer 𝔤 (x : A) := fun Z =>
      (mem_lieCentralizer.mp Z.2).1
    exact Subtype.ext (ι.injOn (hS Z₁) (hS Z₂) h)
  have h := LinearMap.finrank_range_of_inj hinj
  rw [LinearMap.range_comp, Submodule.range_subtype, ι.map_lieCentralizer hX] at h
  exact h

include ι in
/-- `rank 𝔤'_y = rank 𝔤_x`. -/
theorem lieRank_eq : lieRank (lieCentralizer 𝔤' (y : A')) = lieRank (lieCentralizer 𝔤 (x : A)) := by
  have hbij : Function.Bijective (fun X : ↥(lieCentralizer 𝔤 (x : A)) =>
      (⟨ι.lin X, ι.mapsTo _ X.2⟩ : ↥(lieCentralizer 𝔤' (y : A')))) :=
    ⟨fun X₁ X₂ h => Subtype.ext (ι.injOn X₁.2 X₂.2 (congrArg Subtype.val h)), fun X' => by
      obtain ⟨X, hX, hXX'⟩ := ι.surjOn X'.1 X'.2
      exact ⟨⟨X, hX⟩, Subtype.ext hXX'⟩⟩
  unfold lieRank
  rw [← (Equiv.ofBijective _ hbij).iInf_comp]
  exact iInf_congr fun X => ι.finrank_lieCentralizer X.2

/-- Regular nilpotent elements correspond. -/
theorem isRegularNil_iff {X : A} (hX : X ∈ lieCentralizer 𝔤 (x : A)) :
    IsRegularNil (lieCentralizer 𝔤' (y : A')) (ι.lin X) ↔
      IsRegularNil (lieCentralizer 𝔤 (x : A)) X := by
  unfold IsRegularNil
  rw [ι.finrank_lieCentralizer hX, ι.lieRank_eq, ι.isNilpotent_iff X hX]
  exact ⟨fun h => ⟨hX, h.2⟩, fun h => ⟨ι.mapsTo X hX, h.2⟩⟩

/-- The bijection `Nil(𝔤_x) ≃ Nil(𝔤'_y)` maps `Nil_reg(𝔤_x)` onto `Nil_reg(𝔤'_y)`. -/
theorem nilOrbitEquiv_mem_nilReg_iff (hG : ∀ g ∈ G, ∀ Y ∈ 𝔤, (g : A) * Y * (↑g⁻¹ : A) ∈ 𝔤)
    (hG' : ∀ g ∈ G', ∀ Y ∈ 𝔤', (g : A') * Y * (↑g⁻¹ : A') ∈ 𝔤')
    (O : NilOrbit (grpCentralizer G x) (lieCentralizer 𝔤 (x : A))) :
    ι.nilOrbitEquiv hG O ∈ NilReg _ _ ↔ O ∈ NilReg _ _ := by
  induction O using Quotient.inductionOn with | h X => ?_
  have hGx : ∀ g ∈ grpCentralizer G x, ∀ Y ∈ lieCentralizer 𝔤 (x : A),
      (g : A) * Y * (↑g⁻¹ : A) ∈ lieCentralizer 𝔤 (x : A) := fun g hg Y hY =>
    conj_mem_lieCentralizer hG hg hY
  have hGy : ∀ g ∈ grpCentralizer G' y, ∀ Y ∈ lieCentralizer 𝔤' (y : A'),
      (g : A') * Y * (↑g⁻¹ : A') ∈ lieCentralizer 𝔤' (y : A') := fun g hg Y hY =>
    conj_mem_lieCentralizer hG' hg hY
  show Quotient.mk _ (ι.nilMap X) ∈ NilReg _ _ ↔ Quotient.mk _ X ∈ NilReg _ _
  rw [mk_mem_nilReg_iff hGy, mk_mem_nilReg_iff hGx]
  exact ι.isRegularNil_iff X.2.1

/-- The restriction `𝔤_x(F) → 𝔤'_y(F)` as a linear map. -/
def linRestrict : ↥(lieCentralizer 𝔤 (x : A)).toSubmodule →ₗ[F]
    ↥(lieCentralizer 𝔤' (y : A')).toSubmodule :=
  (ι.lin.domRestrict (lieCentralizer 𝔤 (x : A)).toSubmodule).codRestrict _
    fun X => ι.mapsTo _ X.property

theorem linRestrict_bijective : Function.Bijective ι.linRestrict :=
  ⟨fun X₁ X₂ h => Subtype.ext (ι.injOn X₁.property X₂.property (congrArg Subtype.val h)),
    fun X' => by
      obtain ⟨X, hX, hXX'⟩ := ι.surjOn X'.1 X'.property
      exact ⟨⟨X, hX⟩, Subtype.ext hXX'⟩⟩

/-- The bijection `𝔤_x(F) ≃ 𝔤'_y(F)` as a linear equivalence. -/
def linEquiv : ↥(lieCentralizer 𝔤 (x : A)).toSubmodule ≃ₗ[F]
    ↥(lieCentralizer 𝔤' (y : A')).toSubmodule :=
  LinearEquiv.ofBijective ι.linRestrict ι.linRestrict_bijective

/-- **`ι⁻¹` is continuous at `0`**: for every neighbourhood `U` of `0` in `A` there is a
neighbourhood `U'` of `0` in `A'` with `X ∈ U` whenever `X ∈ 𝔤_x` and `ι X ∈ U'` (finite
dimension). -/
theorem exists_nhds_of_mem_nhds {U : Set A} (hU : U ∈ 𝓝 (0 : A)) :
    ∃ U' ∈ 𝓝 (0 : A'), ∀ X ∈ lieCentralizer 𝔤 (x : A), ι.lin X ∈ U' → X ∈ U := by
  have := t2Space_of_moduleTopology F A
  have := t2Space_of_moduleTopology F A'
  have := isTopologicalRing_of_moduleTopology F A
  have := isTopologicalRing_of_moduleTopology F A'
  set e := ι.linEquiv with he_def
  have hcont : Continuous e.symm := LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap
  have h1 : (Subtype.val ⁻¹' U : Set ↥(lieCentralizer 𝔤 (x : A)).toSubmodule) ∈ 𝓝 0 :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using hU)
  have h2 : (e.symm ⁻¹' (Subtype.val ⁻¹' U)) ∈ 𝓝 (0 : ↥(lieCentralizer 𝔤' (y : A')).toSubmodule) :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using h1)
  obtain ⟨U', hU', hsub⟩ := (mem_nhds_subtype _ _ _).mp h2
  refine ⟨U', by simpa using hU', fun X hX hXU' => ?_⟩
  have h3 := hsub (show (⟨ι.lin X, ι.mapsTo X hX⟩ : ↥(lieCentralizer 𝔤' (y : A')).toSubmodule) ∈
    Subtype.val ⁻¹' U' from hXU')
  have he : e.symm ⟨ι.lin X, ι.mapsTo X hX⟩ = ⟨X, hX⟩ := e.symm_apply_eq.mpr rfl
  simpa [he] using h3

end CentralizerIso

end GSpinGGP
