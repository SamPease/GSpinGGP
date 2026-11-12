/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalGroups
import GSpinGGP.Foundations.LieEquivAd

/-!
# Isomorphisms of descent data at two semisimple elements

For semisimple `x ∈ G(F)` and `y ∈ G'(F)` (possibly in different groups), an `F`-isomorphism
`ι : G_x ≃ G'_y` (for instance `ι = ψ ∘ Ad(g)` for strongly stably conjugate `x`, `y`, Thesis §6.1)
induces a bijection `𝔤_x(F) ≃ 𝔤'_y(F)` and a bijection `G_x(F) ≃ G'_y(F)` compatible with all the
structure entering the local expansions of quasi-characters. `CentralizerIso` records exactly those
compatibilities, on the ambient algebras.

* `CentralizerIso.nilOrbitEquiv`: the induced bijection `Nil(𝔤_x) ≃ Nil(𝔤'_y)`;
* `CentralizerIso.nilOrbitEquiv_mem_nilReg_iff`: it maps `Nil_reg(𝔤_x)` onto `Nil_reg(𝔤'_y)`.
* `CentralizerIso.lieEquiv`: the Lie algebra isomorphism `𝔤_x(F) ≃ 𝔤'_y(F)`;
* `CentralizerIso.linEquiv_lie`, `ker_ad_linEquiv`, `kirillovForm_linEquiv`,
  `linEquiv_mem_nilOrbitSet_iff`, `preimage_conjAd_image`, `preimage_orbitMap_image`: the structure
  entering orbit measures (bracket, centralizers, Kirillov forms, orbits, adjoint action, charts)
  is transported.
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
  bijOn : Set.BijOn lin (lieCentralizer 𝔤 (x : A)) (lieCentralizer 𝔤' (y : A'))
  map_commutator : ∀ X ∈ lieCentralizer 𝔤 (x : A), ∀ Y ∈ lieCentralizer 𝔤 (x : A),
    lin (X * Y - Y * X) = lin X * lin Y - lin Y * lin X
  map_bilin : ∀ X ∈ lieCentralizer 𝔤 (x : A), ∀ Y ∈ lieCentralizer 𝔤 (x : A),
    b' (lin X) (lin Y) = b X Y
  isNilpotent_iff : ∀ X ∈ lieCentralizer 𝔤 (x : A), IsNilpotent (lin X) ↔ IsNilpotent X
  isRegularSS_iff : ∀ X ∈ lieCentralizer 𝔤 (x : A),
    IsRegularSS (lieCentralizer 𝔤' (y : A')) (lin X) ↔ IsRegularSS (lieCentralizer 𝔤 (x : A)) X
  /-- `ι(e^Y X e^{-Y}) = e^{ι Y} ι(X) e^{-ι Y}`. Where the exponential series of `Y` diverges,
  `expA` is `0` and so is that of `ι Y` (`ι` is the restriction of an algebra isomorphism over `F̄`,
  so `Y`, `ι Y` have the same spectral radius), and both sides are `0`. -/
  map_orbitMap : ∀ X ∈ lieCentralizer 𝔤 (x : A), ∀ Y ∈ lieCentralizer 𝔤 (x : A),
    lin (orbitMap F X Y) = orbitMap F (lin X) (lin Y)
  /-- The map on groups. -/
  grp : Aˣ → A'ˣ
  grp_mapsTo : Set.MapsTo grp (grpCentralizer G x) (grpCentralizer G' y)
  grp_surjOn : Set.SurjOn grp (grpCentralizer G x) (grpCentralizer G' y)
  map_conj : ∀ g ∈ grpCentralizer G x, ∀ X ∈ lieCentralizer 𝔤 (x : A),
    lin ((g : A) * X * (↑g⁻¹ : A)) = (grp g : A') * lin X * (↑(grp g)⁻¹ : A')

namespace CentralizerIso

variable {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A} {b : LinearMap.BilinForm F A}
  {G' : Subgroup A'ˣ} {𝔤' : LieSubalgebra F A'} {b' : LinearMap.BilinForm F A'}
  {x : Aˣ} {y : A'ˣ} (ι : CentralizerIso G 𝔤 b G' 𝔤' b' x y)

/-- The map on nilpotent elements of `𝔤_x`. -/
def nilMap (X : {X : A // X ∈ lieCentralizer 𝔤 (x : A) ∧ IsNilpotent X}) :
    {X' : A' // X' ∈ lieCentralizer 𝔤' (y : A') ∧ IsNilpotent X'} :=
  ⟨ι.lin X.1, ι.bijOn.mapsTo X.2.1, (ι.isNilpotent_iff _ X.2.1).mpr X.2.2⟩

/-- The induced map `Nil(𝔤_x) → Nil(𝔤'_y)`. -/
def nilOrbitMap : NilOrbit (grpCentralizer G x) (lieCentralizer 𝔤 (x : A)) →
    NilOrbit (grpCentralizer G' y) (lieCentralizer 𝔤' (y : A')) :=
  Quotient.map ι.nilMap fun X Y ⟨g, hg, h⟩ =>
    ⟨ι.grp g, ι.grp_mapsTo hg, by
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
    obtain ⟨g, hg, rfl⟩ := ι.grp_surjOn hg'
    refine Quotient.sound ⟨g, hg, ι.bijOn.injOn (conj_mem_lieCentralizer hG hg X.2.1) Y.2.1 ?_⟩
    rw [ι.map_conj g hg X.1 X.2.1]
    exact hgXY
  · intro O'
    induction O' using Quotient.inductionOn with | h X' => ?_
    obtain ⟨X, hX, hXX'⟩ := ι.bijOn.surjOn X'.2.1
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
    refine ⟨ι.bijOn.mapsTo hZ, ?_⟩
    have := ι.map_commutator X hX Z hZ
    rw [hZX, sub_self, map_zero] at this
    exact sub_eq_zero.mp this.symm
  · rintro ⟨hZ', hZX'⟩
    obtain ⟨Z, hZ, rfl⟩ := ι.bijOn.surjOn hZ'
    refine ⟨Z, mem_lieCentralizer.mpr ⟨hZ, ?_⟩, rfl⟩
    have hmem : X * Z - Z * X ∈ lieCentralizer 𝔤 (x : A) := by
      have := (lieCentralizer 𝔤 (x : A)).lie_mem hX hZ
      rwa [Ring.lie_def] at this
    have h0 := ι.bijOn.injOn hmem (zero_mem _) (by
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
    exact Subtype.ext (ι.bijOn.injOn (hS Z₁) (hS Z₂) h)
  have h := LinearMap.finrank_range_of_inj hinj
  rw [LinearMap.range_comp, Submodule.range_subtype, ι.map_lieCentralizer hX] at h
  exact h

include ι in
/-- `rank 𝔤'_y = rank 𝔤_x`. -/
theorem lieRank_eq : lieRank (lieCentralizer 𝔤' (y : A')) = lieRank (lieCentralizer 𝔤 (x : A)) := by
  have hbij : Function.Bijective (fun X : ↥(lieCentralizer 𝔤 (x : A)) =>
      (⟨ι.lin X, ι.bijOn.mapsTo X.2⟩ : ↥(lieCentralizer 𝔤' (y : A')))) :=
    ⟨fun X₁ X₂ h => Subtype.ext (ι.bijOn.injOn X₁.2 X₂.2 (congrArg Subtype.val h)), fun X' => by
      obtain ⟨X, hX, hXX'⟩ := ι.bijOn.surjOn X'.2
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
  exact ⟨fun h => ⟨hX, h.2⟩, fun h => ⟨ι.bijOn.mapsTo hX, h.2⟩⟩

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

/-- The bijection `𝔤_x(F) ≃ 𝔤'_y(F)` as a linear equivalence. -/
def linEquiv : ↥(lieCentralizer 𝔤 (x : A)) ≃ₗ[F] ↥(lieCentralizer 𝔤' (y : A')) :=
  LinearEquiv.ofBijective (ι.lin.restrict fun _ hX => ι.bijOn.mapsTo hX)
    ⟨fun X₁ X₂ h => Subtype.ext (ι.bijOn.injOn X₁.property X₂.property (congrArg Subtype.val h)),
      fun X' => by
        obtain ⟨X, hX, hXX'⟩ := ι.bijOn.surjOn X'.property
        exact ⟨⟨X, hX⟩, Subtype.ext hXX'⟩⟩

@[simp] theorem linEquiv_apply (X : ↥(lieCentralizer 𝔤 (x : A))) :
    (ι.linEquiv X : A') = ι.lin X := rfl

/-- `ι` respects the Lie bracket of `𝔤_x`. -/
theorem linEquiv_lie (X Z : ↥(lieCentralizer 𝔤 (x : A))) :
    ι.linEquiv ⁅X, Z⁆ = ⁅ι.linEquiv X, ι.linEquiv Z⁆ :=
  Subtype.ext (by
    simp only [linEquiv_apply, LieSubalgebra.coe_bracket, Ring.lie_def]
    exact ι.map_commutator X X.2 Z Z.2)

/-- The bijection `𝔤_x(F) ≃ 𝔤'_y(F)` as an isomorphism of Lie algebras. -/
def lieEquiv : ↥(lieCentralizer 𝔤 (x : A)) ≃ₗ⁅F⁆ ↥(lieCentralizer 𝔤' (y : A')) :=
  { ι.linEquiv with map_lie' := fun {X Z} => ι.linEquiv_lie X Z }

/-- `ι` maps the centralizer `ker(ad X)` of `X` in `𝔤_x` onto that of `ι X` in `𝔤'_y`
(`LieAlgebra.ker_ad_lieEquiv` for `lieEquiv`). -/
theorem ker_ad_linEquiv (X : ↥(lieCentralizer 𝔤 (x : A))) :
    LinearMap.ker (LieAlgebra.ad F ↥(lieCentralizer 𝔤' (y : A')) (ι.linEquiv X)) =
      (LinearMap.ker (LieAlgebra.ad F ↥(lieCentralizer 𝔤 (x : A)) X)).map
        (ι.linEquiv : ↥(lieCentralizer 𝔤 (x : A)) →ₗ[F] ↥(lieCentralizer 𝔤' (y : A'))) :=
  LieAlgebra.ker_ad_lieEquiv ι.lieEquiv X

/-- `ι` carries the Kirillov form `b(·, [X, ·])` on `𝔤_x` to `b'(·, [ι X, ·])` on `𝔤'_y`. -/
theorem kirillovForm_linEquiv (X Y Z : ↥(lieCentralizer 𝔤 (x : A))) :
    kirillovForm (lieCentralizer 𝔤' (y : A')) b' (ι.linEquiv X) (ι.linEquiv Y) (ι.linEquiv Z) =
      kirillovForm (lieCentralizer 𝔤 (x : A)) b X Y Z := by
  simp only [kirillovForm, LinearMap.compl₂_apply, LieAlgebra.ad_apply, ← ι.linEquiv_lie]
  exact ι.map_bilin _ Y.2 _ (⁅X, Z⁆ : ↥(lieCentralizer 𝔤 (x : A))).2

/-- `ι X` lies in the orbit `ι O` iff `X` lies in `O`. -/
theorem linEquiv_mem_nilOrbitSet_iff (hG : ∀ g ∈ G, ∀ Y ∈ 𝔤, (g : A) * Y * (↑g⁻¹ : A) ∈ 𝔤)
    (O : NilOrbit (grpCentralizer G x) (lieCentralizer 𝔤 (x : A)))
    (X : ↥(lieCentralizer 𝔤 (x : A))) :
    ι.linEquiv X ∈ nilOrbitSet (ι.nilOrbitEquiv hG O) ↔ X ∈ nilOrbitSet O := by
  constructor
  · rintro ⟨hn', hq'⟩
    exact ⟨(ι.isNilpotent_iff X X.2).mp hn', (ι.nilOrbitMap_bijective hG).1 hq'⟩
  · rintro ⟨hn, rfl⟩
    exact ⟨(ι.isNilpotent_iff X X.2).mpr hn, rfl⟩

/-- Conjugation by `g ∈ G_x(F)` on `𝔤_x` corresponds under `ι` to conjugation by `ι g` on
`𝔤'_y`, as an identity of preimages. -/
theorem preimage_conjAd_image (hG : ∀ g ∈ G, ∀ Y ∈ 𝔤, (g : A) * Y * (↑g⁻¹ : A) ∈ 𝔤)
    {g : Aˣ} (hg : g ∈ grpCentralizer G x) (S' : Set ↥(lieCentralizer 𝔤' (y : A'))) :
    ι.linEquiv ⁻¹' (Subtype.val ⁻¹' (conjAd F (ι.grp g) ⁻¹' (Subtype.val '' S'))) =
      Subtype.val ⁻¹' (conjAd F g ⁻¹' (Subtype.val '' (ι.linEquiv ⁻¹' S'))) := by
  ext Z
  simp only [Set.mem_preimage, Set.mem_image]
  have hZ : (g : A) * Z * (↑g⁻¹ : A) ∈ lieCentralizer 𝔤 (x : A) :=
    conj_mem_lieCentralizer hG hg Z.2
  have hc : conjAd F (ι.grp g) ((ι.linEquiv Z : ↥(lieCentralizer 𝔤' (y : A'))) : A') =
      ι.lin ((g : A) * Z * (↑g⁻¹ : A)) := (ι.map_conj g hg Z Z.2).symm
  have hc' : conjAd F g (Z : A) = (g : A) * Z * (↑g⁻¹ : A) := rfl
  rw [hc, hc']
  constructor
  · rintro ⟨s', hs', he⟩
    refine ⟨⟨_, hZ⟩, ?_, rfl⟩
    convert hs'
    exact Subtype.ext he.symm
  · rintro ⟨s, hs, he⟩
    exact ⟨_, hs, by rw [linEquiv_apply, he]⟩

/-- `ι` carries the chart `Y ↦ e^Y X e^{-Y}` on a subspace `C ⊆ 𝔤_x` to the chart at `ι X` on
`ι C`, as an identity of preimages, on sets `S` on which the chart stays in `𝔤_x`. -/
theorem preimage_orbitMap_image (X : ↥(lieCentralizer 𝔤 (x : A)))
    (C : Submodule F ↥(lieCentralizer 𝔤 (x : A))) (S : Set ↥C)
    (hS : ∀ Y ∈ S, orbitMap F (X : A) ((Y : ↥(lieCentralizer 𝔤 (x : A))) : A) ∈
      lieCentralizer 𝔤 (x : A)) :
    ι.linEquiv ⁻¹' (Subtype.val ⁻¹'
        ((fun Y' : ↥(C.map (ι.linEquiv :
            ↥(lieCentralizer 𝔤 (x : A)) →ₗ[F] ↥(lieCentralizer 𝔤' (y : A')))) ↦
          orbitMap F ((ι.linEquiv X : ↥(lieCentralizer 𝔤' (y : A'))) : A')
            ((Y' : ↥(lieCentralizer 𝔤' (y : A'))) : A')) ''
          (ι.linEquiv.submoduleMap C '' S))) =
      Subtype.val ⁻¹' ((fun Y : ↥C ↦ orbitMap F (X : A) ((Y : ↥(lieCentralizer 𝔤 (x : A))) : A)) ''
        S) := by
  ext Z
  simp only [Set.mem_preimage, Set.mem_image, exists_exists_and_eq_and,
    LinearEquiv.submoduleMap_apply, linEquiv_apply]
  constructor
  · rintro ⟨Y, hY, he⟩
    refine ⟨Y, hY, ι.bijOn.injOn (hS Y hY) Z.2 ?_⟩
    rw [ι.map_orbitMap _ X.2 _ (Y : ↥(lieCentralizer 𝔤 (x : A))).2, he]
  · rintro ⟨Y, hY, he⟩
    exact ⟨Y, hY, by rw [← ι.map_orbitMap _ X.2 _ (Y : ↥(lieCentralizer 𝔤 (x : A))).2, he]⟩

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
  have hind : IsInducing (Subtype.val : ↥(lieCentralizer 𝔤 (x : A)) → A) :=
    IsInducing.subtypeVal
  have : IsTopologicalAddGroup ↥(lieCentralizer 𝔤 (x : A)) :=
    hind.isTopologicalAddGroup (lieCentralizer 𝔤 (x : A)).incl.toLinearMap
  have : ContinuousSMul F ↥(lieCentralizer 𝔤 (x : A)) :=
    hind.continuousSMul continuous_id
      (fun {c X} => (lieCentralizer 𝔤 (x : A)).incl.toLinearMap.map_smul c X)
  have hind' : IsInducing (Subtype.val : ↥(lieCentralizer 𝔤' (y : A')) → A') :=
    IsInducing.subtypeVal
  have : IsTopologicalAddGroup ↥(lieCentralizer 𝔤' (y : A')) :=
    hind'.isTopologicalAddGroup (lieCentralizer 𝔤' (y : A')).incl.toLinearMap
  have : ContinuousSMul F ↥(lieCentralizer 𝔤' (y : A')) :=
    hind'.continuousSMul continuous_id
      (fun {c X} => (lieCentralizer 𝔤' (y : A')).incl.toLinearMap.map_smul c X)
  have hcont : Continuous e.symm := LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap
  have h1 : (Subtype.val ⁻¹' U : Set ↥(lieCentralizer 𝔤 (x : A))) ∈ 𝓝 0 :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using hU)
  have h2 : (e.symm ⁻¹' (Subtype.val ⁻¹' U)) ∈ 𝓝 (0 : ↥(lieCentralizer 𝔤' (y : A'))) :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using h1)
  obtain ⟨U', hU', hsub⟩ := (mem_nhds_subtype _ _ _).mp h2
  refine ⟨U', by simpa using hU', fun X hX hXU' => ?_⟩
  have h3 := hsub (show (⟨ι.lin X, ι.bijOn.mapsTo hX⟩ : ↥(lieCentralizer 𝔤' (y : A'))) ∈
    Subtype.val ⁻¹' U' from hXU')
  have he : e.symm ⟨ι.lin X, ι.bijOn.mapsTo hX⟩ = ⟨X, hX⟩ := e.symm_apply_eq.mpr rfl
  simpa [he] using h3

end CentralizerIso

end GSpinGGP
