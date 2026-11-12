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

/-! ### Construction from a partial algebra isomorphism -/

section OfSubalgebra

variable {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A} {b : LinearMap.BilinForm F A}
  {G' : Subgroup A'ˣ} {𝔤' : LieSubalgebra F A'} {b' : LinearMap.BilinForm F A'}
  {x : Aˣ} {y : A'ˣ}

/-- A linear map that is multiplicative on a subalgebra commutes with powers there. -/
theorem map_pow_of_mul {S : Subalgebra F A} {f : A →ₗ[F] A'} (hone : f 1 = 1)
    (hmul : ∀ a ∈ S, ∀ c ∈ S, f (a * c) = f a * f c) {X : A} (hX : X ∈ S) (n : ℕ) :
    f (X ^ n) = f X ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, hone]
  | succ n ih => rw [pow_succ, hmul _ (S.pow_mem hX n) _ hX, ih, pow_succ]

/-- A linear map that is multiplicative and unital on a subalgebra commutes with `aeval` there. -/
theorem map_aeval_of_mul {S : Subalgebra F A} {f : A →ₗ[F] A'} (hone : f 1 = 1)
    (hmul : ∀ a ∈ S, ∀ c ∈ S, f (a * c) = f a * f c) {X : A} (hX : X ∈ S) (p : Polynomial F) :
    f (Polynomial.aeval X p) = Polynomial.aeval (f X) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, smul_mul_assoc, one_mul, one_mul, map_smul,
      map_pow_of_mul hone hmul hX]

/-- `p(x) = 0` for `p` the minimal polynomial of left multiplication by `x`. -/
theorem aeval_minpoly_mulLeft (X : A) :
    Polynomial.aeval X (minpoly F (LinearMap.mulLeft F X)) = 0 := by
  have h := Polynomial.aeval_algHom_apply (Algebra.lmul F A) X (minpoly F (LinearMap.mulLeft F X))
  have h0 : Polynomial.aeval (Algebra.lmul F A X) (minpoly F (LinearMap.mulLeft F X)) = 0 :=
    minpoly.aeval F _
  rw [h0] at h
  have := LinearMap.congr_fun h.symm 1
  simpa using this

/-- **`exp` commutes with a linear map preserving the powers of `X`** and admitting a linear left
inverse on them: `f(e^X) = e^{f X}`, also where the exponential series of `X` diverges (both sides
are `0`: the series of `f X` diverges too, since `r` maps it back to that of `X`). -/
theorem map_expA_of_leftInverse (f : A →ₗ[F] A') (r : A' →ₗ[F] A) {X : A}
    (hpow : ∀ n : ℕ, f (X ^ n) = f X ^ n) (hr : ∀ n : ℕ, r (f (X ^ n)) = X ^ n) :
    f (expA F X) = expA F (f X) := by
  have := isTopologicalRing_of_moduleTopology F A
  have := isTopologicalRing_of_moduleTopology F A'
  have := t2Space_of_moduleTopology F A
  have := t2Space_of_moduleTopology F A'
  have hfc : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have hrc : Continuous r := IsModuleTopology.continuous_of_linearMap r
  rw [expA, expA, NormedSpace.exp_eq_tsum F, NormedSpace.exp_eq_tsum F]
  beta_reduce
  have hterm : ∀ n : ℕ, f (((n.factorial : F)⁻¹) • X ^ n) = ((n.factorial : F)⁻¹) • f X ^ n :=
    fun n => by rw [map_smul, hpow]
  by_cases hs : Summable fun n : ℕ => ((n.factorial : F)⁻¹) • X ^ n
  · have h := hs.hasSum.map f hfc
    simp only [Function.comp_def, hterm] at h
    exact h.tsum_eq.symm
  · have hs' : ¬ Summable fun n : ℕ => ((n.factorial : F)⁻¹) • f X ^ n := fun h' => by
      refine hs ?_
      have h2 := h'.map r hrc
      convert h2 using 2 with n
      simp only [Function.comp_apply, map_smul, ← hpow, hr]
    rw [tsum_eq_zero_of_not_summable hs, tsum_eq_zero_of_not_summable hs', map_zero]

/-- A subalgebra of `A` is stable under `expA` (it is closed, and `expA` is `0` where the series
diverges). -/
theorem expA_mem_subalgebra (S : Subalgebra F A) {X : A} (hX : X ∈ S) :
    expA F X ∈ S := by
  have := isTopologicalRing_of_moduleTopology F A
  have := t2Space_of_moduleTopology F A
  have hclosed : IsClosed (S : Set A) := (Subalgebra.toSubmodule S).closed_of_finiteDimensional
  rw [expA, NormedSpace.exp_eq_tsum F]
  beta_reduce
  by_cases hs : Summable fun n : ℕ => ((n.factorial : F)⁻¹) • X ^ n
  · exact hclosed.mem_of_tendsto hs.hasSum (Filter.Eventually.of_forall fun s =>
      Subalgebra.sum_mem _ fun n _ => Subalgebra.smul_mem _ (Subalgebra.pow_mem _ hX n) _)
  · rw [tsum_eq_zero_of_not_summable hs]
    exact S.zero_mem

/-- `f` is multiplicative on `S'` when `f'` is, and they are mutually inverse on `S`, `S'`. -/
theorem map_mul_of_inverse {S : Subalgebra F A} {S' : Subalgebra F A'} {f : A →ₗ[F] A'}
    {f' : A' →ₗ[F] A} (hmul : ∀ a ∈ S, ∀ c ∈ S, f (a * c) = f a * f c)
    (hf'S : ∀ a ∈ S', f' a ∈ S) (hinv : ∀ a ∈ S, f' (f a) = a) (hinv' : ∀ a ∈ S', f (f' a) = a)
    {a c : A'} (ha : a ∈ S') (hc : c ∈ S') : f' (a * c) = f' a * f' c := by
  conv_lhs => rw [← hinv' a ha, ← hinv' c hc, ← hmul _ (hf'S a ha) _ (hf'S c hc)]
  exact hinv _ (S.mul_mem (hf'S a ha) (hf'S c hc))

open Classical in
/-- The map on units `u ↦ f u` (when `f u` is a unit; `1` otherwise). -/
noncomputable def unitsMap (f : A →ₗ[F] A') (u : Aˣ) : A'ˣ :=
  if h : ∃ v : A'ˣ, (v : A') = f u then Classical.choose h else 1

theorem coe_unitsMap {f : A →ₗ[F] A'} {u : Aˣ} (h : ∃ v : A'ˣ, (v : A') = f u) :
    (unitsMap f u : A') = f u := by
  unfold unitsMap
  split_ifs
  exact Classical.choose_spec h

namespace CentralizerIso

/-- **An isomorphism of descent data from a partial algebra isomorphism.** Let `f : A → A'`,
`f' : A' → A` be `F`-linear maps restricting to mutually inverse algebra isomorphisms between
subalgebras `S ⊆ A`, `S' ⊆ A'` that contain `𝔤_x`, `G_x(F)` and `𝔤'_y`, `G'_y(F)`, and that match
`𝔤_x` with `𝔤'_y` and `G_x(F)` with `G'_y(F)`. If `f` preserves the forms on `𝔤_x`, it is an
isomorphism of descent data. -/
noncomputable def ofSubalgebra (S : Subalgebra F A) (S' : Subalgebra F A') (f : A →ₗ[F] A')
    (f' : A' →ₗ[F] A) (hfS : ∀ a ∈ S, f a ∈ S') (hf'S : ∀ a ∈ S', f' a ∈ S) (hone : f 1 = 1)
    (hmul : ∀ a ∈ S, ∀ c ∈ S, f (a * c) = f a * f c) (hinv : ∀ a ∈ S, f' (f a) = a)
    (hinv' : ∀ a ∈ S', f (f' a) = a)
    (h𝔤S : ∀ X ∈ lieCentralizer 𝔤 (x : A), X ∈ S)
    (h𝔤S' : ∀ X ∈ lieCentralizer 𝔤' (y : A'), X ∈ S')
    (h𝔤 : ∀ X ∈ lieCentralizer 𝔤 (x : A), f X ∈ lieCentralizer 𝔤' (y : A'))
    (h𝔤' : ∀ X ∈ lieCentralizer 𝔤' (y : A'), f' X ∈ lieCentralizer 𝔤 (x : A))
    (hGS : ∀ u ∈ grpCentralizer G x, (u : A) ∈ S)
    (hGS' : ∀ u ∈ grpCentralizer G' y, (u : A') ∈ S')
    (hG : ∀ u ∈ grpCentralizer G x, ∀ v : A'ˣ, (v : A') = f u → v ∈ grpCentralizer G' y)
    (hG' : ∀ v ∈ grpCentralizer G' y, ∀ u : Aˣ, (u : A) = f' v → u ∈ grpCentralizer G x)
    (hb : ∀ X ∈ lieCentralizer 𝔤 (x : A), ∀ Y ∈ lieCentralizer 𝔤 (x : A), b' (f X) (f Y) = b X Y) :
    CentralizerIso G 𝔤 b G' 𝔤' b' x y :=
  have hmul' := fun a c (ha : a ∈ S') (hc : c ∈ S') =>
    map_mul_of_inverse hmul hf'S hinv hinv' ha hc
  have hone' : f' 1 = 1 := by rw [← hone]; exact hinv 1 S.one_mem
  have hunit : ∀ u ∈ grpCentralizer G x, ∃ v : A'ˣ, (v : A') = f u := fun u hu =>
    ⟨⟨f u, f ↑u⁻¹, by rw [← hmul _ (hGS u hu) _ (hGS _ (inv_mem hu)), Units.mul_inv, hone],
      by rw [← hmul _ (hGS _ (inv_mem hu)) _ (hGS u hu), Units.inv_mul, hone]⟩, rfl⟩
  have hinvj : ∀ {X Y : A}, X ∈ S → Y ∈ S → f X = f Y → X = Y := fun hX hY h => by
    rw [← hinv _ hX, h, hinv _ hY]
  { lin := f
    bijOn := ⟨h𝔤, fun X hX Y hY h => hinvj (h𝔤S X hX) (h𝔤S Y hY) h, fun X' hX' =>
      ⟨f' X', h𝔤' X' hX', hinv' X' (h𝔤S' X' hX')⟩⟩
    map_commutator := fun X hX Y hY => by
      rw [map_sub, hmul _ (h𝔤S X hX) _ (h𝔤S Y hY), hmul _ (h𝔤S Y hY) _ (h𝔤S X hX)]
    map_bilin := hb
    isNilpotent_iff := fun X hX => by
      have hXS := h𝔤S X hX
      constructor
      · rintro ⟨n, hn⟩
        refine ⟨n, ?_⟩
        rw [← map_pow_of_mul hone hmul hXS] at hn
        rw [← hinv _ (S.pow_mem hXS n), hn, map_zero]
      · rintro ⟨n, hn⟩
        exact ⟨n, by rw [← map_pow_of_mul hone hmul hXS, hn, map_zero]⟩
    isRegularSS_iff := fun X hX => by
      have hXS := h𝔤S X hX
      have hfX : f X ∈ S' := hfS X hXS
      refine and_congr ⟨fun h => ?_, fun h => ?_⟩ ?_
      · refine isSS_of_aeval_eq_zero h.minpoly_squarefree ?_
        rw [← hinv _ (Algebra.adjoin_le (Set.singleton_subset_iff.mpr hXS)
          (Polynomial.aeval_mem_adjoin_singleton F X)), map_aeval_of_mul hone hmul hXS,
          aeval_minpoly_mulLeft, map_zero]
      · refine isSS_of_aeval_eq_zero h.minpoly_squarefree ?_
        rw [← map_aeval_of_mul hone hmul hXS, aeval_minpoly_mulLeft, map_zero]
      · rw [isLieAbelian_iff_forall_commute, isLieAbelian_iff_forall_commute]
        constructor
        · intro h Z₁ hZ₁ Z₂ hZ₂
          obtain ⟨hZ₁x, hXZ₁⟩ := mem_lieCentralizer.mp hZ₁
          obtain ⟨hZ₂x, hXZ₂⟩ := mem_lieCentralizer.mp hZ₂
          have hS₁ := h𝔤S _ hZ₁x
          have hS₂ := h𝔤S _ hZ₂x
          have hc : ∀ {Z : A}, Z ∈ S → X * Z = Z * X → f X * f Z = f Z * f X := fun hZ hXZ => by
            rw [← hmul _ hXS _ hZ, hXZ, hmul _ hZ _ hXS]
          have := h _ (mem_lieCentralizer.mpr ⟨h𝔤 _ hZ₁x, hc hS₁ hXZ₁⟩)
            _ (mem_lieCentralizer.mpr ⟨h𝔤 _ hZ₂x, hc hS₂ hXZ₂⟩)
          rw [← hmul _ hS₁ _ hS₂, ← hmul _ hS₂ _ hS₁] at this
          exact hinvj (S.mul_mem hS₁ hS₂) (S.mul_mem hS₂ hS₁) this
        · intro h Z₁ hZ₁ Z₂ hZ₂
          obtain ⟨hZ₁y, hXZ₁⟩ := mem_lieCentralizer.mp hZ₁
          obtain ⟨hZ₂y, hXZ₂⟩ := mem_lieCentralizer.mp hZ₂
          have hS₁ := h𝔤S' _ hZ₁y
          have hS₂ := h𝔤S' _ hZ₂y
          have hc : ∀ {Z : A'}, Z ∈ S' → f X * Z = Z * f X → X * f' Z = f' Z * X :=
            fun hZ hXZ => by
              rw [← hinv X hXS, ← hmul' _ _ hfX hZ, hXZ, hmul' _ _ hZ hfX]
          have := h _ (mem_lieCentralizer.mpr ⟨h𝔤' _ hZ₁y, hc hS₁ hXZ₁⟩)
            _ (mem_lieCentralizer.mpr ⟨h𝔤' _ hZ₂y, hc hS₂ hXZ₂⟩)
          rw [← hmul' _ _ hS₁ hS₂, ← hmul' _ _ hS₂ hS₁] at this
          rw [← hinv' _ (S'.mul_mem hS₁ hS₂), this, hinv' _ (S'.mul_mem hS₂ hS₁)]
    map_orbitMap := fun X hX Y hY => by
      have hXS := h𝔤S X hX
      have hexp : ∀ {Z : A}, Z ∈ S → f (expA F Z) = expA F (f Z) := fun hZ =>
        map_expA_of_leftInverse f f' (map_pow_of_mul hone hmul hZ)
          (fun n => hinv _ (S.pow_mem hZ n))
      have hYS := h𝔤S Y hY
      have hnYS : -Y ∈ S := S.neg_mem hYS
      rw [orbitMap, orbitMap, hmul _ (S.mul_mem (expA_mem_subalgebra S hYS) hXS) _
        (expA_mem_subalgebra S hnYS), hmul _ (expA_mem_subalgebra S hYS) _ hXS, hexp hYS,
        hexp hnYS, map_neg]
    grp := unitsMap f
    grp_mapsTo := fun u hu => hG u hu _ (coe_unitsMap (hunit u hu))
    grp_surjOn := fun v hv => by
      have hvS := hGS' v hv
      have hvS' := hGS' _ (inv_mem hv)
      let u : Aˣ := ⟨f' v, f' ↑v⁻¹, by rw [← hmul' _ _ hvS hvS', Units.mul_inv, hone'],
        by rw [← hmul' _ _ hvS' hvS, Units.inv_mul, hone']⟩
      have hu : u ∈ grpCentralizer G x := hG' v hv u rfl
      refine ⟨u, hu, Units.ext ?_⟩
      rw [coe_unitsMap (hunit u hu)]
      exact hinv' _ hvS
    map_conj := fun u hu X hX => by
      have huS := hGS u hu
      have huS' := hGS _ (inv_mem hu)
      have hXS := h𝔤S X hX
      have h1 := coe_unitsMap (hunit u hu)
      have h2 : ((unitsMap f u)⁻¹ : A'ˣ) = f ↑u⁻¹ := by
        refine Units.inv_eq_of_mul_eq_one_right ?_
        rw [h1, ← hmul _ huS _ huS', Units.mul_inv, hone]
      rw [h1, h2, hmul _ (S.mul_mem huS hXS) _ huS', hmul _ huS _ hXS] }

@[simp] theorem ofSubalgebra_lin (S : Subalgebra F A) (S' : Subalgebra F A') (f : A →ₗ[F] A')
    (f' : A' →ₗ[F] A) (hfS hf'S hone hmul hinv hinv' h𝔤S h𝔤S' h𝔤 h𝔤' hGS hGS' hG hG' hb) :
    (ofSubalgebra (G := G) (𝔤 := 𝔤) (b := b) (G' := G') (𝔤' := 𝔤') (b' := b') (x := x) (y := y)
      S S' f f' hfS hf'S hone hmul hinv hinv' h𝔤S h𝔤S' h𝔤 h𝔤' hGS hGS' hG hG' hb).lin = f :=
  rfl

end CentralizerIso

end OfSubalgebra


end GSpinGGP
