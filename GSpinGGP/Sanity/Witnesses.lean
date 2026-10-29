/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.Triple
import GSpinGGP.TraceFormula.Spine
import GSpinGGP.Literature.Fourier

/-!
# Sanity witnesses: the key hypotheses and normalizations are not vacuous

For each predicate that the main theorem quantifies over, or that is used to pin a
normalization by the "epsilon pattern" (`if h : ∃ μ, P μ then h.choose else 0`), we exhibit an
explicit inhabitant, at least in a toy case.  An uninhabitable hypothesis would make the main
theorem vacuous; an uninhabitable normalization would make the epsilon fall through to its junk
value `0`.

## Results

1. **Self-dual measures** (`IsSelfDual`, `selfDualMeasure`; Thesis §2.4).  On a zero-dimensional
   space, `dirac 0` is self-dual for every form and character (`isSelfDual_dirac_zero`), it is the
   *only* self-dual measure (`eq_dirac_of_isSelfDual`), so `selfDualMeasure B ψ = dirac 0 ≠ 0`
   (`selfDualMeasure_eq_dirac_zero`).  In general `selfDualMeasure B ψ ≠ 0` as soon as a self-dual
   measure exists (`selfDualMeasure_ne_zero`) and it is then locally finite.
2. **Orbit measures and `ĵ`** (`IsOrbitMeasure`, `orbitMeasure`, `IsJHat`; Thesis §2.4, §4.1.1,
   BP §1.6, §1.8).  For *every* unbundled `(G, 𝔤, b, ψ)` the zero orbit has the orbit measure
   `dirac 0` (`isOrbitMeasure_zeroOrbit`), which is the only one
   (`eq_dirac_of_isOrbitMeasure_zeroOrbit`), hence `orbitMeasure … zeroOrbit = dirac 0`, and
   `ĵ(0, ·) = 1` satisfies `IsJHat` (`isJHat_zeroOrbit_one`): `μ_0(f̂) = f̂(0) = ∫ f`.
3. **A GGP datum** (`toyData`: `W = 0`, `V = Z = ⟨z_0⟩`, `ν = 1`).  Its `G = GSpin(0) × GSpin(1)`
   is abelian (`toyData_G_comm`), it is quasi-split and even split (`toyData_isQuasiSplit`,
   `toyData_isSplit`), its Witt indices are `0` (`toyData_wittIndex_QW/QV`).
4. **A Whittaker datum** for `toyData` (`toyWhittaker`): the empty flags are full, and the trivial
   character is generic because `G` is abelian.  *Caveat*: for this datum `IsFull` forces the flags
   to be empty, so `U = 1`; this is the Whittaker datum of a torus and does not test genericity of
   a nondegenerate character.
5. **`TemperedPacketFamily`** for `toyData` (`toyPacketFamily`, packet `{1}`): every field is
   proved — (STAB), (TRANS) via "stable conjugacy is equality in the toy `G`", (WHITT) via
   `U = 1`, and temperedness: the weak containment `1 ≺ L²(G)` is proved by Følner
   sets (§4½: `weaklyContainedIn_leftRegular_of_isClosed_comm`, valid for every closed commutative
   subgroup of the units of a finite-dimensional algebra over a `p`-adic field; it uses the
   compact open subgroup `latticeStab`, the stabilizer of `𝒪^d`). No literature axiom is needed.

6. **The toy trace formula** (§6 below).  For `toyData`:
   * `toy_ellRegSet`: the elliptic regular set is all of `G` (so the hypotheses of the spine
     statements `prop_11_5_1_ii_ell`, `exists_scusp_ell` are not vacuous there);
   * `toy_distribJ`: `J(f) = f(1)`, with `weilMeasureHG` of mass `1` (`toy_weilMeasureHG_real_univ`,
     from an explicit Weil measure, no axiom);
   * `toy_thetaF`: `θ_f = c · f` with `c = haar(G/A_G) = 1` (Mathlib's Haar measure on a point);
   * `toyD_mGeom`: `m_geom(θ) = θ(1)` for locally constant `θ` constant on `A_{G,H}`: one torus
     class, `|W(T)| = 1`, `D^G = Δ = 1`, probability measure = point mass, germ = value;
   * `toy_geomAt`: the geometric expansion `J(f) = m_geom(θ_f)` (Thesis Thm 12.2.1) holds;
   * `toy_multAt`, `toy_defect_zero`: the multiplicity formula and `defect = 0`, but only via the
     spine (`multAt_of_hyp_geom`; (HYP) is vacuous since `dim G = 2` is minimal), hence through the
     spine `sorry`s `prop_11_5_1_ii_ell`, `exists_scusp_ell`.
   Generic by-products: `jHat_zeroOrbit_eq_one` (`ĵ(0,·) = 1` *pointwise* once a self-dual measure
   exists and `𝔤 = 𝔤_reg`), `exists_nhds_zero_mul_expA`, `continuousAt_expA_zero`.

Upstream `sorry`s reached: `toyWhittaker` and the packet family depend on `sorryAx` only through
upstream files (e.g. `flagUnip`, via `isNilpotent_mul_sub_one_of_flagUnipSO`),
not through anything in this file.  This file has no `sorry`: `exists_isSelfDual_toyLie`
(Fourier inversion on `F²`), formerly the only unproved input of `toy_geomAt`, now follows from the
literature axiom `exists_isSelfDual` (Tate's thesis; `Literature/Fourier`).
-/

noncomputable section

open MeasureTheory Filter Topology Module CliffordAlgebra
open scoped Classical TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace GSpinGGP

namespace Sanity

/-! ## 1. Self-dual measures on a zero-dimensional space -/

section SelfDualZero

variable {F : Type*} [NontriviallyNormedField F]
variable {V : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V] [MeasurableSpace V]

/-- `ψ(0) = 1`. -/
@[simp] lemma nontrivialAddChar_zero (ψ : NontrivialAddChar F) : ψ 0 = 1 := by
  show ((ψ.toAddChar 0 : Circle) : ℂ) = 1
  simp

/-- On a subsingleton every set is `∅` or `univ`, hence measurable. -/
lemma measurableSet_of_subsingleton [Subsingleton V] (s : Set V) : MeasurableSet s := by
  rcases s.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · rw [h]; exact MeasurableSet.empty
  · have : s = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
    rw [this]; exact MeasurableSet.univ

lemma measurableSingletonClass_of_subsingleton [Subsingleton V] : MeasurableSingletonClass V :=
  ⟨fun _ => measurableSet_of_subsingleton _⟩

/-- `dirac 0` is a Haar measure on a zero-dimensional space. -/
lemma isAddHaarMeasure_dirac_zero [Subsingleton V] : (Measure.dirac (0 : V)).IsAddHaarMeasure where
  lt_top_of_isCompact _ _ := measure_lt_top _ _
  map_add_left_eq_self a := by
    rw [Measure.map_dirac' (fun s _ => measurableSet_of_subsingleton _), add_zero]
    rw [Subsingleton.elim a 0]
  open_pos U _ hU := by
    obtain ⟨x, hx⟩ := hU
    rw [Measure.dirac_apply' _ (measurableSet_of_subsingleton U),
      Set.indicator_of_mem (Subsingleton.elim x (0 : V) ▸ hx)]
    simp

/-- **Non-vacuity of `IsSelfDual`**: on a zero-dimensional space `dirac 0` is self-dual for every
form `B` and character `ψ`. -/
theorem isSelfDual_dirac_zero [Subsingleton V] (B : LinearMap.BilinForm F V)
    (ψ : NontrivialAddChar F) : IsSelfDual (Measure.dirac (0 : V)) B ψ := by
  haveI := measurableSingletonClass_of_subsingleton (V := V)
  refine ⟨isAddHaarMeasure_dirac_zero, fun f _ Z => ?_⟩
  simp only [fourierWRT, integral_dirac, map_zero, LinearMap.zero_apply, neg_zero,
    nontrivialAddChar_zero, mul_one]
  rw [Subsingleton.elim Z 0]

/-- The self-dual measure on a zero-dimensional space is unique: it is `dirac 0`
(apply Fourier inversion to `f ≡ 1`: `μ(pt)² = 1`). -/
theorem eq_dirac_of_isSelfDual [Subsingleton V] {μ : Measure V} {B : LinearMap.BilinForm F V}
    {ψ : NontrivialAddChar F} (h : IsSelfDual μ B ψ) : μ = Measure.dirac 0 := by
  letI : Unique V := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  have htest : IsTestFn (fun _ : V => (1 : ℂ)) :=
    ⟨IsLocallyConstant.const _, IsCompact.of_isClosed_subset
      (Set.finite_univ.isCompact) (isClosed_tsupport _) (Set.subset_univ _)⟩
  have h1 := h.2 _ htest 0
  have hd : (default : V) = 0 := Subsingleton.elim _ _
  simp only [fourierWRT, integral_unique, hd, map_zero, LinearMap.zero_apply, neg_zero,
    nontrivialAddChar_zero, mul_one] at h1
  -- `h1 : μ.real univ * μ.real univ = 1`
  have hc : μ.real Set.univ = 1 := by
    have h0 : 0 ≤ μ.real Set.univ := measureReal_nonneg
    have h1' : (μ.real Set.univ : ℂ) * (μ.real Set.univ : ℂ) = 1 := by
      simpa using h1
    have h2 : μ.real Set.univ * μ.real Set.univ = 1 := by exact_mod_cast h1'
    nlinarith
  have hU : μ Set.univ = 1 := by
    rw [measureReal_def] at hc
    have hne : μ Set.univ ≠ ⊤ := by
      intro htop; rw [htop] at hc; simp at hc
    rw [← ENNReal.ofReal_toReal hne, hc, ENNReal.ofReal_one]
  ext s hs
  rcases s.eq_empty_or_nonempty with h' | ⟨x, hx⟩
  · simp [h']
  · have : s = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
    subst this
    simp [hU]

/-- `selfDualMeasure B ψ = dirac 0` on a zero-dimensional space. -/
theorem selfDualMeasure_eq_dirac_zero [Subsingleton V] (B : LinearMap.BilinForm F V)
    (ψ : NontrivialAddChar F) : selfDualMeasure B ψ = Measure.dirac 0 := by
  have h : ∃ μ, IsSelfDual μ B ψ := ⟨_, isSelfDual_dirac_zero B ψ⟩
  unfold selfDualMeasure
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact eq_dirac_of_isSelfDual h.choose_spec

/-- In general, `selfDualMeasure B ψ` is a genuine (nonzero) Haar measure as soon as some self-dual
measure exists. -/
theorem selfDualMeasure_isAddHaar {B : LinearMap.BilinForm F V} {ψ : NontrivialAddChar F}
    (h : ∃ μ, IsSelfDual μ B ψ) : (selfDualMeasure B ψ).IsAddHaarMeasure := by
  unfold selfDualMeasure
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec.1

theorem selfDualMeasure_ne_zero [IsTopologicalAddGroup V] {B : LinearMap.BilinForm F V}
    {ψ : NontrivialAddChar F} (h : ∃ μ, IsSelfDual μ B ψ) : selfDualMeasure B ψ ≠ 0 := by
  haveI := selfDualMeasure_isAddHaar h
  intro h0
  have := isOpen_univ.measure_ne_zero (selfDualMeasure B ψ) ⟨(0 : V), Set.mem_univ _⟩
  rw [h0] at this
  simp at this

/-- `selfDualMeasure B ψ` is always locally finite (it is Haar or `0`). -/
theorem isLocallyFiniteMeasure_selfDualMeasure [WeaklyLocallyCompactSpace V]
    (B : LinearMap.BilinForm F V) (ψ : NontrivialAddChar F) :
    IsLocallyFiniteMeasure (selfDualMeasure B ψ) := by
  unfold selfDualMeasure
  split_ifs with h
  · haveI := h.choose_spec.1
    infer_instance
  · infer_instance

/-- **Toy case of `selfDualHaar`**: for the zero Lie algebra, `selfDualHaar ⊥ b ψ = dirac 0 ≠ 0`. -/
example {A : Type*} [Ring A] [Algebra F A] [TopologicalSpace A] (b : LinearMap.BilinForm F A)
    (ψ : NontrivialAddChar F) :
    selfDualHaar (⊥ : LieSubalgebra F A) b ψ = Measure.dirac 0 ∧
      selfDualHaar (⊥ : LieSubalgebra F A) b ψ ≠ 0 := by
  haveI : Subsingleton ↥(⊥ : LieSubalgebra F A) :=
    ⟨fun x y => Subtype.ext <| by
      rw [(LieSubalgebra.mem_bot (x : A)).mp x.2, (LieSubalgebra.mem_bot (y : A)).mp y.2]⟩
  refine ⟨selfDualMeasure_eq_dirac_zero _ ψ, ?_⟩
  rw [selfDualHaar, selfDualMeasure_eq_dirac_zero]
  exact Measure.dirac_ne_zero

end SelfDualZero

/-! ## 2. The zero orbit: `IsOrbitMeasure`, `orbitMeasure`, `IsJHat` -/

section ZeroOrbit

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
variable {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A]
  [IsModuleTopology F A]

/-- The zero nilpotent orbit `{0} ∈ Nil(𝔤)`. -/
def zeroOrbit (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A) : NilOrbit G 𝔤 :=
  Quotient.mk (nilSetoid G 𝔤) ⟨0, 𝔤.zero_mem, IsNilpotent.zero⟩

lemma mem_nilOrbitSet_zeroOrbit {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A} (X : ↥𝔤) :
    X ∈ nilOrbitSet (zeroOrbit G 𝔤) ↔ X = 0 := by
  constructor
  · rintro ⟨_, hX⟩
    obtain ⟨g, _, hg⟩ := Quotient.exact hX
    apply Subtype.ext
    have : (X : A) = (↑g⁻¹ : A) * ((g : A) * (X : A) * (↑g⁻¹ : A)) * (g : A) := by
      simp [mul_assoc]
    rw [this]
    simp only at hg
    rw [hg]; simp
  · rintro rfl
    exact ⟨IsNilpotent.zero, rfl⟩

lemma nilOrbitSet_zeroOrbit {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A} :
    nilOrbitSet (zeroOrbit G 𝔤) = {0} := by
  ext X; simp [mem_nilOrbitSet_zeroOrbit]

lemma measurableSingletonClass_lie (𝔤 : LieSubalgebra F A) : MeasurableSingletonClass ↥𝔤 := by
  haveI := t2Space_of_moduleTopology F A
  infer_instance

lemma subsingleton_of_isCompl_top {𝔤 : LieSubalgebra F A} {C : Submodule F ↥𝔤}
    (hC : IsCompl C ⊤) : Subsingleton ↥C := by
  have hC' : C = ⊥ := by
    have := hC.inf_eq_bot
    rwa [inf_top_eq] at this
  subst hC'
  infer_instance

/-- **Non-vacuity of `IsOrbitMeasure`**: for every `(G, 𝔤, b, ψ)`, `dirac 0` is the orbit measure
of the zero orbit (Thesis §2.4: `μ_0 = δ_0`). -/
theorem isOrbitMeasure_zeroOrbit (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A)
    (b : LinearMap.BilinForm F A) (ψ : NontrivialAddChar F) :
    IsOrbitMeasure G 𝔤 b ψ (zeroOrbit G 𝔤) (Measure.dirac 0) := by
  haveI := measurableSingletonClass_lie 𝔤
  refine ⟨?_, ?_, ?_⟩
  · rw [nilOrbitSet_zeroOrbit, Measure.dirac_apply]
    simp
  · intro g _ S _
    rw [Measure.dirac_apply, Measure.dirac_apply]
    have : ((0 : ↥𝔤) ∈ Subtype.val ⁻¹' (conjAd F g ⁻¹' (Subtype.val '' S))) ↔ (0 : ↥𝔤) ∈ S := by
      simp only [Set.mem_preimage, ZeroMemClass.coe_zero, conjAd_apply, mul_zero, zero_mul,
        Set.mem_image]
      constructor
      · rintro ⟨x, hx, hx0⟩
        rwa [show x = 0 from Subtype.ext hx0] at hx
      · intro h; exact ⟨0, h, rfl⟩
    by_cases h : (0 : ↥𝔤) ∈ S
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (this.mpr h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt this.mp h)]
  · intro X hX C hC
    rw [mem_nilOrbitSet_zeroOrbit] at hX
    subst hX
    have hker : LinearMap.ker (LieAlgebra.ad F ↥𝔤 (0 : ↥𝔤)) = ⊤ := by
      rw [map_zero]; exact LinearMap.ker_zero
    rw [hker] at hC
    haveI := subsingleton_of_isCompl_top hC
    refine ⟨Set.univ, univ_mem, fun S _ _ => ?_⟩
    rw [selfDualMeasure_eq_dirac_zero, Measure.dirac_apply' _ (measurableSet_of_subsingleton S),
      Measure.dirac_apply]
    rcases S.eq_empty_or_nonempty with hS | ⟨y, hy⟩
    · subst hS; simp
    · have h0 : (0 : ↥C) ∈ S := Subsingleton.elim y 0 ▸ hy
      have hm : (0 : ↥𝔤) ∈ Subtype.val ⁻¹'
          ((fun Y : ↥C ↦ orbitMap F ((0 : ↥𝔤) : A) ((Y : ↥𝔤) : A)) '' S) :=
        ⟨0, h0, by simp [orbitMap]⟩
      rw [Set.indicator_of_mem h0, Set.indicator_of_mem hm]
      rfl

/-- The zero orbit has a *unique* orbit measure, `dirac 0`. -/
theorem eq_dirac_of_isOrbitMeasure_zeroOrbit {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A}
    {b : LinearMap.BilinForm F A} {ψ : NontrivialAddChar F} {μ : Measure ↥𝔤}
    (h : IsOrbitMeasure G 𝔤 b ψ (zeroOrbit G 𝔤) μ) : μ = Measure.dirac 0 := by
  haveI := measurableSingletonClass_lie 𝔤
  obtain ⟨h1, -, h3⟩ := h
  rw [nilOrbitSet_zeroOrbit] at h1
  have hC : IsCompl (⊥ : Submodule F ↥𝔤) (LinearMap.ker (LieAlgebra.ad F ↥𝔤 (0 : ↥𝔤))) := by
    rw [map_zero, LinearMap.ker_zero]; exact isCompl_bot_top
  obtain ⟨U, hU, hS⟩ := h3 0 ((mem_nilOrbitSet_zeroOrbit 0).mpr rfl) ⊥ hC
  have hsub : ∀ Y ∈ (Set.univ : Set ↥(⊥ : Submodule F ↥𝔤)), ((Y : ↥𝔤) : A) ∈ U := by
    intro Y _
    rw [show Y = 0 from Subsingleton.elim _ _]
    exact mem_of_mem_nhds hU
  have h0 := hS Set.univ MeasurableSet.univ hsub
  rw [selfDualMeasure_eq_dirac_zero, measure_univ] at h0
  have himg : (Subtype.val ⁻¹' ((fun Y : ↥(⊥ : Submodule F ↥𝔤) ↦
      orbitMap F ((0 : ↥𝔤) : A) ((Y : ↥𝔤) : A)) '' Set.univ) : Set ↥𝔤) = {0} := by
    ext Z
    simp only [Set.mem_preimage, Set.image_univ, Set.mem_range, Set.mem_singleton_iff,
      orbitMap, ZeroMemClass.coe_zero, mul_zero, zero_mul]
    constructor
    · rintro ⟨_, hZ⟩; exact Subtype.ext hZ.symm
    · rintro rfl; exact ⟨0, rfl⟩
  rw [himg] at h0
  have hae : ∀ᵐ x ∂μ, x ∈ ({0} : Set ↥𝔤) := by
    rw [ae_iff]; exact h1
  rw [← Measure.restrict_eq_self_of_ae_mem hae, Measure.restrict_singleton, h0, one_smul]

/-- `orbitMeasure G 𝔤 b ψ (zeroOrbit) = dirac 0`: the epsilon is not junk. -/
theorem orbitMeasure_zeroOrbit (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A)
    (b : LinearMap.BilinForm F A) (ψ : NontrivialAddChar F) :
    orbitMeasure G 𝔤 b ψ (zeroOrbit G 𝔤) = Measure.dirac 0 := by
  have h : ∃ μ, IsOrbitMeasure G 𝔤 b ψ (zeroOrbit G 𝔤) μ := ⟨_, isOrbitMeasure_zeroOrbit G 𝔤 b ψ⟩
  unfold orbitMeasure
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact eq_dirac_of_isOrbitMeasure_zeroOrbit h.choose_spec

/-- A Lie subalgebra of `A` is locally compact (finite-dimensional subspaces of a Hausdorff TVS
over a complete field are closed). -/
lemma locallyCompactSpace_lie (𝔤 : LieSubalgebra F A) : LocallyCompactSpace ↥𝔤 := by
  haveI := t2Space_of_moduleTopology F A
  haveI := isTopologicalRing_of_moduleTopology F A
  haveI := locallyCompactSpace_of_moduleTopology F A
  haveI : ContinuousSMul F A := IsModuleTopology.toContinuousSMul F A
  have hcl : IsClosed (𝔤.toSubmodule : Set A) := Submodule.closed_of_finiteDimensional _
  exact hcl.locallyCompactSpace

/-- **Non-vacuity of `IsJHat`**: `ĵ(0, ·) = 1` (`μ_0(f̂) = f̂(0) = ∫_𝔤 f`). -/
theorem isJHat_zeroOrbit_one (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A)
    (b : LinearMap.BilinForm F A) (ψ : NontrivialAddChar F) :
    IsJHat G 𝔤 b ψ (zeroOrbit G 𝔤) (fun _ => 1) := by
  haveI := measurableSingletonClass_lie 𝔤
  haveI := locallyCompactSpace_lie 𝔤
  haveI : IsLocallyFiniteMeasure (selfDualHaar 𝔤 b ψ) :=
    isLocallyFiniteMeasure_selfDualMeasure (restrictForm 𝔤 b) ψ
  refine ⟨continuousOn_const, locallyIntegrable_const 1, fun f _ => ?_⟩
  rw [orbitMeasure_zeroOrbit, integral_dirac]
  simp [fourierLie, fourierWRT, selfDualHaar]

theorem exists_isJHat_zeroOrbit (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A)
    (b : LinearMap.BilinForm F A) (ψ : NontrivialAddChar F) :
    ∃ j, IsJHat G 𝔤 b ψ (zeroOrbit G 𝔤) j :=
  ⟨_, isJHat_zeroOrbit_one G 𝔤 b ψ⟩

end ZeroOrbit

/-! ## 3. Quadratic-space helpers -/

section QuadHelpers

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- An anisotropic quadratic space has Witt index `0`. -/
theorem wittIndex_eq_zero_of_anisotropic {Q : QuadraticForm K V} (h : ∀ v, Q v = 0 → v = 0) :
    wittIndex Q = 0 := by
  have hset : {n | ∃ U : Submodule K V, IsTotallyIsotropic Q U ∧ finrank K U = n} = {0} := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨U, hU, rfl⟩
      have : U = ⊥ := (Submodule.eq_bot_iff U).mpr fun u hu => h u (hU u hu)
      subst this
      exact finrank_bot K V
    · rintro rfl
      refine ⟨⊥, fun u hu => ?_, finrank_bot K V⟩
      rw [(Submodule.mem_bot K).mp hu, map_zero]
  unfold wittIndex
  rw [hset, csSup_singleton]

/-- The one-dimensional split space `Z = ⟨z_0⟩`: `q(z) = ν z_0²` (Thesis (5.2.1) with `r = 0`). -/
theorem splitOddForm_zero_apply (ν : K) (z : Fin (2 * 0 + 1) → K) :
    splitOddForm 0 ν z = ν * (z 0 * z 0) := by
  simp [splitOddForm, splitOddMatrix, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply',
    dotProduct, Matrix.mulVec]
  ring

end QuadHelpers

/-! ## 4. An explicit GGP datum and a Whittaker datum for it -/

section Toy

variable {K : Type*} [Field K] [Invertible (2 : K)]

lemma fin_eq_zero_of {n : ℕ} (hn : n = 0) (i : Fin (n + 1)) : i = 0 := by
  subst hn; exact Fin.fin_one_eq_zero i

/-- A Clifford algebra whose generators pairwise commute is commutative. -/
theorem cliff_commute_of_ι {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (h : ∀ v w, Commute (ι Q v) (ι Q w)) (a b : CliffordAlgebra Q) : Commute a b := by
  have hι : ∀ v (b : CliffordAlgebra Q), Commute (ι Q v) b := by
    intro v b
    induction b using CliffordAlgebra.induction with
    | algebraMap r => exact Algebra.commute_algebraMap_right r _
    | ι w => exact h v w
    | mul x y hx hy => exact hx.mul_right hy
    | add x y hx hy => exact hx.add_right hy
  induction a using CliffordAlgebra.induction with
  | algebraMap r => exact Algebra.commute_algebraMap_left r _
  | ι v => exact hι v b
  | mul x y hx hy => exact hx.mul_left hy
  | add x y hx hy => exact hx.add_left hy

/-- The toy GGP datum: `W = 0`, `Z = V = ⟨z_0⟩` with `q(z_0) = 1` (`m = 0`, `r = 0`, `ν = 1`).
Then `G = GSpin(0) × GSpin(1) = GL₁ × GL₁`, `H = GSpin(0) = GL₁` (diagonal), `ξ = 1`
(Thesis §5.2 with `n = 0`, `r = 0`: the degenerate "Waldspurger" case `SO(1) ⊂ SO(1)`). -/
abbrev toyData : GGPData K where
  m := 0
  QW := 0
  nondeg := ⟨fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
  r := 0
  ν := 1

lemma toyData_QV_apply (v : (toyData (K := K)).V) :
    (toyData (K := K)).QV v = v.2 0 * v.2 0 := by
  show (0 : QuadraticForm K (Fin 0 → K)) v.1 + splitOddForm 0 ((1 : Kˣ) : K) v.2 = _
  rw [splitOddForm_zero_apply]
  simp

theorem toyData_wittIndex_QW : wittIndex (toyData (K := K)).QW = 0 :=
  wittIndex_eq_zero_of_anisotropic fun _ _ => Subsingleton.elim _ _

theorem toyData_wittIndex_QV : wittIndex (toyData (K := K)).QV = 0 := by
  refine wittIndex_eq_zero_of_anisotropic fun v hv => ?_
  rw [toyData_QV_apply, mul_self_eq_zero] at hv
  refine Prod.ext (Subsingleton.elim _ _) (funext fun i => ?_)
  rw [fin_eq_zero_of rfl i, hv]
  rfl

/-- The toy datum is quasi-split (Thesis §6.4 hypothesis of the main theorem). -/
theorem toyData_isQuasiSplit : (toyData (K := K)).IsQuasiSplit := by
  refine ⟨?_, ?_⟩ <;> unfold IsQuasiSplitQF
  · show finrank K (Fin 0 → K) ≤ _
    simp
  · simp only [toyData_wittIndex_QV]
    show finrank K ((Fin 0 → K) × (Fin (2 * 0 + 1) → K)) ≤ 2 * 0 + 2
    simp [Module.finrank_prod]

theorem toyData_isSplit :
    IsSplitQF (toyData (K := K)).QW ∧ IsSplitQF (toyData (K := K)).QV := by
  refine ⟨?_, ?_⟩ <;> unfold IsSplitQF
  · show finrank K (Fin 0 → K) ≤ _
    simp
  · simp only [toyData_wittIndex_QV]
    show finrank K ((Fin 0 → K) × (Fin (2 * 0 + 1) → K)) ≤ 2 * 0 + 1
    simp [Module.finrank_prod]

theorem toyData_cliffW_comm (a b : CliffordAlgebra (toyData (K := K)).QW) : Commute a b :=
  cliff_commute_of_ι (fun v w => by rw [Subsingleton.elim v 0]; simp) a b

theorem toyData_cliffV_comm (a b : CliffordAlgebra (toyData (K := K)).QV) : Commute a b := by
  refine cliff_commute_of_ι (fun v w => ?_) a b
  let e : (toyData (K := K)).V := (0, fun _ => 1)
  have hv : ∀ u : (toyData (K := K)).V, u = u.2 0 • e := fun u =>
    Prod.ext (Subsingleton.elim _ _) (funext fun i => by
      rw [fin_eq_zero_of rfl i]; simp [e])
  rw [hv v, hv w, map_smul, map_smul]
  exact ((Commute.refl _).smul_left _).smul_right _

/-- `algebraMap K C(Q)` is injective (characteristic `≠ 2`: transport to the exterior algebra). -/
theorem algebraMap_cliff_injective {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : Function.Injective (algebraMap K (CliffordAlgebra Q)) := by
  intro a b hab
  have h := congrArg (equivExterior Q) hab
  simp only [equivExterior, changeFormEquiv_apply, changeForm_algebraMap] at h
  exact (ExteriorAlgebra.algebraMap_leftInverse V).injective h

/-- A scalar `x = c` of a Clifford algebra with `x - 1` nilpotent is `1`. -/
theorem eq_one_of_scalar_of_isNilpotent {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {x : CliffordAlgebra Q} (hx : ∃ c, x = algebraMap K _ c)
    (hn : IsNilpotent (x - 1)) : x = 1 := by
  obtain ⟨c, rfl⟩ := hx
  obtain ⟨n, hn⟩ := hn
  rw [← map_one (algebraMap K (CliffordAlgebra Q)), ← map_sub, ← map_pow,
    ← map_zero (algebraMap K (CliffordAlgebra Q))] at hn
  have := eq_zero_of_pow_eq_zero ((algebraMap_cliff_injective Q) hn)
  rw [sub_eq_zero.mp this, map_one]

/-- Every element of `C(W)`, `W = 0`, is a scalar. -/
theorem toy_cliffW_scalar (x : CliffordAlgebra (toyData (K := K)).QW) :
    ∃ c, x = algebraMap K _ c := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact ⟨r, rfl⟩
  | ι w => exact ⟨0, by rw [Subsingleton.elim w 0, map_zero, map_zero]⟩
  | mul x y hx hy =>
    obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a * b, (map_mul _ _ _).symm⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, (map_add _ _ _).symm⟩

/-- Every even element of `C(V)`, `V` a line, is a scalar. -/
theorem toy_cliffV_even_scalar (x : CliffordAlgebra (toyData (K := K)).QV)
    (hx : x ∈ evenOdd (toyData (K := K)).QV 0) : ∃ c, x = algebraMap K _ c := by
  let e : (toyData (K := K)).V := (0, fun _ => 1)
  have hv : ∀ u : (toyData (K := K)).V, u = u.2 0 • e := fun u =>
    Prod.ext (Subsingleton.elim _ _) (funext fun i => by
      rw [fin_eq_zero_of rfl i]; simp [e])
  induction x, hx using even_induction with
  | algebraMap r => exact ⟨r, rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, (map_add _ _ _).symm⟩
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
    obtain ⟨c, rfl⟩ := hx
    refine ⟨m₁.2 0 * m₂.2 0 * (toyData (K := K)).QV e * c, ?_⟩
    rw [hv m₁, hv m₂, map_smul, map_smul, smul_mul_smul_comm, ι_sq_scalar, smul_mul_assoc,
      ← map_mul, Algebra.smul_def, ← map_mul]
    simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    congr 1
    simp [e]
    ring

/-- `G = GSpin(0) × GSpin(1)` is abelian for the toy datum. -/
theorem toyData_G_comm (g h : ↥(toyData (K := K)).G) : g * h = h * g := by
  apply Subtype.ext
  apply Units.ext
  show ((g : (toyData (K := K)).ambientˣ) : (toyData (K := K)).ambient) * h = h * g
  exact Prod.ext (toyData_cliffW_comm _ _) (toyData_cliffV_comm _ _)

theorem toyData_mem_center (g : ↥(toyData (K := K)).G) :
    g ∈ Subgroup.center (toyData (K := K)).G :=
  Subgroup.mem_center_iff.mpr fun h => toyData_G_comm h g

/-- For the toy datum the unipotent radical of every "Borel" is trivial (`G` is a torus):
a unipotent element of `GSpin(0)` or `GSpin(1)` is `1`. -/
theorem toy_whittU_eq_one (FW : IsotropicFlag (toyData (K := K)).QW)
    (FV : IsotropicFlag (toyData (K := K)).QV) {u : ↥(toyData (K := K)).G}
    (hu : u ∈ (toyData (K := K)).whittU FW FV) : u = 1 := by
  obtain ⟨hW, hV⟩ := hu
  have h1 : (((toyData (K := K)).fst u : (CliffordAlgebra (toyData (K := K)).QW)ˣ) :
      CliffordAlgebra (toyData (K := K)).QW) = 1 := eq_one_of_scalar_of_isNilpotent (toy_cliffW_scalar _) (by exact hW.2.2.2)
  have hev := (((toyData (K := K)).snd u : GSpin _)).2.1
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at hev
  have h2 : (((toyData (K := K)).snd u : (CliffordAlgebra (toyData (K := K)).QV)ˣ) :
      CliffordAlgebra (toyData (K := K)).QV) = 1 := eq_one_of_scalar_of_isNilpotent (toy_cliffV_even_scalar _ hev) (by exact hV.2.2.2)
  apply Subtype.ext
  apply Units.ext
  exact Prod.ext h1 h2

/-- The empty isotropic flag. -/
def emptyFlag {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) :
    IsotropicFlag Q where
  len := 0
  sub _ := ⊥
  sub_zero := rfl
  strictMono i j hij := absurd hij (by
    rw [fin_eq_zero_of rfl i, fin_eq_zero_of rfl j]; exact lt_irrefl _)
  isotropic _ u hu := by rw [(Submodule.mem_bot K).mp hu, map_zero]

/-- The empty flag is full iff the Witt index is `0`. -/
theorem emptyFlag_isFull {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (h : wittIndex Q = 0) : (emptyFlag Q).IsFull := by
  refine ⟨h.symm, fun i => ?_⟩
  rw [fin_eq_zero_of rfl i]
  exact finrank_bot K V

/-- **Non-vacuity of `WhittakerDatum`**: a Whittaker datum for the toy GGP datum (empty flags,
trivial character; generic because `G` is abelian). -/
def toyWhittaker [TopologicalSpace K] : WhittakerDatum (toyData (K := K)) where
  flagW := emptyFlag _
  flagV := emptyFlag _
  fullW := emptyFlag_isFull toyData_wittIndex_QW
  fullV := emptyFlag_isFull toyData_wittIndex_QV
  χ _ := 1
  χ_one := rfl
  χ_mul _ _ := (mul_one 1).symm
  χ_norm _ := norm_one
  χ_cont := continuous_const
  generic b _ := iff_of_true (fun _ _ _ => rfl)
    ⟨b, toyData_mem_center b, 1, Subgroup.one_mem _, (mul_one b).symm⟩

theorem nonempty_whittakerDatum_toyData [TopologicalSpace K] :
    Nonempty (WhittakerDatum (toyData (K := K))) :=
  ⟨toyWhittaker⟩

/-- Over a `p`-adic field: an explicit quasi-split GGP datum with a Whittaker datum. -/
example {F : Type*} [NontriviallyNormedField F] [PAdicField F] :
    ∃ d : GGPData F, d.IsQuasiSplit ∧ Nonempty (WhittakerDatum d) :=
  ⟨toyData, toyData_isQuasiSplit, nonempty_whittakerDatum_toyData⟩

end Toy

/-! ## 4½. Amenability: the trivial representation is weakly contained in `L²(G)`

For a commutative closed subgroup `G` of the units of a finite-dimensional algebra over a
`p`-adic field (e.g. the toy `G = F^× × F^×`), the trivial representation is weakly contained in
the left regular representation.  Proof (Følner): `G` has a compact open subgroup `C`
(`latticeStab`: the stabilizer of the unit lattice `𝒪^d` under left multiplication); covering a
compact `K` by cosets `t_1 C, …, t_k C`, the sets `A_n = ⋃_{a ∈ [0,n]^k} t^a C` satisfy
`K · A_n ⊆ A_{n+1}` (here commutativity is used) and `μ(C) ≤ μ(A_n) ≤ (n+1)^k μ(C)`, so polynomial
growth forces `μ(A_{n+1}) ≤ (1+ε) μ(A_n)` for some `n`; then `1_{A_n}/√μ(A_n)` is almost
invariant under `K`. -/

section Amenable

open scoped InnerProductSpace ENNReal Pointwise

section WeakContainment

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- **Følner criterion** (uniform on compacta) for weak containment of a trivial representation
in `L²(G)`: if every compact `K` admits, for every `ε > 0`, a set `A` of finite positive Haar
measure with `μ(gA ∩ A) ≥ (1 - ε) μ(A)` for `g ∈ K`, then every representation `π` acting
trivially is weakly contained in the left regular representation (take `w = ‖v‖ 1_A/√μ(A)`). -/
theorem weaklyContainedIn_leftRegular_of_foelner (π : UnitaryRep G) (hπ : ∀ g v, π.ρ g v = v)
    (hF : ∀ K : Set G, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ A : Set G, MeasurableSet A ∧
      (Measure.haar : Measure G) A ≠ 0 ∧ (Measure.haar : Measure G) A ≠ ∞ ∧
      ∀ g ∈ K, (1 - ε) * (Measure.haar : Measure G).real A ≤
        (Measure.haar : Measure G).real ((fun x => g⁻¹ * x) ⁻¹' A ∩ A)) :
    WeaklyContainedIn π (leftRegular G) := by
  intro v K hK ε hε
  set μ : Measure G := Measure.haar
  have hv : 0 ≤ ‖v‖ ^ 2 := by positivity
  obtain ⟨A, hA, hA0, hAt, hFA⟩ := hF K hK (ε / (‖v‖ ^ 2 + 1)) (by positivity)
  have hApos : 0 < μ.real A := ENNReal.toReal_pos hA0 hAt
  let c : ℂ := ((‖v‖ / Real.sqrt (μ.real A) : ℝ) : ℂ)
  refine ⟨1, fun _ => indicatorConstLp 2 hA hAt c, fun g hg => ?_⟩
  have hpre : MeasurableSet ((fun x => g⁻¹ * x) ⁻¹' A) := hA.preimage (measurable_const_mul _)
  have hpret : μ ((fun x => g⁻¹ * x) ⁻¹' A) ≠ ∞ := by
    rwa [(measurePreserving_mul_left μ g⁻¹).measure_preimage hA.nullMeasurableSet]
  have h1 : ((leftRegular G).ρ g) (indicatorConstLp 2 hA hAt c) =
      indicatorConstLp 2 hpre hpret c := rfl
  have h2 : ⟪π.ρ g v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [hπ, inner_self_eq_norm_sq_to_K]; push_cast; rfl
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  have h3 : ⟪(indicatorConstLp 2 hpre hpret c : Lp ℂ 2 μ), indicatorConstLp 2 hA hAt c⟫_ℂ =
      μ.real ((fun x => g⁻¹ * x) ⁻¹' A ∩ A) • ⟪c, c⟫_ℂ :=
    L2.inner_indicatorConstLp_indicatorConstLp hpre hA hpret hAt c c
  rw [h1, h2]
  erw [h3]
  have hc : ⟪c, c⟫_ℂ = ((‖v‖ ^ 2 / μ.real A : ℝ) : ℂ) := by
    have hn : ‖c‖ ^ 2 = ‖v‖ ^ 2 / μ.real A := by
      simp only [c, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity), div_pow, Real.sq_sqrt hApos.le]
    rw [inner_self_eq_norm_sq_to_K, ← hn]; norm_cast
  rw [hc, Complex.real_smul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  have hle : μ.real ((fun x => g⁻¹ * x) ⁻¹' A ∩ A) ≤ μ.real A :=
    measureReal_mono Set.inter_subset_right hAt
  have hlo := hFA g hg
  have key : μ.real ((fun x => g⁻¹ * x) ⁻¹' A ∩ A) * (‖v‖ ^ 2 / μ.real A) ≤ ‖v‖ ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ hApos]; nlinarith
  rw [abs_of_nonneg (by linarith)]
  have hεv : ε / (‖v‖ ^ 2 + 1) * ‖v‖ ^ 2 < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
  have : ‖v‖ ^ 2 - μ.real ((fun x => g⁻¹ * x) ⁻¹' A ∩ A) * (‖v‖ ^ 2 / μ.real A)
      ≤ ε / (‖v‖ ^ 2 + 1) * ‖v‖ ^ 2 := by
    have e : μ.real ((fun x => g⁻¹ * x) ⁻¹' A ∩ A) * (‖v‖ ^ 2 / μ.real A) =
        (μ.real ((fun x => g⁻¹ * x) ⁻¹' A ∩ A) / μ.real A) * ‖v‖ ^ 2 := by ring
    rw [e]
    have : 1 - ε / (‖v‖ ^ 2 + 1) ≤ μ.real ((fun x => g⁻¹ * x) ⁻¹' A ∩ A) / μ.real A := by
      rw [le_div_iff₀ hApos]; linarith
    nlinarith
  linarith

end WeakContainment

/-- Exponential growth beats polynomial growth: `r^n ≤ (n+1)^k` fails for some `n` if `r > 1`. -/
lemma not_forall_pow_le_pow (k : ℕ) {r : ℝ} (hr : 1 < r) :
    ¬ ∀ n : ℕ, r ^ n ≤ ((n : ℝ) + 1) ^ k := by
  intro h
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt k hr).comp (tendsto_add_atTop_nat 1)
  have hr0 : (0 : ℝ) < r := by linarith
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (inv_pos.mpr hr0))).exists
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one] at hn
  have h1 := h n
  rw [div_lt_iff₀ (pow_pos hr0 _)] at hn
  have he : r⁻¹ * r ^ (n + 1) = r ^ n := by
    rw [pow_succ, mul_comm, mul_assoc, mul_inv_cancel₀ hr0.ne', mul_one]
  linarith

section Foelner

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- **Følner sets** for a commutative locally compact group with a compact open subgroup `C`:
uniformly on each compact `K`, there are sets `A` of finite positive Haar measure with
`μ(gA ∩ A) ≥ (1 - ε) μ(A)` (`A = ⋃_{a ∈ [0,n]^k} t^a C`, polynomial growth). -/
theorem foelner_of_compactOpenSubgroup (C : Subgroup G) (hCc : IsCompact (C : Set G))
    (hCo : IsOpen (C : Set G)) :
    ∀ K : Set G, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ A : Set G, MeasurableSet A ∧
      (Measure.haar : Measure G) A ≠ 0 ∧ (Measure.haar : Measure G) A ≠ ∞ ∧
      ∀ g ∈ K, (1 - ε) * (Measure.haar : Measure G).real A ≤
        (Measure.haar : Measure G).real ((fun x => g⁻¹ * x) ⁻¹' A ∩ A) := by
  classical
  intro K hK ε hε
  set μ : Measure G := Measure.haar
  -- cover `K` by finitely many cosets `x C`
  obtain ⟨s, -, hKs⟩ := hK.elim_nhds_subcover (fun x => x • (C : Set G)) fun x _ =>
    (hCo.smul x).mem_nhds ⟨1, C.one_mem, mul_one x⟩
  -- the sets `A n = ⋃_{a ∈ [0,n]^s} t^a C`
  let pw : (s → ℕ) → G := fun a => ∏ i : s, (i : G) ^ a i
  let box : ℕ → Finset (s → ℕ) := fun n => Fintype.piFinset fun _ => Finset.range (n + 1)
  let A : ℕ → Set G := fun n => ⋃ a ∈ box n, pw a • (C : Set G)
  have hAo : ∀ n, IsOpen (A n) := fun n => isOpen_biUnion fun a _ => hCo.smul _
  have hAc : ∀ n, IsCompact (A n) := fun n => (box n).isCompact_biUnion fun a _ => hCc.smul _
  have hAt : ∀ n, μ (A n) ≠ ∞ := fun n => (hAc n).measure_lt_top.ne
  have hC_A : ∀ n, (C : Set G) ⊆ A n := by
    intro n x hx
    refine Set.mem_iUnion₂.mpr ⟨0, ?_, ?_⟩
    · simp [box]
    · simpa [pw] using hx
  have hCpos : 0 < μ.real (C : Set G) :=
    ENNReal.toReal_pos (hCo.measure_pos μ ⟨1, C.one_mem⟩).ne' hCc.measure_lt_top.ne
  have hAlow : ∀ n, μ.real (C : Set G) ≤ μ.real (A n) := fun n =>
    measureReal_mono (hC_A n) (hAt n)
  have hAup : ∀ n, μ.real (A n) ≤ ((n : ℝ) + 1) ^ Fintype.card s * μ.real (C : Set G) := by
    intro n
    calc μ.real (A n) ≤ ∑ a ∈ box n, μ.real (pw a • (C : Set G)) :=
          measureReal_biUnion_finset_le _ _
      _ = ∑ a ∈ box n, μ.real (C : Set G) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          simp only [Measure.real, measure_smul]
      _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp [box]
  -- translation by `g ∈ K` maps `A n` into `A (n+1)` (uses commutativity)
  have hshift : ∀ n, ∀ g ∈ K, g • A n ⊆ A (n + 1) := by
    intro n g hg
    obtain ⟨i, his, hgi⟩ := Set.mem_iUnion₂.mp (hKs hg)
    obtain ⟨c', hc', rfl⟩ := hgi
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨a, ha, hya⟩ := Set.mem_iUnion₂.mp hy
    obtain ⟨c, hc, rfl⟩ := hya
    refine Set.mem_iUnion₂.mpr ⟨a + Pi.single ⟨i, his⟩ 1, ?_, c' * c, C.mul_mem hc' hc, ?_⟩
    · simp only [box, Fintype.mem_piFinset, Finset.mem_range] at ha ⊢
      intro j
      have := ha j
      simp only [Pi.add_apply]
      by_cases hj : j = ⟨i, his⟩
      · subst hj; simp; omega
      · rw [Pi.single_eq_of_ne hj]; omega
    · have hprod : ∏ j : s, (j : G) ^ (Pi.single (⟨i, his⟩ : s) 1 : s → ℕ) j = i := by
        rw [Finset.prod_eq_single (⟨i, his⟩ : s)
          (fun j _ hj => by rw [Pi.single_eq_of_ne hj, pow_zero]) (by simp)]
        simp
      simp only [pw, smul_eq_mul, Pi.add_apply, pow_add, Finset.prod_mul_distrib, hprod]
      ac_rfl
  -- some `n` has small growth
  have hgrow : ∃ n, μ.real (A (n + 1)) ≤ (1 + ε) * μ.real (A n) := by
    by_contra hcon
    push Not at hcon
    apply not_forall_pow_le_pow (Fintype.card s) (show 1 < 1 + ε by linarith)
    intro n
    have hexp : ∀ n, (1 + ε) ^ n * μ.real (C : Set G) ≤ μ.real (A n) := by
      intro n
      induction n with
      | zero => simpa using hAlow 0
      | succ n ih =>
        rw [pow_succ]
        nlinarith [hcon n]
    have := (hexp n).trans (hAup n)
    exact le_of_mul_le_mul_right this hCpos
  obtain ⟨n, hn⟩ := hgrow
  refine ⟨A n, (hAo n).measurableSet, ?_, hAt n, fun g hg => ?_⟩
  · exact (hAo n).measure_ne_zero μ ⟨1, hC_A n C.one_mem⟩
  · have hpre : (fun x => g⁻¹ * x) ⁻¹' A n = g • A n := Set.preimage_smul_inv g (A n)
    have hgA : μ (g • A n) ≠ ∞ := by rw [measure_smul]; exact hAt n
    have hmeas : μ.real (g • A n) = μ.real (A n) := by simp only [Measure.real, measure_smul]
    have hU : μ.real (g • A n ∪ A n) ≤ μ.real (A (n + 1)) :=
      measureReal_mono (Set.union_subset (hshift n g hg) (fun x hx => by
        obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hx
        refine Set.mem_iUnion₂.mpr ⟨a, ?_, hxa⟩
        simp only [box, Fintype.mem_piFinset, Finset.mem_range] at ha ⊢
        exact fun j => Nat.lt_succ_of_lt (ha j))) (hAt _)
    have hui := measureReal_union_add_inter (μ := μ) (s := g • A n) (hAo n).measurableSet hgA
      (hAt n)
    rw [hpre]
    nlinarith

end Foelner

section LatticeStab


variable (F : Type*) [NontriviallyNormedField F] [PAdicField F]
  {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A] [IsModuleTopology F A]

local notation "V" => (Fin (Module.finrank F A) → F)

/-- The stabilizer in `Aˣ` of the unit ball `𝒪^d ⊆ F^d` (for left multiplication). -/
def latticeStab : Subgroup Aˣ where
  carrier := {u | (∀ v ∈ Metric.closedBall (0 : V) 1, lmulPi F (u : A) v ∈ Metric.closedBall (0 : V) 1) ∧
    (∀ v ∈ Metric.closedBall (0 : V) 1, lmulPi F ((u⁻¹ : Aˣ) : A) v ∈ Metric.closedBall (0 : V) 1)}
  one_mem' := ⟨fun v hv => by simpa [lmulPi_one] using hv, fun v hv => by simpa [lmulPi_one] using hv⟩
  mul_mem' := by
    rintro u w ⟨hu1, hu2⟩ ⟨hw1, hw2⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [Units.val_mul, lmulPi_mul]; exact hu1 _ (hw1 _ hv)
    · rw [mul_inv_rev, Units.val_mul, lmulPi_mul]
      exact hw2 _ (hu2 _ hv)
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    exact ⟨hu2, by simpa using hu1⟩

lemma isCompact_latticeStab : IsCompact (latticeStab F (A := A) : Set Aˣ) := by
  have := isTopologicalRing_of_moduleTopology F A
  have := t2Space_of_moduleTopology F A
  have : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  set e := toPiCLE F A
  obtain ⟨l, hl0, hl⟩ := NormedField.exists_norm_lt F (show (0 : ℝ) < 1 / (‖e 1‖ + 1) by positivity)
  have hl0' : l ≠ 0 := norm_pos_iff.mp hl0
  have hle1 : l • e 1 ∈ Metric.closedBall (0 : V) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul]
    rw [lt_div_iff₀ (by positivity)] at hl
    nlinarith [norm_nonneg (e 1)]
  set B : Set A := e ⁻¹' Metric.closedBall (0 : V) ‖l⁻¹‖
  have hB : IsCompact B := e.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  have hbound : ∀ a : A, (∀ v ∈ Metric.closedBall (0 : V) 1, lmulPi F a v ∈ Metric.closedBall (0 : V) 1) →
      a ∈ B := by
    intro a ha
    have h := ha _ hle1
    have hcalc : lmulPi F a (l • e 1) = l • e a := by
      rw [lmulPi_apply, map_smul, ContinuousLinearEquiv.symm_apply_apply, mul_smul_comm, mul_one,
        map_smul]
    rw [hcalc, mem_closedBall_zero_iff, norm_smul] at h
    show e a ∈ Metric.closedBall (0 : V) ‖l⁻¹‖
    rw [mem_closedBall_zero_iff, norm_inv]
    calc ‖e a‖ = ‖l‖⁻¹ * (‖l‖ * ‖e a‖) := by field_simp
      _ ≤ ‖l‖⁻¹ * 1 := mul_le_mul_of_nonneg_left h (by positivity)
      _ = ‖l‖⁻¹ := mul_one _
  have hcl : ∀ f : Aˣ → A, Continuous f →
      IsClosed {u : Aˣ | ∀ v ∈ Metric.closedBall (0 : V) 1, lmulPi F (f u) v ∈ Metric.closedBall (0 : V) 1} := by
    intro f hf
    simp only [Set.ofPred_forall]
    exact isClosed_biInter fun v _ => Metric.isClosed_closedBall.preimage
      ((ContinuousLinearMap.apply F V v).continuous.comp ((continuous_lmulPi F).comp hf))
  have hclosed : IsClosed (latticeStab F (A := A) : Set Aˣ) :=
    (hcl _ Units.continuous_val).inter (hcl _ Units.continuous_coe_inv)
  have hK : IsCompact {u : Aˣ | (u : A) ∈ B ∧ ((u⁻¹ : Aˣ) : A) ∈ B} :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hB.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.mpr hB))
  exact hK.of_isClosed_subset hclosed fun u hu => ⟨hbound _ hu.1, hbound _ hu.2⟩

lemma isOpen_latticeStab : IsOpen (latticeStab F (A := A) : Set Aˣ) := by
  have := isTopologicalRing_of_moduleTopology F A
  have hUF : IsUltrametricDist F := PAdicField.toIsUltrametricDist
  have hUV : IsUltrametricDist V := Pi.instIsUltrametricDist
  have hsub : ∀ T : V →L[F] V, ‖T - 1‖ < 1 →
      ∀ v ∈ Metric.closedBall (0 : V) 1, T v ∈ Metric.closedBall (0 : V) 1 := by
    intro T hT v hv
    rw [mem_closedBall_zero_iff] at hv ⊢
    have h1 : ‖(T - 1) v‖ ≤ 1 :=
      ((T - 1).le_opNorm v).trans (by nlinarith [norm_nonneg (T - 1), norm_nonneg v])
    have : T v = v + (T - 1) v := by simp
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hv h1)
  have hc : ∀ f : Aˣ → A, Continuous f → Continuous fun u => dist (lmulPi F (f u)) 1 :=
    fun f hf => ((continuous_lmulPi F).comp hf).dist continuous_const
  let N : Set Aˣ := {u | dist (lmulPi F (u : A)) 1 < 1 ∧ dist (lmulPi F ((u⁻¹ : Aˣ) : A)) 1 < 1}
  have hN : IsOpen N := (isOpen_lt (hc _ Units.continuous_val) continuous_const).inter
    (isOpen_lt (hc _ Units.continuous_coe_inv) continuous_const)
  have h1N : (1 : Aˣ) ∈ N := by simp [N, lmulPi_one]
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hN.mem_nhds h1N) ?_)
  intro u hu
  exact ⟨hsub _ (by simpa only [dist_eq_norm] using hu.1),
    hsub _ (by simpa only [dist_eq_norm] using hu.2)⟩


include F in
/-- **Amenability of commutative `p`-adic groups** (in the form needed for temperedness):
for a closed commutative subgroup `G ≤ Aˣ` of the units of a finite-dimensional algebra over a
`p`-adic field, every representation acting trivially is weakly contained in `L²(G)`.
(Følner sets from the compact open subgroup `latticeStab ∩ G`.)  The topological-group,
local-compactness and Hausdorff instances are implicit so that they unify with whichever
instances the goal carries (e.g. `GGPData.instLocallyCompactSpaceG` for an inner form). -/
theorem weaklyContainedIn_leftRegular_of_isClosed_comm (Gs : Subgroup Aˣ)
    (hG : IsClosed (Gs : Set Aˣ)) (hcomm : ∀ a b : Gs, a * b = b * a) {_ : IsTopologicalGroup Gs}
    {_ : LocallyCompactSpace Gs} {_ : T2Space Gs} (π : UnitaryRep Gs) (hπ : ∀ g v, π.ρ g v = v) :
    WeaklyContainedIn π (leftRegular Gs) := by
  apply weaklyContainedIn_leftRegular_of_foelner π hπ
  let C := (latticeStab F (A := A)).subgroupOf Gs
  have hCo : IsOpen (C : Set Gs) := (isOpen_latticeStab F).preimage continuous_subtype_val
  have hCc : IsCompact (C : Set Gs) :=
    hG.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_latticeStab F)
  letI : CommGroup Gs := { (inferInstance : Group Gs) with mul_comm := hcomm }
  exact foelner_of_compactOpenSubgroup C hCc hCo

end LatticeStab

end Amenable

/-! ## 5. Toward `TemperedPacketFamily` for the toy datum (partially blocked) -/

section Packet

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- The (only) inner form of the toy datum: `W = 0` has no nontrivial twists, so
`Idx = Unit` (`H¹(F, SO(0)) = 1`). -/
def toyInnerForms : InnerFormSystem (toyData (K := F)) where
  Idx := Unit
  twist _ := (toyData (K := F)).reflTwist
  base := ()
  twist_base := rfl
  classify Q' _ _ := by
    refine ⟨(), ⟨?_⟩, fun _ _ => rfl⟩
    exact
      { toLinearEquiv := LinearEquiv.refl F (Fin 0 → F)
        map_app' := fun v => by
          rw [Subsingleton.elim v 0]
          simp only [map_zero]
          rfl }

/-- The trivial one-dimensional unitary representation. -/
def trivialRep (G : Type) [Group G] [TopologicalSpace G] : UnitaryRep G where
  H := ℂ
  ρ := 1
  unitary_ρ _ := one_mem _
  strongCont _ := continuous_const

theorem trivialRep_ρ_apply (G : Type) [Group G] [TopologicalSpace G] (g : G)
    (v : (trivialRep G).H) : (trivialRep G).ρ g v = v := by
  have : ((1 : G →* (ℂ →L[ℂ] ℂ)) g) = 1 := MonoidHom.one_apply g
  exact congrArg (fun T : ℂ →L[ℂ] ℂ => T (v : ℂ)) this

theorem trivialRep_isIrreducible (G : Type) [Group G] [TopologicalSpace G] :
    (trivialRep G).IsIrreducible := by
  refine ⟨inferInstanceAs (Nontrivial ℂ), fun W _ _ => ?_⟩
  exact Ideal.eq_bot_or_top W

/-- The trivial representation has an `(S, ξ)`-model whenever `ξ ≡ 1`. -/
theorem trivialRep_hasModel (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (S : Subgroup G) (ξ : ↥S → ℂ) (hξ : ∀ s, ξ s = 1) : HasModel (trivialRep G) S ξ := by
  intro hbot
  have hℓ : (smoothVectors (trivialRep G)).subtype ∈ equivariantForms (trivialRep G) S ξ := by
    intro s v
    rw [hξ, one_mul]
    exact trivialRep_ρ_apply G s (v : (trivialRep G).H)
  have hv : (1 : ℂ) ∈ smoothVectors (trivialRep G) :=
    ⟨⊤, isOpen_univ, fun u _ => trivialRep_ρ_apply G u (1 : ℂ)⟩
  rw [hbot] at hℓ
  have := LinearMap.congr_fun ((Submodule.mem_bot ℂ).mp hℓ) ⟨(1 : ℂ), hv⟩
  exact one_ne_zero this

/-- **(WHITT) holds for `{1}`**: for every Whittaker datum of the toy datum, the trivial
representation has a Whittaker model (the identity functional `π^∞ = ℂ → ℂ`; `U = 1`). -/
theorem toy_hasModel_trivial (w : WhittakerDatum (toyData (K := F))) :
    HasModel (trivialRep ↥(toyData (K := F)).G) w.U w.χ :=
  trivialRep_hasModel _ _ _ fun s => by
    rw [show s = 1 from Subtype.ext (toy_whittU_eq_one _ _ s.2)]
    exact w.χ_one

/-! ### Stable conjugacy in the toy datum is equality -/

/-- Base change `C(Q) → C(Q_{K̄})` is injective (`K̄` is flat over `K`). -/
theorem bcHom_injective {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V]
    [Module K V] (Q : QuadraticForm K V) : Function.Injective (bcHom Q) := by
  intro a b h
  have h' := congrArg (CliffordAlgebra.toBaseChange (AlgebraicClosure K) Q) h
  simp only [bcHom, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
    Function.comp_apply, toBaseChange_ofBaseChange] at h'
  exact Algebra.TensorProduct.includeRight_injective
    (algebraMap K (AlgebraicClosure K)).injective h'

theorem bcUnits_injective {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*}
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) : Function.Injective (bcUnits Q) :=
  fun _ _ h => Units.ext (bcHom_injective Q (congrArg Units.val h))

/-- If every vector of `V` is a multiple of `e`, every vector of `K̄ ⊗ V` is a multiple of
`1 ⊗ e`. -/
theorem baseChange_line {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] (e : V)
    (he : ∀ v : V, ∃ c : K, v = c • e) (t : AlgebraicClosure K ⊗[K] V) :
    ∃ a : AlgebraicClosure K, t = a • ((1 : AlgebraicClosure K) ⊗ₜ[K] e) := by
  induction t using TensorProduct.inductionOn with
  | tmul a v =>
    obtain ⟨c, rfl⟩ := he v
    refine ⟨a * algebraMap K _ c, ?_⟩
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.smul_def, mul_comm]
  | add t t' ht ht' =>
    obtain ⟨a, rfl⟩ := ht; obtain ⟨b, rfl⟩ := ht'
    exact ⟨a + b, (add_smul _ _ _).symm⟩

/-- A Clifford algebra of a "line" (every vector a multiple of `e`) over `K̄` is commutative. -/
theorem cliff_baseChange_line_comm {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*}
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (e : V)
    (he : ∀ v : V, ∃ c : K, v = c • e) (a b : CliffordAlgebra (Q.baseChange (AlgebraicClosure K))) :
    Commute a b := by
  refine cliff_commute_of_ι (fun t t' => ?_) a b
  obtain ⟨c, rfl⟩ := baseChange_line e he t
  obtain ⟨c', rfl⟩ := baseChange_line e he t'
  rw [map_smul, map_smul]
  exact ((Commute.refl _).smul_left _).smul_right _

/-- Stable conjugacy through the identity, in a commutative Clifford algebra over `K̄`, is
equality. -/
theorem eq_of_stablyConjVia_refl {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (hcomm : ∀ a b : CliffordAlgebra (Q.baseChange (AlgebraicClosure K)), Commute a b)
    {φ : (Q.baseChange (AlgebraicClosure K)).IsometryEquiv (Q.baseChange (AlgebraicClosure K))}
    (hφ : ∀ t, φ t = t) {x y : (CliffordAlgebra Q)ˣ} (h : StablyConjVia φ x y) :
    x = y := by
  obtain ⟨g, _, hg⟩ := h
  apply bcUnits_injective Q
  rw [← hg]
  have hmap : CliffordAlgebra.map φ.toIsometry = AlgHom.id _ _ := by
    apply CliffordAlgebra.hom_ext
    refine LinearMap.ext fun t => ?_
    show CliffordAlgebra.map φ.toIsometry (ι _ t) = ι _ t
    rw [CliffordAlgebra.map_apply_ι]
    exact congrArg _ (hφ t)
  have hc : cliffUnits φ (bcUnits Q x) = bcUnits Q x := by
    apply Units.ext
    show CliffordAlgebra.map φ.toIsometry _ = _
    rw [hmap]
    rfl
  rw [hc]
  have : Commute g (bcUnits Q x) := Units.ext (hcomm _ _)
  rw [this.eq, mul_inv_cancel_right]

theorem toy_line_V : ∀ v : (toyData (K := F)).V, ∃ c : F, v = c • ((0, fun _ => 1) : _) :=
  fun u => ⟨u.2 0, Prod.ext (Subsingleton.elim _ _) (funext fun i => by
    rw [fin_eq_zero_of rfl i]; simp)⟩

theorem toy_line_W : ∀ v : Fin (toyData (K := F)).m → F, ∃ c : F, v = c • 0 :=
  fun _ => ⟨0, Subsingleton.elim _ _⟩

/-- In the toy datum, stably conjugate elements of `G` are equal. -/
theorem toy_eq_of_stablyConj {x y : ↥(toyData (K := F)).G}
    (h : (toyData (K := F)).StablyConj x y) : x = y := by
  have h1 := eq_of_stablyConjVia_refl
    (cliff_baseChange_line_comm _ 0 toy_line_W) (fun _ => rfl) h.1
  have h2 := eq_of_stablyConjVia_refl
    (cliff_baseChange_line_comm _ _ toy_line_V) (fun _ => rfl) h.2
  apply Subtype.ext
  apply Units.ext
  exact Prod.ext (congrArg Units.val h1) (congrArg Units.val h2)

/-- The extension `φ ⊕ id_Z` of the trivial twist is the identity. -/
theorem twistV_reflTwist_apply {K : Type*} [Field K] [Invertible (2 : K)] (d : GGPData K)
    (t : AlgebraicClosure K ⊗[K] d.V) : d.twistV d.reflTwist t = t := by
  change (prodBaseChange d.QW d.QZ).toLinearEquiv.symm
    ((prodBaseChange d.QW d.QZ).toLinearEquiv t) = t
  exact (prodBaseChange d.QW d.QZ).toLinearEquiv.symm_apply_apply t

/-- In the toy datum, elements of `G` stably conjugate through the trivial twist are equal. -/
theorem toy_eq_of_stablyConjG_refl {x : ↥(toyData (K := F)).G}
    {y : ↥((toyData (K := F)).twist (toyData (K := F)).reflTwist).G}
    (h : (toyData (K := F)).StablyConjG (toyData (K := F)).reflTwist x y) : x = y := by
  have h1 := eq_of_stablyConjVia_refl
    (cliff_baseChange_line_comm _ 0 toy_line_W) (fun _ => rfl) h.1
  have h2 := eq_of_stablyConjVia_refl
    (cliff_baseChange_line_comm _ _ toy_line_V) (twistV_reflTwist_apply _) h.2
  apply Subtype.ext
  apply Units.ext
  exact Prod.ext (congrArg Units.val h1) (congrArg Units.val h2)

/-- **Toward non-vacuity of `TemperedPacketFamily`** (Thesis §6.3): the toy datum
with its single inner form and the packet `{1}` (trivial character of `G = GL₁ × GL₁`).
Every field is proved (the remaining `sorryAx` is upstream, see the module docstring):
* `stab`/`trans` hold because stable conjugacy in the toy `G` is equality
  (`toy_eq_of_stablyConj`, `toy_eq_of_stablyConjG_refl`: `C(Q) → C(Q_{F̄})` is injective and
  `C(Q_{F̄})` is commutative), so no knowledge of the epsilon-defined `charG` is needed;
* `whitt` holds since every Whittaker datum of `toyData` has `U = 1` (`toy_whittU_eq_one`);
* `tempered`: `1 ≺ λ_G` (weak containment of the trivial representation in
  `L²(F^× × F^×)`) is amenability of the abelian group `G`, proved here by Følner sets
  (`weaklyContainedIn_leftRegular_of_isClosed_comm`, §4½). -/
def toyPacketFamily : TemperedPacketFamily (toyData (K := F)) toyInnerForms where
  ι _ := Unit
  rep α _ := trivialRep _
  tempered α _ := ⟨trivialRep_isIrreducible _,
    weaklyContainedIn_leftRegular_of_isClosed_comm F _ (toyInnerForms.data α).isClosed_G
      (fun g h => toyData_G_comm g h) _ (trivialRep_ρ_apply _)⟩
  inequiv _ i j h := absurd (Subsingleton.elim i j) h
  central_trivial _ _ _ _ := rfl
  stab _ x y _ _ hxy := by
    have : x = y := toy_eq_of_stablyConj (F := F) hxy
    rw [this]
  trans _ x y _ _ hxy := by
    have hxy' : x = y := toy_eq_of_stablyConjG_refl hxy
    subst hxy'
    show _ = (kottwitzSign (toyData (K := F)) (toyData (K := F)).reflTwist : ℂ) * _
    rw [kottwitzSign_refl, Int.cast_one, one_mul]
    rfl
  whitt w := ⟨(), toy_hasModel_trivial w, fun _ _ => rfl⟩

end Packet

/-! ## 6. The toy trace formula

For the toy datum (`m = 0`, `r = 0`) `G = A_G ≅ F^× × F^×`, `G/A_G = 1`, `H = A_{G,H}` and
`Γ(G,H) = {GSpin(W)} = {F^×}`.  We compute both sides of the geometric expansion
(Thesis Thm 12.2.1) directly: `J(f) = f(1)` (`toyD_distribJ`), `θ_f = f` (`toyD_thetaF`) and
`m_geom(θ_f) = f(1)` (`toyD_mGeom`), so `GeomAt` holds (`toy_geomAt`).  This checks that the
normalizations of `J` (`weilMeasureHG`), `θ_f` (`orbitalPairing`, Haar on `G/A_G`) and `m_geom`
(`probHaar`, `weylCard`, `weylDisc`, `deltaGGP`, the germ at the zero orbit, `ĵ(0,·) = 1`) agree
**at the zero orbit**; nonzero orbits are not tested here (see `Sanity/NilpotentOrbit.lean`).
-/

section CoreToy

open Polynomial

section ToyStructure

variable {K : Type*} [Field K] [Invertible (2 : K)]

/-- A Clifford algebra element which is a unit and a scalar `c` has `c ≠ 0`. -/
theorem scalar_ne_zero_of_unit {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (u : (CliffordAlgebra Q)ˣ) {c : K} (hc : (u : CliffordAlgebra Q) = algebraMap K _ c) :
    c ≠ 0 := by
  rintro rfl
  rw [map_zero] at hc
  have h1 : (1 : CliffordAlgebra Q) = 0 := by
    rw [← u.mul_inv, hc, zero_mul]
  have h2 : algebraMap K (CliffordAlgebra Q) 1 = algebraMap K (CliffordAlgebra Q) 0 := by
    rw [map_one, map_zero]; exact h1
  exact one_ne_zero (algebraMap_cliff_injective Q h2)

/-- A `GSpin` element which is a scalar is in the image of `scalarGSpin`. -/
theorem mem_range_scalarGSpin_of_scalar {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (g : GSpin Q)
    (hg : ∃ c, ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = algebraMap K _ c) :
    g ∈ (scalarGSpin Q).range := by
  obtain ⟨c, hc⟩ := hg
  have hc0 := scalar_ne_zero_of_unit (g : (CliffordAlgebra Q)ˣ) hc
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [hc]
  rfl

/-- Every element of `GSpin(W)`, `W = 0`, is a scalar. -/
theorem toy_gspinW_mem_range (g : GSpin (toyData (K := K)).QW) :
    g ∈ (scalarGSpin (toyData (K := K)).QW).range :=
  mem_range_scalarGSpin_of_scalar g (toy_cliffW_scalar _)

/-- Every element of `GSpin(V)`, `V` a line, is a scalar. -/
theorem toy_gspinV_mem_range (g : GSpin (toyData (K := K)).QV) :
    g ∈ (scalarGSpin (toyData (K := K)).QV).range := by
  refine mem_range_scalarGSpin_of_scalar g (toy_cliffV_even_scalar _ ?_)
  have hev := g.2.1
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at hev
  exact hev

theorem scalarGSpin_range_le_splitCentral {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : (scalarGSpin Q).range ≤ splitCentralGSpin Q := by
  rintro _ ⟨c, rfl⟩
  exact scalarGSpin_mem_splitCentralGSpin Q c

/-- For the toy datum `A_G = G`. -/
theorem toy_AG_eq_top : (toyData (K := K)).AG = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ?_
  refine ⟨((toyData (K := K)).fst g, (toyData (K := K)).snd g), ⟨?_, ?_⟩, ?_⟩
  · exact scalarGSpin_range_le_splitCentral _ (toy_gspinW_mem_range _)
  · exact scalarGSpin_range_le_splitCentral _ (toy_gspinV_mem_range _)
  · exact (toyData (K := K)).G_ext rfl rfl

/-- For the toy datum `H = A_{G,H}`: `N = 1` (a unipotent scalar is `1`) and `GSpin(W)` is the
scalars. -/
theorem toy_mem_AGH_of_mem_H {h : ↥(toyData (K := K)).G} (hh : h ∈ (toyData (K := K)).H) :
    h ∈ (toyData (K := K)).AGH := by
  have hN : (toyData (K := K)).nPart h ∈ (toyData (K := K)).N := hh
  have hn1 : (toyData (K := K)).nPart h = 1 := by
    obtain ⟨c, hc⟩ := toy_gspinV_mem_range ((toyData (K := K)).nPart h)
    have h1 : ((((toyData (K := K)).nPart h : GSpin (toyData (K := K)).QV) :
        (CliffordAlgebra (toyData (K := K)).QV)ˣ) : CliffordAlgebra (toyData (K := K)).QV) = 1 :=
      eq_one_of_scalar_of_isNilpotent ⟨c, by rw [← hc]; rfl⟩ hN.2.2.2
    exact Subtype.ext (Units.ext h1)
  obtain ⟨c, hc⟩ := toy_gspinW_mem_range ((toyData (K := K)).fst h)
  refine ⟨c, ?_⟩
  have hsnd : (toyData (K := K)).snd h = (toyData (K := K)).incl ((toyData (K := K)).fst h) := by
    have : ((toyData (K := K)).incl ((toyData (K := K)).fst h))⁻¹ *
        (toyData (K := K)).snd h = 1 := hn1
    exact (inv_mul_eq_one.mp this).symm
  apply (toyData (K := K)).G_ext
  · exact hc
  · exact (congrArg (toyData (K := K)).incl hc).trans hsnd.symm

/-- The ambient algebra `C(W) × C(V)` of the toy datum is commutative. -/
theorem toy_ambient_comm (a b : (toyData (K := K)).ambient) : a * b = b * a :=
  Prod.ext (toyData_cliffW_comm _ _) (toyData_cliffV_comm _ _)

/-- Elements of the toy Lie algebra are pairs of scalars. -/
theorem toy_lie_scalar {X : (toyData (K := K)).ambient} (hX : X ∈ (toyData (K := K)).lie) :
    ∃ a b : K, X = (algebraMap K _ a, algebraMap K _ b) := by
  obtain ⟨hW, hV⟩ := hX
  obtain ⟨a, ha⟩ := toy_cliffW_scalar X.1
  have hev := hV.1
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at hev
  obtain ⟨b, hb⟩ := toy_cliffV_even_scalar X.2 hev
  exact ⟨a, b, Prod.ext ha hb⟩

end ToyStructure

section SS

variable {K : Type*} [NontriviallyNormedField K]

/-- An element annihilated by a squarefree polynomial is semisimple. -/
theorem isSS_of_aeval_eq_zero {A : Type*} [Ring A] [Algebra K A] {x : A} {p : K[X]}
    (hp : Squarefree p) (h : aeval x p = 0) : IsSS K x := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp ?_
  have := Polynomial.aeval_algHom_apply (Algebra.lmul K A) x p
  rw [h, map_zero] at this
  rw [← this]
  rfl

/-- A pair of scalars in a product of algebras is semisimple. -/
theorem isSS_pair_algebraMap {A₁ A₂ : Type*} [Ring A₁] [Algebra K A₁] [Ring A₂] [Algebra K A₂]
    (a b : K) : IsSS K ((algebraMap K A₁ a, algebraMap K A₂ b) : A₁ × A₂) := by
  by_cases hab : a = b
  · subst hab
    refine isSS_of_aeval_eq_zero (p := X - C a) separable_X_sub_C.squarefree ?_
    simp [Prod.algebraMap_apply]
  · have hcop : IsCoprime (X - C a) (X - C b) :=
      isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit
    refine isSS_of_aeval_eq_zero (p := (X - C a) * (X - C b))
      (separable_X_sub_C.mul separable_X_sub_C hcop).squarefree ?_
    simp only [map_mul, map_sub, aeval_X, aeval_C, Prod.algebraMap_apply]
    ext <;> simp

end SS

section Generic

/-- On a one-point group the Haar measure of Mathlib (`haarMeasure K₀` with `K₀(K₀) = 1`) is the
unit point mass: `haar(univ) = 1`. -/
theorem haar_univ_of_subsingleton {X : Type*} [Group X] [TopologicalSpace X]
    [IsTopologicalGroup X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [Subsingleton X] : (Measure.haar : Measure X) Set.univ = 1 := by
  set K₀ : TopologicalSpace.PositiveCompacts X := Classical.arbitrary _
  have hK : (K₀ : Set X) = Set.univ := K₀.nonempty.eq_univ
  change Measure.haarMeasure K₀ Set.univ = 1
  rw [← hK]
  exact Measure.haarMeasure_self

theorem haar_real_univ_of_subsingleton {X : Type*} [Group X] [TopologicalSpace X]
    [IsTopologicalGroup X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [Subsingleton X] : (Measure.haar : Measure X).real Set.univ = 1 := by
  rw [measureReal_def, haar_univ_of_subsingleton, ENNReal.toReal_one]

/-- On a subsingleton, an integral is the value times the total mass. -/
theorem integral_of_subsingleton {X E : Type*} [MeasurableSpace X] [Subsingleton X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X) (φ : X → E) (x₀ : X) :
    ∫ x, φ x ∂μ = μ.real Set.univ • φ x₀ := by
  have : φ = fun _ => φ x₀ := funext fun x => congrArg φ (Subsingleton.elim x x₀)
  rw [this, integral_const]

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
variable {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A]
  [IsModuleTopology F A]

theorem expA_zero : expA F (0 : A) = 1 := by
  letI := isTopologicalRing_of_moduleTopology F A
  exact NormedSpace.exp_zero

/-- The exponential is continuous at `0`. -/
theorem continuousAt_expA_zero : ContinuousAt (expA F : A → A) 0 := by
  letI := isTopologicalRing_of_moduleTopology F A
  obtain ⟨U, hU, -, h⟩ := expA_aux F (A := A)
  set B := Metric.eball (0 : (Fin (Module.finrank F A) → F) →L[F] (Fin (Module.finrank F A) → F))
    (NormedSpace.expSeries F ((Fin (Module.finrank F A) → F) →L[F]
      (Fin (Module.finrank F A) → F))).radius
  have heq : (fun X : A => lmulPiInv F (NormedSpace.exp (lmulPi F X))) =ᶠ[𝓝 0] expA F := by
    filter_upwards [hU] with X hX
    rw [← (h X hX).2.2, lmulPiInv_lmulPi]
  refine ContinuousAt.congr ?_ heq
  have h0 : lmulPi F (0 : A) ∈ B := (h 0 (mem_of_mem_nhds hU)).1
  have hexp : ContinuousAt (NormedSpace.exp : _ → _) (lmulPi F (0 : A)) :=
    (NormedSpace.continuousOn_exp (𝕂 := F)).continuousAt (Metric.isOpen_eball.mem_nhds h0)
  exact (lmulPiInv F).continuous.continuousAt.comp
    (hexp.comp (continuous_lmulPi F).continuousAt)

/-- **Local constancy transported along `x e^X`**: if `θ` is constant near `x` in `G(F)`, then
`θ(y) = θ(x)` whenever `y = x e^X` with `X` in a neighbourhood of `0` (the topology of
`G(F) ⊆ Aˣ` is that of `A × Aᵐᵒᵖ` via `(y, y⁻¹)`; `e^{-X} x⁻¹` is the inverse of `x e^X`). -/
theorem exists_nhds_zero_mul_expA {G : Subgroup Aˣ} {θ : ↥G → ℂ} {x : ↥G}
    (hθ : ∀ᶠ y in 𝓝 x, θ y = θ x) :
    ∃ ω ∈ 𝓝 (0 : A), ∀ X ∈ ω, ∀ y : ↥G,
      ((y : Aˣ) : A) = ((x : Aˣ) : A) * expA F X → θ y = θ x := by
  letI := isTopologicalRing_of_moduleTopology F A
  -- the neighbourhood of `x` in `G`, pulled back to `A × Aᵐᵒᵖ`
  rw [nhds_subtype, Filter.eventually_comap] at hθ
  have hθ' : ∀ᶠ u in 𝓝 (x : Aˣ), ∀ y : ↥G, (y : Aˣ) = u → θ y = θ x := hθ
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.eventually_comap] at hθ'
  -- continuity of `X ↦ (x e^X, op (e^{-X} x⁻¹))` at `0`
  set f : A → A × Aᵐᵒᵖ := fun X => (((x : Aˣ) : A) * expA F X,
      MulOpposite.op (expA F (-X) * (((x : Aˣ)⁻¹ : Aˣ) : A))) with hf
  have hc : ContinuousAt f 0 := by
    have h1 : ContinuousAt (fun X : A => expA F X) 0 := continuousAt_expA_zero
    have h2 : ContinuousAt (fun X : A => expA F (-X)) 0 := by
      have : ContinuousAt (fun X : A => -X) 0 := continuous_neg.continuousAt
      exact ContinuousAt.comp (g := expA F) (by simpa using continuousAt_expA_zero) this
    refine ContinuousAt.prodMk (continuousAt_const.mul h1) ?_
    exact MulOpposite.continuous_op.continuousAt.comp (h2.mul continuousAt_const)
  have hval : f 0 = Units.embedProduct A (x : Aˣ) := by
    simp [hf, expA_zero, Units.embedProduct]
  have hc2 : Tendsto f (𝓝 0) (𝓝 (Units.embedProduct A (x : Aˣ))) := by
    rw [← hval]; exact hc
  obtain ⟨U, hU, hUinv⟩ := expA_mul_expA_neg F (A := A)
  refine ⟨_, Filter.inter_mem (hc2.eventually hθ') hU, fun X hX y hy => ?_⟩
  obtain ⟨hX1, hX2⟩ := hX
  refine hX1 (y : Aˣ) ?_ y rfl
  -- `y⁻¹ = e^{-X} x⁻¹`
  have hinv : (((y : Aˣ)⁻¹ : Aˣ) : A) = expA F (-X) * (((x : Aˣ)⁻¹ : Aˣ) : A) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hy, mul_assoc, ← mul_assoc (expA F X), hUinv X hX2, one_mul, Units.mul_inv]
  simp only [hf, Units.embedProduct_apply, hy, hinv]


/-- **`ĵ(0, ·) = 1` pointwise** on a Lie algebra all of whose elements are regular semisimple
(e.g. an abelian `𝔤` of semisimple elements), provided a self-dual measure for `b|_𝔤` exists.
`ĵ(0, ·)` is defined by an epsilon (`jHat`): any `j` with `IsJHat` is continuous on `𝔤_reg = 𝔤`
and satisfies `∫ f j = f̂(0) = ∫ f` for all test functions; testing against the indicator of a small
compact open neighbourhood of a point (Haar measure is positive on nonempty open sets) gives
`j = 1` everywhere.  Without a self-dual measure `selfDualHaar = 0` and `ĵ(0, ·)` would be an
arbitrary continuous function. -/
theorem jHat_zeroOrbit_eq_one (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A)
    (b : LinearMap.BilinForm F A) (ψ : NontrivialAddChar F)
    (hsd : ∃ μ, IsSelfDual μ (restrictForm 𝔤 b) ψ)
    (hreg : ∀ X : ↥𝔤, IsRegularSS 𝔤 (X : A)) {X : A} (hX : X ∈ 𝔤) :
    jHat G 𝔤 b ψ (zeroOrbit G 𝔤) X = 1 := by
  haveI := measurableSingletonClass_lie 𝔤
  haveI := locallyCompactSpace_lie 𝔤
  haveI : T2Space A := t2Space_of_moduleTopology F A
  haveI : TotallyDisconnectedSpace A := totallyDisconnectedSpace_of_moduleTopology F A
  have hJ : ∃ j, IsJHat G 𝔤 b ψ (zeroOrbit G 𝔤) j := exists_isJHat_zeroOrbit G 𝔤 b ψ
  have hμ : (selfDualHaar 𝔤 b ψ).IsAddHaarMeasure := by
    unfold selfDualHaar selfDualMeasure
    rw [dite_eq_left_of_eq_true (eq_true hsd)]
    exact hsd.choose_spec.1
  obtain ⟨hjc, -, hjint⟩ := hJ.choose_spec
  have hjcont : Continuous hJ.choose := by
    exact continuousOn_univ.mp (hjc.mono fun Y _ => hreg Y)
  -- `∫ f j = ∫ f` for every test function
  have key : ∀ f : ↥𝔤 → ℂ, IsTestFn f →
      ∫ Y, f Y * hJ.choose Y ∂(selfDualHaar 𝔤 b ψ) = ∫ Y, f Y ∂(selfDualHaar 𝔤 b ψ) := by
    intro f hf
    rw [← hjint f hf, orbitMeasure_zeroOrbit, integral_dirac]
    simp [fourierLie, fourierWRT]
  unfold jHat
  rw [dite_eq_left_of_eq_true (eq_true hJ), dite_eq_left_of_eq_true (eq_true hX)]
  set j := hJ.choose
  set μ := selfDualHaar 𝔤 b ψ
  set X₀ : ↥𝔤 := ⟨X, hX⟩
  by_contra hne
  have hz : j X₀ - 1 ≠ 0 := sub_ne_zero.mpr hne
  set ε := ‖j X₀ - 1‖ / 2 with hεdef
  have hε : 0 < ε := by have := norm_pos_iff.mpr hz; positivity
  have hU : IsOpen (j ⁻¹' Metric.ball (j X₀) ε) := Metric.isOpen_ball.preimage hjcont
  obtain ⟨V, hVc, hVo, hXV, hVU⟩ := exists_isCompact_isClopen_between isCompact_singleton hU
    (Set.singleton_subset_iff.mpr (Metric.mem_ball_self hε))
  have hX₀V : X₀ ∈ V := hXV rfl
  have hf : IsTestFn (V.indicator (1 : ↥𝔤 → ℂ)) := by
    refine ⟨?_, HasCompactSupport.intro' hVc hVc.isClosed fun x hx => Set.indicator_of_notMem hx _⟩
    rw [← LocallyConstant.coe_charFn ℂ hVo]
    exact (LocallyConstant.charFn ℂ hVo).isLocallyConstant
  have hVm : MeasurableSet V := hVo.isOpen.measurableSet
  have e1 : ∫ Y, V.indicator (1 : ↥𝔤 → ℂ) Y * j Y ∂μ = ∫ Y in V, j Y ∂μ := by
    rw [← integral_indicator hVm]
    congr 1
    funext Y
    by_cases hY : Y ∈ V <;> simp [hY]
  have e2 : ∫ Y, V.indicator (1 : ↥𝔤 → ℂ) Y ∂μ = (μ.real V : ℂ) := by
    rw [integral_indicator hVm]
    simp only [Pi.one_apply]
    rw [setIntegral_const]
    simp
  have h1 := key _ hf
  rw [e1, e2] at h1
  have hint : IntegrableOn j V μ := hjcont.continuousOn.integrableOn_compact hVc
  have e3 : ∫ Y in V, (j Y - j X₀) ∂μ = -((μ.real V : ℂ) * (j X₀ - 1)) := by
    rw [integral_sub hint (integrableOn_const hVc.measure_lt_top.ne), h1, setIntegral_const]
    simp only [Complex.real_smul]
    ring
  have hbound : ‖∫ Y in V, (j Y - j X₀) ∂μ‖ ≤ ε * μ.real V :=
    norm_setIntegral_le_of_norm_le_const hVc.measure_lt_top fun Y hY =>
      (mem_ball_iff_norm.mp (hVU hY)).le
  have hpos : 0 < μ.real V :=
    ENNReal.toReal_pos (hVo.isOpen.measure_ne_zero μ ⟨X₀, hX₀V⟩) hVc.measure_lt_top.ne
  rw [e3, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le] at hbound
  have : μ.real V * ‖j X₀ - 1‖ = 2 * (ε * μ.real V) := by rw [hεdef]; ring
  nlinarith

end Generic

section ToyPAdic

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- The toy datum `toyData` over `F`, as a plain definition: with the `abbrev` the instances on
`H(F)/A_{G,H}(F)`, `G(F)/A_G(F)` (keyed on `GGPData.HmodAGH d` etc.) are not found by instance
search, because `toyData` unfolds to a structure literal. -/
def toyD : GGPData F := toyData

local notation "𝕋" => (toyD (F := F))

theorem toyD_AG_eq_top : (𝕋).AG = ⊤ := toy_AG_eq_top

theorem toyD_mem_AGH_of_mem_H {h : ↥(𝕋).G} (hh : h ∈ (𝕋).H) : h ∈ (𝕋).AGH :=
  toy_mem_AGH_of_mem_H hh

theorem toyD_G_comm (g h : ↥(𝕋).G) : g * h = h * g := toyData_G_comm g h

theorem toyD_ambient_comm (a b : (𝕋).ambient) : a * b = b * a := toy_ambient_comm a b


/-- Elements of the toy `G` are pairs of scalars. -/
theorem toy_G_scalar (g : ↥(𝕋).G) :
    ∃ a b : F, ((g : (𝕋).ambientˣ) : (𝕋).ambient) = (algebraMap F _ a, algebraMap F _ b) := by
  obtain ⟨a, ha⟩ := toy_gspinW_mem_range ((𝕋).fst g)
  obtain ⟨b, hb⟩ := toy_gspinV_mem_range ((𝕋).snd g)
  refine ⟨(a : F), (b : F), Prod.ext ?_ ?_⟩
  · have := congrArg (fun u : GSpin (𝕋).QW => ((u : (CliffordAlgebra (𝕋).QW)ˣ) : CliffordAlgebra (𝕋).QW)) ha
    exact this.symm
  · have := congrArg (fun u : GSpin (𝕋).QV => ((u : (CliffordAlgebra (𝕋).QV)ˣ) : CliffordAlgebra (𝕋).QV)) hb
    exact this.symm

/-- In the toy Lie algebra every centralizer is the whole algebra (the ambient algebra is
commutative). -/
theorem toy_lieCentralizer_eq (L : LieSubalgebra F (𝕋).ambient) (x : (𝕋).ambient) :
    lieCentralizer L x = L := by
  ext X
  rw [mem_lieCentralizer]
  exact ⟨fun h => h.1, fun h => ⟨h, toyD_ambient_comm _ _⟩⟩

theorem toy_isLieAbelian (L : LieSubalgebra F (𝕋).ambient) : IsLieAbelian ↥L :=
  ⟨fun X Y => by
    apply Subtype.ext
    rw [LieSubalgebra.coe_bracket, Ring.lie_def, toyD_ambient_comm, sub_self]
    rfl⟩

/-- **Every element of the toy `G` is regular semisimple.** -/
theorem toy_regularSet_eq_univ : regularSet (𝕋).G (𝕋).lie = Set.univ := by
  refine Set.eq_univ_of_forall fun g => ⟨?_, toy_isLieAbelian _⟩
  obtain ⟨a, b, h⟩ := toy_G_scalar g
  rw [h]
  exact isSS_pair_algebraMap a b

instance toy_subsingleton_GmodAG : Subsingleton (𝕋).GmodAG :=
  ⟨fun x y => Quotient.inductionOn₂' x y fun a b =>
    QuotientGroup.eq.mpr (by rw [toyD_AG_eq_top]; trivial)⟩

instance toy_subsingleton_HmodAGH : Subsingleton (𝕋).HmodAGH :=
  ⟨fun x y => Quotient.inductionOn₂' x y fun a b =>
    QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr (toyD_mem_AGH_of_mem_H (a⁻¹ * b).2))⟩

instance toy_subsingleton_HGQuot : Subsingleton (𝕋).HGQuot :=
  ⟨fun x y => Quotient.inductionOn₂ x y fun a b => congrArg _ (Subsingleton.elim a b)⟩

/-- **The elliptic regular set of the toy datum is all of `G`** (non-vacuity of the hypotheses of
`prop_11_5_1_ii_ell` and `exists_scusp_ell`). -/
theorem toyD_ellRegSet : (𝕋).ellRegSet = Set.univ := by
  refine Set.eq_univ_of_forall fun g => ⟨?_, ?_⟩
  · rw [toy_regularSet_eq_univ]; trivial
  · exact Set.Subsingleton.isCompact fun x _ y _ => Subsingleton.elim (α := (𝕋).GmodAG) x y


variable (χ : CentralCharOn (toyD (F := F))) (ψ : NontrivialAddChar F)

/-- A `χ⁻¹`-equivariant function takes the value `f(1)` on `A_{G,H}` (`χ` is trivial there). -/
theorem toy_apply_of_mem_AGH {f : ↥(𝕋).G → ℂ} (hf : IsChiEquivariant (𝕋) χ f) {h : ↥(𝕋).G}
    (hh : h ∈ (𝕋).AGH) : f h = f 1 := by
  have := hf ⟨h, (𝕋).AGH_le_AG hh⟩ 1
  rw [mul_one, χ.trivial_AGH h hh] at this
  simpa using this

/-- **The kernel of the toy datum**: `K(f, x) = f(1)` (Thesis §7.1; here `H = A_{G,H}`, so
`H/A_{G,H}` is a point of Haar mass `1`, and `ξ = 1`). -/
theorem toyD_kernelK {f : ↥(𝕋).G → ℂ} (hf : IsChiEquivariant (𝕋) χ f) (x : ↥(𝕋).G) :
    kernelK (𝕋) ψ f x = f 1 := by
  have key : ∀ q : (𝕋).HmodAGH, kernelIntegrand (𝕋) ψ f x (Quotient.out q) = f 1 := by
    intro q
    have hh : ((Quotient.out q : ↥(𝕋).H) : ↥(𝕋).G) ∈ (𝕋).AGH :=
      toyD_mem_AGH_of_mem_H (Quotient.out q).2
    have hc : x⁻¹ * ((Quotient.out q : ↥(𝕋).H) : ↥(𝕋).G) * x = (Quotient.out q : ↥(𝕋).H) := by
      rw [toyD_G_comm x⁻¹, inv_mul_cancel_right]
    unfold kernelIntegrand
    rw [hc, toy_apply_of_mem_AGH χ hf hh, (𝕋).xi_eq_one_of_mem_AGH' ψ.toAddChar _ hh, mul_one]
  unfold kernelK
  simp_rw [key]
  rw [integral_const, haar_real_univ_of_subsingleton, one_smul]

/-- A Weil measure exists for the toy datum: `dirac` at the unique point of `H\G/A_G`. -/
theorem toy_exists_weil : ∃ m, IsWeilMeasure (𝕋).toGmodAG
    (Measure.haar : Measure (𝕋).GmodAG) (Measure.haar : Measure (𝕋).HmodAGH) m := by
  refine ⟨Measure.dirac (CosetSpace.mk (𝕋).toGmodAG 1), ?_⟩
  intro φ _ _
  have hpt : (𝕋).toGmodAG 1 * CosetSpace.out (𝕋).toGmodAG (CosetSpace.mk (𝕋).toGmodAG 1) = 1 :=
    toy_subsingleton_GmodAG.elim _ _
  simp only [integral_of_subsingleton (Measure.haar : Measure (𝕋).GmodAG) φ 1,
    @integral_of_subsingleton _ _ _ toy_subsingleton_HGQuot _ _ _
      (Measure.dirac (CosetSpace.mk (𝕋).toGmodAG 1)) _ (CosetSpace.mk (𝕋).toGmodAG 1),
    integral_of_subsingleton (Measure.haar : Measure (𝕋).HmodAGH) _ 1, hpt,
    haar_real_univ_of_subsingleton (X := (𝕋).GmodAG),
    haar_real_univ_of_subsingleton (X := (𝕋).HmodAGH), probReal_univ, one_smul]

/-- The Weil measure `dx` on the point `H\G/A_G` has mass `1` (from `IsWeilMeasure` with
`φ = 1`; no axiom is used: the toy Weil measure exists by `toy_exists_weil`). -/
theorem toy_weilMeasureHG_real_univ : (𝕋).weilMeasureHG.real Set.univ = 1 := by
  have hW := (𝕋).weilMeasureHG_spec_of_exists toy_exists_weil
  have h := hW (fun _ => 1) continuous_const (HasCompactSupport.of_compactSpace _)
  simp only [integral_const, haar_real_univ_of_subsingleton (X := (𝕋).GmodAG),
    haar_real_univ_of_subsingleton (X := (𝕋).HmodAGH), smul_eq_mul, mul_one] at h
  exact h.symm

/-- **`J(f) = f(1)` for the toy datum** (Thesis §7.1, §10.1). -/
theorem toyD_distribJ {f : ↥(𝕋).G → ℂ} (hf : IsChiEquivariant (𝕋) χ f) :
    distribJ (𝕋) ψ f = f 1 := by
  unfold distribJ
  simp_rw [toyD_kernelK χ ψ hf]
  rw [integral_const, toy_weilMeasureHG_real_univ, one_smul]

/-- For the toy datum every continuous `f` represents its own orbital pairing (`G` is abelian
and `G/A_G` is a point of Haar mass `1`). -/
theorem toyD_isThetaF {f : ↥(𝕋).G → ℂ} (hf : Continuous f) : IsThetaF (𝕋) f f := by
  refine ⟨hf.locallyIntegrable, hf.continuousOn, fun f' _ => ?_⟩
  rw [orbitalPairing, integral_of_subsingleton (Measure.haar : Measure (𝕋).GmodAG) _ 1,
    haar_real_univ_of_subsingleton, one_smul]
  congr 1
  funext g
  rw [toyD_G_comm _ g, inv_mul_cancel_right]

/-- `θ_f = f` on all of `G` for the toy datum, for every continuous `f` (uniqueness of `θ_f` on
`G_reg = G`, by separation with test functions; no Harish-Chandra axiom is used). -/
theorem toyD_thetaF_eq {f : ↥(𝕋).G → ℂ} (hf : Continuous f) : thetaF (𝕋) f = f := by
  have h1 := isThetaF_thetaF_of_exists (𝕋) f ⟨f, toyD_isThetaF hf⟩
  have h2 := toyD_isThetaF hf
  haveI := totallyDisconnectedSpace_subgroup F (𝕋).ambient (𝕋).G
  have hae : thetaF (𝕋) f =ᵐ[Measure.haar] f :=
    ae_eq_of_integral_testFunctions h1.1 h2.1 fun f' hf' => by rw [h1.2.2 f' hf', h2.2.2 f' hf']
  have hc : Continuous (thetaF (𝕋) f) := by
    refine continuousOn_univ.mp ?_
    rw [← toy_regularSet_eq_univ]
    exact h1.2.1
  exact (hc.ae_eq_iff_eq Measure.haar hf).mp hae

/-- **`θ_f = c · f` with `c` the Haar mass of the point `G/A_G`**, for
`f ∈ 𝒞_scusp`; Mathlib's normalization gives `c = 1` (`haar_real_univ_of_subsingleton`). -/
theorem toyD_thetaF {f : ↥(𝕋).G → ℂ} (hf : f ∈ ScuspTestFn (𝕋) χ) :
    thetaF (𝕋) f = (((Measure.haar : Measure (𝕋).GmodAG).real Set.univ : ℝ) : ℂ) • f := by
  rw [haar_real_univ_of_subsingleton, Complex.ofReal_one, one_smul]
  exact toyD_thetaF_eq hf.1.continuous


/-! ### The geometric side for the toy datum -/

theorem absF_one' : absF (1 : F) = 1 := by
  rw [absF_of_ne_zero one_ne_zero]
  have : Units.mk0 (1 : F) one_ne_zero = 1 := Units.ext rfl
  rw [this, map_one]
  rfl

instance toyD_subsingleton_W : Subsingleton (Fin (𝕋).m → F) :=
  (inferInstance : Subsingleton (Fin 0 → F))

theorem toyD_gspinW_comm (a b : GSpin (𝕋).QW) : a * b = b * a :=
  Subtype.ext (Units.ext (toyData_cliffW_comm (K := F) _ _).eq)

theorem toyD_gspinW_scalar (x : GSpin (𝕋).QW) :
    ∃ c : F, ((x : (CliffordAlgebra (𝕋).QW)ˣ) : CliffordAlgebra (𝕋).QW) = algebraMap F _ c := by
  obtain ⟨c, hc⟩ := toy_gspinW_mem_range (K := F) x
  exact ⟨(c : F), by rw [← hc]; rfl⟩

/-- `T_x = GSpin(W)` for every `x` (the group is commutative and `W = 0`). -/
theorem toyD_torusOf (x : GSpin (𝕋).QW) : (𝕋).torusOf x = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ⟨?_, ?_⟩
  · exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]; exact toyD_gspinW_comm _ _
  · intro w _
    exact Subsingleton.elim _ _

instance toyD_subsingleton_torusQuot (T : Subgroup (GSpin (𝕋).QW)) :
    Subsingleton ((𝕋).TorusQuot T) :=
  ⟨fun x y => Quotient.inductionOn₂' x y fun _ _ =>
    QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr (toy_gspinW_mem_range (K := F) _))⟩

/-- Every `x ∈ GSpin(W)(F) = F^×` lies in `Γ(G,H)`. -/
theorem toyD_isGammaElt (x : GSpin (𝕋).QW) : (𝕋).IsGammaElt x := by
  refine ⟨?_, fun a _ b _ => toyD_gspinW_comm a b, Finite.compactSpace⟩
  obtain ⟨c, hc⟩ := toyD_gspinW_scalar x
  rw [hc]
  exact isSS_of_aeval_eq_zero (p := Polynomial.X - Polynomial.C c)
    Polynomial.separable_X_sub_C.squarefree (by simp)

/-- The torus `GSpin(W)` as an element of `𝒯`. -/
def toyD_gammaTorus : (𝕋).GammaTorus := ⟨⊤, 1, toyD_isGammaElt 1, toyD_torusOf 1⟩

theorem toyD_gammaTorus_val (T : (𝕋).GammaTorus) : T.1 = ⊤ := by
  obtain ⟨x, -, hx⟩ := T.2
  rw [← hx, toyD_torusOf]

/-- The unique class of `Γ(G,H)` for the toy datum. -/
def toyD_gammaClass : GammaClass (𝕋) := Quot.mk _ toyD_gammaTorus

instance toyD_subsingleton_gammaClass : Subsingleton (GammaClass (𝕋)) :=
  ⟨fun x y => Quot.inductionOn x fun a => Quot.inductionOn y fun b =>
    congrArg _ (Subtype.ext ((toyD_gammaTorus_val a).trans (toyD_gammaTorus_val b).symm))⟩

/-- `|W(T)| = 1` for every `T` (the group is commutative). -/
theorem toyD_weylCardOf (T : Subgroup (GSpin (𝕋).QW)) : weylCardOf (𝕋) T = 1 := by
  unfold weylCardOf
  have : Subsingleton (↥(Subgroup.normalizer (T : Set (GSpin (𝕋).QW))) ⧸
      (Subgroup.centralizer (T : Set (GSpin (𝕋).QW))).subgroupOf
        (Subgroup.normalizer (T : Set (GSpin (𝕋).QW)))) :=
    ⟨fun x y => Quotient.inductionOn₂' x y fun _ _ => QuotientGroup.eq.mpr
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_centralizer_iff.mpr fun _ _ =>
        toyD_gspinW_comm _ _))⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨this, ⟨1⟩⟩

theorem probHaar_real_univ (Q : Type*) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [MeasurableSpace Q] [BorelSpace Q] [CompactSpace Q] : (probHaar Q).real Set.univ = 1 := by
  unfold probHaar
  rw [dite_eq_left_of_eq_true (eq_true ‹_›), measureReal_def]
  have : Measure.haarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ :
      TopologicalSpace.PositiveCompacts Q) Set.univ = 1 := Measure.haarMeasure_self
  rw [this, ENNReal.toReal_one]

/-- `Δ(t) = 1` (`W'' = 0`). -/
theorem toyD_deltaGGP (t : GSpin (𝕋).QW) : deltaGGP (𝕋) t = 1 := by
  unfold deltaGGP
  rw [LinearMap.det_eq_one_of_subsingleton, absF_one']

/-- `D^G(t) = 1` for the toy datum (`Ad t` is trivial on the commutative ambient algebra). -/
theorem toyD_weylDisc (x : (𝕋).ambientˣ) : weylDisc (𝕋).lie x = 1 := by
  have hconj : ∀ X : (𝕋).ambient, conjAd F x X = X := fun X => by
    rw [conjAd_apply, toyD_ambient_comm (x : (𝕋).ambient) X, mul_assoc, Units.mul_inv, mul_one]
  have hst : ∀ X ∈ (𝕋).lie.toSubmodule, conjAd F x X ∈ (𝕋).lie.toSubmodule := fun X hX => by
    rw [hconj]; exact hX
  unfold weylDisc
  rw [dite_eq_left_of_eq_true (eq_true hst)]
  have h0 : (conjAd F x).toLinearEquiv.toLinearMap.restrict hst = 1 :=
    LinearMap.ext fun v => Subtype.ext (hconj (v : (𝕋).ambient))
  rw [h0, sub_self, LinearMap.charpoly_zero, Polynomial.trailingCoeff, Polynomial.natTrailingDegree_X_pow,
    Polynomial.coeff_X_pow_self, absF_one']


/-- The trace form `b(X,Y) = tr(L_{XY})` of a GGP datum is symmetric (`tr(L_X L_Y) = tr(L_Y L_X)`). -/
theorem ggp_bilin_symm (d : GGPData F) (X Y : d.ambient) : d.bilin X Y = d.bilin Y X := by
  rw [GGPData.bilin_apply, GGPData.bilin_apply, LinearMap.mulLeft_mul, ← Module.End.mul_eq_comp,
    LinearMap.trace_mul_comm, Module.End.mul_eq_comp, ← LinearMap.mulLeft_mul]

/-- The restriction of `b` to `𝔤` is nondegenerate (left and right separating), for every GGP
datum (Thesis §2.4): `GGPData.bilin_nondegenerate_lie` plus symmetry. -/
theorem restrictForm_lie_nondegenerate (d : GGPData F) :
    (restrictForm d.lie d.bilin).Nondegenerate := by
  have hL : ∀ X : ↥d.lie, (∀ Y : ↥d.lie, restrictForm d.lie d.bilin X Y = 0) → X = 0 :=
    fun X hX => Subtype.ext (d.bilin_nondegenerate_lie X X.2 fun Y hY => hX ⟨Y, hY⟩)
  refine ⟨hL, fun Y hY => hL Y fun X => ?_⟩
  have := hY X
  simp only [restrictForm, LinearMap.compl₁₂_apply] at this ⊢
  rw [ggp_bilin_symm]; exact this

/-- **A self-dual measure exists on the toy Lie algebra** `𝔤 = gspin(0) × gspin(1) = F × F`, for
the restriction of the trace form `b` (Thesis §2.4).  Here `b((a,b),(a',b')) = aa' + 2bb'` (the
trace of left multiplication on `C(0) × C(V) = F × C(V)`, `dim C(V) = 2`), a nondegenerate form,
so this is Fourier inversion on `F²` for Schwartz–Bruhat functions with the Haar measure
self-dual for `ψ ∘ b` (Tate's thesis; Weil, *Basic Number Theory* VII §2).

Proved from the literature axiom `exists_isSelfDual` (`Literature/Fourier`; standard harmonic
analysis on a `p`-adic vector space, not in Mathlib) and the nondegeneracy of `b` on `𝔤`
(`restrictForm_lie_nondegenerate`). Without a self-dual measure `selfDualHaar = 0`, `ĵ(0,·)`
would not be determined by `IsJHat`, and the germ at the zero orbit would not be pinned down. -/
theorem exists_isSelfDual_toyLie (ψ : NontrivialAddChar F) :
    ∃ μ, IsSelfDual μ (restrictForm (𝕋).lie (𝕋).bilin) ψ := by
  haveI := t2Space_of_moduleTopology F (𝕋).ambient
  exact exists_isSelfDual_of_isInducing (𝕋).lie.incl.toLinearMap IsInducing.subtypeVal
    Subtype.val_injective _ (restrictForm_lie_nondegenerate _) ψ

/-- Every element of a subalgebra of the toy Lie algebra is regular semisimple in it. -/
theorem toyD_isRegularSS (L : LieSubalgebra F (𝕋).ambient) (hL : L ≤ (𝕋).lie) (X : ↥L) :
    IsRegularSS L (X : (𝕋).ambient) := by
  obtain ⟨a, b, h⟩ := toy_lie_scalar (K := F) (hL X.2)
  refine ⟨?_, toy_isLieAbelian _⟩
  rw [h]
  exact isSS_pair_algebraMap a b

/-- The toy Lie algebra has no nonzero nilpotent elements. -/
theorem toyD_eq_zero_of_isNilpotent {X : (𝕋).ambient} (hX : X ∈ (𝕋).lie) (hn : IsNilpotent X) :
    X = 0 := by
  obtain ⟨a, b, rfl⟩ := toy_lie_scalar (K := F) hX
  have ha : IsNilpotent a := (IsNilpotent.map_iff (algebraMap_cliff_injective _)).mp
    (hn.map (RingHom.fst (CliffordAlgebra (𝕋).QW) (CliffordAlgebra (𝕋).QV)))
  have hb : IsNilpotent b := (IsNilpotent.map_iff (algebraMap_cliff_injective _)).mp
    (hn.map (RingHom.snd (CliffordAlgebra (𝕋).QW) (CliffordAlgebra (𝕋).QV)))
  rw [ha.eq_zero, hb.eq_zero, map_zero, map_zero]
  rfl

/-- `Nil(𝔩) = {0}` for every subalgebra `𝔩` of the toy Lie algebra. -/
theorem toyD_nilOrbit_eq_zero (Gx : Subgroup (𝕋).ambientˣ) (L : LieSubalgebra F (𝕋).ambient)
    (hL : L ≤ (𝕋).lie) (O : NilOrbit Gx L) : O = zeroOrbit Gx L := by
  induction O using Quotient.inductionOn with
  | h X =>
    obtain ⟨X, hXL, hn⟩ := X
    obtain rfl : X = 0 := toyD_eq_zero_of_isNilpotent (hL hXL) hn
    rfl

/-- The zero orbit is regular (`𝔩` is abelian, so `rank 𝔩 = dim 𝔩 = dim 𝔩_0`). -/
theorem toyD_mem_nilReg (Gx : Subgroup (𝕋).ambientˣ) (L : LieSubalgebra F (𝕋).ambient)
    (O : NilOrbit Gx L) : O ∈ NilReg Gx L := by
  refine ⟨(Quotient.out O).2.1, (Quotient.out O).2.2, ?_⟩
  have hc : ∀ X : ↥L, finrank F ↥(lieCentralizer L (X : (𝕋).ambient)) = finrank F ↥L :=
    fun X => by rw [toy_lieCentralizer_eq]
  rw [toy_lieCentralizer_eq]
  unfold lieRank
  simp only [hc, ciInf_const]

/-- **The germ of a locally constant `θ` on the toy group** (Thesis §4.2): at every `x` the only
nilpotent orbit of `𝔤_x = 𝔤` is `0`, it is regular, `ĵ(0,·) = 1`, so `θ(x e^X) = θ(x)` is the local
expansion and the germ is `θ(x)`.  Uses the self-dual measure (`exists_isSelfDual_toyLie`). -/
theorem toyD_germ (ψ : NontrivialAddChar F) {θ : ↥(𝕋).G → ℂ} (hθ : IsLocallyConstant θ)
    (x : ↥(𝕋).G)
    (O : NilOrbit (grpCentralizer (𝕋).G (x : (𝕋).ambientˣ))
      (lieCentralizer (𝕋).lie ((x : (𝕋).ambientˣ) : (𝕋).ambient))) :
    germ (𝕋).G (𝕋).lie (𝕋).bilin ψ θ x O = θ x := by
  have hL : (lieCentralizer (𝕋).lie ((x : (𝕋).ambientˣ) : (𝕋).ambient)) ≤ (𝕋).lie := inf_le_left
  haveI : Subsingleton (NilOrbit (grpCentralizer (𝕋).G (x : (𝕋).ambientˣ)) (lieCentralizer (𝕋).lie ((x : (𝕋).ambientˣ) : (𝕋).ambient))) :=
    ⟨fun a b => (toyD_nilOrbit_eq_zero _ _ hL a).trans (toyD_nilOrbit_eq_zero _ _ hL b).symm⟩
  have hsd : ∃ μ, IsSelfDual μ (restrictForm (lieCentralizer (𝕋).lie ((x : (𝕋).ambientˣ) : (𝕋).ambient)) (𝕋).bilin) ψ := by
    rw [toy_lieCentralizer_eq]
    exact exists_isSelfDual_toyLie ψ
  have hsum : ∀ (c : NilOrbit (grpCentralizer (𝕋).G (x : (𝕋).ambientˣ)) (lieCentralizer (𝕋).lie ((x : (𝕋).ambientˣ) : (𝕋).ambient)) → ℂ) (X : (𝕋).ambient), X ∈ (lieCentralizer (𝕋).lie ((x : (𝕋).ambientˣ) : (𝕋).ambient)) →
      ∑ᶠ O', c O' * jHat (grpCentralizer (𝕋).G (x : (𝕋).ambientˣ)) (lieCentralizer (𝕋).lie ((x : (𝕋).ambientˣ) : (𝕋).ambient)) (𝕋).bilin ψ O' X = c (zeroOrbit _ _) := by
    intro c X hX
    rw [finsum_eq_single _ (zeroOrbit _ _) (fun O' hO' => (hO' (Subsingleton.elim _ _)).elim),
      jHat_zeroOrbit_eq_one _ _ _ ψ hsd (toyD_isRegularSS _ hL) hX, mul_one]
  -- every local expansion has coefficient `θ(x)` (evaluate at `X = 0`)
  have huniq : ∀ c, HasGermExpansion (𝕋).G (𝕋).lie (𝕋).bilin ψ θ x c → c O = θ x := by
    rintro c ⟨-, ω, hω, hexp⟩
    have h0 := hexp 0 (mem_of_mem_nhds hω) (zero_mem _) (toyD_isRegularSS _ hL 0) x
      (by rw [expA_zero, mul_one])
    rw [hsum c 0 (zero_mem _), ← Subsingleton.elim O (zeroOrbit _ _)] at h0
    exact h0.symm
  -- `θ(x e^X) = θ(x)` is a local expansion
  obtain ⟨ω, hω, hloc⟩ :=
    exists_nhds_zero_mul_expA (F := F) ((IsLocallyConstant.iff_eventually_eq _).mp hθ x)
  have hex : HasGermExpansion (𝕋).G (𝕋).lie (𝕋).bilin ψ θ x (fun _ => θ x) := by
    refine ⟨Set.toFinite _, ω, hω, fun X hXω hXL _ y hy => ?_⟩
    rw [hsum _ X hXL]
    exact hloc X hXω y hy
  have hE : ∃ c, HasGermExpansion (𝕋).G (𝕋).lie (𝕋).bilin ψ θ x c := ⟨_, hex⟩
  unfold germ
  rw [ite_eq_left_of_eq_true _ _ (eq_true (toyD_mem_nilReg _ _ O)),
    dite_eq_left_of_eq_true (eq_true hE)]
  exact huniq _ hE.choose_spec


/-- **`m_geom(θ) = θ(1)` for the toy datum** (Thesis §7.2, Prop 12.1.1), for `θ` locally constant
and constant on `diag(GSpin(W)) = A_{G,H}`: `Γ(G,H)` is the single torus `GSpin(W) = F^×` with
`T/A_{G,H} = 1` (probability measure = point mass), `|W(T)| = 1`, `D^G = Δ = 1`, and the germ at
the (zero) regular orbit is `θ(t)`.  So `m_{geom,s}(θ) = θ(1)` for every `s`. -/
theorem toyD_mGeom (ψ : NontrivialAddChar F) {θ : ↥(𝕋).G → ℂ} (hθ : IsLocallyConstant θ)
    (hθ1 : ∀ t : GSpin (𝕋).QW, θ ((𝕋).diag t) = θ 1) : mGeom ψ (𝕋) θ = θ 1 := by
  have hS : ∀ s, mGeomS ψ (𝕋) θ s = θ 1 := by
    intro s
    unfold mGeomS
    have hsingle := tsum_eq_single (L := SummationFilter.unconditional (GammaClass (𝕋)))
      (f := fun c : GammaClass (𝕋) =>
      ((weylCard (𝕋) c : ℂ))⁻¹ * torusIntegral ψ (𝕋) θ (Quot.out c).1 s)
      (toyD_gammaClass (F := F)) fun c hc => (hc (Subsingleton.elim _ _)).elim
    rw [hsingle, show weylCard (𝕋) (toyD_gammaClass (F := F)) = 1 from toyD_weylCardOf _, Nat.cast_one,
      inv_one, one_mul]
    unfold torusIntegral
    have hT : (Quot.out (toyD_gammaClass (F := F))).1 = ⊤ := toyD_gammaTorus_val _
    letI : MeasurableSpace ((𝕋).TorusQuot (Quot.out (toyD_gammaClass (F := F))).1) := borel _
    haveI : BorelSpace ((𝕋).TorusQuot (Quot.out (toyD_gammaClass (F := F))).1) := ⟨rfl⟩
    rw [integral_of_subsingleton _ _ 1, probHaar_real_univ, one_smul]
    unfold gammaIntegrand
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨toyD_isGammaElt _, by rw [toyD_torusOf, hT]⟩),
      toyD_weylDisc, toyD_germ ψ hθ, toyD_deltaGGP, hθ1, Real.sqrt_one, Real.one_rpow]
    simp
  unfold mGeom
  rw [show mGeomS ψ (𝕋) θ = fun _ => θ 1 from funext hS]
  exact tendsto_const_nhds.limUnder_eq

/-- `f(t) = f(1)` on `diag(GSpin(W)) = A_{G,H}` for `χ⁻¹`-equivariant `f`. -/
theorem toyD_apply_diag {f : ↥(𝕋).G → ℂ} (hf : IsChiEquivariant (𝕋) χ f) (t : GSpin (𝕋).QW) :
    f ((𝕋).diag t) = f 1 := by
  obtain ⟨c, hc⟩ := toy_gspinW_mem_range (K := F) t
  exact toy_apply_of_mem_AGH χ hf ⟨c, by rw [← hc]; rfl⟩

/-- **The geometric expansion holds for the toy datum** (Thesis Thm 12.2.1 at `m = r = 0`): `J(f) = f(1) = m_geom(θ_f)` for every `f ∈ 𝒞_scusp`, every `χ`.
This checks that `J`, `θ_f` and `m_geom` are normalized consistently *at the zero orbit*:
`dx` on the point `H\G/A_G` and `dg` on `G/A_G` both have mass `1`, the probability measure on
`T/A_{G,H}` is the point mass, and `ĵ(0,·) = 1`.  It does not test nonzero orbits.
Uses the literature axiom `exists_isSelfDual` (via `exists_isSelfDual_toyLie`). -/
theorem toyD_geomAt (ψ : NontrivialAddChar F) : GeomAt ψ (𝕋) χ := by
  intro f hf
  rw [toyD_distribJ χ ψ hf.2.1, toyD_thetaF_eq hf.1.continuous]
  exact (toyD_mGeom ψ hf.1 (toyD_apply_diag χ hf.2.1)).symm


/-- **The geometric expansion for the toy datum** (`GeomAt` for `toyData` itself; see
`toyD_geomAt`). -/
theorem toy_geomAt (ψ : NontrivialAddChar F) (χ' : CentralCharOn (toyData (K := F))) :
    GeomAt ψ toyData χ' :=
  toyD_geomAt χ' ψ

/-- `dim G ≥ 2` for every GGP datum (`dim GSpin(U) ≥ 1`). -/
theorem two_le_dimG (d : GGPData F) : 2 ≤ d.dimG := by
  unfold GGPData.dimG GGPData.dimGSpin
  omega

theorem toyD_dimG : (𝕋).dimG = 2 := by
  simp [toyD, toyData, GGPData.dimG, GGPData.dimGSpin]

/-- The toy datum has the smallest possible `dim G = 2`, so (HYP) is vacuous for it. -/
theorem toyD_hyp (ψ : NontrivialAddChar F) : HYP ψ (𝕋) := fun d' hd' =>
  absurd hd' (not_lt.mpr (by rw [toyD_dimG]; exact two_le_dimG d'))

/-- **The multiplicity formula for the toy datum, from the spine** (`multAt_of_hyp_geom`, with
`toy_hyp` and `toy_geomAt`).  Not a direct computation: it goes through the spine `sorry`s
`prop_11_5_1_ii_ell` and `exists_scusp_ell` (and the axioms `schur_central`,
`emoryTakeda_mult_le_one`), so it checks only that the spine closes at the bottom of the
induction, where (HYP) is empty. -/
theorem toyD_multAt (ψ : NontrivialAddChar F) : MultAt ψ (𝕋) :=
  multAt_of_hyp_geom ψ (𝕋) (toyD_hyp ψ) (fun χ' => toyD_geomAt χ' ψ)

/-- `toyD_multAt` for `toyData` itself. -/
theorem toy_multAt (ψ : NontrivialAddChar F) : MultAt ψ (toyData (K := F)) :=
  toyD_multAt ψ

/-- A representation with central character `η` on `A_G` is trivial on `A_{G,H}` (`η` is). -/
theorem isTrivialOn_AGH_of_hasCentralChar {d : GGPData F} {η : CentralCharOn d}
    {π : UnitaryRep ↥d.G} (h : HasCentralChar π d.AG (fun a => ((η.toHom a : Circle) : ℂ))) :
    IsTrivialOn π (d.AGH : Set ↥d.G) := by
  intro s hs
  have h2 : η.toHom ⟨s, d.AGH_le_AG hs⟩ = 1 := η.trivial_AGH s hs
  calc π.ρ s = ((η.toHom ⟨s, d.AGH_le_AG hs⟩ : Circle) : ℂ) • 1 := h ⟨s, d.AGH_le_AG hs⟩
    _ = 1 := by simp only [h2, Circle.coe_one, one_smul]

/-- **The defect vanishes on all virtual tempered representations of the toy datum**
(`defect = m − m_geom`, Thesis §7.4), from `toy_multAt` (so with the same dependencies). -/
theorem toy_defect_zero (ψ : NontrivialAddChar F) (η : CentralCharOn (toyData (K := F)))
    (P : VirtualTemp toyData η) : defect ψ toyData P = 0 := by
  induction P using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add P Q hP hQ => rw [map_add, hP, hQ, add_zero]
  | single c a =>
    rw [defect_single, ((toy_multAt ψ) c.rep c.isTempCC_rep.1
      (isTrivialOn_AGH_of_hasCentralChar c.isTempCC_rep.2)).2, sub_self,
      mul_zero]

/-! #### The four statements, stated for `toyData` itself (defeq to the `toyD` versions) -/

/-- **`G_ell = G` for the toy datum** (Thesis §2.5). -/
theorem toy_ellRegSet : (toyData (K := F)).ellRegSet = Set.univ := toyD_ellRegSet

/-- **`J(f) = f(1)` for the toy datum** (Thesis §7.1, §10.1). -/
theorem toy_distribJ (ψ : NontrivialAddChar F) (χ' : CentralCharOn (toyData (K := F)))
    {f : ↥(toyData (K := F)).G → ℂ} (hf : IsChiEquivariant toyData χ' f) :
    distribJ toyData ψ f = f 1 :=
  toyD_distribJ χ' ψ hf

/-- **`θ_f = c · f`, `c = haar(G/A_G) = 1`, for the toy datum** (Thesis §4.8). -/
theorem toy_thetaF (χ' : CentralCharOn (toyData (K := F))) {f : ↥(toyData (K := F)).G → ℂ}
    (hf : f ∈ ScuspTestFn toyData χ') :
    thetaF toyData f =
      (((Measure.haar : Measure (toyD (F := F)).GmodAG).real Set.univ : ℝ) : ℂ) • f :=
  toyD_thetaF χ' hf

end ToyPAdic

end CoreToy

end Sanity

end GSpinGGP
