/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Local fields and unbundled linear groups

Generic `p`-adic foundations for the formalization of the dissertation
*The Local Gan–Gross–Prasad Conjecture for General Spin Groups* (henceforth "Thesis").

Everything here is **unbundled**: a "reductive group" is a plain `G : Subgroup Aˣ` and its
Lie algebra a plain `𝔤 : LieSubalgebra F A` inside an ambient finite-dimensional `F`-algebra `A`
carrying the module topology. Other files apply these notions directly to Mathlib objects
(e.g. `GSpin Q ⊆ (CliffordAlgebra Q)ˣ`).

Contents.
* `PAdicField`, `absF`, `NontrivialAddChar` (Thesis §2.1, §2.4).
* Topology plumbing for the ambient algebra (as *theorems*, see the note below).
* `conjAd`, `IsSS`, `lieCentralizer`, `grpCentralizer`, `IsRegularSS`, `regularSet`,
  `regularSetLie`, `weylDisc`, `weylDiscLie` (Thesis §2.1).
* `ellipticRegularSet` (Thesis §2.5).
* `totallyDisconnectedSpace_subgroup`: `G(F)` is totally disconnected.
* `expA` (the exponential series); `exists_nhds_isRegularSS_mul_expA` (`x e^X` is regular for
  `X ∈ 𝔤_x` small and regular, Harish-Chandra).
* `logNorm` `σ`, with `logNorm_mul_le`, `logNorm_inv`, `one_le_logNorm` (BP §1.2).
* `NilOrbit`, `lieRank`, `IsRegularNil`, `NilReg` (Thesis §4.2, §4.4; BP §1.6).
* `selfDual` measures, `selfDualHaar`, `fourierLie`, `orbitMeasure`, `jHat` (Thesis §2.4,
  BP Astérisque 418 §1.6, §1.8, §4.1).
* `IsQuasiCharacter`, `germ`, `germAvg` (Thesis §4.1.1, §4.2; BP §4.1, §4.5).

**Instance note.** `IsTopologicalRing A`, `T2Space A`, `LocallyCompactSpace A` cannot be global
instances: their conclusions do not mention `F`, so instance search could not find `F`.
They are the theorems `isTopologicalRing_of_moduleTopology F A`, `t2Space_of_moduleTopology F A`,
`locallyCompactSpace_of_moduleTopology F A` (plus `units_t2Space`, `units_locallyCompactSpace`,
`subgroup_t2Space`, `subgroup_locallyCompactSpace_of_isClosed`); use them via `haveI`.
-/

open MeasureTheory Topology Filter
open scoped NNReal ENNReal Pointwise Classical

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GSpinGGP

/-! ## 1. The field -/

/-- A *`p`-adic field*: a finite extension of `ℚ_p` (Thesis §2.1). We use the analytic
characterization: a nontrivially normed field that is complete, locally compact, ultrametric and of
characteristic zero. (Any such field is a finite extension of some `ℚ_p`.) -/
class PAdicField (F : Type*) [NontriviallyNormedField F] : Prop
    extends CompleteSpace F, LocallyCompactSpace F, IsUltrametricDist F, CharZero F

/-- `ℚ_p` is a `p`-adic field. -/
instance (p : ℕ) [Fact p.Prime] : PAdicField ℚ_[p] where

variable {F : Type*} [NontriviallyNormedField F]

/-- The normalized absolute value `|a|_F` of Thesis §2.1: the unique positive real such that
`d(ax) = |a| dx` for any Haar measure `dx` on `F`, i.e. the distributive Haar character of `Fˣ`
acting on `F` (Mathlib's `MeasureTheory.distribHaarChar`), extended by `|0| = 0`. -/
def absF [LocallyCompactSpace F] (a : F) : ℝ :=
  if h : a = 0 then 0 else (distribHaarChar F (Units.mk0 a h) : ℝ)

@[simp] lemma absF_zero [LocallyCompactSpace F] : absF (0 : F) = 0 := by unfold absF; simp

lemma absF_of_ne_zero [LocallyCompactSpace F] {a : F} (h : a ≠ 0) :
    absF a = (distribHaarChar F (Units.mk0 a h) : ℝ) := by unfold absF; simp [h]

lemma absF_pos [LocallyCompactSpace F] {a : F} (h : a ≠ 0) : 0 < absF a := by
  rw [absF_of_ne_zero h]; exact_mod_cast distribHaarChar_pos

lemma absF_nonneg [LocallyCompactSpace F] (a : F) : 0 ≤ absF a := by
  by_cases h : a = 0
  · simp [h]
  · exact (absF_pos h).le

/-- The normalized absolute value is multiplicative (Thesis §2.1). -/
lemma absF_mul [LocallyCompactSpace F] (a b : F) : absF (a * b) = absF a * absF b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  rw [absF_of_ne_zero hab, absF_of_ne_zero ha, absF_of_ne_zero hb]
  have : Units.mk0 (a * b) hab = Units.mk0 a ha * Units.mk0 b hb := by ext; simp
  rw [this, map_mul]; push_cast; ring

/-- `d(ax) = |a| dx` for every additive Haar measure on `F` (Thesis §2.1). -/
lemma absF_haar [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] {a : F} (ha : a ≠ 0) (s : Set F) :
    μ (a • s) = ENNReal.ofReal (absF a) * μ s := by
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  rw [absF_of_ne_zero ha, ENNReal.ofReal_coe_nnreal, distribHaarChar_mul]
  rfl

/-- A continuous nontrivial additive character `ψ : F → 𝕊¹` (Thesis §2.4). -/
structure NontrivialAddChar (F : Type*) [NontriviallyNormedField F] where
  /-- the underlying additive character -/
  toAddChar : AddChar F Circle
  continuous : Continuous toAddChar
  ne_one : toAddChar ≠ 1

namespace NontrivialAddChar

/-- `ψ` as a complex-valued function. -/
def toFun (ψ : NontrivialAddChar F) (t : F) : ℂ := ((ψ.toAddChar t : Circle) : ℂ)

instance : CoeFun (NontrivialAddChar F) (fun _ ↦ F → ℂ) := ⟨toFun⟩

end NontrivialAddChar

/-! ## 2. Topology of the ambient algebra -/

section Topology

variable (F) [PAdicField F]
variable (A : Type*) [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A]
  [IsModuleTopology F A]

include F

/-- The ambient algebra is a topological ring (Mathlib `IsModuleTopology.isTopologicalRing`). -/
theorem isTopologicalRing_of_moduleTopology : IsTopologicalRing A :=
  IsModuleTopology.isTopologicalRing F A

/-- The canonical continuous linear equivalence `A ≃L[F] (Fin n → F)` coming from
`Module.finBasis`. -/
def toPiCLE : A ≃L[F] (Fin (Module.finrank F A) → F) :=
  haveI := isTopologicalRing_of_moduleTopology F A
  { (Module.finBasis F A).equivFun with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap
      (Module.finBasis F A).equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap
      (Module.finBasis F A).equivFun.symm.toLinearMap }

/-- The ambient algebra is Hausdorff. -/
theorem t2Space_of_moduleTopology : T2Space A :=
  (toPiCLE F A).toHomeomorph.symm.t2Space

/-- The ambient algebra is locally compact. -/
theorem locallyCompactSpace_of_moduleTopology : LocallyCompactSpace A :=
  haveI : LocallyCompactSpace (Fin (Module.finrank F A) → F) := Pi.locallyCompactSpace_of_finite
  (toPiCLE F A).toHomeomorph.isClosedEmbedding.locallyCompactSpace

/-- `Aˣ` is Hausdorff. -/
theorem units_t2Space : T2Space Aˣ := by
  haveI := t2Space_of_moduleTopology F A
  haveI := isTopologicalRing_of_moduleTopology F A
  exact Units.isEmbedding_embedProduct.t2Space

/-- `Aˣ` is locally compact. -/
theorem units_locallyCompactSpace : LocallyCompactSpace Aˣ := by
  haveI := t2Space_of_moduleTopology F A
  haveI := isTopologicalRing_of_moduleTopology F A
  haveI := locallyCompactSpace_of_moduleTopology F A
  infer_instance

/-- Every subgroup of `Aˣ` is a topological group. -/
theorem subgroup_isTopologicalGroup (G : Subgroup Aˣ) : IsTopologicalGroup ↥G := by
  haveI := isTopologicalRing_of_moduleTopology F A
  infer_instance

/-- Every subgroup of `Aˣ` is Hausdorff. -/
theorem subgroup_t2Space (G : Subgroup Aˣ) : T2Space ↥G := by
  haveI := units_t2Space F A
  infer_instance

/-- A closed subgroup of `Aˣ` is locally compact (e.g. the `F`-points of an algebraic group). -/
theorem subgroup_locallyCompactSpace_of_isClosed (G : Subgroup Aˣ) (hG : IsClosed (G : Set Aˣ)) :
    LocallyCompactSpace ↥G := by
  haveI := units_locallyCompactSpace F A
  exact hG.locallyCompactSpace

/-- The ambient algebra is totally disconnected (`F` is ultrametric, `A ≃ F^n`). -/
theorem totallyDisconnectedSpace_of_moduleTopology : TotallyDisconnectedSpace A :=
  (toPiCLE F A).toHomeomorph.symm.totallyDisconnectedSpace

/-- `Aˣ` is totally disconnected (it embeds in `A × Aᵐᵒᵖ`). -/
theorem units_totallyDisconnectedSpace : TotallyDisconnectedSpace Aˣ := by
  haveI := totallyDisconnectedSpace_of_moduleTopology F A
  haveI := isTopologicalRing_of_moduleTopology F A
  haveI : TotallyDisconnectedSpace Aᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := A)).totallyDisconnectedSpace
  exact (Units.isEmbedding_embedProduct (M := A)).isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- For `p`-adic `F`, every group of points `G(F) ⊆ Aˣ` is totally disconnected (Thesis §2.1: `G(F)`
is a totally disconnected locally compact group, an `ℓ`-group). Combined with
`subgroup_locallyCompactSpace_of_isClosed` and `subgroup_t2Space`, compact open subsets form a
basis of the topology, which is what the separation of distributions by test functions uses. -/
theorem totallyDisconnectedSpace_subgroup (G : Subgroup Aˣ) : TotallyDisconnectedSpace ↥G := by
  haveI := units_totallyDisconnectedSpace F A
  infer_instance

end Topology

/-- Elements of a group of points coerce directly to the ambient algebra, so that e.g.
`lieCentralizer 𝔤 x` typechecks for `x : ↥G`. -/
instance subgroupCoeAmbient {A : Type*} [Monoid A] (G : Subgroup Aˣ) : CoeOut ↥G A :=
  ⟨fun g ↦ ((g : Aˣ) : A)⟩

/-- Groups of points carry their Borel σ-algebra. -/
instance subgroupMeasurableSpace {A : Type*} [Monoid A] [TopologicalSpace A] (G : Subgroup Aˣ) :
    MeasurableSpace ↥G := borel ↥G

instance subgroupBorelSpace {A : Type*} [Monoid A] [TopologicalSpace A] (G : Subgroup Aˣ) :
    BorelSpace ↥G := ⟨rfl⟩

/-- Lie algebras carry their Borel σ-algebra. -/
instance lieSubalgebraMeasurableSpace {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    [TopologicalSpace A] (𝔤 : LieSubalgebra R A) : MeasurableSpace ↥𝔤 := borel ↥𝔤

instance lieSubalgebraBorelSpace {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    [TopologicalSpace A] (𝔤 : LieSubalgebra R A) : BorelSpace ↥𝔤 := ⟨rfl⟩


/-! ## 3. Algebraic notions (Thesis §2.1) -/

section Algebraic

variable (F) {A : Type*} [Ring A] [Algebra F A]

/-- Conjugation `Ad g : a ↦ g a g⁻¹` on the ambient algebra (Thesis §2.1, `Ad`). -/
def conjAd (g : Aˣ) : A ≃ₐ[F] A where
  toFun a := (g : A) * a * (↑g⁻¹ : A)
  invFun a := (↑g⁻¹ : A) * a * (g : A)
  left_inv a := by simp [mul_assoc]
  right_inv a := by simp [mul_assoc]
  map_mul' a b := by simp [mul_assoc]
  map_add' a b := by simp [mul_add, add_mul]
  commutes' r := by simp [← Algebra.commutes r (g : A), mul_assoc]

@[simp] lemma conjAd_apply (g : Aˣ) (a : A) : conjAd F g a = (g : A) * a * (↑g⁻¹ : A) := rfl

/-- `x` is semisimple: left multiplication by `x` on `A` is a semisimple endomorphism
(minimal polynomial squarefree; over a field of characteristic `0` this is diagonalizability over
`F̄`). For `A` containing a faithful representation this is the usual notion for both group and
Lie algebra elements (Thesis §2.1, `G_ss`, `𝔤_ss`). -/
def IsSS (x : A) : Prop := Module.End.IsSemisimple (LinearMap.mulLeft F x)

variable {F}

/-- The centralizer `𝔤_x = {X ∈ 𝔤 | xX = Xx}`. For a unit `x` this is the Lie algebra
`Lie(G_x)` of the centralizer (fixed points of `Ad x`); for `x = X ∈ 𝔤` it is `Z_𝔤(X)`
(Thesis §2.1). -/
def lieCentralizer (𝔤 : LieSubalgebra F A) (x : A) : LieSubalgebra F A :=
  𝔤 ⊓ lieSubalgebraOfSubalgebra F A (Subalgebra.centralizer F {x})

lemma mem_lieCentralizer {𝔤 : LieSubalgebra F A} {x X : A} :
    X ∈ lieCentralizer 𝔤 x ↔ X ∈ 𝔤 ∧ x * X = X * x := by
  change X ∈ 𝔤 ∧ X ∈ Subalgebra.centralizer F {x} ↔ _
  simp [Subalgebra.mem_centralizer_iff, eq_comm]

/-- The centralizer `G_x = Z_G(x)` of `x` in `G` (Thesis §2.1). -/
def grpCentralizer (G : Subgroup Aˣ) (x : Aˣ) : Subgroup Aˣ :=
  G ⊓ Subgroup.centralizer {x}

/-- `x` is regular semisimple for `𝔤`: semisimple, and `𝔤_x` is abelian. In characteristic `0`
with connected reductive centralizers (true for `GSpin`, Steinberg), `G_x^0` is then a maximal
torus (Thesis §2.1, `G_reg`, `𝔤_reg`). -/
def IsRegularSS (𝔤 : LieSubalgebra F A) (x : A) : Prop :=
  IsSS F x ∧ IsLieAbelian ↥(lieCentralizer 𝔤 x)

/-- The regular semisimple set `G_reg(F)` (Thesis §2.1). -/
def regularSet (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A) : Set ↥G :=
  {g | IsRegularSS 𝔤 ((g : Aˣ) : A)}

/-- The regular semisimple set `𝔤_reg(F)` of the Lie algebra (Thesis §2.1). -/
def regularSetLie (𝔤 : LieSubalgebra F A) : Set A :=
  {X | X ∈ 𝔤 ∧ IsRegularSS 𝔤 X}

variable [PAdicField F] [Module.Finite F A]

/-- The Weyl discriminant `D^G(x) = |det(1 - Ad x)|_{𝔤/𝔤_x}|_F` (Thesis §2.1), computed as the
absolute value of the trailing coefficient of the characteristic polynomial of `1 - Ad x` on `𝔤`.
This agrees with the thesis for semisimple `x` (then `1 - Ad x` is semisimple, so its kernel
`𝔤_x` equals its generalized kernel); `0` if `𝔤` is not `Ad x`-stable. -/
def weylDisc (𝔤 : LieSubalgebra F A) (x : Aˣ) : ℝ :=
  if h : ∀ X ∈ 𝔤.toSubmodule, conjAd F x X ∈ 𝔤.toSubmodule then
    absF (LinearMap.charpoly
      (1 - (conjAd F x).toLinearEquiv.toLinearMap.restrict h)).trailingCoeff
  else 0

/-- The Lie algebra Weyl discriminant `D^G(X) = |det(ad X)|_{𝔤/𝔤_X}|_F` (Thesis §2.1), via the
trailing coefficient of the characteristic polynomial of `ad X` on `𝔤`; `0` if `X ∉ 𝔤`. -/
def weylDiscLie (𝔤 : LieSubalgebra F A) (X : A) : ℝ :=
  if h : ∀ Y ∈ 𝔤.toSubmodule, (LinearMap.mulLeft F X - LinearMap.mulRight F X) Y ∈ 𝔤.toSubmodule
  then absF (LinearMap.charpoly
      ((LinearMap.mulLeft F X - LinearMap.mulRight F X).restrict h)).trailingCoeff
  else 0

end Algebraic

/-! ### The elliptic regular set (Thesis §2.5) -/

section Elliptic

variable {A : Type*} [Ring A] [Algebra F A] [TopologicalSpace A]

/-- The elliptic regular set `G(F)_ell ∩ G_reg(F)` (Thesis §2.5, `Γ_ell(G) ∩ Γ_reg(G)`; the thesis
uses "elliptic" without defining it, following BP §1.7, number unverified): the regular
semisimple `x` whose centralizer is compact modulo the split centre `A_G(F)`, given here as the
subgroup `Az ⊆ G(F)` (for the GGP group, `ellRegSet d := ellipticRegularSet d.G d.lie d.AG`).
For regular `x` the centralizer `G_x(F)` contains the maximal torus `T(F) = G_x^0(F)` with finite
index (and equals it for `GSpin`, whose derived group is simply connected, Steinberg), so
compactness of `G_x(F)/A_G(F)` is the same as `T/A_G` being anisotropic, i.e. `T` elliptic.
The quotient `G(F)/Az` is the left coset space with the quotient topology (`Az` need not be
normal for the definition). -/
def ellipticRegularSet (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A) (Az : Subgroup ↥G) : Set ↥G :=
  {x | x ∈ regularSet G 𝔤 ∧
    IsCompact ((QuotientGroup.mk (s := Az) '' (Subgroup.centralizer ({x} : Set ↥G) : Set ↥G)) :
      Set (↥G ⧸ Az))}

lemma mem_ellipticRegularSet {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A} {Az : Subgroup ↥G}
    {x : ↥G} : x ∈ ellipticRegularSet G 𝔤 Az ↔ x ∈ regularSet G 𝔤 ∧
      IsCompact ((QuotientGroup.mk (s := Az) '' (Subgroup.centralizer ({x} : Set ↥G) : Set ↥G)) :
        Set (↥G ⧸ Az)) := Iff.rfl

/-- Elliptic regular elements are regular semisimple. -/
lemma ellipticRegularSet_subset_regularSet (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A)
    (Az : Subgroup ↥G) : ellipticRegularSet G 𝔤 Az ⊆ regularSet G 𝔤 := fun _ hx => hx.1

end Elliptic

/-! ## 4. The exponential -/

section PAdicBound

variable (F) [PAdicField F]

/-- The restriction of the norm of `F` to `ℚ ⊆ F`, as an absolute value on `ℚ`. -/
def ratAbsF : AbsoluteValue ℚ ℝ where
  toFun q := ‖(q : F)‖
  map_mul' a b := by simp
  nonneg' _ := norm_nonneg _
  eq_zero' a := by simp
  add_le' a b := by simpa using norm_add_le (a : F) b

/-- The norm of `F` is nontrivial on `ℚ`: otherwise `ℤ ⊆ F` would be an infinite `1`-separated
subset of the compact unit ball. -/
lemma ratAbsF_isNontrivial : (ratAbsF F).IsNontrivial := by
  by_contra h
  simp only [AbsoluteValue.IsNontrivial, not_exists, not_and, not_not] at h
  have hint : ∀ k : ℤ, k ≠ 0 → ‖(k : F)‖ = 1 := fun k hk => by
    have := h k (by exact_mod_cast hk)
    simpa [ratAbsF] using this
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have hmem : ∀ n : ℕ, ((n : ℤ) : F) ∈ Metric.closedBall (0 : F) 1 := by
    intro n
    rcases eq_or_ne (n : ℤ) 0 with h0 | h0
    · simp [h0]
    · exact mem_closedBall_zero_iff.mpr (hint _ h0).le
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : F) 1).tendsto_subseq hmem
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hlim.cauchySeq (1 / 2) (by norm_num)
  have h1 := hN (N + 1) (by omega)
  have hne : ((φ (N + 1) : ℤ) - (φ N : ℤ)) ≠ 0 := by
    have := hφ (Nat.lt_add_one N); omega
  simp only [Function.comp, dist_eq_norm, ← Int.cast_sub, hint _ hne] at h1
  norm_num at h1

/-- `p`-adic content of the exponential: `|1/n!|_F ≤ R^n`. By Ostrowski (Mathlib
`Rat.AbsoluteValue.equiv_padic_of_bounded`) `‖·‖_F` restricted to `ℚ` is a power of `|·|_p`, and
`v_p(n!) ≤ n`. -/
lemma exists_norm_factorial_inv_le :
    ∃ R : ℝ, 0 < R ∧ ∀ n : ℕ, ‖((n.factorial : F))⁻¹‖ ≤ R ^ n := by
  have bdd : ∀ n : ℕ, ratAbsF F n ≤ 1 := fun n => by
    simpa [ratAbsF] using (isUltrametricDist_iff_forall_norm_natCast_le_one.mp inferInstance n)
  obtain ⟨p, ⟨hp, hequiv⟩, -⟩ :=
    Rat.AbsoluteValue.equiv_padic_of_bounded (ratAbsF_isNontrivial F) bdd
  obtain ⟨c, hc, hcn⟩ := Rat.AbsoluteValue.exists_nat_rpow_iff_isEquiv.mpr hequiv
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  set r : ℝ := ((p : ℝ)⁻¹) ^ (1 / c) with hr
  have hr0 : 0 < r := by positivity
  refine ⟨r⁻¹, inv_pos.mpr hr0, fun n => ?_⟩
  set a : ℝ := ‖(n.factorial : F)‖ with ha
  have ha0 : 0 < a := by simp [ha, Nat.factorial_ne_zero]
  have h1 : a ^ c = (p : ℝ) ^ (-(padicValNat p n.factorial : ℤ)) := by
    have := hcn n.factorial
    simp only [ratAbsF, AbsoluteValue.coe_mk, MulHom.coe_mk, Rat.cast_natCast,
      Rat.AbsoluteValue.padic_eq_padicNorm] at this
    rw [this, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast Nat.factorial_ne_zero n),
      padicValRat.of_nat]
    push_cast; rfl
  have h2 : ((p : ℝ)⁻¹) ^ n ≤ a ^ c := by
    rw [h1, zpow_neg, ← inv_zpow, ← zpow_natCast]
    apply zpow_le_zpow_right_of_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hp1.le)
    exact_mod_cast padicValNat_factorial_le (p := p) n
  have h3 : r ^ n ≤ a := by
    rw [hr, Real.rpow_pow_comm (by positivity)]
    calc (((p : ℝ)⁻¹) ^ n) ^ (1 / c) ≤ (a ^ c) ^ (1 / c) :=
          Real.rpow_le_rpow (by positivity) h2 (by positivity)
      _ = a := by rw [← Real.rpow_mul ha0.le, mul_one_div_cancel hc.ne', Real.rpow_one]
  rw [norm_inv, inv_pow]
  exact inv_anti₀ (by positivity) h3

/-- Over a `p`-adic field the exponential series of any normed `F`-algebra has positive radius. -/
lemma expSeries_radius_pos_of_pAdic (E : Type*) [NormedRing E] [NormedAlgebra F E] :
    0 < (NormedSpace.expSeries F E).radius := by
  obtain ⟨R, hR, hRn⟩ := exists_norm_factorial_inv_le F
  let r : ℝ≥0 := ⟨R⁻¹, (inv_pos.mpr hR).le⟩
  have hle : (r : ℝ≥0∞) ≤ (NormedSpace.expSeries F E).radius := by
    refine FormalMultilinearSeries.le_radius_of_bound _ (max 1 ‖(1 : E)‖) fun n => ?_
    have hm : ‖ContinuousMultilinearMap.mkPiAlgebraFin F n E‖ ≤ max 1 ‖(1 : E)‖ :=
      ContinuousMultilinearMap.norm_mkPiAlgebraFin_le
    simp only [r, NormedSpace.expSeries]
    calc ‖((n.factorial : F)⁻¹) • ContinuousMultilinearMap.mkPiAlgebraFin F n E‖ * R⁻¹ ^ n
        ≤ (R ^ n * max 1 ‖(1 : E)‖) * R⁻¹ ^ n := by
          gcongr
          have := norm_smul_le ((n.factorial : F)⁻¹) (ContinuousMultilinearMap.mkPiAlgebraFin F n E)
          refine le_trans this ?_
          exact mul_le_mul (hRn n) hm (norm_nonneg _) (by positivity)
      _ = max 1 ‖(1 : E)‖ := by
          rw [mul_comm, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hR.ne', one_pow, one_mul]
  exact lt_of_lt_of_le (ENNReal.coe_pos.mpr (show (0 : ℝ) < R⁻¹ from inv_pos.mpr hR)) hle

end PAdicBound

section Exp

variable (F) [PAdicField F] {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A]
  [TopologicalSpace A] [IsModuleTopology F A]

/-- The exponential `e^X = ∑ Xⁿ/n!` in the ambient algebra (Mathlib `NormedSpace.exp`, which only
needs a topological ring). Used in the local expansions `θ(x e^X)` (Thesis §4.1.1, §4.2). -/
def expA (X : A) : A :=
  letI := isTopologicalRing_of_moduleTopology F A
  NormedSpace.exp X

/-! The proofs embed `A` into the Banach algebra `End(F^d)` by left multiplication. -/

local notation "V" => (Fin (Module.finrank F A) → F)

/-- Left multiplication by `a`, transported to a continuous endomorphism of `F^d`. -/
def lmulPi (a : A) : V →L[F] V :=
  LinearMap.toContinuousLinearMap
    ((toPiCLE F A).toLinearEquiv.toLinearMap ∘ₗ LinearMap.mulLeft F a ∘ₗ
      (toPiCLE F A).symm.toLinearEquiv.toLinearMap)

lemma lmulPi_apply (a : A) (v : V) :
    lmulPi F a v = toPiCLE F A (a * (toPiCLE F A).symm v) := rfl

lemma lmulPi_mul (a b : A) : lmulPi F (a * b) = lmulPi F a * lmulPi F b :=
  ContinuousLinearMap.ext fun v => by simp [lmulPi_apply, mul_assoc]

lemma lmulPi_one : lmulPi F (1 : A) = 1 :=
  ContinuousLinearMap.ext fun v => by simp [lmulPi_apply]

lemma lmulPi_pow (a : A) (n : ℕ) : lmulPi F (a ^ n) = lmulPi F a ^ n := by
  induction n with
  | zero => simp [lmulPi_one]
  | succ n ih => rw [pow_succ, lmulPi_mul, ih, pow_succ]

/-- `a ↦ lmulPi a` as a linear map. -/
def lmulPiₗ : A →ₗ[F] (V →L[F] V) where
  toFun := lmulPi F
  map_add' a b := ContinuousLinearMap.ext fun v => by simp [lmulPi_apply, add_mul]
  map_smul' c a := ContinuousLinearMap.ext fun v => by simp [lmulPi_apply]

lemma continuous_lmulPi : Continuous (lmulPi F : A → V →L[F] V) :=
  IsModuleTopology.continuous_of_linearMap (lmulPiₗ F)

lemma lmulPi_leftInv (a : A) : (toPiCLE F A).symm (lmulPi F a (toPiCLE F A 1)) = a := by
  simp [lmulPi_apply]

/-- The continuous left inverse of `lmulPi`. -/
def lmulPiInv : (V →L[F] V) →L[F] A :=
  (toPiCLE F A).symm.toContinuousLinearMap.comp (ContinuousLinearMap.apply F V (toPiCLE F A 1))

lemma lmulPiInv_lmulPi (a : A) : lmulPiInv F (lmulPi F a) = a := lmulPi_leftInv F a

lemma expA_aux :
    letI := isTopologicalRing_of_moduleTopology F A
    ∃ U ∈ 𝓝 (0 : A), (∀ X ∈ U, -X ∈ U) ∧ ∀ X ∈ U,
      lmulPi F X ∈ Metric.eball (0 : V →L[F] V) (NormedSpace.expSeries F (V →L[F] V)).radius ∧
      HasSum (fun n ↦ ((n.factorial : F)⁻¹) • X ^ n) (expA F X) ∧
      lmulPi F (expA F X) = NormedSpace.exp (lmulPi F X) := by
  letI := isTopologicalRing_of_moduleTopology F A
  haveI := t2Space_of_moduleTopology F A
  set B := Metric.eball (0 : V →L[F] V) (NormedSpace.expSeries F (V →L[F] V)).radius
  refine ⟨lmulPi F ⁻¹' B, ?_, ?_, ?_⟩
  · refine (Metric.isOpen_eball.preimage (continuous_lmulPi F)).mem_nhds ?_
    rw [Set.mem_preimage, show lmulPi F (0 : A) = 0 from map_zero (lmulPiₗ F), Metric.mem_eball]
    convert expSeries_radius_pos_of_pAdic F (V →L[F] V)
    exact edist_self (0 : V →L[F] V)
  · intro X hX
    have : lmulPi F (-X) = -lmulPi F X := map_neg (lmulPiₗ F) X
    simpa [B, this] using hX
  · intro X hX
    have hE := NormedSpace.expSeries_hasSum_exp_of_mem_ball' (𝕂 := F) (lmulPi F X) hX
    have hterm : (fun n : ℕ ↦ ((n.factorial : F)⁻¹) • lmulPi F X ^ n) =
        fun n ↦ lmulPi F (((n.factorial : F)⁻¹) • X ^ n) := by
      funext n; rw [← lmulPi_pow]; exact ((lmulPiₗ F).map_smul _ _).symm
    rw [hterm] at hE
    have hA : HasSum (fun n ↦ ((n.factorial : F)⁻¹) • X ^ n)
        (lmulPiInv F (NormedSpace.exp (lmulPi F X))) := by
      simpa [Function.comp_def, lmulPiInv_lmulPi] using hE.map (lmulPiInv F) (lmulPiInv F).continuous
    have hexp : expA F X = lmulPiInv F (NormedSpace.exp (lmulPi F X)) := by
      rw [expA, NormedSpace.exp_eq_tsum F]
      exact hA.tsum_eq
    refine ⟨hX, hexp ▸ hA, ?_⟩
    have h2 := hA.map (lmulPiₗ F) (continuous_lmulPi F)
    rw [hexp]
    exact h2.unique hE

/-- Over a `p`-adic field the exponential series converges on a neighbourhood of `0`
(classically the ball `|X| < p^{-1/(p-1)}`; here `U = lmulPi⁻¹(ball of convergence of expSeries)`,
see `expA_aux`). -/
lemma expA_hasSum :
    letI := isTopologicalRing_of_moduleTopology F A
    ∃ U ∈ 𝓝 (0 : A), ∀ X ∈ U,
      HasSum (fun n : ℕ ↦ ((n.factorial : F)⁻¹) • X ^ n) (expA F X) := by
  obtain ⟨U, hU, -, h⟩ := expA_aux F (A := A)
  exact ⟨U, hU, fun X hX => (h X hX).2.1⟩

/-- Near `0`, `e^X` is a unit with inverse `e^{-X}`. -/
lemma expA_mul_expA_neg : ∃ U ∈ 𝓝 (0 : A), ∀ X ∈ U, expA F X * expA F (-X) = 1 := by
  obtain ⟨U, hU, hneg, h⟩ := expA_aux F (A := A)
  refine ⟨U, hU, fun X hX => ?_⟩
  obtain ⟨hb, -, he⟩ := h X hX
  obtain ⟨hb', -, he'⟩ := h (-X) (hneg X hX)
  have hL : lmulPi F (-X) = -lmulPi F X := map_neg (lmulPiₗ F) X
  rw [hL] at hb' he'
  have key : lmulPi F (expA F X * expA F (-X)) = lmulPi F 1 := by
    have hadd := NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := F) (x := lmulPi F X)
      (y := -lmulPi F X) (by exact (Commute.refl (lmulPi F X)).neg_right) hb hb'
    rw [add_neg_cancel, NormedSpace.exp_zero] at hadd
    rw [lmulPi_mul, he, he', lmulPi_one, hadd]
  calc expA F X * expA F (-X) = lmulPiInv F (lmulPi F (expA F X * expA F (-X))) :=
        (lmulPiInv_lmulPi F _).symm
    _ = 1 := by rw [key, lmulPiInv_lmulPi]

end Exp

/-! ## 4a. The log-norm (Thesis §2.2; BP §1.2) -/

section LogNorm

variable (F) [PAdicField F] {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A]
  [TopologicalSpace A] [IsModuleTopology F A]

/-- `max(1, ‖g‖, ‖g⁻¹‖)`, with `‖a‖` the operator norm of left multiplication by `a` on
`A ≅ F^n` (sup norm), i.e. the norm of `g` in the faithful algebraic representation of `G` on `A`
(BP §1.2, Thesis §2.2). Its log is a log-norm in the sense of Thesis §2.2 (Kottwitz): the matrix
entries of `g` and `g⁻¹` generate the coordinate ring of `G ⊆ GL(A)`. -/
def maxNorm (G : Subgroup Aˣ) (g : ↥G) : ℝ :=
  max 1 (max ‖lmulPi F ((g : Aˣ) : A)‖ ‖lmulPi F (((g⁻¹ : ↥G) : Aˣ) : A)‖)

/-- The log-norm `σ(g) = 1 + log max(1, ‖g‖, ‖g⁻¹‖)` on `G(F)` (BP §1.2; Thesis §2.2, used in the
Harish-Chandra Schwartz space and the estimates of Thesis Ch. 8 and 10). With the
operator norm on `End(F^n)` the norm is submultiplicative, so `σ` is exactly subadditive
(`logNorm_mul_le`), which is stronger than Thesis §2.2's `σ(xy) ≪ σ(x) + σ(y)`. -/
def logNorm (G : Subgroup Aˣ) (g : ↥G) : ℝ := 1 + Real.log (maxNorm F G g)

variable {F}

lemma one_le_maxNorm (G : Subgroup Aˣ) (g : ↥G) : 1 ≤ maxNorm F G g := le_max_left _ _

/-- `σ ≥ 1` (BP §1.2). -/
lemma one_le_logNorm (G : Subgroup Aˣ) (g : ↥G) : 1 ≤ logNorm F G g := by
  unfold logNorm; linarith [Real.log_nonneg (one_le_maxNorm (F := F) G g)]

lemma maxNorm_inv (G : Subgroup Aˣ) (g : ↥G) : maxNorm F G g⁻¹ = maxNorm F G g := by
  unfold maxNorm; rw [inv_inv, max_comm ‖lmulPi F (((g⁻¹ : ↥G) : Aˣ) : A)‖]

/-- `σ(g⁻¹) = σ(g)` (BP §1.2). -/
lemma logNorm_inv (G : Subgroup Aˣ) (g : ↥G) : logNorm F G g⁻¹ = logNorm F G g := by
  simp only [logNorm, maxNorm_inv]

lemma maxNorm_mul_le (G : Subgroup Aˣ) (g h : ↥G) :
    maxNorm F G (g * h) ≤ maxNorm F G g * maxNorm F G h := by
  have hg := one_le_maxNorm (F := F) G g
  have hh := one_le_maxNorm (F := F) G h
  have h1 : ‖lmulPi F ((g : Aˣ) : A)‖ ≤ maxNorm F G g := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : ‖lmulPi F (((g⁻¹ : ↥G) : Aˣ) : A)‖ ≤ maxNorm F G g :=
    (le_max_right _ _).trans (le_max_right _ _)
  have h3 : ‖lmulPi F ((h : Aˣ) : A)‖ ≤ maxNorm F G h := (le_max_left _ _).trans (le_max_right _ _)
  have h4 : ‖lmulPi F (((h⁻¹ : ↥G) : Aˣ) : A)‖ ≤ maxNorm F G h :=
    (le_max_right _ _).trans (le_max_right _ _)
  change max 1 (max ‖lmulPi F (((g * h : ↥G) : Aˣ) : A)‖
    ‖lmulPi F ((((g * h)⁻¹ : ↥G) : Aˣ) : A)‖) ≤ _
  refine max_le (by nlinarith) (max_le ?_ ?_)
  · have : (((g * h : ↥G) : Aˣ) : A) = ((g : Aˣ) : A) * ((h : Aˣ) : A) := by simp
    rw [this, lmulPi_mul]
    refine (norm_mul_le _ _).trans ?_
    exact mul_le_mul h1 h3 (norm_nonneg _) (by linarith)
  · have : ((((g * h)⁻¹ : ↥G) : Aˣ) : A) =
        (((h⁻¹ : ↥G) : Aˣ) : A) * (((g⁻¹ : ↥G) : Aˣ) : A) := by simp
    rw [this, lmulPi_mul, mul_comm (maxNorm F G g)]
    refine (norm_mul_le _ _).trans ?_
    exact mul_le_mul h4 h2 (norm_nonneg _) (by linarith)

/-- Subadditivity `σ(gh) ≤ σ(g) + σ(h)` (Thesis §2.2 has `σ(xy) ≪ σ(x) + σ(y)`; exact here). -/
lemma logNorm_mul_le (G : Subgroup Aˣ) (g h : ↥G) :
    logNorm F G (g * h) ≤ logNorm F G g + logNorm F G h := by
  have hg := one_le_maxNorm (F := F) G g
  have hh := one_le_maxNorm (F := F) G h
  have := Real.log_le_log (by linarith [one_le_maxNorm (F := F) G (g * h)]) (maxNorm_mul_le G g h)
  rw [Real.log_mul (by linarith) (by linarith)] at this
  unfold logNorm; linarith

end LogNorm

/-! ## 4b. Regularity of `x e^X` (Harish-Chandra; Thesis §4.1.1, BP §4.1)

For `x` semisimple and `X ∈ 𝔤_x` small and regular semisimple in `𝔤_x`, `x e^X` is regular
semisimple (`exists_nhds_isRegularSS_mul_expA`; the case `x = 1` is `exists_nhds_isRegularSS_expA`).
The proof is over `F` only: `e^X ∈ F[X]` (semisimplicity), the derivative of `s ↦ e^{sX}` at `0`
along `s = m^k → 0` (`𝔤_{e^X} ⊆ 𝔤_X`), and a norm estimate for `ad x` on its range
(`𝔤_{x e^X} ⊆ 𝔤_x`). -/

section ExpRegular

/-- Linear algebra: a semisimple `N` on a finite-dimensional normed space is invertible on its
range with a bounded inverse, so `N z = K z` for `z ∈ range N` and `‖K‖` small forces `z = 0`. -/
lemma exists_pos_eq_zero_of_isSemisimple {𝕜 W : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [NormedAddCommGroup W] [NormedSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    {N : W →ₗ[𝕜] W} (hN : Module.End.IsSemisimple N) :
    ∃ ε > 0, ∀ K : W →L[𝕜] W, ‖K‖ < ε → ∀ y, N (N y) = K (N y) → N y = 0 := by
  obtain ⟨q, hq, hcompl⟩ := Module.End.isSemisimple_iff.mp hN (LinearMap.ker N)
    (by
      rw [Module.End.mem_invtSubmodule]
      intro v hv
      simp only [Submodule.mem_comap, LinearMap.mem_ker] at hv ⊢
      rw [hv, map_zero])
  have hinj : Function.Injective (N ∘ₗ q.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h1 : (w : W) ∈ LinearMap.ker N := hw
    have := hcompl.disjoint.le_bot ⟨h1, w.2⟩
    exact Subtype.ext this
  obtain ⟨C, hC, hanti⟩ := (N ∘ₗ q.subtype).injective_iff_antilipschitz.mp hinj
  refine ⟨(C : ℝ)⁻¹, inv_pos.mpr hC, fun K hK y hy => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hcompl.sup_eq_top ▸ Submodule.mem_top (x := y))
  have hNa : N a = 0 := LinearMap.mem_ker.mp ha
  rw [map_add, hNa, zero_add] at hy ⊢
  have hz : N b ∈ q := hq hb
  have hbound := ZeroHomClass.bound_of_antilipschitz (N ∘ₗ q.subtype) hanti ⟨N b, hz⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at hbound
  rw [hy] at hbound
  have h2 : ‖K (N b)‖ ≤ ‖K‖ * ‖N b‖ := K.le_opNorm _
  by_contra hne
  have hpos : 0 < ‖N b‖ := norm_pos_iff.mpr hne
  have : ‖N b‖ ≤ (C : ℝ) * ‖K‖ * ‖N b‖ := by
    calc ‖N b‖ ≤ C * ‖K (N b)‖ := hbound
      _ ≤ C * (‖K‖ * ‖N b‖) := by gcongr
      _ = _ := by ring
  have hCK : (C : ℝ) * ‖K‖ < 1 := by
    calc (C : ℝ) * ‖K‖ < C * (C : ℝ)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hC)
  nlinarith

variable (F) [PAdicField F] {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A]
  [TopologicalSpace A] [IsModuleTopology F A]

/-- `e^0 = 1`. -/
lemma expA_zero_eq_one : expA F (0 : A) = 1 := by
  letI := isTopologicalRing_of_moduleTopology F A
  exact NormedSpace.exp_zero

variable {F}

/-- `e^X` commutes with everything that commutes with `X`. -/
lemma commute_expA_of_commute {X Y : A} (h : Commute Y X) : Commute Y (expA F X) := by
  letI := isTopologicalRing_of_moduleTopology F A
  haveI := t2Space_of_moduleTopology F A
  exact h.exp_right

variable (F)

/-- Over a `p`-adic field some positive integer `m` has `0 < ‖m‖ < 1` (the residue characteristic). -/
lemma exists_natCast_norm_lt_one : ∃ m : ℕ, 0 < ‖(m : F)‖ ∧ ‖(m : F)‖ < 1 := by
  by_contra H
  push Not at H
  have hle : ∀ n : ℕ, ‖(n : F)‖ ≤ 1 := fun n =>
    isUltrametricDist_iff_forall_norm_natCast_le_one.mp inferInstance n
  have hone : ∀ n : ℕ, n ≠ 0 → ‖(n : F)‖ = 1 := fun n hn =>
    le_antisymm (hle n) (H n (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hn)))
  obtain ⟨q, hq0, hq1⟩ := ratAbsF_isNontrivial F
  apply hq1
  simp only [ratAbsF, AbsoluteValue.coe_mk, MulHom.coe_mk]
  have hnum : ‖((q.num : ℤ) : F)‖ = 1 := by
    have hn : q.num.natAbs ≠ 0 := by simpa using hq0
    rw [← norm_natAbs]
    exact hone _ hn
  rw [← Rat.num_div_den q]
  push_cast
  rw [norm_div, hnum, hone _ q.den_nz]
  norm_num

local notation "VA" => (Fin (Module.finrank F A) → F)

set_option backward.isDefEq.respectTransparency false in
/-- **The centralizer of `e^X` is that of `X`** for `X` near `0` (one inclusion; the other is
`commute_expA_of_commute`).  Proof: if `Y` commutes with `e^X` it commutes with
`e^{mX} = (e^X)^m` for `m ∈ ℕ`, hence with `(e^{sX} - 1)/s` for `s = m^k`; choosing `|m| < 1`, these
tend to the derivative `X` of `s ↦ e^{sX}` at `0`.  Computed in `End(F^d)` via `lmulPi`. -/
lemma exists_nhds_commute_of_commute_expA :
    ∃ U ∈ 𝓝 (0 : A), ∀ X ∈ U, ∀ Y : A, Commute Y (expA F X) → Commute Y X := by
  letI := isTopologicalRing_of_moduleTopology F A
  obtain ⟨U, hU, -, h⟩ := expA_aux F (A := A)
  refine ⟨U, hU, fun X hX Y hY => ?_⟩
  obtain ⟨hb, -, he⟩ := h X hX
  set L := lmulPi F X
  set M := lmulPi F Y
  set r := (NormedSpace.expSeries F (VA →L[F] VA)).radius
  have hML : Commute M (NormedSpace.exp L) := by
    rw [← he]
    change M * lmulPi F (expA F X) = lmulPi F (expA F X) * M
    rw [← lmulPi_mul, ← lmulPi_mul, hY.eq]
  -- scalar multiples of `L` by elements of norm `≤ 1` stay in the ball of convergence
  have hball : ∀ c : F, ‖c‖ ≤ 1 → c • L ∈ Metric.eball (0 : VA →L[F] VA) r := by
    intro c hc
    rw [Metric.mem_eball, edist_zero_right] at hb ⊢
    refine lt_of_le_of_lt ?_ hb
    rw [enorm_smul]
    calc ‖c‖ₑ * ‖L‖ₑ ≤ 1 * ‖L‖ₑ := by
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_one.mpr hc
      _ = ‖L‖ₑ := one_mul _
  have hle : ∀ n : ℕ, ‖(n : F)‖ ≤ 1 := fun n =>
    isUltrametricDist_iff_forall_norm_natCast_le_one.mp inferInstance n
  have hballn : ∀ n : ℕ, n • L ∈ Metric.eball (0 : VA →L[F] VA) r := fun n => by
    rw [← Nat.cast_smul_eq_nsmul F]; exact hball _ (hle n)
  have hpow : ∀ n : ℕ, NormedSpace.exp (n • L) = NormedSpace.exp L ^ n := by
    intro n
    induction n with
    | zero => rw [zero_nsmul, NormedSpace.exp_zero, pow_zero]
    | succ n ih =>
      rw [succ_nsmul, NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := F)
          (by rw [nsmul_eq_mul]; exact (Nat.cast_commute n L).mul_left (Commute.refl L)) (hballn n) hb, ih, pow_succ]
  -- the derivative of `s ↦ e^{sL}` at `0` is `L`
  have h0 : (0 : F) • L ∈ Metric.eball (0 : VA →L[F] VA) r := by
    simpa using hball 0 (by simp)
  have hd : HasDerivAt (fun u : F => NormedSpace.exp (u • L)) L 0 := by
    have h1 : HasDerivAt (fun u : F => u • L) L 0 := by
      simpa using (hasDerivAt_id (0 : F)).smul_const L
    have h2 := hasFDerivAt_exp_zero_of_radius_pos (expSeries_radius_pos_of_pAdic F (VA →L[F] VA))
    have h3 := h2.comp_hasDerivAt_of_eq (0 : F) h1 (zero_smul F L).symm
    rw [one_apply_eq_self] at h3
    exact h3
  have hf0 : NormedSpace.exp ((0 : F) • L) = 1 := by
    rw [show (0 : F) • L = 0 from zero_smul F L]; exact NormedSpace.exp_zero
  have hderiv := hd.tendsto_slope_zero
  simp only [zero_add, hf0] at hderiv
  obtain ⟨m, hm0, hm1⟩ := exists_natCast_norm_lt_one F
  set s : ℕ → F := fun k => ((m ^ k : ℕ) : F)
  have hs : Tendsto s atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [s, Nat.cast_pow, norm_pow]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hm1
    · simp only [s, Nat.cast_pow, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact pow_ne_zero _ (norm_pos_iff.mp hm0)
  have hlim := hderiv.comp hs
  have hclosed : IsClosed {Z : VA →L[F] VA | M * Z = Z * M} :=
    isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  have hsmulL : ∀ (c : F) (W : VA →L[F] VA), M * (c • W) = c • (M * W) := fun c W => by
    ext v; simp
  have hsmulR : ∀ (c : F) (W : VA →L[F] VA), (c • W) * M = c • (W * M) := fun c W => by
    ext v; simp
  have hML' : M * L = L * M := by
    refine hclosed.mem_of_tendsto hlim (Eventually.of_forall fun k => ?_)
    simp only [Function.comp_apply, Set.mem_ofPred_eq, s]
    have hk : ((m ^ k : ℕ) : F) • L = (m ^ k) • L := by
      rw [← Nat.cast_smul_eq_nsmul F]
    rw [hk, hpow, hsmulL, hsmulR, ((hML.pow_right _).sub_right (Commute.one_right M)).eq]
  have hA : lmulPi F (Y * X) = lmulPi F (X * Y) := by
    rw [lmulPi_mul, lmulPi_mul]; exact hML'
  have := congrArg (lmulPiInv F) hA
  rw [lmulPiInv_lmulPi, lmulPiInv_lmulPi] at this
  exact this

/-- Near `0`, `e^X` lies in the subalgebra `F[X]` (a closed subspace; the exponential series
converges there, `expA_hasSum`). -/
lemma exists_nhds_expA_mem_adjoin :
    ∃ U ∈ 𝓝 (0 : A), ∀ X ∈ U, expA F X ∈ Algebra.adjoin F {X} := by
  letI := isTopologicalRing_of_moduleTopology F A
  haveI := t2Space_of_moduleTopology F A
  obtain ⟨U, hU, h⟩ := expA_hasSum F (A := A)
  refine ⟨U, hU, fun X hX => ?_⟩
  have hclosed : IsClosed ((Algebra.adjoin F {X} : Subalgebra F A) : Set A) :=
    (Subalgebra.toSubmodule (Algebra.adjoin F {X})).closed_of_finiteDimensional
  exact hclosed.mem_of_tendsto (h X hX) (Eventually.of_forall fun s =>
    Subalgebra.sum_mem _ fun n _ => Subalgebra.smul_mem _
      (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton F X) n) _)

/-- Near `0`, the exponential of a semisimple element is semisimple (`e^X` is a polynomial in
`X`). -/
lemma exists_nhds_isSS_expA : ∃ U ∈ 𝓝 (0 : A), ∀ X ∈ U, IsSS F X → IsSS F (expA F X) := by
  obtain ⟨U, hU, h⟩ := exists_nhds_expA_mem_adjoin F (A := A)
  refine ⟨U, hU, fun X hX hss => ?_⟩
  have hmem : Algebra.lmul F A (expA F X) ∈ Algebra.adjoin F {Algebra.lmul F A X} := by
    rw [← AlgHom.map_adjoin_singleton]
    exact Subalgebra.mem_map.mpr ⟨_, h X hX, rfl⟩
  exact Module.End.IsSemisimple.of_mem_adjoin_singleton hss hmem

variable {F}

/-- An abelian Lie subalgebra has abelian Lie subalgebras. -/
lemma isLieAbelian_of_le {K K' : LieSubalgebra F A} (h : K ≤ K') (hK' : IsLieAbelian ↥K') :
    IsLieAbelian ↥K := by
  refine ⟨fun a b => Subtype.ext ?_⟩
  have := congrArg Subtype.val (hK'.trivial (⟨a, h a.2⟩ : ↥K') ⟨b, h b.2⟩)
  simpa using this

lemma lieCentralizer_le_of_commute {𝔤 : LieSubalgebra F A} {a b : A}
    (h : ∀ Y ∈ 𝔤, Commute Y a → Commute Y b) : lieCentralizer 𝔤 a ≤ lieCentralizer 𝔤 b := by
  intro Y hY
  rw [mem_lieCentralizer] at hY ⊢
  exact ⟨hY.1, (h Y hY.1 hY.2.symm).eq.symm⟩

variable (F)

/-- **Regularity of `e^X`** (Harish-Chandra; the case `x = 1` of
`exists_nhds_isRegularSS_mul_expA`): for `X` near `0` and regular semisimple in `𝔤`, `e^X` is
regular semisimple: it is semisimple, and `𝔤_{e^X} ⊆ 𝔤_X` is abelian. -/
theorem exists_nhds_isRegularSS_expA (𝔤 : LieSubalgebra F A) :
    ∃ U ∈ 𝓝 (0 : A), ∀ X ∈ U, IsRegularSS 𝔤 X → IsRegularSS 𝔤 (expA F X) := by
  obtain ⟨U₁, hU₁, h₁⟩ := exists_nhds_isSS_expA F (A := A)
  obtain ⟨U₂, hU₂, h₂⟩ := exists_nhds_commute_of_commute_expA F (A := A)
  refine ⟨U₁ ∩ U₂, inter_mem hU₁ hU₂, fun X hX hreg => ⟨h₁ X hX.1 hreg.1, ?_⟩⟩
  exact isLieAbelian_of_le (lieCentralizer_le_of_commute fun Y _ hY => h₂ X hX.2 Y hY) hreg.2

/-- `e^X` is continuous at `0`. -/
lemma continuousAt_expA_at_zero : ContinuousAt (expA F : A → A) 0 := by
  letI := isTopologicalRing_of_moduleTopology F A
  obtain ⟨U, hU, -, h⟩ := expA_aux F (A := A)
  have heq : (fun X : A => lmulPiInv F (NormedSpace.exp (lmulPi F X))) =ᶠ[𝓝 0] expA F := by
    filter_upwards [hU] with X hX
    rw [← (h X hX).2.2, lmulPiInv_lmulPi]
  refine ContinuousAt.congr ?_ heq
  have h0 := (h 0 (mem_of_mem_nhds hU)).1
  have hexp : ContinuousAt (NormedSpace.exp : (VA →L[F] VA) → _) (lmulPi F (0 : A)) :=
    (NormedSpace.continuousOn_exp (𝕂 := F)).continuousAt (Metric.isOpen_eball.mem_nhds h0)
  exact (lmulPiInv F).continuous.continuousAt.comp (hexp.comp (continuous_lmulPi F).continuousAt)

/-- Right multiplication by `a`, transported to a continuous endomorphism of `F^d`. -/
def rmulPi (a : A) : VA →L[F] VA :=
  LinearMap.toContinuousLinearMap
    ((toPiCLE F A).toLinearEquiv.toLinearMap ∘ₗ LinearMap.mulRight F a ∘ₗ
      (toPiCLE F A).symm.toLinearEquiv.toLinearMap)

lemma rmulPi_apply (a : A) (v : VA) :
    rmulPi F a v = toPiCLE F A ((toPiCLE F A).symm v * a) := rfl

/-- `a ↦ rmulPi a` as a linear map. -/
def rmulPiₗ : A →ₗ[F] (VA →L[F] VA) where
  toFun := rmulPi F
  map_add' a b := ContinuousLinearMap.ext fun v => by simp [rmulPi_apply, mul_add]
  map_smul' c a := ContinuousLinearMap.ext fun v => by simp [rmulPi_apply]

lemma continuous_rmulPi : Continuous (rmulPi F : A → VA →L[F] VA) :=
  IsModuleTopology.continuous_of_linearMap (rmulPiₗ F)

variable {F}

/-- If `x` is semisimple (left multiplication), so is right multiplication by `x`: it is
annihilated by the (squarefree) minimal polynomial of `x`. -/
lemma isSemisimple_mulRight {x : A} (hx : IsSS F x) :
    Module.End.IsSemisimple (LinearMap.mulRight F x) := by
  set p := minpoly F (LinearMap.mulLeft F x)
  have hsq : Squarefree p := hx.minpoly_squarefree
  have hpx : Polynomial.aeval x p = 0 := by
    have h1 : Polynomial.aeval (Algebra.lmul F A x) p = Algebra.lmul F A (Polynomial.aeval x p) :=
      Polynomial.aeval_algHom_apply (Algebra.lmul F A) x p
    have h2 : Polynomial.aeval (LinearMap.mulLeft F x) p = 0 := minpoly.aeval F _
    have h3 := congrArg (fun f : Module.End F A => f 1) (h1.symm.trans h2)
    simpa using h3
  have hR : ∀ q : Polynomial F, Polynomial.aeval (LinearMap.mulRight F x) q =
      LinearMap.mulRight F (Polynomial.aeval x q) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, hp, hq]; ext; simp [mul_add]
    | monomial n c =>
      simp only [Polynomial.aeval_monomial, LinearMap.pow_mulRight]
      ext w
      simp [Algebra.smul_def, mul_assoc, Algebra.commutes]
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq ?_
  rw [hR, hpx]
  ext; simp

/-- `ad x = L_x - R_x` is semisimple for semisimple `x`. -/
lemma isSemisimple_ad {x : A} (hx : IsSS F x) :
    Module.End.IsSemisimple (LinearMap.mulLeft F x - LinearMap.mulRight F x) :=
  Module.End.IsSemisimple.sub_of_commute (LinearMap.commute_mulLeft_right x x) hx
    (isSemisimple_mulRight hx)

/-- Semisimplicity is invariant under conjugation by a linear equivalence. -/
lemma isSemisimple_conj {M₁ M₂ : Type*} [AddCommGroup M₁] [Module F M₁] [AddCommGroup M₂]
    [Module F M₂] [FiniteDimensional F M₁] (e : M₁ ≃ₗ[F] M₂) {f : Module.End F M₁} (hf : f.IsSemisimple) :
    (e.conjAlgEquiv F f).IsSemisimple := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hf.minpoly_squarefree ?_
  rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply, minpoly.aeval, map_zero]

variable (F) in
/-- **Commuting with `x e^X` forces commuting with `x`**, for `x` semisimple and `X ∈ 𝔤_x` near `0`
(the heart of Harish-Chandra's regularity statement near a semisimple element).

Proof.  Put `N = ad x = L_x - R_x` (semisimple), `u = e^X`, `v = e^{-X} = u⁻¹`.  If `Y` commutes with
`xu`, then `Z = N Y` satisfies `N Z = K Z` with `K W = v W u x - W x`, an operator that tends to
`0` as `X → 0` (`K = 0` at `X = 0`).  Since `N` is invertible on its range with bounded inverse
(`exists_pos_eq_zero_of_isSemisimple`), `Z = 0` once `‖K‖` is small.  No eigenvalues over `F̄`
are needed. -/
lemma exists_nhds_commute_of_commute_mul_expA {x : A} (hx : IsSS F x) :
    ∃ U ∈ 𝓝 (0 : A), ∀ X ∈ U, Commute x X → ∀ Y : A, Commute Y (x * expA F X) →
      Commute Y x := by
  letI := isTopologicalRing_of_moduleTopology F A
  set e := (toPiCLE F A).toLinearEquiv
  set NA : Module.End F A := LinearMap.mulLeft F x - LinearMap.mulRight F x
  set NV := e.conjAlgEquiv F NA
  have hNV : NV.IsSemisimple := isSemisimple_conj e (isSemisimple_ad hx)
  obtain ⟨ε, hε, hkey⟩ := exists_pos_eq_zero_of_isSemisimple hNV
  set K : A → (VA →L[F] VA) := fun X =>
    lmulPi F (expA F (-X)) * rmulPi F (expA F X * x) - rmulPi F x
  have hK0 : K 0 = 0 := by
    simp only [K, neg_zero, expA_zero_eq_one F, one_mul, lmulPi_one F, sub_self]
  have hKc : ContinuousAt K 0 := by
    have h1 : ContinuousAt (fun X : A => expA F (-X)) 0 :=
      ContinuousAt.comp (g := expA F) (by simpa using continuousAt_expA_at_zero F)
        continuous_neg.continuousAt
    have h2 : ContinuousAt (fun X : A => expA F X * x) 0 :=
      (continuousAt_expA_at_zero F).mul continuousAt_const
    exact (((continuous_lmulPi F).continuousAt.comp h1).mul
      ((continuous_rmulPi F).continuousAt.comp h2)).sub continuousAt_const
  obtain ⟨U₁, hU₁, h₁⟩ := expA_mul_expA_neg F (A := A)
  have hU₁' : {X : A | -X ∈ U₁} ∈ 𝓝 (0 : A) :=
    continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hU₁)
  have hU₂ : K ⁻¹' Metric.ball 0 ε ∈ 𝓝 (0 : A) :=
    hKc.preimage_mem_nhds (by rw [hK0]; exact Metric.ball_mem_nhds 0 hε)
  refine ⟨_, inter_mem hU₁' hU₂, fun X hX hxX Y hY => ?_⟩
  set u := expA F X
  set v := expA F (-X)
  have hvu : v * u = 1 := by
    have := h₁ (-X) hX.1
    rwa [neg_neg] at this
  have hxu : Commute x u := commute_expA_of_commute hxX
  have hxv : Commute x v := commute_expA_of_commute hxX.neg_right
  have e1 : v * (x * Y) * (u * x) = x * (x * Y) := by
    calc v * (x * Y) * (u * x) = v * (x * (Y * (x * u))) := by
          rw [← hxu.eq]; simp only [mul_assoc]
      _ = v * (x * (x * (u * Y))) := by rw [hY.eq, mul_assoc]
      _ = x * (x * ((v * u) * Y)) := by
          rw [hxv.symm.left_comm, hxv.symm.left_comm, mul_assoc]
      _ = x * (x * Y) := by rw [hvu, one_mul]
  have e2 : v * (Y * x) * (u * x) = x * (Y * x) := by
    calc v * (Y * x) * (u * x) = v * ((Y * (x * u)) * x) := by simp only [mul_assoc]
      _ = v * ((x * u * Y) * x) := by rw [hY.eq]
      _ = x * ((v * u) * (Y * x)) := by
          simp only [mul_assoc]; rw [hxv.symm.left_comm]
      _ = x * (Y * x) := by rw [hvu, one_mul]
  have hid : x * (x * Y - Y * x) = v * (x * Y - Y * x) * (u * x) := by
    rw [mul_sub v, sub_mul, e1, e2, mul_sub]
  have hNVy : ∀ W : A, NV (toPiCLE F A W) = toPiCLE F A (x * W - W * x) := fun W => by
    simp [NV, NA, LinearEquiv.conjAlgEquiv_apply, e]
  have hKy : ∀ W : A, K X (toPiCLE F A W) = toPiCLE F A (v * W * (u * x) - W * x) := fun W => by
    simp [K, lmulPi_apply, rmulPi_apply, mul_assoc, u, v]
  have hKX : ‖K X‖ < ε := by simpa using hX.2
  have h0 := hkey (K X) hKX (toPiCLE F A Y) (by rw [hNVy, hNVy, hKy, ← hid])
  rw [hNVy, map_eq_zero_iff _ (toPiCLE F A).injective, sub_eq_zero] at h0
  exact h0.symm

variable (F) in
/-- **Harish-Chandra's regularity near a semisimple element** (Thesis §4.1.1, BP §4.1: the setting
of the local expansion `θ(x e^X)`): if `x` is a semisimple unit, then for `X ∈ 𝔤_x` close to `0`
and regular semisimple in `𝔤_x`, the element `x e^X` is regular semisimple in `𝔤`.  Indeed `x e^X`
is a product of commuting semisimple elements, and `𝔤_{x e^X} ⊆ (𝔤_x)_X`
(`exists_nhds_commute_of_commute_mul_expA`, `exists_nhds_commute_of_commute_expA`), which is
abelian. -/
theorem exists_nhds_isRegularSS_mul_expA (𝔤 : LieSubalgebra F A) {x : A} (hx : IsSS F x)
    (hxu : IsUnit x) :
    ∃ U ∈ 𝓝 (0 : A), ∀ X ∈ U, X ∈ lieCentralizer 𝔤 x →
      IsRegularSS (lieCentralizer 𝔤 x) X → IsRegularSS 𝔤 (x * expA F X) := by
  obtain ⟨U₁, hU₁, h₁⟩ := exists_nhds_isSS_expA F (A := A)
  obtain ⟨U₂, hU₂, h₂⟩ := exists_nhds_commute_of_commute_expA F (A := A)
  obtain ⟨U₃, hU₃, h₃⟩ := exists_nhds_commute_of_commute_mul_expA F hx
  refine ⟨U₁ ∩ U₂ ∩ U₃, inter_mem (inter_mem hU₁ hU₂) hU₃, fun X hX hXc hreg => ⟨?_, ?_⟩⟩
  · have hxX : Commute x X := (mem_lieCentralizer.mp hXc).2
    have hxe : Commute x (expA F X) := commute_expA_of_commute hxX
    have hcomm : Commute (LinearMap.mulLeft F x) (LinearMap.mulLeft F (expA F X)) := by
      change LinearMap.mulLeft F x * LinearMap.mulLeft F (expA F X) =
        LinearMap.mulLeft F (expA F X) * LinearMap.mulLeft F x
      ext w; simp [← mul_assoc, hxe.eq]
    have := Module.End.IsSemisimple.mul_of_commute hcomm hx (h₁ X hX.1.1 hreg.1)
    unfold IsSS
    rwa [LinearMap.mulLeft_mul]
  · refine isLieAbelian_of_le ?_ hreg.2
    intro Y hY
    rw [mem_lieCentralizer] at hY
    have hxX : Commute x X := (mem_lieCentralizer.mp hXc).2
    have hYg : Commute Y (x * expA F X) := hY.2.symm
    have hYx : Commute Y x := h₃ X hX.2 hxX Y hYg
    have hYe : Commute Y (expA F X) := by
      have h : x * (expA F X * Y) = x * (Y * expA F X) := by
        rw [← mul_assoc, ← hYg.eq, ← mul_assoc, hYx.eq, mul_assoc]
      exact (hxu.mul_left_cancel h).symm
    have hYX : Commute Y X := h₂ X hX.1.2 Y hYe
    rw [mem_lieCentralizer, mem_lieCentralizer]
    exact ⟨⟨hY.1, hYx.eq.symm⟩, hYX.eq.symm⟩

end ExpRegular

/-! ## 5. Nilpotent orbits (Thesis §2.4, §4.2, §4.4) -/

section Nilpotent

variable {A : Type*} [Ring A] [Algebra F A]

/-- `G`-conjugacy on the nilpotent elements of `𝔤`. -/
def nilSetoid (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A) :
    Setoid {X : A // X ∈ 𝔤 ∧ IsNilpotent X} where
  r X Y := ∃ g ∈ G, (g : A) * X.1 * (↑g⁻¹ : A) = Y.1
  iseqv := by
    refine ⟨fun X ↦ ⟨1, G.one_mem, by simp⟩, ?_, ?_⟩
    · rintro X Y ⟨g, hg, h⟩
      refine ⟨g⁻¹, G.inv_mem hg, ?_⟩
      rw [← h]; simp [mul_assoc]
    · rintro X Y Z ⟨g, hg, h⟩ ⟨g', hg', h'⟩
      refine ⟨g' * g, G.mul_mem hg' hg, ?_⟩
      rw [← h', ← h]; simp [mul_assoc]

/-- `Nil(𝔤)`: the set of `G`-orbits of nilpotent elements of `𝔤` (Thesis §2.4). -/
def NilOrbit (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A) : Type _ :=
  Quotient (nilSetoid G 𝔤)

/-- The elements of `𝔤` lying in the orbit `O`. -/
def nilOrbitSet {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A} (O : NilOrbit G 𝔤) : Set ↥𝔤 :=
  {X | ∃ h : IsNilpotent (X : A), Quotient.mk (nilSetoid G 𝔤) ⟨X, X.2, h⟩ = O}

/-- The (absolute) rank of `𝔤`: the minimal dimension of a centralizer `𝔤_X`, `X ∈ 𝔤`
(attained on the dense set of regular elements; `F` is infinite). -/
def lieRank (𝔤 : LieSubalgebra F A) : ℕ :=
  ⨅ X : ↥𝔤, Module.finrank F ↥(lieCentralizer 𝔤 (X : A))

/-- `X` is a regular nilpotent element of `𝔤`: nilpotent with `dim 𝔤_X = rank 𝔤`. -/
def IsRegularNil (𝔤 : LieSubalgebra F A) (X : A) : Prop :=
  X ∈ 𝔤 ∧ IsNilpotent X ∧ Module.finrank F ↥(lieCentralizer 𝔤 X) = lieRank 𝔤

/-- `Nil_reg(𝔤)`: the regular nilpotent orbits (Thesis §4.2, §4.4). Empty iff `G` is not
quasi-split. -/
def NilReg (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A) : Set (NilOrbit G 𝔤) :=
  {O | IsRegularNil 𝔤 (Quotient.out O).1}

end Nilpotent

/-! ## 6. Harmonic analysis on `𝔤` (Thesis §2.4; BP §1.6, §1.8) -/

section Fourier

variable {V : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V] [MeasurableSpace V]

/-- Test functions in the `p`-adic case: locally constant, compactly supported (Schwartz–Bruhat
functions, Thesis §2.3). -/
def IsTestFn {X : Type*} [TopologicalSpace X] (f : X → ℂ) : Prop :=
  IsLocallyConstant f ∧ HasCompactSupport f

/-- Fourier transform w.r.t. a measure `μ` and pairing `ψ(B(X,Y))`:
`f̂(Y) = ∫ f(X) ψ(B(X,Y)) dμ(X)` (Thesis §2.4, no sign). -/
def fourierWRT (μ : Measure V) (B : LinearMap.BilinForm F V) (ψ : NontrivialAddChar F)
    (f : V → ℂ) (Y : V) : ℂ :=
  ∫ X, f X * ψ (B X Y) ∂μ

/-- `μ` is the Haar measure self-dual for `ψ ∘ B`: Fourier inversion
`f(Z) = ∫ f̂(Y) ψ(-B(Z,Y)) dμ(Y)` holds for all test functions. (For symmetric `B` this is
`f̂̂(Z) = f(-Z)`; the form with `-B(Z,Y)` is also correct for alternating `B`, which is needed for
the Kirillov form.) Equivalently `μ(L) μ(L^⊥) = 1` for every lattice `L`. (Thesis §2.4.) -/
def IsSelfDual (μ : Measure V) (B : LinearMap.BilinForm F V) (ψ : NontrivialAddChar F) : Prop :=
  μ.IsAddHaarMeasure ∧
    ∀ f : V → ℂ, IsTestFn f → ∀ Z, ∫ Y, fourierWRT μ B ψ f Y * ψ (-(B Z Y)) ∂μ = f Z

/-- The self-dual Haar measure for `B` and `ψ` (epsilon; `0` if `B` is degenerate). -/
def selfDualMeasure (B : LinearMap.BilinForm F V) (ψ : NontrivialAddChar F) : Measure V :=
  if h : ∃ μ, IsSelfDual μ B ψ then h.choose else 0

variable {A : Type*} [Ring A] [Algebra F A] [TopologicalSpace A]

/-- The restriction of `b` to `𝔤`. -/
def restrictForm (𝔤 : LieSubalgebra F A) (b : LinearMap.BilinForm F A) :
    LinearMap.BilinForm F ↥𝔤 :=
  b.compl₁₂ 𝔤.incl.toLinearMap 𝔤.incl.toLinearMap

/-- The Haar measure on `𝔤(F)` self-dual for `b` and `ψ` (Thesis §2.4). -/
def selfDualHaar (𝔤 : LieSubalgebra F A) (b : LinearMap.BilinForm F A) (ψ : NontrivialAddChar F) :
    Measure ↥𝔤 :=
  selfDualMeasure (restrictForm 𝔤 b) ψ

/-- The Fourier transform on `𝔤(F)`: `f̂(Y) = ∫_𝔤 f(X) ψ(b(X,Y)) dX`, `dX` self-dual
(Thesis §2.4). -/
def fourierLie (𝔤 : LieSubalgebra F A) (b : LinearMap.BilinForm F A) (ψ : NontrivialAddChar F)
    (f : ↥𝔤 → ℂ) (Y : ↥𝔤) : ℂ :=
  fourierWRT (selfDualHaar 𝔤 b ψ) (restrictForm 𝔤 b) ψ f Y

/-- The Kirillov form at `X ∈ 𝔤`: `ω_X(Y,Z) = b(Y,[X,Z])` (Thesis §2.4). Its radical is `𝔤_X`. -/
def kirillovForm (𝔤 : LieSubalgebra F A) (b : LinearMap.BilinForm F A) (X : ↥𝔤) :
    LinearMap.BilinForm F ↥𝔤 :=
  (restrictForm 𝔤 b).compl₂ (LieAlgebra.ad F ↥𝔤 X)

variable [PAdicField F] [Module.Finite F A] [IsModuleTopology F A]

variable (F) in
/-- `Y ↦ Ad(e^Y) X = e^Y X e^{-Y}`, the orbit map near the identity. -/
def orbitMap (X Y : A) : A := expA F Y * X * expA F (-Y)

/-- `μ` is the Kirillov (autodual symplectic) measure on the nilpotent orbit `O`
(Thesis §2.4, BP §1.6): it is carried by `O`, is `G`-invariant, and in the chart
`Y ↦ Ad(e^Y) X` on a complement `C` of `𝔤_X` it agrees *exactly*, on a neighbourhood of `0`,
with the Haar measure on `C ≅ 𝔤/𝔤_X` self-dual for `ψ ∘ ω_X`. (The chart has Jacobian `1` at
`0`; over a `p`-adic field its Jacobian has absolute value in `q^ℤ` and is continuous, hence is
identically `1` near `0`.) -/
def IsOrbitMeasure (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A) (b : LinearMap.BilinForm F A)
    (ψ : NontrivialAddChar F) (O : NilOrbit G 𝔤) (μ : Measure ↥𝔤) : Prop :=
  μ (nilOrbitSet O)ᶜ = 0 ∧
  (∀ g ∈ G, ∀ S : Set ↥𝔤, MeasurableSet S →
    μ (Subtype.val ⁻¹' (conjAd F g ⁻¹' (Subtype.val '' S))) = μ S) ∧
  ∀ X ∈ nilOrbitSet O, ∀ C : Submodule F ↥𝔤,
    IsCompl C (LinearMap.ker (LieAlgebra.ad F ↥𝔤 X)) →
    ∃ U ∈ 𝓝 (0 : A), ∀ S : Set ↥C, MeasurableSet S → (∀ Y ∈ S, ((Y : ↥𝔤) : A) ∈ U) →
      μ (Subtype.val ⁻¹' ((fun Y : ↥C ↦ orbitMap F (X : A) ((Y : ↥𝔤) : A)) '' S)) =
        selfDualMeasure ((kirillovForm 𝔤 b X).compl₁₂ C.subtype C.subtype) ψ S

/-- The Kirillov-normalized invariant measure `μ_O` on a nilpotent orbit (epsilon). -/
def orbitMeasure (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A) (b : LinearMap.BilinForm F A)
    (ψ : NontrivialAddChar F) (O : NilOrbit G 𝔤) : Measure ↥𝔤 :=
  if h : ∃ μ, IsOrbitMeasure G 𝔤 b ψ O μ then h.choose else 0

/-- `j` represents the Fourier transform of `μ_O`: `μ_O(f̂) = ∫_𝔤 f(X) j(X) dX` for all test
functions, `j` locally integrable and continuous on `𝔤_reg` (BP §1.8, §4.1; Thesis §4.1.1). -/
def IsJHat (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A) (b : LinearMap.BilinForm F A)
    (ψ : NontrivialAddChar F) (O : NilOrbit G 𝔤) (j : ↥𝔤 → ℂ) : Prop :=
  ContinuousOn j {X | IsRegularSS 𝔤 (X : A)} ∧
  LocallyIntegrable j (selfDualHaar 𝔤 b ψ) ∧
  ∀ f : ↥𝔤 → ℂ, IsTestFn f →
    ∫ X, fourierLie 𝔤 b ψ f X ∂(orbitMeasure G 𝔤 b ψ O) = ∫ X, f X * j X ∂(selfDualHaar 𝔤 b ψ)

/-- `ĵ(O, X)`: the function representing `f ↦ μ_O(f̂)` (BP §1.8, §4.1; Thesis §4.1.1).
Unique on `𝔤_reg` (an open set of full measure); extended by `0` off `𝔤`. -/
def jHat (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A) (b : LinearMap.BilinForm F A)
    (ψ : NontrivialAddChar F) (O : NilOrbit G 𝔤) (X : A) : ℂ :=
  if h : ∃ j, IsJHat G 𝔤 b ψ O j then
    (if hX : X ∈ 𝔤 then h.choose ⟨X, hX⟩ else 0)
  else 0

end Fourier

/-! ## 7. Quasi-characters and germs (Thesis §4.1.1, §4.2; BP §4.1, §4.5) -/

section QuasiCharacter

variable {A : Type*} [Ring A] [Algebra F A] [TopologicalSpace A]
  [PAdicField F] [Module.Finite F A] [IsModuleTopology F A]

/-- `c` gives the local expansion of `θ` at `x`:
`θ(x e^X) = ∑_{O ∈ Nil(𝔤_x)} c_O ĵ(O, X)` for all `X` in a neighbourhood of `0` in `𝔤_x` that are
regular in `𝔤_x` (BP §4.1; Thesis §4.1.1). Here `ĵ` is taken for `(G_x, 𝔤_x)` and `b|_{𝔤_x}`. -/
def HasGermExpansion (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A) (b : LinearMap.BilinForm F A)
    (ψ : NontrivialAddChar F) (θ : ↥G → ℂ) (x : ↥G)
    (c : NilOrbit (grpCentralizer G x) (lieCentralizer 𝔤 ((x : Aˣ) : A)) → ℂ) : Prop :=
  (Function.support c).Finite ∧
  ∃ ω ∈ 𝓝 (0 : A), ∀ X ∈ ω, X ∈ lieCentralizer 𝔤 ((x : Aˣ) : A) →
    IsRegularSS (lieCentralizer 𝔤 ((x : Aˣ) : A)) X →
    ∀ y : ↥G, ((y : Aˣ) : A) = ((x : Aˣ) : A) * expA F X →
      θ y = ∑ᶠ O, c O * jHat (grpCentralizer G x) (lieCentralizer 𝔤 ((x : Aˣ) : A)) b ψ O X

/-- `θ : G(F) → ℂ` is a quasi-character (`p`-adic definition, BP §4.1, Thesis §4.1.1): it is
conjugation invariant on `G_reg(F)`, and at every semisimple `x` it has a local expansion in the
`ĵ(O, ·)`, `O ∈ Nil(𝔤_x)`. Values of `θ` off `G_reg(F)` are irrelevant. (Local constancy on
`G_reg(F)` follows: at regular `x` only `O = 0` occurs.) -/
def IsQuasiCharacter (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A) (b : LinearMap.BilinForm F A)
    (ψ : NontrivialAddChar F) (θ : ↥G → ℂ) : Prop :=
  (∀ g y : ↥G, y ∈ regularSet G 𝔤 → θ (g * y * g⁻¹) = θ y) ∧
  ∀ x : ↥G, IsSS F ((x : Aˣ) : A) → ∃ c, HasGermExpansion G 𝔤 b ψ θ x c

/-- The germ `c_{θ,O}(x)`, `O ∈ Nil_reg(𝔤_x)` (Thesis §4.2, BP §4.5): the coefficient of `ĵ(O,·)`
in the local expansion of `θ` at `x`. Defined to be `0` if `O ∉ Nil_reg(𝔤_x)` or if there is no
expansion. -/
def germ (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A) (b : LinearMap.BilinForm F A)
    (ψ : NontrivialAddChar F) (θ : ↥G → ℂ) (x : ↥G)
    (O : NilOrbit (grpCentralizer G x) (lieCentralizer 𝔤 ((x : Aˣ) : A))) : ℂ :=
  if O ∈ NilReg _ _ then
    (if h : ∃ c, HasGermExpansion G 𝔤 b ψ θ x c then h.choose O else 0)
  else 0

/-- `c_θ(x) = |Nil_reg(𝔤_x)|⁻¹ ∑_{O ∈ Nil_reg(𝔤_x)} c_{θ,O}(x)` (Thesis §4.2); `0` when
`Nil_reg(𝔤_x)` is empty (i.e. `G_x` not quasi-split, consistent with Thesis Prop 4.2.1(i)). -/
def germAvg (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A) (b : LinearMap.BilinForm F A)
    (ψ : NontrivialAddChar F) (θ : ↥G → ℂ) (x : ↥G) : ℂ :=
  (∑ᶠ O ∈ NilReg (grpCentralizer G x) (lieCentralizer 𝔤 ((x : Aˣ) : A)), germ G 𝔤 b ψ θ x O) /
    ((NilReg (grpCentralizer G x) (lieCentralizer 𝔤 ((x : Aˣ) : A))).ncard : ℂ)

/-- If the local expansion at `x` is unique (true when `b|_{𝔤_x}` is nondegenerate, by the linear
independence of the `ĵ(O,·)`, BP §4.5), the germ is its coefficient. -/
lemma germ_eq_of_unique {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A} {b : LinearMap.BilinForm F A}
    {ψ : NontrivialAddChar F} {θ : ↥G → ℂ} {x : ↥G}
    {c : NilOrbit (grpCentralizer G x) (lieCentralizer 𝔤 ((x : Aˣ) : A)) → ℂ}
    (hc : HasGermExpansion G 𝔤 b ψ θ x c)
    (huniq : ∀ c', HasGermExpansion G 𝔤 b ψ θ x c' → c' = c)
    {O} (hO : O ∈ NilReg _ _) : germ G 𝔤 b ψ θ x O = c O := by
  have h : ∃ c, HasGermExpansion G 𝔤 b ψ θ x c := ⟨c, hc⟩
  have := huniq _ h.choose_spec
  simp [germ, hO, h, this]

lemma germ_of_not_mem {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A} {b : LinearMap.BilinForm F A}
    {ψ : NontrivialAddChar F} {θ : ↥G → ℂ} {x : ↥G} {O} (hO : O ∉ NilReg _ _) :
    germ G 𝔤 b ψ θ x O = 0 := by
  simp [germ, hO]

end QuasiCharacter

end GSpinGGP
