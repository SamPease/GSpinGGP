/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Scusp
import GSpinGGP.TraceFormula.Geometric
import GSpinGGP.Literature.LieAlgebra
import GSpinGGP.Literature.Fourier

/-!
# The geometric expansion near `1`, via the Lie algebra

The statement `geomAt_near` is the interface consumed
by `Spine.lean`.  It fuses Thesis Prop 12.4.1 (descent to `𝔤⁰` near `1`), Prop 12.5.1,
the endgame (Thesis §12.5) and Thm 12.2.2 (`J^Lie = J^Lie_geom`): the group-side
consequence "the geometric expansion holds for test functions supported near `A_G(F)`".

The Lie-algebra definitions (`𝔤⁰`, `𝔥⁰`, `J^Lie`, `θ_f` on `𝔤⁰`, germs, `m^Lie_geom`) and the two
cited theorems Thesis Thm 11.6.1 (`jLie_eq_of_thetaFLie_eqOn`) and the endgame of Thesis §12.5
(`lie_endgame`) are in `Literature/LieAlgebra.lean`; the axioms exclude a hyperbolic-plane factor.
This file holds:
* §1 `jqcLie`: `J^Lie_qc` on the `θ_f` (Prop 12.4.1(ii)), well defined by Thesis Thm 11.6.1;
* §2 Prop 12.5.1 (`prop_11_8_1_of_jqc`, SORRY; `prop_11_8_1`) and Thm 12.2.2 on `𝔤⁰`
  (`distribJLie_eq_mGeomLie`, from Prop 12.5.1 and the endgame);
* §3 the descent from `G` to `𝔤⁰` near `1` (`exists_lie_descent`, SORRY; Prop 12.4.1(i) and
  Prop 12.1.1(iv));
* §4 the triples with a hyperbolic-plane factor (`geomAt_near_of_isHypPlane_V`, elementary, proved
  with `Ω = G(F)` from the helpers in namespace `HypVAux`; `geomAt_near_of_isHypPlane_W`, a gap in
  the literature's coverage, SORRY);
* `geomAt_near`, proved from §2–§4.  Sanity checks: `Sanity/LieAudit.lean`.
-/

noncomputable section

open MeasureTheory Topology Filter

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
variable (ψ : NontrivialAddChar F) (d : GGPData F)

/-! ## 1. `J^Lie_qc` from the spectral expansion of `J^Lie` (Thesis Prop 12.4.1(ii)) -/

/-- `f ∈ S_scusp(𝔤⁰(F))` has a `θ_f` equal to `θ` on `𝔤⁰_reg(F)`. -/
def JqcPred (θ : ↥d.lieZero → ℂ) (f : ↥d.lieZero → ℂ) : Prop :=
  ∃ θ₀, d.IsLieScusp f ∧ d.IsThetaFLie ψ f θ₀ ∧
    ∀ X : ↥d.lieZero, IsRegularSS d.lieZero (X : d.ambient) → θ₀ X = θ X

open Classical in
/-- `J^Lie_qc` on the `θ_f` (Thesis Prop 12.4.1(ii)):
`θ ↦ J^Lie(f)` for any `f ∈ S_scusp(𝔤⁰(F))` with `θ_f = θ` on `𝔤⁰_reg(F)`, `0` if there is none.
Well defined by the spectral expansion of `J^Lie` (Thesis Thm 11.6.1,
`jLie_eq_of_thetaFLie_eqOn`) when neither `W` nor `V` is a hyperbolic plane (`distribJLie_eq_jqcLie`).  (Its continuous extension
to `SQC(𝔤⁰(F))`, given by the `Γ(Σ)` formula, is not needed in test-function form.) -/
def jqcLie (θ : ↥d.lieZero → ℂ) : ℂ :=
  if h : ∃ f, JqcPred ψ d θ f then d.distribJLie ψ h.choose else 0

/-- `J^Lie_qc` only sees the regular set. -/
theorem jqcLie_congr {θ θ' : ↥d.lieZero → ℂ}
    (he : ∀ X : ↥d.lieZero, IsRegularSS d.lieZero (X : d.ambient) → θ X = θ' X) :
    jqcLie ψ d θ = jqcLie ψ d θ' := by
  have e : JqcPred ψ d θ = JqcPred ψ d θ' := by
    funext f
    apply propext
    constructor
    · rintro ⟨θ₀, h1, h2, h3⟩
      exact ⟨θ₀, h1, h2, fun X hX => (h3 X hX).trans (he X hX)⟩
    · rintro ⟨θ₀, h1, h2, h3⟩
      exact ⟨θ₀, h1, h2, fun X hX => (h3 X hX).trans (he X hX).symm⟩
  unfold jqcLie
  rw [e]

/-- **Thesis Prop 12.4.1(ii), existence (from Thesis Thm 11.6.1)**: if neither `W` nor `V` is a hyperbolic
plane, `J^Lie(f) = J^Lie_qc(θ_f)` for every `f ∈ S_scusp(𝔤⁰(F))` whose `θ_f` exists.  This is
where the cited spectral expansion of `J^Lie` (`jLie_eq_of_thetaFLie_eqOn`) is used. -/
theorem distribJLie_eq_jqcLie (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    {f : ↥d.lieZero → ℂ} (hf : d.IsLieScusp f) (hθ : ∃ θ, d.IsThetaFLie ψ f θ) :
    d.distribJLie ψ f = jqcLie ψ d (d.thetaFLie ψ f) := by
  classical
  have hθf := d.isThetaFLie_thetaFLie_of_exists ψ hθ
  have h : ∃ f', JqcPred ψ d (d.thetaFLie ψ f) f' := ⟨f, _, hf, hθf, fun _ _ => rfl⟩
  unfold jqcLie
  rw [dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨θ₀, h1, h2, h3⟩ := h.choose_spec
  exact jLie_eq_of_thetaFLie_eqOn d ψ hW hV hf h1 hθf h2 (fun X hX => (h3 X hX).symm)

/-! ## 2. The Lie-algebra geometric expansion (Thesis Prop 12.5.1, Thm 12.2.2) -/

/-- The regular nilpotent orbits of `𝔤⁰` (at `X = 0`). -/
abbrev NilReg0 : Set (NilOrbit (lieGrpCentralizer d.G 0) (lieCentralizer d.lieZero 0)) :=
  NilReg (lieGrpCentralizer d.G 0) (lieCentralizer d.lieZero 0)

/-- **Thesis Prop 12.5.1 (with Prop 12.4.1(iv)), test-function form**.  Assume (HYP) and that
`J^Lie` factors through `θ_f` by a form `L` that only sees `𝔤⁰_reg` (Prop 12.4.1(ii),
`distribJLie_eq_jqcLie`).  Then `J^Lie(f) − m^Lie_geom(θ_f) = Σ_{O ∈ Nil_reg(𝔤⁰)} c_O c_{θ_f,O}(0)` for some constants `c_O`.

Proof route (own work, not formalized): `L − m^Lie_geom` is a continuous linear form on
`SQC(𝔤⁰(F))` (BP (1.7.2), Prop 12.1.1(iii)), homogeneous of degree `δ(G)/2` (from the `Γ(Σ)`
formula and Prop 12.1.1(iii)); it vanishes on quasi-characters with `0 ∉ Supp θ`
(Prop 12.4.1(iv): semisimple descent to the Lie algebras of the smaller triples `(G'_X, H'_X)`,
which satisfy the geometric expansion by (HYP), via Prop 12.4.1(iii) for them); a homogeneous
form supported at `0` is a combination of the germs at `0` (BP Prop 4.6.1).
Status: SORRY. -/
theorem prop_11_8_1_of_jqc (h : HYP ψ d) (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    (L : (↥d.lieZero → ℂ) → ℂ)
    (hL : ∀ f, d.IsLieScusp f → (∃ θ, d.IsThetaFLie ψ f θ) →
      d.distribJLie ψ f = L (d.thetaFLie ψ f))
    (hLc : ∀ θ θ' : ↥d.lieZero → ℂ,
      (∀ X : ↥d.lieZero, IsRegularSS d.lieZero (X : d.ambient) → θ X = θ' X) → L θ = L θ') :
    ∃ c : NilOrbit (lieGrpCentralizer d.G 0) (lieCentralizer d.lieZero 0) → ℂ,
      ∀ f : ↥d.lieZero → ℂ, d.IsLieScusp f →
        d.distribJLie ψ f - d.mGeomLie ψ (d.thetaFLie ψ f) =
          ∑ᶠ O ∈ NilReg0 d, c O * d.germLie0 ψ (d.thetaFLie ψ f) 0 O := by
  sorry

/-- **Thesis Prop 12.5.1**, from `prop_11_8_1_of_jqc` and Thesis Thm 11.6.1. -/
theorem prop_11_8_1 (h : HYP ψ d) (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) :
    ∃ c : NilOrbit (lieGrpCentralizer d.G 0) (lieCentralizer d.lieZero 0) → ℂ,
      ∀ f : ↥d.lieZero → ℂ, d.IsLieScusp f →
        d.distribJLie ψ f - d.mGeomLie ψ (d.thetaFLie ψ f) =
          ∑ᶠ O ∈ NilReg0 d, c O * d.germLie0 ψ (d.thetaFLie ψ f) 0 O :=
  prop_11_8_1_of_jqc ψ d h hW hV (jqcLie ψ d)
    (fun _ hf hθ => distribJLie_eq_jqcLie ψ d hW hV hf hθ) (fun _ _ he => jqcLie_congr ψ d he)

/-- **Thesis Thm 12.2.2 on `𝔤⁰`: `J^Lie = J^Lie_geom`**,
for triples without a hyperbolic-plane factor: Prop 12.5.1 and the endgame of Thesis §12.5
(`lie_endgame`, all `c_O = 0`). -/
theorem distribJLie_eq_mGeomLie (h : HYP ψ d) (hW : ¬ IsHypPlane d.QW)
    (hV : ¬ IsHypPlane d.QV) {f : ↥d.lieZero → ℂ} (hf : d.IsLieScusp f) :
    d.distribJLie ψ f = d.mGeomLie ψ (d.thetaFLie ψ f) := by
  obtain ⟨c, hc⟩ := prop_11_8_1 ψ d h hW hV
  have h0 := lie_endgame d ψ hW hV c hc
  have hs : ∑ᶠ O ∈ NilReg0 d, c O * d.germLie0 ψ (d.thetaFLie ψ f) 0 O = 0 := by
    rw [finsum_mem_congr rfl (fun O hO => by rw [h0 O hO, zero_mul])]
    simp
  exact sub_eq_zero.mp ((hc f hf).trans hs)

/-! ## 3. Descent from `G` to `𝔤⁰` near `1` (Thesis Prop 12.4.1(i), Prop 12.1.1(iv)) -/

/-- **Descent to the Lie algebra near `1`** (Thesis Prop 12.4.1(i) and Prop 12.1.1(iv)), for triples without a hyperbolic-plane
factor (so `𝔤 = Lie(A_G) ⊕ 𝔤⁰` and `A_G ∩ H = A_{G,H}`).  For a `G(F)`-excellent compact open
`ω ∋ 0` in `𝔤⁰(F)`, `Ω = A_G(F)·exp(ω)` is open, closed, invariant and `A_G(F)`-stable, and for
`f ∈ 𝒞_scusp(A_G\G, χ⁻¹)` supported in `Ω`, `F = (j_G^H)^{1/2} f_ω` (`f_ω(X) = f(e^X)` on `ω`) is
strongly cuspidal on `𝔤⁰` with `J(f) = J^Lie(F)` (BP (3.3.2) on `H`: `𝔥 = Lie(A_{G,H}) ⊕ 𝔥⁰`,
`χ` trivial on `A_{G,H}`) and `m_geom(θ_f) = m^Lie_geom(θ_F)` (`exp` is a measure-preserving
homeomorphism `ω ∩ Γ^Lie(G,H) ≃ exp(ω) ∩ Γ(G,H)`, and `θ_F = (j_G^H)^{1/2}(θ_f)_ω`
near `0`).  Status: SORRY (own work). -/
theorem exists_lie_descent (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    (χ : CentralCharOn d) :
    ∃ Ω : Set ↥d.G, IsInvariantClopen d Ω ∧ (1 : ↥d.G) ∈ Ω ∧
      ∀ f ∈ ScuspTestFn d χ, Function.support f ⊆ Ω →
        ∃ F : ↥d.lieZero → ℂ, d.IsLieScusp F ∧ distribJ d ψ f = d.distribJLie ψ F ∧
          mGeom ψ d (thetaF d f) = d.mGeomLie ψ (d.thetaFLie ψ F) := by
  sorry

/-! ## 4. Triples with a hyperbolic-plane factor -/

/-! ### Helpers for `geomAt_near_of_isHypPlane_V` (namespace `HypVAux`)

The first part copies generic lemmas of `Sanity/Witnesses.lean` (self-dual and orbit measures of the
zero orbit, `ĵ(0,·) = 1`, Haar measure on a point, local constancy along `x e^X`), which cannot be
imported here (`Sanity` imports this file).  The second part shows that when `V` is a hyperbolic
plane (`dim W = 1`, `r = 0`) the datum behaves like the toy datum of `toy_geomAt` (`Sanity/Witnesses.lean`): `G = A_G` is
commutative, `H = A_{G,H}`, every element of `G` and `𝔤` is regular semisimple, `𝔤` has no nonzero
nilpotent, `Γ(G,H)` is the single torus `GSpin(W) = F^×`, and `D^G = Δ = 1`. -/

namespace HypVAux

set_option linter.style.haveILetI false

open Module CliffordAlgebra Polynomial
open scoped Classical

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

section SelfDualZero

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

end SelfDualZero

section ZeroOrbit

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

section CliffHelpers

variable {K : Type*} [Field K] [Invertible (2 : K)]

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


theorem scalarGSpin_range_le_splitCentral {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : (scalarGSpin Q).range ≤ splitCentralGSpin Q := by
  rintro _ ⟨c, rfl⟩
  exact scalarGSpin_mem_splitCentralGSpin Q c

end CliffHelpers

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

theorem absF_one' : absF (1 : F) = 1 := by
  rw [absF_of_ne_zero one_ne_zero]
  have : Units.mk0 (1 : F) one_ne_zero = 1 := Units.ext rfl
  rw [this, map_one]
  rfl
theorem probHaar_real_univ (Q : Type*) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [MeasurableSpace Q] [BorelSpace Q] [CompactSpace Q] : (probHaar Q).real Set.univ = 1 := by
  unfold probHaar
  rw [dite_eq_left_of_eq_true (eq_true ‹_›), measureReal_def]
  have : Measure.haarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ :
      TopologicalSpace.PositiveCompacts Q) Set.univ = 1 := Measure.haarMeasure_self
  rw [this, ENNReal.toReal_one]
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

/-! ### Structure of a GGP datum whose `V` is a hyperbolic plane (`dim W = 1`, `r = 0`) -/

section Plane

variable {K : Type*} [Field K] [Invertible (2 : K)]

/-- Even elements of the Clifford algebra of a line are scalars. -/
theorem even_scalar_of_finrank_one {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (hV : finrank K V = 1) {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q 0) : ∃ c, x = algebraMap K _ c := by
  obtain ⟨e, -, he⟩ := finrank_eq_one_iff'.mp hV
  choose co hco using he
  have hι : ∀ u : V, ι Q u = co u • ι Q e := fun u => by rw [← map_smul, hco]
  induction x, hx using even_induction with
  | algebraMap r => exact ⟨r, rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, (map_add _ _ _).symm⟩
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
    obtain ⟨c, rfl⟩ := hx
    refine ⟨co m₁ * co m₂ * Q e * c, ?_⟩
    rw [hι m₁, hι m₂, smul_mul_smul_comm, ι_sq_scalar, smul_mul_assoc, ← map_mul,
      Algebra.smul_def, ← map_mul]
    congr 1
    ring

/-- Even elements of the Clifford algebra of a plane commute (`C⁺(V) = K ⊕ K e₀e₁`). -/
theorem even_comm_of_finrank_two {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
    {Q : QuadraticForm K V} (hV : finrank K V = 2) {x y : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q 0) (hy : y ∈ evenOdd Q 0) : x * y = y * x := by
  obtain ⟨e, he⟩ := exists_orthogonal_basis_fin_two Q hV
  obtain ⟨a, b, rfl⟩ := exists_eq_smul_one_add_smul_of_even e he _ hx
  obtain ⟨c, c', rfl⟩ := exists_eq_smul_one_add_smul_of_even e he _ hy
  simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one]
  module

/-- An orthogonal basis vector of a nondegenerate plane is anisotropic. -/
theorem Q_basis_ne_zero {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (hnd : IsNondeg Q) (e : Basis (Fin 2) K V) (he : ∀ i j, i ≠ j → bform Q (e i) (e j) = 0)
    (i : Fin 2) : Q (e i) ≠ 0 := by
  intro h0
  have hb : ∀ y, bform Q (e i) y = 0 := by
    intro y
    rw [← e.sum_repr y, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      have : bform Q (e i) (e i) = Q (e i) := QuadraticMap.associated_eq_self_apply K Q (e i)
      rw [this, h0, mul_zero]
    · rw [he i j hij, mul_zero]
  exact e.ne_zero i ((isNondeg_iff Q).mp hnd (e i) hb)

/-- For an orthogonal basis of a plane, `(e₀e₁)² = -q(e₀)q(e₁)`. -/
theorem omega_sq {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (e : Basis (Fin 2) K V) (he : ∀ i j, i ≠ j → bform Q (e i) (e j) = 0) :
    (ι Q (e 0) * ι Q (e 1)) * (ι Q (e 0) * ι Q (e 1)) =
      algebraMap K _ (-(Q (e 0) * Q (e 1))) := by
  have h10 : ι Q (e 1) * ι Q (e 0) = -(ι Q (e 0) * ι Q (e 1)) := by
    have h1 := ι_mul_ι_add_swap (Q := Q) (e 1) (e 0)
    have hb : bform Q (e 1) (e 0) = 0 := he 1 0 (by decide)
    rw [polar_eq_two_mul_bform, hb, mul_zero, (algebraMap K (CliffordAlgebra Q)).map_zero] at h1
    exact eq_neg_of_add_eq_zero_left h1
  calc (ι Q (e 0) * ι Q (e 1)) * (ι Q (e 0) * ι Q (e 1))
      = ι Q (e 0) * (ι Q (e 1) * ι Q (e 0)) * ι Q (e 1) := by simp only [mul_assoc]
    _ = -((ι Q (e 0) * ι Q (e 0)) * (ι Q (e 1) * ι Q (e 1))) := by
        rw [h10]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = _ := by rw [ι_sq_scalar, ι_sq_scalar, ← map_mul, ← map_neg]

end Plane

variable {d}

theorem m_r_of_isHypPlane (hV : IsHypPlane d.QV) : d.m = 1 ∧ d.r = 0 := by
  have h := hV.1
  simp only [GGPData.V, Module.finrank_prod, Module.finrank_fin_fun] at h
  omega

theorem finrank_W (hV : IsHypPlane d.QV) : finrank F (Fin d.m → F) = 1 := by
  rw [Module.finrank_fin_fun]; exact (m_r_of_isHypPlane hV).1

theorem gspinW_scalar (hV : IsHypPlane d.QV) (g : GSpin d.QW) :
    ∃ c, ((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) = algebraMap F _ c := by
  have hev := g.2.1
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at hev
  exact even_scalar_of_finrank_one (finrank_W hV) hev

theorem gspinW_mem_range (hV : IsHypPlane d.QV) (g : GSpin d.QW) :
    g ∈ (scalarGSpin d.QW).range :=
  mem_range_scalarGSpin_of_scalar g (gspinW_scalar hV g)

theorem gspinW_comm (hV : IsHypPlane d.QV) (a b : GSpin d.QW) : a * b = b * a := by
  obtain ⟨c, rfl⟩ := gspinW_mem_range hV a
  exact ((Subgroup.mem_center_iff.mp (scalarGSpin_mem_center d.QW c)) b).symm

/-- Both components even (true for `G(F)` and for `𝔤`). -/
def IsEvenPair (a : d.ambient) : Prop := a.1 ∈ evenOdd d.QW 0 ∧ a.2 ∈ evenOdd d.QV 0

theorem isEvenPair_G (g : ↥d.G) : IsEvenPair ((g : d.ambientˣ) : d.ambient) := by
  have h1 := (d.fst g).2.1
  have h2 := (d.snd g).2.1
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at h1 h2
  exact ⟨h1, h2⟩

theorem isEvenPair_lie {X : d.ambient} (hX : X ∈ d.lie) : IsEvenPair X := by
  obtain ⟨h1, h2⟩ := hX
  have a := h1.1
  have b := h2.1
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at a b
  exact ⟨a, b⟩

/-- Even pairs commute when `V` is a hyperbolic plane (`C⁺(W) = F`, `C⁺(V)` commutative). -/
theorem comm_of_isEvenPair (hV : IsHypPlane d.QV) {a b : d.ambient} (ha : IsEvenPair a)
    (hb : IsEvenPair b) : a * b = b * a := by
  obtain ⟨l, hl⟩ := even_scalar_of_finrank_one (finrank_W hV) ha.1
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_mul]
    rw [hl]
    exact Algebra.commutes _ _
  · simp only [Prod.snd_mul]
    exact even_comm_of_finrank_two hV.1 ha.2 hb.2

/-- Even pairs are semisimple when `V` is a hyperbolic plane: `a = (l, α + β ω)` with
`ω² = c ≠ 0`, the sum of a pair of scalars and `β (0, ω)`, `(0, ω)` being a root of the
squarefree `X (X² − c)`. -/
theorem isSS_of_isEvenPair (hV : IsHypPlane d.QV) {a : d.ambient} (ha : IsEvenPair a) :
    IsSS F a := by
  obtain ⟨l, hl⟩ := even_scalar_of_finrank_one (finrank_W hV) ha.1
  obtain ⟨e, he⟩ := exists_orthogonal_basis_fin_two d.QV hV.1
  obtain ⟨α, β, hαβ⟩ := exists_eq_smul_one_add_smul_of_even e he _ ha.2
  set ω : CliffordAlgebra d.QV := ι d.QV (e 0) * ι d.QV (e 1) with hω
  set c : F := -(d.QV (e 0) * d.QV (e 1)) with hc
  have hc0 : c ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (Q_basis_ne_zero hV.2.1 e he 0)
    (Q_basis_ne_zero hV.2.1 e he 1))
  have hωω : ω * ω = algebraMap F _ c := omega_sq e he
  set u : d.ambient := (algebraMap F _ l, algebraMap F _ α) with hu
  set v : d.ambient := (0, ω) with hv
  have hdec : a = u + β • v := by
    refine Prod.ext ?_ ?_
    · simp [hu, hv, hl]
    · simp only [hu, hv, Prod.snd_add, Prod.smul_snd, hαβ, Algebra.algebraMap_eq_smul_one]
  have hsu : IsSS F u := isSS_pair_algebraMap l α
  have hsv : IsSS F v := by
    refine isSS_of_aeval_eq_zero (p := X * (X ^ 2 - C c)) ?_ ?_
    · have hcop : IsCoprime (X : F[X]) (X ^ 2 - C c) := by
        refine (irreducible_X.coprime_iff_not_dvd).2 ?_
        rw [X_dvd_iff]
        simp [hc0]
      exact (separable_X.mul (separable_X_pow_sub_C c (by norm_num) hc0) hcop).squarefree
    · simp only [map_mul, map_sub, map_pow, aeval_X, aeval_C]
      refine Prod.ext ?_ ?_
      · simp [hv]
      · simp only [hv, Prod.snd_mul, Prod.snd_sub, Prod.algebraMap_apply,
          Prod.snd_zero, pow_two, hωω, sub_self, mul_zero]
  have hcomm : Commute (LinearMap.mulLeft F u) (LinearMap.mulLeft F v) := by
    have huv : u * v = v * u := by
      refine Prod.ext ?_ ?_
      · simp [hu, hv]
      · simp only [hu, hv, Prod.snd_mul]
        exact Algebra.commutes _ _
    refine LinearMap.ext fun z => ?_
    simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, ← mul_assoc, huv]
  have hlin : LinearMap.mulLeft F a = LinearMap.mulLeft F u + β • LinearMap.mulLeft F v := by
    refine LinearMap.ext fun z => ?_
    simp [hdec, add_mul]
  unfold IsSS
  rw [hlin]
  exact Module.End.IsSemisimple.add_of_commute (hcomm.smul_right β) hsu
    (Module.End.IsSemisimple_smul β hsv)

theorem isLieAbelian_of_le (hV : IsHypPlane d.QV) (L : LieSubalgebra F d.ambient)
    (hL : L ≤ d.lie) : IsLieAbelian ↥L :=
  ⟨fun X Y => by
    apply Subtype.ext
    rw [LieSubalgebra.coe_bracket, Ring.lie_def,
      comm_of_isEvenPair hV (isEvenPair_lie (hL X.2)) (isEvenPair_lie (hL Y.2)), sub_self]
    rfl⟩

theorem lieCentralizer_eq (hV : IsHypPlane d.QV) {L : LieSubalgebra F d.ambient} (hL : L ≤ d.lie)
    {x : d.ambient} (hx : IsEvenPair x) : lieCentralizer L x = L := by
  ext X
  rw [mem_lieCentralizer]
  exact ⟨fun h => h.1, fun h => ⟨h, comm_of_isEvenPair hV hx (isEvenPair_lie (hL h))⟩⟩

theorem isRegularSS_of_isEvenPair (hV : IsHypPlane d.QV) {L : LieSubalgebra F d.ambient}
    (hL : L ≤ d.lie) {a : d.ambient} (ha : IsEvenPair a) : IsRegularSS L a :=
  ⟨isSS_of_isEvenPair hV ha, isLieAbelian_of_le hV _ (inf_le_left.trans hL)⟩

theorem regularSet_eq_univ (hV : IsHypPlane d.QV) : regularSet d.G d.lie = Set.univ :=
  Set.eq_univ_of_forall fun g => isRegularSS_of_isEvenPair hV le_rfl (isEvenPair_G g)

theorem eq_zero_of_isNilpotent (hV : IsHypPlane d.QV) {X : d.ambient} (hX : X ∈ d.lie)
    (hn : IsNilpotent X) : X = 0 := by
  have hs := isSS_of_isEvenPair hV (isEvenPair_lie hX)
  have hn' : IsNilpotent (LinearMap.mulLeft F X) := hn.map (Algebra.lmul F d.ambient)
  have h0 := Module.End.eq_zero_of_isNilpotent_isSemisimple hn' hs
  have := congrArg (fun f => f 1) h0
  simpa using this

theorem N_eq_one (hV : IsHypPlane d.QV) {n : GSpin d.QV} (hn : n ∈ d.N) : n = 1 := by
  have hr := (m_r_of_isHypPlane hV).2
  obtain ⟨-, -, h2, h3⟩ := hn
  have htop : d.flag.top = ⊥ := by
    have : Fin.last d.flag.len = 0 := Fin.ext (by simp only [Fin.val_last, Fin.val_zero]; exact hr)
    unfold IsotropicFlag.top
    rw [this, d.flag.sub_zero]
  have hP : specP d.QV n = 1 := by
    refine LinearEquiv.ext fun v => ?_
    have := h2 v (by rw [htop, LinearMap.BilinForm.orthogonal_bot]; trivial)
    rw [htop, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  have hk : n ∈ (specP d.QV).ker := hP
  rw [ker_specP d.nondeg_QV] at hk
  obtain ⟨c, hc⟩ := hk
  have h1 : ((n : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) = 1 :=
    eq_one_of_scalar_of_isNilpotent ⟨c, by rw [← hc]; rfl⟩ h3
  exact Subtype.ext (Units.ext h1)

theorem AG_eq_top (hV : IsHypPlane d.QV) : d.AG = ⊤ := by
  classical
  refine eq_top_iff.mpr fun g _ => ?_
  refine ⟨(d.fst g, d.snd g), ⟨?_, ?_⟩, ?_⟩
  · exact scalarGSpin_range_le_splitCentral _ (gspinW_mem_range hV _)
  · unfold splitCentralGSpin
    simp only [hV, ↓reduceIte]
    trivial
  · exact d.G_ext rfl rfl

theorem mem_AGH_of_mem_H (hV : IsHypPlane d.QV) {h : ↥d.G} (hh : h ∈ d.H) : h ∈ d.AGH := by
  have hN : d.nPart h ∈ d.N := hh
  have hn1 : d.nPart h = 1 := N_eq_one hV hN
  obtain ⟨c, hc⟩ := gspinW_mem_range hV (d.fst h)
  refine ⟨c, ?_⟩
  have hsnd : d.snd h = d.incl (d.fst h) := by
    have : (d.incl (d.fst h))⁻¹ * d.snd h = 1 := hn1
    exact (inv_mul_eq_one.mp this).symm
  apply d.G_ext
  · exact hc
  · exact (congrArg d.incl hc).trans hsnd.symm

theorem G_comm (hV : IsHypPlane d.QV) (g h : ↥d.G) : g * h = h * g := by
  apply Subtype.ext
  apply Units.ext
  show ((g : d.ambientˣ) : d.ambient) * h = h * g
  exact comm_of_isEvenPair hV (isEvenPair_G g) (isEvenPair_G h)



/-! ### The two sides of the trace formula when `V` is a hyperbolic plane -/

theorem subsingleton_GmodAG (hV : IsHypPlane d.QV) : Subsingleton d.GmodAG :=
  ⟨fun x y => Quotient.inductionOn₂' x y fun _ _ =>
    QuotientGroup.eq.mpr (by rw [AG_eq_top hV]; trivial)⟩

theorem subsingleton_HmodAGH (hV : IsHypPlane d.QV) : Subsingleton d.HmodAGH :=
  ⟨fun x y => Quotient.inductionOn₂' x y fun a b =>
    QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr (mem_AGH_of_mem_H hV (a⁻¹ * b).2))⟩

theorem subsingleton_HGQuot (hV : IsHypPlane d.QV) : Subsingleton d.HGQuot := by
  haveI := subsingleton_GmodAG hV
  exact ⟨fun x y => Quotient.inductionOn₂ x y fun a b => congrArg _ (Subsingleton.elim a b)⟩

/-- A `χ⁻¹`-equivariant function takes the value `f(1)` on `A_{G,H}`. -/
theorem apply_of_mem_AGH (χ : CentralCharOn d) {f : ↥d.G → ℂ} (hf : IsChiEquivariant d χ f)
    {h : ↥d.G} (hh : h ∈ d.AGH) : f h = f 1 := by
  have := hf ⟨h, d.AGH_le_AG hh⟩ 1
  rw [mul_one, χ.trivial_AGH h hh] at this
  simpa using this

/-- `K(f, x) = f(1)` (`H = A_{G,H}`, `G` commutative, `H/A_{G,H}` a point). -/
theorem kernelK_eq (hV : IsHypPlane d.QV) (χ : CentralCharOn d) {f : ↥d.G → ℂ}
    (hf : IsChiEquivariant d χ f) (x : ↥d.G) : kernelK d ψ f x = f 1 := by
  haveI := subsingleton_HmodAGH hV
  have key : ∀ q : d.HmodAGH, kernelIntegrand d ψ f x (Quotient.out q) = f 1 := by
    intro q
    have hh : ((Quotient.out q : ↥d.H) : ↥d.G) ∈ d.AGH := mem_AGH_of_mem_H hV (Quotient.out q).2
    have hc : x⁻¹ * ((Quotient.out q : ↥d.H) : ↥d.G) * x = (Quotient.out q : ↥d.H) := by
      rw [G_comm hV x⁻¹, inv_mul_cancel_right]
    unfold kernelIntegrand
    rw [hc, apply_of_mem_AGH χ hf hh, d.xi_eq_one_of_mem_AGH' ψ.toAddChar _ hh, mul_one]
  unfold kernelK
  simp_rw [key]
  rw [integral_const, haar_real_univ_of_subsingleton, one_smul]

/-- A Weil measure exists: `dirac` at the unique point of `H\G/A_G`. -/
theorem exists_weil (hV : IsHypPlane d.QV) : ∃ m, IsWeilMeasure d.toGmodAG
    (Measure.haar : Measure d.GmodAG) (Measure.haar : Measure d.HmodAGH) m := by
  haveI := subsingleton_GmodAG hV
  haveI := subsingleton_HmodAGH hV
  haveI hq := subsingleton_HGQuot hV
  refine ⟨Measure.dirac (CosetSpace.mk d.toGmodAG 1), ?_⟩
  intro φ _ _
  have hpt : d.toGmodAG 1 * CosetSpace.out d.toGmodAG (CosetSpace.mk d.toGmodAG 1) = 1 :=
    Subsingleton.elim _ _
  simp only [integral_of_subsingleton (Measure.haar : Measure d.GmodAG) φ 1,
    @integral_of_subsingleton _ _ _ hq _ _ _
      (Measure.dirac (CosetSpace.mk d.toGmodAG 1)) _ (CosetSpace.mk d.toGmodAG 1),
    integral_of_subsingleton (Measure.haar : Measure d.HmodAGH) _ 1, hpt,
    haar_real_univ_of_subsingleton (X := d.GmodAG),
    haar_real_univ_of_subsingleton (X := d.HmodAGH), probReal_univ, one_smul]

theorem weilMeasureHG_real_univ (hV : IsHypPlane d.QV) : d.weilMeasureHG.real Set.univ = 1 := by
  haveI := subsingleton_GmodAG hV
  haveI := subsingleton_HmodAGH hV
  have hW := d.weilMeasureHG_spec_of_exists (exists_weil hV)
  have h := hW (fun _ => 1) continuous_const (HasCompactSupport.of_compactSpace _)
  simp only [integral_const, haar_real_univ_of_subsingleton (X := d.GmodAG),
    haar_real_univ_of_subsingleton (X := d.HmodAGH), smul_eq_mul, mul_one] at h
  exact h.symm

/-- **`J(f) = f(1)`** when `V` is a hyperbolic plane. -/
theorem distribJ_eq (hV : IsHypPlane d.QV) (χ : CentralCharOn d) {f : ↥d.G → ℂ}
    (hf : IsChiEquivariant d χ f) : distribJ d ψ f = f 1 := by
  unfold distribJ
  simp_rw [kernelK_eq ψ hV χ hf]
  rw [integral_const, weilMeasureHG_real_univ hV, one_smul]

theorem isThetaF_self (hV : IsHypPlane d.QV) {f : ↥d.G → ℂ} (hf : Continuous f) :
    IsThetaF d f f := by
  haveI := subsingleton_GmodAG hV
  refine ⟨hf.locallyIntegrable, hf.continuousOn, fun f' _ => ?_⟩
  rw [orbitalPairing, integral_of_subsingleton (Measure.haar : Measure d.GmodAG) _ 1,
    haar_real_univ_of_subsingleton, one_smul]
  congr 1
  funext g
  rw [G_comm hV _ g, inv_mul_cancel_right]

/-- **`θ_f = f`** when `V` is a hyperbolic plane (`G` commutative, `G/A_G` a point, `G_reg = G`). -/
theorem thetaF_eq (hV : IsHypPlane d.QV) {f : ↥d.G → ℂ} (hf : Continuous f) : thetaF d f = f := by
  have h1 := isThetaF_thetaF_of_exists d f ⟨f, isThetaF_self hV hf⟩
  have h2 := isThetaF_self hV hf
  haveI := totallyDisconnectedSpace_subgroup F d.ambient d.G
  have hae : thetaF d f =ᵐ[Measure.haar] f :=
    ae_eq_of_integral_testFunctions h1.1 h2.1 fun f' hf' => by rw [h1.2.2 f' hf', h2.2.2 f' hf']
  have hc : Continuous (thetaF d f) := by
    refine continuousOn_univ.mp ?_
    rw [← regularSet_eq_univ hV]
    exact h1.2.1
  exact (hc.ae_eq_iff_eq Measure.haar hf).mp hae

/-! #### The geometric side -/

theorem torusOf_eq_top (hV : IsHypPlane d.QV) (x : GSpin d.QW) : d.torusOf x = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ⟨?_, ?_⟩
  · exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]; exact gspinW_comm hV _ _
  · intro w _
    obtain ⟨c, rfl⟩ := gspinW_mem_range hV g
    rw [specP_scalarGSpin_eq_one]
    rfl

theorem subsingleton_torusQuot (hV : IsHypPlane d.QV) (T : Subgroup (GSpin d.QW)) :
    Subsingleton (d.TorusQuot T) :=
  ⟨fun x y => Quotient.inductionOn₂' x y fun _ _ =>
    QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr (gspinW_mem_range hV _))⟩

theorem isGammaElt (hV : IsHypPlane d.QV) (x : GSpin d.QW) : d.IsGammaElt x := by
  haveI := subsingleton_torusQuot hV (d.torusOf x)
  refine ⟨?_, fun a _ b _ => gspinW_comm hV a b, Finite.compactSpace⟩
  obtain ⟨c, hc⟩ := gspinW_scalar hV x
  rw [hc]
  exact isSS_of_aeval_eq_zero (p := X - C c) separable_X_sub_C.squarefree (by simp)

/-- The torus `GSpin(W) = F^×`. -/
def gammaTorus (hV : IsHypPlane d.QV) : d.GammaTorus :=
  ⟨⊤, 1, isGammaElt hV 1, torusOf_eq_top hV 1⟩

theorem gammaTorus_val (hV : IsHypPlane d.QV) (T : d.GammaTorus) : T.1 = ⊤ := by
  obtain ⟨x, -, hx⟩ := T.2
  rw [← hx, torusOf_eq_top hV]

theorem subsingleton_gammaClass (hV : IsHypPlane d.QV) : Subsingleton (GammaClass d) :=
  ⟨fun x y => Quot.inductionOn x fun a => Quot.inductionOn y fun b =>
    congrArg _ (Subtype.ext ((gammaTorus_val hV a).trans (gammaTorus_val hV b).symm))⟩

theorem weylCardOf_eq_one (hV : IsHypPlane d.QV) (T : Subgroup (GSpin d.QW)) :
    weylCardOf d T = 1 := by
  unfold weylCardOf
  have : Subsingleton (↥(Subgroup.normalizer (T : Set (GSpin d.QW))) ⧸
      (Subgroup.centralizer (T : Set (GSpin d.QW))).subgroupOf
        (Subgroup.normalizer (T : Set (GSpin d.QW)))) :=
    ⟨fun x y => Quotient.inductionOn₂' x y fun _ _ => QuotientGroup.eq.mpr
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_centralizer_iff.mpr fun _ _ =>
        gspinW_comm hV _ _))⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨this, ⟨1⟩⟩

/-- `Δ(t) = 1` (`P(t) = 1` on `W`, so `W''_t = 0`). -/
theorem deltaGGP_eq_one (hV : IsHypPlane d.QV) (t : GSpin d.QW) : deltaGGP d t = 1 := by
  obtain ⟨c, rfl⟩ := gspinW_mem_range hV t
  have hm : movedSub (scalarGSpin d.QW c) = ⊥ := by
    unfold movedSub
    rw [specP_scalarGSpin_eq_one]
    simp
  unfold deltaGGP
  haveI : Subsingleton ↥(movedSub (scalarGSpin d.QW c)) := by
    rw [hm]; infer_instance
  rw [LinearMap.det_eq_one_of_subsingleton, absF_one']

/-- `D^G(g) = 1` (`Ad g` is trivial on `𝔤`). -/
theorem weylDisc_eq_one (hV : IsHypPlane d.QV) (g : ↥d.G) :
    weylDisc d.lie (g : d.ambientˣ) = 1 := by
  have hconj : ∀ X ∈ d.lie, conjAd F (g : d.ambientˣ) X = X := fun X hX => by
    rw [conjAd_apply, comm_of_isEvenPair hV (isEvenPair_G g) (isEvenPair_lie hX), mul_assoc,
      Units.mul_inv, mul_one]
  have hst : ∀ X ∈ d.lie.toSubmodule, conjAd F (g : d.ambientˣ) X ∈ d.lie.toSubmodule :=
    fun X hX => by rw [hconj X hX]; exact hX
  unfold weylDisc
  rw [dite_eq_left_of_eq_true (eq_true hst)]
  have h0 : (conjAd F (g : d.ambientˣ)).toLinearEquiv.toLinearMap.restrict hst = 1 :=
    LinearMap.ext fun v => Subtype.ext (hconj (v : d.ambient) v.2)
  rw [h0, sub_self, LinearMap.charpoly_zero, Polynomial.trailingCoeff,
    Polynomial.natTrailingDegree_X_pow, Polynomial.coeff_X_pow_self, absF_one']

theorem exists_isSelfDual_lie : ∃ μ, IsSelfDual μ (restrictForm d.lie d.bilin) ψ := by
  haveI := t2Space_of_moduleTopology F d.ambient
  exact exists_isSelfDual_of_isInducing d.lie.incl.toLinearMap IsInducing.subtypeVal
    Subtype.val_injective _ (restrictForm_lie_nondegenerate _) ψ

theorem nilOrbit_eq_zero (hV : IsHypPlane d.QV) (Gx : Subgroup d.ambientˣ)
    (L : LieSubalgebra F d.ambient) (hL : L ≤ d.lie) (O : NilOrbit Gx L) :
    O = zeroOrbit Gx L := by
  induction O using Quotient.inductionOn with
  | h X =>
    obtain ⟨X, hXL, hn⟩ := X
    obtain rfl : X = 0 := eq_zero_of_isNilpotent hV (hL hXL) hn
    rfl

theorem mem_nilReg (hV : IsHypPlane d.QV) (Gx : Subgroup d.ambientˣ)
    (L : LieSubalgebra F d.ambient) (hL : L ≤ d.lie) (O : NilOrbit Gx L) : O ∈ NilReg Gx L := by
  refine ⟨(Quotient.out O).2.1, (Quotient.out O).2.2, ?_⟩
  have hc : ∀ X : ↥L, finrank F ↥(lieCentralizer L (X : d.ambient)) = finrank F ↥L :=
    fun X => by rw [lieCentralizer_eq hV hL (isEvenPair_lie (hL X.2))]
  rw [lieCentralizer_eq hV hL (isEvenPair_lie (hL (Quotient.out O).2.1))]
  unfold lieRank
  simp only [hc, ciInf_const]

/-- **The germ of a locally constant `θ`** at `x ∈ G(F)` is `θ(x)`: the only nilpotent orbit of
`𝔤_x = 𝔤` is `0`, it is regular, and `ĵ(0,·) = 1`. -/
theorem germ_eq (hV : IsHypPlane d.QV) {θ : ↥d.G → ℂ} (hθ : IsLocallyConstant θ) (x : ↥d.G)
    (O : NilOrbit (grpCentralizer d.G (x : d.ambientˣ))
      (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))) :
    germ d.G d.lie d.bilin ψ θ x O = θ x := by
  have hL : (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) ≤ d.lie := inf_le_left
  haveI : Subsingleton (NilOrbit (grpCentralizer d.G (x : d.ambientˣ))
      (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))) :=
    ⟨fun a b => (nilOrbit_eq_zero hV _ _ hL a).trans (nilOrbit_eq_zero hV _ _ hL b).symm⟩
  have hsd : ∃ μ, IsSelfDual μ (restrictForm (lieCentralizer d.lie
      ((x : d.ambientˣ) : d.ambient)) d.bilin) ψ := by
    rw [lieCentralizer_eq hV le_rfl (isEvenPair_G x)]
    exact exists_isSelfDual_lie ψ
  have hsum : ∀ (c : NilOrbit (grpCentralizer d.G (x : d.ambientˣ))
      (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) → ℂ) (X : d.ambient),
      X ∈ (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) →
      ∑ᶠ O', c O' * jHat (grpCentralizer d.G (x : d.ambientˣ))
        (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) d.bilin ψ O' X =
        c (zeroOrbit _ _) := by
    intro c X hX
    rw [finsum_eq_single _ (zeroOrbit _ _) (fun O' hO' => (hO' (Subsingleton.elim _ _)).elim),
      jHat_zeroOrbit_eq_one _ _ _ ψ hsd
        (fun Y => isRegularSS_of_isEvenPair hV hL (isEvenPair_lie (hL Y.2))) hX, mul_one]
  have huniq : ∀ c, HasGermExpansion d.G d.lie d.bilin ψ θ x c → c O = θ x := by
    rintro c ⟨-, ω, hω, hexp⟩
    have h0 := hexp 0 (mem_of_mem_nhds hω) (zero_mem _)
      (isRegularSS_of_isEvenPair hV hL (isEvenPair_lie (hL (zero_mem _)))) x
      (by rw [expA_zero, mul_one])
    rw [hsum c 0 (zero_mem _), ← Subsingleton.elim O (zeroOrbit _ _)] at h0
    exact h0.symm
  obtain ⟨ω, hω, hloc⟩ :=
    exists_nhds_zero_mul_expA (F := F) ((IsLocallyConstant.iff_eventually_eq _).mp hθ x)
  have hex : HasGermExpansion d.G d.lie d.bilin ψ θ x (fun _ => θ x) := by
    refine ⟨Set.toFinite _, ω, hω, fun X hXω hXL _ y hy => ?_⟩
    rw [hsum _ X hXL]
    exact hloc X hXω y hy
  have hE : ∃ c, HasGermExpansion d.G d.lie d.bilin ψ θ x c := ⟨_, hex⟩
  unfold germ
  rw [ite_eq_left_of_eq_true _ _ (eq_true (mem_nilReg hV _ _ hL O)),
    dite_eq_left_of_eq_true (eq_true hE)]
  exact huniq _ hE.choose_spec

/-- **`m_geom(θ) = θ(1)`** for `θ` locally constant and constant on `diag(GSpin(W)) = A_{G,H}`. -/
theorem mGeom_eq (hV : IsHypPlane d.QV) {θ : ↥d.G → ℂ} (hθ : IsLocallyConstant θ)
    (hθ1 : ∀ t : GSpin d.QW, θ (d.diag t) = θ 1) : mGeom ψ d θ = θ 1 := by
  haveI := subsingleton_gammaClass hV
  have hS : ∀ s, mGeomS ψ d θ s = θ 1 := by
    intro s
    unfold mGeomS
    have hsingle := tsum_eq_single (L := SummationFilter.unconditional (GammaClass d))
      (f := fun c : GammaClass d =>
      ((weylCard d c : ℂ))⁻¹ * torusIntegral ψ d θ (Quot.out c).1 s)
      (Quot.mk _ (gammaTorus hV) : GammaClass d) fun c hc => (hc (Subsingleton.elim _ _)).elim
    rw [hsingle, show weylCard d (Quot.mk _ (gammaTorus hV)) = 1 from weylCardOf_eq_one hV _,
      Nat.cast_one, inv_one, one_mul]
    unfold torusIntegral
    have hT : (Quot.out (Quot.mk _ (gammaTorus hV) : GammaClass d)).1 = ⊤ := gammaTorus_val hV _
    letI : MeasurableSpace (d.TorusQuot (Quot.out (Quot.mk _ (gammaTorus hV) : GammaClass d)).1) :=
      borel _
    haveI : BorelSpace (d.TorusQuot (Quot.out (Quot.mk _ (gammaTorus hV) : GammaClass d)).1) :=
      ⟨rfl⟩
    haveI := subsingleton_torusQuot hV (Quot.out (Quot.mk _ (gammaTorus hV) : GammaClass d)).1
    rw [integral_of_subsingleton _ _ 1, probHaar_real_univ, one_smul]
    unfold gammaIntegrand
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨isGammaElt hV _, by rw [torusOf_eq_top hV, hT]⟩),
      weylDisc_eq_one hV, germ_eq ψ hV hθ, deltaGGP_eq_one hV, hθ1, Real.sqrt_one, Real.one_rpow]
    simp
  unfold mGeom
  rw [show mGeomS ψ d θ = fun _ => θ 1 from funext hS]
  exact tendsto_const_nhds.limUnder_eq

theorem apply_diag (hV : IsHypPlane d.QV) (χ : CentralCharOn d) {f : ↥d.G → ℂ}
    (hf : IsChiEquivariant d χ f) (t : GSpin d.QW) : f (d.diag t) = f 1 := by
  obtain ⟨c, hc⟩ := gspinW_mem_range hV t
  exact apply_of_mem_AGH χ hf ⟨c, by rw [← hc]; rfl⟩

/-- **The geometric expansion `J(f) = m_geom(θ_f)` for every `f ∈ 𝒞_scusp`** when `V` is a
hyperbolic plane: `J(f) = f(1) = m_geom(θ_f)`. -/
theorem geomAt (hV : IsHypPlane d.QV) (χ : CentralCharOn d) :
    ∀ f ∈ ScuspTestFn d χ, distribJ d ψ f = mGeom ψ d (thetaF d f) := by
  intro f hf
  rw [distribJ_eq ψ hV χ hf.2.1, thetaF_eq hV hf.1.continuous]
  exact (mGeom_eq ψ hV hf.1 (apply_diag hV χ hf.2.1)).symm


end HypVAux


/-- **`geomAt_near` when `V` is a hyperbolic plane** (`dim W = 1`, `r = 0`).
Then `GSpin(W) = G_m` and `GSpin(V) ≅ G_m²` are commutative and split, so `A_G = G` and an
`A_G(F)`-stable `Ω ∋ 1` is all of `G(F)`: the statement is the full geometric expansion, which is
elementary here.  `H = A_{G,H}` (`N = 1` since `r = 0`), so `H\G/A_G` and `H/A_{G,H}` are points
and `J(f) = f(1)`; `G/A_G` is a point, so `θ_f = f`; `Γ(G,H)` is the class of `1` (the only torus
of `GSpin(W)` is the scalars) and `𝔤 = 𝔤_1` is abelian, so `m_geom(θ_f) = c_{θ_f,0}(1) = f(1)`
(`ĵ(0,·) = 1`).  This is the computation `toy_geomAt` (`Sanity/Witnesses.lean`)
for `dim W = 0`, `dim V = 1`, to be repeated for `dim W = 1`, `dim V = 2`.  The cited
Lie-algebra theorems are not used (and do not apply: `J^Lie` of Luo diverges here).
Status: proved, with `Ω = G(F)` (`HypVAux.geomAt`); the only axiom used is `exists_isSelfDual`
(a self-dual measure on `𝔤`, for `ĵ(0,·) = 1`). -/
theorem geomAt_near_of_isHypPlane_V (hV : IsHypPlane d.QV) (χ : CentralCharOn d) :
    ∃ Ω : Set ↥d.G, IsInvariantClopen d Ω ∧ (1 : ↥d.G) ∈ Ω ∧
      ∀ f ∈ ScuspTestFn d χ, Function.support f ⊆ Ω →
        distribJ d ψ f = mGeom ψ d (thetaF d f) :=
  ⟨Set.univ, isInvariantClopen_univ d, trivial, fun f hf _ => HypVAux.geomAt ψ hV χ f hf⟩

/-- **`geomAt_near` when `W` is a hyperbolic plane** (`dim V = 2r + 3`).  Then
`A_Ḡ = SO(W) ≅ G_m` is a nontrivial split central torus of `Ḡ = SO(W) × SO(V)`, and the
Lie-algebra half must be run for the special orthogonal triple modulo `A_Ḡ`: `𝔤⁰` is reductive
with centre `Lie(A_Ḡ) = so(W)`, and `H\G/A_G ≃ H̄\Ḡ/A_Ḡ` (`quotHG_equiv`).  Neither Luo (whose
`J^Lie` on `H̄\Ḡ` is `0` or divergent here, although his §6.3(2) treats `dim W = 2`) nor
Waldspurger 2010 (whose group is `SO(V)` alone, with `dim V ≥ 3`, and whose `I_N` formalism does
cover `d_W = 2` but is not the BP-form `J^Lie`) states the needed theorems in this form; the
natural citation is Beuzart-Plessis's general framework (Astérisque 418, Ch. 1–5, which allows a
nontrivial `A_G`) applied to the argument of BP Ch. 10–11 modulo `A_Ḡ`.
Status: SORRY (genuine gap in the cited literature's coverage). -/
theorem geomAt_near_of_isHypPlane_W (h : HYP ψ d) (hW : IsHypPlane d.QW) (χ : CentralCharOn d) :
    ∃ Ω : Set ↥d.G, IsInvariantClopen d Ω ∧ (1 : ↥d.G) ∈ Ω ∧
      ∀ f ∈ ScuspTestFn d χ, Function.support f ⊆ Ω →
        distribJ d ψ f = mGeom ψ d (thetaF d f) := by
  sorry

/-! ## Interface statement -/

/-- **The geometric expansion near `A_G(F)`** (Thesis Prop 12.4.1 and Thm 12.2.2, with
Prop 12.5.1 and the endgame of Thesis §12.5).
Assume (HYP).  For every central character `χ` there is an invariant clopen `Ω ∋ 1`
(`A_G(F)·exp(ω)` for a `G(F)`-excellent compact open `ω ∋ 0` in `𝔤(F)`) such that
`J(f) = m_geom(θ_f)` for every `f ∈ ScuspTestFn d χ` supported in `Ω`.

Derivation: for `f` supported in `Ω`, `J(f) = J^Lie((j_G^H)^{1/2} f_ω)` (Prop 12.4.1(i)), and
`J^Lie = J^Lie_geom` on `𝔤⁰` (Thm 12.2.2, from Prop 12.5.1, the spectral expansion of `J^Lie`
and the vanishing of the `c_O`), and `J^Lie_geom` corresponds to `m_geom` near `1`
(Prop 12.1.1(iii)).  Status: proved, by cases: `V` a hyperbolic plane
(`geomAt_near_of_isHypPlane_V`), `W` a hyperbolic plane (`geomAt_near_of_isHypPlane_W`), otherwise
`exists_lie_descent` and `distribJLie_eq_mGeomLie` (Prop 12.5.1 with Thesis Thm 11.6.1, and the endgame). -/
theorem geomAt_near (h : HYP ψ d) (χ : CentralCharOn d) :
    ∃ Ω : Set ↥d.G, IsInvariantClopen d Ω ∧ (1 : ↥d.G) ∈ Ω ∧
      ∀ f ∈ ScuspTestFn d χ, Function.support f ⊆ Ω →
        distribJ d ψ f = mGeom ψ d (thetaF d f) := by
  by_cases hV : IsHypPlane d.QV
  · exact geomAt_near_of_isHypPlane_V ψ d hV χ
  by_cases hW : IsHypPlane d.QW
  · exact geomAt_near_of_isHypPlane_W ψ d h hW χ
  obtain ⟨Ω, hΩ, h1, hdesc⟩ := exists_lie_descent ψ d hW hV χ
  refine ⟨Ω, hΩ, h1, fun f hf hs => ?_⟩
  obtain ⟨F', hF', hJ, hm⟩ := hdesc f hf hs
  rw [hJ, hm]
  exact distribJLie_eq_mGeomLie ψ d h hW hV hF'

end GSpinGGP
