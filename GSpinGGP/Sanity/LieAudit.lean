/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Sanity.Witnesses
import GSpinGGP.TraceFormula.Lie

/-!
# Consistency checks of the Lie-algebra axioms on small triples

The two axioms of `Literature/LieAlgebra.lean`
(`jLie_eq_of_thetaFLie_eqOn`, `lie_endgame`) are instantiated at the smallest triple
(`toyData`: `W = 0`, `V` a line) and at small triples with a hyperbolic-plane factor, and each
instance is checked to give no `False`.

* **`toyData`** (§1–§3).  Neither factor is a hyperbolic plane, so both axioms apply.  Here
  `𝔤⁰ = so(0) ⊕ so(1) = 0`, every Lie test function is strongly cuspidal (there is no proper
  parabolic), and we compute, *without the axioms*:
  `J^Lie(f) = f(0)` (`toyD_distribJLie`), `θ_f = f` (`toyD_thetaFLie`),
  `m^Lie_geom(θ) = θ(0)` (`toyD_mGeomLie`) and `c_{θ,0}(0) = θ(0)` (`toyD_germLie0`).
  Both axiom instances are then *proved* from these computations (`toyD_jLie_eq_of_thetaFLie_eqOn`,
  `toyD_lie_endgame`), so they are consistent there.  This is load-bearing: had any of the measures
  `measH0`, `measLie0`, `measLieTorus` been a junk value (`0`), or had `IsLieScusp` collapsed to
  `{0}`, the instance of `lie_endgame` at `toyData` would prove `False`.
* **Hyperbolic-plane triples** (§4): `hypVData` (`dim W = 1`, `r = 0`, `V` a hyperbolic plane) and
  `hypWData` (`W` a hyperbolic plane, `r = 0`), plain `def`s.  Both axioms carry the hypotheses
  `¬ IsHypPlane d.QW`, `¬ IsHypPlane d.QV`, which fail there (`hypVData_isHypPlane_QV`,
  `hypWData_isHypPlane_QW`): the instances are vacuous, and `geomAt_near` goes through
  `geomAt_near_of_isHypPlane_V` (proved, only axiom `exists_isSelfDual`) and the named `sorry`
  `geomAt_near_of_isHypPlane_W` instead.
-/

noncomputable section

open MeasureTheory Topology Filter Module

set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

namespace Sanity

section LieToy

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝕋" => (toyD (F := F))

/-! ## 1. The Lie algebra objects of the toy datum are zero-dimensional -/

theorem cliffTrace_algebraMap {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (Q : QuadraticForm F V) (a : F) :
    cliffTrace Q (algebraMap F _ a) = a * (finrank F (CliffordAlgebra Q) : F) := by
  rw [Algebra.algebraMap_eq_smul_one, cliffTrace_smul, cliffTrace_one]

/-- A scalar in `so(V)` is `0` (`tr(L_a) = a · dim C(V)` and `char F = 0`). -/
theorem eq_zero_of_algebraMap_mem_soSub {V : Type*} [AddCommGroup V] [Module F V]
    [Module.Finite F V] {Q : QuadraticForm F V} {a : F} (h : algebraMap F _ a ∈ soSub Q) :
    a = 0 := by
  have h2 := (mem_soSub.mp h).2
  rw [cliffTrace_algebraMap] at h2
  have hpos : 0 < finrank F (CliffordAlgebra Q) := Module.finrank_pos
  exact (mul_eq_zero.mp h2).resolve_right (Nat.cast_ne_zero.mpr hpos.ne')

/-- `so(W) = 0` for the toy datum (`W = 0`). -/
theorem toyD_soSub_W {X : CliffordAlgebra (𝕋).QW} (hX : X ∈ soSub (𝕋).QW) : X = 0 := by
  obtain ⟨a, rfl⟩ := toy_cliffW_scalar (K := F) X
  simp [eq_zero_of_algebraMap_mem_soSub hX]
  rfl

/-- `𝔤⁰ = 0` for the toy datum. -/
theorem toyD_lie0_eq_zero {X : (𝕋).ambient} (hX : X ∈ (𝕋).lie0) : X = 0 := by
  obtain ⟨a, b, rfl⟩ := toy_lie_scalar (K := F) ((𝕋).lie0_le_lie hX)
  rw [eq_zero_of_algebraMap_mem_soSub hX.1, eq_zero_of_algebraMap_mem_soSub hX.2, map_zero,
    map_zero]
  rfl

instance toyD_subsingleton_lieZero : Subsingleton ↥(𝕋).lieZero :=
  ⟨fun X Y => Subtype.ext ((toyD_lie0_eq_zero X.2).trans (toyD_lie0_eq_zero Y.2).symm)⟩

instance toyD_subsingleton_lieH0 : Subsingleton ↥(𝕋).lieH0 :=
  ⟨fun X Y => Subtype.ext ((toyD_lie0_eq_zero X.2.1).trans (toyD_lie0_eq_zero Y.2.1).symm)⟩

instance toyD_subsingleton_lieTorus (T : Subgroup (GSpin (𝕋).QW)) :
    Subsingleton ↥((𝕋).lieTorus T) :=
  ⟨fun X Y => Subtype.ext ((toyD_soSub_W X.2.1).trans (toyD_soSub_W Y.2.1).symm)⟩

instance toyD_subsingleton_lieCentralizer (X : (𝕋).ambient) :
    Subsingleton ↥(lieCentralizer (𝕋).lieZero X) :=
  ⟨fun Y Z => Subtype.ext ((toyD_lie0_eq_zero Y.2.1).trans (toyD_lie0_eq_zero Z.2.1).symm)⟩

/-- Every function on the zero space `𝔤⁰` is a test function. -/
theorem toyD_isTestFn (f : ↥(𝕋).lieZero → ℂ) : IsTestFn f :=
  ⟨IsLocallyConstant.of_constant f fun x y => congrArg f (Subsingleton.elim x y),
    IsCompact.of_isClosed_subset (Set.finite_univ.isCompact) (isClosed_tsupport _)
      (Set.subset_univ _)⟩

/-- **No proper parabolic for the toy datum**: every isotropic flag of `W = 0` or of the
anisotropic line `V` is `0`, so its stabilizer is everything. -/
theorem toyD_not_isProperFlagPair (FW : IsotropicFlag (𝕋).QW) (FV : IsotropicFlag (𝕋).QV) :
    ¬ (𝕋).IsProperFlagPair FW FV := by
  have hW : ∀ i, FW.sub i = ⊥ := fun i => Subsingleton.elim _ _
  have hV : ∀ i, FV.sub i = ⊥ := fun i => by
    refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
    have h0 := FV.isotropic i v hv
    rw [show (𝕋).QV v = v.2 0 * v.2 0 from toyData_QV_apply v, mul_self_eq_zero] at h0
    refine Prod.ext (Subsingleton.elim _ _) (funext fun j => ?_)
    obtain ⟨j, hj⟩ := j
    have hj0 : j = 0 := by change j < 2 * 0 + 1 at hj; omega
    subst hj0
    exact h0
  intro h
  apply h
  refine eq_top_iff.mpr fun g _ => ⟨fun i => ?_, fun i => ?_⟩
  · show ((FW.sub i).map _) = FW.sub i
    rw [hW i, Submodule.map_bot]
  · show ((FV.sub i).map _) = FV.sub i
    rw [hV i, Submodule.map_bot]

/-- **`S_scusp(𝔤⁰)` is everything for the toy datum** (non-vacuity of `IsLieScusp`). -/
theorem toyD_isLieScusp (f : ↥(𝕋).lieZero → ℂ) : (𝕋).IsLieScusp f :=
  ⟨toyD_isTestFn f, fun FW FV h => absurd h (toyD_not_isProperFlagPair FW FV)⟩

/-! ## 2. `J^Lie`, `θ_f`, germs and `m^Lie_geom` at the toy datum -/

variable (ψ : NontrivialAddChar F)

/-- The self-dual measure on `𝔤⁰ = 0` is `dirac 0`. -/
theorem toyD_measLie0 : (𝕋).measLie0 ψ = Measure.dirac 0 :=
  selfDualMeasure_eq_dirac_zero _ ψ

theorem toyD_measLie0_real_univ : ((𝕋).measLie0 ψ).real Set.univ = 1 := by
  rw [toyD_measLie0]; simp

/-- `dirac 0` is the `exp`-compatible measure on `𝔥⁰ = 0` (`exp 0 = 1`, `H/A_{G,H}` a point of
Haar mass `1`). -/
theorem toyD_isExpCompatH_dirac : (𝕋).IsExpCompatH (Measure.dirac 0) := by
  refine ⟨isAddHaarMeasure_dirac_zero, Set.univ, Filter.univ_mem, fun S _ _ => ?_⟩
  rcases S.eq_empty_or_nonempty with hS | ⟨x, hx⟩
  · subst hS
    simp
  · have hS : S = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
    subst hS
    have hset : {q : (𝕋).HmodAGH | ∃ X ∈ (Set.univ : Set ↥(𝕋).lieH0), ∃ h : ↥(𝕋).H,
        (((h : ↥(𝕋).G) : (𝕋).ambientˣ) : (𝕋).ambient) = expA F ((X : (𝕋).ambient)) ∧
          q = (h : (𝕋).HmodAGH)} = Set.univ := by
      refine Set.eq_univ_of_forall fun q => ⟨0, Set.mem_univ _, 1, ?_, Subsingleton.elim _ _⟩
      simp [expA_zero]
    rw [hset, haar_univ_of_subsingleton]
    simp

/-- Any `exp`-compatible measure on `𝔥⁰ = 0` has mass `1`. -/
theorem toyD_measH0_eq : (𝕋).measH0 = Measure.dirac 0 := by
  have h : ∃ μ, (𝕋).IsExpCompatH μ := ⟨_, toyD_isExpCompatH_dirac⟩
  have hμ : (𝕋).IsExpCompatH (𝕋).measH0 := by
    unfold GGPData.measH0
    rw [dite_eq_left_of_eq_true (eq_true h)]
    exact h.choose_spec
  obtain ⟨-, U, hU, hS⟩ := hμ
  have hUu : U = Set.univ :=
    Set.eq_univ_of_forall fun y => Subsingleton.elim (0 : ↥(𝕋).lieH0) y ▸ mem_of_mem_nhds hU
  obtain ⟨-, U', hU', hS'⟩ := toyD_isExpCompatH_dirac (F := F)
  have hU'u : U' = Set.univ :=
    Set.eq_univ_of_forall fun y => Subsingleton.elim (0 : ↥(𝕋).lieH0) y ▸ mem_of_mem_nhds hU'
  ext s hs
  rcases s.eq_empty_or_nonempty with h' | ⟨x, hx⟩
  · simp [h']
  · have : s = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
    subst this
    rw [hS _ MeasurableSet.univ hUu.symm.subset, hS' _ MeasurableSet.univ hU'u.symm.subset]

/-- `λ = 0` on `𝔥⁰` for `r = 0`, so `ξ = 1`. -/
theorem toyD_xiLie (X : (𝕋).ambient) : (𝕋).xiLie ψ X = 1 := by
  haveI : IsEmpty (Fin (𝕋).r) := show IsEmpty (Fin 0) from inferInstance
  simp only [GGPData.xiLie, GGPData.lamLie]
  rw [Finset.univ_eq_empty, Finset.sum_empty]
  exact nontrivialAddChar_zero ψ

/-- `K^Lie(f, x) = f(0)`. -/
theorem toyD_kernelLie (f : ↥(𝕋).lieZero → ℂ) (x : ↥(𝕋).G) :
    (𝕋).kernelLie ψ f x = f 0 := by
  unfold GGPData.kernelLie
  rw [toyD_measH0_eq, integral_of_subsingleton _ _ 0, toyD_xiLie]
  simp [Subsingleton.elim ((𝕋).adLie0 x⁻¹ ((𝕋).lieH0Incl 0)) 0]

/-- **`J^Lie(f) = f(0)` for the toy datum.** -/
theorem toyD_distribJLie (f : ↥(𝕋).lieZero → ℂ) : (𝕋).distribJLie ψ f = f 0 := by
  unfold GGPData.distribJLie
  simp_rw [toyD_kernelLie]
  rw [integral_const, toy_weilMeasureHG_real_univ, one_smul]

/-- Every `f` represents its own orbital pairing on `𝔤⁰ = 0`. -/
theorem toyD_isThetaFLie (f : ↥(𝕋).lieZero → ℂ) : (𝕋).IsThetaFLie ψ f f := by
  have hc : Continuous f := continuous_of_const fun x y => congrArg f (Subsingleton.elim x y)
  rw [GGPData.IsThetaFLie, toyD_measLie0]
  refine ⟨hc.locallyIntegrable, hc.continuousOn, fun f' _ => ?_⟩
  rw [GGPData.orbitalPairingLie, integral_of_subsingleton (Measure.haar : Measure (𝕋).GmodAG) _ 1,
    haar_real_univ_of_subsingleton, one_smul, toyD_measLie0]
  congr 1
  funext X
  rw [Subsingleton.elim ((𝕋).adLie0 _ X) X]

/-- **`θ_f = f` for the toy datum.** -/
theorem toyD_thetaFLie (f : ↥(𝕋).lieZero → ℂ) : (𝕋).thetaFLie ψ f = f := by
  have h1 := (𝕋).isThetaFLie_thetaFLie_of_exists ψ ⟨f, toyD_isThetaFLie ψ f⟩
  have h2 := toyD_isThetaFLie ψ f
  have e := (h1.2.2 (fun _ => 1) (toyD_isTestFn _)).trans (h2.2.2 (fun _ => 1) (toyD_isTestFn _)).symm
  rw [toyD_measLie0, integral_of_subsingleton _ _ 0, integral_of_subsingleton _ _ 0] at e
  simp only [mul_one, smul_eq_mul] at e
  have e' : (𝕋).thetaFLie ψ f 0 = f 0 := by simpa using e
  funext X
  rw [Subsingleton.elim X 0, e']

/-- **The germ at `0` of any function on `𝔤⁰ = 0` is its value** (the only nilpotent orbit is
`0`, it is regular, and `ĵ(0, ·) = 1`). -/
theorem toyD_germLie0 (θ : ↥(𝕋).lieZero → ℂ) {X : (𝕋).ambient} (hX : X = 0)
    (O : NilOrbit (lieGrpCentralizer (𝕋).G X) (lieCentralizer (𝕋).lieZero X)) :
    (𝕋).germLie0 ψ θ X O = θ 0 := by
  subst hX
  have hL : lieCentralizer (𝕋).lieZero (0 : (𝕋).ambient) ≤ (𝕋).lie :=
    fun Y hY => (𝕋).lieZero_le_lie hY.1
  haveI : Subsingleton (NilOrbit (lieGrpCentralizer (𝕋).G (0 : (𝕋).ambient))
      (lieCentralizer (𝕋).lieZero (0 : (𝕋).ambient))) :=
    ⟨fun a b => (toyD_nilOrbit_eq_zero _ _ hL a).trans (toyD_nilOrbit_eq_zero _ _ hL b).symm⟩
  have hsd : ∃ μ, IsSelfDual μ
      (restrictForm (lieCentralizer (𝕋).lieZero (0 : (𝕋).ambient)) (𝕋).bilin) ψ :=
    ⟨_, isSelfDual_dirac_zero _ ψ⟩
  have hsum : ∀ (c : NilOrbit (lieGrpCentralizer (𝕋).G (0 : (𝕋).ambient))
      (lieCentralizer (𝕋).lieZero (0 : (𝕋).ambient)) → ℂ) (Y : (𝕋).ambient),
      Y ∈ lieCentralizer (𝕋).lieZero (0 : (𝕋).ambient) →
      ∑ᶠ O', c O' * jHat (lieGrpCentralizer (𝕋).G (0 : (𝕋).ambient))
        (lieCentralizer (𝕋).lieZero (0 : (𝕋).ambient)) (𝕋).bilin ψ O' Y =
        c (zeroOrbit _ _) := by
    intro c Y hY
    rw [finsum_eq_single _ (zeroOrbit _ _) (fun O' hO' => (hO' (Subsingleton.elim _ _)).elim),
      jHat_zeroOrbit_eq_one _ _ _ ψ hsd (toyD_isRegularSS _ hL) hY, mul_one]
  have huniq : ∀ c, HasGermExpansionLie (𝕋).G (𝕋).lieZero (𝕋).bilin ψ θ 0 c → c O = θ 0 := by
    rintro c ⟨-, ω, hω, hexp⟩
    have h0 := hexp 0 (mem_of_mem_nhds hω) (zero_mem _) (toyD_isRegularSS _ hL 0) 0 (by simp)
    rw [hsum c 0 (zero_mem _), ← Subsingleton.elim O (zeroOrbit _ _)] at h0
    exact h0.symm
  have hex : HasGermExpansionLie (𝕋).G (𝕋).lieZero (𝕋).bilin ψ θ 0 (fun _ => θ 0) := by
    refine ⟨Set.toFinite _, Set.univ, Filter.univ_mem, fun Y _ hY _ Z _ => ?_⟩
    rw [hsum _ Y hY, Subsingleton.elim Z 0]
  have hE : ∃ c, HasGermExpansionLie (𝕋).G (𝕋).lieZero (𝕋).bilin ψ θ 0 c := ⟨_, hex⟩
  unfold GGPData.germLie0 germLie
  rw [ite_cond_eq_true _ _ (eq_true (toyD_mem_nilReg _ _ O)),
    dite_eq_left_of_eq_true (eq_true hE)]
  exact huniq _ hE.choose_spec

/-- `dirac 0` is the `exp`-compatible measure on `𝔱⁰ = 0`. -/
theorem toyD_isExpCompatT_dirac (T : Subgroup (GSpin (𝕋).QW)) :
    (𝕋).IsExpCompatT T (Measure.dirac 0) := by
  letI : MeasurableSpace ((𝕋).TorusQuot T) := borel _
  haveI : BorelSpace ((𝕋).TorusQuot T) := ⟨rfl⟩
  refine ⟨isAddHaarMeasure_dirac_zero, Set.univ, Filter.univ_mem, fun S _ _ => ?_⟩
  rcases S.eq_empty_or_nonempty with hS | ⟨x, hx⟩
  · subst hS
    simp
  · have hS : S = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
    subst hS
    have hset : {q : (𝕋).TorusQuot T | ∃ X ∈ (Set.univ : Set ↥((𝕋).lieTorus T)), ∃ t : ↥T,
        (((t : GSpin (𝕋).QW) : (CliffordAlgebra (𝕋).QW)ˣ) : CliffordAlgebra (𝕋).QW) =
          expA F (X : CliffordAlgebra (𝕋).QW) ∧ q = (t : (𝕋).TorusQuot T)} = Set.univ := by
      refine Set.eq_univ_of_forall fun q => ⟨0, Set.mem_univ _, 1, ?_, Subsingleton.elim _ _⟩
      simp [expA_zero]
    rw [hset]
    have h1 := probHaar_real_univ ((𝕋).TorusQuot T)
    rw [measureReal_def] at h1
    have hne : probHaar ((𝕋).TorusQuot T) Set.univ ≠ ⊤ := by
      intro htop; rw [htop] at h1; simp at h1
    rw [← ENNReal.ofReal_toReal hne, h1]
    simp

theorem toyD_measLieTorus_eq (T : Subgroup (GSpin (𝕋).QW)) :
    (𝕋).measLieTorus T = Measure.dirac 0 := by
  have h : ∃ μ, (𝕋).IsExpCompatT T μ := ⟨_, toyD_isExpCompatT_dirac T⟩
  have hμ : (𝕋).IsExpCompatT T ((𝕋).measLieTorus T) := by
    unfold GGPData.measLieTorus
    rw [dite_eq_left_of_eq_true (eq_true h)]
    exact h.choose_spec
  obtain ⟨-, U, hU, hS⟩ := hμ
  have hUu : U = Set.univ := Set.eq_univ_of_forall fun y =>
    Subsingleton.elim (0 : ↥((𝕋).lieTorus T)) y ▸ mem_of_mem_nhds hU
  obtain ⟨-, U', hU', hS'⟩ := toyD_isExpCompatT_dirac (F := F) T
  have hU'u : U' = Set.univ := Set.eq_univ_of_forall fun y =>
    Subsingleton.elim (0 : ↥((𝕋).lieTorus T)) y ▸ mem_of_mem_nhds hU'
  ext s hs
  rcases s.eq_empty_or_nonempty with h' | ⟨x, hx⟩
  · simp [h']
  · have : s = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
    subst this
    rw [hS _ MeasurableSet.univ hUu.symm.subset, hS' _ MeasurableSet.univ hU'u.symm.subset]

/-- `0 ∈ 𝔱⁰_♮` for every `T` (`W = 0`). -/
theorem toyD_isGammaEltLie_zero (T : Subgroup (GSpin (𝕋).QW)) : (𝕋).IsGammaEltLie T 0 :=
  ⟨zero_mem _, Subsingleton.elim _ _, fun Y hY _ _ => by
    rw [toyD_soSub_W hY]; exact zero_mem _⟩

/-- `D^G = 1` on the zero space `𝔤⁰`. -/
theorem toyD_weylDiscLie (X : (𝕋).ambient) : weylDiscLie (𝕋).lieZero X = 1 := by
  have hst : ∀ Y ∈ (𝕋).lieZero.toSubmodule,
      (LinearMap.mulLeft F X - LinearMap.mulRight F X) Y ∈ (𝕋).lieZero.toSubmodule :=
    fun Y _ => by
      simp only [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        toyD_ambient_comm X Y, sub_self]
      exact zero_mem _
  haveI : Subsingleton ↥(𝕋).lieZero.toSubmodule :=
    ⟨fun a b => Subtype.ext ((toyD_lie0_eq_zero a.2).trans (toyD_lie0_eq_zero b.2).symm)⟩
  unfold weylDiscLie
  rw [dite_eq_left_of_eq_true (eq_true hst)]
  have h0 : (LinearMap.mulLeft F X - LinearMap.mulRight F X).restrict hst = 0 :=
    LinearMap.ext fun v => Subsingleton.elim (α := ↥(𝕋).lieZero.toSubmodule) _ _
  rw [h0, LinearMap.charpoly_zero, Polynomial.trailingCoeff, Polynomial.natTrailingDegree_X_pow,
    Polynomial.coeff_X_pow_self, absF_one']

theorem toyD_deltaLie (X : CliffordAlgebra (𝕋).QW) : (𝕋).deltaLie X = 1 := by
  unfold GGPData.deltaLie
  rw [LinearMap.det_eq_one_of_subsingleton, absF_one']

theorem toyD_diagLie_zero : (𝕋).diagLie 0 = 0 := by
  simp [GGPData.diagLie]

/-- **`m^Lie_geom(θ) = θ(0)` for the toy datum** (one torus, `𝔱⁰ = 0` an atom of mass `1`,
`|W(T)| = 1`, `D^G = Δ = 1`, germ `θ(0)`). -/
theorem toyD_mGeomLie (θ : ↥(𝕋).lieZero → ℂ) : (𝕋).mGeomLie ψ θ = θ 0 := by
  have hS : ∀ s, (𝕋).mGeomLieS ψ θ s = θ 0 := by
    intro s
    unfold GGPData.mGeomLieS
    have hsingle := tsum_eq_single (L := SummationFilter.unconditional (GammaClass (𝕋)))
      (f := fun c : GammaClass (𝕋) =>
        ((weylCard (𝕋) c : ℂ))⁻¹ * (𝕋).torusIntegralLie ψ θ (Quot.out c).1 s)
      (toyD_gammaClass (F := F)) fun c hc => (hc (Subsingleton.elim _ _)).elim
    rw [hsingle, show weylCard (𝕋) (toyD_gammaClass (F := F)) = 1 from toyD_weylCardOf _,
      Nat.cast_one, inv_one, one_mul]
    unfold GGPData.torusIntegralLie
    rw [toyD_measLieTorus_eq, integral_of_subsingleton _ _ 0]
    simp only [measureReal_def, Measure.dirac_apply_of_mem (Set.mem_univ _), ENNReal.toReal_one,
      one_smul]
    unfold GGPData.gammaIntegrandLie
    rw [if_pos (by simpa using toyD_isGammaEltLie_zero _), toyD_weylDiscLie, toyD_deltaLie,
      toyD_germLie0 ψ θ (by simpa using toyD_diagLie_zero)]
    simp
  unfold GGPData.mGeomLie
  rw [show (𝕋).mGeomLieS ψ θ = fun _ => θ 0 from funext hS]
  exact tendsto_const_nhds.limUnder_eq

/-! ## 3. The two axioms at the toy datum, proved without them -/

/-- The toy datum has no hyperbolic-plane factor: both axioms apply to it. -/
theorem toyD_not_isHypPlane_QW : ¬ IsHypPlane (𝕋).QW := fun h => by
  have := h.1
  simp only [Module.finrank_fin_fun] at this
  rw [show (𝕋).m = 0 from rfl] at this
  exact absurd this (by norm_num)

theorem toyD_not_isHypPlane_QV : ¬ IsHypPlane (𝕋).QV := fun h => by
  have := h.2.2
  have h0 : wittIndex (𝕋).QV = 0 := toyData_wittIndex_QV
  rw [h0] at this
  exact zero_ne_one this

/-- **`jLie_eq_of_thetaFLie_eqOn` holds at the toy datum** (proved without the axiom). -/
theorem toyD_jLie_eq_of_thetaFLie_eqOn {f f' θ θ' : ↥(𝕋).lieZero → ℂ}
    (hθ : (𝕋).IsThetaFLie ψ f θ) (hθ' : (𝕋).IsThetaFLie ψ f' θ')
    (he : ∀ X : ↥(𝕋).lieZero, IsRegularSS (𝕋).lieZero (X : (𝕋).ambient) → θ X = θ' X) :
    (𝕋).distribJLie ψ f = (𝕋).distribJLie ψ f' := by
  -- `θ(0) = f(0)` from the defining identity with `f' = 1`
  have key : ∀ {g φ : ↥(𝕋).lieZero → ℂ}, (𝕋).IsThetaFLie ψ g φ → φ 0 = g 0 := by
    intro g φ hφ
    have e := (hφ.2.2 (fun _ => 1) (toyD_isTestFn _)).trans
      ((toyD_isThetaFLie ψ g).2.2 (fun _ => 1) (toyD_isTestFn _)).symm
    rw [toyD_measLie0, integral_of_subsingleton _ _ 0, integral_of_subsingleton _ _ 0] at e
    simpa using e
  have hreg : IsRegularSS (𝕋).lieZero ((0 : ↥(𝕋).lieZero) : (𝕋).ambient) :=
    toyD_isRegularSS _ (𝕋).lieZero_le_lie 0
  rw [toyD_distribJLie, toyD_distribJLie, ← key hθ, ← key hθ', he 0 hreg]

/-- **`lie_endgame` holds at the toy datum** (proved without the axiom): with `f = 1`,
`J^Lie(1) − m^Lie_geom(θ_1) = 1 − 1 = 0 = c_0 · c_{θ_1,0}(0) = c_0`. -/
theorem toyD_lie_endgame
    (c : NilOrbit (lieGrpCentralizer (𝕋).G 0) (lieCentralizer (𝕋).lieZero 0) → ℂ)
    (h : ∀ f : ↥(𝕋).lieZero → ℂ, (𝕋).IsLieScusp f →
      (𝕋).distribJLie ψ f - (𝕋).mGeomLie ψ ((𝕋).thetaFLie ψ f) =
        ∑ᶠ O ∈ NilReg (lieGrpCentralizer (𝕋).G 0) (lieCentralizer (𝕋).lieZero 0),
          c O * (𝕋).germLie0 ψ ((𝕋).thetaFLie ψ f) 0 O) :
    ∀ O ∈ NilReg (lieGrpCentralizer (𝕋).G 0) (lieCentralizer (𝕋).lieZero 0), c O = 0 := by
  intro O hO
  have hL : lieCentralizer (𝕋).lieZero (0 : (𝕋).ambient) ≤ (𝕋).lie :=
    fun Y hY => (𝕋).lieZero_le_lie hY.1
  haveI : Subsingleton (NilOrbit (lieGrpCentralizer (𝕋).G 0) (lieCentralizer (𝕋).lieZero 0)) :=
    ⟨fun a b => (toyD_nilOrbit_eq_zero _ _ hL a).trans (toyD_nilOrbit_eq_zero _ _ hL b).symm⟩
  have h1 := h (fun _ => 1) (toyD_isLieScusp _)
  rw [toyD_distribJLie, toyD_thetaFLie, toyD_mGeomLie, sub_self] at h1
  have hset : NilReg (lieGrpCentralizer (𝕋).G 0) (lieCentralizer (𝕋).lieZero 0) = {O} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨hO, fun O' _ => Subsingleton.elim _ _⟩
  have hs : ∑ᶠ O' ∈ NilReg (lieGrpCentralizer (𝕋).G 0) (lieCentralizer (𝕋).lieZero 0),
      c O' * (𝕋).germLie0 ψ (fun _ => (1 : ℂ)) 0 O' = c O := by
    rw [hset, finsum_mem_singleton, toyD_germLie0 ψ _ rfl, mul_one]
  rw [hs] at h1
  exact h1.symm

/-- The axiom instances at the toy datum (for `#print axioms`: they use the axioms, while the
two theorems above show the same statements without them). -/
example (c : NilOrbit (lieGrpCentralizer (𝕋).G 0) (lieCentralizer (𝕋).lieZero 0) → ℂ) :=
  lie_endgame (𝕋) ψ toyD_not_isHypPlane_QW toyD_not_isHypPlane_QV c

example {f f' θ θ' : ↥(𝕋).lieZero → ℂ} :=
  @jLie_eq_of_thetaFLie_eqOn F _ _ (𝕋) ψ toyD_not_isHypPlane_QW toyD_not_isHypPlane_QV f f' θ θ'

end LieToy

/-! ## 4. Triples with a hyperbolic-plane factor -/

section HypTriples

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- A nondegenerate plane with a nonzero isotropic vector has Witt index `1`. -/
theorem wittIndex_eq_one_of_isotropic {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {Q : QuadraticForm F V} (hdim : finrank F V = 2) (hnd : IsNondeg Q)
    {v : V} (hv0 : v ≠ 0) (hv : Q v = 0) : wittIndex Q = 1 := by
  unfold wittIndex
  apply IsGreatest.csSup_eq
  refine ⟨⟨Submodule.span F {v}, fun u hu => ?_, finrank_span_singleton hv0⟩, ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [QuadraticMap.map_smul, hv, smul_zero]
  · rintro n ⟨U, hU, rfl⟩
    by_contra hlt
    push_neg at hlt
    have h2 : finrank F U = finrank F V :=
      le_antisymm (Submodule.finrank_le U) (hdim ▸ hlt)
    have htop : U = ⊤ := Submodule.eq_top_of_finrank_eq h2
    have hQ : ∀ w, Q w = 0 := fun w => hU w (htop ▸ Submodule.mem_top)
    have hb : ∀ y, bform Q v y = 0 := fun y => by
      simp [bform, QuadraticMap.associated_apply, hQ]
    exact hv0 ((isNondeg_iff Q).mp hnd v hb)

/-- **`V` a hyperbolic plane**: `W = ⟨w⟩` with `q(w) = −1`, `r = 0`, `ν = 1`, so
`V = W ⊕ ⟨z₀⟩` has form `−x² + y²` (plain `def`). -/
def hypVData : GGPData F where
  m := 2 * 0 + 1
  QW := splitOddForm 0 (-1 : F)
  nondeg := isNondeg_splitOddForm 0 (neg_ne_zero.mpr one_ne_zero)
  r := 0
  ν := 1

theorem hypVData_isHypPlane_QV : IsHypPlane (hypVData (F := F)).QV := by
  have hdim : finrank F (hypVData (F := F)).V = 2 := by
    show finrank F ((Fin (2 * 0 + 1) → F) × (Fin (2 * 0 + 1) → F)) = 2
    simp
  refine ⟨hdim, (hypVData (F := F)).nondeg_QV, ?_⟩
  · refine wittIndex_eq_one_of_isotropic hdim (hypVData (F := F)).nondeg_QV
      (v := ((fun _ => 1), (fun _ => 1))) (fun h => by
        have := congrArg (fun p : (hypVData (F := F)).V => p.2 ⟨0, Nat.succ_pos _⟩) h
        simp at this) ?_
    show splitOddForm 0 (-1 : F) (fun _ => 1) + splitOddForm 0 ((1 : Fˣ) : F) (fun _ => 1) = 0
    rw [splitOddForm_zero_apply, splitOddForm_zero_apply]
    simp

theorem hypForm_one_apply (x : Fin (2 * 1) → F) : hypForm F 1 x = 2 * (x 0 * x 1) := by
  simp [hypForm, hypMatrix, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply', dotProduct,
    Matrix.mulVec, Fin.sum_univ_two]
  ring

theorem isNondeg_hypForm_one : IsNondeg (hypForm F 1) := by
  rw [isNondeg_iff]
  intro x hx
  have hp : ∀ y, QuadraticMap.polar (hypForm F 1) x y = 2 * (x 0 * y 1 + x 1 * y 0) := by
    intro y
    simp only [QuadraticMap.polar, hypForm_one_apply, Pi.add_apply]
    ring
  have hb : ∀ y : Fin (2 * 1) → F, x 0 * y 1 + x 1 * y 0 = 0 := fun y => by
    have h2 := congrArg (fun B => B x y) (QuadraticMap.two_nsmul_associated F (hypForm F 1))
    simp only [LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply] at h2
    have h0 : QuadraticMap.associated (hypForm F 1) x y = 0 := hx y
    rw [h0, smul_zero, hp] at h2
    exact (mul_eq_zero.mp h2.symm).resolve_left two_ne_zero
  have h0 := hb (Pi.single 1 1)
  have h1 := hb (Pi.single 0 1)
  simp at h0 h1
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1

/-- **`W` a hyperbolic plane**: `W = H` (form `2xy`), `r = 0`, `ν = 1`, so `dim V = 3`
(plain `def`). -/
def hypWData : GGPData F where
  m := 2 * 1
  QW := hypForm F 1
  nondeg := isNondeg_hypForm_one
  r := 0
  ν := 1

theorem hypWData_isHypPlane_QW : IsHypPlane (hypWData (F := F)).QW := by
  have hdim : finrank F (Fin (hypWData (F := F)).m → F) = 2 := Module.finrank_fin_fun F
  refine ⟨hdim, isNondeg_hypForm_one, ?_⟩
  refine wittIndex_eq_one_of_isotropic hdim isNondeg_hypForm_one
    (v := (Pi.single (⟨0, by decide⟩ : Fin (2 * 1)) (1 : F) : Fin (2 * 1) → F)) (fun h => by
      have := congrFun h ⟨0, by decide⟩
      simp only [Pi.single_eq_same] at this
      exact one_ne_zero this) ?_
  show hypForm F 1 _ = 0
  rw [hypForm_one_apply]
  simp

/-- **The axioms are vacuous at `hypVData`**: their hypothesis `¬ IsHypPlane QV` fails.
`geomAt_near` for it is `geomAt_near_of_isHypPlane_V` (proved with `Ω = G(F)`, only axiom
`exists_isSelfDual`). -/
theorem hypVData_axioms_vacuous : ¬ ¬ IsHypPlane (hypVData (F := F)).QV :=
  not_not_intro hypVData_isHypPlane_QV

/-- **The axioms are vacuous at `hypWData`**: their hypothesis `¬ IsHypPlane QW` fails.
`geomAt_near` for it is `geomAt_near_of_isHypPlane_W` (a named `sorry`). -/
theorem hypWData_axioms_vacuous : ¬ ¬ IsHypPlane (hypWData (F := F)).QW :=
  not_not_intro hypWData_isHypPlane_QW

end HypTriples

end Sanity

end GSpinGGP
