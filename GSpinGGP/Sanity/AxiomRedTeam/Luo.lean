/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Sanity.Witnesses
import GSpinGGP.Literature.Luo
import GSpinGGP.TraceFormula.LuoTransfer
import GSpinGGP.Sanity.AxiomRedTeam.HarishChandra

/-!
# Checks of `luo_lie_geomExpansion_SO` and `germLie_unique_SO` on the smallest Luo datum

The Luo datum `L0 = toyD.luoOf`: `W = 0`, `V` a line, so `SO(V) = 1`, `so(V) = 0`, `Ḡ = H̄ = 1`,
`𝔤 = 𝔥 = 0`, the only `Γ`-torus is trivial and the only nilpotent orbit is `0`.  Without the axiom,
for every `ψ`, every choice of Haar measures, exponential-compatible measures, Weil measure and
every `f`, the conclusion holds with `θ ≡ μ_Ḡ(Ḡ) f(0)` (`luo_conclusion_L0`): both
`J^Lie(f)` and `m^Lie_{geom,s}(θ)` equal `μ_Ḡ(Ḡ) f(0)`.  This checks that the normalizations of
`distribJLie`, `orbitalPairing`, `mGeomLieS` (Weyl group order, measures on tori, `Δ`, `c_θ`) agree
in the degenerate case.

`germLie_unique_SO` (Lie germ uniqueness): verified at `L0` for every `θ` (`L0_germLie_unique`,
from `L0_coeff_eq`: every expansion has coefficient `θ(0)`), with satisfiable hypotheses
(`L0_hasGermExpansionLie`).  The hypothesis `X ∈ 𝔤` is needed: at `X = 1 ∉ 𝔤` every `c` is an
expansion of `θ = 0`, and the statement without it proves `False`
(`L0_germLie_unique_needs_mem_lie`).  Two consequences of the axiom on any Luo datum: distinct
orbits, one regular, have distinct orbit measures (`false_of_orbitMeasure_eq_lie`), and `ĵ(O, ·)`
is not eventually `0` near `0` on regular elements for `O` regular
(`germLie_unique_SO_forces_jHat_ne_zero`), so an orbit measure of `O` in the sense of
`IsOrbitMeasure` exists.

Not covered: any datum with a nontrivial torus or a nonzero nilpotent orbit.
-/

noncomputable section
open MeasureTheory Topology Filter Module
attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace GSpinGGP.AxiomRedTeam
open GSpinGGP GSpinGGP.Sanity GSpinGGP.LuoDatum
variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- The Luo datum with `W = 0`, `V = D` a line (`m = 0`, `r = 0`). -/
abbrev L0 : LuoDatum F := (toyD (F := F)).luoOf

instance : Subsingleton (L0 (F := F)).W := inferInstanceAs (Subsingleton (Fin 0 → F))

instance : Subsingleton (Module.End F (L0 (F := F)).W) :=
  ⟨fun _ _ => LinearMap.ext fun _ => Subsingleton.elim _ _⟩

theorem L0_QV_apply (v : (L0 (F := F)).V) : (L0 (F := F)).QV v = v.2 0 * v.2 0 :=
  toyData_QV_apply (K := F) v

def e0 : (L0 (F := F)).V := (0, fun _ => 1)

theorem L0_line (v : (L0 (F := F)).V) : v = v.2 0 • (e0 (F := F)) :=
  Prod.ext (Subsingleton.elim _ _) (funext fun i => by
    rw [fin_eq_zero_of rfl i]; exact (mul_one _).symm)

theorem L0_finrank_V : finrank F (L0 (F := F)).V = 1 := by
  show finrank F ((Fin 0 → F) × (Fin (2 * 0 + 1) → F)) = 1
  simp

/-- Every endomorphism of `V` is a scalar. -/
theorem L0_end_eq_smul (g : Module.End F (L0 (F := F)).V) :
    g = ((g e0).2 0) • (1 : Module.End F (L0 (F := F)).V) := by
  apply LinearMap.ext; intro v
  rw [L0_line (F := F) v, map_smul, L0_line (F := F) (g e0)]
  have : (e0 (F := F)).2 0 = 1 := rfl
  simp [smul_smul, mul_comm, this]

theorem L0_SO_trivial {g : (Module.End F (L0 (F := F)).V)ˣ} (hg : g ∈ SOu (L0 (F := F)).QV) :
    (g : Module.End F (L0 (F := F)).V) = 1 := by
  obtain ⟨_, hdet⟩ := hg
  have h := L0_end_eq_smul (F := F) (g : Module.End F (L0 (F := F)).V)
  set c := ((g : Module.End F (L0 (F := F)).V) e0).2 0
  have hdet' : LinearMap.det (g : Module.End F (L0 (F := F)).V) = 1 := hdet
  rw [h, LinearMap.det_smul, map_one, L0_finrank_V, pow_one, mul_one] at hdet'
  rw [h, hdet', one_smul]


theorem L0_bform_e0 : bform (L0 (F := F)).QV e0 e0 = 1 := by
  rw [bform, QuadraticMap.associated_eq_self_apply, L0_QV_apply]
  show (1 : F) * 1 = 1
  ring

/-- `so(V) = 0` for a line `V`. -/
theorem L0_skew_eq_zero {X : Module.End F (L0 (F := F)).V}
    (hX : X ∈ skewAdjointLieSubalgebra (bform (L0 (F := F)).QV)) : X = 0 := by
  have hX' := (LinearMap.mem_skewAdjointSubmodule _).mp hX e0 e0
  have h := L0_end_eq_smul (F := F) X
  set c := (X e0).2 0
  rw [h] at hX'
  rw [Pi.neg_apply, LinearMap.smul_apply, Module.End.one_apply,
    map_smul, map_neg, map_smul, LinearMap.smul_apply, L0_bform_e0] at hX'
  have hc : c = 0 := by
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    have : (2 : F) * c = 0 := by
      have := hX'
      simp only [smul_eq_mul, mul_one] at this
      linear_combination this
    exact (mul_eq_zero.mp this).resolve_left h2
  rw [h, hc, zero_smul]

instance L0_subsingleton_lie : Subsingleton ↥(L0 (F := F)).lie := by
  refine ⟨fun X Y => Subtype.ext ?_⟩
  have hX := L0_skew_eq_zero (F := F) X.2.2
  have hY := L0_skew_eq_zero (F := F) Y.2.2
  exact Prod.ext (Subsingleton.elim _ _) (hX.trans hY.symm)

theorem L0_unit_eq_one {g : (L0 (F := F)).Ambˣ} (hg : g ∈ (L0 (F := F)).Gbar) : g = 1 := by
  apply Units.ext
  refine Prod.ext (Subsingleton.elim _ _) ?_
  exact L0_SO_trivial (F := F) (g := (L0 (F := F)).unitSnd g) hg.2

instance L0_subsingleton_Gbar : Subsingleton ↥(L0 (F := F)).Gbar :=
  ⟨fun a b => Subtype.ext ((L0_unit_eq_one a.2).trans (L0_unit_eq_one b.2).symm)⟩

theorem L0_HbarU_eq_bot : (L0 (F := F)).HbarU = ⊥ := by
  rw [eq_bot_iff, HbarU, Subgroup.closure_le]
  rintro g (⟨a, ha, rfl⟩ | ⟨n, hn, rfl⟩)
  · rw [SetLike.mem_coe, Subgroup.mem_bot]
    apply Units.ext
    refine Prod.ext (Subsingleton.elim _ _) ?_
    show (L0 (F := F)).extGrp (a : Module.End F (L0 (F := F)).W) = 1
    rw [show (a : Module.End F (L0 (F := F)).W) = 1 from Subsingleton.elim _ _, map_one]
  · rw [SetLike.mem_coe, Subgroup.mem_bot]
    apply Units.ext
    refine Prod.ext rfl ?_
    exact L0_SO_trivial (F := F) hn.1

instance L0_subsingleton_HbarU : Subsingleton ↥(L0 (F := F)).HbarU := by
  rw [L0_HbarU_eq_bot]; infer_instance

instance L0_subsingleton_Hbar : Subsingleton ↥(L0 (F := F)).Hbar :=
  ⟨fun _ _ => Subtype.ext (Subsingleton.elim (α := ↥(L0 (F := F)).Gbar) _ _)⟩

instance L0_subsingleton_lieH : Subsingleton ↥(L0 (F := F)).lieH :=
  ⟨fun X Y => Subtype.ext (congrArg Subtype.val
    (Subsingleton.elim (α := ↥(L0 (F := F)).lie) ⟨(X : (L0 (F := F)).Amb), X.2.1⟩
      ⟨(Y : (L0 (F := F)).Amb), Y.2.1⟩) :)⟩

instance L0_subsingleton_lieTorus (T : Subgroup (L0 (F := F)).Ambˣ) :
    Subsingleton ↥((L0 (F := F)).lieTorus T) := by
  refine ⟨fun X Y => Subtype.ext ?_⟩
  have hX := X.2.1
  have hY := Y.2.1
  refine Prod.ext (Subsingleton.elim _ _) ?_
  show (L0 (F := F)).sndA X = (L0 (F := F)).sndA Y
  rw [hX, hY, show (L0 (F := F)).fstA X = (L0 (F := F)).fstA Y from Subsingleton.elim _ _]


instance L0_subsingleton_lieCent (X : (L0 (F := F)).Amb) :
    Subsingleton ↥(lieCentralizer (L0 (F := F)).lie X) :=
  ⟨fun a b => Subtype.ext (congrArg Subtype.val
    (Subsingleton.elim (α := ↥(L0 (F := F)).lie) ⟨(a : (L0 (F := F)).Amb), a.2.1⟩
      ⟨(b : (L0 (F := F)).Amb), b.2.1⟩) :)⟩

instance L0_subsingleton_nilOrbit (G : Subgroup (L0 (F := F)).Ambˣ) (X : (L0 (F := F)).Amb) :
    Subsingleton (NilOrbit G (lieCentralizer (L0 (F := F)).lie X)) := by
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      have : a = b := Subtype.ext (congrArg Subtype.val
        (Subsingleton.elim (α := ↥(lieCentralizer (L0 (F := F)).lie X)) ⟨a.1, a.2.1⟩
          ⟨b.1, b.2.1⟩) :)
      rw [this]

instance L0_subsingleton_lieCent2 (X Y : (L0 (F := F)).Amb) :
    Subsingleton ↥(lieCentralizer (lieCentralizer (L0 (F := F)).lie X) Y) :=
  ⟨fun a b => Subtype.ext (congrArg Subtype.val
    (Subsingleton.elim (α := ↥(L0 (F := F)).lie) ⟨(a : (L0 (F := F)).Amb), a.2.1.1⟩
      ⟨(b : (L0 (F := F)).Amb), b.2.1.1⟩) :)⟩

theorem L0_val_eq_zero {X : (L0 (F := F)).Amb} (hX : X ∈ (L0 (F := F)).lie) : X = 0 :=
  congrArg Subtype.val (Subsingleton.elim (α := ↥(L0 (F := F)).lie) ⟨X, hX⟩ 0)

theorem L0_jHat_eq_one (ψ : NontrivialAddChar F) (G : Subgroup (L0 (F := F)).Ambˣ)
    (X : (L0 (F := F)).Amb) (O : NilOrbit G (lieCentralizer (L0 (F := F)).lie X))
    {Y : (L0 (F := F)).Amb} (hY : Y ∈ lieCentralizer (L0 (F := F)).lie X) :
    jHat G (lieCentralizer (L0 (F := F)).lie X) (L0 (F := F)).traceForm ψ O Y = 1 := by
  rw [Subsingleton.elim O (zeroOrbit _ _)]
  refine jHat_zeroOrbit_eq_one _ _ _ ψ ⟨_, isSelfDual_dirac_zero _ ψ⟩ (fun Z => ?_) hY
  rw [L0_val_eq_zero (F := F) Z.2.1]
  exact ⟨isSS_zero F, ⟨fun a b => Subsingleton.elim _ _⟩⟩

/-- Every function has the expansion `c ≡ θ(0)` (the germ at the zero orbit). -/
theorem L0_hasGermExpansionLie (ψ : NontrivialAddChar F) (θ : ↥(L0 (F := F)).lie → ℂ)
    (X : (L0 (F := F)).Amb) :
    HasGermExpansionLie (L0 (F := F)).Gbar (L0 (F := F)).lie (L0 (F := F)).traceForm ψ θ X
      (fun _ => θ 0) := by
  refine ⟨Set.toFinite _, Set.univ, Filter.univ_mem, fun Y _ hY _ Z _ => ?_⟩
  rw [finsum_eq_single _ (zeroOrbit _ _) (fun O hO => (hO (Subsingleton.elim _ _)).elim),
    L0_jHat_eq_one ψ _ X _ hY, mul_one, Subsingleton.elim Z 0]

/-- Any expansion has coefficient `θ(0)`. -/
theorem L0_coeff_eq (ψ : NontrivialAddChar F) (θ : ↥(L0 (F := F)).lie → ℂ)
    (X : (L0 (F := F)).Amb) (hX : X ∈ (L0 (F := F)).lie)
    {c : NilOrbit (lieGrpCentralizer (L0 (F := F)).Gbar X) (lieCentralizer (L0 (F := F)).lie X) → ℂ}
    (hc : HasGermExpansionLie (L0 (F := F)).Gbar (L0 (F := F)).lie (L0 (F := F)).traceForm ψ θ X c)
    (O : NilOrbit (lieGrpCentralizer (L0 (F := F)).Gbar X) (lieCentralizer (L0 (F := F)).lie X)) :
    c O = θ 0 := by
  obtain ⟨-, ω, hω, h⟩ := hc
  have h0 : (0 : (L0 (F := F)).Amb) ∈ lieCentralizer (L0 (F := F)).lie X := zero_mem _
  have := h 0 (mem_of_mem_nhds hω) h0
    (by
      refine ⟨isSS_zero F, ⟨fun a b => Subsingleton.elim _ _⟩⟩) 0
    (by rw [L0_val_eq_zero (F := F) hX]; simp)
  rw [finsum_eq_single _ O (fun O' hO' => (hO' (Subsingleton.elim _ _)).elim),
    L0_jHat_eq_one ψ _ X _ h0, mul_one] at this
  exact this.symm


theorem L0_measLie (ψ : NontrivialAddChar F) : (L0 (F := F)).measLie ψ = Measure.dirac 0 :=
  selfDualMeasure_eq_dirac_zero _ ψ

theorem L0_orbitalPairing (ψ : NontrivialAddChar F) (μG : Measure ↥(L0 (F := F)).Gbar)
    (f f' : ↥(L0 (F := F)).lie → ℂ) :
    (L0 (F := F)).orbitalPairing ψ μG f f' = (μG.real Set.univ : ℂ) * (f 0 * f' 0) := by
  unfold LuoDatum.orbitalPairing
  rw [integral_of_subsingleton _ _ 1, L0_measLie]
  rw [integral_of_subsingleton _ _ 0]
  have h1 : (Measure.dirac (0 : ↥(L0 (F := F)).lie)).real Set.univ = 1 := by simp
  have h2 : (L0 (F := F)).extFn f
      ((L0 (F := F)).conjInv 1 ((0 : ↥(L0 (F := F)).lie) : (L0 (F := F)).Amb)) = f 0 := by
    unfold LuoDatum.extFn LuoDatum.conjInv
    split_ifs with h
    · congr 1
    · exact absurd (by simp) h
  rw [h1, h2, one_smul, Complex.real_smul]


theorem L0_distribJLie (ψ : NontrivialAddChar F) (μ𝔥 : Measure ↥(L0 (F := F)).lieH)
    (m : Measure (CosetSpace (L0 (F := F)).Hbar.subtype)) (f : ↥(L0 (F := F)).lie → ℂ) :
    (L0 (F := F)).distribJLie ψ μ𝔥 m f =
      (m.real Set.univ : ℂ) * ((μ𝔥.real Set.univ : ℂ) * f 0) := by
  have hk : ∀ x, (L0 (F := F)).kernelLie ψ μ𝔥 f x = (μ𝔥.real Set.univ : ℂ) * f 0 := by
    intro x
    unfold LuoDatum.kernelLie
    rw [integral_of_subsingleton _ _ 0, Complex.real_smul]
    congr 1
    have hxi : (L0 (F := F)).xi ψ ((0 : ↥(L0 (F := F)).lieH) : (L0 (F := F)).Amb) = 1 := by
      unfold LuoDatum.xi LuoDatum.lam
      simp [NontrivialAddChar.map_zero]
    rw [hxi, mul_one]
    unfold LuoDatum.extFn LuoDatum.conjInv
    split_ifs with h
    · congr 1; exact Subtype.ext (L0_val_eq_zero (F := F) h)
    · exact absurd (by simp) h
  unfold LuoDatum.distribJLie
  simp only [hk]
  rw [integral_const, Complex.real_smul]

theorem L0_expCompatH_univ (μH : Measure ↥(L0 (F := F)).Hbar) (μ𝔥 : Measure ↥(L0 (F := F)).lieH)
    (h : (L0 (F := F)).IsExpCompatH μH μ𝔥) : μ𝔥 Set.univ = μH Set.univ := by
  obtain ⟨-, U, hU, hS⟩ := h
  have hsub : Set.univ ⊆ U := fun y _ => by
    rw [Subsingleton.elim y 0]; exact mem_of_mem_nhds hU
  rw [hS Set.univ MeasurableSet.univ hsub]
  congr 1
  ext h
  simp only [Set.mem_setOf_eq, Set.mem_univ, true_and, iff_true]
  refine ⟨0, ?_⟩
  rw [Subsingleton.elim h 1]
  simp [expA_zero]

theorem L0_weil (μG : Measure ↥(L0 (F := F)).Gbar) (μH : Measure ↥(L0 (F := F)).Hbar)
    (m : Measure (CosetSpace (L0 (F := F)).Hbar.subtype))
    (hm : IsWeilMeasure (L0 (F := F)).Hbar.subtype μG μH m) :
    μG.real Set.univ = m.real Set.univ * μH.real Set.univ := by
  haveI : Finite ↥(L0 (F := F)).Gbar := Finite.of_subsingleton
  have := hm (fun _ => 1) continuous_const
    (HasCompactSupport.intro' isCompact_univ isClosed_univ (fun x hx => (hx trivial).elim))
  simp only [integral_const, smul_eq_mul, mul_one] at this
  rw [this, mul_comm]


instance : Subsingleton (Module.End F (L0 (F := F)).W)ˣ :=
  ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩

theorem L0_torusOf (X : Module.End F (L0 (F := F)).W) : (L0 (F := F)).torusOf X = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨g, -, rfl⟩
  rw [Subgroup.mem_bot, Subsingleton.elim g 1, map_one]

theorem L0_isGammaElt_zero : (L0 (F := F)).IsGammaElt 0 := by
  refine ⟨zero_mem _, isSS_zero F, ?_, ?_⟩
  · intro a ha b hb
    rw [L0_torusOf, Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  · rw [L0_torusOf]
    haveI : Finite ↥(⊥ : Subgroup (L0 (F := F)).Ambˣ) := Finite.of_subsingleton
    infer_instance

instance : Subsingleton (L0 (F := F)).GammaTorus := by
  refine ⟨fun T T' => Subtype.ext ?_⟩
  obtain ⟨X, -, hX⟩ := T.2
  obtain ⟨X', -, hX'⟩ := T'.2
  rw [← hX, ← hX', L0_torusOf, L0_torusOf]

def L0_gammaTorus : (L0 (F := F)).GammaTorus := ⟨_, 0, L0_isGammaElt_zero, rfl⟩

instance : Subsingleton (L0 (F := F)).GammaClass := by
  refine ⟨fun a b => ?_⟩
  induction a using Quot.ind
  induction b using Quot.ind
  congr 1
  exact Subsingleton.elim _ _

theorem L0_gammaTorus_eq_bot (T : (L0 (F := F)).GammaTorus) : T.1 = ⊥ := by
  obtain ⟨X, -, hX⟩ := T.2
  rw [← hX, L0_torusOf]

theorem L0_weylCardOf (T : Subgroup (L0 (F := F)).Ambˣ) : (L0 (F := F)).weylCardOf T = 1 := by
  unfold LuoDatum.weylCardOf
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
  induction a using QuotientGroup.induction_on
  induction b using QuotientGroup.induction_on
  congr 1
  exact Subsingleton.elim _ _


theorem L0_expCompatT_univ (T : (L0 (F := F)).GammaTorus)
    (μ : Measure ↥((L0 (F := F)).lieTorus T.1))
    (h : (L0 (F := F)).IsExpCompatT T.1 μ) : μ.real Set.univ = 1 := by
  letI : MeasurableSpace ↥T.1 := borel _
  haveI : BorelSpace ↥T.1 := ⟨rfl⟩
  obtain ⟨-, U, hU, hS⟩ := h
  have hsub : Set.univ ⊆ U := fun y _ => by
    rw [Subsingleton.elim y 0]; exact mem_of_mem_nhds hU
  have hT : Subsingleton ↥T.1 := by rw [L0_gammaTorus_eq_bot]; infer_instance
  haveI : Finite ↥T.1 := Finite.of_subsingleton
  have e := hS Set.univ MeasurableSet.univ hsub
  have hset : {t : ↥T.1 | ∃ X ∈ (Set.univ : Set ↥((L0 (F := F)).lieTorus T.1)),
      ((t : (L0 (F := F)).Ambˣ) : (L0 (F := F)).Amb) = expA F (X : (L0 (F := F)).Amb)} =
      Set.univ := by
    ext t
    simp only [Set.mem_univ, true_and, iff_true]
    refine ⟨0, ?_⟩
    rw [Subsingleton.elim t 1]
    simp [expA_zero]
  rw [hset] at e
  rw [measureReal_def, e]
  have := probHaar_real_univ ↥T.1
  rwa [measureReal_def] at this


theorem charpoly_eq_one_of_subsingleton {M : Type*} [AddCommGroup M] [Module F M]
    [Module.Finite F M] [Subsingleton M] (g : M →ₗ[F] M) : LinearMap.charpoly g = 1 :=
  Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic g)
    (by rw [LinearMap.charpoly_natDegree, Module.finrank_zero_of_subsingleton])

theorem absF_one' : absF (1 : F) = 1 := by
  rw [absF_of_ne_zero one_ne_zero]
  simp

theorem L0_weylDiscLie : weylDiscLie (L0 (F := F)).lie 0 = 1 := by
  unfold weylDiscLie
  rw [dif_pos (fun Y _ => by simp)]
  haveI : Subsingleton ↥(L0 (F := F)).lie.toSubmodule :=
    inferInstanceAs (Subsingleton ↥(L0 (F := F)).lie)
  rw [charpoly_eq_one_of_subsingleton, Polynomial.trailingCoeff, Polynomial.natTrailingDegree_one,
    Polynomial.coeff_one_zero, absF_one']

theorem L0_delta : (L0 (F := F)).delta 0 = 1 := by
  unfold LuoDatum.delta
  rw [LinearMap.det_eq_one_of_finrank_eq_zero (Module.finrank_zero_of_subsingleton), absF_one']

theorem L0_isNat (T : Subgroup (L0 (F := F)).Ambˣ) : (L0 (F := F)).IsNat T 0 := by
  refine ⟨zero_mem _, Subsingleton.elim _ _, ?_⟩
  rw [charpoly_eq_one_of_subsingleton]
  exact squarefree_one

theorem L0_nilReg (X : (L0 (F := F)).Amb)
    (O : NilOrbit (lieGrpCentralizer (L0 (F := F)).Gbar X) (lieCentralizer (L0 (F := F)).lie X)) :
    O ∈ NilReg _ _ := by
  refine ⟨(Quotient.out O).2.1, (Quotient.out O).2.2, ?_⟩
  unfold lieRank
  simp only [Module.finrank_zero_of_subsingleton, ciInf_const]

theorem L0_cTheta (ψ : NontrivialAddChar F) (θ : ↥(L0 (F := F)).lie → ℂ) :
    (L0 (F := F)).cTheta ψ θ 0 = θ 0 := by
  unfold LuoDatum.cTheta germLie
  have hE : ∃ c, HasGermExpansionLie (L0 (F := F)).Gbar (L0 (F := F)).lie
      (L0 (F := F)).traceForm ψ θ 0 c := ⟨_, L0_hasGermExpansionLie ψ θ 0⟩
  rw [if_pos (L0_nilReg _ _), dif_pos hE]
  exact L0_coeff_eq ψ θ 0 (zero_mem _) hE.choose_spec _

theorem L0_mGeomLieS (ψ : NontrivialAddChar F)
    (μT : ∀ T : (L0 (F := F)).GammaTorus, Measure ↥((L0 (F := F)).lieTorus T.1))
    (hμT : ∀ T, (L0 (F := F)).IsExpCompatT T.1 (μT T)) (θ : ↥(L0 (F := F)).lie → ℂ) (s : ℝ) :
    (L0 (F := F)).mGeomLieS ψ μT θ s = θ 0 := by
  unfold LuoDatum.mGeomLieS
  have hsingle := tsum_eq_single (L := SummationFilter.unconditional (L0 (F := F)).GammaClass)
    (f := fun c : (L0 (F := F)).GammaClass =>
      (((L0 (F := F)).weylCardOf (Quot.out c).1 : ℂ))⁻¹ *
        ∫ X : ↥((L0 (F := F)).lieTorus (Quot.out c).1),
          (L0 (F := F)).gammaIntegrand ψ θ (Quot.out c).1 s X ∂μT (Quot.out c))
    (Quot.mk _ L0_gammaTorus) fun c hc => (hc (Subsingleton.elim _ _)).elim
  rw [hsingle]
  rw [L0_weylCardOf, Nat.cast_one, inv_one, one_mul, integral_of_subsingleton _ _ 0,
    L0_expCompatT_univ _ _ (hμT _), one_smul]
  unfold LuoDatum.gammaIntegrand
  rw [ZeroMemClass.coe_zero, if_pos (L0_isNat _), L0_weylDiscLie, L0_delta, L0_cTheta]
  simp


/-- **The conclusion of `luo_lie_geomExpansion_SO` holds at the Luo datum `W = 0`, `V` a line**,
for every choice of `ψ`, Haar measures, compatible measures and `f`, proved without the axiom.
The witness is `θ ≡ μG(Ḡ) f(0)`; both `J^Lie(f)` and `m^Lie_{geom,s}(θ)` equal `μG(Ḡ) f(0)`. -/
theorem luo_conclusion_L0 (ψ : NontrivialAddChar F)
    (μG : Measure ↥(L0 (F := F)).Gbar) (μH : Measure ↥(L0 (F := F)).Hbar)
    (μ𝔥 : Measure ↥(L0 (F := F)).lieH) (h𝔥 : (L0 (F := F)).IsExpCompatH μH μ𝔥)
    (m : Measure (CosetSpace (L0 (F := F)).Hbar.subtype))
    (hm : IsWeilMeasure (L0 (F := F)).Hbar.subtype μG μH m)
    (μT : ∀ T : (L0 (F := F)).GammaTorus, Measure ↥((L0 (F := F)).lieTorus T.1))
    (hμT : ∀ T : (L0 (F := F)).GammaTorus, (L0 (F := F)).IsExpCompatT T.1 (μT T))
    (f : ↥(L0 (F := F)).lie → ℂ) :
    ∃ θ : ↥(L0 (F := F)).lie → ℂ,
      (LocallyIntegrable θ ((L0 (F := F)).measLie ψ) ∧
        ContinuousOn θ
          {X : ↥(L0 (F := F)).lie | IsRegularSS (L0 (F := F)).lie (X : (L0 (F := F)).Amb)} ∧
        ∀ f' : ↥(L0 (F := F)).lie → ℂ, IsTestFn f' →
          ∫ X, θ X * f' X ∂(L0 (F := F)).measLie ψ = (L0 (F := F)).orbitalPairing ψ μG f f') ∧
      IsLieQuasiCharacter (L0 (F := F)).Gbar (L0 (F := F)).lie (L0 (F := F)).traceForm ψ θ ∧
      Tendsto ((L0 (F := F)).mGeomLieS ψ μT θ) (𝓝[>] (0 : ℝ))
        (𝓝 ((L0 (F := F)).distribJLie ψ μ𝔥 m f)) := by
  set c : ℂ := (μG.real Set.univ : ℂ) * f 0
  refine ⟨fun _ => c, ⟨?_, continuousOn_const, fun f' _ => ?_⟩, ⟨fun _ _ _ _ _ _ => rfl,
    fun X _ => ⟨_, L0_hasGermExpansionLie ψ _ X⟩⟩, ?_⟩
  · rw [L0_measLie]; exact (integrable_const c).locallyIntegrable
  · rw [L0_orbitalPairing, L0_measLie, integral_of_subsingleton _ _ 0]
    simp [c, mul_assoc]
  · have h1 : ∀ s, (L0 (F := F)).mGeomLieS ψ μT (fun _ => c) s = c :=
      fun s => L0_mGeomLieS ψ μT hμT _ s
    have h2 : (L0 (F := F)).distribJLie ψ μ𝔥 m f = c := by
      have hh : μ𝔥.real Set.univ = μH.real Set.univ := by
        rw [measureReal_def, measureReal_def, L0_expCompatH_univ μH μ𝔥 h𝔥]
      rw [L0_distribJLie, hh]
      simp only [c, L0_weil μG μH m hm]
      push_cast; ring
    rw [show (L0 (F := F)).mGeomLieS ψ μT (fun _ => c) = fun _ => c from funext h1, h2]
    exact tendsto_const_nhds

/-! ## `germLie_unique_SO` -/

/-- **`germLie_unique_SO` at `L0`, for every function `θ`**: two expansions of `θ` at `X ∈ 𝔤`
have the same coefficients, both `θ(0)` (`L0_coeff_eq`). -/
theorem L0_germLie_unique (ψ : NontrivialAddChar F) (θ : ↥(L0 (F := F)).lie → ℂ)
    (X : (L0 (F := F)).Amb) (hX : X ∈ (L0 (F := F)).lie)
    (c c' : NilOrbit (lieGrpCentralizer (L0 (F := F)).Gbar X)
      (lieCentralizer (L0 (F := F)).lie X) → ℂ)
    (hc : HasGermExpansionLie (L0 (F := F)).Gbar (L0 (F := F)).lie (L0 (F := F)).traceForm ψ θ X c)
    (hc' : HasGermExpansionLie (L0 (F := F)).Gbar (L0 (F := F)).lie (L0 (F := F)).traceForm ψ θ X
      c') :
    ∀ O ∈ NilReg (lieGrpCentralizer (L0 (F := F)).Gbar X) (lieCentralizer (L0 (F := F)).lie X),
      c O = c' O := fun O _ =>
  (L0_coeff_eq ψ θ X hX hc O).trans (L0_coeff_eq ψ θ X hX hc' O).symm

/-- The axiom's instance at `L0` (agrees with `L0_germLie_unique`; its hypotheses are satisfiable
by `L0_hasGermExpansionLie`). -/
example (ψ : NontrivialAddChar F) (θ : ↥(L0 (F := F)).lie → ℂ)
    (X : (L0 (F := F)).Amb) (hX : X ∈ (L0 (F := F)).lie) (hss : IsSS F X)
    (c c' : NilOrbit (lieGrpCentralizer (L0 (F := F)).Gbar X)
      (lieCentralizer (L0 (F := F)).lie X) → ℂ)
    (hc : HasGermExpansionLie (L0 (F := F)).Gbar (L0 (F := F)).lie (L0 (F := F)).traceForm ψ θ X c)
    (hc' : HasGermExpansionLie (L0 (F := F)).Gbar (L0 (F := F)).lie (L0 (F := F)).traceForm ψ θ X
      c') :
    ∀ O ∈ NilReg _ _, c O = c' O :=
  germLie_unique_SO (L0 (F := F)) (toyD (F := F)).nondeg_QV ψ θ X hX hss c c' hc hc'

/-- In `L0`, the zero orbit of `𝔤_X` is regular (`𝔤_X = 0`). -/
theorem L0_zeroOrbit_mem_nilReg (G : Subgroup (L0 (F := F)).Ambˣ) (X : (L0 (F := F)).Amb) :
    zeroOrbit G (lieCentralizer (L0 (F := F)).lie X) ∈
      NilReg G (lieCentralizer (L0 (F := F)).lie X) := by
  change IsRegularNil _ (Quotient.out (zeroOrbit G (lieCentralizer (L0 (F := F)).lie X))).1
  refine ⟨(Quotient.out (zeroOrbit G _)).2.1, (Quotient.out (zeroOrbit G _)).2.2, ?_⟩
  rw [Module.finrank_zero_of_subsingleton, lieRank]
  simp [Module.finrank_zero_of_subsingleton]

/-- `1 ∉ 𝔤` in `L0` (`so(V) = 0` and `V ≠ 0`). -/
theorem L0_one_not_mem_lie : (1 : (L0 (F := F)).Amb) ∉ (L0 (F := F)).lie := by
  intro h
  have h1 := L0_val_eq_zero (F := F) h
  have h2 : ((1 : (L0 (F := F)).Amb).2 : Module.End F (L0 (F := F)).V) e0 = e0 := rfl
  rw [h1] at h2
  change (0 : Module.End F (L0 (F := F)).V) e0 = e0 at h2
  rw [LinearMap.zero_apply] at h2
  have h3 := congrArg (fun v : (L0 (F := F)).V => v.2 0) h2
  simp [e0] at h3

/-- **The hypothesis `X ∈ 𝔤` of `germLie_unique_SO` is needed.**  At `L0` and the semisimple
`X = 1 ∉ 𝔤`, no `Z ∈ 𝔤` is `X + Y` with `Y ∈ 𝔤_X`, so every `c` is an expansion of `θ = 0`;
the statement without `hX` would give `1 = 0` at the regular zero orbit. -/
theorem L0_germLie_unique_needs_mem_lie (ψ : NontrivialAddChar F)
    (h : ∀ (X : (L0 (F := F)).Amb), IsSS F X →
      ∀ c c' : NilOrbit (lieGrpCentralizer (L0 (F := F)).Gbar X)
          (lieCentralizer (L0 (F := F)).lie X) → ℂ,
        HasGermExpansionLie (L0 (F := F)).Gbar (L0 (F := F)).lie (L0 (F := F)).traceForm ψ 0 X c →
        HasGermExpansionLie (L0 (F := F)).Gbar (L0 (F := F)).lie (L0 (F := F)).traceForm ψ 0 X
          c' →
        ∀ O ∈ NilReg _ _, c O = c' O) : False := by
  have hss : IsSS F (1 : (L0 (F := F)).Amb) := by
    unfold IsSS
    rw [LinearMap.mulLeft_one]
    exact Module.End.isSemisimple_id
  have hexp : ∀ c : NilOrbit (lieGrpCentralizer (L0 (F := F)).Gbar 1)
      (lieCentralizer (L0 (F := F)).lie 1) → ℂ,
      HasGermExpansionLie (L0 (F := F)).Gbar (L0 (F := F)).lie (L0 (F := F)).traceForm ψ 0 1 c :=
    fun c => ⟨Set.toFinite _, Set.univ, Filter.univ_mem, fun Y _ hY _ Z hZ => by
      exfalso
      have hY0 : Y = 0 := L0_val_eq_zero (F := F) (mem_lieCentralizer.mp hY).1
      rw [hY0, add_zero] at hZ
      exact L0_one_not_mem_lie (hZ ▸ Z.2)⟩
  have := h 1 hss (fun _ => 1) 0 (hexp _) (hexp _) _ (L0_zeroOrbit_mem_nilReg _ 1)
  simp at this

end GSpinGGP.AxiomRedTeam

/-! ## Consequences of `germLie_unique_SO` on any Luo datum -/

namespace GSpinGGP.AxiomRedTeam

open GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- Under `germLie_unique_SO`, two distinct nilpotent orbits of `𝔤_X`, one of them regular, have
distinct orbit measures (otherwise `ĵ(O, ·) = ĵ(O', ·)` and `θ = 0` has two expansions). -/
theorem false_of_orbitMeasure_eq_lie (L : LuoDatum F) (hQV : IsNondeg L.QV)
    (ψ : NontrivialAddChar F) (X : L.Amb) (hX : X ∈ L.lie) (hss : IsSS F X)
    (O O' : NilOrbit (lieGrpCentralizer L.Gbar X) (lieCentralizer L.lie X))
    (hO : O ∈ NilReg _ _) (hne : O ≠ O')
    (h : orbitMeasure (lieGrpCentralizer L.Gbar X) (lieCentralizer L.lie X) L.traceForm ψ O =
      orbitMeasure (lieGrpCentralizer L.Gbar X) (lieCentralizer L.lie X) L.traceForm ψ O') :
    False := by
  classical
  have hj := jHat_eq_of_orbitMeasure_eq (lieGrpCentralizer L.Gbar X) (lieCentralizer L.lie X)
    L.traceForm ψ O O' h
  set c : NilOrbit (lieGrpCentralizer L.Gbar X) (lieCentralizer L.lie X) → ℂ :=
    fun P => (if P = O then 1 else 0) - (if P = O' then 1 else 0)
  have hfin : (Function.support c).Finite := by
    refine (Set.toFinite ({O, O'} : Set _)).subset fun P hP => ?_
    by_contra hP'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hP'
    exact hP (by simp [c, hP'.1, hP'.2])
  have hexp : HasGermExpansionLie L.Gbar L.lie L.traceForm ψ 0 X c := by
    refine ⟨hfin, Set.univ, Filter.univ_mem, fun Y _ _ _ Z _ => ?_⟩
    have hsupp : (Function.support fun P => c P * jHat (lieGrpCentralizer L.Gbar X)
        (lieCentralizer L.lie X) L.traceForm ψ P Y) ⊆ (({O, O'} : Finset _) : Set _) := by
      intro P hP
      by_contra h'
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or] at h'
      exact hP (by simp [c, h'.1, h'.2])
    rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_pair hne]
    simp [c, hne, Ne.symm hne, hj]
  have h0 : HasGermExpansionLie L.Gbar L.lie L.traceForm ψ 0 X 0 :=
    ⟨by simp, Set.univ, Filter.univ_mem, fun _ _ _ _ _ _ => by simp⟩
  have := germLie_unique_SO L hQV ψ 0 X hX hss c 0 hexp h0 O hO
  simp [c, hne] at this

/-- Under `germLie_unique_SO`, for `O` regular, `ĵ(O, ·)` is not eventually `0` near `0` on the
regular semisimple elements of `𝔤_X` (otherwise `0` and `δ_O` are two expansions of `θ = 0`).
Since `ĵ(O, ·)` is `0` when no orbit measure of `O` exists, this implies that one exists. -/
theorem germLie_unique_SO_forces_jHat_ne_zero (L : LuoDatum F) (hQV : IsNondeg L.QV)
    (ψ : NontrivialAddChar F) (X : L.Amb) (hX : X ∈ L.lie) (hss : IsSS F X)
    (O : NilOrbit (lieGrpCentralizer L.Gbar X) (lieCentralizer L.lie X))
    (hO : O ∈ NilReg (lieGrpCentralizer L.Gbar X) (lieCentralizer L.lie X)) :
    ∀ ω ∈ 𝓝 (0 : L.Amb), ∃ Y ∈ ω, Y ∈ lieCentralizer L.lie X ∧
      IsRegularSS (lieCentralizer L.lie X) Y ∧
      jHat (lieGrpCentralizer L.Gbar X) (lieCentralizer L.lie X) L.traceForm ψ O Y ≠ 0 := by
  classical
  intro ω hω
  by_contra hcon
  push Not at hcon
  have h0 : HasGermExpansionLie L.Gbar L.lie L.traceForm ψ 0 X 0 :=
    ⟨by simp, ω, hω, fun _ _ _ _ _ _ => by simp⟩
  have h1 : HasGermExpansionLie L.Gbar L.lie L.traceForm ψ 0 X (Pi.single O 1) := by
    refine ⟨(Set.finite_singleton O).subset fun O' hO' => ?_, ω, hω, fun Y hYω hYc hYr Z _ => ?_⟩
    · by_contra h; exact hO' (Pi.single_eq_of_ne h _)
    · rw [finsum_eq_single _ O (fun O' hO' => by rw [Pi.single_eq_of_ne hO', zero_mul]),
        Pi.single_eq_same, one_mul, hcon Y hYω hYc hYr]
      rfl
  have := germLie_unique_SO L hQV ψ 0 X hX hss 0 (Pi.single O 1) h0 h1 O hO
  simp at this

end GSpinGGP.AxiomRedTeam
