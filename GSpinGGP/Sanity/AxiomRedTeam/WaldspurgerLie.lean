/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.WaldspurgerLie
import GSpinGGP.Sanity.AxiomRedTeam.Luo

/-!
# Checks of `waldspurger2010_thm_7_9`

* **Junk values.**  The truncated integrals vanish identically for `f = 0` or `θ = 0`
  (`IN_zero_right`, `IN_zero_left`), without the axiom; so for `f = 0` (very cuspidal) and any `τ`
  representing its orbital pairing, the axiom says `I(θ, τ) = 0` (`Igeom_eq_zero_of_f_zero`), and
  for `θ = 0` that `I(0, τ) = 0` (`Igeom_zero_left`).  The geometric side is built from the
  germs `germLie` (a choice among expansions when one exists), so these are statements about those
  choices: for `τ = 0` and `θ = 0` they hold whenever the chosen expansions of `0` vanish, which is
  the case when the regular coefficients are unique (Harish-Chandra 1999 Cor 5.10).  No
  contradiction is derivable from them alone.
* `0` is very cuspidal, and `τ = 0` represents its orbital pairing, so `Igeom_eq_zero_of_f_zero`
  is not vacuous in `θ`, `f`, `τ` (`isVeryCuspidal_zero`, `isThetaFW1_zero`).

* **Verified at `L0`** (`W = 0`, `V` a line, `r = 0`; the Luo datum of `Sanity/AxiomRedTeam/Luo.lean`):
  for every `W1Input`, every `θ`, `f` and every `τ` with `IsThetaFW1`, the conclusion holds without
  the axiom (`w1_conclusion_L0`): `I_N(θ, f) = κ_N(1) μ_G(G) θ(0) f(0)` (`w1_IN`), `κ_N(1) = 1` for
  `N` large (`w1_kappa_eventually`, from the special lattice `R₀`), and
  `I(θ, τ) = θ(0) τ(0) = μ_G(G) θ(0) f(0)` (`w1_Igeom`, `w1_tau`).  This checks the normalizations
  of `I_N` (Weil quotient, `du dh`, `exp`-compatible measures) against those of `I(θ, f)` (`𝒯`,
  `|W(H, T)|`, `ν(T)`, `D^H`, `Δ^r`, germs) and `θ_f`.  Hypotheses satisfiable there: every test
  function is very cuspidal (`w1_isVeryCuspidal`) and `τ ≡ μ_G(G) f(0)` satisfies `IsThetaFW1`
  (`w1_isThetaFW1`).

Not covered: a constructed `W1Input` (only quantified over); any datum with a nontrivial torus,
a nonzero nilpotent orbit, a nontrivial `U` or a proper parabolic.
-/

noncomputable section
open MeasureTheory Topology Filter

namespace GSpinGGP

namespace Sanity

open LuoDatum

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] {L : LuoDatum F}
  {ψ : NontrivialAddChar F}

theorem extV_zero : L.extV (0 : ↥L.soV → ℂ) = 0 := by
  funext X; unfold extV; split_ifs <;> rfl

theorem IN_zero_right (I : L.W1Input ψ) (θ : ↥L.soW → ℂ) (N : ℕ) : I.IN θ 0 N = 0 := by
  simp [W1Input.IN, W1Input.Ig, LuoDatum.Ig, fXi, extV_zero]

theorem IN_zero_left (I : L.W1Input ψ) (f : ↥L.soV → ℂ) (N : ℕ) : I.IN 0 f N = 0 := by
  simp [W1Input.IN, W1Input.Ig, LuoDatum.Ig]

theorem isVeryCuspidal_zero : L.IsVeryCuspidal 0 := by
  refine ⟨?_, fun FV _ X _ μ _ => ⟨integrable_zero _ _ _, by simp⟩⟩
  exact ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

theorem isLieQuasiCharacter_zero_soV : IsLieQuasiCharacter L.SOV L.soV L.bV ψ 0 :=
  ⟨fun _ _ _ _ _ _ => rfl,
    fun _ _ => ⟨0, by simp, _, Filter.univ_mem, fun _ _ _ _ _ _ => by simp⟩⟩

theorem isThetaFW1_zero (μG : Measure ↥L.SOV) : L.IsThetaFW1 ψ μG 0 0 := by
  refine ⟨isLieQuasiCharacter_zero_soV, locallyIntegrable_zero, continuousOn_const,
    fun f' _ => ?_⟩
  simp [extV_zero]

/-- The axiom at `f = 0`: `I(θ, τ) = 0` for every `τ` representing the zero pairing. -/
theorem Igeom_eq_zero_of_f_zero (hV : IsNondeg L.QV) (hV2 : ¬ IsHypPlane L.QV) (I : L.W1Input ψ)
    {θ : ↥L.soW → ℂ} (hθ : IsLieQuasiCharacter L.SOW L.soW L.bW ψ θ) {τ : ↥L.soV → ℂ}
    (hτ : L.IsThetaFW1 ψ I.μG 0 τ) : I.Igeom θ τ = 0 := by
  have h := waldspurger2010_thm_7_9 L hV hV2 ψ I θ hθ 0 isVeryCuspidal_zero τ hτ
  rw [show I.IN θ 0 = fun _ => 0 from funext (IN_zero_right I θ)] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The axiom at `θ = 0` (a quasi-character): `I(0, τ) = 0`. -/
theorem Igeom_zero_left (hV : IsNondeg L.QV) (hV2 : ¬ IsHypPlane L.QV) (I : L.W1Input ψ)
    (h0 : IsLieQuasiCharacter L.SOW L.soW L.bW ψ 0) {f : ↥L.soV → ℂ} (hf : L.IsVeryCuspidal f)
    {τ : ↥L.soV → ℂ} (hτ : L.IsThetaFW1 ψ I.μG f τ) : I.Igeom 0 τ = 0 := by
  have h := waldspurger2010_thm_7_9 L hV hV2 ψ I 0 h0 f hf τ hτ
  rw [show I.IN 0 f = fun _ => 0 from funext (IN_zero_left I f)] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

end Sanity

end GSpinGGP

open Module
attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace GSpinGGP.AxiomRedTeam
open GSpinGGP GSpinGGP.Sanity GSpinGGP.LuoDatum
variable {F : Type} [NontriviallyNormedField F] [PAdicField F]



instance w1_sub_EndW : Subsingleton (L0 (F := F)).EndW :=
  inferInstanceAs (Subsingleton (Module.End F (L0 (F := F)).W))

instance w1_sub_soW : Subsingleton ↥(L0 (F := F)).soW :=
  ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩

theorem w1_soV_val {X : (L0 (F := F)).EndV} (hX : X ∈ (L0 (F := F)).soV) : X = 0 :=
  L0_skew_eq_zero (F := F) (X := (X : Module.End F (L0 (F := F)).V)) hX

instance w1_sub_soV : Subsingleton ↥(L0 (F := F)).soV :=
  ⟨fun a b => Subtype.ext ((w1_soV_val a.2).trans (w1_soV_val b.2).symm)⟩

instance w1_sub_lieU : Subsingleton ↥(L0 (F := F)).lieU :=
  ⟨fun a b => Subtype.ext ((L0_skew_eq_zero (F := F) a.2.1).trans
    (L0_skew_eq_zero (F := F) b.2.1).symm)⟩

instance w1_sub_SOV : Subsingleton ↥(L0 (F := F)).SOV :=
  ⟨fun a b => Subtype.ext (Units.ext ((L0_SO_trivial (F := F) a.2).trans
    (L0_SO_trivial (F := F) b.2).symm))⟩

theorem w1_SOV_eq_one (g : ↥(L0 (F := F)).SOV) : g = 1 := Subsingleton.elim _ _

instance w1_sub_Ubar : Subsingleton ↥(L0 (F := F)).Ubar := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
instance w1_sub_Hbar : Subsingleton ↥(L0 (F := F)).Hbar' := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
instance w1_sub_UHbar : Subsingleton ↥(L0 (F := F)).UHbar :=
  ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩

instance w1_sub_coset : Subsingleton (CosetSpace (L0 (F := F)).UHbar.subtype) :=
  ⟨fun a b => by
    induction a using CosetSpace.ind; induction b using CosetSpace.ind
    congr 1; exact Subsingleton.elim _ _⟩

def q0 : CosetSpace (L0 (F := F)).UHbar.subtype := CosetSpace.mk _ 1

section
variable {ψ : NontrivialAddChar F} (J : (L0 (F := F)).W1Input ψ)

theorem w1_mu𝔥 : J.μ𝔥.real Set.univ = J.μH.real Set.univ := by
  obtain ⟨-, U, hU, hS⟩ := J.h𝔥
  have hsub : Set.univ ⊆ U := fun y _ => by
    rw [Subsingleton.elim y 0]; exact mem_of_mem_nhds hU
  rw [measureReal_def, measureReal_def, hS Set.univ MeasurableSet.univ hsub]
  congr 2
  ext h
  simp only [Set.mem_setOf_eq, Set.mem_univ, true_and, iff_true]
  refine ⟨0, ?_⟩
  have h1 : (((h : ↥(L0 (F := F)).SOV) : (L0 (F := F)).EndVˣ) : (L0 (F := F)).EndV) = 1 := by
    rw [w1_SOV_eq_one (h : ↥(L0 (F := F)).SOV)]; rfl
  rw [h1]
  rw [show (L0 (F := F)).ofV ((L0 (F := F)).extLie ((L0 (F := F)).asW
      ((0 : ↥(L0 (F := F)).soW) : (L0 (F := F)).EndW))) = 0 from map_zero (L0 (F := F)).extLie,
    expA_zero]

theorem w1_mu𝔲 : J.μ𝔲.real Set.univ = J.μU.real Set.univ := by
  obtain ⟨-, U, hU, hS⟩ := J.h𝔲
  have hsub : Set.univ ⊆ U := fun y _ => by
    rw [Subsingleton.elim y 0]; exact mem_of_mem_nhds hU
  rw [measureReal_def, measureReal_def, hS Set.univ MeasurableSet.univ hsub]
  congr 2
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_univ, true_and, iff_true]
  refine ⟨0, ?_⟩
  have h1 : (((u : ↥(L0 (F := F)).SOV) : (L0 (F := F)).EndVˣ) : (L0 (F := F)).EndV) = 1 := by
    rw [w1_SOV_eq_one (u : ↥(L0 (F := F)).SOV)]; rfl
  rw [h1]
  simp [expA_zero]

theorem w1_muUH : J.μUH.real Set.univ = J.μU.real Set.univ * J.μH.real Set.univ := by
  haveI : Finite ↥(L0 (F := F)).UHbar := Finite.of_subsingleton
  have := J.μUH_prod (fun _ => 1) continuous_const
    (HasCompactSupport.intro' isCompact_univ isClosed_univ (fun x hx => (hx trivial).elim))
  simp only [integral_const, smul_eq_mul, mul_one] at this
  rw [this, mul_comm]

theorem w1_weil : J.μG.real Set.univ = J.m.real Set.univ * J.μUH.real Set.univ := by
  haveI : Finite ↥(L0 (F := F)).SOV := Finite.of_subsingleton
  have := J.hm (fun _ => 1) continuous_const
    (HasCompactSupport.intro' isCompact_univ isClosed_univ (fun x hx => (hx trivial).elim))
  simp only [integral_const, smul_eq_mul, mul_one] at this
  rw [this, mul_comm]

theorem w1_extV (f : ↥(L0 (F := F)).soV → ℂ) (X : (L0 (F := F)).EndV) (hX : X ∈ (L0 (F := F)).soV) :
    (L0 (F := F)).extV f X = f 0 := by
  unfold LuoDatum.extV
  rw [dif_pos hX]; congr 1; exact Subsingleton.elim _ _

theorem w1_Ig (θ : ↥(L0 (F := F)).soW → ℂ) (f : ↥(L0 (F := F)).soV → ℂ) (g : ↥(L0 (F := F)).SOV) :
    J.Ig θ f g = (J.μ𝔥.real Set.univ : ℂ) * ((J.μ𝔲.real Set.univ : ℂ) * (θ 0 * f 0)) := by
  unfold W1Input.Ig LuoDatum.Ig LuoDatum.fXi
  rw [integral_of_subsingleton _ _ 0, Complex.real_smul]
  congr 1
  rw [integral_of_subsingleton _ _ 0, Complex.real_smul]
  have hxi : (L0 (F := F)).xiArg J.ξc ((L0 (F := F)).asV ((0 : ↥(L0 (F := F)).lieU) : (L0 (F := F)).EndV)) = 0 := by
    unfold LuoDatum.xiArg
    exact Finset.sum_eq_zero (fun i _ => (Fin.elim0 i))
  rw [hxi, NontrivialAddChar.map_zero, mul_one]
  rw [w1_extV f _ (by
    rw [w1_SOV_eq_one g]
    simp only [ZeroMemClass.coe_zero, add_zero, map_zero]
    simp [LuoDatum.ofV]
    exact (L0 (F := F)).soV.zero_mem)]
  ring

/-- `I_N(θ, f) = κ_N(1) μ_G(G) θ(0) f(0)` at `L0`. -/
theorem w1_IN (θ : ↥(L0 (F := F)).soW → ℂ) (f : ↥(L0 (F := F)).soV → ℂ) (N : ℕ) :
    J.IN θ f N = (J.μG.real Set.univ : ℂ) * (θ 0 * f 0) *
      (L0 (F := F)).kappa J.ϖ J.R0 J.cZ N 1 := by
  unfold W1Input.IN
  rw [integral_of_subsingleton _ _ q0, Complex.real_smul, w1_Ig,
    w1_SOV_eq_one (CosetSpace.out _ q0), w1_weil, w1_muUH, w1_mu𝔥, w1_mu𝔲]
  push_cast; ring

end


section GenericGerm
variable {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A]
  [IsModuleTopology F A]

/-- On a zero Lie algebra, every germ of every function at the only point is its value at `0`. -/
theorem germLie_of_subsingleton (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A) [hs : Subsingleton ↥𝔤]
    (b : LinearMap.BilinForm F A) (ψ : NontrivialAddChar F) (θ : ↥𝔤 → ℂ) {X : A} (hX : X ∈ 𝔤)
    (O : NilOrbit (lieGrpCentralizer G X) (lieCentralizer 𝔤 X)) :
    germLie G 𝔤 b ψ θ X O = θ 0 := by
  haveI hc : Subsingleton ↥(lieCentralizer 𝔤 X) :=
    ⟨fun a b => Subtype.ext (congrArg Subtype.val
      (Subsingleton.elim (α := ↥𝔤) ⟨(a : A), (mem_lieCentralizer.1 a.2).1⟩
        ⟨(b : A), (mem_lieCentralizer.1 b.2).1⟩) :)⟩
  haveI hc2 : ∀ Y, Subsingleton ↥(lieCentralizer (lieCentralizer 𝔤 X) Y) := fun Y =>
    ⟨fun a b => Subtype.ext (congrArg Subtype.val
      (Subsingleton.elim (α := ↥(lieCentralizer 𝔤 X))
        ⟨(a : A), (mem_lieCentralizer.1 a.2).1⟩ ⟨(b : A), (mem_lieCentralizer.1 b.2).1⟩) :)⟩
  haveI hO : Subsingleton (NilOrbit (lieGrpCentralizer G X) (lieCentralizer 𝔤 X)) := by
    refine ⟨fun a b => ?_⟩
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        have : a = b := Subtype.ext (congrArg Subtype.val
          (Subsingleton.elim (α := ↥(lieCentralizer 𝔤 X)) ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩) :)
        rw [this]
  have hreg : ∀ Z : ↥(lieCentralizer 𝔤 X), IsRegularSS (lieCentralizer 𝔤 X) (Z : A) := by
    intro Z
    have hZ : (Z : A) = 0 := congrArg Subtype.val (Subsingleton.elim Z 0)
    rw [hZ]
    exact ⟨isSS_zero F, ⟨fun a b => Subsingleton.elim _ _⟩⟩
  have hj : ∀ {Y : A}, Y ∈ lieCentralizer 𝔤 X → ∀ O',
      jHat (lieGrpCentralizer G X) (lieCentralizer 𝔤 X) b ψ O' Y = 1 := by
    intro Y hY O'
    rw [Subsingleton.elim O' (zeroOrbit _ _)]
    exact jHat_zeroOrbit_eq_one _ _ _ ψ ⟨_, isSelfDual_dirac_zero _ ψ⟩ hreg hY
  have hE : HasGermExpansionLie G 𝔤 b ψ θ X (fun _ => θ 0) := by
    refine ⟨Set.toFinite _, Set.univ, Filter.univ_mem, fun Y _ hY _ Z _ => ?_⟩
    rw [finsum_eq_single _ (zeroOrbit _ _) (fun O hO => (hO (Subsingleton.elim _ _)).elim),
      hj hY, mul_one, Subsingleton.elim Z 0]
  have hcoef : ∀ c, HasGermExpansionLie G 𝔤 b ψ θ X c → c O = θ 0 := by
    intro c hc'
    obtain ⟨-, ω, hω, h⟩ := hc'
    have h0 : (0 : A) ∈ lieCentralizer 𝔤 X := zero_mem _
    have := h 0 (mem_of_mem_nhds hω) h0 (hreg 0) ⟨X, hX⟩ (by simp)
    rw [finsum_eq_single _ O (fun O' hO' => (hO' (Subsingleton.elim _ _)).elim), hj h0, mul_one,
      Subsingleton.elim (⟨X, hX⟩ : ↥𝔤) 0] at this
    exact this.symm
  have hreg' : O ∈ NilReg (lieGrpCentralizer G X) (lieCentralizer 𝔤 X) := by
    refine ⟨(Quotient.out O).2.1, (Quotient.out O).2.2, ?_⟩
    unfold lieRank
    simp only [Module.finrank_zero_of_subsingleton, ciInf_const]
  unfold germLie
  rw [ite_eq_left (by exact hreg'), dite_eq_left ⟨_, hE⟩]
  exact hcoef _ (Exists.choose_spec ⟨_, hE⟩)

end GenericGerm

section Geom
variable {ψ : NontrivialAddChar F}

instance w1_sub_EndWu : Subsingleton (L0 (F := F)).EndWˣ :=
  ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩

theorem w1_cTheta (θ : ↥(L0 (F := F)).soW → ℂ) : (L0 (F := F)).cThetaW ψ θ 0 = θ 0 :=
  germLie_of_subsingleton _ _ _ ψ θ (zero_mem _) _

theorem w1_cF (τ : ↥(L0 (F := F)).soV → ℂ) : (L0 (F := F)).cFW ψ τ 0 = τ 0 :=
  germLie_of_subsingleton _ _ _ ψ τ (Eq.subst (motive := fun x => x ∈ (L0 (F := F)).soV)
    (map_zero (L0 (F := F)).extLie).symm (L0 (F := F)).soV.zero_mem) _

theorem w1_aniso : (L0 (F := F)).anisoDim ((L0 (F := F)).V2sub 0) = 1 := by
  have htop : (L0 (F := F)).V2sub 0 = ⊤ := by
    unfold LuoDatum.V2sub
    rw [show LinearMap.ker ((L0 (F := F)).asW 0) = ⊤ from LinearMap.ker_zero, Submodule.prod_top]
  unfold LuoDatum.anisoDim
  rw [htop, finrank_top, L0_finrank_V]
  rw [wittIndex_eq_zero_of_anisotropic]
  intro v hv
  have h0 : ((v : (L0 (F := F)).V).2 0) * ((v : (L0 (F := F)).V).2 0) = 0 := by
    rw [← L0_QV_apply]; exact hv
  have h1 : (v : (L0 (F := F)).V).2 0 = 0 := mul_self_eq_zero.mp h0
  apply Subtype.ext
  rw [L0_line (F := F) (v : (L0 (F := F)).V), h1, zero_smul]
  rfl

theorem w1_isW1Elt : (L0 (F := F)).IsW1Elt 0 := by
  refine ⟨zero_mem _, isSS_zero F, fun a _ b _ => Subsingleton.elim _ _, ?_, ?_⟩
  · haveI : Finite ↥((L0 (F := F)).torusH 0) := Finite.of_subsingleton
    infer_instance
  · unfold LuoDatum.Cond4
    rw [if_neg (by rw [L0_finrank_V]; decide)]
    exact w1_aniso

instance : Subsingleton (L0 (F := F)).W1Torus :=
  ⟨fun a b => Subtype.ext (Subsingleton.elim (α := Subgroup (L0 (F := F)).EndWˣ) _ _)⟩

def w1Torus0 : (L0 (F := F)).W1Torus := ⟨_, 0, w1_isW1Elt, rfl⟩

instance : Subsingleton (L0 (F := F)).W1Class := by
  refine ⟨fun a b => ?_⟩
  induction a using Quot.ind
  induction b using Quot.ind
  congr 1
  exact Subsingleton.elim _ _

theorem w1_weyl (T : Subgroup (L0 (F := F)).EndWˣ) : (L0 (F := F)).weylW1 T = 1 := by
  unfold LuoDatum.weylW1
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
  induction a using QuotientGroup.induction_on
  induction b using QuotientGroup.induction_on
  congr 1
  exact Subsingleton.elim _ _

instance w1_sub_lieTorus (T : Subgroup (L0 (F := F)).EndWˣ) :
    Subsingleton ↥((L0 (F := F)).lieTorusW T) :=
  ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩

theorem w1_muT (J : (L0 (F := F)).W1Input ψ) (T : (L0 (F := F)).W1Torus) :
    (J.μT T).real Set.univ = 1 := by
  have h := J.hμT T
  letI : MeasurableSpace ↥T.1 := borel _
  haveI : BorelSpace ↥T.1 := ⟨rfl⟩
  obtain ⟨-, U, hU, hS⟩ := h
  have hsub : Set.univ ⊆ U := fun y _ => by
    rw [Subsingleton.elim y 0]; exact mem_of_mem_nhds hU
  haveI : Finite ↥T.1 := Finite.of_subsingleton
  have e := hS Set.univ MeasurableSet.univ hsub
  have hset : {t : ↥T.1 | ∃ X ∈ (Set.univ : Set ↥((L0 (F := F)).lieTorusW T.1)),
      ((t : (L0 (F := F)).EndWˣ) : (L0 (F := F)).EndW) = expA F (X : (L0 (F := F)).EndW)} =
      Set.univ := by
    ext t
    simp only [Set.mem_univ, true_and, iff_true]
    refine ⟨0, ?_⟩
    exact Subsingleton.elim _ _
  rw [hset] at e
  rw [measureReal_def, e]
  have := probHaar_real_univ ↥T.1
  rwa [measureReal_def] at this

theorem w1_isNat (T : Subgroup (L0 (F := F)).EndWˣ) : (L0 (F := F)).IsNatW T 0 := by
  refine ⟨zero_mem _, Subsingleton.elim _ _, ?_⟩
  rw [charpoly_eq_one_of_subsingleton]
  exact squarefree_one

theorem w1_weylDisc : weylDiscLie (L0 (F := F)).soW 0 = 1 := by
  unfold weylDiscLie
  rw [dite_eq_left (fun Y _ => by simp)]
  haveI : Subsingleton ↥(L0 (F := F)).soW.toSubmodule :=
    inferInstanceAs (Subsingleton ↥(L0 (F := F)).soW)
  rw [charpoly_eq_one_of_subsingleton, Polynomial.trailingCoeff, Polynomial.natTrailingDegree_one,
    AddMonoidAlgebra.coeff_one_zero, absF_one']

/-- `I(θ, τ) = θ(0) τ(0)` at `L0`, for every `W1Input`. -/
theorem w1_Igeom (J : (L0 (F := F)).W1Input ψ) (θ : ↥(L0 (F := F)).soW → ℂ)
    (τ : ↥(L0 (F := F)).soV → ℂ) : J.Igeom θ τ = θ 0 * τ 0 := by
  unfold W1Input.Igeom LuoDatum.Igeom
  have hsingle := tsum_eq_single (L := SummationFilter.unconditional (L0 (F := F)).W1Class)
    (f := fun c : (L0 (F := F)).W1Class =>
      (((L0 (F := F)).weylW1 (Quot.out c).1 : ℂ))⁻¹ *
        ∫ Y : ↥((L0 (F := F)).lieTorusW (Quot.out c).1),
          (L0 (F := F)).geomIntegrand ψ θ τ (Quot.out c).1 Y ∂J.μT (Quot.out c))
    (Quot.mk _ w1Torus0) fun c hc => (hc (Subsingleton.elim _ _)).elim
  rw [hsingle]
  rw [w1_weyl, Nat.cast_one, inv_one, one_mul, integral_of_subsingleton _ _ 0, w1_muT, one_smul]
  unfold LuoDatum.geomIntegrand
  rw [ZeroMemClass.coe_zero, if_pos (w1_isNat _), w1_weylDisc, w1_cTheta, w1_cF]
  have hr : (L0 (F := F)).r = 0 := rfl
  simp [hr]

/-- `τ(0) = μ_G(G) f(0)` at `L0`. -/
theorem w1_tau (μG : Measure ↥(L0 (F := F)).SOV) (f τ : ↥(L0 (F := F)).soV → ℂ)
    (hτ : (L0 (F := F)).IsThetaFW1 ψ μG f τ) : τ 0 = (μG.real Set.univ : ℂ) * f 0 := by
  haveI : Finite ↥(L0 (F := F)).soV := Finite.of_subsingleton
  have h := hτ.2.2.2 (fun _ => 1) ⟨IsLocallyConstant.const 1,
    HasCompactSupport.intro' isCompact_univ isClosed_univ (fun x hx => (hx trivial).elim)⟩
  have hsd : selfDualHaar (L0 (F := F)).soV (L0 (F := F)).bV ψ = Measure.dirac 0 :=
    selfDualMeasure_eq_dirac_zero _ ψ
  rw [hsd, integral_of_subsingleton _ _ 0, integral_of_subsingleton _ _ 1] at h
  rw [integral_of_subsingleton _ _ 0] at h
  rw [w1_extV f _ (by rw [w1_SOV_eq_one 1]; simp)] at h
  simp at h
  rw [h]

end Geom

section Kappa
variable {ψ : NontrivialAddChar F} (J : (L0 (F := F)).W1Input ψ)

theorem w1_zV0_mem : (L0 (F := F)).zV 0 ∈ (L0 (F := F)).V0sub :=
  Submodule.mem_prod.2 ⟨Submodule.mem_top, Submodule.mem_span_singleton_self _⟩

theorem w1_V0_aniso (v : ↥(L0 (F := F)).V0sub)
    (hv : ((L0 (F := F)).QV.comp (L0 (F := F)).V0sub.subtype) v = 0) : v = 0 := by
  have h0 : ((v : (L0 (F := F)).V).2 0) * ((v : (L0 (F := F)).V).2 0) = 0 := by
    rw [← L0_QV_apply]; exact hv
  have h1 : (v : (L0 (F := F)).V).2 0 = 0 := mul_self_eq_zero.mp h0
  apply Subtype.ext
  rw [L0_line (F := F) (v : (L0 (F := F)).V), h1, zero_smul]
  rfl

/-- At `L0` the special lattice `R₀` contains `ϖ^N z₀` for `N` large. -/
theorem w1_R0_eventually : ∀ᶠ N : ℕ in atTop,
    (J.ϖ ^ N • (⟨_, w1_zV0_mem⟩ : ↥(L0 (F := F)).V0sub)) ∈ J.R0 := by
  obtain ⟨Uan, n, w, c, hanis, hgram, horth, hspan, hc, hR⟩ := J.hR0
  set Q := (L0 (F := F)).QV.comp (L0 (F := F)).V0sub.subtype with hQ
  have hn : n = 0 := by
    by_contra hn
    have h1 : (1 : ℤ) ≤ |(1 : ℤ)| := by simp
    have h2 : |(1 : ℤ)| ≤ n := by simp; omega
    have h3 : (1 : ℤ) ≤ |(-1 : ℤ)| := by simp
    have h4 : |(-1 : ℤ)| ≤ n := by simp; omega
    have e11 := hgram 1 1 h1 h2 h1 h2
    have e1m := hgram 1 (-1) h1 h2 h3 h4
    rw [if_neg (by norm_num), QuadraticMap.associated_eq_self_apply] at e11
    have hw : w 1 = 0 := w1_V0_aniso _ e11
    rw [if_pos (by norm_num), hw, map_zero, LinearMap.zero_apply] at e1m
    exact zero_ne_one e1m
  subst hn
  have hUan : Uan = ⊤ := by
    have hset : {i : ℤ | 1 ≤ |i| ∧ |i| ≤ ((0 : ℕ) : ℤ)} = ∅ := by
      ext i; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2; push_cast at h2; omega
    rw [hset, Set.image_empty, Submodule.span_empty, bot_sup_eq] at hspan
    exact hspan
  set z : ↥(L0 (F := F)).V0sub := ⟨_, w1_zV0_mem⟩
  obtain ⟨hpos, hlt, -⟩ := J.hϖ
  have hcpos : 0 < absF J.ϖ ^ c := zpow_pos hpos c
  have ht : Tendsto (fun N : ℕ => absF J.ϖ ^ (2 * N) * absF (⅟(2 : F) * Q z)) atTop
      (𝓝 (0 * absF (⅟(2 : F) * Q z))) := by
    refine Tendsto.mul_const _ ?_
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (absF_nonneg J.ϖ) hlt
    exact this.comp (tendsto_id.const_mul_atTop' (by norm_num : (0 : ℕ) < 2))
  rw [zero_mul] at ht
  filter_upwards [ht.eventually (gt_mem_nhds hcpos)] with N hN
  rw [hR]
  refine ⟨Fin.elim0, Fin.elim0, J.ϖ ^ N • z, fun i => i.elim0, fun i => i.elim0,
    by rw [hUan]; exact Submodule.mem_top, ?_, by simp⟩
  rw [QuadraticMap.map_smul, smul_eq_mul, ← mul_assoc, mul_comm (⅟(2 : F)), mul_assoc,
    absF_mul, ← pow_add, absF_pow, ← two_mul]
  exact hN.le

/-- `κ_N(1) = 1` for `N` large at `L0`. -/
theorem w1_kappa_eventually : ∀ᶠ N : ℕ in atTop,
    (L0 (F := F)).kappa J.ϖ J.R0 J.cZ N 1 = 1 := by
  filter_upwards [w1_R0_eventually J] with N hN
  have hϖ0 : J.ϖ ≠ 0 := fun h => by
    have := J.hϖ.1; rw [h, absF_zero] at this; exact lt_irrefl _ this
  unfold LuoDatum.kappa
  rw [if_pos]
  refine ⟨1, ⟨(SOu (L0 (F := F)).QV).one_mem, fun k hk => (Nat.not_lt_zero k hk).elim,
    fun v _ => by
      show v - v ∈ _
      rw [sub_self]; exact zero_mem _⟩, 1, ⟨(L0 (F := F)).SOV.one_mem, fun v _ => rfl,
    fun i h1 h2 => by exfalso; have : (L0 (F := F)).r = 0 := rfl; rw [this] at h2; push_cast at h2; omega⟩,
    1, ⟨(L0 (F := F)).SOV.one_mem, fun v _ => rfl, _, hN, ?_⟩,
    1, ⟨(L0 (F := F)).SOV.one_mem, by
      show (fun v => v) '' _ = _
      exact Set.image_id' _⟩, by simp⟩
  show (L0 (F := F)).zV 0 = J.ϖ ^ (-(N : ℤ)) • (J.ϖ ^ N • (L0 (F := F)).zV 0)
  rw [smul_smul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hϖ0), one_smul]

/-- **Both sides of `waldspurger2010_thm_7_9` at `L0` (W = 0, V a line)**, without the axiom:
`I_N(θ, f) → μ_G(G) θ(0) f(0) = I(θ, τ)` for every `W1Input`, every `θ`, `f`, and every `τ`
satisfying `IsThetaFW1`. -/
theorem w1_conclusion_L0 (θ : ↥(L0 (F := F)).soW → ℂ) (f τ : ↥(L0 (F := F)).soV → ℂ)
    (hτ : (L0 (F := F)).IsThetaFW1 ψ J.μG f τ) :
    Tendsto (J.IN θ f) atTop (𝓝 (J.Igeom θ τ)) := by
  rw [w1_Igeom, w1_tau J.μG f τ hτ]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [w1_kappa_eventually J] with N hN
  rw [w1_IN, hN]; ring

end Kappa

section Hyps
variable {ψ : NontrivialAddChar F}

/-- Every function on a zero Lie algebra is a quasi-character. -/
theorem isLieQC_of_subsingleton {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A]
    [TopologicalSpace A] [IsModuleTopology F A] (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A)
    [Subsingleton ↥𝔤] (b : LinearMap.BilinForm F A) (θ : ↥𝔤 → ℂ) :
    IsLieQuasiCharacter G 𝔤 b ψ θ := by
  refine ⟨fun _ _ Y Z _ _ => congrArg θ (Subsingleton.elim _ _), fun X _ => ?_⟩
  have hX : (X : A) = 0 := congrArg Subtype.val (Subsingleton.elim X 0)
  -- the expansion `c ≡ θ 0` from the generic germ lemma's proof
  haveI hc : Subsingleton ↥(lieCentralizer 𝔤 (X : A)) :=
    ⟨fun a b => Subtype.ext (congrArg Subtype.val
      (Subsingleton.elim (α := ↥𝔤) ⟨(a : A), (mem_lieCentralizer.1 a.2).1⟩
        ⟨(b : A), (mem_lieCentralizer.1 b.2).1⟩) :)⟩
  haveI hO : Subsingleton (NilOrbit (lieGrpCentralizer G (X : A)) (lieCentralizer 𝔤 (X : A))) := by
    refine ⟨fun a b => ?_⟩
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        have : a = b := Subtype.ext (congrArg Subtype.val
          (Subsingleton.elim (α := ↥(lieCentralizer 𝔤 (X : A))) ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩) :)
        rw [this]
  haveI hc2 : ∀ Y, Subsingleton ↥(lieCentralizer (lieCentralizer 𝔤 (X : A)) Y) := fun Y =>
    ⟨fun a b => Subtype.ext (congrArg Subtype.val
      (Subsingleton.elim (α := ↥(lieCentralizer 𝔤 (X : A)))
        ⟨(a : A), (mem_lieCentralizer.1 a.2).1⟩ ⟨(b : A), (mem_lieCentralizer.1 b.2).1⟩) :)⟩
  have hreg : ∀ Z : ↥(lieCentralizer 𝔤 (X : A)), IsRegularSS (lieCentralizer 𝔤 (X : A)) (Z : A) := by
    intro Z
    have hZ : (Z : A) = 0 := congrArg Subtype.val (Subsingleton.elim Z 0)
    rw [hZ]
    exact ⟨isSS_zero F, ⟨fun a b => Subsingleton.elim _ _⟩⟩
  refine ⟨fun _ => θ 0, Set.toFinite _, Set.univ, Filter.univ_mem, fun Y _ hY _ Z _ => ?_⟩
  rw [finsum_eq_single _ (zeroOrbit _ _) (fun O hO => (hO (Subsingleton.elim _ _)).elim),
    jHat_zeroOrbit_eq_one _ _ _ ψ ⟨_, isSelfDual_dirac_zero _ ψ⟩ hreg hY, mul_one,
    Subsingleton.elim Z 0]

/-- At `L0` every test function is very cuspidal (there is no proper parabolic). -/
theorem w1_isVeryCuspidal (f : ↥(L0 (F := F)).soV → ℂ) (hf : IsTestFn f) :
    (L0 (F := F)).IsVeryCuspidal f := by
  refine ⟨hf, fun FV hFV => ?_⟩
  exfalso
  obtain ⟨g, hg, hne⟩ := hFV
  apply hne
  intro i
  have h1 : (L0 (F := F)).asV ((g : (L0 (F := F)).EndVˣ) : (L0 (F := F)).EndV) = 1 :=
    L0_SO_trivial (F := F) hg
  rw [h1]
  rintro x ⟨y, hy, rfl⟩
  exact hy

/-- At `L0`, `τ ≡ μ_G(G) f(0)` satisfies `IsThetaFW1` for every `f`. -/
theorem w1_isThetaFW1 (μG : Measure ↥(L0 (F := F)).SOV) (f : ↥(L0 (F := F)).soV → ℂ) :
    (L0 (F := F)).IsThetaFW1 ψ μG f (fun _ => (μG.real Set.univ : ℂ) * f 0) := by
  have hsd : selfDualHaar (L0 (F := F)).soV (L0 (F := F)).bV ψ = Measure.dirac 0 :=
    selfDualMeasure_eq_dirac_zero _ ψ
  refine ⟨isLieQC_of_subsingleton _ _ _ _, by rw [hsd]; exact (integrable_const _).locallyIntegrable,
    continuousOn_const, fun f' _ => ?_⟩
  rw [hsd, integral_of_subsingleton _ _ 0, integral_of_subsingleton _ _ 1,
    integral_of_subsingleton _ _ 0]
  rw [w1_extV f _ (by rw [w1_SOV_eq_one 1]; simp)]
  simp; ring

end Hyps

end GSpinGGP.AxiomRedTeam
