/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Interface
import GSpinGGP.GGP.Descent

/-!
# The Lie-algebra theorems of Waldspurger 2010 and Luo (cited)

This file holds the *definitions* of the Lie-algebra objects on
`𝔤⁰ = so(W) ⊕ so(V)` that the two cited theorems mention, followed by the two literature axioms.
(The definitions live here, not in `TraceFormula/Lie.lean`, because the axioms must mention them
and `Lie.lean` imports this file.)  All definitions are real definitions; measures and functions
that are pinned only by a property are chosen by the epsilon pattern, as elsewhere in the project.

## Definitions (§1–§6)

* `lieZero d`: `𝔤⁰ = so(W) ⊕ so(V)` as a Lie subalgebra of `C(W) × C(V)` (Thesis §5.2;
  `lie0`, `lie_eq_center_sup_lie0`).  `G(F)` acts on it by conjugation
  (`adLie0`), through `Ḡ(F) = SO(W)(F) × SO(V)(F)` (`conj_lie0_factors`).
* `lieFlagUnip`, `lieH0`, `lamLie`: `𝔫 = Lie(N)`, `𝔥⁰ = 𝔥 ∩ 𝔤⁰ = so(W) ⊕ 𝔫` (with `so(W)`
  diagonal) and the linear form `λ` on `𝔥⁰` with `ξ(X) = ψ(λ(X))` (Thesis §5.2, §11.1; Luo §2.1).
* `measH0`: the Haar measure on `𝔥⁰(F)` compatible through `exp` with `Measure.haar` on
  `H(F)/A_{G,H}(F)` (BP §1.6, `j^H = 1` near `0`).
* `distribJLie`: `J^Lie(f) = ∫_{H\G/A_G} ∫_{𝔥⁰} f(x⁻¹Xx) ξ(X) dX dx` (Thesis §10.1;
  Luo §4, BP §8.1), with the Weil measure `weilMeasureHG` of `J`.
* `IsLieScusp`: strongly cuspidal Schwartz–Bruhat functions on `𝔤⁰(F)` (Thesis §4.5, BP §5.1).
* `HasGermExpansionLie`, `IsLieQuasiCharacter`, `germLie`: quasi-characters on `𝔤⁰(F)` and their
  germs `c_{θ,O}(X)` (Thesis §4.1.1, §4.2; BP §4.1, §4.5), with `ĵ` of `(G_X, 𝔤⁰_X)`.
* `IsThetaFLie`, `thetaFLie`: the quasi-character `θ_f` of `f ∈ S_scusp(𝔤⁰(F))`, defined like
  `thetaF` by the orbital pairing `∫_{G/A_G} ∫_{𝔤⁰} f(x⁻¹Xx) f'(X) dX dx` (BP §5.5, §5.6).
* `mGeomLieS`, `mGeomLie`: `m^Lie_geom(θ) = lim_{s→0⁺} ∫_{Γ^Lie(G,H)} D^G(X)^{1/2}
  c_{θ,O_X}(X) Δ(X)^{s-1/2} dX` (Thesis Prop 12.1.1(iii)):
  the same tori `T` as `mGeom` (`GammaClass d`), with `𝔱⁰ = Lie(T/A_{G,H})` (`lieTorus`) and the
  measure on `𝔱⁰(F)` compatible through `exp` with the probability measure on `T(F)/A_{G,H}(F)`.

## The axioms (§7)

The two cited theorems are stated on `𝔤⁰` for triples **without a hyperbolic-plane factor**:
`¬ IsHypPlane d.QW` and `¬ IsHypPlane d.QV`.  Then `Ā_G = 1` (`AGbar_eq_bot`) and
`H(F)\G(F)/A_G(F) ≃ H̄(F)\Ḡ(F)` (`quotHG_equiv_SO`), so `J^Lie`, `θ_f`, the germs and
`m^Lie_geom` above are literally the objects of the special orthogonal triple `(Ḡ, H̄, ξ)` of
Waldspurger 2010 and Luo.  The exclusion is needed: both sources
integrate over `H̄(F)\Ḡ(F)` with no quotient by a central torus (Luo §4, definition of `J` and
`J^Lie`; Waldspurger 2010 §7.2–7.9), and when `W` (or `V`) is a hyperbolic plane `Ḡ` has the split
centre `A_Ḡ ≅ SO(2) ≅ G_m`, which acts trivially on `𝔤⁰` and freely on `H̄\Ḡ`, so the integral
over `H̄\Ḡ` is `0` or divergent.  The triples with a hyperbolic-plane factor are treated
separately in `TraceFormula/Lie.lean`.

Normalization: as for `J` and `m_geom`, nothing depends on a choice of Haar measure
except through the one measure `Measure.haar` on `G(F)/A_G(F)`: `J^Lie` and `θ_f^Lie` both scale
with it; the measure on `H(F)/A_{G,H}(F)` cancels in `J^Lie` (it fixes both `measH0` and
`weilMeasureHG`); the germs and `m^Lie_geom` are pinned by `ψ`, the trace form and probability
measures.  The constant in the Weyl-integration step relating `θ_f` to BP's weighted orbital
integrals is `1` (BP §1.7).
-/

noncomputable section

open MeasureTheory Topology Filter Module

/- The commutator Lie structure on associative algebras is only a local instance in Mathlib. -/
attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

/-! ## 1. `𝔤⁰ = so(W) ⊕ so(V)` and the adjoint action -/

/-- **`𝔤⁰ = so(W) ⊕ so(V)`** (Thesis §5.2): the Lie algebra of
`Ḡ = SO(W) × SO(V)`, the traceless part of `𝔤 = gspin(W) × gspin(V)`, with `𝔤 = 𝔷 ⊕ 𝔤⁰`
(`lie_eq_center_sup_lie0`, `disjoint_lieCenter_lie0`).  When `W` or `V` is a hyperbolic plane,
`𝔤⁰` has the nonzero centre `Lie(A_Ḡ)` (reductive, not semisimple). -/
def lieZero : LieSubalgebra F d.ambient :=
  { d.lie0 with
    lie_mem' := fun {X Y} hX hY => by
      rw [Ring.lie_def]
      exact d.lie0_lie_mem hX hY }

theorem mem_lieZero {X : d.ambient} : X ∈ d.lieZero ↔ X ∈ d.lie0 := Iff.rfl

theorem lieZero_le_lie : d.lieZero ≤ d.lie := fun _ hX => d.lie0_le_lie hX

/-- `Ad(g) X = g X g⁻¹` on `𝔤⁰` (it factors through `Ḡ(F)`, `conj_lie0_factors`). -/
def adLie0 (g : ↥d.G) (X : ↥d.lieZero) : ↥d.lieZero :=
  ⟨((g : d.ambientˣ) : d.ambient) * X * (((g : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient),
    d.conj_mem_lie0 g X.2⟩

@[simp] theorem coe_adLie0 (g : ↥d.G) (X : ↥d.lieZero) :
    ((d.adLie0 g X : ↥d.lieZero) : d.ambient) =
      ((g : d.ambientˣ) : d.ambient) * X * (((g : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) := rfl

end GGPData

/-! ## 2. `𝔫`, `𝔥⁰` and `ξ` on `𝔥⁰` -/

section Flag

variable {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]

theorem lieAlg_adV_add (Q : QuadraticForm F V) (X Y : CliffordAlgebra Q) (v : V) :
    adV Q (X + Y) v = adV Q X v + adV Q Y v := by
  simp [adV, add_mul, mul_add, sub_add_sub_comm]

theorem lieAlg_adV_smul (Q : QuadraticForm F V) (c : F) (X : CliffordAlgebra Q) (v : V) :
    adV Q (c • X) v = c • adV Q X v := by
  simp [adV, smul_sub]

theorem lieAlg_adV_zero (Q : QuadraticForm F V) (v : V) : adV Q 0 v = 0 := by
  simp [adV]

/-- **`𝔫_F = Lie(N_F)`**, the nilpotent radical of the parabolic subalgebra stabilizing an
isotropic flag `0 = Z_0 ⊂ Z_1 ⊂ … ⊂ Z_k` (Thesis §5.1.2, §5.2): the `X ∈ so(V)` with
`X Z_{i+1} ⊆ Z_i` and `X (Z_k^⊥) ⊆ Z_k` (the Lie-algebra form of `flagUnipSO`). -/
def lieFlagUnip {Q : QuadraticForm F V} (Fl : IsotropicFlag Q) :
    Submodule F (CliffordAlgebra Q) where
  carrier := {X | X ∈ soSub Q ∧
    (∀ i : Fin Fl.len, ∀ v ∈ Fl.sub i.succ, adV Q X v ∈ Fl.sub i.castSucc) ∧
    ∀ v ∈ (bform Q).orthogonal Fl.top, adV Q X v ∈ Fl.top}
  add_mem' := by
    rintro X Y ⟨hX0, hX1, hX2⟩ ⟨hY0, hY1, hY2⟩
    refine ⟨(soSub Q).add_mem hX0 hY0, fun i v hv => ?_, fun v hv => ?_⟩
    · have e : adV Q (X + Y) v = adV Q X v + adV Q Y v := by
        simp [adV, add_mul, mul_add, sub_add_sub_comm]
      rw [e]; exact add_mem (hX1 i v hv) (hY1 i v hv)
    · have e : adV Q (X + Y) v = adV Q X v + adV Q Y v := by
        simp [adV, add_mul, mul_add, sub_add_sub_comm]
      rw [e]; exact add_mem (hX2 v hv) (hY2 v hv)
  zero_mem' := ⟨(soSub Q).zero_mem, fun i v _ => by simp [adV], fun v _ => by simp [adV]⟩
  smul_mem' := by
    rintro c X ⟨hX0, hX1, hX2⟩
    have e : ∀ v, adV Q (c • X) v = c • adV Q X v := fun v => by
      simp [adV, smul_sub]
    refine ⟨(soSub Q).smul_mem c hX0, fun i v hv => ?_, fun v hv => ?_⟩
    · rw [e]; exact Submodule.smul_mem _ c (hX1 i v hv)
    · rw [e]; exact Submodule.smul_mem _ c (hX2 v hv)

/-- **`𝔭⁰_F`**, the Lie algebra of the stabilizer of the flag in `SO(V)`: `X ∈ so(V)` with
`X Z_i ⊆ Z_i` for every `i` (Thesis §5.1.2). -/
def lieFlagStab {Q : QuadraticForm F V} (Fl : IsotropicFlag Q) :
    Submodule F (CliffordAlgebra Q) where
  carrier := {X | X ∈ soSub Q ∧ ∀ i, ∀ v ∈ Fl.sub i, adV Q X v ∈ Fl.sub i}
  add_mem' := by
    rintro X Y ⟨hX0, hX1⟩ ⟨hY0, hY1⟩
    refine ⟨(soSub Q).add_mem hX0 hY0, fun i v hv => ?_⟩
    have e : adV Q (X + Y) v = adV Q X v + adV Q Y v := by
      simp [adV, add_mul, mul_add, sub_add_sub_comm]
    rw [e]; exact add_mem (hX1 i v hv) (hY1 i v hv)
  zero_mem' := ⟨(soSub Q).zero_mem, fun i v _ => by simp [adV]⟩
  smul_mem' := by
    rintro c X ⟨hX0, hX1⟩
    refine ⟨(soSub Q).smul_mem c hX0, fun i v hv => ?_⟩
    have e : adV Q (c • X) v = c • adV Q X v := by simp [adV, smul_sub]
    rw [e]; exact Submodule.smul_mem _ c (hX1 i v hv)

end Flag

namespace GGPData

variable (d : GGPData F)

/-- The diagonal embedding `so(W) → so(W) ⊕ so(V)` on the Clifford level, `X ↦ (X, X)`
(`C(W) → C(V)` induced by `W ⊆ V`), the Lie-algebra form of `diag`. -/
def diagLie (X : CliffordAlgebra d.QW) : d.ambient :=
  (X, CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ) X)

/-- **`𝔥⁰ = 𝔥 ∩ 𝔤⁰ = so(W) ⊕ 𝔫`** (Thesis §5.2): the `X = (X_W, X_V) ∈ 𝔤⁰` with
`X_V − X_W ∈ 𝔫` (`X_W` embedded diagonally), the Lie algebra of `H̄ = SO(W) ⋉ N`. -/
def lieH0 : Submodule F d.ambient where
  carrier := {X | X ∈ d.lie0 ∧ X.2 - (d.diagLie X.1).2 ∈ lieFlagUnip d.flag}
  add_mem' := by
    rintro X Y ⟨hX0, hX1⟩ ⟨hY0, hY1⟩
    refine ⟨d.lie0.add_mem hX0 hY0, ?_⟩
    have e : (X + Y).2 - (d.diagLie (X + Y).1).2 =
        (X.2 - (d.diagLie X.1).2) + (Y.2 - (d.diagLie Y.1).2) := by
      simp only [diagLie, Prod.snd_add, Prod.fst_add, map_add]; abel
    rw [e]; exact add_mem hX1 hY1
  zero_mem' := ⟨d.lie0.zero_mem, by simp [diagLie]⟩
  smul_mem' := by
    rintro c X ⟨hX0, hX1⟩
    refine ⟨d.lie0.smul_mem c hX0, ?_⟩
    have e : (c • X).2 - (d.diagLie (c • X).1).2 = c • (X.2 - (d.diagLie X.1).2) := by
      simp only [diagLie, Prod.smul_snd, Prod.smul_fst, map_smul, smul_sub]
    rw [e]; exact Submodule.smul_mem _ c hX1

theorem lieH0_le_lie0 : d.lieH0 ≤ d.lie0 := fun _ hX => hX.1

/-- `𝔥⁰ → 𝔤⁰`. -/
def lieH0Incl (X : ↥d.lieH0) : ↥d.lieZero := ⟨X, d.lieH0_le_lie0 X.2⟩

/-- **`λ` on `𝔥⁰`** (Thesis §5.2, §11.1; Luo §2.1): `λ(X) = Σ_{i=0}^{r-1} b(z_{-i-1}, X z_i)`, the
differential of `lam`.  (The `so(W)`-component kills `Z`, so only the `𝔫`-component contributes.)
`ξ(X) = ψ(λ(X))`. -/
def lamLie (X : d.ambient) : F :=
  ∑ i : Fin d.r, bform d.QV (d.zV (-(i : ℤ) - 1)) (adV d.QV X.2 (d.zV (i : ℕ)))

/-- `ξ(X) = ψ(λ(X))` on `𝔥⁰(F)`. -/
def xiLie (ψ : NontrivialAddChar F) (X : d.ambient) : ℂ := ψ (d.lamLie X)

/-! ## 3. Measures and `J^Lie` -/

instance instMeasurableSpaceLieH0 : MeasurableSpace ↥d.lieH0 := borel _

instance instBorelSpaceLieH0 : BorelSpace ↥d.lieH0 := ⟨rfl⟩

/-- `μ` is the Haar measure on `𝔥⁰(F)` compatible through `exp` with `Measure.haar` on
`H(F)/A_{G,H}(F)` (BP §1.6: measures on a group and its Lie algebra correspond under `exp` with
Jacobian `j^H`, which is `1` on a neighbourhood of `0`; `𝔥 = Lie(A_{G,H}) ⊕ 𝔥⁰`): an
additive Haar measure such that on a neighbourhood `U` of `0`, every measurable
`S ⊆ U` has the measure of its image `{exp X : X ∈ S}` in `H(F)/A_{G,H}(F)`. -/
def IsExpCompatH (μ : Measure ↥d.lieH0) : Prop :=
  μ.IsAddHaarMeasure ∧
    ∃ U ∈ 𝓝 (0 : ↥d.lieH0), ∀ S : Set ↥d.lieH0, MeasurableSet S → S ⊆ U →
      μ S = (Measure.haar : Measure d.HmodAGH)
        {q | ∃ X ∈ S, ∃ h : ↥d.H, (((h : ↥d.G) : d.ambientˣ) : d.ambient) =
          expA F ((X : d.ambient)) ∧ q = (h : d.HmodAGH)}

open Classical in
/-- The measure `dX` on `𝔥⁰(F)` of `J^Lie` (epsilon; `0` if none). -/
def measH0 : Measure ↥d.lieH0 :=
  if h : ∃ μ, d.IsExpCompatH μ then h.choose else 0

variable (ψ : NontrivialAddChar F)

/-- `K^Lie(f, x) = ∫_{𝔥⁰(F)} f(x⁻¹ X x) ξ(X) dX` (Thesis §10.1; Luo §4; BP §8.1). -/
def kernelLie (f : ↥d.lieZero → ℂ) (x : ↥d.G) : ℂ :=
  ∫ X : ↥d.lieH0, f (d.adLie0 x⁻¹ (d.lieH0Incl X)) * d.xiLie ψ (X : d.ambient) ∂d.measH0

/-- **`J^Lie(f) = ∫_{H(F)\G(F)/A_G(F)} K^Lie(f, x) dx`** (Thesis §10.1;
Luo §4, BP §8.1), for the Weil quotient measure of `J` (`weilMeasureHG`),
integrating over the same coset representatives as `distribJ` (`K^Lie(f, ·)` is left
`H(F)`- and right `A_G(F)`-invariant: `A_G(F)` acts trivially on `𝔤⁰`).  By `quotHG_equiv`
this is the integral over `H̄(F)\Ḡ(F)/A_Ḡ(F)`. -/
def distribJLie (f : ↥d.lieZero → ℂ) : ℂ :=
  ∫ q : d.HGQuot, d.kernelLie ψ f (Quotient.out (CosetSpace.out d.toGmodAG q : d.GmodAG))
    ∂d.weilMeasureHG

/-! ## 4. Strongly cuspidal functions on `𝔤⁰(F)` -/

/-- `𝔭⁰ = Lie(P) ∩ 𝔤⁰` for the parabolic `P = P_{F_W} × P_{F_V}` (Thesis §5.1.2). -/
def liePar (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) : Submodule F d.ambient :=
  d.lie0 ⊓ ((lieFlagStab FW).comap (LinearMap.fst F _ _) ⊓
    (lieFlagStab FV).comap (LinearMap.snd F _ _))

/-- `𝔲 = Lie(U_P)`, the nilpotent radical of `𝔭⁰` (Thesis §5.1.2). -/
def lieUnip (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) : Submodule F d.ambient :=
  d.lie0 ⊓ ((lieFlagUnip FW).comap (LinearMap.fst F _ _) ⊓
    (lieFlagUnip FV).comap (LinearMap.snd F _ _))

instance instMeasurableSpaceLieUnip (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) :
    MeasurableSpace ↥(d.lieUnip FW FV) := borel _

theorem lieUnip_le_lie0 (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) :
    d.lieUnip FW FV ≤ d.lie0 := inf_le_left

/-- **`S_scusp(𝔤⁰(F))`** (Thesis §4.5; BP §5.1): Schwartz–Bruhat functions `f` on `𝔤⁰(F)` with
`∫_{𝔲(F)} f(X + N) dN = 0` for every proper parabolic `P = MU` and every `X ∈ 𝔭⁰(F)` (as for
`IsStronglyCuspidal`, quantifying over `𝔭` instead of `𝔪` is equivalent).  The condition is
stated for every Haar measure on `𝔲(F)` (they are proportional), with integrability included. -/
def IsLieScusp (f : ↥d.lieZero → ℂ) : Prop :=
  IsTestFn f ∧ ∀ (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV), d.IsProperFlagPair FW FV →
    ∀ X : ↥d.lieZero, (X : d.ambient) ∈ d.liePar FW FV →
      ∀ μ : Measure ↥(d.lieUnip FW FV), μ.IsAddHaarMeasure →
        Integrable (fun N : ↥(d.lieUnip FW FV) =>
            f ⟨(X : d.ambient) + N, d.lie0.add_mem X.2 (d.lieUnip_le_lie0 FW FV N.2)⟩) μ ∧
          ∫ N : ↥(d.lieUnip FW FV),
            f ⟨(X : d.ambient) + N, d.lie0.add_mem X.2 (d.lieUnip_le_lie0 FW FV N.2)⟩ ∂μ = 0

end GGPData

/-! ## 5. Quasi-characters on a Lie algebra and their germs (Thesis §4.1.1, §4.2; BP §4.1) -/

section LieQC

variable {A : Type*} [Ring A] [Algebra F A] [TopologicalSpace A]

/-- The centralizer `Z_G(X) = {g ∈ G : g X = X g}` of a Lie algebra element `X`. -/
def lieGrpCentralizer (G : Subgroup Aˣ) (X : A) : Subgroup Aˣ where
  carrier := {u | u ∈ G ∧ (u : A) * X = X * u}
  one_mem' := ⟨G.one_mem, by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨G.mul_mem ha.1 hb.1, by
    rw [Units.val_mul, mul_assoc, hb.2, ← mul_assoc, ha.2, mul_assoc]⟩
  inv_mem' := fun {a} ha => ⟨G.inv_mem ha.1, by
    calc ((a⁻¹ : Aˣ) : A) * X = ((a⁻¹ : Aˣ) : A) * (X * a) * ((a⁻¹ : Aˣ) : A) := by
          simp [mul_assoc]
      _ = ((a⁻¹ : Aˣ) : A) * ((a : A) * X) * ((a⁻¹ : Aˣ) : A) := by rw [ha.2]
      _ = X * ((a⁻¹ : Aˣ) : A) := by simp [← mul_assoc]⟩

variable [Module.Finite F A] [IsModuleTopology F A]

/-- `c` gives the local expansion of `θ` at the semisimple `X ∈ 𝔤`:
`θ(X + Y) = Σ_{O ∈ Nil(𝔤_X)} c_O ĵ(O, Y)` for all `Y` near `0` in `𝔤_X` that are regular in `𝔤_X`
(BP §4.1, Lie-algebra case; Thesis §4.1.1).  `ĵ` is taken for `(Z_G(X), 𝔤_X)` and `b|_{𝔤_X}`. -/
def HasGermExpansionLie (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A) (b : LinearMap.BilinForm F A)
    (ψ : NontrivialAddChar F) (θ : ↥𝔤 → ℂ) (X : A)
    (c : NilOrbit (lieGrpCentralizer G X) (lieCentralizer 𝔤 X) → ℂ) : Prop :=
  (Function.support c).Finite ∧
  ∃ ω ∈ 𝓝 (0 : A), ∀ Y ∈ ω, Y ∈ lieCentralizer 𝔤 X → IsRegularSS (lieCentralizer 𝔤 X) Y →
    ∀ Z : ↥𝔤, (Z : A) = X + Y →
      θ Z = ∑ᶠ O, c O * jHat (lieGrpCentralizer G X) (lieCentralizer 𝔤 X) b ψ O Y

/-- `θ : 𝔤(F) → ℂ` is a quasi-character (BP §4.1, Lie-algebra case; Thesis §4.1.1): invariant
under `G(F)`-conjugation on `𝔤_reg(F)`, with a local expansion at every semisimple `X ∈ 𝔤(F)`. -/
def IsLieQuasiCharacter (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A) (b : LinearMap.BilinForm F A)
    (ψ : NontrivialAddChar F) (θ : ↥𝔤 → ℂ) : Prop :=
  (∀ g ∈ G, ∀ Y Z : ↥𝔤, (Y : A) ∈ regularSetLie 𝔤 →
      (Z : A) = (g : A) * Y * ((g⁻¹ : Aˣ) : A) → θ Z = θ Y) ∧
    ∀ X : ↥𝔤, IsSS F (X : A) → ∃ c, HasGermExpansionLie G 𝔤 b ψ θ X c

open Classical in
/-- The germ `c_{θ,O}(X)`, `O ∈ Nil_reg(𝔤_X)` (BP §4.5, Lie-algebra case; Thesis §4.2): the
coefficient of `ĵ(O,·)` in the local expansion of `θ` at `X`; `0` if `O ∉ Nil_reg(𝔤_X)` or if
there is no expansion (as `germ`). -/
def germLie (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A) (b : LinearMap.BilinForm F A)
    (ψ : NontrivialAddChar F) (θ : ↥𝔤 → ℂ) (X : A)
    (O : NilOrbit (lieGrpCentralizer G X) (lieCentralizer 𝔤 X)) : ℂ :=
  if O ∈ NilReg _ _ then
    (if h : ∃ c, HasGermExpansionLie G 𝔤 b ψ θ X c then h.choose O else 0)
  else 0

end LieQC

namespace GGPData

variable (d : GGPData F) (ψ : NontrivialAddChar F)

/-! ## 6. `θ_f` on `𝔤⁰` and `m^Lie_geom` -/

/-- The self-dual measure `dX` on `𝔤⁰(F)` (Thesis §2.4); it cancels in `θ_f^Lie`. -/
def measLie0 : Measure ↥d.lieZero := selfDualHaar d.lieZero d.bilin ψ

/-- The orbital pairing on `𝔤⁰`: `⟨f, f'⟩ = ∫_{G(F)/A_G(F)} ∫_{𝔤⁰(F)} f(x⁻¹Xx) f'(X) dX dx`
(BP §5.5, Lie-algebra case; as `orbitalPairing`), for `Measure.haar` on `G(F)/A_G(F)`. -/
def orbitalPairingLie (f f' : ↥d.lieZero → ℂ) : ℂ :=
  ∫ x : d.GmodAG, (∫ X : ↥d.lieZero, f (d.adLie0 (Quotient.out x)⁻¹ X) * f' X ∂d.measLie0 ψ)
    ∂Measure.haar

/-- `θ` represents the orbital pairing of `f` on `𝔤⁰` (as `IsThetaF`; BP §5.5–5.6, Lie case). -/
def IsThetaFLie (f θ : ↥d.lieZero → ℂ) : Prop :=
  LocallyIntegrable θ (d.measLie0 ψ) ∧
    ContinuousOn θ {X | IsRegularSS d.lieZero (X : d.ambient)} ∧
    ∀ f' : ↥d.lieZero → ℂ, IsTestFn f' →
      ∫ X, θ X * f' X ∂d.measLie0 ψ = d.orbitalPairingLie ψ f f'

open Classical in
/-- **`θ_f` for `f ∈ S_scusp(𝔤⁰(F))`** (Thesis §4.8; BP §5.5, Lie case): epsilon; `0` if none. -/
def thetaFLie (f : ↥d.lieZero → ℂ) : ↥d.lieZero → ℂ :=
  if h : ∃ θ, d.IsThetaFLie ψ f θ then h.choose else 0

/-- **`𝔱⁰ = Lie(S)`** for `T = P⁻¹(S)` a torus of `𝒯` (Thesis Prop 12.1.1(iii), `Γ^Lie(G,H)`): the `X ∈ so(W)`
commuting with `T` and killing `W' = W^T` (the fixed space of `T`). -/
def lieTorus (T : Subgroup ↥(GSpin d.QW)) : Submodule F (CliffordAlgebra d.QW) where
  carrier := {X | X ∈ soSub d.QW ∧
    (∀ t ∈ T, (((t : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X =
      X * (((t : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) ∧
    ∀ w ∈ commonFixed T, adV d.QW X w = 0}
  add_mem' := by
    rintro X Y ⟨hX0, hX1, hX2⟩ ⟨hY0, hY1, hY2⟩
    refine ⟨(soSub d.QW).add_mem hX0 hY0, fun t ht => ?_, fun w hw => ?_⟩
    · rw [mul_add, add_mul, hX1 t ht, hY1 t ht]
    · rw [lieAlg_adV_add, hX2 w hw, hY2 w hw, add_zero]
  zero_mem' := ⟨(soSub d.QW).zero_mem, fun _ _ => by simp, fun w _ => lieAlg_adV_zero _ w⟩
  smul_mem' := by
    rintro c X ⟨hX0, hX1, hX2⟩
    refine ⟨(soSub d.QW).smul_mem c hX0, fun t ht => ?_, fun w hw => ?_⟩
    · rw [mul_smul_comm, smul_mul_assoc, hX1 t ht]
    · rw [lieAlg_adV_smul, hX2 w hw, smul_zero]

instance instMeasurableSpaceLieTorus (T : Subgroup ↥(GSpin d.QW)) :
    MeasurableSpace ↥(d.lieTorus T) := borel _

instance instBorelSpaceLieTorus (T : Subgroup ↥(GSpin d.QW)) :
    BorelSpace ↥(d.lieTorus T) := ⟨rfl⟩

/-- `μ` is the Haar measure on `𝔱⁰(F)` compatible through `exp` with the probability Haar measure
on `T(F)/A_{G,H}(F)` (`exp` induces a measure preserving homeomorphism
`ω ∩ Γ^Lie(G,H) ≃ exp(ω) ∩ Γ(G,H)`; BP §1.6, §11.1). -/
def IsExpCompatT (T : Subgroup ↥(GSpin d.QW)) (μ : Measure ↥(d.lieTorus T)) : Prop :=
  letI : MeasurableSpace (d.TorusQuot T) := borel _
  haveI : BorelSpace (d.TorusQuot T) := ⟨rfl⟩
  μ.IsAddHaarMeasure ∧
    ∃ U ∈ 𝓝 (0 : ↥(d.lieTorus T)), ∀ S : Set ↥(d.lieTorus T), MeasurableSet S → S ⊆ U →
      μ S = probHaar (d.TorusQuot T)
        {q | ∃ X ∈ S, ∃ t : ↥T,
          (((t : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) =
            expA F (X : CliffordAlgebra d.QW) ∧ q = (t : d.TorusQuot T)}

open Classical in
/-- The measure on `𝔱⁰(F)` (epsilon; `0` if none). -/
def measLieTorus (T : Subgroup ↥(GSpin d.QW)) : Measure ↥(d.lieTorus T) :=
  if h : ∃ μ, d.IsExpCompatT T μ then h.choose else 0

/-- `X ∈ 𝔱⁰_♮(F)` (Lie version of `T_♮`): `X` has no eigenvalue `0` on `W'' = (W')^⊥`,
i.e. `ker X = W'`, and `X` is regular in `so(W'')`: every `Y ∈ so(W)` commuting with `X` and
killing `W'` lies in `𝔱⁰`. -/
def IsGammaEltLie (T : Subgroup ↥(GSpin d.QW)) (X : CliffordAlgebra d.QW) : Prop :=
  X ∈ d.lieTorus T ∧ LinearMap.ker (adV d.QW X) = commonFixed T ∧
    ∀ Y ∈ soSub d.QW, Y * X = X * Y → (∀ w ∈ commonFixed T, adV d.QW Y w = 0) →
      Y ∈ d.lieTorus T

/-- `Δ(X) = |det(X|_{W''_X})|_F` with `W''_X` the image of `X` on `W` (Waldspurger 2010 §7.9;
Thesis (6.5.9), Lie version of `deltaGGP`). -/
def deltaLie (X : CliffordAlgebra d.QW) : ℝ :=
  absF (LinearMap.det ((adV d.QW X).restrict (p := LinearMap.range (adV d.QW X))
    (q := LinearMap.range (adV d.QW X)) (fun v _ => LinearMap.mem_range_self _ v)))

/-- Luo's recipe (Luo §7.1) for the GGP triple of `(U, U ⊕ Z)`, `U ⊆ W`, as a
condition on `Y = (Y_W, Y_V)`: `OrbitSpec` with `fixedSub x` replaced by `U` (for the Lie algebra,
`U = ker X`). -/
def OrbitSpecAt (U : Submodule F (Fin d.m → F)) (Y : d.ambient) : Prop :=
  if Even (finrank F ↥(U.prod (⊤ : Submodule F d.Z))) ∧
      4 ≤ finrank F ↥(U.prod (⊤ : Submodule F d.Z)) then
    IsInOrbitNu d.QV (U.prod ⊤) (d.ν : F) (adV d.QV Y.2)
  else if Even (finrank F ↥U) ∧ 4 ≤ finrank F ↥U then
    IsInOrbitNu d.QW U (-(d.ν : F)) (adV d.QW Y.1)
  else True

open Classical in
/-- The orbit `O_X ∈ Nil_reg(𝔤⁰_X)` (Lie version of `orbitChoice`), for
`X ∈ so(W)` embedded diagonally; junk (the zero orbit) if there is none. -/
def orbitChoiceLie (X : CliffordAlgebra d.QW) :
    NilOrbit (lieGrpCentralizer d.G (d.diagLie X)) (lieCentralizer d.lieZero (d.diagLie X)) :=
  if h : ∃ O ∈ NilReg (lieGrpCentralizer d.G (d.diagLie X)) (lieCentralizer d.lieZero (d.diagLie X)),
      ∃ Y ∈ nilOrbitSet O, d.OrbitSpecAt (LinearMap.ker (adV d.QW X)) (Y : d.ambient)
  then h.choose
  else Quotient.mk (nilSetoid _ _) ⟨0, LieSubalgebra.zero_mem _, IsNilpotent.zero⟩

/-- The germ `c_{θ,O}(X)` of a function on `𝔤⁰` (`germLie` for `(G, 𝔤⁰, b)`). -/
abbrev germLie0 (θ : ↥d.lieZero → ℂ) (X : d.ambient)
    (O : NilOrbit (lieGrpCentralizer d.G X) (lieCentralizer d.lieZero X)) : ℂ :=
  germLie d.G d.lieZero d.bilin ψ θ X O

open Classical in
/-- The integrand `D^G(X)^{1/2} c_{θ,O_X}(X) Δ(X)^{s−1/2}` on `𝔱⁰(F)`, `0` off `𝔱⁰_♮(F)`
(Lie version of `gammaIntegrand`). -/
def gammaIntegrandLie (θ : ↥d.lieZero → ℂ) (T : Subgroup ↥(GSpin d.QW)) (s : ℝ)
    (X : CliffordAlgebra d.QW) : ℂ :=
  if d.IsGammaEltLie T X then
    (Real.sqrt (weylDiscLie d.lieZero (d.diagLie X)) : ℂ) *
      d.germLie0 ψ θ (d.diagLie X) (d.orbitChoiceLie X) * ((d.deltaLie X ^ (s - 1 / 2) : ℝ) : ℂ)
  else 0

/-- `∫_{𝔱⁰(F)} D^G(X)^{1/2} c_{θ,O_X}(X) Δ(X)^{s−1/2} dX`. -/
def torusIntegralLie (θ : ↥d.lieZero → ℂ) (T : Subgroup ↥(GSpin d.QW)) (s : ℝ) : ℂ :=
  ∫ X : ↥(d.lieTorus T), d.gammaIntegrandLie ψ θ T s X ∂d.measLieTorus T

/-- `m^Lie_{geom,s}(θ) = ∫_{Γ^Lie(G,H)} D^G(X)^{1/2} c_{θ,O_X}(X) Δ(X)^{s−1/2} dX
= Σ_{[T]} |W(T)|⁻¹ ∫_{𝔱⁰(F)} …` (Thesis Prop 12.1.1(iii)). -/
def mGeomLieS (θ : ↥d.lieZero → ℂ) (s : ℝ) : ℂ :=
  ∑' c : GammaClass d, ((weylCard d c : ℂ))⁻¹ * d.torusIntegralLie ψ θ (Quot.out c).1 s

/-- **`m^Lie_geom(θ) = lim_{s → 0⁺} m^Lie_{geom,s}(θ)`** (Thesis Prop 12.1.1(iii)). -/
def mGeomLie (θ : ↥d.lieZero → ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (d.mGeomLieS ψ θ)

/-- If some `θ` represents the orbital pairing of `f` on `𝔤⁰`, so does `thetaFLie d ψ f`. -/
theorem isThetaFLie_thetaFLie_of_exists {f : ↥d.lieZero → ℂ} (h : ∃ θ, d.IsThetaFLie ψ f θ) :
    d.IsThetaFLie ψ f (d.thetaFLie ψ f) := by
  classical
  unfold thetaFLie
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

end GGPData

/-! ## 7. The cited theorems (special orthogonal triple, no hyperbolic-plane factor) -/

/-- **The spectral expansion of `J^Lie` (Thesis Thm 11.6.1), in the
normalization-free form used: `J^Lie(f)` depends only on `θ_f|_{𝔤⁰_reg}`.**

Source: Luo, *A local trace formula for the local Gan–Gross–Prasad conjecture for special
orthogonal groups* (arXiv:2009.13947v1), Thm 6.6.1: `J^Lie(f) = ∫_{Γ(Σ)} D^G(X)^{1/2} θ̂_f(X) dX`
for `f ∈ S_scusp(𝔤(F))`, any local field of characteristic `0` (following BP, Astérisque 418,
Thm 10.8.1); for `p`-adic `F` the content is Waldspurger, Compositio 146 (2010) §9–10, in his
truncated `I_N` formalism.  The right-hand side depends only on `θ_f` as a distribution, hence
only on `θ_f|_{𝔤⁰_reg}` (`𝔤⁰_reg` is open of full measure).  The `Γ(Σ)` formula itself is not
stated: it needs the measure on `Γ(𝔤⁰)` (tori, Weyl groups, normalized measures on each `𝔱(F)`),
which is not formalized, and a wrong constant there would make the axiom false.  This form is
normalization-free: rescaling `Measure.haar` on `G(F)/A_G(F)` rescales `θ_f` and `θ_{f'}` alike.

**Coverage.**  Luo defines `J^Lie(f) = ∫_{H(F)\G(F)} K^Lie(f,x) dx` with
`G = SO(W) × SO(V)` and no quotient by a central torus (Luo §4), and treats `dim W = 2` explicitly
(Luo §6.3(2)).  When `W` or `V` is a hyperbolic plane, `SO(W) ≅ G_m` (resp. `SO(V)`) is a split
central torus of `G` acting trivially on `𝔤` and freely on `H\G` with noncompact orbits, so
`∫_{H\G} |K^Lie|` is `0` or `∞`; Luo's statements are then not literally usable.  So the
hypothesis "neither `W` nor `V` is a hyperbolic plane" is added: then `A_Ḡ = 1` (`AGbar_eq_bot`),
`H\G/A_G ≃ H̄\Ḡ` (`quotHG_equiv_SO`), and `distribJLie`, `IsLieScusp`, `IsThetaFLie` are
Luo's objects for `(Ḡ, H̄, ξ)`.

Not confirmed against the texts: that Waldspurger 2010 / Luo need no
odd-residue-characteristic hypothesis (`PAdicField` imposes none), and that the degenerate
Whittaker-type triples `dim W ∈ {0, 1}`, which the hyperbolic-plane exclusion still admits, are
covered. -/
axiom jLie_eq_of_thetaFLie_eqOn (d : GGPData F) (ψ : NontrivialAddChar F)
    (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    {f f' θ θ' : ↥d.lieZero → ℂ} (hf : d.IsLieScusp f) (hf' : d.IsLieScusp f')
    (hθ : d.IsThetaFLie ψ f θ) (hθ' : d.IsThetaFLie ψ f' θ')
    (he : ∀ X : ↥d.lieZero, IsRegularSS d.lieZero (X : d.ambient) → θ X = θ' X) :
    d.distribJLie ψ f = d.distribJLie ψ f'

/-- **The endgame (Thesis §12.5), in test-function form: if
`J^Lie(f) − m^Lie_geom(θ_f) = Σ_{O ∈ Nil_reg(𝔤⁰)} c_O c_{θ_f,O}(0)` for every
`f ∈ S_scusp(𝔤⁰(F))`, then every `c_O` vanishes.**

Source: Waldspurger, Compositio 146 (2010) §11.4–11.6 (`p`-adic), Luo (arXiv:2009.13947v1)
Prop 7.3.7 and Lemma B.3.1 (any local field of characteristic `0`).  It uses the spectral expansion of `J^Lie` (Luo Thm 6.6.1) for the
explicit values `J^Lie_qc(θ_T) ∈ {0, 1}`, the Shalika-germ facts,
the Lie-algebra form of BP Cor 5.7.2 (every compactly supported quasi-character is a `θ_f`), and
the orbit choice `orbitChoiceLie` (Luo §7.1).  In the sources it is a step of the proof of the
geometric expansion `J^Lie(f) = m^Lie_geom(θ_f)` for the special orthogonal triple, which they
prove unconditionally (Waldspurger 2010 Thm 7.9 / §12.3; Luo Thm 7.3.3 with Prop 7.3.6); the
statement here (unconditional, with arbitrary `c`) is that geometric expansion together with the
linear independence of the germ functionals `f ↦ c_{θ_f,O}(0)` shown in the endgame.

**Normalization-sensitive** (unlike `jLie_eq_of_thetaFLie_eqOn`): `measH0` and `measLieTorus` are
the measures compatible with `exp` (BP §1.6), `θ_f^Lie` and `J^Lie` are tied to `Measure.haar` on
`G(F)/A_G(F)`, the germs to `ψ` and the trace form; the constant of the
Weyl-integration step relating `θ_f` to BP's weighted orbital integrals (`= 1`) is inherited.  Checked at
the smallest triple in `Sanity/LieAudit.lean`.

**The constant must be exactly 1.**  Because `c` is
arbitrary, the axiom is equivalent to `J^Lie(f) = m^Lie_geom(θ_f)` modulo regular germs at `0`
*with Lean's normalizations*.  At a triple whose `Γ^Lie(G,H)` is only the zero torus (`W = 0`, or
`dim W = 1`), `m^Lie_geom(θ)` is the germ of `θ` at `0` for `orbitChoiceLie 0`; if the true
identity were `J^Lie(f) = κ · m^Lie_geom(θ_f)` with `κ ≠ 1` (from the Weyl-integration constant, the
`ĵ`/self-dual germ normalization, or the `measH0`/`weilMeasureHG` conventions), then
`c = (κ − 1) δ_{O_0}` satisfies the hypothesis and the axiom would prove `False`.  Likewise if
`orbitChoiceLie 0` (sign of `ν`) picked a different regular orbit than the sources' central term.
Checked: `toyD` (proved in Lean, `κ = 1`); by hand computation with the Lean measures,
`dim W = 1`, `V` an anisotropic plane (`κ = 1`), and the first case with a nonzero regular
nilpotent orbit, `W = 0`, `V` split of dimension 3 (`SO(3) ≅ PGL_2`, Whittaker-type `J^Lie`, one
regular orbit so `orbitChoiceLie 0` is forced): `κ = 1`, any residue characteristic.
Higher rank (hand computations): `W = 0` with
`dim V = 5`, and `dim W = 2` with `dim V = 3`, each have a unique regular orbit, and `OrbitSpecAt`
at `X = 0` reduces to `True` there (`dim V` odd, `dim W < 4`), so they test only the constant.
The first triple where `orbitChoiceLie 0` makes a real choice is
`dim W = 1`, `dim V = 4`; there the element dual to `λ` lies in `O_ν` (Luo
§7.1's `O_{ν_0}`).  Constants: `κ = 1` for every `dim W ≤ 1`, any rank and any `p` (one Kostant-slice
computation, Whittaker type; covers `(0, 5)` and `(1, 4)`); `κ = 1` at `dim W = 2` (`W`
anisotropic), `dim V = 3` split, `p` odd (one explicit computation).  Not computed: the `W`-side
`−ν` choice (first at `dim W = 4`, `dim V = 5`), `p = 2` at `(2, 3)`.

**Coverage**: as for `jLie_eq_of_thetaFLie_eqOn`, whence the hypotheses
`¬ IsHypPlane d.QW`, `¬ IsHypPlane d.QV`. -/
axiom lie_endgame (d : GGPData F) (ψ : NontrivialAddChar F)
    (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    (c : NilOrbit (lieGrpCentralizer d.G 0) (lieCentralizer d.lieZero 0) → ℂ)
    (h : ∀ f : ↥d.lieZero → ℂ, d.IsLieScusp f →
      d.distribJLie ψ f - d.mGeomLie ψ (d.thetaFLie ψ f) =
        ∑ᶠ O ∈ NilReg (lieGrpCentralizer d.G 0) (lieCentralizer d.lieZero 0),
          c O * d.germLie0 ψ (d.thetaFLie ψ f) 0 O) :
    ∀ O ∈ NilReg (lieGrpCentralizer d.G 0) (lieCentralizer d.lieZero 0), c O = 0

end GSpinGGP
