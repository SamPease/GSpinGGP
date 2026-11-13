/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Interface
import GSpinGGP.Literature.HarishChandra

/-!
# Translating germs between semisimple elements with the same centralizers

Tools for comparing the germs `c_{θ,O}(x)` and `c_{θ,O'}(x')` (Thesis §4.2) at two semisimple
elements `x, x'` of `G(F)` with the same centralizers in `G` and `𝔤`, used both for the germ at
central elements (Thesis §6.7) and for the `A_{G,H}(F)`-invariance of the integrand of
`m_{geom,s}` (Thesis §6.5):

* scalars: `isRegularSS_algebraMap_mul`, `isSS_algebraMap`,
  `grpCentralizer_eq_of_central`, `lieCentralizer_eq_of_central`;
* `isSS_diag_of_isSS`: `x` semisimple in `GSpin(W)(F)` ⇒ `diag x` semisimple in `G(F)`;
* `germ_eq_germ_of_translate`: germs only see the local behaviour (uniqueness of local
  expansions, `germ_unique`);
* `pickNilOrbit`, `heq_pickNilOrbit`: the orbit choice `orbitChoice` only depends on the
  centralizers and on the condition `OrbitSpec`.
-/

noncomputable section

open MeasureTheory Filter Topology Module
open scoped Classical

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (ψ : NontrivialAddChar F)

section Scalars

variable {d : GGPData F}

/-- `x ↦ c x` preserves regular semisimplicity for a nonzero scalar `c`. -/
theorem isRegularSS_algebraMap_mul {A : Type*} [Ring A] [Algebra F A] (𝔤 : LieSubalgebra F A)
    {a : F} (ha : a ≠ 0) {y : A} (hy : IsRegularSS 𝔤 y) :
    IsRegularSS 𝔤 (algebraMap F A a * y) := by
  rw [← Algebra.smul_def]
  have hL : LinearMap.mulLeft F (a • y) = a • LinearMap.mulLeft F y := by
    ext w; simp
  have hC : lieCentralizer 𝔤 (a • y) = lieCentralizer 𝔤 y := by
    ext X
    rw [mem_lieCentralizer, mem_lieCentralizer, smul_mul_assoc, mul_smul_comm]
    exact and_congr_right fun _ => smul_right_inj ha
  refine ⟨?_, hC ▸ hy.2⟩
  unfold IsSS
  rw [hL]
  exact Module.End.IsSemisimple_smul a hy.1

/-- A scalar is semisimple. -/
theorem isSS_algebraMap {A : Type*} [Ring A] [Algebra F A] (a : F) :
    IsSS F (algebraMap F A a) := by
  have hL : LinearMap.mulLeft F (algebraMap F A a) = a • LinearMap.id := by
    ext w; simp [Algebra.smul_def]
  unfold IsSS
  rw [hL]
  exact Module.End.IsSemisimple_smul a Module.End.isSemisimple_id

/-- `G_x = G` for `x` central in the ambient algebra. -/
theorem grpCentralizer_eq_of_central {A : Type*} [Ring A] (G : Subgroup Aˣ) {x : Aˣ}
    (hx : ∀ a : A, (x : A) * a = a * x) : grpCentralizer G x = G := by
  ext g
  simp only [grpCentralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq, and_iff_left_iff_imp]
  exact fun _ => Units.ext (hx g)

/-- `𝔤_x = 𝔤` for `x` central in the ambient algebra. -/
theorem lieCentralizer_eq_of_central {A : Type*} [Ring A] [Algebra F A] (𝔤 : LieSubalgebra F A)
    {x : A} (hx : ∀ a : A, x * a = a * x) : lieCentralizer 𝔤 x = 𝔤 := by
  ext X
  rw [mem_lieCentralizer]
  exact and_iff_left (hx X)

end Scalars

section DiagSS

variable (d : GGPData F)

/-- **`x ∈ GSpin(W)(F)` semisimple ⇒ `diag x = (x, x)` semisimple in `C(W) × C(V)`**: the
squarefree minimal polynomial `p` of `x` kills `x` in `C(W)`, hence its image under the algebra
map `C(W) → C(V)`, hence the pair. -/
theorem isSS_diag_of_isSS {t : ↥(GSpin d.QW)}
    (ht : IsSS F (((t : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW)) :
    IsSS F (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient) := by
  set a : CliffordAlgebra d.QW := ((t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)
  set p := minpoly F (LinearMap.mulLeft F a)
  have hsq : Squarefree p := Module.End.IsSemisimple.minpoly_squarefree ht
  have h0 : Polynomial.aeval (Algebra.lmul F (CliffordAlgebra d.QW) a) p = 0 := minpoly.aeval F _
  rw [Polynomial.aeval_algHom_apply] at h0
  have h1 : Polynomial.aeval a p = 0 :=
    Algebra.lmul_injective (R := F) (h0.trans (map_zero _).symm)
  set φ := CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
  have hcoe : (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient) = (a, φ a) := rfl
  have h2 : Polynomial.aeval (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient) p = 0 := by
    rw [hcoe]
    refine Prod.ext ?_ ?_
    · have := Polynomial.aeval_algHom_apply (AlgHom.fst F (CliffordAlgebra d.QW)
        (CliffordAlgebra d.QV)) (a, φ a) p
      simp only [AlgHom.fst_apply] at this
      rw [Prod.fst_zero, ← this, h1]
    · have := Polynomial.aeval_algHom_apply (AlgHom.snd F (CliffordAlgebra d.QW)
        (CliffordAlgebra d.QV)) (a, φ a) p
      simp only [AlgHom.snd_apply] at this
      rw [Prod.snd_zero, ← this, Polynomial.aeval_algHom_apply, h1, map_zero]
  have h3 : Polynomial.aeval (Algebra.lmul F d.ambient
      (((d.diag t : ↥d.G) : d.ambientˣ) : d.ambient)) p = 0 := by
    rw [Polynomial.aeval_algHom_apply, h2, map_zero]
  exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq h3


end DiagSS

section Translate

variable {d : GGPData F}

/-- Transport of germ coefficients along equalities of centralizers. -/
theorem exists_coeff_transport (b : LinearMap.BilinForm F d.ambient)
    (H H' : Subgroup d.ambientˣ) (𝔥 𝔥' : LieSubalgebra F d.ambient) (hH : H = H') (h𝔥 : 𝔥 = 𝔥')
    (c' : NilOrbit H' 𝔥' → ℂ) :
    ∃ c : NilOrbit H 𝔥 → ℂ, ((Function.support c).Finite ↔ (Function.support c').Finite) ∧
      (∀ X, ∑ᶠ O, c O * jHat H 𝔥 b ψ O X = ∑ᶠ O, c' O * jHat H' 𝔥' b ψ O X) ∧
      ∀ O O', HEq O O' → c O = c' O' ∧ (O ∈ NilReg H 𝔥 ↔ O' ∈ NilReg H' 𝔥') := by
  subst hH h𝔥
  refine ⟨c', Iff.rfl, fun _ => rfl, fun O O' hO => ?_⟩
  obtain rfl := eq_of_heq hO
  exact ⟨rfl, Iff.rfl⟩

/-- **Germs only see the local behaviour**: if `x, x'` are semisimple with the same centralizers
and `θ(x e^X) = θ(x' e^X)` for `X ∈ 𝔤_x` small and regular, then the germs of `θ` at `x` and `x'`
agree (via uniqueness of the local expansion, `germ_unique`). -/
theorem germ_eq_germ_of_translate (θ : ↥d.G → ℂ) (x x' : ↥d.G)
    (hx : IsSS F ((x : d.ambientˣ) : d.ambient)) (hx' : IsSS F ((x' : d.ambientˣ) : d.ambient))
    (hH : grpCentralizer d.G x = grpCentralizer d.G x')
    (h𝔥 : lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient) =
      lieCentralizer d.lie ((x' : d.ambientˣ) : d.ambient))
    (hθ : ∃ ω ∈ 𝓝 (0 : d.ambient), ∀ X ∈ ω, X ∈ lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient) →
      IsRegularSS (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) X →
      ∀ y : ↥d.G, ((y : d.ambientˣ) : d.ambient) = ((x : d.ambientˣ) : d.ambient) * expA F X →
        ∃ y' : ↥d.G, ((y' : d.ambientˣ) : d.ambient) = ((x' : d.ambientˣ) : d.ambient) * expA F X ∧
          θ y = θ y')
    (hexp : ∃ c, HasGermExpansion d.G d.lie d.bilin ψ θ x' c)
    (O : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)))
    (O' : NilOrbit (grpCentralizer d.G x') (lieCentralizer d.lie ((x' : d.ambientˣ) : d.ambient)))
    (hO : HEq O O') :
    germ d.G d.lie d.bilin ψ θ x O = germ d.G d.lie d.bilin ψ θ x' O' := by
  obtain ⟨c', hc'⟩ := hexp
  obtain ⟨c, hfin, hsum, hcO⟩ := exists_coeff_transport ψ d.bilin _ _ _ _ hH h𝔥 c'
  obtain ⟨ω₁, hω₁, hθ'⟩ := hθ
  obtain ⟨ω₂, hω₂, hc'e⟩ := hc'.2
  have hc : HasGermExpansion d.G d.lie d.bilin ψ θ x c := by
    refine ⟨hfin.mpr hc'.1, ω₁ ∩ ω₂, inter_mem hω₁ hω₂, fun X hX hXc hXr y hy => ?_⟩
    obtain ⟨y', hy', hθy⟩ := hθ' X hX.1 hXc hXr y hy
    rw [hθy, hsum X]
    exact hc'e X hX.2 (h𝔥 ▸ hXc) (h𝔥 ▸ hXr) y' hy'
  obtain ⟨hcc, hreg⟩ := hcO O O' hO
  by_cases hOr : O ∈ NilReg _ _
  · rw [germ_eq_of_hasGermExpansion d ψ hx hc hOr,
      germ_eq_of_hasGermExpansion d ψ hx' hc' (hreg.mp hOr), hcc]
  · rw [germ_of_not_mem hOr, germ_of_not_mem fun h => hOr (hreg.mpr h)]

/-- The selection rule behind `orbitChoice`, with the centralizers and the condition as
parameters. -/
def pickNilOrbit (H : Subgroup d.ambientˣ) (𝔥 : LieSubalgebra F d.ambient)
    (P : d.ambient → Prop) : NilOrbit H 𝔥 :=
  if h : ∃ O ∈ NilReg H 𝔥, ∃ X ∈ nilOrbitSet O, P (X : d.ambient) then h.choose
  else Quotient.mk (nilSetoid _ _) ⟨0, LieSubalgebra.zero_mem _, IsNilpotent.zero⟩

theorem orbitChoice_eq_pickNilOrbit (x : ↥(GSpin d.QW)) :
    orbitChoice d x = pickNilOrbit _ _ (OrbitSpec d x) := rfl

theorem heq_pickNilOrbit (H H' : Subgroup d.ambientˣ) (𝔥 𝔥' : LieSubalgebra F d.ambient)
    (hH : H = H') (h𝔥 : 𝔥 = 𝔥') (P P' : d.ambient → Prop) (hP : P = P') :
    HEq (pickNilOrbit H 𝔥 P) (pickNilOrbit H' 𝔥' P') := by
  subst hH h𝔥 hP
  rfl

end Translate

end GSpinGGP
