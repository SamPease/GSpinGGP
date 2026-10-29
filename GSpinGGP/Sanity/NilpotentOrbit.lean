/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Sanity.Witnesses
import GSpinGGP.Literature.Fourier

/-!
# Sanity check: the normalization of `ĵ` on a *nonzero* regular nilpotent orbit

The normalization of `selfDualMeasure` / `orbitMeasure` / `jHat` must match Beuzart-Plessis
§1.6, §4.5, or `rodier_germ_one` would be false as stated. This file checks it on `𝔰𝔩₂`; the
analytic values are stated with `sorry`, being hand computations.

Test case: `𝔤 = 𝔰𝔩₂(F) ⊆ M₂(F)`, `G = GL₂(F)` (all units of `M₂(F)`, acting by `Ad`; this is the
action of `GSpin(V) ≅ GL₂` for a split 3-dimensional `V`, modulo the centre), the trace form
`b(X,Y) = tr(XY)`, and the regular nilpotent orbit `O_reg = G · E`, `E = [[0,1],[0,0]]`.

## Proved here

* `E` is a regular nilpotent element of `𝔰𝔩₂` (`isRegularNil_E`), with centralizer `F·E`
  (`mem_lieCentralizer_E_iff`, `finrank_lieCentralizer_E`) and `lieRank 𝔰𝔩₂ = 1` (`lieRank_sl2`).
  So `O_reg ∈ Nil_reg(𝔰𝔩₂)` (`regOrbit_mem_nilReg`) and `O_reg ≠ 0` (`regOrbit_ne_zeroOrbit`).
* The Kirillov form at `E` in the basis `H, F` of `𝔤/𝔤_E`: `ω_E(H,F) = 2`, `ω_E(F,H) = -2`,
  `ω_E(H,H) = ω_E(F,F) = 0` (`kirillov_E_*`). This is the input of the hand computation.
* **Generic non-vanishing** (`ne_zero_of_isOrbitMeasure`, `orbitMeasure_ne_zero`): for any
  `(G, 𝔤, b, ψ)` and any orbit `O`, an orbit measure is nonzero as soon as `O` is nonempty and the
  Kirillov form on one complement of `𝔤_X` has a self-dual measure. So the epsilon `orbitMeasure`
  is never the junk value `0` once `IsOrbitMeasure` is satisfiable.
* `jHat_regOrbit_not_eventually_zero`: `ĵ(O_reg, ·)` is not identically zero on any neighbourhood
  of `0`, derived from the value of `ĵ` on the split torus (below).

* `exists_isSelfDual_kirillov_E`: a self-dual measure exists for `ψ ∘ ω_E` on any complement of
  `𝔤_E` (`ω_E` is nondegenerate there, `kirillov_E_compl_nondegenerate`; existence from the
  literature axiom `exists_isSelfDual`, Tate's thesis / Weil, `Literature/Fourier`).

## Stated with `sorry` (true; hand computation)

* `exists_isOrbitMeasure_regOrbit`: `IsOrbitMeasure` is satisfiable for `O_reg` (existence of the
  autodual invariant measure on a symplectic `F`-analytic manifold, BP §1.6).
* `jHat_regOrbit_split`, `jHat_regOrbit_elliptic`: for `X = x·H` (`x ≠ 0`),
  `ĵ(O_reg, X) = 2 / |α(X)| = 2 / |2x|` (`|·| = absF`, the normalized absolute value), and
  `ĵ(O_reg, ·) = 0` on regular elliptic elements. Any residue characteristic, `p = 2` included.

Combined with the classical character formula for a principal series `π = Ind χ` of `GL₂`
(`θ_π(e^X) = 2/|α(X)|` near `0` on the split torus, `0` on elliptic elements), these values give
`c_{θ_π, O_reg}(1) = 1` and `c_{θ_π, 0}(1) = 0`, which is exactly what Rodier's theorem
(`rodier_germ_one`) predicts for a generic representation. So **no constant is missing** in the
normalization of `IsOrbitMeasure` / `selfDualHaar` / `jHat`.
-/

noncomputable section

open MeasureTheory Filter Topology Module
open scoped Classical

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace GSpinGGP

namespace Sanity

namespace NilpotentOrbit

/-! ## 1. A generic non-vanishing lemma for orbit measures -/

section Generic

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
variable {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A]
  [IsModuleTopology F A]

/-- An orbit measure of a nonempty orbit is nonzero, provided the Kirillov form on some complement
of `𝔤_X` (`X ∈ O`) admits a self-dual measure (true whenever that form is nondegenerate, which it
is when `b|_𝔤` is nondegenerate). The chart condition of `IsOrbitMeasure` then gives a set of
positive self-dual measure in the chart. -/
theorem ne_zero_of_isOrbitMeasure {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A}
    {b : LinearMap.BilinForm F A} {ψ : NontrivialAddChar F} {O : NilOrbit G 𝔤} {μ : Measure ↥𝔤}
    (hμ : IsOrbitMeasure G 𝔤 b ψ O μ) {X : ↥𝔤} (hX : X ∈ nilOrbitSet O)
    {C : Submodule F ↥𝔤} (hC : IsCompl C (LinearMap.ker (LieAlgebra.ad F ↥𝔤 X)))
    (hsd : ∃ ν, IsSelfDual ν ((kirillovForm 𝔤 b X).compl₁₂ C.subtype C.subtype) ψ) :
    μ ≠ 0 := by
  obtain ⟨U, hU, hS⟩ := hμ.2.2 X hX C hC
  set S : Set ↥C := (fun Y : ↥C ↦ ((Y : ↥𝔤) : A)) ⁻¹' interior U with hSdef
  have hcont : Continuous (fun Y : ↥C ↦ ((Y : ↥𝔤) : A)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hSopen : IsOpen S := isOpen_interior.preimage hcont
  have hS0 : (0 : ↥C) ∈ S := by
    show ((0 : ↥𝔤) : A) ∈ interior U
    simpa using mem_interior_iff_mem_nhds.mpr hU
  have hSsub : ∀ Y ∈ S, ((Y : ↥𝔤) : A) ∈ U := fun Y hY => interior_subset hY
  have heq := hS S hSopen.measurableSet hSsub
  haveI := selfDualMeasure_isAddHaar hsd
  have hpos : selfDualMeasure ((kirillovForm 𝔤 b X).compl₁₂ C.subtype C.subtype) ψ S ≠ 0 :=
    hSopen.measure_ne_zero _ ⟨0, hS0⟩
  intro h0
  rw [h0, Measure.coe_zero, Pi.zero_apply] at heq
  exact hpos heq.symm

/-- `orbitMeasure` is not the junk value `0` as soon as an orbit measure exists (under the
hypotheses of `ne_zero_of_isOrbitMeasure`). -/
theorem orbitMeasure_ne_zero {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A}
    {b : LinearMap.BilinForm F A} {ψ : NontrivialAddChar F} {O : NilOrbit G 𝔤}
    (h : ∃ μ, IsOrbitMeasure G 𝔤 b ψ O μ) {X : ↥𝔤} (hX : X ∈ nilOrbitSet O)
    {C : Submodule F ↥𝔤} (hC : IsCompl C (LinearMap.ker (LieAlgebra.ad F ↥𝔤 X)))
    (hsd : ∃ ν, IsSelfDual ν ((kirillovForm 𝔤 b X).compl₁₂ C.subtype C.subtype) ψ) :
    orbitMeasure G 𝔤 b ψ O ≠ 0 := by
  unfold orbitMeasure
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact ne_zero_of_isOrbitMeasure h.choose_spec hX hC hsd

end Generic

/-! ## 2. The test case `𝔰𝔩₂` -/

section SL2

variable {F : Type*} [NontriviallyNormedField F] [CharZero F]

/-- The ambient algebra `M₂(F)`. -/
abbrev M2 (F : Type*) [Field F] := Matrix (Fin 2) (Fin 2) F

/-- `𝔰𝔩₂(F)`: trace-zero matrices, as a Lie subalgebra of `M₂(F)` with the commutator bracket. -/
def sl2 : LieSubalgebra F (M2 F) where
  carrier := {X | X.trace = 0}
  add_mem' := fun {X Y} (hX : X.trace = 0) (hY : Y.trace = 0) => by
    show (X + Y).trace = 0
    rw [Matrix.trace_add, hX, hY, add_zero]
  zero_mem' := Matrix.trace_zero _ _
  smul_mem' := fun c X (hX : X.trace = 0) => by
    show (c • X).trace = 0
    rw [Matrix.trace_smul, hX, smul_zero]
  lie_mem' := fun {X Y} _ _ => by
    show (⁅X, Y⁆ : M2 F).trace = 0
    rw [Ring.lie_def, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

lemma mem_sl2 {X : M2 F} : X ∈ (sl2 : LieSubalgebra F (M2 F)) ↔ X.trace = 0 := Iff.rfl

/-- The trace form `b(X,Y) = tr(XY)` on `M₂(F)`. -/
def trForm : LinearMap.BilinForm F (M2 F) :=
  (LinearMap.mul F (M2 F)).compr₂ (Matrix.traceLinearMap (Fin 2) F F)

@[simp] lemma trForm_apply (X Y : M2 F) : trForm X Y = (X * Y).trace := rfl

/-- `E = [[0,1],[0,0]]`. -/
def E : M2 F := !![0, 1; 0, 0]
/-- `H = [[1,0],[0,-1]]`. -/
def H : M2 F := !![1, 0; 0, -1]
/-- `F = [[0,0],[1,0]]` (called `Fm` to avoid a clash with the field). -/
def Fm : M2 F := !![0, 0; 1, 0]

lemma E_mem : (E : M2 F) ∈ (sl2 : LieSubalgebra F (M2 F)) := by
  simp [mem_sl2, E, Matrix.trace_fin_two]
lemma H_mem : (H : M2 F) ∈ (sl2 : LieSubalgebra F (M2 F)) := by
  simp [mem_sl2, H, Matrix.trace_fin_two]
lemma Fm_mem : (Fm : M2 F) ∈ (sl2 : LieSubalgebra F (M2 F)) := by
  simp [mem_sl2, Fm, Matrix.trace_fin_two]

lemma E_mul_E : (E : M2 F) * E = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E, Matrix.mul_apply, Fin.sum_univ_two]

lemma E_ne_zero : (E : M2 F) ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [E] at this

lemma isNilpotent_E : IsNilpotent (E : M2 F) := ⟨2, by rw [pow_two, E_mul_E]⟩

/-- The centralizer of `E` in `𝔰𝔩₂` is `F·E`. -/
lemma mem_lieCentralizer_E_iff {X : M2 F} :
    X ∈ lieCentralizer (sl2 : LieSubalgebra F (M2 F)) E ↔ ∃ c : F, X = c • E := by
  rw [mem_lieCentralizer, mem_sl2]
  constructor
  · rintro ⟨htr, hc⟩
    refine ⟨X 0 1, ?_⟩
    have h00 := congrFun (congrFun hc 0) 0
    have h01 := congrFun (congrFun hc 0) 1
    simp [E, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
    rw [Matrix.trace_fin_two] at htr
    have ha : X 0 0 = 0 := by
      have : (2 : F) * X 0 0 = 0 := by linear_combination htr - h01
      simpa using this
    ext i j; fin_cases i <;> fin_cases j <;> simp [E, ha, h00]
    linear_combination h01 + ha
  · rintro ⟨c, rfl⟩
    refine ⟨(sl2 : LieSubalgebra F (M2 F)).smul_mem c E_mem, ?_⟩
    rw [Matrix.mul_smul, Matrix.smul_mul, E_mul_E]

/-- A Lie subalgebra of `M₂(F)` containing a nonzero element has `finrank ≥ 1`. -/
lemma one_le_finrank_of_mem (L : LieSubalgebra F (M2 F)) {Y : M2 F} (hY : Y ∈ L) (hne : Y ≠ 0) :
    1 ≤ Module.finrank F ↥L := by
  haveI : Module.Finite F ↥L.toSubmodule := inferInstance
  haveI : Module.Finite F ↥L := this
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨Y, hY⟩, fun h => hne (congrArg Subtype.val h)⟩

/-- The centralizer in `𝔰𝔩₂` of a conjugate `N = g E g⁻¹` of `E` is the line `F·N`. -/
lemma lieCentralizer_conj_E (g : (M2 F)ˣ) :
    (lieCentralizer (sl2 : LieSubalgebra F (M2 F)) ((g : M2 F) * E * (↑g⁻¹ : M2 F))).toSubmodule =
      Submodule.span F {(g : M2 F) * E * (↑g⁻¹ : M2 F)} := by
  ext Y
  rw [LieSubalgebra.mem_toSubmodule, Submodule.mem_span_singleton]
  constructor
  · intro hY
    rw [mem_lieCentralizer, mem_sl2] at hY
    obtain ⟨htr, hc⟩ := hY
    have hmem : (↑g⁻¹ : M2 F) * Y * (g : M2 F) ∈ lieCentralizer (sl2 : LieSubalgebra F (M2 F)) E := by
      rw [mem_lieCentralizer, mem_sl2, Matrix.trace_units_conj']
      refine ⟨htr, ?_⟩
      have h1 : (↑g⁻¹ : M2 F) * ((g : M2 F) * E * (↑g⁻¹ : M2 F) * Y) * (g : M2 F) =
          (↑g⁻¹ : M2 F) * (Y * ((g : M2 F) * E * (↑g⁻¹ : M2 F))) * (g : M2 F) := by rw [hc]
      simpa [mul_assoc] using h1
    obtain ⟨c, hc'⟩ := (mem_lieCentralizer_E_iff).mp hmem
    refine ⟨c, ?_⟩
    have : Y = (g : M2 F) * ((↑g⁻¹ : M2 F) * Y * (g : M2 F)) * (↑g⁻¹ : M2 F) := by
      simp [mul_assoc]
    rw [this, hc']
    simp
  · rintro ⟨c, rfl⟩
    rw [mem_lieCentralizer, mem_sl2, Matrix.trace_smul, Matrix.trace_units_conj]
    refine ⟨by simp [E, Matrix.trace_fin_two], ?_⟩
    simp only [Matrix.mul_smul, Matrix.smul_mul]

lemma conj_E_ne_zero (g : (M2 F)ˣ) : (g : M2 F) * E * (↑g⁻¹ : M2 F) ≠ 0 := by
  intro h
  apply E_ne_zero (F := F)
  have : (E : M2 F) = (↑g⁻¹ : M2 F) * ((g : M2 F) * E * (↑g⁻¹ : M2 F)) * (g : M2 F) := by
    simp [mul_assoc]
  rw [this, h]; simp

/-- `dim 𝔤_N = 1` for every conjugate `N` of `E`. -/
lemma finrank_lieCentralizer_conj_E (g : (M2 F)ˣ) :
    Module.finrank F ↥(lieCentralizer (sl2 : LieSubalgebra F (M2 F))
      ((g : M2 F) * E * (↑g⁻¹ : M2 F))) = 1 := by
  show Module.finrank F ↥(lieCentralizer (sl2 : LieSubalgebra F (M2 F))
      ((g : M2 F) * E * (↑g⁻¹ : M2 F))).toSubmodule = 1
  rw [lieCentralizer_conj_E]
  exact finrank_span_singleton (conj_E_ne_zero g)

/-- `dim 𝔤_E = 1`. -/
lemma finrank_lieCentralizer_E :
    Module.finrank F ↥(lieCentralizer (sl2 : LieSubalgebra F (M2 F)) E) = 1 := by
  have h := finrank_lieCentralizer_conj_E (F := F) 1
  rwa [inv_one, Units.val_one, one_mul, mul_one] at h

/-- `rank 𝔰𝔩₂ = 1`. -/
lemma lieRank_sl2 : lieRank (sl2 : LieSubalgebra F (M2 F)) = 1 := by
  unfold lieRank
  apply le_antisymm
  · have h : (⨅ X : ↥(sl2 : LieSubalgebra F (M2 F)),
        Module.finrank F ↥(lieCentralizer (sl2 : LieSubalgebra F (M2 F)) (X : M2 F))) ≤
        Module.finrank F ↥(lieCentralizer (sl2 : LieSubalgebra F (M2 F)) E) :=
      ciInf_le (OrderBot.bddBelow _) (⟨E, E_mem⟩ : ↥(sl2 : LieSubalgebra F (M2 F)))
    rw [finrank_lieCentralizer_E] at h
    exact h
  · haveI : Nonempty ↥(sl2 : LieSubalgebra F (M2 F)) := ⟨0⟩
    refine le_ciInf fun X => ?_
    by_cases hX : (X : M2 F) = 0
    · refine one_le_finrank_of_mem _ (Y := E) ?_ E_ne_zero
      rw [mem_lieCentralizer, hX]
      exact ⟨E_mem, by simp⟩
    · exact one_le_finrank_of_mem _ (Y := X) (mem_lieCentralizer.mpr ⟨X.2, rfl⟩) hX

/-- `E` is a regular nilpotent element of `𝔰𝔩₂` (Thesis §4.2, BP §1.6). -/
theorem isRegularNil_E : IsRegularNil (sl2 : LieSubalgebra F (M2 F)) E :=
  ⟨E_mem, isNilpotent_E, by rw [finrank_lieCentralizer_E, lieRank_sl2]⟩

instance : IsModuleTopology F (M2 F) := inferInstanceAs (IsModuleTopology F (Fin 2 → Fin 2 → F))

/-- The group: all of `GL₂(F)`, acting on `𝔰𝔩₂` by conjugation. -/
abbrev GL2 (F : Type*) [Field F] : Subgroup (M2 F)ˣ := ⊤

/-- The regular nilpotent orbit `O_reg = GL₂(F) · E` (all nonzero nilpotents of `𝔰𝔩₂`). -/
def regOrbit : NilOrbit (GL2 F) (sl2 : LieSubalgebra F (M2 F)) :=
  Quotient.mk (nilSetoid _ _) ⟨E, E_mem, isNilpotent_E⟩

lemma E_mem_regOrbit : (⟨E, E_mem⟩ : ↥(sl2 : LieSubalgebra F (M2 F))) ∈ nilOrbitSet (regOrbit (F := F)) :=
  ⟨isNilpotent_E, rfl⟩

/-- `O_reg ∈ Nil_reg(𝔰𝔩₂)`. -/
theorem regOrbit_mem_nilReg : regOrbit (F := F) ∈ NilReg (GL2 F) (sl2 : LieSubalgebra F (M2 F)) := by
  show IsRegularNil _ (Quotient.out (regOrbit (F := F))).1
  obtain ⟨g, -, hg⟩ := Quotient.exact (Quotient.out_eq (regOrbit (F := F))).symm
  obtain ⟨hmem, hnil⟩ := (Quotient.out (regOrbit (F := F))).2
  refine ⟨hmem, hnil, ?_⟩
  rw [← hg, finrank_lieCentralizer_conj_E, lieRank_sl2]

/-! ### The Kirillov form at `E` (Thesis §2.4, BP §1.6): `ω_E(Y,Z) = tr(Y [E,Z])` -/

/-- `E`, `H`, `F` as elements of `𝔰𝔩₂`. -/
def sE : ↥(sl2 : LieSubalgebra F (M2 F)) := ⟨E, E_mem⟩
/-- `H` as an element of `𝔰𝔩₂`. -/
def sH : ↥(sl2 : LieSubalgebra F (M2 F)) := ⟨H, H_mem⟩
/-- `F` as an element of `𝔰𝔩₂`. -/
def sF : ↥(sl2 : LieSubalgebra F (M2 F)) := ⟨Fm, Fm_mem⟩

lemma kirillov_apply (Y Z : ↥(sl2 : LieSubalgebra F (M2 F))) :
    kirillovForm sl2 trForm sE Y Z = ((Y : M2 F) * (E * (Z : M2 F) - (Z : M2 F) * E)).trace := rfl

theorem kirillov_E_HF : kirillovForm sl2 trForm (sE (F := F)) sH sF = 2 := by
  rw [kirillov_apply]
  simp [sH, sF, E, H, Fm, Matrix.trace_fin_two]; norm_num

theorem kirillov_E_FH : kirillovForm sl2 trForm (sE (F := F)) sF sH = -2 := by
  rw [kirillov_apply]
  simp [sH, sF, E, H, Fm, Matrix.trace_fin_two]; norm_num

theorem kirillov_E_HH : kirillovForm sl2 trForm (sE (F := F)) sH sH = 0 := by
  rw [kirillov_apply]
  simp [sH, E, H, Matrix.trace_fin_two]

theorem kirillov_E_FF : kirillovForm sl2 trForm (sE (F := F)) sF sF = 0 := by
  rw [kirillov_apply]
  simp [sF, E, Fm, Matrix.trace_fin_two]

/-! ### The analytic statements (sorried; hand computations) -/

end SL2

section SL2Analytic

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- `O_reg` is not the zero orbit. -/
theorem regOrbit_ne_zeroOrbit :
    regOrbit (F := F) ≠ zeroOrbit (GL2 F) (sl2 : LieSubalgebra F (M2 F)) := by
  intro h
  have := E_mem_regOrbit (F := F)
  rw [h, mem_nilOrbitSet_zeroOrbit] at this
  exact E_ne_zero (congrArg Subtype.val this)


/-- `ω_E(Y,Z) = (y₀₀ - y₁₁) z₁₀ - y₁₀ (z₀₀ - z₁₁)`. -/
lemma kirillov_E_formula (Y Z : ↥(sl2 : LieSubalgebra F (M2 F))) :
    kirillovForm sl2 trForm sE Y Z = ((Y : M2 F) 0 0 - (Y : M2 F) 1 1) * (Z : M2 F) 1 0 -
      (Y : M2 F) 1 0 * ((Z : M2 F) 0 0 - (Z : M2 F) 1 1) := by
  rw [kirillov_apply]
  simp [E, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.vecMul,
    dotProduct]
  ring

/-- `ω_E` is alternating. -/
lemma kirillov_E_antisymm (Y Z : ↥(sl2 : LieSubalgebra F (M2 F))) :
    kirillovForm sl2 trForm sE Y Z = -kirillovForm sl2 trForm sE Z Y := by
  rw [kirillov_E_formula, kirillov_E_formula]; ring

/-- `ker ad E`: `Y ∈ 𝔤_E` iff `y₁₀ = 0` and `y₀₀ = y₁₁`. -/
lemma mem_ker_ad_E_iff (Y : ↥(sl2 : LieSubalgebra F (M2 F))) :
    Y ∈ LinearMap.ker (LieAlgebra.ad F ↥(sl2 : LieSubalgebra F (M2 F)) sE) ↔
      (Y : M2 F) 1 0 = 0 ∧ (Y : M2 F) 0 0 = (Y : M2 F) 1 1 := by
  have hc : ((⁅sE (F := F), Y⁆ : ↥(sl2 : LieSubalgebra F (M2 F))) : M2 F) = E * (Y : M2 F) - (Y : M2 F) * E := by
    rw [LieSubalgebra.coe_bracket, Ring.lie_def]; rfl
  rw [LinearMap.mem_ker, LieAlgebra.ad_apply]
  constructor
  · intro h
    have h' : E * (Y : M2 F) - (Y : M2 F) * E = 0 := by rw [← hc, h]; rfl
    have a := congrFun (congrFun h' 0) 0
    have b := congrFun (congrFun h' 0) 1
    simp [E, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at a b
    exact ⟨a, by linear_combination -b⟩
  · rintro ⟨h1, h2⟩
    apply Subtype.ext
    rw [hc]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, h1, h2]

/-- `ω_E` restricted to a complement `C` of `𝔤_E` is nondegenerate. -/
lemma kirillov_E_compl_nondegenerate (C : Submodule F ↥(sl2 : LieSubalgebra F (M2 F)))
    (hC : IsCompl C (LinearMap.ker (LieAlgebra.ad F ↥(sl2 : LieSubalgebra F (M2 F)) sE))) :
    ((kirillovForm sl2 trForm sE).compl₁₂ C.subtype C.subtype).Nondegenerate := by
  set K := LinearMap.ker (LieAlgebra.ad F ↥(sl2 : LieSubalgebra F (M2 F)) sE)
  -- `ω_E(Y, k) = 0` for `k ∈ 𝔤_E`
  have hrad : ∀ Y k, k ∈ K → kirillovForm sl2 trForm sE Y k = 0 := fun Y k hk => by
    obtain ⟨h1, h2⟩ := (mem_ker_ad_E_iff k).mp hk
    rw [kirillov_E_formula, h1, h2]; ring
  have hL : ∀ Y : ↥C, (∀ Z : ↥C, kirillovForm sl2 trForm sE (Y : ↥(sl2 : LieSubalgebra F (M2 F))) (Z : ↥(sl2 : LieSubalgebra F (M2 F))) = 0) →
      Y = 0 := by
    intro Y hY
    have hall : ∀ Z, kirillovForm sl2 trForm sE (Y : ↥(sl2 : LieSubalgebra F (M2 F))) Z = 0 := fun Z => by
      have hZ : Z ∈ C ⊔ K := by rw [hC.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨c, hc, k, hk, rfl⟩ := Submodule.mem_sup.mp hZ
      rw [map_add, hY ⟨c, hc⟩, hrad _ k hk, add_zero]
    have hH := hall sH
    have hF := hall sF
    rw [kirillov_E_formula] at hH hF
    simp [sH, sF, H, Fm] at hH hF
    have hK : (Y : ↥(sl2 : LieSubalgebra F (M2 F))) ∈ K :=
      (mem_ker_ad_E_iff _).mpr ⟨hH, by linear_combination hF⟩
    have : (Y : ↥(sl2 : LieSubalgebra F (M2 F))) ∈ C ⊓ K := ⟨Y.2, hK⟩
    rw [hC.inf_eq_bot, Submodule.mem_bot] at this
    exact Subtype.ext this
  refine ⟨fun Y hY => hL Y hY, fun Z hZ => hL Z fun Y => ?_⟩
  have := hZ Y
  simp only [LinearMap.compl₁₂_apply, Submodule.coe_subtype] at this
  rw [kirillov_E_antisymm, this, neg_zero]

/-- Self-dual measures exist for `ψ ∘ ω_E` on any complement `C` of `𝔤_E = F·E` (on which `ω_E`
is nondegenerate, `kirillov_E_compl_nondegenerate`: in the basis `H, F` of `𝔤/𝔤_E` its Gram matrix
is `[[0,2],[-2,0]]`). From the literature axiom `exists_isSelfDual` (Tate's thesis; Weil,
*Basic Number Theory*; `Literature/Fourier`), with the subspace topology on `C ⊆ 𝔰𝔩₂ ⊆ M₂(F)`. -/
theorem exists_isSelfDual_kirillov_E (ψ : NontrivialAddChar F)
    (C : Submodule F ↥(sl2 : LieSubalgebra F (M2 F)))
    (hC : IsCompl C (LinearMap.ker (LieAlgebra.ad F ↥(sl2 : LieSubalgebra F (M2 F)) sE))) :
    ∃ ν, IsSelfDual ν ((kirillovForm sl2 trForm sE).compl₁₂ C.subtype C.subtype) ψ :=
  exists_isSelfDual_of_isInducing
    ((sl2 : LieSubalgebra F (M2 F)).incl.toLinearMap ∘ₗ C.subtype)
    (IsInducing.subtypeVal.comp IsInducing.subtypeVal)
    (Subtype.val_injective.comp Subtype.val_injective) _
    (kirillov_E_compl_nondegenerate C hC) ψ

/-- **`IsOrbitMeasure` is satisfiable on a nonzero regular orbit.** The `GL₂(F)`-invariant measure
on `O_reg ≅ GL₂(F)/N(F)`, normalized by the autodual measure for `ψ ∘ ω_E` on `𝔤/𝔤_E` (BP §1.6,
Thesis §2.4). Own `sorry`: it needs the `p`-adic inverse function theorem and
invariant measures on homogeneous spaces. -/
theorem exists_isOrbitMeasure_regOrbit (ψ : NontrivialAddChar F) :
    ∃ μ, IsOrbitMeasure (GL2 F) sl2 trForm ψ regOrbit μ := by
  sorry

/-- **`orbitMeasure O_reg ≠ 0`**: the epsilon does not fall through to `0` on a nonzero regular
orbit (modulo the analytic `sorry` `exists_isOrbitMeasure_regOrbit` above). -/
theorem orbitMeasure_regOrbit_ne_zero (ψ : NontrivialAddChar F) :
    orbitMeasure (GL2 F) sl2 trForm ψ regOrbit ≠ 0 := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl
    (LinearMap.ker (LieAlgebra.ad F ↥(sl2 : LieSubalgebra F (M2 F)) sE))
  exact orbitMeasure_ne_zero (exists_isOrbitMeasure_regOrbit ψ) E_mem_regOrbit hC.symm
    (exists_isSelfDual_kirillov_E ψ C hC.symm)

/-- **`ĵ(O_reg, ·)` on the split torus** (hand computation): for `X = x·H`,
`x ≠ 0`, `ĵ(O_reg, X) = 2 / |α(X)|` with `α(X) = 2x`. Independent of `ψ` (rescaling `ψ` or `b`
does not change `ĵ` for this orbit, since `O_reg` is stable under `F^×`). `|·|` is the normalized
absolute value `absF` (Thesis §2.1); the field norm `‖·‖` of a `PAdicField` need not be normalized.
Checked by hand for every residue characteristic, `p = 2` included. Own `sorry`.

Because `jHat` is defined by three nested epsilons, this statement also *contains* the claims that
(a) a self-dual measure exists for `tr` on `𝔰𝔩₂`, (b) `IsOrbitMeasure` is satisfiable for `O_reg`
(`exists_isOrbitMeasure_regOrbit`), and (c) `IsJHat` is satisfiable, i.e. Harish-Chandra's theorem
that `μ̂_O` is a locally integrable function, continuous on `𝔤_reg` (Harish-Chandra 1973; BP §1.8).
If any of these failed, `jHat` would be `0` and this statement would be false. -/
theorem jHat_regOrbit_split (ψ : NontrivialAddChar F) {x : F} (hx : x ≠ 0) :
    jHat (GL2 F) sl2 trForm ψ regOrbit (x • H) = ((2 / absF ((2 : F) * x) : ℝ) : ℂ) := by
  sorry

/-- **`ĵ(O_reg, ·)` vanishes on regular elliptic elements** (hand computation): `μ_{O_reg}` is the
measure on the whole regular nilpotent cone, parabolically induced from `0` on the Borel, so its
Fourier transform is induced from the split torus. Any residue characteristic.
Own `sorry`. -/
theorem jHat_regOrbit_elliptic (ψ : NontrivialAddChar F) {ε x : F}
    (hε : ¬ IsSquare ε) (hx : x ≠ 0) :
    jHat (GL2 F) sl2 trForm ψ regOrbit (x • !![0, 1; ε, 0]) = 0 := by
  sorry

/-- **`ĵ(O_reg, ·)` is not identically zero near `0`** (so `rodier_germ_one` is not
made vacuous by the normalization), from the split-torus value. -/
theorem jHat_regOrbit_not_eventually_zero (ψ : NontrivialAddChar F) :
    ∀ U ∈ 𝓝 (0 : M2 F), ∃ X ∈ U, jHat (GL2 F) sl2 trForm ψ regOrbit X ≠ 0 := by
  intro U hU
  have ht : Tendsto (fun x : F => x • (H : M2 F)) (𝓝[≠] 0) (𝓝 0) := by
    have : Continuous (fun x : F => x • (H : M2 F)) := continuous_id.smul continuous_const
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨x, hxU, hx0⟩ := ((ht.eventually hU).and self_mem_nhdsWithin).exists
  refine ⟨x • H, hxU, ?_⟩
  rw [jHat_regOrbit_split ψ hx0]
  have : (0 : ℝ) < absF ((2 : F) * x) := absF_pos (mul_ne_zero two_ne_zero hx0)
  exact_mod_cast (div_pos two_pos this).ne'

end SL2Analytic

end NilpotentOrbit

end Sanity

end GSpinGGP

