import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.l2Space
import TauCeti.Analysis.Normed.Module.ApproximationProperty.SequenceSpace
import TauCeti.Analysis.Normed.Module.ApproximationProperty.TensorProduct
import TauCeti.Analysis.Normed.Module.ApproximationProperty.Transport
import TauCeti.Analysis.OperatorIdeal.Nuclear.Comparison

/-!
# The trace of a nuclear operator on a Hilbert space

Let `E` be a Hilbert space over `𝕜 = ℝ` or `ℂ`. An operator `T : E →L[𝕜] E` is *nuclear*
(`TauCeti.nuclearOperators`) when `T v = ∑ n, f n v • y n` for functionals `f n` and vectors `y n`
with `∑ n, ‖f n‖ * ‖y n‖ < ∞`. Tau Ceti defines the nuclear trace
`TauCeti.NuclearOperator.trace`, `∑ n, f n (y n)`, on every Banach space for which the tensor trace
vanishes on the kernel of `E* ⊗̂π E → (E →L[𝕜] E)`; by Grothendieck this is the approximation
property. A Hilbert space has the metric approximation property, being isometric to `ℓ²(ι, 𝕜)`
through a Hilbert basis, so the nuclear trace is defined on every Hilbert space.

`GSpinGGP.hilbertTrace T` is that trace when `T` is nuclear and `0` otherwise. The definition
involves no choice of basis or of series representation. For every Hilbert basis `b` of `E` and
every nuclear `T`, `∑ i, ⟪b i, T (b i)⟫` converges unconditionally to `hilbertTrace T`
(`GSpinGGP.hasSum_hilbertTrace`): the familiar definition of the trace through a basis is a
theorem, and in particular it does not depend on the basis.

The nuclear operators are contained in the trace class (summable approximation numbers,
`ContinuousLinearMap.nuclearENorm ≠ ∞`; Tau Ceti
`ContinuousLinearMap.nuclearENorm_le_nuclearGauge`). On Hilbert spaces the two classes coincide
(Schmidt decomposition), but the reverse inclusion is not available in Mathlib or Tau Ceti. The
definition is guarded by nuclearity, so that every
statement here is proved; an operator of infinite `nuclearENorm` has trace `0`
(`GSpinGGP.hilbertTrace_eq_zero_of_nuclearENorm_eq_top`).

## Main declarations

* `GSpinGGP.hasApproximationProperty_of_innerProductSpace`: Hilbert spaces have the approximation
  property.
* `GSpinGGP.hilbertTrace`: the trace, with junk value `0` off the nuclear operators.
* `GSpinGGP.hasSum_hilbertTrace`: the trace is `∑ i, ⟪b i, T (b i)⟫` for every Hilbert basis `b`.
* `GSpinGGP.hasSum_hilbertTrace_of_hasSum`: the trace of `∑ n, f n (·) • y n` is `∑ n, f n (y n)`.
* `GSpinGGP.hilbertTrace_add`, `GSpinGGP.hilbertTrace_smul`: linearity on nuclear operators.
* `GSpinGGP.hilbertTrace_smulRight`, `GSpinGGP.hilbertTrace_innerSL_smulRight`: rank-one operators.
* `GSpinGGP.hilbertTrace_comp_comm`: `tr (A T) = tr (T A)` for `T` nuclear.
* `GSpinGGP.hilbertTrace_eq_trace`: in finite dimension, `hilbertTrace` is `LinearMap.trace`.
* `GSpinGGP.hilbertTrace_id_of_not_finiteDimensional`: the identity of an infinite-dimensional
  Hilbert space is not trace class, so its trace is the junk value `0`.

## References

* A. Grothendieck, *Produits tensoriels topologiques et espaces nucléaires*, Mem. Amer. Math.
  Soc. **16** (1955).
* B. Simon, *Trace Ideals and Their Applications*, second edition, AMS, 2005, Chapters 1–3.
-/

noncomputable section

open scoped InnerProductSpace lp ENNReal

open TauCeti

namespace GSpinGGP

section ApproximationProperty

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- An inner product space with a Hilbert basis has the metric approximation property: it is
isometric to `ℓ²(ι, 𝕜)`. -/
theorem hasMetricApproximationProperty_of_hilbertBasis {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    HasMetricApproximationProperty 𝕜 E :=
  b.repr.hasMetricApproximationProperty_iff.2 (hasMetricApproximationProperty_lp (by simp))

variable (𝕜 E) [CompleteSpace E]

/-- A Hilbert space has the approximation property. -/
theorem hasApproximationProperty_of_innerProductSpace : HasApproximationProperty 𝕜 E := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  exact (hasMetricApproximationProperty_iff.1
    (hasMetricApproximationProperty_of_hilbertBasis b)).hasApproximationProperty

/-- On a Hilbert space the canonical operator `E* ⊗̂π E → (E →L[𝕜] E)` is injective, so the
tensor trace vanishes on its kernel: this is the hypothesis of `TauCeti.NuclearOperator.trace`. -/
theorem ker_toContinuousLinearMap_le_ker_trace :
    (CompletedProjectiveTensor.toContinuousLinearMap 𝕜 E E).ker ≤
      (CompletedProjectiveTensor.trace 𝕜 E).ker := by
  intro u hu
  have hinj := CompletedProjectiveTensor.injective_toContinuousLinearMap_of_hasApproximationProperty
    (E := E) (hasApproximationProperty_of_innerProductSpace 𝕜 E)
  have hu0 : u = 0 := hinj (by simpa using hu)
  simp [hu0]

end ApproximationProperty

section Trace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

open Classical in
/-- The **trace** of a bounded operator `T` on a Hilbert space: the nuclear trace
`∑ n, f n (y n)` of any representation `T v = ∑ n, f n v • y n` with `∑ n, ‖f n‖ * ‖y n‖ < ∞`
when `T` is nuclear (trace class), and the junk value `0` otherwise. For every Hilbert basis `b`
it equals `∑ i, ⟪b i, T (b i)⟫` (`hasSum_hilbertTrace`). -/
def hilbertTrace (T : E →L[𝕜] E) : 𝕜 :=
  if hT : T ∈ nuclearOperators 𝕜 E E then
    NuclearOperator.trace (ker_toContinuousLinearMap_le_ker_trace 𝕜 E) (NuclearOperator.mk' hT)
  else 0

theorem hilbertTrace_of_mem {T : E →L[𝕜] E} (hT : T ∈ nuclearOperators 𝕜 E E) :
    hilbertTrace T =
      NuclearOperator.trace (ker_toContinuousLinearMap_le_ker_trace 𝕜 E) (NuclearOperator.mk' hT) :=
  dite_eq_left hT

/-- The junk value: the trace of an operator that is not nuclear is `0`. -/
theorem hilbertTrace_of_notMem {T : E →L[𝕜] E} (hT : T ∉ nuclearOperators 𝕜 E E) :
    hilbertTrace T = 0 :=
  dite_eq_right hT

/-- On `TauCeti.NuclearOperator 𝕜 E E`, `hilbertTrace` is Tau Ceti's nuclear trace. -/
theorem hilbertTrace_toContinuousLinearMap (T : NuclearOperator 𝕜 E E) :
    hilbertTrace T.toContinuousLinearMap =
      NuclearOperator.trace (ker_toContinuousLinearMap_le_ker_trace 𝕜 E) T := by
  rw [hilbertTrace_of_mem T.toContinuousLinearMap_mem]
  rfl

/-- An operator whose approximation numbers are not summable has trace `0`. -/
theorem hilbertTrace_eq_zero_of_nuclearENorm_eq_top {T : E →L[𝕜] E} (h : T.nuclearENorm = ∞) :
    hilbertTrace T = 0 := by
  refine hilbertTrace_of_notMem fun hT ↦ ?_
  have := (nuclearGauge_lt_top_iff.2 hT).trans_le' T.nuclearENorm_le_nuclearGauge
  simp [h] at this

/-- **Trace of a nuclear series.** If `T v = ∑ i, f i v • y i` with `∑ i, ‖f i‖ * ‖y i‖ < ∞`, then
`T` is nuclear and its trace is `∑ i, f i (y i)`. -/
theorem hasSum_hilbertTrace_of_hasSum {ι : Type*} {T : E →L[𝕜] E} {f : ι → StrongDual 𝕜 E}
    {y : ι → E} (hfy : Summable fun i ↦ ‖f i‖ * ‖y i‖)
    (hT : ∀ v, HasSum (fun i ↦ f i v • y i) (T v)) :
    HasSum (fun i ↦ f i (y i)) (hilbertTrace T) := by
  have hmem : T ∈ nuclearOperators 𝕜 E E := by
    refine nuclearGauge_lt_top_iff.1 ((nuclearGauge_le_tsum_of_hasSum hT).trans_lt ?_)
    rw [tsum_enorm_mul_enorm_eq_ofReal hfy]
    exact ENNReal.ofReal_lt_top
  rw [hilbertTrace_of_mem hmem]
  exact NuclearOperator.hasSum_trace _ hfy hT

/-- **Basis independence.** For every Hilbert basis `b` and every nuclear operator `T`, the
diagonal sum `∑ i, ⟪b i, T (b i)⟫` converges unconditionally to `hilbertTrace T`.

Proof: write `T v = ∑ n, ⟪z n, v⟫ • y n` with `∑ n, ‖z n‖ * ‖y n‖ < ∞` (Riesz). The double family
`⟪z n, b i⟫ * ⟪b i, y n⟫` is absolutely summable, its row `n` having norm sum at most
`‖z n‖ * ‖y n‖` by Cauchy–Schwarz in `ℓ²`. Summing over `i` first gives `∑ n, ⟪z n, y n⟫` by
Parseval, the nuclear trace; summing over `n` first gives `∑ i, ⟪b i, T (b i)⟫`. -/
theorem hasSum_hilbertTrace {ι : Type*} (b : HilbertBasis ι 𝕜 E) {T : E →L[𝕜] E}
    (hT : T ∈ nuclearOperators 𝕜 E E) :
    HasSum (fun i ↦ ⟪b i, T (b i)⟫_𝕜) (hilbertTrace T) := by
  obtain ⟨f, y, hfy, hTf⟩ := mem_nuclearOperators_iff_exists_hasSum.1 hT
  set z : ℕ → E := fun n ↦ (InnerProductSpace.toDual 𝕜 E).symm (f n)
  have hz : ∀ n v, f n v = ⟪z n, v⟫_𝕜 := fun n v ↦ by
    simp [z, InnerProductSpace.toDual_symm_apply]
  have hnz : ∀ n, ‖z n‖ = ‖f n‖ := fun n ↦ by simp [z]
  set g : ℕ × ι → 𝕜 := fun p ↦ ⟪z p.1, b p.2⟫_𝕜 * ⟪b p.2, y p.1⟫_𝕜
  have hrow : ∀ n, Summable (fun i ↦ ‖g (n, i)‖) ∧ ∑' i, ‖g (n, i)‖ ≤ ‖f n‖ * ‖y n‖ := by
    intro n
    have hH := lp.tsum_mul_le_mul_norm (p := 2) (q := 2)
      (by simpa using Real.HolderConjugate.two_two) (b.repr (z n)) (b.repr (y n))
    simp only [b.repr_apply_apply, LinearIsometryEquiv.norm_map, hnz] at hH
    have hgn : (fun i ↦ ‖g (n, i)‖) = fun i ↦ ‖⟪b i, z n⟫_𝕜‖ * ‖⟪b i, y n⟫_𝕜‖ := by
      ext i
      simp [g, norm_inner_symm]
    rw [hgn]
    exact hH
  have hg : Summable g := by
    refine Summable.of_norm ?_
    refine (summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)).2 ⟨fun n ↦ (hrow n).1, ?_⟩
    exact Summable.of_nonneg_of_le (fun n ↦ tsum_nonneg fun _ ↦ norm_nonneg _)
      (fun n ↦ (hrow n).2) hfy
  have htr : HasSum (fun n ↦ f n (y n)) (hilbertTrace T) := hasSum_hilbertTrace_of_hasSum hfy hTf
  have hn : ∀ n, HasSum (fun i ↦ g (n, i)) (f n (y n)) := fun n ↦ by
    rw [hz]
    exact b.hasSum_inner_mul_inner (z n) (y n)
  have htot : HasSum g (hilbertTrace T) := by
    have h := hg.hasSum.prod_fiberwise hn
    rw [htr.unique h]
    exact hg.hasSum
  have hi : ∀ i, HasSum (fun n ↦ (g ∘ Equiv.prodComm ι ℕ) (i, n)) ⟪b i, T (b i)⟫_𝕜 := fun i ↦ by
    have h := (hTf (b i)).mapL (innerSL 𝕜 (b i))
    simpa [g, hz, inner_smul_right] using h
  exact ((Equiv.hasSum_iff (Equiv.prodComm ι ℕ)).2 htot).prod_fiberwise hi

/-- `hilbertTrace T = ∑' i, ⟪b i, T (b i)⟫` for every Hilbert basis `b` and nuclear `T`. -/
theorem hilbertTrace_eq_tsum {ι : Type*} (b : HilbertBasis ι 𝕜 E) {T : E →L[𝕜] E}
    (hT : T ∈ nuclearOperators 𝕜 E E) :
    hilbertTrace T = ∑' i, ⟪b i, T (b i)⟫_𝕜 :=
  (hasSum_hilbertTrace b hT).tsum_eq.symm

/-- The trace of the rank-one operator `v ↦ f v • y` is `f y`. -/
@[simp]
theorem hilbertTrace_smulRight (f : StrongDual 𝕜 E) (y : E) :
    hilbertTrace (f.smulRight y) = f y := by
  rw [hilbertTrace_of_mem (smulRight_mem_nuclearOperators f y)]
  exact NuclearOperator.trace_smulRight _ f y

/-- The trace of the rank-one operator `v ↦ ⟪x, v⟫ • y` is `⟪x, y⟫`. -/
theorem hilbertTrace_innerSL_smulRight (x y : E) :
    hilbertTrace ((innerSL 𝕜 x).smulRight y) = ⟪x, y⟫_𝕜 := by
  simp

@[simp]
theorem hilbertTrace_zero : hilbertTrace (0 : E →L[𝕜] E) = 0 := by
  rw [hilbertTrace_of_mem (zero_mem _)]
  convert map_zero (NuclearOperator.trace (ker_toContinuousLinearMap_le_ker_trace 𝕜 E))
  exact OperatorGauge.Carrier.ext (by simp)

theorem hilbertTrace_add {S T : E →L[𝕜] E} (hS : S ∈ nuclearOperators 𝕜 E E)
    (hT : T ∈ nuclearOperators 𝕜 E E) :
    hilbertTrace (S + T) = hilbertTrace S + hilbertTrace T := by
  rw [hilbertTrace_of_mem hS, hilbertTrace_of_mem hT, hilbertTrace_of_mem (add_mem hS hT),
    ← map_add]
  rfl

/-- The trace is homogeneous on all operators (both sides vanish off the nuclear operators). -/
@[simp]
theorem hilbertTrace_smul (c : 𝕜) (T : E →L[𝕜] E) :
    hilbertTrace (c • T) = c * hilbertTrace T := by
  by_cases hT : T ∈ nuclearOperators 𝕜 E E
  · rw [hilbertTrace_of_mem hT, hilbertTrace_of_mem (Submodule.smul_mem _ c hT), ← smul_eq_mul,
      ← map_smul]
    rfl
  · rcases eq_or_ne c 0 with rfl | hc
    · simp
    · rw [hilbertTrace_of_notMem hT, hilbertTrace_of_notMem fun h ↦ hT ?_, mul_zero]
      simpa [hc] using Submodule.smul_mem _ c⁻¹ h

@[simp]
theorem hilbertTrace_neg (T : E →L[𝕜] E) : hilbertTrace (-T) = -hilbertTrace T := by
  simpa using hilbertTrace_smul (-1 : 𝕜) T

theorem hilbertTrace_sub {S T : E →L[𝕜] E} (hS : S ∈ nuclearOperators 𝕜 E E)
    (hT : T ∈ nuclearOperators 𝕜 E E) :
    hilbertTrace (S - T) = hilbertTrace S - hilbertTrace T := by
  rw [sub_eq_add_neg, hilbertTrace_add hS (neg_mem hT), hilbertTrace_neg, ← sub_eq_add_neg]

/-- **Cyclicity.** For a bounded operator `A : E → D` and a nuclear operator `T : D → E` between
Hilbert spaces, `tr (A T) = tr (T A)`. -/
theorem hilbertTrace_comp_comm {D : Type*} [NormedAddCommGroup D] [InnerProductSpace 𝕜 D]
    [CompleteSpace D] (A : E →L[𝕜] D) {T : D →L[𝕜] E} (hT : T ∈ nuclearOperators 𝕜 D E) :
    hilbertTrace (A ∘L T) = hilbertTrace (T ∘L A) := by
  rw [hilbertTrace_of_mem (comp_left_mem_nuclearOperators A hT),
    hilbertTrace_of_mem (comp_right_mem_nuclearOperators hT A)]
  exact NuclearOperator.trace_mk'_comp_comm _ _ A hT

/-- The identity of an infinite-dimensional Hilbert space is not trace class; its trace is the
junk value `0`. -/
theorem hilbertTrace_id_of_not_finiteDimensional (hE : ¬ FiniteDimensional 𝕜 E) :
    hilbertTrace (ContinuousLinearMap.id 𝕜 E) = 0 :=
  hilbertTrace_eq_zero_of_nuclearENorm_eq_top (ContinuousLinearMap.nuclearENorm_id_eq_top hE)

section FiniteDimensional

variable [FiniteDimensional 𝕜 E]

/-- In finite dimension every operator is nuclear. -/
theorem mem_nuclearOperators_of_finiteDimensional (T : E →L[𝕜] E) :
    T ∈ nuclearOperators 𝕜 E E := by
  let b := stdOrthonormalBasis 𝕜 E
  have hT : T = ∑ i, (innerSL 𝕜 (b i)).smulRight (T (b i)) := by
    ext v
    conv_lhs => rw [← b.sum_repr' v]
    simp [map_sum, map_smul]
  rw [hT]
  exact Submodule.sum_mem _ fun i _ ↦ smulRight_mem_nuclearOperators _ _

/-- In finite dimension, `hilbertTrace` is the trace of linear maps. -/
theorem hilbertTrace_eq_trace (T : E →L[𝕜] E) :
    hilbertTrace T = LinearMap.trace 𝕜 E (T : E →ₗ[𝕜] E) := by
  let b := stdOrthonormalBasis 𝕜 E
  have h := hasSum_hilbertTrace b.toHilbertBasis (mem_nuclearOperators_of_finiteDimensional T)
  rw [h.unique (hasSum_fintype _), LinearMap.trace_eq_sum_inner _ b]
  simp

end FiniteDimensional

end Trace

end GSpinGGP
