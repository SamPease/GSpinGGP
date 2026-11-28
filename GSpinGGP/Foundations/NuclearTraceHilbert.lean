import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.l2Space
import TauCeti.Analysis.Normed.Module.ApproximationProperty.SequenceSpace
import TauCeti.Analysis.Normed.Module.ApproximationProperty.TensorProduct
import TauCeti.Analysis.Normed.Module.ApproximationProperty.Transport

/-!
# The nuclear trace on Hilbert spaces

General facts about Tau Ceti's nuclear operators and nuclear trace, used for the trace of
trace-class operators on a Hilbert space (`GSpinGGP.hilbertTrace`).

* `HilbertBasis.hasMetricApproximationProperty`, `InnerProductSpace.hasApproximationProperty`:
  a Hilbert space is isometric to `ℓ²(ι, 𝕜)` through a Hilbert basis, so it has the metric
  approximation property.
* `TauCeti.HasApproximationProperty.ker_toContinuousLinearMap_le_ker_trace`: on a Banach space with
  the approximation property, the tensor trace vanishes on the kernel of
  `E* ⊗̂π E → (E →L[𝕜] E)`, which is the hypothesis of `TauCeti.NuclearOperator.trace`;
  `InnerProductSpace.ker_toContinuousLinearMap_le_ker_trace` is the Hilbert-space case.
* `TauCeti.mem_nuclearOperators_of_hasSum`: an operator with a nuclear series representation
  indexed by any type is nuclear.
* `TauCeti.mem_nuclearOperators_of_finiteDimensional`: an operator out of a finite-dimensional
  inner product space is nuclear.
* `TauCeti.NuclearOperator.hasSum_trace_hilbertBasis`: for every Hilbert basis `b`, the nuclear
  trace of `T` is the unconditional sum `∑ i, ⟪b i, T (b i)⟫`.

## References

* A. Grothendieck, *Produits tensoriels topologiques et espaces nucléaires*, Mem. Amer. Math.
  Soc. **16** (1955).
* B. Simon, *Trace Ideals and Their Applications*, second edition, AMS, 2005, Chapters 1–3.
-/

noncomputable section

open scoped InnerProductSpace lp ENNReal

section ApproximationProperty

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- An inner product space with a Hilbert basis has the metric approximation property: it is
isometric to `ℓ²(ι, 𝕜)`. -/
theorem HilbertBasis.hasMetricApproximationProperty {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    TauCeti.HasMetricApproximationProperty 𝕜 E :=
  b.repr.hasMetricApproximationProperty_iff.2 (TauCeti.hasMetricApproximationProperty_lp (by simp))

variable (𝕜 E) [CompleteSpace E]

/-- A Hilbert space has the approximation property. -/
theorem InnerProductSpace.hasApproximationProperty : TauCeti.HasApproximationProperty 𝕜 E := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  exact (TauCeti.hasMetricApproximationProperty_iff.1
    b.hasMetricApproximationProperty).hasBoundedApproximationProperty.hasApproximationProperty

end ApproximationProperty

namespace TauCeti

section Kernel

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- On a Banach space with the approximation property, the tensor trace `E* ⊗̂π E → 𝕜` vanishes on
the kernel of the canonical operator `E* ⊗̂π E → (E →L[𝕜] E)`: the hypothesis of
`TauCeti.NuclearOperator.trace`. -/
theorem HasApproximationProperty.ker_toContinuousLinearMap_le_ker_trace
    (h : HasApproximationProperty 𝕜 E) :
    (CompletedProjectiveTensor.toContinuousLinearMap 𝕜 E E).ker ≤
      (CompletedProjectiveTensor.trace 𝕜 E).ker := fun u hu ↦
  hasApproximationProperty_iff_trace_eq_zero_of_toContinuousLinearMap_eq_zero.1 h u hu

end Kernel

section Series

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- An operator `T x = ∑ i, f i x • y i` with `∑ i, ‖f i‖ * ‖y i‖ < ∞`, for any index type, is
nuclear. -/
theorem mem_nuclearOperators_of_hasSum {ι : Type*} {T : E →L[𝕜] F} {f : ι → StrongDual 𝕜 E}
    {y : ι → F} (hfy : Summable fun i ↦ ‖f i‖ * ‖y i‖)
    (hT : ∀ x, HasSum (fun i ↦ f i x • y i) (T x)) :
    T ∈ nuclearOperators 𝕜 E F := by
  refine nuclearGauge_lt_top_iff.1 ((nuclearGauge_le_tsum_of_hasSum hT).trans_lt ?_)
  rw [tsum_enorm_mul_enorm_eq_ofReal hfy]
  exact ENNReal.ofReal_lt_top

end Series

section FiniteDimensional

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- Every operator out of a finite-dimensional inner product space is nuclear. -/
theorem mem_nuclearOperators_of_finiteDimensional (T : E →L[𝕜] F) :
    T ∈ nuclearOperators 𝕜 E F := by
  let b := stdOrthonormalBasis 𝕜 E
  have hT : T = ∑ i, (innerSL 𝕜 (b i)).smulRight (T (b i)) := by
    ext v
    conv_lhs => rw [← b.sum_repr' v]
    simp [map_sum, map_smul]
  rw [hT]
  exact Submodule.sum_mem _ fun i _ ↦ smulRight_mem_nuclearOperators _ _

end FiniteDimensional

namespace NuclearOperator

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- **The nuclear trace through a Hilbert basis.** For every Hilbert basis `b` and every nuclear
operator `T` on a Hilbert space, the diagonal sum `∑ i, ⟪b i, T (b i)⟫` converges unconditionally
to the nuclear trace of `T`; in particular it does not depend on `b`.

Proof: write `T v = ∑ n, ⟪z n, v⟫ • y n` with `∑ n, ‖z n‖ * ‖y n‖ < ∞` (Riesz). The double family
`⟪z n, b i⟫ * ⟪b i, y n⟫` is absolutely summable, its row `n` having norm sum at most
`‖z n‖ * ‖y n‖` by Cauchy–Schwarz in `ℓ²`. Summing over `i` first gives `∑ n, ⟪z n, y n⟫` by
Parseval, the nuclear trace; summing over `n` first gives `∑ i, ⟪b i, T (b i)⟫`. -/
theorem hasSum_trace_hilbertBasis
    (hker : (CompletedProjectiveTensor.toContinuousLinearMap 𝕜 E E).ker ≤
      (CompletedProjectiveTensor.trace 𝕜 E).ker)
    {ι : Type*} (b : HilbertBasis ι 𝕜 E) (T : NuclearOperator 𝕜 E E) :
    HasSum (fun i ↦ ⟪b i, T.toContinuousLinearMap (b i)⟫_𝕜) (trace hker T) := by
  obtain ⟨f, y, hfy, hTf⟩ := mem_nuclearOperators_iff_exists_hasSum.1 T.toContinuousLinearMap_mem
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
  have htr : HasSum (fun n ↦ f n (y n)) (trace hker T) := hasSum_trace hker hfy hTf
  have hn : ∀ n, HasSum (fun i ↦ g (n, i)) (f n (y n)) := fun n ↦ by
    rw [hz]
    exact b.hasSum_inner_mul_inner (z n) (y n)
  have htot : HasSum g (trace hker T) := by
    have h := hg.hasSum.prod_fiberwise hn
    rw [htr.unique h]
    exact hg.hasSum
  have hi : ∀ i, HasSum (fun n ↦ (g ∘ Equiv.prodComm ι ℕ) (i, n))
      ⟪b i, T.toContinuousLinearMap (b i)⟫_𝕜 := fun i ↦ by
    have h := (hTf (b i)).mapL (innerSL 𝕜 (b i))
    simpa [g, hz, inner_smul_right] using h
  exact ((Equiv.hasSum_iff (Equiv.prodComm ι ℕ)).2 htot).prod_fiberwise hi

end NuclearOperator

end TauCeti

namespace InnerProductSpace

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- On a Hilbert space the tensor trace vanishes on the kernel of `E* ⊗̂π E → (E →L[𝕜] E)`, so the
nuclear trace `TauCeti.NuclearOperator.trace` is defined. -/
theorem ker_toContinuousLinearMap_le_ker_trace :
    (TauCeti.CompletedProjectiveTensor.toContinuousLinearMap 𝕜 E E).ker ≤
      (TauCeti.CompletedProjectiveTensor.trace 𝕜 E).ker :=
  (hasApproximationProperty 𝕜 E).ker_toContinuousLinearMap_le_ker_trace

end InnerProductSpace
