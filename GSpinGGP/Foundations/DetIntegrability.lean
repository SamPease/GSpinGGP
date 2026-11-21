/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.TorusIntegrability
import GSpinGGP.Foundations.CyclicCommutant

/-!
# Local integrability of `|det|^a` on a commutative family of endomorphisms

Let `A` be a semisimple, injective endomorphism of a finite-dimensional space `K` over a `p`-adic
field `F` whose commutant is commutative, and `ρ : V → End(K)` a linear family of endomorphisms
commuting with `A` whose image contains the odd powers `A^{2k+1}`.  Then `v ↦ |det ρ(v)|_F^a` is
locally integrable on `V` for every `a > −1/2` (`locallyIntegrable_absF_det_rpow_of_odd_pow`).

This is the Lie-algebra form of the torus estimate behind BP Astérisque 418, Lemma B.1.2: on a
maximal torus `𝔱` of `so(W'')` acting on a `𝔱`-stable subspace `K`, the eigenvalues come in pairs
`±μ_i` with `μ_i` independent, so each `μ_i` is counted twice in `det`.  Here the pairing is
replaced by a rank count over `F`, without eigencharacters:

* `K` is the direct sum of minimal `A`-invariant subspaces `K_j`
  (`Module.End.IsSemisimple.exists_supIndep_minimal`); each `ρ(v)` preserves them (it commutes
  with the projections, which commute with `A`), and `ρ(v)|_{K_j}` is `0` or invertible (its kernel
  is `A`-invariant).  So `|det ρ(v)| = ∏_j |det ρ(v)|_{K_j}|`, a product of gauges of degree
  `dim K_j` (`locallyIntegrable_prod_gauge_rpow`).
* Rank condition: for `M = ⊕_{j ∈ J} K_j`, the restrictions of `ρ(V)` to `M` contain the odd powers
  of `A_M = A|_M`.  The commutant of `A_M` is commutative (`commute_restrict_of_commute'`), so its
  characteristic polynomial is squarefree and its minimal polynomial has degree `dim M`
  (`finrank_le_natDegree_minpoly_of_squarefree`); hence the odd powers span a space of dimension
  `≥ dim M / 2` (`finrank_le_two_mul_of_odd_pow_mem`): `2 · rank ≥ ∑_{j∈J} dim K_j`.
-/

noncomputable section

open Module Polynomial MeasureTheory

set_option linter.style.haveILetI false

namespace GSpinGGP

section Integrability

universe u

variable {F : Type*} [NontriviallyNormedField F] [LocallyCompactSpace F]

/-- **Local integrability of `|det|^a` on a commutative family with odd powers** (the Lie-algebra
form of BP Astérisque 418, Lemma B.1.2, for a torus whose characters come in pairs `±μ_i`).
Let `A` be a semisimple injective endomorphism of `K` whose commutant is commutative, and
`ρ : V → End(K)` linear with `ρ(v)` commuting with `A` and `A^{2k+1} ∈ ρ(V)` for all `k`.  Then
`v ↦ |det ρ(v)|_F^a` is locally integrable for every `a > −1/2`.

Proof: `K = ⊕_j K_j` with `K_j` minimal `A`-invariant; `ρ(v)` preserves each `K_j` and is `0` or
invertible there, so `N_j(v) = |det ρ(v)|_{K_j}|` is a gauge of degree `dim K_j` on a complement of
its kernel; for `M = ⊕_{j∈J} K_j`, the restrictions `ρ(V)|_M` contain the odd powers of `A|_M`,
whose minimal polynomial has degree `dim M`, so `2 · rank ≥ ∑_{j∈J} dim K_j`
(`finrank_le_two_mul_of_odd_pow_mem`) and `locallyIntegrable_prod_gauge_rpow` applies. -/
theorem locallyIntegrable_absF_det_rpow_of_odd_pow [IsUltrametricDist F] [PerfectField F]
    {V : Type u} [NormedAddCommGroup V] [NormedSpace F V] [FiniteDimensional F V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    {K : Type*} [AddCommGroup K] [Module F K] [FiniteDimensional F K]
    (ρ : V →ₗ[F] Module.End F K) {A : Module.End F K} (hA : A.IsSemisimple)
    (hAinj : Function.Injective A)
    (hcomm : ∀ g g' : Module.End F K, Commute A g → Commute A g' → Commute g g')
    (hρ : ∀ v, Commute A (ρ v)) (hodd : ∀ k : ℕ, A ^ (2 * k + 1) ∈ LinearMap.range ρ)
    {a : ℝ} (ha : -(1 / 2) < a) :
    LocallyIntegrable (fun v => absF (LinearMap.det (ρ v)) ^ a) μ := by
  classical
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : CompleteSpace F := complete_of_proper
  obtain ⟨s, hind, htop, hBs⟩ := hA.exists_supIndep_minimal
  let B : ↥s → Submodule F K := fun i => i.1
  have hBi : iSupIndep B := iSupIndep_comp_coe_iff_supIndep.mpr hind
  have hBtop : iSup B = ⊤ := by
    rw [← htop, Finset.sup_eq_iSup, iSup_subtype']; rfl
  have hint : DirectSum.IsInternal B :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top B).mpr ⟨hBi, hBtop⟩
  have hBA : ∀ i, ∀ u ∈ B i, A u ∈ B i := fun i => (hBs i.1 i.2).1
  have hB0 : ∀ i, B i ≠ ⊥ := fun i => (hBs i.1 i.2).2.1
  have hBmin : ∀ i, ∀ N : Submodule F K, (∀ v ∈ N, A v ∈ N) → N ≤ B i → N = ⊥ ∨ N = B i :=
    fun i => (hBs i.1 i.2).2.2
  -- `ρ v` preserves every block: it commutes with the projections onto them
  have hmaps : ∀ v i, ∀ u ∈ B i, ρ v u ∈ B i := by
    intro v i u hu
    set C : Submodule F K := ⨆ (j : ↥s) (_ : j ≠ i), B j
    have hC : ∀ w ∈ C, A w ∈ C := by
      have : C ≤ C.comap A := iSup₂_le fun j hj => le_trans
        (show B j ≤ (B j).comap A from fun w hw => hBA j w hw)
        (Submodule.comap_mono (le_iSup₂ (f := fun (j : ↥s) (_ : j ≠ i) => B j) j hj))
      exact fun w hw => this hw
    have hcompl : IsCompl (B i) C := by
      refine ⟨hBi i, codisjoint_iff.mpr (eq_top_iff.mpr ?_)⟩
      rw [← hBtop]
      refine iSup_le fun j => ?_
      by_cases hji : j = i
      · exact hji ▸ le_sup_left
      · exact le_sup_of_le_right (le_iSup₂ (f := fun (j : ↥s) (_ : j ≠ i) => B j) j hji)
    have hP : Commute A ((B i).subtype ∘ₗ Submodule.projectionOnto (B i) C hcompl) :=
      ((LinearMap.IsIdempotentElem.commute_iff (Submodule.isIdempotentElem_projection hcompl)).mpr
        ⟨by rw [Submodule.range_projection]; exact hBA i,
          by rw [Submodule.ker_projection]; exact hC⟩).symm
    have hPρ := hcomm _ _ hP (hρ v)
    have hu' : (B i).subtype (Submodule.projectionOnto (B i) C hcompl u) = u := by
      rw [Submodule.subtype_apply, Submodule.projectionOnto_apply_left hcompl ⟨u, hu⟩]
    rw [← hu']
    have := LinearMap.congr_fun hPρ.eq u
    simp only [mul_apply_eq_comp, LinearMap.comp_apply] at this
    rw [← this]
    exact Submodule.coe_mem _
  -- the block maps
  let ρb : ∀ i, V →ₗ[F] Module.End F (B i) := fun i =>
    { toFun := fun v => (ρ v).restrict (hmaps v i)
      map_add' := fun v w => LinearMap.ext fun u => Subtype.ext (by simp)
      map_smul' := fun c v => LinearMap.ext fun u => Subtype.ext (by simp) }
  have hρb : ∀ i v, ρb i v = (ρ v).restrict (hmaps v i) := fun _ _ => rfl
  -- on a block, `ρ v` is `0` or invertible
  have hdet0 : ∀ i v, ρb i v ≠ 0 → LinearMap.det (ρb i v) ≠ 0 := by
    intro i v hv
    set N : Submodule F K := (LinearMap.ker (ρb i v)).map (B i).subtype
    have hNA : ∀ w ∈ N, A w ∈ N := by
      rintro _ ⟨w, hw, rfl⟩
      have hw' : ρ v (w : K) = 0 := by
        have := congrArg Subtype.val (LinearMap.mem_ker.mp hw)
        simpa [hρb] using this
      refine ⟨⟨A w, hBA i w w.2⟩, LinearMap.mem_ker.mpr (Subtype.ext ?_), rfl⟩
      simp only [hρb, LinearMap.coe_restrict_apply, ZeroMemClass.coe_zero]
      rw [← mul_apply_eq_comp, ← (hρ v).eq, mul_apply_eq_comp, hw', map_zero]
    rcases hBmin i N hNA (Submodule.map_subtype_le _ _) with hN | hN
    · have hker : LinearMap.ker (ρb i v) = ⊥ := eq_bot_iff.mpr fun w hw => by
        have : (w : K) ∈ N := ⟨w, hw, rfl⟩
        rw [hN] at this
        exact (Submodule.mem_bot F).mpr (Subtype.ext ((Submodule.mem_bot F).mp this))
      exact (LinearMap.isUnit_iff_isUnit_det _).mp ((LinearMap.isUnit_iff_ker_eq_bot _).mpr hker)
        |>.ne_zero
    · exfalso
      refine hv (LinearMap.ext fun w => ?_)
      have : (w : K) ∈ N := by rw [hN]; exact w.2
      obtain ⟨w', hw', hww'⟩ := this
      rw [show w = w' from Subtype.ext hww'.symm]
      exact hw'
  -- complements of the kernels in `V`
  have hCex : ∀ i, ∃ C : Submodule F V, IsCompl C (LinearMap.ker (ρb i)) :=
    fun i => Submodule.exists_isCompl _ |>.imp fun _ h => h.symm
  choose Cv hCv using hCex
  let π : ∀ i, V →ₗ[F] Cv i := fun i => Submodule.projectionOnto (Cv i) _ (hCv i)
  have hπρ : ∀ i v, ρb i (π i v) = ρb i v := by
    intro i v
    obtain ⟨c, k, rfl, -⟩ := Submodule.existsUnique_add_of_isCompl (hCv i) v
    have e1 : π i (c : V) = c := Submodule.projectionOnto_apply_left (hCv i) c
    have e2 : π i (k : V) = 0 := Submodule.projectionOnto_apply_right (hCv i) k
    rw [map_add, e1, e2, add_zero, map_add, LinearMap.mem_ker.mp k.2, add_zero]
  have hkerπ : ∀ i v, π i v = 0 ↔ ρb i v = 0 := by
    intro i v
    rw [← LinearMap.mem_ker, ← LinearMap.mem_ker, Submodule.ker_projectionOnto]
  -- the gauges
  let N : ∀ i, ↥(Cv i) → ℝ := fun i c => absF (LinearMap.det (ρb i c))
  have hNc : ∀ i, Continuous (N i) := by
    intro i
    let b := Module.finBasis F (B i)
    have hlin : Continuous fun c : ↥(Cv i) => LinearMap.toMatrix b b (ρb i c) :=
      ((LinearMap.toMatrix b b).toLinearMap ∘ₗ
        (ρb i ∘ₗ (Cv i).subtype)).continuous_of_finiteDimensional
    refine continuous_absF.comp ?_
    have : Continuous fun c : ↥(Cv i) => (LinearMap.toMatrix b b (ρb i c)).det := hlin.matrix_det
    simpa only [LinearMap.det_toMatrix] using this
  have hNpos : ∀ i (c : ↥(Cv i)), c ≠ 0 → 0 < N i c := by
    intro i c hc
    refine absF_pos (hdet0 i c fun h0 => hc ?_)
    have hk : (c : V) ∈ LinearMap.ker (ρb i) := h0
    exact Subtype.ext ((Submodule.disjoint_def.mp (hCv i).disjoint) _ c.2 hk)
  have hNhom : ∀ i (r : F) (c : ↥(Cv i)), N i (r • c) = absF r ^ (finrank F (B i) : ℝ) * N i c := by
    intro i r c
    simp only [N, Submodule.coe_smul, map_smul, LinearMap.det_smul, absF_mul, absF_pow,
      Real.rpow_natCast]
  have he : ∀ i, (0 : ℝ) < finrank F (B i) := fun i => by
    haveI := Submodule.nontrivial_iff_ne_bot.mpr (hB0 i)
    exact_mod_cast Module.finrank_pos (R := F) (M := B i)
  -- the function is the gauge product
  have hfun : (fun v => absF (LinearMap.det (ρ v)) ^ a) =
      fun v => ∏ i, N i (π i v) ^ a := by
    funext v
    rw [IsomCent.det_eq_prod_det_restrict hint (ρ v) (fun i => hmaps v i), absF_prod,
      ← Real.finsetProd_rpow _ _ (fun i _ => absF_nonneg _)]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [N, hπρ]
    rfl
  rw [hfun]
  refine locallyIntegrable_prod_gauge_rpow N hNc hNpos (fun i => (finrank F (B i) : ℝ)) he hNhom
    (fun _ => a) Finset.univ μ π fun J _ hJ => ?_
  -- the rank condition
  set MJ : Submodule F K := ⨆ j ∈ J, B j
  have hMA : ∀ w ∈ MJ, A w ∈ MJ := by
    have : MJ ≤ MJ.comap A := iSup₂_le fun j hj => le_trans
      (show B j ≤ (B j).comap A from fun w hw => hBA j w hw) (Submodule.comap_mono (le_biSup B hj))
    exact fun w hw => this hw
  have hMρ : ∀ v, ∀ w ∈ MJ, ρ v w ∈ MJ := by
    intro v
    have : MJ ≤ MJ.comap (ρ v) := iSup₂_le fun j hj => le_trans
      (show B j ≤ (B j).comap (ρ v) from fun w hw => hmaps v j w hw)
      (Submodule.comap_mono (le_biSup B hj))
    exact fun w hw => this hw
  let R : V →ₗ[F] Module.End F MJ :=
    { toFun := fun v => (ρ v).restrict (hMρ v)
      map_add' := fun v w => LinearMap.ext fun u => Subtype.ext (by simp)
      map_smul' := fun c v => LinearMap.ext fun u => Subtype.ext (by simp) }
  have hker : LinearMap.ker R = LinearMap.ker (LinearMap.pi fun j : J => π j) := by
    ext v
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    constructor
    · intro hv
      funext j
      refine (hkerπ j v).mpr (LinearMap.ext fun u => Subtype.ext ?_)
      have := congrArg Subtype.val (LinearMap.congr_fun hv ⟨u, le_biSup B j.2 u.2⟩)
      simpa [R, hρb] using this
    · intro hv
      have hj : ∀ j ∈ J, ρb j v = 0 := fun j hj => (hkerπ j v).mp (congrFun hv ⟨j, hj⟩)
      have hle : MJ ≤ LinearMap.ker (ρ v) := by
        refine iSup₂_le fun j hjJ => ?_
        intro w hw
        have := congrArg Subtype.val (LinearMap.congr_fun (hj j hjJ) ⟨w, hw⟩)
        simpa [hρb] using this
      exact LinearMap.ext fun u => Subtype.ext (by simpa [R] using hle u.2)
  have hrank : finrank F (LinearMap.range (LinearMap.pi fun j : J => π j)) =
      finrank F (LinearMap.range R) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker R
    have h2 := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi fun j : J => π j)
    rw [hker] at h1
    omega
  -- the odd powers of `A|_M`
  set AM := A.restrict hMA
  have hAMinj : Function.Injective AM := fun u w h =>
    Subtype.ext (hAinj (congrArg Subtype.val h))
  have hAMc : ∀ g g' : Module.End F MJ, Commute AM g → Commute AM g' → Commute g g' :=
    fun g g' hg hg' => commute_restrict_of_commute' hA hcomm hMA hg hg'
  have hAMdeg : finrank F MJ ≤ (minpoly F AM).natDegree :=
    finrank_le_natDegree_minpoly_of_squarefree
      (squarefree_charpoly_of_commute (hA.restrict (fun w hw => hMA w hw)) hAMc)
  have hAModd : ∀ k : ℕ, AM ^ (2 * k + 1) ∈ LinearMap.range R := by
    intro k
    obtain ⟨v, hv⟩ := hodd k
    refine ⟨v, LinearMap.ext fun u => Subtype.ext ?_⟩
    change ρ v u = ((AM ^ (2 * k + 1)) u : K)
    rw [hv, Module.End.pow_restrict, LinearMap.coe_restrict_apply]
  have hMdim := finrank_le_two_mul_of_odd_pow_mem hAMinj hAMdeg _ hAModd
  have hD := finrank_biSup_eq_sum hBi J
  have hDpos : (0 : ℝ) < ∑ j ∈ J, (finrank F (B j) : ℝ) :=
    Finset.sum_pos (fun j _ => he j) hJ
  rw [hrank, ← Finset.sum_mul]
  have hD' : (∑ j ∈ J, (finrank F (B j) : ℝ)) ≤ 2 * (finrank F (LinearMap.range R) : ℝ) := by
    have : ∑ j ∈ J, finrank F (B j) ≤ 2 * finrank F (LinearMap.range R) := hD ▸ hMdim
    exact_mod_cast this
  nlinarith

end Integrability

end GSpinGGP
