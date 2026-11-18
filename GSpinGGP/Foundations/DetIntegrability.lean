/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.TorusIntegrability
import GSpinGGP.Foundations.CommutantSquarefree
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

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
  (`Module.End.IsSemisimple.exists_isInternal_minimal`); each `ρ(v)` preserves them (it commutes
  with the projections, which commute with `A`), and `ρ(v)|_{K_j}` is `0` or invertible (its kernel
  is `A`-invariant).  So `|det ρ(v)| = ∏_j |det ρ(v)|_{K_j}|`, a product of gauges of degree
  `dim K_j` (`locallyIntegrable_prod_gauge_rpow`).
* Rank condition: for `M = ⊕_{j ∈ J} K_j`, the restrictions of `ρ(V)` to `M` contain the odd powers
  of `A_M = A|_M`.  The commutant of `A_M` is commutative (`commute_restrict_of_commute`), so its
  characteristic polynomial is squarefree and its minimal polynomial has degree `dim M`
  (`finrank_le_natDegree_minpoly_of_squarefree`); hence the odd powers span a space of dimension
  `≥ dim M / 2` (`finrank_le_two_mul_of_odd_pow_mem`): `2 · rank ≥ ∑_{j∈J} dim K_j`.
-/

noncomputable section

open Module Polynomial MeasureTheory

set_option linter.style.haveILetI false

namespace GSpinGGP

section Cyclic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **A squarefree characteristic polynomial is the minimal polynomial**: if `χ_f` is squarefree
(`K` perfect), the minimal polynomial of `f` has degree `dim V`.  Over `K̄` every root of `χ_f` is an
eigenvalue, hence a root of `minpoly f`; `χ_f` is separable, so it divides `minpoly f`. -/
theorem finrank_le_natDegree_minpoly_of_squarefree [PerfectField K] {f : Module.End K V}
    (hf : Squarefree f.charpoly) : finrank K V ≤ (minpoly K f).natDegree := by
  classical
  let L := AlgebraicClosure K
  let φ := algebraMap K L
  let b := Module.finBasis K V
  set M := LinearMap.toMatrix b b f with hMdef
  have hχ : M.charpoly = f.charpoly := LinearMap.charpoly_toMatrix f b
  have hm : minpoly K M = minpoly K f := LinearMap.minpoly_toMatrix b f
  rcases Nat.eq_zero_or_pos (finrank K V) with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  haveI : Nonempty (Fin (finrank K V)) := ⟨⟨0, hpos⟩⟩
  set m := minpoly K f
  have hm0 : m ≠ 0 := minpoly.ne_zero (LinearMap.isIntegral f)
  have hsep : (f.charpoly.map φ).Separable :=
    (PerfectField.separable_iff_squarefree.mpr hf).map
  have hroots : (f.charpoly.map φ).roots ≤ (m.map φ).roots := by
    rw [Multiset.le_iff_subset (nodup_roots hsep)]
    intro r hr
    have hr' : IsRoot (M.map φ).charpoly r := by
      rw [Matrix.charpoly_map, hχ]; exact isRoot_of_mem_roots hr
    rw [← Matrix.mem_spectrum_iff_isRoot_charpoly] at hr'
    have h1 := spectrum.subset_polynomial_aeval (M.map φ) (m.map φ) ⟨r, hr', rfl⟩
    have h2 : aeval (M.map φ) (m.map φ) = 0 := by
      rw [aeval_map_algebraMap]
      have : M.map φ = (Algebra.ofId K L).mapMatrix M := rfl
      rw [this, aeval_algHom_apply, ← hm, minpoly.aeval, map_zero]
    rw [h2, spectrum.zero_eq] at h1
    exact (mem_roots (Polynomial.map_ne_zero hm0)).mpr h1
  have hdvd := (IsAlgClosed.splits _).dvd_of_roots_le_roots
    (Polynomial.map_ne_zero f.charpoly_monic.ne_zero) hroots
  have := natDegree_le_of_dvd hdvd (Polynomial.map_ne_zero hm0)
  rwa [natDegree_map, natDegree_map, LinearMap.charpoly_natDegree] at this

omit [FiniteDimensional K V] in
/-- **The commutant passes to invariant subspaces**: if `f` is semisimple, `P ≤ U` are
`f`-invariant and the endomorphisms of `U` commuting with `f|_U` commute with each other, then so do
the endomorphisms of `P` commuting with `f|_P` (extend them by `0` on an `f`-invariant complement
of `P`). -/
theorem commute_restrict_of_commute {f : Module.End K V} (hf : f.IsSemisimple)
    {U P : Submodule K V} (hU : ∀ v ∈ U, f v ∈ U) (hP : ∀ v ∈ P, f v ∈ P) (hPU : P ≤ U)
    (hcomm : ∀ g g' : Module.End K U, Commute (f.restrict hU) g → Commute (f.restrict hU) g' →
      Commute g g')
    {g g' : Module.End K P} (hg : Commute (f.restrict hP) g)
    (hg' : Commute (f.restrict hP) g') : Commute g g' := by
  obtain ⟨Q, hQ, hPQ⟩ := Module.End.isSemisimple_iff.mp hf P (fun v hv => hP v hv)
  have hQ' : ∀ v ∈ Q, f v ∈ Q := fun v hv => hQ hv
  set π := Submodule.projectionOnto P Q hPQ
  -- `π` intertwines `f` and `f|_P`
  have hπf : ∀ v, π (f v) = f.restrict hP (π v) := by
    intro v
    obtain ⟨p, q, rfl, -⟩ := Submodule.existsUnique_add_of_isCompl hPQ v
    have e1 : π (p : V) = p := Submodule.projectionOnto_apply_left hPQ p
    have e2 : π (q : V) = 0 := Submodule.projectionOnto_apply_right hPQ q
    have e3 : π (f q) = 0 := Submodule.projectionOnto_apply_right hPQ ⟨f q, hQ' q q.2⟩
    have e4 : π (f p) = f.restrict hP p :=
      Submodule.projectionOnto_apply_left hPQ (f.restrict hP p)
    rw [map_add, map_add, map_add, e1, e2, e3, e4, add_zero, add_zero]
  let ext : Module.End K P → Module.End K U := fun h =>
    (P.subtype ∘ₗ h ∘ₗ π ∘ₗ U.subtype).codRestrict U fun v => hPU (h _).2
  have hext : ∀ h u, ((ext h u : U) : V) = h (π u) := fun _ _ => rfl
  have hcomm_ext : ∀ h : Module.End K P, Commute (f.restrict hP) h →
      Commute (f.restrict hU) (ext h) := by
    intro h hh
    refine LinearMap.ext fun u => Subtype.ext ?_
    simp only [Module.End.mul_apply]
    rw [hext, LinearMap.coe_restrict_apply, hext]
    change f (h (π u)) = h (π (f u))
    rw [hπf, ← Module.End.mul_apply, ← hh.eq]
    rfl
  have hc := hcomm _ _ (hcomm_ext g hg) (hcomm_ext g' hg')
  refine LinearMap.ext fun p => Subtype.ext ?_
  have h1 := congrArg Subtype.val (LinearMap.congr_fun hc.eq ⟨p, hPU p.2⟩)
  simp only [Module.End.mul_apply, hext] at h1
  have hπp : ∀ p' : P, π (p' : V) = p' := Submodule.projectionOnto_apply_left hPQ
  have hπU : ∀ p' : P, π ((⟨p', hPU p'.2⟩ : U) : V) = p' := hπp
  rw [hπU, hπp, hπp] at h1
  simpa only [Module.End.mul_apply] using h1

/-- **Odd powers span at least half the dimension**: if `f` is injective and its minimal polynomial
has degree `dim V`, any subspace `R ⊆ End(V)` containing all `f^{2k+1}` has `dim V ≤ 2 dim R`.
With `r = deg minpoly(f²)`: `minpoly f ∣ minpoly(f²)(X²)`, so `dim V ≤ 2r`, and
`f, f³, …, f^{2r−1}` are independent (`f · h(f²) = 0` forces `h(f²) = 0`). -/
theorem finrank_le_two_mul_of_odd_pow_mem {f : Module.End K V} (hinj : Function.Injective f)
    (hdeg : finrank K V ≤ (minpoly K f).natDegree) (R : Submodule K (Module.End K V))
    (hR : ∀ k : ℕ, f ^ (2 * k + 1) ∈ R) : finrank K V ≤ 2 * finrank K R := by
  classical
  set q := minpoly K (f ^ 2) with hq
  set r := q.natDegree
  have hqm : q.Monic := minpoly.monic (LinearMap.isIntegral _)
  -- `dim V ≤ 2r`
  have h1 : (minpoly K f).natDegree ≤ 2 * r := by
    have hX2 : (X ^ 2 : K[X]).natDegree = 2 := natDegree_X_pow 2
    have hmon : (q.comp (X ^ 2)).Monic := hqm.comp (monic_X_pow 2) (by rw [hX2]; norm_num)
    have hev : aeval f (q.comp (X ^ 2)) = 0 := by
      rw [aeval_comp, aeval_X_pow, minpoly.aeval]
    have := natDegree_le_natDegree (minpoly.degree_le_of_ne_zero K f hmon.ne_zero hev)
    rwa [natDegree_comp, hX2, mul_comm] at this
  -- `r ≤ dim R`
  have h2 : r ≤ finrank K R := by
    let v : Fin r → R := fun k => ⟨f ^ (2 * (k : ℕ) + 1), hR k⟩
    have hli : LinearIndependent K v := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hc' : ∑ i, c i • f ^ (2 * (i : ℕ) + 1) = 0 := by
        have := congrArg Subtype.val hc
        simpa [v] using this
      set h : K[X] := ∑ i : Fin r, C (c i) * X ^ (i : ℕ) with hh
      have hfh : f * aeval (f ^ 2) h = 0 := by
        rw [← hc', hh, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, aeval_C, aeval_X_pow, ← pow_mul, Algebra.algebraMap_eq_smul_one,
          smul_mul_assoc, one_mul, mul_smul_comm, ← pow_succ']
      have hev : aeval (f ^ 2) h = 0 := by
        refine LinearMap.ext fun w => hinj ?_
        have := LinearMap.congr_fun hfh w
        simpa only [Module.End.mul_apply, LinearMap.zero_apply, map_zero] using this
      have hh0 : h = 0 := by
        by_contra hne
        have hdeg := minpoly.degree_le_of_ne_zero K (f ^ 2) hne hev
        have hlt : h.degree < r := degree_sum_fin_lt c
        rw [← hq, degree_eq_natDegree hqm.ne_zero] at hdeg
        exact absurd (lt_of_le_of_lt hdeg hlt) (lt_irrefl _)
      intro i
      have := congrArg (fun p : K[X] => p.coeff i) hh0
      simpa [hh, Polynomial.finsetSum_coeff, coeff_C_mul, coeff_X_pow, Fin.val_inj] using this
    simpa using hli.fintype_card_le_finrank
  omega

omit [FiniteDimensional K V] in
/-- An endomorphism preserving two complementary subspaces `p`, `q` commutes with the projection
onto `p` along `q`. -/
theorem commute_subtype_comp_projectionOnto {f : Module.End K V} {p q : Submodule K V}
    (hp : ∀ v ∈ p, f v ∈ p) (hq : ∀ v ∈ q, f v ∈ q) (h : IsCompl p q) :
    Commute f (p.subtype ∘ₗ Submodule.projectionOnto p q h) := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨a, b, rfl, -⟩ := Submodule.existsUnique_add_of_isCompl h v
  have e1 : Submodule.projectionOnto p q h (a : V) = a := Submodule.projectionOnto_apply_left h a
  have e2 : Submodule.projectionOnto p q h (b : V) = 0 := Submodule.projectionOnto_apply_right h b
  have e3 : Submodule.projectionOnto p q h (f b) = 0 :=
    Submodule.projectionOnto_apply_right h ⟨f b, hq b b.2⟩
  have e4 : Submodule.projectionOnto p q h (f a) = ⟨f a, hp a a.2⟩ :=
    Submodule.projectionOnto_apply_left h ⟨f a, hp a a.2⟩
  simp only [Module.End.mul_apply, LinearMap.comp_apply, map_add, e1, e2, e3, e4, add_zero,
    Submodule.subtype_apply, map_zero]

omit [FiniteDimensional K V] in
/-- **The commutant passes to invariant subspaces** (ambient form of
`commute_restrict_of_commute`): if `f` is semisimple with commutative commutant, then for an
`f`-invariant `P` the endomorphisms of `P` commuting with `f|_P` commute. -/
theorem commute_restrict_of_commute' {f : Module.End K V} (hf : f.IsSemisimple)
    (hcomm : ∀ g g' : Module.End K V, Commute f g → Commute f g' → Commute g g')
    {P : Submodule K V} (hP : ∀ v ∈ P, f v ∈ P) {g g' : Module.End K P}
    (hg : Commute (f.restrict hP) g) (hg' : Commute (f.restrict hP) g') : Commute g g' := by
  obtain ⟨Q, hQ, hPQ⟩ := Module.End.isSemisimple_iff.mp hf P (fun v hv => hP v hv)
  have hQ' : ∀ v ∈ Q, f v ∈ Q := fun v hv => hQ hv
  set π := Submodule.projectionOnto P Q hPQ
  have hπ := commute_subtype_comp_projectionOnto hP hQ' hPQ
  have hπp : ∀ p' : P, π (p' : V) = p' := Submodule.projectionOnto_apply_left hPQ
  let ext : Module.End K P → Module.End K V := fun h => P.subtype ∘ₗ h ∘ₗ π
  have hce : ∀ h : Module.End K P, Commute (f.restrict hP) h → Commute f (ext h) := by
    intro h hh
    refine LinearMap.ext fun v => ?_
    have h1 : π (f v) = f.restrict hP (π v) := Subtype.ext (by
      have := LinearMap.congr_fun hπ.eq v
      simp only [Module.End.mul_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this
      rw [LinearMap.coe_restrict_apply]
      exact this.symm)
    change f (h (π v) : V) = (h (π (f v)) : V)
    rw [h1, ← Module.End.mul_apply h, ← hh.eq]
    rfl
  have hc := hcomm _ _ (hce g hg) (hce g' hg')
  refine LinearMap.ext fun p => Subtype.ext ?_
  have h1 := LinearMap.congr_fun hc.eq (p : V)
  simp only [Module.End.mul_apply, ext, LinearMap.comp_apply, Submodule.subtype_apply, hπp] at h1
  simpa only [Module.End.mul_apply] using h1

/-- **Decomposition into minimal invariant subspaces**: for a semisimple `f`, `V` is the
independent sum of a finite set of nonzero `f`-invariant subspaces, each minimal among nonzero
`f`-invariant subspaces.  (Strong induction on the dimension of an invariant subspace: split off
an invariant subspace of least positive dimension and its invariant complement.) -/
theorem _root_.Module.End.IsSemisimple.exists_supIndep_minimal {f : Module.End K V}
    (hf : f.IsSemisimple) :
    ∃ s : Finset (Submodule K V), s.SupIndep id ∧ s.sup id = ⊤ ∧ ∀ B ∈ s,
      (∀ v ∈ B, f v ∈ B) ∧ B ≠ ⊥ ∧
        ∀ N : Submodule K V, (∀ v ∈ N, f v ∈ N) → N ≤ B → N = ⊥ ∨ N = B := by
  classical
  suffices H : ∀ (n : ℕ) (P : Submodule K V), finrank K P = n → (∀ v ∈ P, f v ∈ P) →
      ∃ s : Finset (Submodule K V), s.SupIndep id ∧ s.sup id = P ∧ ∀ B ∈ s,
        (∀ v ∈ B, f v ∈ B) ∧ B ≠ ⊥ ∧
          ∀ N : Submodule K V, (∀ v ∈ N, f v ∈ N) → N ≤ B → N = ⊥ ∨ N = B from
    H _ ⊤ rfl fun _ _ => Submodule.mem_top
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hPn hP
  by_cases hP0 : P = ⊥
  · exact ⟨∅, Finset.supIndep_empty _, by rw [Finset.sup_empty, hP0], by simp⟩
  -- an invariant subspace of least positive dimension inside `P`
  have hex : ∃ d, ∃ N : Submodule K V, (∀ v ∈ N, f v ∈ N) ∧ N ≠ ⊥ ∧ N ≤ P ∧ finrank K N = d :=
    ⟨_, P, hP, hP0, le_rfl, rfl⟩
  obtain ⟨B₀, hB₀, hB₀0, hB₀P, hB₀d⟩ := Nat.find_spec hex
  have hmin : ∀ N : Submodule K V, (∀ v ∈ N, f v ∈ N) → N ≤ B₀ → N = ⊥ ∨ N = B₀ := by
    intro N hN hNB
    by_cases hN0 : N = ⊥
    · exact Or.inl hN0
    refine Or.inr (Submodule.eq_of_le_of_finrank_le hNB ?_)
    rw [hB₀d]
    exact Nat.find_min' hex ⟨N, hN, hN0, hNB.trans hB₀P, rfl⟩
  obtain ⟨C, hC, hBC⟩ := Module.End.isSemisimple_iff.mp hf B₀ (fun v hv => hB₀ v hv)
  set P' := C ⊓ P
  have hP' : ∀ v ∈ P', f v ∈ P' := fun v hv => ⟨hC hv.1, hP v hv.2⟩
  have hsup : B₀ ⊔ P' = P := by
    rw [← sup_inf_assoc_of_le C hB₀P, hBC.sup_eq_top, top_inf_eq]
  have hdisj : Disjoint B₀ P' := hBC.disjoint.mono_right inf_le_left
  have hlt : P' < P := by
    refine lt_of_le_of_ne inf_le_right fun heq => hB₀0 ?_
    have : B₀ ≤ P' := heq ▸ hB₀P
    exact disjoint_self.mp (hdisj.mono_right this)
  obtain ⟨s, hs, hssup, hsB⟩ := ih _ (hPn ▸ Submodule.finrank_lt_finrank_of_lt hlt) P' rfl hP'
  have hB₀s : B₀ ∉ s := by
    intro hm
    have hle : B₀ ≤ P' := hssup ▸ Finset.le_sup (f := id) hm
    exact hB₀0 (disjoint_self.mp (hdisj.mono_right hle))
  refine ⟨insert B₀ s, hs.insert (by rw [hssup]; exact hdisj), ?_, ?_⟩
  · rw [Finset.sup_insert, hssup]; exact hsup
  · intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact ⟨hB₀, hB₀0, hmin⟩
    · exact hsB B hB

/-- For an independent family, the dimension of a finite partial sum is the sum of the
dimensions. -/
theorem finrank_biSup_eq_sum {ι : Type*} {B : ι → Submodule K V} (hB : iSupIndep B)
    (J : Finset ι) : finrank K ↥(⨆ j ∈ J, B j) = ∑ j ∈ J, finrank K (B j) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | insert i J hi ih =>
    rw [Finset.sum_insert hi, ← ih, Finset.iSup_insert]
    have hd : Disjoint (B i) (⨆ j ∈ J, B j) := hB.disjoint_biSup (by simpa using hi)
    have := Submodule.finrank_sup_add_finrank_inf_eq (B i) (⨆ j ∈ J, B j)
    rw [hd.eq_bot, finrank_bot, add_zero] at this
    exact this

end Cyclic

section Integrability

universe u

variable {F : Type*} [NontriviallyNormedField F] [LocallyCompactSpace F]

/-- `|∏ x_i|_F = ∏ |x_i|_F`. -/
theorem absF_prod {ι : Type*} (s : Finset ι) (x : ι → F) :
    absF (∏ i ∈ s, x i) = ∏ i ∈ s, absF (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [absF_one]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, absF_mul, ih]

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
    have hP := commute_subtype_comp_projectionOnto (hBA i) hC hcompl
    have hPρ := hcomm _ _ hP (hρ v)
    have hu' : (B i).subtype (Submodule.projectionOnto (B i) C hcompl u) = u := by
      rw [Submodule.subtype_apply, Submodule.projectionOnto_apply_left hcompl ⟨u, hu⟩]
    rw [← hu']
    have := LinearMap.congr_fun hPρ.eq u
    simp only [Module.End.mul_apply, LinearMap.comp_apply] at this
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
      rw [← Module.End.mul_apply, ← (hρ v).eq, Module.End.mul_apply, hw', map_zero]
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
      ((LinearMap.toMatrix b b).toLinearMap ∘ₗ (ρb i ∘ₗ (Cv i).subtype)).continuous_of_finiteDimensional
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
