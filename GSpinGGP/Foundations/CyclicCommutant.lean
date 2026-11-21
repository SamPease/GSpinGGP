/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.CommutantSquarefree
import TauCeti.LinearAlgebra.Dimension.DirectSum

/-!
# Cyclic endomorphisms and minimal invariant subspaces

Linear algebra over a field `K` for endomorphisms with commutative commutant:

* `finrank_le_natDegree_minpoly_of_squarefree`: a squarefree characteristic polynomial (`K`
  perfect) forces the minimal polynomial to have degree `dim V`;
* `commute_restrict_of_commute`, `commute_restrict_of_commute'`: for `f` semisimple, a commutative
  commutant passes to invariant subspaces;
* `Module.End.IsSemisimple.exists_supIndep_minimal`: `V` is the independent sum of minimal nonzero
  `f`-invariant subspaces;
* `finrank_le_two_mul_of_odd_pow_mem`: for `f` injective with minimal polynomial of degree
  `dim V`, the odd powers of `f` span a space of dimension `≥ dim V / 2`;
* `finrank_biSup_eq_sum`: dimension of a finite partial sum of an independent family.
-/

noncomputable section

open Module Polynomial

namespace GSpinGGP

section Cyclic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **A squarefree characteristic polynomial is the minimal polynomial**: if `χ_f` is squarefree
(`K` perfect), the minimal polynomial of `f` has degree `dim V`.  Over `K̄` every root of `χ_f` is
an eigenvalue, hence a root of `minpoly f`; `χ_f` is separable, so it divides `minpoly f`. -/
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
  have : Nonempty (Fin (finrank K V)) := ⟨⟨0, hpos⟩⟩
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
    simp only [mul_apply_eq_comp]
    rw [hext, LinearMap.coe_restrict_apply, hext]
    change f (h (π u)) = h (π (f u))
    rw [hπf, ← mul_apply_eq_comp, ← hh.eq]
    rfl
  have hc := hcomm _ _ (hcomm_ext g hg) (hcomm_ext g' hg')
  refine LinearMap.ext fun p => Subtype.ext ?_
  have h1 := congrArg Subtype.val (LinearMap.congr_fun hc.eq ⟨p, hPU p.2⟩)
  simp only [mul_apply_eq_comp, hext] at h1
  have hπp : ∀ p' : P, π (p' : V) = p' := Submodule.projectionOnto_apply_left hPQ
  have hπU : ∀ p' : P, π ((⟨p', hPU p'.2⟩ : U) : V) = p' := hπp
  rw [hπU, hπp, hπp] at h1
  simpa only [mul_apply_eq_comp] using h1

omit [FiniteDimensional K V] in
/-- **The commutant passes to invariant subspaces** (ambient form of
`commute_restrict_of_commute`, with `U = ⊤`): if `f` is semisimple with commutative commutant, then
for an `f`-invariant `P` the endomorphisms of `P` commuting with `f|_P` commute. -/
theorem commute_restrict_of_commute' {f : Module.End K V} (hf : f.IsSemisimple)
    (hcomm : ∀ g g' : Module.End K V, Commute f g → Commute f g' → Commute g g')
    {P : Submodule K V} (hP : ∀ v ∈ P, f v ∈ P) {g g' : Module.End K P}
    (hg : Commute (f.restrict hP) g) (hg' : Commute (f.restrict hP) g') : Commute g g' := by
  have hU : ∀ v ∈ (⊤ : Submodule K V), f v ∈ (⊤ : Submodule K V) := fun _ _ => Submodule.mem_top
  refine commute_restrict_of_commute hf hU hP le_top (fun h h' hh hh' => ?_) hg hg'
  let e := LinearEquiv.ofTop (⊤ : Submodule K V) rfl
  have hes : ∀ v, e.symm v = ⟨v, Submodule.mem_top⟩ := fun _ => rfl
  have hes' : ∀ w : ↥(⊤ : Submodule K V), e.symm w = w := fun _ => rfl
  have hf' : ∀ v, f.restrict hU ⟨v, Submodule.mem_top⟩ = ⟨f v, Submodule.mem_top⟩ := fun _ => rfl
  have key : ∀ k : Module.End K ↥(⊤ : Submodule K V), Commute (f.restrict hU) k →
      Commute f (e.conj k) := by
    intro k hk
    refine LinearMap.ext fun v => ?_
    have := congrArg Subtype.val (LinearMap.congr_fun hk.eq (e.symm v))
    simpa [LinearEquiv.conj_apply, mul_apply_eq_comp, hes, hf', e] using this
  have hc := hcomm _ _ (key h hh) (key h' hh')
  refine LinearMap.ext fun w => Subtype.ext ?_
  have := LinearMap.congr_fun hc.eq (e w)
  simpa [LinearEquiv.conj_apply, mul_apply_eq_comp, hes'] using this

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
  -- `r ≤ dim R`: `f, f³, …, f^{2r−1}` are independent
  have h2 : r ≤ finrank K R := by
    have hl := (linearIndependent_pow (K := K) (f ^ 2)).map' (LinearMap.mulLeft K f) (by
      rw [LinearMap.ker_eq_bot']
      intro g hg
      ext v; exact hinj (by simpa using LinearMap.congr_fun hg v))
    let v : Fin r → R := fun k => ⟨f ^ (2 * (k : ℕ) + 1), hR k⟩
    have hli : LinearIndependent K v := by
      refine LinearIndependent.of_comp R.subtype ?_
      convert hl using 1
      funext i
      simp [v, pow_mul, pow_succ']
    simpa using hli.fintype_card_le_finrank
  omega

/-- For an independent family, the dimension of a finite partial sum is the sum of the
dimensions (`TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep`). -/
theorem finrank_biSup_eq_sum {ι : Type*} {B : ι → Submodule K V} (hB : iSupIndep B)
    (J : Finset ι) : finrank K ↥(⨆ j ∈ J, B j) = ∑ j ∈ J, finrank K (B j) := by
  rw [iSup_subtype', ← Finset.sum_coe_sort J]
  exact TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep (hB.comp Subtype.val_injective)

end Cyclic

end GSpinGGP
